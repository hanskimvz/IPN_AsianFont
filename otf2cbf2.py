#!/usr/bin/python

"""
Rasterises OTF font files into a CBF (UDP compressed binary font) file.

(c) Copyright UDP Technology (2013).  All Rights Reserved.

Trying to convert python3 program. failed.
"""

from bitarray import bitarray
from collections import Counter
import getopt
from freetype import *
import heapq
from multiprocessing import Process, Queue, Manager
from os import path
from Queue import Empty
from struct import pack
from StringIO import StringIO
import sys, re, csv
from sets import Set

sys.exit()
class CommentedFile:
    def __init__(self, f, commentstring='#'):
        self.f = f
        self.commentstring = commentstring

    def next(self):
        while 1:
            line = self.f.next().split("#")[0].strip()
            if line != None and len(line):
               return line

    def __iter__(self):
        return self

class Char:
    dwidth = (0, 0)
    bbx = (0, 0, 0, 0)
    bitmap = None
    runs = None

def rasteriseChar(face, c):

    char = Char()

    face.load_char(unichr(c), FT_LOAD_TARGET_MONO | FT_LOAD_RENDER)
    width, height = face.glyph.bitmap.width, face.glyph.bitmap.rows
    left, top = face.glyph.bitmap_left, face.glyph.bitmap_top
    buffer = face.glyph.bitmap.buffer

    assert face.glyph.bitmap.pixel_mode == FT_PIXEL_MODE_MONO

    # Encode the glyph image as a bitmap
    bits = bitarray(width * height)
    rowLengthBytes = 2 * ((width + 15) / 16)
    for y in range(height):
        rowStart = y * rowLengthBytes
        for x in range(width):
          bits[y * width + x] = (buffer[x / 8 + rowStart] & (0x80 >> (x % 8)))

    # Trim the top edge
    while height != 0 and not any(bits[0:width]):
        del bits[0:width]
        height -= 1
        top -= 1

    # Trim the bottom edge
    while height != 0 and not any(bits[-width:]):
        del bits[-width:]
        height -= 1

    # Trim the left edge
    while width != 0 and not any(bits[0::width]):
        del bits[0::width]
        width -= 1
        left += 1

    # Trim the right edge
    while width != 0 and not any(bits[width-1::width]):
        del bits[width-1::width]
        width -= 1

    char.bitmap = bits
    char.bbx = (width, height, left, top)
    char.dwidth = (face.glyph.linearHoriAdvance / 65536,
        face.glyph.linearVertAdvance / 65536)

    return char

class Worker(Process):
    def __init__(self, work_queue, result_queue, size):
        super(Worker, self).__init__()
        self.work_queue = work_queue
        self.result_queue = result_queue
        self.size = size
        self.face = None
        self.faceName = None

    def run(self):
        while 1:
            try:
                (faceName, char) = self.work_queue.get_nowait()
            except Empty:
                break

            if self.faceName != faceName or self.face == None:
                self.face = Face(faceName)
                self.face.set_char_size(self.size)
                self.faceName = faceName
            self.result_queue.put((char, rasteriseChar(self.face, char)))

def rleEncodeBitmap(counts, c):
    runs = []
    state = False   # Begin with white
    begin = 0       # The first run begins at offset = 0
    while 1:
        try:
            end = c.bitmap.index(state == False, begin)
        except ValueError:
            break
        length = end - begin
        runs.append(length)
        counts[state][length] += 1
        begin = end
        state = (state == False)

    # The last run is simply omitted. The decoded will ink up to the end of the
    # the character block if it needs to.

    c.runs = runs

def buildHuffTree(counts):
    trees = []
    for symbol, count in counts.items():
        trees.append((count, symbol))
    heapq.heapify(trees)
    while len(trees) > 1:
        childR, childL = heapq.heappop(trees), heapq.heappop(trees)
        parent = (childL[0] + childR[0], childL, childR)
        heapq.heappush(trees, parent)

    return trees[0]

def makeHuffLut(huffTree, prefix = bitarray()):
    if len(huffTree) == 2:
        huffLut = dict()
        huffLut[huffTree[1]] = prefix
    else:
        huffLut = makeHuffLut(huffTree[1], prefix + bitarray('0'))
        huffLut.update(makeHuffLut(huffTree[2], prefix + bitarray('1')))
    return huffLut

def lslBitArray(a):
    return a[1:] + bitarray('0')

def incBitArray(a):
    if a.length() == 0:
        return a
    c = a.copy()
    c.setall(False)
    c[-1] = True
    while c.any():
        a, c = a ^ c, lslBitArray(a & c)
    return a

def sortLutEntries(a, b):
    alen, blen = a[1].length(), b[1].length()
    return int(a[0] - b[0]) if (alen == blen) else int(alen - blen)

def makeHuffLutCanonical(huffLut):
    lut = sorted(huffLut.items(), cmp=sortLutEntries)

    lastBitLength = 0
    code = bitarray()
    for i in range(len(lut)):
        curBitLength = lut[i][1].length()

        code = incBitArray(code)
        code.extend([False] * (curBitLength - lastBitLength))

        lut[i] = (lut[i][0], code)
        lastBitLength = curBitLength

    return dict(lut)


def writeHuffLutCodeBook(f, huffLut):
    """
    Prints a code-book into a file. Each symbol is represented by 16-bits. The
    code is written by it's length as a 16-bit value. huffLut is assumed to be
    the lookup table of a canonical huffman code. The code book for any
    canonical huffman code can be recovered from knowledge of the symbols it
    contains and the lengths of their codes.
    """
    table = sorted(huffLut.items(), cmp=sortLutEntries)
    f.write(pack("<I", len(table)))
    for symbol, code in table:
        f.write(pack("<H", symbol))
        f.write(pack("<H", code.length()))

def writeBitArrayWordPadded(f, bits):
    # Write the data
    f.write(bits.tobytes())

    # Pad the character to 32-bits
    while (f.tell() % 4) != 0:
        f.write('\0')

def writeCbfChar(f, c, huffLuts):
    # Write bbx
    f.write(pack("bbbb", *c.bbx))

    # Write advanceX
    f.write(pack("<h", c.dwidth[0]))

    # Huffman compress the RLE data
    huffData = bitarray()
    lut = 0         # Begin pointing at the white LUT
    for run in c.runs:
        huffData.extend(huffLuts[lut][run])
        lut = 0 if (lut == 1) else 1

    # Write dataLengthBits
    f.write(pack("<h", huffData.length()))

    writeBitArrayWordPadded(f, huffData)

def writeCbfCharDataIndex(f, charDataOffsets):

    # Delta code the offsets, and accumulate statistics
    counts = Counter()
    deltas = [None] * len(charDataOffsets)
    inHole = True
    offset = 0
    terminator = 65535
    finalChar = 0
    for i in range(len(charDataOffsets)):
        if charDataOffsets[i] == None:
            if inHole == False:
                inHole = True
                counts[terminator] += 1
        else:
            if inHole == True:
                inHole = False

            lastOffset = offset
            offset = charDataOffsets[i]
            deltas[i] = offset - lastOffset
            counts[offset - lastOffset] += 1
            finalChar = i

    # Write the number of entries in the index
    f.write(pack("<I", finalChar + 1))

    # Build a huffman tree
    huffLut = makeHuffLutCanonical(makeHuffLut(buildHuffTree(counts)))

    # Write the code book
    writeHuffLutCodeBook(f, huffLut)

    # Huffman code the deltas
    i = 0
    while 1:
        while i < len(deltas) and deltas[i] == None:
            i += 1

        if i >= len(deltas):
            break

        # Write the index of the beginning of the character group
        f.write(pack("<I", i))

        # Encode the deltas
        huffData = bitarray()
        while i < len(deltas) and deltas[i] != None:
            huffData.extend(huffLut[deltas[i]])
            i += 1

        # Add a terminator marker to the stream
        huffData.extend(huffLut[terminator])

        # Write the compressed length of the group
        bytes = huffData.tobytes()
        f.write(pack("<I", len(bytes)))
        f.write(bytes)

def writeCbf(f, chars, height):

    # RLE encode bitmaps, and accumulate run length statistics
    sys.stderr.write("RLE Encoding\n")
    counts = [Counter(), Counter()]
    for c in chars:
        if c.bitmap != None:
            rleEncodeBitmap(counts, c)

    # Make a huffman tree for black and white runs
    sys.stderr.write("Generating Huffman Tree\n")
    charHuffLuts = map(lambda c: makeHuffLutCanonical(
        makeHuffLut(buildHuffTree(c))), counts)

    # Encode the characters
    sys.stderr.write("Compressing Glyphs\n")
    charData = StringIO()
    charDataOffsets = [None] * len(chars)
    for i in range(len(chars)):
        c = chars[i]
        if c.bitmap != None:
            charDataOffsets[i] = charData.tell()
            writeCbfChar(charData, c, charHuffLuts)

    # Encode the character data index
    sys.stderr.write("Writing Glyph Index\n")
    charIndex = StringIO()
    writeCbfCharDataIndex(charIndex, charDataOffsets)

    # Write out the huffman LUTs
    charCodeBooks = [None] * len(charHuffLuts)
    for i in range(len(charHuffLuts)):
        charCodeBook = StringIO()
        writeHuffLutCodeBook(charCodeBook, charHuffLuts[i])
        charCodeBooks[i] = charCodeBook

    # Write the file
    cbfHeader = StringIO()
    cbfHeader.write(pack("<I", len(chars)))
    cbfHeader.write(pack("<I", height))
    cbfHeader.write(pack("<I", charData.tell()))
    offset = cbfHeader.tell()

    cbfBody = StringIO()
    chunks = [charCodeBooks[0], charCodeBooks[1], charIndex, charData]
    offset += len(chunks) * 4
    for chunk in chunks:
        cbfHeader.write(pack("<I", offset + cbfBody.tell()))
        cbfBody.write(chunk.getvalue())

    f.write(cbfHeader.getvalue())
    f.write(cbfBody.getvalue())

def usage():
    print >> sys.stderr, ("Usage:\n"
        "%s -o OUTFILE -m FONTMAP -s SIZE\n") % sys.argv[0]

def main():
    outFilePath = None
    mapFilePath = None
    printChars = False
    size = 48
    maxCharCode = 0
    fontChars = Set()

    try:
        optlist, args = getopt.getopt(sys.argv[1:], 'm:s:o:')
    except getopt.GetoptError as err:
        print >> sys.stderr, str(err)
        usage()
        sys.exit(2)

    for opt in optlist:
        if opt[0] == '-m':
            mapFilePath = opt[1]
        elif opt[0] == '-s':
            size = int(opt[1])
        elif opt[0] == '-o':
            outFilePath = opt[1]

    if mapFilePath == None:
        sys.stderr.write("No map file specified\n")
        usage()
        sys.exit(2)

    if outFilePath == None:
        sys.stderr.write("No output file path specified\n")
        usage()
        sys.exit(2)

    # Open the ourput file
    outFile = open(outFilePath, "w")

    # Rasterise the characters in multiple processes
    manager = Manager()
    work_queue = Queue()
    result_queue = Queue()

    # Parse the map file
    fontMap = csv.reader(CommentedFile(open(mapFilePath, "rb")),
        delimiter=',')
    for row in fontMap:
        if len(row) != 3:
            sys.stderr.write("Each entry must have a font file, " +
                "a start address and end address\n")
            sys.exit(1)

        faceName = row[0].strip()
        startCode = int(row[1], 16)
        endCode = int(row[2], 16) + 1

        try:
            face = Face(faceName)
        except ft_errors.FT_Exception as err:
            sys.stderr.write("Failed to load font file: %s\n" % faceName)
            sys.exit(2)

        face.set_char_size(size * 64)

        # Determine the maximum glyph index
        charcode, gindex = face.get_first_char()
        while ( gindex ):
            charcode, gindex = face.get_next_char( charcode, gindex )
            maxCharCode = max(charcode, maxCharCode)

        # Determine which glyphs are present
        charsPresent = [False] * (maxCharCode + 1)
        charcode, gindex = face.get_first_char()
        while ( gindex ):
            charcode, gindex = face.get_next_char( charcode, gindex )
            charsPresent[charcode] = True

        # Make sure the space is included
        if startCode <= 0x20 and 0x20 < endCode:
            charsPresent[0x20] = True

        # Select characters
        charInSet = [False] * (maxCharCode + 1)
        charInSet[startCode:endCode] = [True] * (endCode - startCode)

        # Queue the rendering
        for c in range(maxCharCode):
            assert(c < len(charsPresent))
            assert(c < len(charInSet))
            if charsPresent[c] and charInSet[c] and not c in fontChars:
                fontChars.add(c)
                work_queue.put((faceName, c))

    chars = [Char()] * (maxCharCode + 1)
    renderCount = work_queue.qsize()

    for i in range(4):
        Worker(work_queue, result_queue, size * 64).start()

    renderedCount = 0
    for c in range(renderCount):
        r = result_queue.get()
        renderedCount += 1
        sys.stderr.write("Rendered %d / %d\r" %
            (renderedCount, renderCount))
        chars[r[0]] = r[1]

    sys.stderr.write("\n")

    writeCbf(outFile, chars, face.height * size / face.units_per_EM)

if __name__ == "__main__":
    main()
