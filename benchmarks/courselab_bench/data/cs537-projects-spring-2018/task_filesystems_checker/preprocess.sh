#!/bin/bash
set -e

echo "=== Setting up CS537 Project 5: File System Checker ==="

cd /workspace

echo "Installing dependencies"
apt-get update > /dev/null 2>&1
apt-get install -y git python3 > /dev/null 2>&1

echo "Cloning ostep-projects repository"
git clone https://github.com/remzi-arpacidusseau/ostep-projects.git > /dev/null 2>&1
cd ostep-projects
git checkout 76cff3f89f4bf337af6e02e53a831b7eeb1396df > /dev/null 2>&1
rm -rf .git

cd /workspace

echo "Cloning xv6-public source"
git clone https://github.com/mit-pdos/xv6-public.git > /dev/null 2>&1
cd xv6-public
git checkout eeb7b415dbcb12cc362d0783e41c3d1f44066b17 > /dev/null 2>&1
rm -rf .git

cp fs.h param.h stat.h types.h /workspace/ostep-projects/filesystems-checker/

echo "Building mkfs"
gcc -Wall -Werror -Wno-error=stringop-truncation -O2 -o mkfs mkfs.c

echo "Generating file system images"
echo "dummy" > dummy.txt
./mkfs fs_base.img dummy.txt > /dev/null 2>&1

mkdir -p /workspace/ostep-projects/filesystems-checker/tests/images

python3 - <<'PY'
import os
import shutil
import struct

BSIZE = 512
DINODE_SIZE = 64
IPB = BSIZE // DINODE_SIZE
SUPER_FMT = "<7I"
DINODE_FMT = "<hhhhI13I"
DIRENT_FMT = "<H14s"
DIRSIZE = struct.calcsize(DIRENT_FMT)
NDIRECT = 12
BPB = BSIZE * 8

base = "/workspace/xv6-public/fs_base.img"
images_dir = "/workspace/ostep-projects/filesystems-checker/tests/images"

names = [
    "valid",
    "bad_inode",
    "bad_direct",
    "bad_indirect",
    "bad_root",
    "bad_dirformat",
    "bad_bitmap",
    "bad_bitmap_marked",
    "bad_direct_twice",
    "bad_indirect_twice",
    "bad_inode_referred",
    "bad_inode_unreferenced",
    "bad_refcount",
    "bad_dir_dup",
]

paths = {name: os.path.join(images_dir, f"{name}.img") for name in names}

for path in paths.values():
    shutil.copy(base, path)

def read_superblock(path):
    with open(path, "rb") as f:
        f.seek(BSIZE)
        data = f.read(struct.calcsize(SUPER_FMT))
        return struct.unpack(SUPER_FMT, data)

sb_size, sb_nblocks, sb_ninodes, sb_nlog, sb_logstart, sb_inodestart, sb_bmapstart = read_superblock(base)
nbitmap = (sb_size + BPB - 1) // BPB
data_start = sb_bmapstart + nbitmap

def inode_offset(inum):
    block = sb_inodestart + (inum // IPB)
    return block * BSIZE + (inum % IPB) * DINODE_SIZE

def read_inode(path, inum):
    with open(path, "rb") as f:
        off = inode_offset(inum)
        f.seek(off)
        data = f.read(DINODE_SIZE)
        fields = list(struct.unpack(DINODE_FMT, data))
    return off, fields

def write_inode(path, off, fields):
    with open(path, "r+b") as f:
        f.seek(off)
        f.write(struct.pack(DINODE_FMT, *fields))

def set_bitmap_bit(path, blockno, used):
    bitmap_block = sb_bmapstart + (blockno // BPB)
    bit_index = blockno % BPB
    byte_index = bit_index // 8
    bit_offset = bit_index % 8
    byte_offset = bitmap_block * BSIZE + byte_index

    with open(path, "r+b") as f:
        f.seek(byte_offset)
        b = f.read(1)
        if not b:
            return
        val = b[0]
        if used:
            val |= (1 << bit_offset)
        else:
            val &= ~(1 << bit_offset)
        f.seek(byte_offset)
        f.write(bytes([val]))

def find_free_block(path):
    with open(path, "rb") as f:
        for bmap_index in range(nbitmap):
            f.seek((sb_bmapstart + bmap_index) * BSIZE)
            bitmap = f.read(BSIZE)
            for bit in range(BPB):
                blockno = bmap_index * BPB + bit
                if blockno < data_start or blockno >= sb_size:
                    continue
                byte_index = bit // 8
                bit_offset = bit % 8
                if (bitmap[byte_index] & (1 << bit_offset)) == 0:
                    return blockno
    return None

def dir_entries(path, blockno):
    entries = []
    with open(path, "rb") as f:
        f.seek(blockno * BSIZE)
        data = f.read(BSIZE)
    entry_size = struct.calcsize(DIRENT_FMT)
    for off in range(0, BSIZE, entry_size):
        inum, name = struct.unpack(DIRENT_FMT, data[off:off + entry_size])
        clean = name.split(b"\x00", 1)[0].decode("ascii", errors="ignore")
        entries.append((off, inum, clean))
    return entries

def write_dir_inum(path, blockno, entry_offset, new_inum):
    with open(path, "r+b") as f:
        f.seek(blockno * BSIZE + entry_offset)
        f.write(struct.pack("<H", new_inum))

def write_block(path, blockno, data):
    if len(data) != BSIZE:
        raise ValueError("block data must be exactly one block")
    with open(path, "r+b") as f:
        f.seek(blockno * BSIZE)
        f.write(data)

def allocate_block(path):
    blockno = find_free_block(path)
    if blockno is None:
        raise RuntimeError("no free blocks available")
    set_bitmap_bit(path, blockno, True)
    return blockno

def write_dir_entry(path, blockno, entry_offset, inum, name):
    name_bytes = name.encode("ascii")[:14]
    name_bytes = name_bytes + b"\x00" * (14 - len(name_bytes))
    with open(path, "r+b") as f:
        f.seek(blockno * BSIZE + entry_offset)
        f.write(struct.pack(DIRENT_FMT, inum, name_bytes))

# Bad inode type (inum 2 should exist if dummy file is present)
off, fields = read_inode(paths["bad_inode"], 2)
fields[0] = 7
write_inode(paths["bad_inode"], off, fields)

# Bad direct address in inode
off, fields = read_inode(paths["bad_direct"], 2)
fields[5] = sb_size + 5
write_inode(paths["bad_direct"], off, fields)

# Bad indirect address in inode
off, fields = read_inode(paths["bad_indirect"], 2)
fields[4] = (NDIRECT + 1) * BSIZE
fields[5 + NDIRECT] = sb_size + 11
write_inode(paths["bad_indirect"], off, fields)

# Root directory not a directory
root_off, root_fields = read_inode(paths["bad_root"], 1)
root_fields[0] = 2
write_inode(paths["bad_root"], root_off, root_fields)

# Directory not properly formatted (bad . entry)
root_off, root_fields = read_inode(paths["bad_dirformat"], 1)
root_block = root_fields[5]
for off, inum, name in dir_entries(paths["bad_dirformat"], root_block):
    if name == ".":
        write_dir_inum(paths["bad_dirformat"], root_block, off, 2)
        break

# Address used by inode but marked free in bitmap
_, fields = read_inode(paths["bad_bitmap"], 2)
blockno = fields[5]
set_bitmap_bit(paths["bad_bitmap"], blockno, False)

# Bitmap marks block in use but it is not in use
free_block = find_free_block(paths["bad_bitmap_marked"])
if free_block is not None:
    set_bitmap_bit(paths["bad_bitmap_marked"], free_block, True)

# Direct address used more than once (duplicate root dir block)
root_off, root_fields = read_inode(paths["bad_direct_twice"], 1)
root_block = root_fields[5]
off, fields = read_inode(paths["bad_direct_twice"], 2)
fields[5] = root_block
write_inode(paths["bad_direct_twice"], off, fields)

# Indirect address used more than once
off, fields = read_inode(paths["bad_indirect_twice"], 2)
for i in range(NDIRECT):
    if fields[5 + i] == 0:
        fields[5 + i] = allocate_block(paths["bad_indirect_twice"])
ind_block = allocate_block(paths["bad_indirect_twice"])
data_block = allocate_block(paths["bad_indirect_twice"])
fields[5 + NDIRECT] = ind_block
fields[4] = (NDIRECT + 2) * BSIZE
write_inode(paths["bad_indirect_twice"], off, fields)

indirect = [0] * (BSIZE // 4)
indirect[0] = data_block
indirect[1] = data_block
write_block(
    paths["bad_indirect_twice"],
    ind_block,
    struct.pack("<" + "I" * len(indirect), *indirect),
)

# Inode referred to in directory but marked free
root_off, root_fields = read_inode(paths["bad_inode_referred"], 1)
root_block = root_fields[5]
target_offset = None
for off, inum, name in dir_entries(paths["bad_inode_referred"], root_block):
    if name and name not in (".", ".."):
        target_offset = off
        break
if target_offset is not None:
    write_dir_inum(paths["bad_inode_referred"], root_block, target_offset, 3)

# Inode marked used but not found in a directory
off, fields = read_inode(paths["bad_inode_unreferenced"], 3)
data_block = allocate_block(paths["bad_inode_unreferenced"])
fields[0] = 2
fields[1] = 0
fields[2] = 0
fields[3] = 1
fields[4] = BSIZE
fields[5] = data_block
for i in range(1, 13):
    fields[5 + i] = 0
write_inode(paths["bad_inode_unreferenced"], off, fields)

# Bad reference count for file
off, fields = read_inode(paths["bad_refcount"], 2)
fields[3] = max(fields[3] + 1, 2)
write_inode(paths["bad_refcount"], off, fields)

# Directory appears more than once in file system
dir_block = allocate_block(paths["bad_dir_dup"])
write_block(paths["bad_dir_dup"], dir_block, b"\x00" * BSIZE)
write_dir_entry(paths["bad_dir_dup"], dir_block, 0, 3, ".")
write_dir_entry(paths["bad_dir_dup"], dir_block, DIRSIZE, 1, "..")

off, fields = read_inode(paths["bad_dir_dup"], 3)
fields[0] = 1
fields[1] = 0
fields[2] = 0
fields[3] = 1
fields[4] = 2 * DIRSIZE
fields[5] = dir_block
for i in range(1, 13):
    fields[5 + i] = 0
write_inode(paths["bad_dir_dup"], off, fields)

root_off, root_fields = read_inode(paths["bad_dir_dup"], 1)
root_block = root_fields[5]
free_offsets = [off for off, inum, _ in dir_entries(paths["bad_dir_dup"], root_block) if inum == 0]
if len(free_offsets) >= 2:
    write_dir_entry(paths["bad_dir_dup"], root_block, free_offsets[0], 3, "subdir")
    write_dir_entry(paths["bad_dir_dup"], root_block, free_offsets[1], 3, "subdir2")
    max_index = max(free_offsets[0], free_offsets[1]) // DIRSIZE
    root_fields[4] = max(root_fields[4], (max_index + 1) * DIRSIZE)
    write_inode(paths["bad_dir_dup"], root_off, root_fields)
PY

echo "Creating checksums for protected files"
mkdir -p /tmp/checksums
CHECKSUM_FILE=/tmp/checksums/protected.sha256
: > "$CHECKSUM_FILE"

for img in /workspace/ostep-projects/filesystems-checker/tests/images/*.img; do
  sha256sum "$img" >> "$CHECKSUM_FILE"
  echo "  Protected: $img"
done

echo "Setup complete"
exit 0
