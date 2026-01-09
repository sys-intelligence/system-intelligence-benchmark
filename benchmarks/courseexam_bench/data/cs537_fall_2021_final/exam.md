# CS 537 Fall 2021 Final

```json
{
  "exam_id": "cs537_fall_2021_final",
  "test_paper_name": "CS 537 Fall 2021 Final",
  "course": "Operating Systems",
  "institution": "University of Wisconsin-Madison",
  "year": 2021,
  "score_total": 60,
  "num_questions": 59
}
```

---


## Question 1 [1 point]

The drive consists of a large number of sectors (512-byte blocks), each of which can be read or ______.
A) deleted

B) written

C) read from

D) erased

E) truncated

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "1",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "disks",
    "storage-hardware",
    "disk-geometry"
  ],
  "answer": "B"
}
```
---


## Question 2 [1 point]

We start with a _____, a circular hard surface on which data is stored persistently by inducing magnetic changes to it.
A) platter

B) surface

C) track

D) sector

E) block

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "2",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "disks",
    "storage-hardware",
    "disk-geometry"
  ],
  "answer": "A"
}
```
---


## Question 3 [1 point]

Data is encoded on each surface in concentric circles of sectors; we call one such concentric circle a ______.
A) platter

B) surface

C) track

D) sector

E) block

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "3",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "disks",
    "storage-hardware",
    "disk-geometry"
  ],
  "answer": "C"
}
```
---


## Question 4 [1 point]

Another reality is that outer tracks tend to have more sectors than inner tracks, which is a result of geometry; there is simply more room out there. These disks are often referred to as ______ disk drives.
A) wicked smart

B) extended

C) regular

D) multi-zoned

E) shingled

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "4",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "disks",
    "storage-hardware",
    "disk-geometry"
  ],
  "answer": "D"
}
```
---

## Question 5 [1 point]

The image depicts a fully specified physical magnetic disk model viewed from above, with all elements needed for disk-scheduling reasoning explicitly encoded. The disk consists of four concentric circular tracks: an outermost track, two intermediate tracks, and a small innermost track surrounding a central spindle marked by a yellow dot that represents the axis of rotation. Each of the three outer tracks is divided into angular sectors labeled with block numbers, and these numbers increase monotonically in the counter-clockwise direction, which is the disk’s rotation direction as indicated by a bold upward arrow on the right side labeled “Rotate.” The outermost track contains blocks 0 through 11, the next track inward contains blocks 12 through 23, and the third track inward contains blocks 24 through 35; the innermost circle contains no numbered blocks and appears to be non-addressable or irrelevant for the scheduling problem. Sector numbers are positioned at their approximate angular locations on each track, implicitly defining sector boundaries and relative angular offsets across tracks. On the left side of the disk is a grey actuator arm assembly consisting of a vertical column and a horizontal extension, forming an inverted L shape, terminating in a yellow circular read/write head. This head is positioned radially over the second track from the outside and angularly aligned with the sector labeled 6, which is further emphasized by a small rectangular marker containing the number “6” placed at that exact angular position on the track boundary; this unambiguously defines the initial head state in both radius (track) and angle (sector). The disk’s alternating grey shading distinguishes tracks visually but has no semantic meaning beyond clarity. The head is assumed to move only radially (to change tracks), while angular movement is entirely due to disk rotation, so a block can only be serviced when it physically rotates under the head. Text in the upper right (“s to start”, “p to pause”, “q to quit”) indicates the image likely originates from an interactive visualization but does not affect the disk model itself. Combined, the diagram explicitly defines the disk geometry, track layout, block ordering, rotation direction, initial head position at block 6, and the physical access model in which rotational latency matters; together with the stated scheduling assumptions in the problem (FIFO versus SSTF with essentially zero seek time), this information is sufficient to deterministically reason about the service order and identify which request is serviced last.

Given the disk to the right (which rotates counter-clockwise), and assuming FIFO disk scheduling, what request would be serviced last, assuming the requests are: 13, 4, 35, 34, 5
A) 13

B) 4

C) 35

D) 34

E) 5

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "5",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "disks",
    "disk-scheduling",
    "io"
  ],
  "answer": "E"
}
```
---

## Question 6 [1 point]

The image depicts a fully specified physical magnetic disk model viewed from above, with all elements needed for disk-scheduling reasoning explicitly encoded. The disk consists of four concentric circular tracks: an outermost track, two intermediate tracks, and a small innermost track surrounding a central spindle marked by a yellow dot that represents the axis of rotation. Each of the three outer tracks is divided into angular sectors labeled with block numbers, and these numbers increase monotonically in the counter-clockwise direction, which is the disk’s rotation direction as indicated by a bold upward arrow on the right side labeled “Rotate.” The outermost track contains blocks 0 through 11, the next track inward contains blocks 12 through 23, and the third track inward contains blocks 24 through 35; the innermost circle contains no numbered blocks and appears to be non-addressable or irrelevant for the scheduling problem. Sector numbers are positioned at their approximate angular locations on each track, implicitly defining sector boundaries and relative angular offsets across tracks. On the left side of the disk is a grey actuator arm assembly consisting of a vertical column and a horizontal extension, forming an inverted L shape, terminating in a yellow circular read/write head. This head is positioned radially over the second track from the outside and angularly aligned with the sector labeled 6, which is further emphasized by a small rectangular marker containing the number “6” placed at that exact angular position on the track boundary; this unambiguously defines the initial head state in both radius (track) and angle (sector). The disk’s alternating grey shading distinguishes tracks visually but has no semantic meaning beyond clarity. The head is assumed to move only radially (to change tracks), while angular movement is entirely due to disk rotation, so a block can only be serviced when it physically rotates under the head. Text in the upper right (“s to start”, “p to pause”, “q to quit”) indicates the image likely originates from an interactive visualization but does not affect the disk model itself. Combined, the diagram explicitly defines the disk geometry, track layout, block ordering, rotation direction, initial head position at block 6, and the physical access model in which rotational latency matters; together with the stated scheduling assumptions in the problem (FIFO versus SSTF with essentially zero seek time), this information is sufficient to deterministically reason about the service order and identify which request is serviced last.

Now assume a SSTF (shortest seek first) disk scheduler, and a VERY FAST (essentially infinitely fast) seek; which request would be serviced last? (assume that when you get to a particular track, the scheduler will read the blocks in the fastest order available on that track). Requests: 13, 4, 35, 34, 5.
A) 13

B) 4

C) 35

D) 34

E) 5

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "6",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "disks",
    "disk-scheduling",
    "io"
  ],
  "answer": "C"
}
```
---

## Question 7 [1 point]

The image depicts a fully specified physical magnetic disk model viewed from above, with all elements needed for disk-scheduling reasoning explicitly encoded. The disk consists of four concentric circular tracks: an outermost track, two intermediate tracks, and a small innermost track surrounding a central spindle marked by a yellow dot that represents the axis of rotation. Each of the three outer tracks is divided into angular sectors labeled with block numbers, and these numbers increase monotonically in the counter-clockwise direction, which is the disk’s rotation direction as indicated by a bold upward arrow on the right side labeled “Rotate.” The outermost track contains blocks 0 through 11, the next track inward contains blocks 12 through 23, and the third track inward contains blocks 24 through 35; the innermost circle contains no numbered blocks and appears to be non-addressable or irrelevant for the scheduling problem. Sector numbers are positioned at their approximate angular locations on each track, implicitly defining sector boundaries and relative angular offsets across tracks. On the left side of the disk is a grey actuator arm assembly consisting of a vertical column and a horizontal extension, forming an inverted L shape, terminating in a yellow circular read/write head. This head is positioned radially over the second track from the outside and angularly aligned with the sector labeled 6, which is further emphasized by a small rectangular marker containing the number “6” placed at that exact angular position on the track boundary; this unambiguously defines the initial head state in both radius (track) and angle (sector). The disk’s alternating grey shading distinguishes tracks visually but has no semantic meaning beyond clarity. The head is assumed to move only radially (to change tracks), while angular movement is entirely due to disk rotation, so a block can only be serviced when it physically rotates under the head. Text in the upper right (“s to start”, “p to pause”, “q to quit”) indicates the image likely originates from an interactive visualization but does not affect the disk model itself. Combined, the diagram explicitly defines the disk geometry, track layout, block ordering, rotation direction, initial head position at block 6, and the physical access model in which rotational latency matters; together with the stated scheduling assumptions in the problem (FIFO versus SSTF with essentially zero seek time), this information is sufficient to deterministically reason about the service order and identify which request is serviced last.

Now assume a SATF (shortest access first) scheduler, and a VERY FAST (essentially infinitely fast) seek; which request will be serviced last?
A) 13

B) 4

C) 35

D) 34

E) 5

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "7",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "disks",
    "disk-scheduling",
    "io"
  ],
  "answer": "E"
}
```
---

## Question 8 [1 point]

The image depicts a fully specified physical magnetic disk model viewed from above, with all elements needed for disk-scheduling reasoning explicitly encoded. The disk consists of four concentric circular tracks: an outermost track, two intermediate tracks, and a small innermost track surrounding a central spindle marked by a yellow dot that represents the axis of rotation. Each of the three outer tracks is divided into angular sectors labeled with block numbers, and these numbers increase monotonically in the counter-clockwise direction, which is the disk’s rotation direction as indicated by a bold upward arrow on the right side labeled “Rotate.” The outermost track contains blocks 0 through 11, the next track inward contains blocks 12 through 23, and the third track inward contains blocks 24 through 35; the innermost circle contains no numbered blocks and appears to be non-addressable or irrelevant for the scheduling problem. Sector numbers are positioned at their approximate angular locations on each track, implicitly defining sector boundaries and relative angular offsets across tracks. On the left side of the disk is a grey actuator arm assembly consisting of a vertical column and a horizontal extension, forming an inverted L shape, terminating in a yellow circular read/write head. This head is positioned radially over the second track from the outside and angularly aligned with the sector labeled 6, which is further emphasized by a small rectangular marker containing the number “6” placed at that exact angular position on the track boundary; this unambiguously defines the initial head state in both radius (track) and angle (sector). The disk’s alternating grey shading distinguishes tracks visually but has no semantic meaning beyond clarity. The head is assumed to move only radially (to change tracks), while angular movement is entirely due to disk rotation, so a block can only be serviced when it physically rotates under the head. Text in the upper right (“s to start”, “p to pause”, “q to quit”) indicates the image likely originates from an interactive visualization but does not affect the disk model itself. Combined, the diagram explicitly defines the disk geometry, track layout, block ordering, rotation direction, initial head position at block 6, and the physical access model in which rotational latency matters; together with the stated scheduling assumptions in the problem (FIFO versus SSTF with essentially zero seek time), this information is sufficient to deterministically reason about the service order and identify which request is serviced last.

Assuming a VERY FAST seek (essentially infinitely fast), how would you order the disk schedulers for those five requests, from fastest to slowest?
A) SSTF, SATF, FIFO

B) SSTF, FIFO, SATF

C) SATF, SSTF, FIFO

D) SATF, FIFO, SSTF

E) FIFO, SATF, SSTF

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "8",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "disks",
    "disk-scheduling",
    "io"
  ],
  "answer": "C"
}
```
---


## Question 9 [1 point]

The three basic components of disk I/O time are ______, _______, and ______.
A) transition, position, constitution

B) move head, wait for head to stop moving, transfer

C) position, transfer, react

D) shake, rattle, roll

E) seek, rotate, transfer

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "9",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "disks",
    "disk-scheduling",
    "io"
  ],
  "answer": "E"
}
```
---


## Question 10 [1 point]

A disk scheduling algorithm that avoids starvation is called ______
A) PASS

B) CRANK

C) SCAN

D) CHECK

E) FAIRPLAY

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "10",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "disks",
    "disk-scheduling",
    "io"
  ],
  "answer": "C"
}
```
---


## Question 11 [1 point]

RAIDs offer a number of advantages over a single disk. One advantage is performance. Using multiple disks in parallel can greatly speed up I/O times. Another benefit is capacity. Large data sets demand large disks. Finally, RAIDs can improve ______
A) size

B) the odds

C) reliability

D) latency

E) distribution

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "11",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "raid",
    "storage",
    "fault-tolerance"
  ],
  "answer": "C"
}
```
---


## Question 12-13 [2 points]

Part A: More generally, a mirrored system (with mirroring level of 2) can tolerate 1 disk failure for certain, and up to ______ failures depending on which disks fail. [Assume here there are N disks in the system]
A) 2

B) N/4

C) N/2

D) N/3

E) N

Part B: Thus, we can conclude that the maximum bandwidth obtained during sequential writing to a 2-way mirrored array is ______ [Assume here there are N disks, and that a single disk delivers S MB/s of disk bandwidth]
A) S MB/s

B) 2 x S MB/s

C) N x S MB/s

D) N x S / 2 MB/s

E) N x S x S MB/s

Your answer should be two letters separated by a comma, in order for Part A then Part B (for example: C,D).

```json
{
  "problem_id": "12-13",
  "points": 2,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "raid",
    "fault-tolerance",
    "performance"
  ],
  "answer": "C,D"
}
```
---


## Question 14 [1 point]

For example, in RAID-4, if we had blocks of size 2 bits... they might look something like this:
Block0: 00
Block1: 10
Block2: 11
Block3: 10
Parity: _____
A) 00

B) 01

C) 10

D) 11

E) None of the above

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "14",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "raid",
    "storage",
    "fault-tolerance"
  ],
  "answer": "D"
}
```
---


## Question 15 [1 point]

RAID-4 uses a disk for parity information for every group of disks it is protecting. Thus, our useful capacity for a RAID group is ______ [Assume N disks, and B bytes of data per disk]
A) N x B

B) N

C) B

D) N x (B - 1)

E) (N - 1) x B

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "15",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "raid",
    "storage",
    "fault-tolerance"
  ],
  "answer": "E"
}
```
---


## Question 16 [1 point]

Random read performance of RAID-5 (as compared to RAID-4) is ______
A) a little better

B) a little worse

C) a lot better

D) a lot worse

E) about the same

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "16",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "raid",
    "storage",
    "fault-tolerance"
  ],
  "answer": "A"
}
```
---


## Question 17 [1 point]

RAID Level(s) _____ encounter(s) the ‘small write’ problem.
A) 0

B) 1

C) 4

D) 5

E) 4 and 5

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "17",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "raid",
    "storage",
    "fault-tolerance"
  ],
  "answer": "E"
}
```
---


## Question 18 [1 point]

A single write (to a RAID-4) requires _____ read(s) and then ______ write(s) to the underlying disks. [assuming subtractive parity]
A) 2, 1

B) 1, 2

C) 2, 2

D) 1, 1

E) None of the above

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "18",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "raid",
    "storage",
    "fault-tolerance"
  ],
  "answer": "C"
}
```
---


## Question 19 [1 point]

Assuming that each disk, under a random write workload, delivers R MB/s, a RAID-5 system with N disks will deliver ______ MB/s under a random write workload.
A) N x R MB/s

B) N x R / 2 MB/s

C) N x R / 4 MB/s

D) R / 2 MB/s

E) R MB/s

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "19",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "raid",
    "storage",
    "fault-tolerance"
  ],
  "answer": "C"
}
```
---


## Question 20 [1 point]

To conclude, if you strictly want performance and do not care about reliability, ______ is obviously best.
A) rebooting

B) a parity-based approach

C) mirroring

D) thinking

E) striping

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "20",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "raid",
    "storage",
    "fault-tolerance"
  ],
  "answer": "E"
}
```
---


## Question 21 [1 point]

A Flash bank is organized into a large number of ______, each of which is further sub-divided into pages.
A) mega pages

B) blocks

C) units

D) chunks

E) candy bars

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "21",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "flash",
    "storage",
    "ftl"
  ],
  "answer": "B"
}
```
---


## Question 22 [1 point]

A typical size of a Flash page is ____.
A) 4 KB

B) 256 KB

C) 256 MB

D) 256 GB

E) over 1 TB

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "22",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "flash",
    "storage",
    "ftl"
  ],
  "answer": "A"
}
```
---


## Question 23 [1 point]

Once a Flash page is programmed, it _____.
A) can be re-programmed repeatedly (without intervening steps)

B) is guaranteed to store bits within it, permanently

C) can never be re-programmed

D) can be re-programmed, but first must be read

E) cannot be re-programmed until the entire block is erased

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "23",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "flash",
    "storage",
    "ftl"
  ],
  "answer": "E"
}
```
---


## Question 24 [1 point]

The biggest reliability problem Flash chips have is ______.
A) head crashes

B) read/write disturbance

C) cracking

D) wear out

E) burn out

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "24",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "flash",
    "storage",
    "ftl"
  ],
  "answer": "D"
}
```
---


## Question 25 [1 point]

The process of _______ ensures that dead pages can be reclaimed for subsequent writes.
A) wear leveling

B) read programming

C) garbage collection

D) input reduction

E) write amplification

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "25",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "flash",
    "storage",
    "ftl"
  ],
  "answer": "C"
}
```
---


## Question 26 [1 point]

If erases take 1000 microseconds, and page programming takes 40 microseconds, how long did the entire sequence of five writes take to complete? (Block 0 was erased, then 5 pages written).
A) 1000 microseconds

B) 1100 microseconds

C) 1200 microseconds

D) 40000 microseconds

E) 1 millisecond

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "26",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "flash",
    "storage",
    "ftl"
  ],
  "answer": "C"
}
```
---


## Question 27 [1 point]

Given the state... how long will the next write take to complete? (Block 0 has 5 valid, 5 empty pages. Next write goes to an empty page).
A) 10 microseconds

B) 40 microseconds

C) 1000 microseconds

D) 1040 microseconds

E) 2 milliseconds

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "27",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "flash",
    "storage",
    "ftl"
  ],
  "answer": "B"
}
```
---


## Question 28 [1 point]

After the five writes above took place, assume the FTL has the following contents: 12->4 14->3 29->2 37->0 39->1. What data value will be returned if the user issues a read to block 29?
Data in Block 0: qiUKz
(q at 0, i at 1, U at 2, K at 3, z at 4)
A) q

B) i

C) U

D) K

E) z

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "28",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "flash",
    "storage",
    "ftl"
  ],
  "answer": "C"
}
```
---


## Question 29 [1 point]

After the first five writes... assume the next five writes are to blocks 12, 20, 30, 39, and 50. After these writes, how many pages in the SSD will be live?
A) 7

B) 8

C) 9

D) 10

E) 11

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "29",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "flash",
    "storage",
    "ftl"
  ],
  "answer": "B"
}
```
---


## Question 30 [1 point]

Assuming the same times (erase 1000, program 40), what is the average cost per write for the first 10 writes? (First 5: 1200 us. Next 5: 200 us).
A) 100 microseconds

B) 120 microseconds

C) 140 microseconds

D) 200 microseconds

E) 1040 microseconds

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "30",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "flash",
    "storage",
    "ftl"
  ],
  "answer": "C"
}
```
---


## Question 31 [1 point]

The ______ is the generic name that is used in many file systems to describe the structure that holds the metadata for a given file.
A) superblock

B) inode

C) data block

D) directory

E) journal

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "31",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "metadata",
    "storage"
  ],
  "answer": "B"
}
```
---


## Question 32 [1 point]

Thus, an inode has a fixed number of direct pointers (12), and a single indirect pointer... Assuming each slot can point to a 4-KB block, and that disk addresses are 4 bytes, the file can grow to be ______.
A) 4096 KB

B) 4100 KB

C) 4104 KB

D) 4044 KB

E) 4144 KB

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "32",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "inodes",
    "metadata"
  ],
  "answer": "E"
}
```
---


## Question 33 [1 point]

Let’s examine an example with twelve direct pointers, as well as both a single and a double indirect block. Assuming a block size of 4 KB... max file size of ______ (approximately).
A) ~4 KB

B) ~1 MB

C) ~4 MB

D) ~1 GB

E) ~4 GB

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "33",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "inodes",
    "metadata"
  ],
  "answer": "E"
}
```
---


## Question 34 [1 point]

In VSFS... directories have a simple organization; a directory basically just contains a list of (______, ______) pairs.
A) directory name, file attribute

B) file name, inode number

C) file name, parent location

D) inode number, file type

E) inode type, file directory

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "34",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "directories",
    "metadata"
  ],
  "answer": "B"
}
```
---


## Question 35 [1 point]

Free space management is important... In VSFS, we have two simple ______ for this task.
A) free lists

B) management teams

C) hamburgers

D) bitmaps

E) inodes

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "35",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "free-space",
    "allocation"
  ],
  "answer": "D"
}
```
---


## Question 36 [1 point]

In this example, let us first assume that you want to simply open a file /foo/bar, read it, and then close it. In doing so, the file system will read ______ inodes.
A) 0

B) 1

C) 2

D) 3

E) 4

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "36",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "directories",
    "path-lookup"
  ],
  "answer": "D"
}
```
---


## Question 37 [1 point]

Once /foo/bar is opened, assume a process appends a data block to it three times. The following blocks will be written to during each append: ______, ______, and ______.
A) the file’s inode, data bitmap, and the data block itself

B) the directory data block, the data block, and the superblock

C) the inode bitmap, the directory data block, and the inode

D) the journal, the data block itself, and the directory

E) the department, the chair, the entire university

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "37",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "inodes",
    "allocation"
  ],
  "answer": "A"
}
```
---


## Question 38 [1 point]

Write buffering... has a number of performance benefits. They are ______, ______, and ______.
A) skipping, tricking, and faking out

B) batching, scheduling, and avoiding writes altogether

C) batching, scheduling, and smoothing writes out

D) batching, avoiding writes, and spacing writes out over time

E) anticipating, logging, and batch amortizing

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "38",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "buffering",
    "performance"
  ],
  "answer": "B"
}
```
---


## Question 39 [1 point]

VSFS Simulator. Initial State: inodes [d a:0 r:2]... Final State: inodes [d a:0 r:2][f a:-1 r:1]... data [(.,0) (..,0) (m,1)]... What operation took place?
A) creat("/m")

B) mkdir("/m")

C) unlink("/m")

D) append a block to root directory

E) append a block to root inode

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "39",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "vsfs",
    "directories"
  ],
  "answer": "A"
}
```
---


## Question 40 [1 point]

Continuing from Q39... Final State: inodes [d a:0 r:2][f a:-1 r:2]... data [(.,0) (..,0) (m,1) (o,1)]... What operation was it?
A) mkdir("/o")

B) unlink("/m")

C) read("/m")

D) link("/m", "/o")

E) creat("/o")

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "40",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "vsfs",
    "directories"
  ],
  "answer": "D"
}
```
---


## Question 41 [1 point]

Crash scenario: just the data block is written to disk. In this case, ______
A) the data is on disk, but it can never be read

B) the data is on disk, and can be read after recovery, but it is garbage

C) the data is on disk, but the inode bitmap says it is free

D) the data is on disk, and it can be easily read after recovery

E) the data never reaches the disk

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "41",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "crash-consistency",
    "fsck"
  ],
  "answer": "A"
}
```
---


## Question 42 [1 point]

Crash scenario: just the updated inode is written to disk. In this case, ______
A) the data is on disk, but it can never be read

B) the data may seemingly be read after recovery, but it is garbage

C) the data bitmap and inode bitmap don’t agree

D) the data is on disk, and can be easily read after recovery

E) the inode cannot be read

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "42",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "crash-consistency",
    "fsck"
  ],
  "answer": "B"
}
```
---


## Question 43 [1 point]

Just the updated inode is written to disk. Sometimes we refer to this as a ______
A) file system inconsistency (the inode and data bitmap disagree)

B) file system inconsistency (the data block and inode disagree)

C) file system inconsistency (the directory and inode disagree)

D) file system inconsistency (the data bitmap and inode bitmap disagree)

E) file system confusion

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "43",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "crash-consistency",
    "fsck"
  ],
  "answer": "A"
}
```
---


## Question 44 [1 point]

What we’d like to do ideally is move the file system from one consistent state to another ______
A) computationally

B) passionately

C) logically

D) atomically

E) sequentially

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "44",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "crash-consistency",
    "fsck"
  ],
  "answer": "D"
}
```
---


## Question 45 [1 point]

fsck has a big and perhaps more fundamental problem: it is too ______
A) slow

B) complicated

C) redundant

D) incoherent

E) fast

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "45",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "crash-consistency",
    "fsck"
  ],
  "answer": "A"
}
```
---


## Question 46 [1 point]

The basic journaling protocol includes the following three phases: journal write, journal commit, and ______
A) transaction

B) full write

C) journal delete

D) checkpoint

E) phase out

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "46",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "journaling",
    "crash-consistency"
  ],
  "answer": "D"
}
```
---


## Question 47 [1 point]

A simpler (and more common) form of journaling is sometimes called ordered journaling... except that ______ is/are not written to the journal.
A) inodes

B) user data

C) directory data

D) bitmaps

E) information

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "47",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "journaling",
    "crash-consistency"
  ],
  "answer": "B"
}
```
---


## Question 48 [1 point]

In ordered (or metadata) journaling, data must be written to disk before _______ in order to ensure that a committed inode does not point to garbage data.
A) the checkpoint

B) freeing space in the journal

C) the transaction commit block

D) anything else

E) sunrise

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "48",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "journaling",
    "crash-consistency"
  ],
  "answer": "C"
}
```
---


## Question 49 [1 point]

If a crash happens during replay, _______
A) all data is lost

B) the system may not be able to reboot

C) the recovery starts over after reboot, but might lose data committed to the journal

D) the recovery starts over after reboot, and should work correctly

E) you are out of luck.

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "49",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "journaling",
    "crash-consistency"
  ],
  "answer": "D"
}
```
---


## Question 50 [1 point]

Data journaling reduces performance by (roughly) a factor of _______ during sequential writes as compared to ordered journaling.
A) 1.5

B) 2

C) 3

D) 4

E) 5

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "50",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "file-systems",
    "journaling",
    "performance"
  ],
  "answer": "B"
}
```
---


## Question 51 [1 point]

The largest benefit of using a distributed client/server file system such as NFS is ______
A) performance

B) sharing

C) reliability

D) code coverage

E) ease of testing

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "51",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "nfs",
    "distributed-systems",
    "network-file-systems"
  ],
  "answer": "B"
}
```
---


## Question 52 [1 point]

Servers (seem to) crash (or become unavailable) primarily due to power outages, bugs, and _______
A) application demands

B) clients with little memory

C) slow disks

D) bears

E) network partitions

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "52",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "nfs",
    "distributed-systems",
    "network-file-systems"
  ],
  "answer": "E"
}
```
---


## Question 53 [1 point]

NFS protocol requests, which contain all relevant information needed to complete the request, are sometimes called _______
A) stateless

B) harmless

C) connectionless

D) tasteless

E) quirky

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "53",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "nfs",
    "distributed-systems",
    "network-file-systems"
  ],
  "answer": "A"
}
```
---


## Question 54 [1 point]

The NFS file handle consists of three parts: volume identifier, inode number, and ______
A) file descriptor

B) security token

C) smoke screen indicator

D) request identifier

E) generation number

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "54",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "nfs",
    "distributed-systems",
    "network-file-systems"
  ],
  "answer": "E"
}
```
---


## Question 55 [1 point]

During a file open, many ________ requests will likely be made to the server.
A) NFSPROC_RMDIR

B) NFSPROC_MKDIR

C) NFSPROC_LOOKUP

D) NFSPROC_REMOVE

E) NFSPROC_FLUSH

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "55",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "nfs",
    "distributed-systems",
    "network-file-systems"
  ],
  "answer": "C"
}
```
---


## Question 56 [1 point]

An operation is called idempotent when the effect of performing the operation ______ is equivalent to the effect of performing the operation a single time.
A) never

B) once

C) silently

D) many times

E) in reverse

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "56",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "nfs",
    "distributed-systems",
    "network-file-systems"
  ],
  "answer": "D"
}
```
---


## Question 57 [1 point]

NFS clients handle network packet losses and server crashes uniformly by using a _______ approach.
A) caching

B) oddly efficient

C) redundancy-based

D) timeout/retry

E) handshake/fistbump

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "57",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "nfs",
    "distributed-systems",
    "network-file-systems"
  ],
  "answer": "D"
}
```
---


## Question 58 [1 point]

NFS clients use caches to improve performance... Two primary subproblems of cache consistency are _______.
A) latency/staleness

B) visibility/correctness

C) choiceness/visibility

D) correctness/staleness

E) staleness/visibility

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "58",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "nfs",
    "distributed-systems",
    "network-file-systems"
  ],
  "answer": "E"
}
```
---


## Question 59 [1 point]

NFS clients buffer writes... ‘flush on close’ behavior addresses the _______ problem.
A) latency

B) staleness

C) correctness

D) visibility

E) choiceness

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "59",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "nfs",
    "distributed-systems",
    "network-file-systems"
  ],
  "answer": "D"
}
```
---


## Question 60 [1 point]

NFS servers also have a cache, but must flush writes to disk immediately before returning success to clients. The reason for this is ________.
A) performance; this approach is usually faster

B) correctness; this ensures no writes are lost due to an untimely server crash

C) choiceness; having more choice is critical in the modern world

D) caching in both clients and servers adds too much complexity to the protocol

E) lost to history

Your answer should be one letter only (A, B, C, D, or E). No extra text.

```json
{
  "problem_id": "60",
  "points": 1,
  "type": "ExactMatch",
  "tags": [
    "operating-systems",
    "nfs",
    "distributed-systems",
    "network-file-systems"
  ],
  "answer": "B"
}
```
