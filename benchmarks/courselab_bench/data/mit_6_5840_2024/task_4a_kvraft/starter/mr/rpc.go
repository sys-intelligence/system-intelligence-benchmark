package mr

//
// RPC definitions.
//
// remember to capitalize all names.
//

import (
	"os"
	"strconv"
)

//
// example to show how to declare the arguments
// and reply for an RPC.
//

type ExampleArgs struct {
	X int
}

type ExampleReply struct {
	Y int
}

/*-Define Work-*/

type WorkStatus int

const (
	IDLE WorkStatus = iota
	START
	FINISH
)

type WorkType int

const (
	MAP WorkType = iota
	REDUCE
)

type Work struct {
	WorkType  WorkType // MAP or REDUCE
	Filename  string
	FileIndex int // This is a convention for mr-X index
	NMapWork  int // how many map files
	NReduce   int // how many reduce files
}

type WorkArgs struct {
	WorkerID int
}

type WorkReply struct {
	HasWork bool
	Work    Work
	Term    int
}

/*-Define Report-*/
// Report work finish only if success
type ReportArgs struct {
	Work Work
	Term int
}

type ReportReply struct {
	Success bool
}

// Cook up a unique-ish UNIX-domain socket name
// in /var/tmp, for the coordinator.
// Can't use the current directory since
// Athena AFS doesn't support UNIX-domain sockets.
func coordinatorSock() string {
	s := "/var/tmp/5840-mr-"
	s += strconv.Itoa(os.Getuid())
	return s
}
