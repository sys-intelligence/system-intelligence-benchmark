package mr

import (
	"log"
	"math"
	"net"
	"net/http"
	"net/rpc"
	"os"
	"sync"
	"time"
)

const SUCCESS = math.MaxInt32

type Coordinator struct {
	// Your definitions here.
	tasks   chan Work // a taskqueue
	mu      sync.Mutex
	terms   []int
	wg      sync.WaitGroup
	nMap    int
	nReduce int
	done    bool
}

func (c *Coordinator) CallGetWork(args *WorkArgs, reply *WorkReply) error {
	if len(c.tasks) == 0 {
		reply.HasWork = false
		return nil
	}
	reply.Work = <-c.tasks
	c.mu.Lock()
	reply.Term = c.terms[reply.Work.FileIndex]
	c.mu.Unlock()
	reply.HasWork = true

	go func() {
		time.Sleep(10 * time.Second)
		c.mu.Lock()
		defer c.mu.Unlock()
		if c.terms[reply.Work.FileIndex] == SUCCESS {
			return
		}
		c.terms[reply.Work.FileIndex]++
		c.tasks <- reply.Work
	}()

	return nil
}

func (c *Coordinator) CallReport(args *ReportArgs, reply *ReportReply) error {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.terms[args.Work.FileIndex] != args.Term {
		reply.Success = false
		return nil
	}
	c.terms[args.Work.FileIndex] = SUCCESS
	c.wg.Done()
	reply.Success = true
	return nil
}

// start a thread that listens for RPCs from worker.go
func (c *Coordinator) server() {
	rpc.Register(c)
	rpc.HandleHTTP()
	//l, e := net.Listen("tcp", ":1234")
	sockname := coordinatorSock()
	os.Remove(sockname)
	l, e := net.Listen("unix", sockname)
	if e != nil {
		log.Fatal("listen error:", e)
	}
	go http.Serve(l, nil)
}

// main/mrcoordinator.go calls Done() periodically to find out
// if the entire job has finished.
func (c *Coordinator) Done() bool {
	return c.done
}

func StartReduceWork(c *Coordinator) {
	c.wg.Wait()
	c.terms = make([]int, c.nReduce)
	for i := 0; i < c.nReduce; i++ {
		c.tasks <- Work{
			WorkType:  REDUCE,
			FileIndex: i,
			NReduce:   c.nReduce,
			NMapWork:  c.nMap,
		}
		c.wg.Add(1)
	}
	go WorkDone(c)
}

func WorkDone(c *Coordinator) {
	c.wg.Wait()
	c.done = true
}

// create a Coordinator.
// main/mrcoordinator.go calls this function.
// nReduce is the number of reduce tasks to use.
func MakeCoordinator(files []string, nReduce int) *Coordinator {

	var buflen int
	if len(files) > nReduce {
		buflen = len(files)
	} else {
		buflen = nReduce
	}

	c := Coordinator{
		nMap:    len(files),
		nReduce: nReduce,
		wg:      sync.WaitGroup{},
		tasks:   make(chan Work, buflen),
		terms:   make([]int, len(files)),
		done:    false,
	}

	for idx, file := range files {
		c.tasks <- Work{
			WorkType:  MAP,
			Filename:  file,
			FileIndex: idx,
			NReduce:   c.nReduce,
			NMapWork:  c.nMap,
		}
		c.wg.Add(1)
	}
	go StartReduceWork(&c)
	c.server()

	return &c
}
