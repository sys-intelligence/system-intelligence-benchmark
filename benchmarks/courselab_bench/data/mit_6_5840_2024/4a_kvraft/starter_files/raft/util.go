package raft

import (
	"log"
	"os"
)

// Debugging
var Debug = os.Getenv("DEBUG") == "1"

func DPrintf(format string, a ...interface{}) {
	if !Debug {
		return
	}
	log.Printf(format, a...)
}
