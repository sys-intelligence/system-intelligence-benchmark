package edu.uchicago.cs.systems.wasabi;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.stream.Collectors;

class StackSnapshot {
  private ArrayList<String> stacktrace;

  public StackSnapshot() {
    this.stacktrace = new ArrayList<String>();

    StackTraceElement[] ste = Thread.currentThread().getStackTrace();
    for (StackTraceElement frame : ste) {
      if (!frame.toString().contains("edu.uchicago.cs.systems.wasabi") && 
          !frame.toString().contains("java.lang.Thread.getStackTrace(Thread.java:")) {
        this.stacktrace.add(frame.toString());
      }
    }
  }

  public StackSnapshot(ArrayList<String> stacktrace) {
    this.stacktrace = stacktrace;
  }

  public int getSize() {
    return this.stacktrace.size();
  }
  
  public Boolean isNullOrEmpty() {
    return this.stacktrace == null || this.stacktrace.isEmpty();
  }
  
  public String toString() {
    return this.stacktrace.stream().map(frame -> "\t" + frame).collect(Collectors.joining("\n"));
  }

  public ArrayList<String> getStacktrace() {
    return this.stacktrace;
  }

  public String serializeTopFrames(int maxLevel) {
    ArrayList<String> topOfStack = new ArrayList<String>();
    int level = 0;

    for (String frame : this.stacktrace) {
      if (++level > maxLevel) {
        break;
      }
      topOfStack.add(frame);
    }

    return topOfStack.stream().map(frame -> "\t" + frame).collect(Collectors.joining("\n"));
  }

  public String getFrame(int index) {
    if (index >= 0 && index < this.stacktrace.size()) {
      return stacktrace.get(index);
    }
    return null;
  }

  public Boolean hasFrame(String target) {
    return this.stacktrace.stream().anyMatch(frame -> frame.contains(target));
  }

  public Boolean isEqual(StackSnapshot target) {
    if (target.isNullOrEmpty()) {
      return false;
    }

    if (this.stacktrace.size() != target.stacktrace.size()) {
      return false;
    }

    for (int i = 0; i < this.stacktrace.size(); ++i) {
      if (!this.stacktrace.get(i).equals(target.stacktrace.get(i))) {
        return false;
      }
    }

    return true;
  }

  public ArrayList<String> normalizeStackBelowFrame(String target) {
    ArrayList<String> normalizedStack = new ArrayList<String>();
    Boolean targetFound = false;

    for (String frame : stacktrace) {
      if (frame.contains(target)) {
        targetFound = true;
        normalizedStack.add(target);
        continue;
      } 
      
      if (targetFound) {
        normalizedStack.add(frame);
      }
    }

    return normalizedStack;
  }

  public static String getQualifiedName(String frame) {
    return frame != null ? frame.split("\\(")[0] : null;
  }
}
