package edu.uchicago.cs.systems.wasabi;

// A simple interface for runnables that can hold a WasabiContext object
public interface WasabiContextHolder {
    public void setWasabiContext(WasabiContext ctx);
    public WasabiContext getWasabiContext();
  }