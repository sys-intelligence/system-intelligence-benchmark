package edu.uchicago.cs.systems.wasabi;

class InjectionPoint {

  public StackSnapshot stackSnapshot = null;
  public String retrySourceLocation = null;
  public String retryCallerFunction = null;
  public String injectionSite = null;
  public String retryException = null;
  public Integer injectionCount = 0;

  public InjectionPoint(StackSnapshot stackSnapshot, 
                        String retrySourceLocation,
                        String retryCallerFunction,
                        String injectionSite,
                        String retryException,
                        Integer injectionCount) {
    this.stackSnapshot = stackSnapshot;
    this.retrySourceLocation = retrySourceLocation;
    this.retryCallerFunction = retryCallerFunction;
    this.injectionSite = injectionSite;
    this.retryException = retryException;
    this.injectionCount = injectionCount;
    }

  public Boolean isEmpty() {
    return (
      this.stackSnapshot.isNullOrEmpty() &&
      this.retrySourceLocation == null && 
      this.retryCallerFunction == null &&
      this.injectionSite == null &&
      this.retryException == null
    );
  }
}