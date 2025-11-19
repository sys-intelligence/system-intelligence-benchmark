package edu.uchicago.cs.systems.wasabi;

import java.util.Random;

abstract class InjectionPolicy {

  public abstract boolean shouldInject(int injectionCount);
}

class NoInjection extends InjectionPolicy {
  @Override
  public boolean shouldInject(int injectionCount) {
    return false;
  }
}

class InjectForever extends InjectionPolicy {
  @Override
  public boolean shouldInject(int injectionCount) {
    return true;
  }
}

class InjectUpToMaxCount extends InjectionPolicy {
  private int maxInjectionCount = 0;

  InjectUpToMaxCount(int maxInjectionCount) {
    this.maxInjectionCount = maxInjectionCount;
  }

  @Override
  public boolean shouldInject(int injectionCount) {
    if (injectionCount < this.maxInjectionCount) {
      return true;
    }
    return false;
  }
}
