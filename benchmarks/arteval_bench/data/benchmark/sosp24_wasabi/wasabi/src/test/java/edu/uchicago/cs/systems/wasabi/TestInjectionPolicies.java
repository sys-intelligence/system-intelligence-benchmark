package edu.uchicago.cs.systems.wasabi;

import java.util.ArrayList;
import edu.uchicago.cs.systems.wasabi.StackSnapshot;

import static org.junit.Assert.*;
import org.junit.Test;

public class TestInjectionPolicies {
  
  int fakeCount = 1;
  int fakeBound = 2;

  @Test
  public void testNoInjectionPolicy() {
    InjectionPolicy policy = new NoInjection();
    assertFalse(policy.shouldInject(this.fakeCount));
  }

  @Test
  public void testInjectForeverPolicy() {
    InjectionPolicy policy = new InjectForever();
    assertTrue(policy.shouldInject(this.fakeCount));
  }

  @Test
  public void testInjectUpToMaxCountPolicy() {
    InjectionPolicy policy = new InjectUpToMaxCount(this.fakeBound);
    assertTrue(policy.shouldInject(this.fakeCount));
    assertFalse(policy.shouldInject(this.fakeCount + this.fakeBound));
  }
}
