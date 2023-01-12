package jvmstd;

public abstract class Either {
  private Either() {}

  public final static class Left extends Either {
    public final Object value;

    public Left(Object value) { this.value = value; }
  }

  public final static class Right extends Either {
    public final Object value;
    
    public Right(Object value) { this.value = value; }
  }
}
