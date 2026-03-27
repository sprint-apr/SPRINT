package sprint.tracer.key;

public class Context {
  private final static String empty = "\"\"";

  private static String curCtx = empty;
  private static String invocationSite = empty;

  public static void append(String ctx) {
    invocationSite = ctx;
  }

  public static void drop() {
    curCtx = empty;
    invocationSite = empty;
  }

  public static void updateCurrentContext(String methodName) {
    curCtx = invocationSite;
  }

  public static void clean() {
    curCtx = empty;
  }

  public static String get() {
    return curCtx;
  }
}