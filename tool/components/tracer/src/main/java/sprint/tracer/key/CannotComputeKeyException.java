package sprint.tracer.key;

public class CannotComputeKeyException extends Exception {
  final public Exception cause;

  public CannotComputeKeyException(Exception cause) {
    this.cause = cause;
  }

}
