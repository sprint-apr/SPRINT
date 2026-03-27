package sprint.tracer.key;

import java.util.ArrayList;
import java.util.List;

import javassist.CannotCompileException;
import javassist.CtBehavior;
import javassist.expr.Expr;
import javassist.expr.ExprEditor;
import javassist.expr.MethodCall;
import javassist.expr.NewExpr;

public class InvocationKeyGenerator extends KeyGenerator<Expr> {
  public InvocationKeyGenerator(CtBehavior method) {
    super(method);
  }

  @Override
  protected Iterable<Expr> getOrderedElementIterator() {
    Visitor visitor = new Visitor();
    try {
      method.instrument(visitor);
    } catch (CannotCompileException e) {
      /* No-op visitors. CCE cannot happen */
      assert (false);
    }
    return visitor.invokes;
  }

  @Override
  protected int getLine(Expr m) {
    return m.getLineNumber();
  }

  private class Visitor extends ExprEditor {
    public List<Expr> invokes = new ArrayList<>();

    @Override
    public void edit(MethodCall methodCall) {
      invokes.add(methodCall);
    }

    @Override
    public void edit(NewExpr newExpr) {
      invokes.add(newExpr);
    }
  }

  @Override
  protected int getByteIndex(Expr expr) {
    return expr.indexOfBytecode();
  }
}
