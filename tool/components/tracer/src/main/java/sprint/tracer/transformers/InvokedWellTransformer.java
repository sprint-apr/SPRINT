package sprint.tracer.transformers;

import java.io.File;
import java.util.Set;

import sprint.tracer.key.InvocationKeyGenerator;
import javassist.CannotCompileException;
import javassist.CtBehavior;
import javassist.CtClass;
import javassist.bytecode.BadBytecode;
import javassist.compiler.CompileError;
import javassist.expr.ExprEditor;
import javassist.expr.MethodCall;
import javassist.expr.NewExpr;


public class InvokedWellTransformer extends AbstractTransformer {
  public InvokedWellTransformer(File projectRoot, Set<String> projectPackages) {
    super(projectRoot, projectPackages);
  }

  @Override
  protected void instrument(Class<?> classBeingRedefined, CtClass cls, CtBehavior method)
      throws BadBytecode, CompileError, CannotCompileException {
    method.instrument(new InvocationEditor(method));
  }

  private class InvocationEditor extends ExprEditor {
    final private InvocationKeyGenerator keyGen;

    public InvocationEditor(CtBehavior caller) {
      this.keyGen = new InvocationKeyGenerator(caller);
    }

    @Override
    public void edit(MethodCall m) {
      String key = keyGen.compute(m);

      if (key == null) {
        return;
      }
      String toInvokeBefore = String.format(
          "sprint.tracer.data.InvokedWell.init(\"%s\", sprint.tracer.data.InvokedWell.isNullable($0));", key);
      String toInvokeAfter = String.format("sprint.tracer.data.InvokedWell.completed(\"%s\");",
          key);
      try {
        m.replace(String.format("%s; $_ = $proceed($$); %s;", toInvokeBefore, toInvokeAfter));
      } catch (CannotCompileException e) {
        e.printStackTrace();
      }
    }

    @Override
    public void edit(NewExpr m) {
      String key = keyGen.compute(m);

      if (key == null) {
        return;
      }
      String toInvokeBefore = String.format(
          "sprint.tracer.data.InvokedWell.init(\"%s\", sprint.tracer.data.InvokedWell.isNullable($0));", key);
      String toInvokeAfter = String.format("sprint.tracer.data.InvokedWell.completed(\"%s\");", key);
      try {
        m.replace(String.format("%s; $_ = $proceed($$); %s;", toInvokeBefore, toInvokeAfter));
      } catch (CannotCompileException e) {
        e.printStackTrace();
      }
    }
  }

}
