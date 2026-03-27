package sprint.tracer.transformers;

import java.io.File;
import java.lang.reflect.Modifier;
import java.util.Set;

import sprint.tracer.key.InvocationKeyGenerator;
import javassist.CannotCompileException;
import javassist.CtBehavior;
import javassist.CtClass;
import javassist.NotFoundException;
import javassist.bytecode.BadBytecode;
import javassist.compiler.CompileError;
import javassist.expr.ExprEditor;
import javassist.expr.MethodCall;
import javassist.expr.NewExpr;

public class InvocationTracerTransformer extends AbstractTransformer {
  public InvocationTracerTransformer(File projectRoot, Set<String> projectPackages) {
    super(projectRoot, projectPackages);
  }

  @Override
  protected void instrument(Class<?> classBeingRedefined, CtClass cls, CtBehavior method)
      throws BadBytecode, CompileError, CannotCompileException {
    method.instrument(new InvokedMethodClassEditor(method));
    /** Insert InvokedMethodSet recorder **/
    method.insertBefore(String.format("sprint.tracer.data.InvokedMethodSet.record(\"%s\");",
        method.getLongName()));
  }

  private class InvokedMethodClassEditor extends ExprEditor {
    final private InvocationKeyGenerator keyGen;
    final private boolean isInClassInitializer;

    public InvokedMethodClassEditor(CtBehavior caller) {
      this.keyGen = new InvocationKeyGenerator(caller);
      this.isInClassInitializer = caller.getName().equals("<clinit>");
    }

    @Override
    public void edit(NewExpr m) {
      keyGen.compute(m);
    }

    @Override
    public void edit(MethodCall m) {
      String key = keyGen.compute(m);
      if (key == null) {
        return;
      }
      String toInvoke = String.format("sprint.tracer.data.InvokedMethodClass.record(\"%s\", %s);", key,
          "sprint.tracer.data.InvokedMethodClass.getObject($0)");
      try {
        if (isInClassInitializer && m.getMethodName().equals("valueOf")) {
          // This is a guard for very long array initialization in class initializers,
          // e.g., Jsoup-24).
          return;
        }
        if (Modifier.isStatic(m.getMethod().getModifiers()))
          return;
        m.replace(String.format("%s; $_ = $proceed($$);", toInvoke));
      } catch (CannotCompileException e) {
        e.printStackTrace();
      } catch (NotFoundException e) {
        e.printStackTrace();
      }
    }
  }
}
