package sprint.tracer.transformers;

import java.io.File;
import java.util.Set;

import javassist.CannotCompileException;
import javassist.CtBehavior;
import javassist.CtClass;
import javassist.bytecode.BadBytecode;
import javassist.compiler.CompileError;
import javassist.expr.ExprEditor;
import javassist.expr.Handler;

public class CatchTransformer extends AbstractTransformer {

  public CatchTransformer(File projectRoot, Set<String> projectPackages) {
    super(projectRoot, projectPackages);
  }

  @Override
  protected void instrument(Class<?> classBeingRedefined, CtClass cls, CtBehavior method)
      throws BadBytecode, CompileError, CannotCompileException {
    method.instrument(new CatchEditor());
  }

  private class CatchEditor extends ExprEditor {
    @Override
    public void edit(Handler h) {
      String classname = h.getEnclosingClass().getName();
      int lineNo = h.getLineNumber();
      String key = String.format("%s,%d", classname, lineNo);
      if (h.isFinally())
        return;
      try {
        h.insertBefore(String.format("sprint.tracer.data.Catched.record(\"%s\");", key));
      } catch (CannotCompileException exn) {
        exn.printStackTrace();
      }
      catch (NullPointerException exn) {
        System.out.println("failed to edit " + classname + ": " + lineNo);
      }
    }
  }

}
