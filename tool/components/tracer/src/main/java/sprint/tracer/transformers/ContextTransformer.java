package sprint.tracer.transformers;

import java.io.File;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import sprint.tracer.key.InvocationKeyGenerator;
import javassist.CannotCompileException;
import javassist.ClassPool;
import javassist.CtBehavior;
import javassist.CtClass;
import javassist.CtMethod;
import javassist.NotFoundException;
import javassist.bytecode.AccessFlag;
import javassist.bytecode.AnnotationsAttribute;
import javassist.bytecode.AttributeInfo;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.annotation.Annotation;
import javassist.compiler.CompileError;
import javassist.expr.Expr;
import javassist.expr.ExprEditor;
import javassist.expr.Handler;
import javassist.expr.MethodCall;
import javassist.expr.NewExpr;

public class ContextTransformer extends AbstractTransformer {
  final private Set<CtMethod> testMethods;

  private boolean isTestMethod(CtBehavior method) {
    String name = method.getName();
    try {
      if (method.getParameterTypes().length != 0 || !AccessFlag.isPublic(method.getModifiers())) {
        return false;
      }

      List<AttributeInfo> attributeInfos = method.getMethodInfo().getAttributes();
      if (!attributeInfos.isEmpty()) {
        AnnotationsAttribute annots = (AnnotationsAttribute) method.getMethodInfo()
            .getAttribute(AnnotationsAttribute.visibleTag);
        if (annots != null)
          for (Annotation annot : annots.getAnnotations()) {
            if (annot.getTypeName().equals("org.junit.Test"))
              return true;
          }
      }

      return name.startsWith("test") || name.startsWith("Test") || name.endsWith("test") || name.endsWith("Test");
    } catch (NotFoundException e) {
      return false;
    }
  }

  public ContextTransformer(File projectRoot, Set<String> projectPackages, String testClassName)
      throws NotFoundException {
    super(projectRoot, projectPackages);

    this.testMethods = new HashSet<>(Arrays.asList(ClassPool.getDefault().get(testClassName).getMethods()));
  }

  @Override
  protected void instrument(Class<?> classBeingRedefined, CtClass cls, CtBehavior method)
      throws BadBytecode, CompileError, CannotCompileException {
    if (testMethods.contains(method) && isTestMethod(method)) {
      method.instrument(new TestMethodEditor(method));
      method.insertBefore("sprint.tracer.key.Context.drop();");
    }
    method.insertBefore(String.format("sprint.tracer.key.Context.updateCurrentContext(\"%s\");", method.getName()));
  }

  private class TestMethodEditor extends ExprEditor {
    final private InvocationKeyGenerator keyGen;

    public TestMethodEditor(CtBehavior caller) {
      this.keyGen = new InvocationKeyGenerator(caller);
    }

    @Override
    public void edit(MethodCall m) {
      instrument(m);
    }

    @Override
    public void edit(NewExpr e) {
      instrument(e);
    }

    @Override
    public void edit(Handler h) {
      try {
        /* TODO: check this is correct */
        if (h.isFinally()) {
          System.out.println("skip insert drop because of NPE");
        } else {
          h.insertBefore("sprint.tracer.key.Context.drop();");
        }
      } catch (CannotCompileException exn) {
        exn.printStackTrace();
      }
    }

    private void instrument(Expr e) {
      String key = keyGen.compute(e);
      if (key == null) {
        return;
      }
      String append = String.format("sprint.tracer.key.Context.append(\"%s\");", key);
      String drop = String.format("sprint.tracer.key.Context.drop();");

      try {
        e.replace(String.format("%s; $_ = $proceed($$); %s;", append, drop));
      } catch (CannotCompileException exn) {
        exn.printStackTrace();
      }
    }
  }
}