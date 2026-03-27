package sprint.tracer.transformers;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Set;

import javassist.CannotCompileException;
import javassist.CtBehavior;
import javassist.CtClass;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.CodeAttribute;
import javassist.bytecode.CodeIterator;
import javassist.bytecode.MethodInfo;
import javassist.compiler.CompileError;

public abstract class WellExecutedTransformer extends AbstractTransformer {
  protected abstract boolean hasInterestingOpcode(int opcode);

  protected abstract String getInitCall(String clsName, int line);

  protected abstract String getCompleteCall(String clsName, int line);

  public WellExecutedTransformer(File projectRoot, Set<String> projectPackages) {
    super(projectRoot, projectPackages);
  }

  @Override
  protected void instrument(Class<?> classBeingRedefined, CtClass cls, CtBehavior method)
      throws BadBytecode, CompileError, CannotCompileException {
    /* skip class initializer to avoid method length explosion for Math-20 */
    if (method.getMethodInfo().isStaticInitializer()) {
      return;
    }

    MethodInfo minfo = method.getMethodInfo();
    CodeAttribute ca = minfo.getCodeAttribute();
    CodeIterator ci = ca.iterator();
    ArrayList<Integer> positions = new ArrayList<Integer>();
    while (ci.hasNext()) {
      int pos = ci.next();
      if (hasInterestingOpcode(ci.byteAt(pos)))
        positions.add(pos);

    }

    int ssize_incr = 0;
    String clsName = cls.getName();
    Collections.reverse(positions);
    for (int pos : positions) {
      ci.move(pos);
      ci.next();
      ci.insertEx(compileJavac(cls, getCompleteCall(clsName, minfo.getLineNumber(pos))));
      ci.insertAt(pos, compileJavac(cls, getInitCall(clsName, minfo.getLineNumber(pos))));
      ssize_incr += 2;
    }
    ca.setMaxStack(ca.getMaxStack() + ssize_incr);

  }
}
