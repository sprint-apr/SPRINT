package sprint.tracer.transformers;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import javassist.CannotCompileException;
import javassist.CtBehavior;
import javassist.CtClass;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.Bytecode;
import javassist.bytecode.CodeAttribute;
import javassist.bytecode.CodeIterator;
import javassist.bytecode.MethodInfo;
import javassist.bytecode.Opcode;
import javassist.compiler.CompileError;
import javassist.compiler.Javac;

public class SwitchTransformer extends AbstractTransformer {
  public SwitchTransformer(File projectRoot, Set<String> projectPackages) {
    super(projectRoot, projectPackages);
  }

  // @Override
  protected void instrument2(Class<?> classBeingRedefined, CtClass cls, CtBehavior method)
      throws BadBytecode, CompileError, CannotCompileException {
    MethodInfo minfo = method.getMethodInfo();
    CodeAttribute ca = minfo.getCodeAttribute();
    List<Integer> switchPositions = new ArrayList<>();

    /* find switch positions */
    CodeIterator ci = ca.iterator();
    while (ci.hasNext()) {
      int pos = ci.next();
      if (ci.byteAt(pos) == Opcode.TABLESWITCH || ci.byteAt(pos) == Opcode.LOOKUPSWITCH) {
        switchPositions.add(pos);
      }
      Collections.reverse(switchPositions);
    }

    for (int pos : switchPositions) {
      Bytecode storeInstr = new Bytecode(ca.getConstPool());
      /* dup. loaded switch value on the stack top */
      storeInstr.add(Bytecode.DUP);
      storeInstr.addPutstatic("sprint.tracer.data.SwitchValue", "probe", "I");
      byte[] bytecode = storeInstr.get();
      ci.move(pos);
      ci.insertEx(bytecode);

      String key = String.format("%s,%d,%d", cls.getName(), minfo.getLineNumber(pos), 0);
      Javac probeCallStmt = new Javac(cls);
      String invokeSrc = String.format("sprint.tracer.data.SwitchValue.record(\"%s\");", key);
      probeCallStmt.compileStmnt((invokeSrc));
      ci.insert(probeCallStmt.getBytecode().get());
    }
  }

  @Override
  protected void instrument(Class<?> classBeingRedefined, CtClass cls, CtBehavior method)
      throws BadBytecode, CompileError, CannotCompileException {
    MethodInfo minfo = method.getMethodInfo();
    CodeAttribute ca = minfo.getCodeAttribute();
    List<Integer> switchPositions = new ArrayList<>();

    /* find switch positions */
    CodeIterator ci = ca.iterator();
    while (ci.hasNext()) {
      int pos = ci.next();
      if (ci.byteAt(pos) == Opcode.TABLESWITCH || ci.byteAt(pos) == Opcode.LOOKUPSWITCH) {
        switchPositions.add(pos);
      }
    }
    Collections.reverse(switchPositions);

    int ssize = 0;
    for (int pos : switchPositions) {
      Bytecode storeInstr = new Bytecode(ca.getConstPool());
      storeInstr.addPutstatic("sprint.tracer.data.SwitchValue", "probe", "I");

      String key = String.format("%s,%d,%d", cls.getName(), minfo.getLineNumber(pos), 0);
      Javac probeCallStmt = new Javac(cls);
      String invokeSrc = String.format("sprint.tracer.data.SwitchValue.record(\"%s\");", key);
      probeCallStmt.compileStmnt((invokeSrc));
      Bytecode getInstr = new Bytecode(ca.getConstPool());
      getInstr.addGetstatic("sprint.tracer.data.SwitchValue", "probe", "I");

      ci.move(pos);
      ci.insert(storeInstr.get());
      ci.insert(probeCallStmt.getBytecode().get());
      ci.insert(getInstr.get());

      ssize += 2;
    }
    ca.setMaxLocals(ca.getMaxLocals() + ssize);
  }

}
