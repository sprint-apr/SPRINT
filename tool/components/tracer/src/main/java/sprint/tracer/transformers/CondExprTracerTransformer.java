package sprint.tracer.transformers;

import static javassist.bytecode.Opcode.IFEQ;
import static javassist.bytecode.Opcode.IFGE;
import static javassist.bytecode.Opcode.IFGT;
import static javassist.bytecode.Opcode.IFLE;
import static javassist.bytecode.Opcode.IFLT;
import static javassist.bytecode.Opcode.IFNE;
import static javassist.bytecode.Opcode.IFNONNULL;
import static javassist.bytecode.Opcode.IFNULL;
import static javassist.bytecode.Opcode.IF_ACMPEQ;
import static javassist.bytecode.Opcode.IF_ACMPNE;
import static javassist.bytecode.Opcode.IF_ICMPEQ;
import static javassist.bytecode.Opcode.IF_ICMPGE;
import static javassist.bytecode.Opcode.IF_ICMPGT;
import static javassist.bytecode.Opcode.IF_ICMPLE;
import static javassist.bytecode.Opcode.IF_ICMPLT;
import static javassist.bytecode.Opcode.IF_ICMPNE;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import javassist.CannotCompileException;
import javassist.CtBehavior;
import javassist.CtClass;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.CodeAttribute;
import javassist.bytecode.CodeIterator;
import javassist.bytecode.MethodInfo;
import javassist.compiler.CompileError;
import javassist.compiler.Javac;

public class CondExprTracerTransformer extends AbstractTransformer {
	private static HashSet<Integer> ifOpcodes = new HashSet<Integer>(Arrays.asList(
			new Integer[] { IF_ACMPEQ, IF_ACMPNE, IF_ICMPEQ, IF_ICMPGE, IF_ICMPGT, IF_ICMPLE, IF_ICMPLT,
					IF_ICMPNE, IFEQ, IFGE, IFGT, IFLE, IFLT, IFNE, IFNONNULL, IFNULL }));

	public CondExprTracerTransformer(File projectRoot, Set<String> projectPackages) {
		super(projectRoot, projectPackages);
	}

	@Override
	protected void instrument(Class<?> classBeingRedefined, CtClass cls, CtBehavior method)
			throws BadBytecode, CompileError, CannotCompileException {

		MethodInfo minfo = method.getMethodInfo();
		CodeAttribute ca = minfo.getCodeAttribute();

		SortedMap<Integer, String> ifKeyMap = new TreeMap<>();
		int currentVistingLine = 0;
		int ifCount = 0;
		CodeIterator ci = ca.iterator();
		while (ci.hasNext()) {
			int pos = ci.next();
			int opcode = ci.byteAt(pos);
			if (!ifOpcodes.contains(opcode)) {
				continue;
			}

			int curLine = minfo.getLineNumber(pos);
			if (curLine != currentVistingLine) {
				currentVistingLine = curLine;
				ifCount = 0;
			}

			String key = String.format("%s,%d,%d", cls.getName(), curLine, ifCount++);
			ifKeyMap.put(pos, key);
		}

		List<Entry<Integer, String>> entries = new ArrayList<>(ifKeyMap.entrySet());
		Collections.reverse(entries);

		int ssize_incr = 0;
		for (Entry<Integer, String> entry : entries) {
			int pos = entry.getKey();
			Javac javac = new Javac(cls);
			String nojumpCode = String.format("sprint.tracer.data.BranchTaken.nojump(\"%s\");", entry.getValue());
			javac.compileStmnt(nojumpCode);
			ci.move(pos);
			ci.next();
			ci.insertEx(javac.getBytecode().get());
			Javac javac2 = new Javac(cls);
			String initCode = String.format("sprint.tracer.data.BranchTaken.init(\"%s\");", entry.getValue());
			javac2.compileStmnt(initCode);
			ci.insertAt(pos, javac2.getBytecode().get());

			ssize_incr += 2;
		}

		ca.setMaxStack(ca.getMaxStack() + ssize_incr);
	}
}