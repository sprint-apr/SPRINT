package sprint.tracer.key;

import java.util.Arrays;
import java.util.HashSet;
import java.util.SortedMap;
import java.util.TreeMap;

import javassist.CtBehavior;
import javassist.bytecode.BadBytecode;
import javassist.bytecode.CodeIterator;
import javassist.bytecode.MethodInfo;
import static javassist.bytecode.Opcode.*;

public class ConditionalKeyGenerator extends KeyGenerator<Integer> {
  private static HashSet<Integer> ifOpcodes = new HashSet<Integer>(Arrays.asList(
      new Integer[] { IF_ACMPEQ, IF_ACMPNE, IF_ICMPEQ, IF_ICMPGE, IF_ICMPGT, IF_ICMPLE, IF_ICMPLT,
          IF_ICMPNE, IFEQ, IFGE, IFGT, IFLE, IFLT, IFNE, IFNONNULL, IFNULL }));

  private static SortedMap<Integer, Integer> conditionalLineMap = new TreeMap<>();

  public ConditionalKeyGenerator(CtBehavior method) {
    super(method);
    try {
      computeConditionalPositions(method);
    } catch (BadBytecode e) {
      e.printStackTrace();
      System.exit(1);
    }
  }

  private static void computeConditionalPositions(CtBehavior method) throws BadBytecode {
    MethodInfo minfo = method.getMethodInfo();
    CodeIterator ci = minfo.getCodeAttribute().iterator();
    while (ci.hasNext()) {
      int pos = ci.next();
      if (!ifOpcodes.contains(ci.byteAt(pos))) {
        continue;
      }
      conditionalLineMap.put(pos, minfo.getLineNumber(pos));
    }
  }

  @Override
  protected Iterable<Integer> getOrderedElementIterator() {
    return conditionalLineMap.keySet();
  }

  @Override
  protected int getLine(Integer bytepos) {
    return conditionalLineMap.get(bytepos);
  }

  @Override
  protected int getByteIndex(Integer bytepos) {
    return bytepos;
  }
}
