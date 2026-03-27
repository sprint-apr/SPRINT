package sprint.tracer.transformers;

import java.io.File;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

import javassist.bytecode.Opcode;

public class ArrayAccessedWellTransformer extends WellExecutedTransformer {

  public ArrayAccessedWellTransformer(File projectRoot, Set<String> projectPackages) {
    super(projectRoot, projectPackages);
  }

  protected static List<Integer> OPCODES = Arrays.asList(new Integer[] {
      Opcode.AALOAD, Opcode.AASTORE, Opcode.BALOAD, Opcode.BASTORE, Opcode.CALOAD, Opcode.CASTORE, Opcode.DALOAD,
      Opcode.SALOAD, Opcode.DASTORE, Opcode.FALOAD, Opcode.FASTORE, Opcode.IALOAD, Opcode.IASTORE, Opcode.LALOAD,
      Opcode.LASTORE, Opcode.SASTORE
  });

  protected boolean hasInterestingOpcode(int opcode) {
    return OPCODES.contains(opcode);
  }

  protected String getInitCall(String clsName, int line) {
    return String.format("sprint.tracer.data.ArrayAccessedWell.init(\"%s,%d\");", clsName, line);
  }

  protected String getCompleteCall(String clsName, int line) {
    return String.format("sprint.tracer.data.ArrayAccessedWell.completed(\"%s,%d\");", clsName, line);
  }
}
