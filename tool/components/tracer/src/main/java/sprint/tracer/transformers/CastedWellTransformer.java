package sprint.tracer.transformers;

import java.io.File;
import java.util.Set;

import javassist.bytecode.Opcode;

public class CastedWellTransformer extends WellExecutedTransformer {

  public CastedWellTransformer(File projectRoot, Set<String> projectPackages) {
    super(projectRoot, projectPackages);
  }

  protected boolean hasInterestingOpcode(int opcode) {
    return opcode == Opcode.CHECKCAST;
  }

  protected String getInitCall(String clsName, int line) {
    return String.format("sprint.tracer.data.CastedWell.init(\"%s,%d\");", clsName, line);
  }

  protected String getCompleteCall(String clsName, int line) {
    return String.format("sprint.tracer.data.CastedWell.completed(\"%s,%d\");", clsName, line);
  }
}