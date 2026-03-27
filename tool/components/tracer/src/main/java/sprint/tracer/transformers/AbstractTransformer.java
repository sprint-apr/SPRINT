package sprint.tracer.transformers;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.lang.instrument.ClassFileTransformer;
import java.security.ProtectionDomain;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javassist.CannotCompileException;
import javassist.ClassPool;
import javassist.CtBehavior;
import javassist.CtClass;
import javassist.Modifier;
import javassist.NotFoundException;
import javassist.bytecode.BadBytecode;
import javassist.compiler.CompileError;
import javassist.compiler.Javac;
import sprint.tracer.Config;
import sprint.tracer.key.Context;

public abstract class AbstractTransformer implements ClassFileTransformer {
  final ClassPool cp = ClassPool.getDefault();

  final File projectRoot;
  final Set<String> projectPackages;
  final boolean excludeLibraries;

  final File resultsDir;

  final boolean debug;

  final static ArrayList<String> blacklist = new ArrayList<String>();
  final static Map<String, byte[]> originalBytecodes = new HashMap<>();

  protected final Logger logger = LoggerFactory.getLogger(getClass().getName());

  private AbstractTransformer(
      File projectRoot,
      boolean excludeLibraries,
      Set<String> projectPackages,
      boolean debug) {
    this.projectRoot = projectRoot;
    this.projectPackages = projectPackages;
    this.excludeLibraries = excludeLibraries;

    this.resultsDir = Config.sprint_RESULTS_DIR;
    this.debug = debug;
  }

  public AbstractTransformer(File projectRoot, Set<String> projectPackages) {
    this(projectRoot, true, projectPackages, Config.DEBUG_MODE);
    Context.clean();
  }

  public byte[] transform(
      ClassLoader loader,
      String className,
      Class<?> classBeingRedefined,
      ProtectionDomain protectionDomain,
      byte[] classfileBuffer) {

    String pkg = className.replace('/', '.').substring(0, className.lastIndexOf('/'));
    if (!projectPackages.contains(pkg) || pkg.equals("sprint"))
      return classfileBuffer;

    CtClass cls = null;
    try {
      if (className.contains("$$")) {
        return classfileBuffer;
      }
      cls = cp.get(className.replace("/", "."));
    } catch (NotFoundException e) {
      e.printStackTrace();
      System.exit(Config.CLASS_NOT_FOUND);
    }

    if (!projectPackages.contains(cls.getPackageName()))
      return classfileBuffer;

    if (!originalBytecodes.containsKey(className)) {
      originalBytecodes.put(className, classfileBuffer);
    }

    if (blacklist.contains(className)) {
      return originalBytecodes.get(className);
    }

    for (CtBehavior method : cls.getDeclaredBehaviors()) {
      try {
        if (method.getMethodInfo().getCodeAttribute() == null) {
          assert (Modifier.isAbstract(cls.getModifiers()) || cls.isInterface());
          continue;
        }
        instrument(classBeingRedefined, cls, method);
      } catch (Exception e) {
        this.logger.warn("Could not instrument " + method.getLongName());
        blacklist.add(className);
        return originalBytecodes.get(className);
      }
    }

    try {
      cls.rebuildClassFile();
      classfileBuffer = cls.toBytecode();
    } catch (Exception e) {
      e.printStackTrace();
      System.exit(Config.CLASS_CANNOT_CONVERTED);
    }

    if (this.debug) {
      File outFile = new File("./sprint-out" + "/" + className.replace('/', '.') + ".class");
      try (FileOutputStream outputStream = new FileOutputStream(outFile)) {
        outputStream.write(classfileBuffer);
      } catch (IOException e) {
        e.printStackTrace();
        System.exit(Config.CANNOT_OPEN_FILE);
      }
    }

    cls.defrost();

    return classfileBuffer;
  }

  protected byte[] compileJavac(CtClass cls, String snippet) throws CompileError {
    Javac javac = new Javac(cls);
    javac.compileStmnt(snippet);
    return javac.getBytecode().get();
  }

  protected abstract void instrument(Class<?> classBeingRedefined, CtClass cls, CtBehavior method)
      throws BadBytecode, CompileError, CannotCompileException;

}