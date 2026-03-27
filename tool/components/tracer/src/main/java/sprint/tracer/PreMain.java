package sprint.tracer;

import java.io.File;
import java.lang.instrument.Instrumentation;
import java.util.HashSet;

import org.apache.commons.io.FileUtils;

import sprint.tracer.data.ArrayAccessedWell;
import sprint.tracer.data.BranchTaken;
import sprint.tracer.data.CastedWell;
import sprint.tracer.data.Catched;
import sprint.tracer.data.InvokedMethodClass;
import sprint.tracer.data.InvokedMethodSet;
import sprint.tracer.data.InvokedWell;
import sprint.tracer.data.SwitchValue;
import sprint.tracer.transformers.ArrayAccessedWellTransformer;
import sprint.tracer.transformers.CastedWellTransformer;
import sprint.tracer.transformers.CatchTransformer;
import sprint.tracer.transformers.CondExprTracerTransformer;
import sprint.tracer.transformers.ContextTransformer;
import sprint.tracer.transformers.InvocationTracerTransformer;
import sprint.tracer.transformers.InvokedWellTransformer;
import sprint.tracer.transformers.SwitchTransformer;

public class PreMain {
	public static void premain(String agentArgs, Instrumentation inst) {
		HashSet<String> packages = new HashSet<>();

		String[] args = agentArgs.split(",");

		File projectRoot = new File(args[0]);
		String testClass = args[1];

		String pattern = resolveTargetDirPattern(projectRoot);
		for (File cls : FileUtils.listFiles(projectRoot, new String[] { "class" }, true)) {
			String stripped = cls.getAbsolutePath().replaceAll(pattern, "");
			try {
				String pkg = stripped.substring(0, stripped.lastIndexOf("/")).replace("/", ".");
				packages.add(pkg);
			} catch (StringIndexOutOfBoundsException e) {
				packages.add(stripped);
			}
		}

		System.out.println("Target Dir Pattern: " + pattern);
		System.out.println("Collected packages: " + packages);
		System.out.println("Test class: " + testClass);

		try {
			inst.addTransformer(new InvokedWellTransformer(projectRoot, packages));
			inst.addTransformer(new CondExprTracerTransformer(projectRoot, packages));
			inst.addTransformer(new InvocationTracerTransformer(projectRoot, packages));
			inst.addTransformer(new CatchTransformer(projectRoot, packages));
			inst.addTransformer(new ContextTransformer(projectRoot, packages, testClass));
			inst.addTransformer(new SwitchTransformer(projectRoot, packages));
			inst.addTransformer(new ArrayAccessedWellTransformer(projectRoot, packages));
			inst.addTransformer(new CastedWellTransformer(projectRoot, packages));
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException(e);
		}
		Runtime.getRuntime().addShutdownHook(new ShutdownHookThread(testClass));
	}

	private static String resolveTargetDirPattern(File root) {
		if (new File(root, "target/classes").isDirectory()) {
			return ".*/target/[^/]+/";
		} else if (new File(root, "build/classes/main").isDirectory()) {
			return ".*/build/classes/[^/]+/";
		} else if (new File(root, "build/classes").isDirectory()) {
			return ".*/build/[^/]+/";
		} else if (new File(root, "build").isDirectory() && new File(root, "build-tests").isDirectory()) {
			return ".*/build[^/]*/";
		}
		return ".*/target/.*classes/";
	}

}

class ShutdownHookThread extends Thread {
	String testClassName;

	public ShutdownHookThread(String testClassName) {
		super();
		this.testClassName = testClassName;
	}

	public void run() {
		try {
			File resultsDir = new File(Config.sprint_RESULTS_DIR, this.testClassName);
			resultsDir.mkdirs();
			BranchTaken.print(resultsDir);
			InvokedMethodClass.print(resultsDir);
			InvokedMethodSet.print(resultsDir);
			SwitchValue.print(resultsDir);
			ArrayAccessedWell.print(resultsDir);
			CastedWell.print(resultsDir);
			InvokedWell.print(resultsDir);
			Catched.print(resultsDir);
		} catch (Exception e) {
			e.printStackTrace();
			System.exit(-1);
		}
	}
}