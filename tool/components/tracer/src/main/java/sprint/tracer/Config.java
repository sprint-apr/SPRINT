package sprint.tracer;

import java.io.File;
import java.util.Map;

public class Config {
	public static final int INSTRUMENT_FAILURE = -100;
	public static final int CLASS_NOT_FOUND = -101;
	public static final int CLASS_CANNOT_CONVERTED = -102;
	public static final int CANNOT_OPEN_FILE = -103;

	public static final String sprint_RESULTS_DIRNAME = "sprint-out";
	public static final File sprint_RESULTS_DIR = new File(sprint_RESULTS_DIRNAME);
	public static final Map<String, String> ENVIRONMENT = System.getenv();
	public static final boolean DEBUG_MODE = Boolean.parseBoolean(ENVIRONMENT.getOrDefault("TRACER_DEBUG", "false"));
}
