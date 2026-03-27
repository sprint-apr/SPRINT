package sprint.tracer.data;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.invoke.MethodHandles;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import sprint.tracer.Config;
import sprint.tracer.key.Context;

public class InvokedMethodClass {
  public static HashMap<String, Set<String>> map = new HashMap<>();

  public static void record(String key, String klass) {
    map.compute(Context.get() + "/" + key, (k, v) -> {
      Set<String> _v = v == null ? new HashSet<String>() : v;
      _v.add(klass);
      return _v;
    });
  }

  public static String getObject(Object o) {
    if (o instanceof Class) {
        String underlyingClassName = ((Class) o).getCanonicalName();
        return "Class@" + underlyingClassName;
    }
    return o.getClass().getName();
  }

  public static void print(File resultsDir) {
    File outFile = new File(resultsDir, MethodHandles.lookup().lookupClass().getSimpleName() + ".csv");
    try {
      BufferedWriter writer = new BufferedWriter(new FileWriter(outFile));
      Set<String> keys = new HashSet<String>();
      keys.addAll(map.keySet());
      for (String key : keys) {
        String row = String.format("%s/%s", key, String.join(",", map.get(key)));
        writer.write(row + "\n");
      }
      writer.close();
    } catch (IOException e) {
      e.printStackTrace();
      System.exit(Config.CANNOT_OPEN_FILE);
    }
  }

}
