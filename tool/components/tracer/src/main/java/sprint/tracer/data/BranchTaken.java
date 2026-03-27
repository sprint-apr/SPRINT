package sprint.tracer.data;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.invoke.MethodHandles;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import sprint.tracer.Config;
import sprint.tracer.key.Context;

public class BranchTaken {
  public enum STATE {
    I {
      public STATE init() {
        return T;
      }

      public STATE nojump() {
        return F;
      }

      public Set<STATE> toSet() {
        return Collections.singleton(this);
      }
    },
    F {
      public STATE init() {
        return FI;
      }

      public STATE nojump() {
        throw new IllegalStateException("Illegal state transition");
      }

      public Set<STATE> toSet() {
        return Collections.singleton(this);
      }
    },
    T {
      public STATE init() {
        return TI;
      }

      public STATE nojump() {
        return FT;
      }

      public Set<STATE> toSet() {
        return Collections.singleton(this);
      }
    },
    FI {
      public STATE init() {
        return FT;
      }

      public STATE nojump() {
        return F;
      }

      public Set<STATE> toSet() {
        return new HashSet<>(Arrays.asList(new STATE[] { F, I }));
      }
    },
    FT {
      public STATE init() {
        return FT;
      }

      public STATE nojump() {
        return FT;
      }

      public Set<STATE> toSet() {
        return new HashSet<>(Arrays.asList(new STATE[] { F, T }));
      }
    },
    TI {
      public STATE init() {
        return TI;
      }

      public STATE nojump() {
        return FT;
      }

      public Set<STATE> toSet() {
        return new HashSet<>(Arrays.asList(new STATE[] { T, I }));
      }
    };

    public abstract STATE init();

    public abstract STATE nojump();

    public abstract Set<STATE> toSet();

    public Set<String> toStringSet() {
      return this.toSet().stream().map(s -> s.toString()).collect(Collectors.toSet());
    }
  };

  public static ConcurrentHashMap<String, STATE> map = new ConcurrentHashMap<>();

  public static void init(String key) {
    map.compute(Context.get() + "/" + key, (k, v) -> v == null ? STATE.I : v.init());
  }

  public static void nojump(String key) {
    map.compute(Context.get() + "/" + key, (k, v) -> v.nojump());
  }

  public static void print(File resultsDir) {
    File outFile = new File(resultsDir, MethodHandles.lookup().lookupClass().getSimpleName() + ".csv");

    try {
      BufferedWriter writer = new BufferedWriter(new FileWriter(outFile));
      for (Entry<String, STATE> entry : map.entrySet()) {
        String row = String.format("%s/%s", entry.getKey(), String.join(",", entry.getValue().toStringSet()));
        writer.write(row + "\n");
      }
      writer.close();
    } catch (IOException e) {
      e.printStackTrace();
      System.exit(Config.CANNOT_OPEN_FILE);
    }
  }
}
