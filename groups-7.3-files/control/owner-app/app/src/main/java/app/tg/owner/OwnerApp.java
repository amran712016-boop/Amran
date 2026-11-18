package app.tg.owner;

import android.app.Application;
import android.content.Context;
import android.os.Build;

import java.io.File;
import java.io.FileOutputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;

/**
 * The app as a whole: if it ever stops on an error, the error is written (with the phone and its Android) to
 * crash.txt, and the next time it opens it shows it, with a button to copy it — so it can be sent and fixed.
 */
public class OwnerApp extends Application {
    static final String CRASH_FILE = "crash.txt";

    @Override
    public void onCreate() {
        super.onCreate();
        Thread.UncaughtExceptionHandler before = Thread.getDefaultUncaughtExceptionHandler();
        Thread.setDefaultUncaughtExceptionHandler((thread, error) -> {
            note(this, "توقف التطبيق", error);
            if (before != null) {
                before.uncaughtException(thread, error);
            }
        });
    }

    /** Writes an error for the next start to show (kept short: the newest first, up to 30 KB). */
    static void note(Context context, String what, Throwable error) {
        try {
            StringWriter trace = new StringWriter();
            error.printStackTrace(new PrintWriter(trace));
            String head = what + " · التطبيق " + BuildInfo.VERSION + " · " + Build.MANUFACTURER + " " + Build.MODEL
                + " · Android " + Build.VERSION.RELEASE + " (SDK " + Build.VERSION.SDK_INT + ")\n";
            File file = new File(context.getFilesDir(), CRASH_FILE);
            String old = file.exists() ? new String(java.nio.file.Files.readAllBytes(file.toPath()), StandardCharsets.UTF_8) : "";
            String all = head + trace + (old.isEmpty() ? "" : "\n----------\n" + old);
            if (all.length() > 30000) {
                all = all.substring(0, 30000);
            }
            try (FileOutputStream out = new FileOutputStream(file)) {
                out.write(all.getBytes(StandardCharsets.UTF_8));
            }
        } catch (Throwable ignored) {
            // (nothing more can be done)
        }
    }

    static final class BuildInfo {
        static final String VERSION = "1.2";

        private BuildInfo() {
        }
    }
}
