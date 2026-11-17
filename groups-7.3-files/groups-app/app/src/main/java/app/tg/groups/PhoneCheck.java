package app.tg.groups;

import android.app.ActivityManager;
import android.content.Context;
import android.content.pm.PackageInfo;
import android.os.BatteryManager;
import android.os.Build;
import android.os.PowerManager;
import android.provider.Settings;
import android.webkit.WebView;

import org.json.JSONObject;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;

/**
 * «اختبار قدرة الهاتف»: what the phone has and how it is now (memory, processor, its WebView, heat, battery,
 * and whether the app may keep working in the background). The panel weighs these, with a short speed test of
 * its own, and says how many accounts the phone can run at the same time.
 */
final class PhoneCheck {
    private PhoneCheck() {
    }

    static String report(Context context) {
        JSONObject out = new JSONObject();
        try {
            out.put("in_app", true);
            out.put("model", (Build.MANUFACTURER + " " + Build.MODEL).trim());
            out.put("android", Build.VERSION.RELEASE);
            out.put("sdk", Build.VERSION.SDK_INT);

            ActivityManager manager = (ActivityManager) context.getSystemService(Context.ACTIVITY_SERVICE);
            if (manager != null) {
                ActivityManager.MemoryInfo memory = new ActivityManager.MemoryInfo();
                manager.getMemoryInfo(memory);
                out.put("ram_total_mb", memory.totalMem / (1024 * 1024));
                out.put("ram_avail_mb", memory.availMem / (1024 * 1024));
                out.put("ram_low", memory.lowMemory);
                out.put("low_ram_device", manager.isLowRamDevice());
            }
            out.put("cores", Runtime.getRuntime().availableProcessors());
            out.put("max_mhz", maxCpuMhz());

            PackageInfo webView = WebView.getCurrentWebViewPackage();
            out.put("webview", webView != null ? String.valueOf(webView.versionName) : "");
            out.put("profiles", BrowserHost.profilesSupported());
            out.put("browsers_open", BrowserHost.count());

            PowerManager power = (PowerManager) context.getSystemService(Context.POWER_SERVICE);
            if (power != null) {
                out.put("power_save", power.isPowerSaveMode());
                out.put("battery_free", power.isIgnoringBatteryOptimizations(context.getPackageName()));
                out.put("thermal", Build.VERSION.SDK_INT >= 29 ? power.getCurrentThermalStatus() : -1);
            }
            BatteryManager battery = (BatteryManager) context.getSystemService(Context.BATTERY_SERVICE);
            if (battery != null) {
                out.put("battery", battery.getIntProperty(BatteryManager.BATTERY_PROPERTY_CAPACITY));
                out.put("charging", battery.isCharging());
            }
            out.put("overlay", Settings.canDrawOverlays(context));
        } catch (Exception e) {
            try {
                out.put("error", e.getClass().getSimpleName());
            } catch (Exception ignored) {
                // (what was read so far is still sent)
            }
        }
        return out.toString();
    }

    /** The fastest core's top speed, in MHz (0 when the phone does not say). */
    static long maxCpuMhz() {
        long best = 0;
        for (int i = 0; i < 16; i++) {
            File file = new File("/sys/devices/system/cpu/cpu" + i + "/cpufreq/cpuinfo_max_freq");
            if (!file.exists()) {
                continue;
            }
            try (BufferedReader reader = new BufferedReader(new FileReader(file))) {
                String line = reader.readLine();
                if (line != null) {
                    best = Math.max(best, Long.parseLong(line.trim()) / 1000);
                }
            } catch (Exception ignored) {
                // (a core that cannot be read is left out)
            }
        }
        return best;
    }
}
