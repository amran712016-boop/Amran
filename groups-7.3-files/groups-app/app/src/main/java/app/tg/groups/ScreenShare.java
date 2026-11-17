package app.tg.groups;

import android.app.AlertDialog;
import android.graphics.Bitmap;
import android.os.Handler;
import android.os.Looper;
import android.util.Base64;
import android.view.PixelCopy;
import android.view.View;
import android.view.Window;

import java.io.ByteArrayOutputStream;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

/**
 * «معاينة الشاشة»: صاحب البرنامج يرى شاشة هذا التطبيق مباشرة من لوحة التحكّم ليعرف المشكلة التي تواجه المستخدم.
 * لا تبدأ إلا بموافقة المستخدم في كل مرة، ويبقى أعلى الشاشة شريط أحمر ظاهر طوال المعاينة فيه زر «إيقاف».
 * عرض فقط: لا يصل من اللوحة أي لمس أو كتابة. السكربت (gg.py) يطلب الموافقة ثم الصور من هنا، ويرسلها للخادم.
 */
public final class ScreenShare {
    private static final Handler MAIN = new Handler(Looper.getMainLooper());
    private static volatile boolean on;
    // A request waiting for the user's answer: shown when the app is on the screen (now, or once it comes back).
    private static volatile CountDownLatch asking;
    private static final AtomicReference<String> answer = new AtomicReference<>("");
    private static AlertDialog dialog;

    private ScreenShare() {
    }

    /** Asks the user (blocks the script's thread, up to seconds): "yes", "no", or "timeout". */
    public static String ask(int seconds) {
        CountDownLatch latch = new CountDownLatch(1);
        answer.set("");
        asking = latch;
        MAIN.post(() -> {
            MainActivity page = BrowserHost.activity;
            if (page != null && page.started && page.alive) {
                showDialog(page);
            } else {
                // Off the screen: a notification, and the question when the app is opened.
                Alerts.notice("طلب معاينة الشاشة", "صاحب البرنامج يطلب مشاهدة شاشة التطبيق لمساعدتك. افتح التطبيق للسماح أو الرفض.");
            }
        });
        try {
            latch.await(Math.max(5, seconds), TimeUnit.SECONDS);
        } catch (InterruptedException ignored) {
            Thread.currentThread().interrupt();
        }
        asking = null;
        MAIN.post(ScreenShare::closeDialog);
        String said = answer.get();
        if ("yes".equals(said)) {
            on = true;
            MAIN.post(ScreenShare::paint);
            return "yes";
        }
        return said.isEmpty() ? "timeout" : said;
    }

    /** Whether the app is on the screen now (a request waiting there shows its question). */
    public static boolean onScreen() {
        MainActivity page = BrowserHost.activity;
        return page != null && page.started && page.alive;
    }

    /** The app came back to the screen: a request still waiting asks now. */
    static void onShown(MainActivity page) {
        if (asking != null) {
            showDialog(page);
        }
        paint();
    }

    private static void showDialog(MainActivity page) {
        if (dialog != null && dialog.isShowing()) {
            return;
        }
        dialog = new AlertDialog.Builder(page)
            .setTitle("طلب معاينة الشاشة")
            .setMessage("صاحب البرنامج يطلب مشاهدة شاشة هذا التطبيق مباشرة، ليعرف المشكلة التي تواجهك.\n\n"
                + "يرى ما يظهر على الشاشة فقط، ولا يستطيع الضغط أو الكتابة أو تغيير أي شيء. "
                + "ويظهر أعلى الشاشة شريط أحمر طوال المعاينة، تستطيع إيقافها منه في أي وقت.")
            .setPositiveButton("سماح", (d, w) -> say("yes"))
            .setNegativeButton("رفض", (d, w) -> say("no"))
            .setOnCancelListener(d -> say("no"))
            .create();
        dialog.show();
    }

    private static void say(String what) {
        answer.compareAndSet("", what);
        CountDownLatch latch = asking;
        if (latch != null) {
            latch.countDown();
        }
    }

    private static void closeDialog() {
        if (dialog != null) {
            try {
                dialog.dismiss();
            } catch (RuntimeException ignored) {
            }
            dialog = null;
        }
    }

    public static boolean isOn() {
        return on;
    }

    /** The viewing ends: by the script (the owner closed it, its time ran out) or by the user (the bar's button). */
    public static void end() {
        on = false;
        MAIN.post(ScreenShare::paint);
    }

    static void paint() {
        MainActivity page = BrowserHost.activity;
        if (page != null && page.shareBar != null) {
            page.shareBar.setVisibility(on ? View.VISIBLE : View.GONE);
        }
    }

    /** What the screen shows now, as a JPEG in base64, at most maxWidth wide; "" when the app is not on the screen. */
    public static String capture(int maxWidth, int quality) {
        if (!on) {
            return "";
        }
        AtomicReference<Bitmap> shot = new AtomicReference<>();
        AtomicBoolean done = new AtomicBoolean(false);
        CountDownLatch latch = new CountDownLatch(1);
        MAIN.post(() -> {
            try {
                MainActivity page = BrowserHost.activity;
                if (page == null || !page.started || !page.alive) {
                    latch.countDown();
                    return;
                }
                Window window = page.getWindow();
                View decor = window.peekDecorView();
                if (decor == null || decor.getWidth() <= 0 || decor.getHeight() <= 0) {
                    latch.countDown();
                    return;
                }
                int width = Math.min(maxWidth, decor.getWidth());
                int height = Math.max(1, Math.round(decor.getHeight() * (width / (float) decor.getWidth())));
                Bitmap bitmap = Bitmap.createBitmap(width, height, Bitmap.Config.ARGB_8888);
                PixelCopy.request(window, bitmap, result -> {
                    if (result == PixelCopy.SUCCESS) {
                        shot.set(bitmap);
                        done.set(true);
                    } else {
                        bitmap.recycle();
                    }
                    latch.countDown();
                }, MAIN);
            } catch (RuntimeException e) {
                latch.countDown();
            }
        });
        try {
            latch.await(3, TimeUnit.SECONDS);
        } catch (InterruptedException ignored) {
            Thread.currentThread().interrupt();
        }
        Bitmap bitmap = shot.get();
        if (!done.get() || bitmap == null) {
            return "";
        }
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        bitmap.compress(Bitmap.CompressFormat.JPEG, Math.max(20, Math.min(90, quality)), out);
        bitmap.recycle();
        return Base64.encodeToString(out.toByteArray(), Base64.NO_WRAP);
    }

    /** Which part of the app is on the screen: "panel", "browser" or "" (not on the screen). */
    public static String tab() {
        MainActivity page = BrowserHost.activity;
        if (page == null || !page.started) {
            return "";
        }
        return page.onBrowserTab ? "browser" : "panel";
    }
}
