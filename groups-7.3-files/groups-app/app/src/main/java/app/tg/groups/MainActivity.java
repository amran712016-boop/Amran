package app.tg.groups;

import android.annotation.SuppressLint;
import android.app.Activity;
import android.app.AlertDialog;
import android.app.DownloadManager;
import android.content.ActivityNotFoundException;
import android.content.ClipData;
import android.content.ClipboardManager;
import android.content.ContentValues;
import android.content.Intent;
import android.content.pm.PackageManager;
import android.content.res.Configuration;
import android.graphics.PixelFormat;
import android.graphics.Typeface;
import android.graphics.drawable.GradientDrawable;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.os.Looper;
import android.os.PowerManager;
import android.provider.MediaStore;
import android.provider.Settings;
import android.text.TextUtils;
import android.util.TypedValue;
import android.view.Gravity;
import android.view.View;
import android.view.ViewGroup;
import android.view.WindowInsets;
import android.view.WindowManager;
import android.webkit.CookieManager;
import android.webkit.JavascriptInterface;
import android.webkit.URLUtil;
import android.webkit.WebChromeClient;
import android.webkit.WebResourceError;
import android.webkit.WebResourceRequest;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.Button;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.PopupMenu;
import android.widget.ScrollView;
import android.widget.TextView;
import android.widget.Toast;

import org.json.JSONArray;
import org.json.JSONObject;

import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;

/**
 * The app's one page. «اللوحة» is the groups script's own page (the script runs inside the app, see Engine), and
 * «المتصفح» shows the browsers the script's tasks open (see BrowserHost). A task's browser works only while the
 * app is on the screen, so the screen is kept on while a browser is open, and leaving the app then shrinks it to a
 * small window over other apps instead of hiding it.
 */
public class MainActivity extends Activity {
    // The groups script's colors (the same as its page).
    static final int PAPER = 0xFFF3F5FA;
    static final int SHEET = 0xFFFFFFFF;
    static final int INK = 0xFF101828;
    static final int MUTED = 0xFF667085;
    static final int LINE = 0xFFE4E7EC;
    static final int PINE = 0xFF2F5BEA;
    static final int ON_PINE = 0xFFFFFFFF;
    static final int CLAY = 0xFFB42318;

    final Handler main = new Handler(Looper.getMainLooper());
    LinearLayout root;
    LinearLayout bar;
    FrameLayout content;
    ScrollView stageScroll;
    BrowserStage stage;
    TextView emptyNote;
    WebView panel;
    TextView status;
    LinearLayout report;
    TextView reportTitle;
    TextView reportText;
    Button tabPanel;
    Button tabBrowser;
    boolean onBrowserTab;
    // «الحسابات»: درج جانبي أصلي داخل التطبيق، يتصل بصفحة السكربت ليعرض الحسابات ويبدّلها ويضيف ويحذف.
    Button menuAccounts;
    FrameLayout drawerOverlay;
    View drawerScrim;
    LinearLayout drawerPanel;
    LinearLayout drawerList;
    String accountsJson = "[]";
    int accountsActive = -1;
    int accountsMax = 3;
    boolean accountsAnyRunning;
    boolean drawerOpen;
    boolean panelLoaded;
    boolean panelFailed;
    boolean alive;
    private FrameLayout overlayHost;
    private boolean inOverlay;
    private boolean overlayAsked;
    private boolean batteryAsked;
    boolean small;                        // picture-in-picture
    boolean started;                      // on the screen (between onStart and onStop)
    String reportCopy = "";

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        alive = true;
        // The script reaches the tasks' browsers through their DevTools socket, which Android opens to the app itself.
        WebView.setWebContentsDebuggingEnabled(true);
        setContentView(buildPage());
        BrowserHost.attach(this);
        browsersChanged();
        Engine.start(this);
        waitForScript();
    }

    @Override
    protected void onStart() {
        super.onStart();
        started = true;
        exitOverlay();
        BrowserHost.setVisible(true);
        askOverlayPermission();
    }

    @Override
    protected void onStop() {
        super.onStop();
        started = false;
        // A task that is working (even while its browser is closed for a pause) keeps the app working here.
        if (!BrowserHost.working()) {
            BrowserHost.setVisible(false);
        } else {
            keepWorkingInBackground();
        }
    }

    /** Off the screen with a task working: its browsers keep running, in the invisible window over other apps. */
    void keepWorkingInBackground() {
        BrowserHost.setVisible(true);
        BrowserHost.keepAwake();
        enterOverlay();
    }

    @Override
    protected void onDestroy() {
        alive = false;
        exitOverlay();
        BrowserHost.detach(this);
        if (panel != null) {
            content.removeView(panel);
            panel.destroy();
            panel = null;
        }
        super.onDestroy();
    }

    private boolean canOverlay() {
        return Build.VERSION.SDK_INT < 23 || Settings.canDrawOverlays(this);
    }

    private void enterOverlay() {
        if (inOverlay || stageScroll == null || content == null || !canOverlay()) {
            return;
        }
        try {
            if (stageScroll.getParent() == content) {
                content.removeView(stageScroll);
            }
            overlayHost = new FrameLayout(this);
            overlayHost.setBackgroundColor(0x00000000);
            overlayHost.addView(stageScroll, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT));
            WindowManager.LayoutParams lp = new WindowManager.LayoutParams(
                WindowManager.LayoutParams.MATCH_PARENT,
                WindowManager.LayoutParams.MATCH_PARENT,
                Build.VERSION.SDK_INT >= 26
                    ? WindowManager.LayoutParams.TYPE_APPLICATION_OVERLAY
                    : WindowManager.LayoutParams.TYPE_PHONE,
                WindowManager.LayoutParams.FLAG_NOT_FOCUSABLE
                    | WindowManager.LayoutParams.FLAG_NOT_TOUCHABLE
                    | WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON,
                PixelFormat.TRANSLUCENT);
            lp.gravity = Gravity.TOP | Gravity.START;
            lp.alpha = 0f;
            ((WindowManager) getSystemService(WINDOW_SERVICE)).addView(overlayHost, lp);
            inOverlay = true;
        } catch (Throwable t) {
            inOverlay = false;
            restoreStage();
        }
    }

    private void exitOverlay() {
        if (!inOverlay) {
            return;
        }
        inOverlay = false;
        try {
            if (overlayHost != null) {
                overlayHost.removeView(stageScroll);
                ((WindowManager) getSystemService(WINDOW_SERVICE)).removeView(overlayHost);
            }
        } catch (Throwable ignore) {
        } finally {
            overlayHost = null;
            restoreStage();
        }
    }

    private void restoreStage() {
        try {
            if (stageScroll == null || content == null) {
                return;
            }
            android.view.ViewParent parent = stageScroll.getParent();
            if (parent instanceof ViewGroup && parent != content) {
                ((ViewGroup) parent).removeView(stageScroll);
            }
            if (stageScroll.getParent() == null) {
                content.addView(stageScroll, 0, fill());
            }
        } catch (Throwable ignore) {
        }
    }

    private void askOverlayPermission() {
        if (overlayAsked || Build.VERSION.SDK_INT < 23 || Settings.canDrawOverlays(this) || isFinishing()) {
            return;
        }
        overlayAsked = true;
        new AlertDialog.Builder(this)
            .setTitle("مطلوب إذن")
            .setMessage("ليعمل التطبيق في الخلفية دون توقف، يجب تفعيل «الظهور فوق التطبيقات الأخرى».\n\n"
                + "اضغط «حسنًا»، ثم اختر «BOT GROB» وفعّل الخيار.")
            .setPositiveButton("حسنًا", (dialog, which) -> {
                try {
                    startActivity(new Intent(Settings.ACTION_MANAGE_OVERLAY_PERMISSION,
                        Uri.parse("package:" + getPackageName())));
                } catch (Throwable ignore) {
                }
            })
            .setNegativeButton("لاحقًا", null)
            .show();
    }

    // On phones that save battery hard (Xiaomi, Huawei, Oppo...) the system slows or kills
    // background work even with the overlay window and the service. Asking once to be left
    // out of battery optimization is what keeps the task at full speed after leaving the app.
    private void askBatteryExemption() {
        if (batteryAsked || Build.VERSION.SDK_INT < 23 || isFinishing()) {
            return;
        }
        try {
            PowerManager power = (PowerManager) getSystemService(POWER_SERVICE);
            if (power == null || power.isIgnoringBatteryOptimizations(getPackageName())) {
                return;
            }
            batteryAsked = true;
            new AlertDialog.Builder(this)
                .setTitle("إبقاء العمل في الخلفية")
                .setMessage("ليبقى العمل بكامل سرعته بعد الخروج من التطبيق، استثنِ «BOT GROB» من توفير البطارية.\n\n"
                    + "اضغط «حسنًا» ثم اختر «عدم التحسين» أو «السماح».")
                .setPositiveButton("حسنًا", (dialog, which) -> openBatteryExemption())
                .setNegativeButton("لاحقًا", null)
                .show();
        } catch (Throwable ignore) {
        }
    }

    private void openBatteryExemption() {
        try {
            startActivity(new Intent(Settings.ACTION_REQUEST_IGNORE_BATTERY_OPTIMIZATIONS,
                Uri.parse("package:" + getPackageName())));
            return;
        } catch (Throwable ignore) {
        }
        try {
            startActivity(new Intent(Settings.ACTION_IGNORE_BATTERY_OPTIMIZATION_SETTINGS));
        } catch (Throwable ignore) {
        }
    }

    // ---------------------------------------------------------------- the page

    View buildPage() {
        root = new LinearLayout(this);
        root.setOrientation(LinearLayout.VERTICAL);
        root.setBackgroundColor(PAPER);
        root.setLayoutDirection(View.LAYOUT_DIRECTION_RTL);

        bar = new LinearLayout(this);
        bar.setGravity(Gravity.CENTER_VERTICAL);
        bar.setPadding(dp(12), dp(6), dp(8), dp(6));
        menuAccounts = tab("☰");
        menuAccounts.setMinWidth(dp(44));
        menuAccounts.setMinimumWidth(dp(44));
        menuAccounts.setContentDescription("الحسابات");
        menuAccounts.setOnClickListener(v -> toggleDrawer());
        bar.addView(menuAccounts, gap(dp(8)));
        TextView title = text("BOT GROB", 18, INK, true);
        title.setSingleLine(true);
        title.setEllipsize(TextUtils.TruncateAt.END);
        title.setGravity(Gravity.CENTER_VERTICAL);
        // Next to ☰, at the bar's start: Latin text would otherwise sit at the left of its space, against the tabs.
        title.setTextAlignment(View.TEXT_ALIGNMENT_VIEW_START);
        LinearLayout.LayoutParams titleParams = new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1);
        titleParams.setMarginEnd(dp(10));
        bar.addView(title, titleParams);
        tabPanel = tab("اللوحة");
        tabPanel.setOnClickListener(v -> showTab(false));
        bar.addView(tabPanel, gap(dp(6)));
        tabBrowser = tab("المتصفح");
        tabBrowser.setOnClickListener(v -> showTab(true));
        bar.addView(tabBrowser, gap(dp(6)));
        Button more = tab("⋮");
        more.setMinWidth(dp(40));
        more.setMinimumWidth(dp(40));
        more.setOnClickListener(this::showMenu);
        bar.addView(more, gap(0));
        root.addView(bar, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));

        content = new FrameLayout(this);
        root.addView(content, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1));

        // Underneath: the browsers. They stay there (and keep working) while the panel is in front of them.
        stageScroll = new ScrollView(this);
        stageScroll.setBackgroundColor(0xFFFFFFFF);
        stageScroll.setFillViewport(true);
        stage = new BrowserStage(this);
        stageScroll.addView(stage, new ScrollView.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        content.addView(stageScroll, fill());
        emptyNote = text("لا يوجد متصفح مفتوح الآن.\nيفتح هنا عند بدء مهمة من «اللوحة»، ويمكنك مشاهدته وهو يعمل.", 15, MUTED, false);
        emptyNote.setGravity(Gravity.CENTER);
        emptyNote.setPadding(dp(24), dp(24), dp(24), dp(24));
        emptyNote.setBackgroundColor(PAPER);
        content.addView(emptyNote, fill());

        panel = buildPanel();
        content.addView(panel, fill());

        status = text("يشغّل السكربت…", 16, MUTED, false);
        status.setGravity(Gravity.CENTER);
        status.setPadding(dp(24), dp(24), dp(24), dp(24));
        status.setBackgroundColor(PAPER);
        content.addView(status, fill());

        report = buildReport();
        report.setVisibility(View.GONE);
        content.addView(report, fill());

        drawerOverlay = buildDrawer();
        drawerOverlay.setVisibility(View.GONE);
        content.addView(drawerOverlay, fill());

        fitToScreen(root);
        showTab(false);
        return root;
    }

    // ---------------------------------------------------------------- the accounts drawer

    FrameLayout buildDrawer() {
        FrameLayout overlay = new FrameLayout(this);
        drawerScrim = new View(this);
        drawerScrim.setBackgroundColor(0x66000000);
        drawerScrim.setOnClickListener(v -> closeDrawer());
        overlay.addView(drawerScrim, fill());

        drawerPanel = new LinearLayout(this);
        drawerPanel.setOrientation(LinearLayout.VERTICAL);
        drawerPanel.setLayoutDirection(View.LAYOUT_DIRECTION_RTL);
        drawerPanel.setBackgroundColor(PAPER);
        drawerPanel.setPadding(dp(14), dp(18), dp(14), dp(18));
        TextView head = text("الحسابات", 18, INK, true);
        drawerPanel.addView(head);
        TextView sub = text("حتى ٣ حسابات. لكل حساب مهمّته، وتعمل المهام في الوقت نفسه.", 13, MUTED, false);
        sub.setPadding(0, dp(4), 0, dp(12));
        drawerPanel.addView(sub);
        drawerList = new LinearLayout(this);
        drawerList.setOrientation(LinearLayout.VERTICAL);
        ScrollView scroll = new ScrollView(this);
        scroll.addView(drawerList);
        drawerPanel.addView(scroll, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1));
        // The panel sits on the start edge (the right, in this RTL app) and slides in from it.
        FrameLayout.LayoutParams lp = new FrameLayout.LayoutParams(dp(300), ViewGroup.LayoutParams.MATCH_PARENT, Gravity.END);
        overlay.addView(drawerPanel, lp);
        return overlay;
    }

    void toggleDrawer() {
        if (drawerOpen) {
            closeDrawer();
        } else {
            openDrawer();
        }
    }

    void openDrawer() {
        if (drawerOpen || drawerOverlay == null) {
            return;
        }
        drawerOpen = true;
        renderDrawer();
        drawerOverlay.setVisibility(View.VISIBLE);
        drawerScrim.setAlpha(0f);
        drawerScrim.animate().alpha(1f).setDuration(180).start();
        drawerPanel.setTranslationX(dp(300));
        drawerPanel.animate().translationX(0).setDuration(220).start();
    }

    void closeDrawer() {
        if (!drawerOpen || drawerOverlay == null) {
            return;
        }
        drawerOpen = false;
        drawerScrim.animate().alpha(0f).setDuration(160).start();
        drawerPanel.animate().translationX(dp(300)).setDuration(200)
            .withEndAction(() -> { if (drawerOverlay != null) drawerOverlay.setVisibility(View.GONE); }).start();
    }

    /** The page reports its accounts (names, which is working, which is active) so the drawer mirrors them. */
    void onAccountsChanged(String json, int active, int max, boolean anyRunning) {
        accountsJson = json != null ? json : "[]";
        accountsActive = active;
        accountsMax = max > 0 ? max : 3;
        accountsAnyRunning = anyRunning;
        if (menuAccounts != null) {
            menuAccounts.setText(anyRunning ? "☰ ●" : "☰");
        }
        if (drawerOpen) {
            renderDrawer();
        }
    }

    void renderDrawer() {
        if (drawerList == null) {
            return;
        }
        drawerList.removeAllViews();
        JSONArray rows;
        try {
            rows = new JSONArray(accountsJson);
        } catch (Exception e) {
            rows = new JSONArray();
        }
        if (rows.length() == 0) {
            TextView empty = text("لا يوجد حساب محفوظ بعد. أضف حسابك الأول.", 14, MUTED, false);
            empty.setPadding(0, dp(6), 0, dp(10));
            drawerList.addView(empty);
        }
        for (int i = 0; i < rows.length(); i++) {
            JSONObject row = rows.optJSONObject(i);
            String name = row != null ? row.optString("name", "") : "";
            boolean running = row != null && row.optBoolean("running", false);
            drawerList.addView(accountRow(i, name, running, i == accountsActive));
        }
        if (rows.length() < accountsMax) {
            Button add = new Button(this);
            add.setText("＋ إضافة حساب");
            add.setAllCaps(false);
            add.setTextColor(ON_PINE);
            add.setTextSize(TypedValue.COMPLEX_UNIT_SP, 15);
            add.setTypeface(Typeface.DEFAULT_BOLD);
            add.setBackground(shape(PINE, 0, 12));
            add.setStateListAnimator(null);
            add.setMinHeight(dp(48));
            add.setMinimumHeight(dp(48));
            add.setOnClickListener(v -> {
                callPage("window.__groupsAccounts&&window.__groupsAccounts.add()");
                showTab(false);
                closeDrawer();
            });
            LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT);
            lp.topMargin = dp(12);
            drawerList.addView(add, lp);
        } else {
            TextView note = text("الحد الأقصى " + accountsMax + " حسابات.", 12, MUTED, false);
            note.setPadding(0, dp(12), 0, 0);
            drawerList.addView(note);
        }
    }

    View accountRow(int index, String name, boolean running, boolean active) {
        LinearLayout row = new LinearLayout(this);
        row.setOrientation(LinearLayout.HORIZONTAL);
        row.setGravity(Gravity.CENTER_VERTICAL);
        row.setLayoutDirection(View.LAYOUT_DIRECTION_RTL);
        row.setBackground(shape(active ? 0xFFEEF2FF : SHEET, active ? PINE : LINE, 12));
        row.setPadding(dp(12), dp(12), dp(12), dp(12));

        View dot = new View(this);
        GradientDrawable dotShape = new GradientDrawable();
        dotShape.setShape(GradientDrawable.OVAL);
        dotShape.setColor(running ? 0xFF067647 : LINE);
        dot.setBackground(dotShape);
        LinearLayout.LayoutParams dlp = new LinearLayout.LayoutParams(dp(10), dp(10));
        dlp.setMarginEnd(dp(10));
        row.addView(dot, dlp);

        TextView who = text(name.isEmpty() ? "حساب" : "@" + name, 15, INK, true);
        who.setSingleLine(true);
        who.setEllipsize(TextUtils.TruncateAt.END);
        row.addView(who, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));

        Button del = new Button(this);
        del.setText("×");
        del.setAllCaps(false);
        del.setTextSize(TypedValue.COMPLEX_UNIT_SP, 18);
        del.setTextColor(CLAY);
        del.setBackground(shape(SHEET, LINE, 8));
        del.setStateListAnimator(null);
        del.setMinWidth(dp(40));
        del.setMinimumWidth(dp(40));
        del.setMinHeight(dp(36));
        del.setMinimumHeight(dp(36));
        del.setPadding(0, 0, 0, 0);
        del.setOnClickListener(v -> confirmDeleteAccount(index, name, running));
        row.addView(del, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT));

        row.setOnClickListener(v -> {
            callPage("window.__groupsAccounts&&window.__groupsAccounts.select(" + index + ")");
            showTab(false);
            closeDrawer();
        });
        LinearLayout.LayoutParams rlp = new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT);
        rlp.topMargin = dp(8);
        row.setLayoutParams(rlp);
        return row;
    }

    void confirmDeleteAccount(int index, String name, boolean running) {
        if (running) {
            Toast.makeText(this, "لهذا الحساب مهمة تعمل الآن. أوقفها قبل حذفه.", Toast.LENGTH_SHORT).show();
            return;
        }
        new AlertDialog.Builder(this)
            .setMessage("حذف الحساب " + (name.isEmpty() ? "" : "@" + name) + " من هذا الجهاز؟")
            .setPositiveButton("حذف", (d, w) -> callPage("window.__groupsAccounts&&window.__groupsAccounts.remove(" + index + ")"))
            .setNegativeButton("إلغاء", null)
            .show();
    }

    void callPage(String js) {
        main.post(() -> {
            if (panel != null) {
                panel.evaluateJavascript(js, null);
            }
        });
    }

    /** The page talks to the drawer through this (added to the panel WebView as "GroupsNative"). */
    final class AccountsBridge {
        @JavascriptInterface
        public void accounts(String json, int active, int max, boolean anyRunning) {
            main.post(() -> onAccountsChanged(json, active, max, anyRunning));
        }
    }

    /** From Android 15 the page goes under the status bar, the navigation bar and the keyboard: it keeps clear. */
    void fitToScreen(View view) {
        if (Build.VERSION.SDK_INT < 35) {
            return;
        }
        view.setOnApplyWindowInsetsListener((target, insets) -> {
            android.graphics.Insets bars = insets.getInsets(WindowInsets.Type.systemBars() | WindowInsets.Type.displayCutout()
                | WindowInsets.Type.ime());
            target.setPadding(bars.left, bars.top, bars.right, bars.bottom);
            return insets;
        });
    }

    @SuppressLint("SetJavaScriptEnabled")
    WebView buildPanel() {
        WebView view = new WebView(this);
        WebSettings settings = view.getSettings();
        settings.setJavaScriptEnabled(true);
        settings.setDomStorageEnabled(true);
        settings.setDatabaseEnabled(true);
        settings.setSupportMultipleWindows(false);
        settings.setMediaPlaybackRequiresUserGesture(true);
        view.setBackgroundColor(PAPER);
        view.setWebChromeClient(new WebChromeClient());        // (the page's own «هل أنت متأكد؟» questions show)
        view.setWebViewClient(new WebViewClient() {
            @Override
            public boolean shouldOverrideUrlLoading(WebView web, WebResourceRequest request) {
                Uri link = request.getUrl();
                if ("127.0.0.1".equals(link.getHost())) {
                    return false;
                }
                openOutside(link);                              // a tweet's link, and any other site: in its own app
                return true;
            }

            @Override
            public void onPageStarted(WebView web, String url, android.graphics.Bitmap icon) {
                panelFailed = false;
            }

            @Override
            public void onPageFinished(WebView web, String url) {
                if (!panelFailed && url != null && url.startsWith("http://127.0.0.1")) {
                    panelLoaded = true;
                    status.setVisibility(View.GONE);
                }
            }

            @Override
            public void onReceivedError(WebView web, WebResourceRequest request, WebResourceError error) {
                if (request.isForMainFrame() && alive) {
                    // (the script was not answering yet, or was restarting: asked again in a moment)
                    panelFailed = true;
                    panelLoaded = false;
                    if (!onBrowserTab && !small) {
                        status.setVisibility(View.VISIBLE);
                    }
                    main.postDelayed(() -> {
                        if (alive && panel != null && Engine.phase.equals("running")) {
                            panel.loadUrl(Engine.url());
                        }
                    }, 1200);
                }
            }
        });
        view.setDownloadListener((url, agent, disposition, mime, length) -> download(url, agent, disposition, mime));
        view.addJavascriptInterface(new AccountsBridge(), "GroupsNative");
        return view;
    }

    LinearLayout buildReport() {
        LinearLayout box = new LinearLayout(this);
        box.setOrientation(LinearLayout.VERTICAL);
        box.setBackgroundColor(PAPER);
        box.setPadding(dp(14), dp(10), dp(14), dp(10));
        LinearLayout head = new LinearLayout(this);
        head.setGravity(Gravity.CENTER_VERTICAL);
        reportTitle = text("", 17, INK, true);
        head.addView(reportTitle, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));
        Button copy = tab("نسخ");
        copy.setOnClickListener(v -> {
            ClipboardManager clipboard = (ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
            clipboard.setPrimaryClip(ClipData.newPlainText("قروبات", reportCopy.isEmpty() ? reportText.getText() : reportCopy));
            Toast.makeText(this, "نُسخ.", Toast.LENGTH_SHORT).show();
        });
        head.addView(copy, gap(dp(6)));
        Button close = tab("إغلاق");
        close.setOnClickListener(v -> report.setVisibility(View.GONE));
        head.addView(close, gap(0));
        box.addView(head);
        ScrollView scroll = new ScrollView(this);
        reportText = text("", 14, INK, false);
        reportText.setTextIsSelectable(true);
        reportText.setPadding(0, dp(10), 0, dp(20));
        scroll.addView(reportText);
        box.addView(scroll, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1));
        return box;
    }

    void showTab(boolean browser) {
        onBrowserTab = browser;
        // The panel is in front of the browsers on its tab, and out of the way on theirs.
        panel.setVisibility(browser ? View.INVISIBLE : View.VISIBLE);
        status.setVisibility(!browser && !panelLoaded ? View.VISIBLE : View.GONE);
        paintBrowserTab();
        paintTab(tabPanel, !browser);
        paintTab(tabBrowser, browser);
    }

    /** «المتصفح» shows the browser of the account the panel shows only: when that account has none open, a note
     * says so (in front of the other accounts' browsers, which keep working behind it). */
    void paintBrowserTab() {
        boolean shown = BrowserHost.shownBrowser() != null;
        tabBrowser.setText(shown ? "المتصفح ●" : "المتصفح");
        emptyNote.setText(BrowserHost.count() == 0
            ? "لا يوجد متصفح مفتوح الآن.\nيفتح هنا عند بدء مهمة من «اللوحة»، ويمكنك مشاهدته وهو يعمل."
            : "متصفح هذا الحساب غير مفتوح الآن.\nيفتح هنا عند بدء مهمة لهذا الحساب، ويمكنك مشاهدته وهو يعمل.\n(متصفحات الحسابات الأخرى تعمل في الخلفية.)");
        // (in the small window over other apps, the browser at work shows, whichever account's it is)
        boolean note = small ? BrowserHost.count() == 0 : onBrowserTab && !shown;
        emptyNote.setVisibility(note ? View.VISIBLE : View.GONE);
    }

    /** A browser was opened or closed. */
    void browsersChanged() {
        paintBrowserTab();
        // A browser opened while the app is off the screen (after a task's pause, say): keep it running there.
        if (BrowserHost.working() && !started && alive) {
            keepWorkingInBackground();
        }
        // The service and the lit screen stay while a task works, even between two of its browsers.
        if (BrowserHost.working()) {
            getWindow().addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
            if (started && Build.VERSION.SDK_INT >= 33
                && checkSelfPermission(android.Manifest.permission.POST_NOTIFICATIONS) != PackageManager.PERMISSION_GRANTED) {
                requestPermissions(new String[] {android.Manifest.permission.POST_NOTIFICATIONS}, 7);
            }
            if (started) {
                askBatteryExemption();
            }
            WorkService.start(this);
        } else {
            getWindow().clearFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
            WorkService.stop(this);
            if (!started && alive) {
                // Nothing works any more and the app is off the screen: the invisible window goes.
                exitOverlay();
                BrowserHost.setVisible(false);
            }
        }
    }

    // ---------------------------------------------------------------- the script's page

    void waitForScript() {
        new Thread(() -> {
            long end = System.currentTimeMillis() + 180_000;
            while (alive && System.currentTimeMillis() < end) {
                if (Engine.phase.equals("failed")) {
                    break;
                }
                if (Engine.answers()) {
                    runOnUiThread(() -> {
                        if (alive && panel != null) {
                            panel.loadUrl(Engine.url());
                        }
                    });
                    return;
                }
                try {
                    Thread.sleep(300);
                } catch (InterruptedException e) {
                    return;
                }
            }
            runOnUiThread(() -> {
                if (alive) {
                    status.setTextColor(CLAY);
                    status.setText("لم يبدأ السكربت. افتح القائمة ⋮ ثم «السجل» وأرسل ما فيه.\n\n"
                        + (Engine.error.length() > 600 ? Engine.error.substring(Engine.error.length() - 600) : Engine.error));
                }
            });
        }, "wait-for-script").start();
    }

    void openOutside(Uri link) {
        try {
            startActivity(new Intent(Intent.ACTION_VIEW, link));
        } catch (ActivityNotFoundException | SecurityException e) {
            Toast.makeText(this, "لا يوجد تطبيق يفتح الرابط.", Toast.LENGTH_SHORT).show();
        }
    }

    /** A file the panel offers (a picture made in «إنشاء محتوى»): saved in the phone's downloads. */
    void download(String url, String agent, String disposition, String mime) {
        try {
            DownloadManager.Request request = new DownloadManager.Request(Uri.parse(url));
            String cookies = CookieManager.getInstance().getCookie(url);
            if (cookies != null) {
                request.addRequestHeader("Cookie", cookies);
            }
            String name = URLUtil.guessFileName(url, disposition, mime);
            request.setTitle(name);
            request.setNotificationVisibility(DownloadManager.Request.VISIBILITY_VISIBLE_NOTIFY_COMPLETED);
            request.setDestinationInExternalPublicDir(Environment.DIRECTORY_DOWNLOADS, name);
            ((DownloadManager) getSystemService(DOWNLOAD_SERVICE)).enqueue(request);
            Toast.makeText(this, "يُحفظ في التنزيلات: " + name, Toast.LENGTH_SHORT).show();
        } catch (RuntimeException e) {
            Toast.makeText(this, "تعذّر حفظ الملف.", Toast.LENGTH_SHORT).show();
        }
    }

    // ---------------------------------------------------------------- the menu: check, log, update

    void showMenu(View anchor) {
        PopupMenu menu = new PopupMenu(this, anchor);
        menu.getMenu().add(0, 5, 0, "إعادة تشغيل السكربت");
        menu.getMenu().add(0, 3, 1, "السجل (الحساب المختار)");
        menu.getMenu().add(0, 8, 2, "السجل العام");
        menu.getMenu().add(0, 6, 2, BrowserHost.manualTyping ? "منع الكتابة" : "السماح بالكتابة");
        menu.setOnMenuItemClickListener(item -> {
            switch (item.getItemId()) {
                case 1:
                    runCheck(false);
                    return true;
                case 2:
                    runCheck(true);
                    return true;
                case 3:
                    showLog("log_text", "السجل");
                    return true;
                case 8:
                    showLog("general_log_text", "السجل العام");
                    return true;
                case 7:
                    showClickLog();
                    return true;
                case 4:
                    confirmUpdate();
                    return true;
                case 5:
                    restart();
                    return true;
                case 6:
                    BrowserHost.setManualTyping(!BrowserHost.manualTyping);
                    Toast.makeText(this, BrowserHost.manualTyping ? "يمكنك الآن الكتابة في المتصفح من تبويب «المتصفح»."
                        : "المتصفح لا يأخذ لوحة المفاتيح.", Toast.LENGTH_SHORT).show();
                    return true;
                default:
                    return false;
            }
        });
        menu.show();
    }

    void openReport(String title, String body) {
        reportTitle.setText(title);
        reportText.setText(body);
        reportCopy = "";
        report.setVisibility(View.VISIBLE);
    }

    void reportAdd(String line) {
        if (alive) {
            reportText.append(line + "\n");
        }
    }

    /** «فحص المتصفح»: everything the script asks of its browser, tried on a small page; a line for each. */
    void runCheck(boolean online) {
        if (!Engine.phase.equals("running")) {
            Toast.makeText(this, "السكربت لم يبدأ بعد.", Toast.LENGTH_SHORT).show();
            return;
        }
        openReport("فحص المتصفح", "");
        Lines lines = new Lines(this);
        new Thread(() -> {
            String whole = Engine.call("check", online, lines);
            runOnUiThread(() -> {
                if (alive) {
                    reportCopy = whole;
                    reportTitle.setText("فحص المتصفح: انتهى");
                }
            });
        }, "browser-check").start();
    }

    void showClickLog() {
        if (!Engine.phase.equals("running") && !Engine.phase.equals("failed")) {
            openReport("سجل النقر", "السكربت لم يبدأ بعد.");
            return;
        }
        openReport("سجل النقر", "…");
        new Thread(() -> {
            String log = com.chaquo.python.Python.isStarted() ? Engine.call("click_log_text") : "";
            runOnUiThread(() -> {
                if (!alive) {
                    return;
                }
                reportText.setText(log);
                reportCopy = log;
                saveTextDownload("groups-click-log.txt", log);
            });
        }, "click-log").start();
    }

    /** The click log as a text file in the phone's Downloads, so it can be sent back. */
    void saveTextDownload(String name, String body) {
        try {
            byte[] bytes = body.getBytes(StandardCharsets.UTF_8);
            if (Build.VERSION.SDK_INT >= 29) {
                ContentValues values = new ContentValues();
                values.put(MediaStore.Downloads.DISPLAY_NAME, name);
                values.put(MediaStore.Downloads.MIME_TYPE, "text/plain");
                values.put(MediaStore.Downloads.IS_PENDING, 1);
                Uri uri = getContentResolver().insert(MediaStore.Downloads.EXTERNAL_CONTENT_URI, values);
                if (uri == null) {
                    throw new RuntimeException("no file");
                }
                try (OutputStream out = getContentResolver().openOutputStream(uri)) {
                    if (out == null) {
                        throw new RuntimeException("no stream");
                    }
                    out.write(bytes);
                }
                values.clear();
                values.put(MediaStore.Downloads.IS_PENDING, 0);
                getContentResolver().update(uri, values, null, null);
            } else {
                File file = new File(Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS), name);
                try (FileOutputStream out = new FileOutputStream(file)) {
                    out.write(bytes);
                }
            }
            Toast.makeText(this, "حُفظ في التنزيلات: " + name + " — أرسل هذا الملف", Toast.LENGTH_LONG).show();
        } catch (Exception e) {
            Toast.makeText(this, "تعذّر حفظ الملف. استخدم زر النسخ.", Toast.LENGTH_LONG).show();
        }
    }

    /** «السجل»: the log of the account the panel shows (each account its own); «السجل العام»: the app's own. */
    void showLog(String which, String title) {
        if (!Engine.phase.equals("running") && !Engine.phase.equals("failed")) {
            openReport(title, "السكربت لم يبدأ بعد.");
            return;
        }
        openReport(title, "…");
        new Thread(() -> {
            String log = com.chaquo.python.Python.isStarted() ? Engine.call(which, 600) : "";
            String all = Engine.phase.equals("failed") ? (log + "\n\n" + Engine.error).trim() : log;
            runOnUiThread(() -> {
                if (alive) {
                    reportText.setText(all);
                    reportCopy = all;
                }
            });
        }, "log").start();
    }

    void confirmUpdate() {
        new AlertDialog.Builder(this)
            .setMessage("يأخذ التطبيق أحدث نسخة من السكربت من الإنترنت ثم يعيد تشغيل نفسه. المهام العاملة الآن تتوقف. هل تتابع؟")
            .setPositiveButton("تحديث", (dialog, which) -> update())
            .setNegativeButton("إلغاء", null)
            .show();
    }

    void update() {
        if (!Engine.phase.equals("running")) {
            Toast.makeText(this, "السكربت لم يبدأ بعد.", Toast.LENGTH_SHORT).show();
            return;
        }
        Toast.makeText(this, "يأخذ أحدث نسخة…", Toast.LENGTH_SHORT).show();
        new Thread(() -> {
            String answer = Engine.call("update_script");
            runOnUiThread(() -> {
                if (!alive) {
                    return;
                }
                if (answer.equals("OK")) {
                    Toast.makeText(this, "تم التحديث. يُعاد تشغيل التطبيق…", Toast.LENGTH_LONG).show();
                    main.postDelayed(this::restart, 900);
                } else {
                    new AlertDialog.Builder(this).setMessage(answer).setPositiveButton("حسنًا", null).show();
                }
            });
        }, "script-update").start();
    }

    /** Start the app afresh: the script runs once for the app's whole life, so a new script needs a new start. */
    void restart() {
        Intent launch = getPackageManager().getLaunchIntentForPackage(getPackageName());
        if (launch == null || launch.getComponent() == null) {
            return;
        }
        startActivity(Intent.makeRestartActivityTask(launch.getComponent()));
        Runtime.getRuntime().exit(0);
    }

    // ---------------------------------------------------------------- leaving the app while tasks run

    @Override
    public void onPictureInPictureModeChanged(boolean inSmallWindow, Configuration newConfig) {
        super.onPictureInPictureModeChanged(inSmallWindow, newConfig);
        small = inSmallWindow;
        bar.setVisibility(inSmallWindow ? View.GONE : View.VISIBLE);
        if (inSmallWindow) {
            // The small window shows the browser at work.
            report.setVisibility(View.GONE);
            panel.setVisibility(View.INVISIBLE);
            status.setVisibility(View.GONE);
            emptyNote.setVisibility(BrowserHost.count() == 0 ? View.VISIBLE : View.GONE);
        } else {
            showTab(onBrowserTab);
        }
    }

    @Override
    public void onBackPressed() {
        if (drawerOpen) {
            closeDrawer();
        } else if (report.getVisibility() == View.VISIBLE) {
            report.setVisibility(View.GONE);
        } else if (onBrowserTab) {
            showTab(false);
        } else if (panel != null && panel.canGoBack()) {
            panel.goBack();
        } else {
            moveTaskToBack(true);                 // (the app is left running, with its tasks)
        }
    }

    // ---------------------------------------------------------------- small view helpers

    int dp(float value) {
        return Math.round(TypedValue.applyDimension(TypedValue.COMPLEX_UNIT_DIP, value, getResources().getDisplayMetrics()));
    }

    FrameLayout.LayoutParams fill() {
        return new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT);
    }

    LinearLayout.LayoutParams gap(int end) {
        LinearLayout.LayoutParams params = new LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
        params.setMarginEnd(end);
        return params;
    }

    TextView text(String value, float size, int color, boolean bold) {
        TextView view = new TextView(this);
        view.setText(value);
        view.setTextSize(TypedValue.COMPLEX_UNIT_SP, size);
        view.setTextColor(color);
        view.setLineSpacing(0, 1.2f);
        if (bold) {
            view.setTypeface(Typeface.DEFAULT_BOLD);
        }
        return view;
    }

    GradientDrawable shape(int fill, int stroke, int radius) {
        GradientDrawable drawable = new GradientDrawable();
        drawable.setColor(fill);
        drawable.setCornerRadius(dp(radius));
        if (stroke != 0) {
            drawable.setStroke(dp(1), stroke);
        }
        return drawable;
    }

    Button tab(String value) {
        Button button = new Button(this);
        button.setText(value);
        button.setAllCaps(false);
        button.setSingleLine(true);
        button.setEllipsize(TextUtils.TruncateAt.END);
        button.setTextColor(INK);
        button.setTextSize(TypedValue.COMPLEX_UNIT_SP, 14);
        button.setBackground(shape(SHEET, LINE, 10));
        button.setStateListAnimator(null);
        button.setMinHeight(dp(38));
        button.setMinimumHeight(dp(38));
        button.setMinWidth(dp(64));
        button.setMinimumWidth(dp(64));
        button.setPadding(dp(12), 0, dp(12), 0);
        return button;
    }

    void paintTab(Button button, boolean chosen) {
        button.setBackground(shape(chosen ? PINE : SHEET, chosen ? 0 : LINE, 10));
        button.setTextColor(chosen ? ON_PINE : INK);
        button.setTypeface(chosen ? Typeface.DEFAULT_BOLD : Typeface.DEFAULT);
    }
}
