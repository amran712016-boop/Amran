package app.tg.owner;

import android.Manifest;
import android.annotation.SuppressLint;
import android.app.Activity;
import android.content.ActivityNotFoundException;
import android.content.ClipData;
import android.content.ContentValues;
import android.content.Intent;
import android.content.pm.PackageManager;
import android.graphics.Typeface;
import android.graphics.drawable.GradientDrawable;
import android.net.Uri;
import android.net.http.SslError;
import android.os.Build;
import android.os.Bundle;
import android.os.Environment;
import android.provider.MediaStore;
import android.text.InputType;
import android.util.Base64;
import android.util.TypedValue;
import android.view.Gravity;
import android.view.View;
import android.view.ViewGroup;
import android.view.WindowInsets;
import android.webkit.CookieManager;
import android.webkit.JavascriptInterface;
import android.webkit.SslErrorHandler;
import android.webkit.ValueCallback;
import android.webkit.WebChromeClient;
import android.webkit.WebResourceError;
import android.webkit.WebResourceRequest;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.Button;
import android.widget.EditText;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.TextView;

import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;

/**
 * «لوحة التحكّم» as the owner's own app: the panel's page (from the control server) in a WebView that trusts the
 * server's certificate by its fingerprint only, a login that lasts (the server keeps it 90 days for this app), and
 * notifications for new failures and users' messages (PulseJob). The panel itself stays on the server: what
 * changes there shows here at once, with no new app.
 */
public class MainActivity extends Activity {
    static final String MARK = " GroupsOwnerApp/1.0";
    static String AGENT = "GroupsOwnerApp/1.0";
    static final int PICK_FILES = 41;
    static final int ASK_NOTES = 42;
    static final int TEAL = 0xFF0F6B66;
    static final int BG = 0xFFEEF2F1;
    static final int CARD = 0xFFFFFFFF;
    static final int INK = 0xFF10201F;
    static final int MUTED = 0xFF566664;
    static final int LINE = 0xFFDCE4E2;
    static final int BAD = 0xFFB42318;

    FrameLayout root;
    WebView web;
    LinearLayout problem;
    TextView problemText;
    Pin.Link link;
    ValueCallback<Uri[]> files;

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        root = new FrameLayout(this);
        root.setBackgroundColor(BG);
        setContentView(root);
        fitToScreen(root);
        File crash = new File(getFilesDir(), OwnerApp.CRASH_FILE);
        if (crash.exists()) {
            showCrash(crash);                                    // (the error of the last time, to send)
            return;
        }
        start();
    }

    void start() {
        link = Pin.parse(PulseJob.prefs(this).getString("link", ""));
        if (link == null) {
            showSetup("");
        } else {
            openPanel(tabOf(getIntent()));
        }
        try {
            askForNotifications();
        } catch (Throwable error) {
            OwnerApp.note(this, "خطأ عند طلب إذن الإشعارات", error);
        }
        try {
            PulseJob.schedule(this);
        } catch (Throwable error) {
            OwnerApp.note(this, "خطأ عند جدولة فحص الإشعارات", error);
        }
    }

    /** The app stopped on an error last time: the error, with a button to copy it and send it. */
    void showCrash(File crash) {
        String report;
        try {
            report = new String(java.nio.file.Files.readAllBytes(crash.toPath()), java.nio.charset.StandardCharsets.UTF_8);
        } catch (Exception e) {
            report = String.valueOf(e);
        }
        root.removeAllViews();
        LinearLayout box = new LinearLayout(this);
        box.setOrientation(LinearLayout.VERTICAL);
        box.setPadding(dp(18), dp(18), dp(18), dp(18));
        box.addView(text("حدث خطأ في التطبيق", 20, INK, true));
        TextView note = text("انسخ الخطأ وأرسله لنا لنصلحه، ثم اضغط «متابعة».", 14, MUTED, false);
        note.setPadding(0, dp(6), 0, dp(12));
        box.addView(note);
        TextView body = text(report, 12, INK, false);
        body.setTextIsSelectable(true);
        body.setTextDirection(View.TEXT_DIRECTION_LTR);
        body.setTypeface(Typeface.MONOSPACE);
        body.setPadding(dp(10), dp(10), dp(10), dp(10));
        body.setBackground(shape(CARD, LINE, 10));
        android.widget.ScrollView scroll = new android.widget.ScrollView(this);
        scroll.addView(body);
        box.addView(scroll, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1));
        String copied = report;
        Button copy = button("نسخ الخطأ", true);
        copy.setOnClickListener(v -> {
            android.content.ClipboardManager clipboard = (android.content.ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
            clipboard.setPrimaryClip(ClipData.newPlainText("خطأ لوحة التحكّم", copied));
            android.widget.Toast.makeText(this, "نُسخ الخطأ. ألصقه في المحادثة.", android.widget.Toast.LENGTH_LONG).show();
        });
        LinearLayout.LayoutParams at = new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(46));
        at.topMargin = dp(12);
        box.addView(copy, at);
        Button go = button("متابعة", false);
        go.setOnClickListener(v -> {
            crash.delete();
            start();
        });
        LinearLayout.LayoutParams at2 = new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(46));
        at2.topMargin = dp(8);
        box.addView(go, at2);
        root.addView(box, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
    }

    @Override
    protected void onNewIntent(Intent intent) {
        super.onNewIntent(intent);
        setIntent(intent);
        String tab = tabOf(intent);
        if (tab != null && web != null && link != null) {
            web.loadUrl(link.panel() + "#" + tab);           // (a notification: its tab)
        }
    }

    @Override
    protected void onPause() {
        super.onPause();
        if (web != null) {
            try {
                CookieManager.getInstance().flush();            // (the login is kept for the 15-minute check)
            } catch (Throwable error) {
                OwnerApp.note(this, "خطأ عند حفظ الدخول", error);
            }
        }
    }

    @Override
    public void onBackPressed() {
        if (web != null && web.getParent() != null && web.canGoBack()) {
            web.goBack();
        } else {
            super.onBackPressed();
        }
    }

    static String tabOf(Intent intent) {
        String tab = intent == null ? null : intent.getStringExtra("tab");
        return "failures".equals(tab) || "support".equals(tab) ? tab : null;
    }

    // ---------------------------------------------------------------- the first time: the server's link

    void showSetup(String error) {
        root.removeAllViews();
        LinearLayout box = new LinearLayout(this);
        box.setOrientation(LinearLayout.VERTICAL);
        box.setGravity(Gravity.CENTER_VERTICAL);
        box.setPadding(dp(22), dp(22), dp(22), dp(22));

        TextView title = text("لوحة التحكّم", 22, INK, true);
        box.addView(title);
        TextView note = text("الصق «رابط تطبيق المالك» من تبويب «الربط» في لوحة التحكّم، أو من سجل تشغيل الخادم. "
            + "يُطلب مرة واحدة، ثم تسجّل الدخول بكلمة مرور اللوحة.", 14, MUTED, false);
        note.setPadding(0, dp(8), 0, dp(16));
        box.addView(note);

        EditText input = new EditText(this);
        input.setHint("https://…/…#…");
        input.setTextDirection(View.TEXT_DIRECTION_LTR);
        input.setTextSize(TypedValue.COMPLEX_UNIT_SP, 14);
        input.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_VARIATION_URI | InputType.TYPE_TEXT_FLAG_MULTI_LINE);
        input.setMinLines(3);
        input.setGravity(Gravity.TOP | Gravity.START);
        input.setBackground(shape(CARD, LINE, 10));
        input.setPadding(dp(12), dp(10), dp(12), dp(10));
        if (link != null) {
            input.setText(link.text());
        }
        box.addView(input, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));

        TextView problemLine = text(error, 13, BAD, false);
        problemLine.setPadding(0, dp(8), 0, 0);
        problemLine.setVisibility(error.isEmpty() ? View.GONE : View.VISIBLE);
        box.addView(problemLine);

        Button connect = button("اتصال", true);
        connect.setOnClickListener(v -> {
            Pin.Link parsed = Pin.parse(input.getText().toString());
            if (parsed == null) {
                problemLine.setText("الرابط غير صحيح. انسخه كاملًا كما هو، مع ما بعد علامة #.");
                problemLine.setVisibility(View.VISIBLE);
                return;
            }
            PulseJob.prefs(this).edit().putString("link", parsed.text()).remove("seen_f").remove("seen_m").apply();
            link = parsed;
            if (web != null) {
                web.destroy();
                web = null;
            }
            openPanel(null);
        });
        LinearLayout.LayoutParams at = new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(48));
        at.topMargin = dp(14);
        box.addView(connect, at);
        root.addView(box, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
    }

    // ---------------------------------------------------------------- the panel

    void openPanel(String tab) {
        root.removeAllViews();
        if (web == null) {
            web = buildWeb();
        }
        root.addView(web, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        root.addView(buildProblem(), new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        web.loadUrl(link.panel() + (tab != null ? "#" + tab : ""));
    }

    @SuppressLint("SetJavaScriptEnabled")
    WebView buildWeb() {
        WebView view = new WebView(this);
        WebSettings settings = view.getSettings();
        settings.setJavaScriptEnabled(true);
        settings.setDomStorageEnabled(true);
        settings.setSupportMultipleWindows(false);
        settings.setMediaPlaybackRequiresUserGesture(true);
        settings.setTextZoom(Math.min(100, settings.getTextZoom()));
        settings.setUserAgentString(settings.getUserAgentString() + MARK);   // (the server keeps this app's login)
        AGENT = settings.getUserAgentString();
        CookieManager.getInstance().setAcceptCookie(true);
        view.setBackgroundColor(BG);
        view.setWebViewClient(new WebViewClient() {
            @Override
            public void onReceivedSslError(WebView v, SslErrorHandler handler, SslError error) {
                // The server's own certificate: let through only the one whose fingerprint the link carries.
                if (link != null && link.owns(error.getUrl()) && Pin.matches(error.getCertificate(), link.pin)) {
                    handler.proceed();
                } else {
                    handler.cancel();
                    if (link != null && link.owns(error.getUrl())) {
                        showProblem("شهادة الخادم لا تطابق الرابط المحفوظ. إن نقلت لوحة التحكّم إلى خادم آخر، "
                            + "اضغط «تغيير الرابط» والصق رابطه الجديد من تبويب «الربط».");
                    }
                }
            }

            @Override
            public boolean shouldOverrideUrlLoading(WebView v, WebResourceRequest request) {
                if (link != null && link.owns(request.getUrl().toString())) {
                    return false;                                // (the panel's own pages stay here)
                }
                try {
                    startActivity(new Intent(Intent.ACTION_VIEW, request.getUrl()));
                } catch (ActivityNotFoundException ignored) {
                }
                return true;
            }

            @Override
            public void onReceivedError(WebView v, WebResourceRequest request, WebResourceError error) {
                if (request.isForMainFrame()) {
                    showProblem("تعذّر الوصول إلى خادم التحكّم. تأكد من الإنترنت ومن أن الخادم يعمل، ثم أعد المحاولة.");
                }
            }

            @Override
            public void onPageFinished(WebView v, String url) {
                CookieManager.getInstance().flush();
            }
        });
        view.setWebChromeClient(new WebChromeClient() {
            @Override
            public boolean onShowFileChooser(WebView v, ValueCallback<Uri[]> callback, FileChooserParams params) {
                return chooseFiles(callback, params);
            }
        });
        view.addJavascriptInterface(new Bridge(), "OwnerApp");
        return view;
    }

    View buildProblem() {
        problem = new LinearLayout(this);
        problem.setOrientation(LinearLayout.VERTICAL);
        problem.setGravity(Gravity.CENTER);
        problem.setBackgroundColor(BG);
        problem.setPadding(dp(24), dp(24), dp(24), dp(24));
        problem.setVisibility(View.GONE);
        problem.setClickable(true);
        problemText = text("", 15, INK, false);
        problemText.setGravity(Gravity.CENTER);
        problem.addView(problemText);
        Button again = button("إعادة المحاولة", true);
        again.setOnClickListener(v -> {
            problem.setVisibility(View.GONE);
            web.loadUrl(link.panel());
        });
        LinearLayout.LayoutParams at = new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(46));
        at.topMargin = dp(18);
        problem.addView(again, at);
        Button change = button("تغيير الرابط", false);
        change.setOnClickListener(v -> showSetup(""));
        LinearLayout.LayoutParams at2 = new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(46));
        at2.topMargin = dp(8);
        problem.addView(change, at2);
        return problem;
    }

    void showProblem(String message) {
        runOnUiThread(() -> {
            if (problem != null) {
                problemText.setText(message);
                problem.setVisibility(View.VISIBLE);
            }
        });
    }

    /** The page hands the app a file to save (a backup): it goes to «التنزيلات». */
    final class Bridge {
        @JavascriptInterface
        public boolean saveFile(String name, String base64) {
            try {
                byte[] bytes = Base64.decode(base64, Base64.DEFAULT);
                String safe = String.valueOf(name).replaceAll("[^A-Za-z0-9._-]", "_");
                if (safe.isEmpty()) {
                    safe = "control-backup.ggbak";
                }
                if (Build.VERSION.SDK_INT >= 29) {
                    ContentValues values = new ContentValues();
                    values.put(MediaStore.Downloads.DISPLAY_NAME, safe);
                    values.put(MediaStore.Downloads.MIME_TYPE, "application/octet-stream");
                    values.put(MediaStore.Downloads.IS_PENDING, 1);
                    Uri uri = getContentResolver().insert(MediaStore.Downloads.EXTERNAL_CONTENT_URI, values);
                    if (uri == null) {
                        return false;
                    }
                    try (OutputStream out = getContentResolver().openOutputStream(uri)) {
                        if (out == null) {
                            return false;
                        }
                        out.write(bytes);
                    }
                    values.clear();
                    values.put(MediaStore.Downloads.IS_PENDING, 0);
                    getContentResolver().update(uri, values, null, null);
                } else {
                    File folder = Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS);
                    if (checkSelfPermission(Manifest.permission.WRITE_EXTERNAL_STORAGE) != PackageManager.PERMISSION_GRANTED) {
                        folder = getExternalFilesDir(Environment.DIRECTORY_DOWNLOADS);   // (the app's own folder)
                    }
                    try (FileOutputStream out = new FileOutputStream(new File(folder, safe))) {
                        out.write(bytes);
                    }
                }
                return true;
            } catch (Exception e) {
                return false;
            }
        }
    }

    // ---------------------------------------------------------------- files for «استعادة نسخة احتياطية»

    boolean chooseFiles(ValueCallback<Uri[]> callback, WebChromeClient.FileChooserParams params) {
        if (files != null) {
            files.onReceiveValue(null);
        }
        files = callback;
        Intent pick = new Intent(Intent.ACTION_GET_CONTENT);
        pick.addCategory(Intent.CATEGORY_OPENABLE);
        pick.setType("*/*");
        pick.putExtra(Intent.EXTRA_ALLOW_MULTIPLE, params.getMode() == WebChromeClient.FileChooserParams.MODE_OPEN_MULTIPLE);
        try {
            startActivityForResult(Intent.createChooser(pick, "اختر الملف"), PICK_FILES);
            return true;
        } catch (ActivityNotFoundException e) {
            files = null;
            return false;
        }
    }

    @Override
    protected void onActivityResult(int requestCode, int resultCode, Intent data) {
        if (requestCode != PICK_FILES) {
            super.onActivityResult(requestCode, resultCode, data);
            return;
        }
        ValueCallback<Uri[]> callback = files;
        files = null;
        if (callback == null) {
            return;
        }
        Uri[] picked = null;
        if (resultCode == RESULT_OK && data != null) {
            ClipData clip = data.getClipData();
            if (clip != null && clip.getItemCount() > 0) {
                picked = new Uri[clip.getItemCount()];
                for (int i = 0; i < clip.getItemCount(); i++) {
                    picked[i] = clip.getItemAt(i).getUri();
                }
            } else if (data.getData() != null) {
                picked = new Uri[] {data.getData()};
            }
        }
        callback.onReceiveValue(picked);
    }

    // ---------------------------------------------------------------- small helpers

    void askForNotifications() {
        if (Build.VERSION.SDK_INT >= 33 && checkSelfPermission(Manifest.permission.POST_NOTIFICATIONS) != PackageManager.PERMISSION_GRANTED) {
            requestPermissions(new String[] {Manifest.permission.POST_NOTIFICATIONS}, ASK_NOTES);
        }
    }

    /** From Android 15 the page goes under the status bar, the navigation bar and the keyboard: it keeps clear. */
    void fitToScreen(View view) {
        if (Build.VERSION.SDK_INT < 30) {
            return;
        }
        view.setOnApplyWindowInsetsListener((target, insets) -> {
            android.graphics.Insets bars = insets.getInsets(WindowInsets.Type.systemBars() | WindowInsets.Type.displayCutout()
                | WindowInsets.Type.ime());
            target.setPadding(bars.left, bars.top, bars.right, bars.bottom);
            return insets;
        });
    }

    int dp(float value) {
        return Math.round(TypedValue.applyDimension(TypedValue.COMPLEX_UNIT_DIP, value, getResources().getDisplayMetrics()));
    }

    TextView text(String value, float size, int color, boolean bold) {
        TextView view = new TextView(this);
        view.setText(value);
        view.setTextSize(TypedValue.COMPLEX_UNIT_SP, size);
        view.setTextColor(color);
        view.setLineSpacing(0, 1.25f);
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

    Button button(String value, boolean primary) {
        Button button = new Button(this);
        button.setText(value);
        button.setAllCaps(false);
        button.setTextSize(TypedValue.COMPLEX_UNIT_SP, 15);
        button.setTypeface(Typeface.DEFAULT_BOLD);
        button.setTextColor(primary ? CARD : INK);
        button.setBackground(shape(primary ? TEAL : CARD, primary ? 0 : LINE, 12));
        button.setStateListAnimator(null);
        return button;
    }
}
