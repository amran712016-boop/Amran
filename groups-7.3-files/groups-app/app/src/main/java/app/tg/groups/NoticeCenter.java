package app.tg.groups;

import android.content.Context;
import android.content.SharedPreferences;
import android.graphics.Typeface;
import android.graphics.drawable.GradientDrawable;
import android.text.format.DateUtils;
import android.view.Gravity;
import android.view.View;
import android.view.ViewGroup;
import android.widget.Button;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.ScrollView;
import android.widget.TextView;

import org.json.JSONArray;
import org.json.JSONObject;

import java.util.ArrayList;
import java.util.List;

/**
 * التنبيهات داخل التطبيق: قائمة منبثقة تجمع كل تنبيه أو تعليمات تُرسلها «اللوحة» (صفحة السكربت) عبر جسر
 * {@code GroupsNative.notify}. تظهر في كل تبويبات التطبيق — حتى على «المتصفح» — وتُحفظ لتُقرأ لاحقًا.
 * يحمل الجرس في الشريط العلوي عدّاد غير المقروء، وتفتح القائمة بالضغط عليه.
 */
public final class NoticeCenter {
    static final int MAX = 60;                 // أحدث ٦٠ تنبيهًا تُحفظ، والأقدم يسقط
    static final int BADGE = 0xFFB42318;       // أحمر العدّاد (نفس CLAY)

    private final MainActivity page;
    private final SharedPreferences store;
    private final List<Item> items = new ArrayList<>();
    private int unread;

    private Button bell;
    private FrameLayout overlay;
    private View scrim;
    private LinearLayout slide;
    private LinearLayout list;
    private TextView empty;
    private boolean open;

    static final class Item {
        final String text;
        final String kind;      // ok / bad / info
        final long when;
        Item(String text, String kind, long when) {
            this.text = text;
            this.kind = kind;
            this.when = when;
        }
    }

    NoticeCenter(MainActivity page) {
        this.page = page;
        this.store = page.getSharedPreferences("notices", Context.MODE_PRIVATE);
        load();
    }

    // ---------------------------------------------------------------- الجرس في الشريط العلوي

    Button bell() {
        bell = page.tab("🔔");
        bell.setMinWidth(page.dp(52));
        bell.setMinimumWidth(page.dp(52));
        bell.setContentDescription("التنبيهات");
        bell.setOnClickListener(v -> openList());
        paintBell();
        return bell;
    }

    private void paintBell() {
        if (bell == null) {
            return;
        }
        if (unread > 0) {
            String count = unread > 99 ? "99+" : String.valueOf(unread);
            bell.setText("🔔 " + count);
            bell.setBackground(page.shape(BADGE, 0, 10));
            bell.setTextColor(MainActivity.ON_PINE);
            bell.setTypeface(Typeface.DEFAULT_BOLD);
        } else {
            bell.setText("🔔");
            bell.setBackground(page.shape(MainActivity.SHEET, MainActivity.LINE, 10));
            bell.setTextColor(MainActivity.INK);
            bell.setTypeface(Typeface.DEFAULT);
        }
    }

    // ---------------------------------------------------------------- استقبال تنبيه من اللوحة

    /** تُستدعى من الجسر عندما تُرسل اللوحة تنبيهًا أو تعليمات. تُنفَّذ على خيط الواجهة. */
    void add(String kind, String text) {
        String body = text == null ? "" : text.trim();
        if (body.isEmpty()) {
            return;
        }
        if (body.length() > 500) {
            body = body.substring(0, 500);
        }
        String tag = normalizeKind(kind);
        // لا تكرّر نفس الرسالة المتتالية (بعض التنبيهات تتكرر أثناء الانتظار).
        if (!items.isEmpty()) {
            Item top = items.get(0);
            if (top.text.equals(body) && top.kind.equals(tag)) {
                return;
            }
        }
        items.add(0, new Item(body, tag, System.currentTimeMillis()));
        while (items.size() > MAX) {
            items.remove(items.size() - 1);
        }
        if (!open) {
            unread++;
            paintBell();
        } else {
            render();
        }
        save();
    }

    private static String normalizeKind(String kind) {
        if ("ok".equals(kind) || "bad".equals(kind) || "info".equals(kind)) {
            return kind;
        }
        if ("true".equalsIgnoreCase(kind)) {
            return "ok";
        }
        if ("false".equalsIgnoreCase(kind)) {
            return "bad";
        }
        return "info";
    }

    // ---------------------------------------------------------------- القائمة المنبثقة

    FrameLayout buildOverlay() {
        overlay = new FrameLayout(page);
        overlay.setVisibility(View.GONE);

        scrim = new View(page);
        scrim.setBackgroundColor(0x66000000);
        scrim.setOnClickListener(v -> closeList());
        overlay.addView(scrim, page.fill());

        slide = new LinearLayout(page);
        slide.setOrientation(LinearLayout.VERTICAL);
        slide.setLayoutDirection(View.LAYOUT_DIRECTION_RTL);
        slide.setBackgroundColor(MainActivity.PAPER);
        slide.setPadding(page.dp(14), page.dp(18), page.dp(14), page.dp(18));

        LinearLayout head = new LinearLayout(page);
        head.setOrientation(LinearLayout.HORIZONTAL);
        head.setGravity(Gravity.CENTER_VERTICAL);
        TextView title = page.text("التنبيهات", 18, MainActivity.INK, true);
        head.addView(title, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));
        Button clear = page.tab("مسح الكل");
        clear.setOnClickListener(v -> clearAll());
        head.addView(clear, page.gap(page.dp(6)));
        Button close = page.tab("إغلاق");
        close.setOnClickListener(v -> closeList());
        head.addView(close, page.gap(0));
        slide.addView(head);

        TextView sub = page.text("كل تنبيه أو تعليمات تصل من اللوحة تظهر هنا.", 13, MainActivity.MUTED, false);
        sub.setPadding(0, page.dp(4), 0, page.dp(12));
        slide.addView(sub);

        list = new LinearLayout(page);
        list.setOrientation(LinearLayout.VERTICAL);
        ScrollView scroll = new ScrollView(page);
        scroll.addView(list);
        slide.addView(scroll, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1));

        empty = page.text("لا توجد تنبيهات بعد.", 14, MainActivity.MUTED, false);
        empty.setPadding(0, page.dp(6), 0, page.dp(10));

        FrameLayout.LayoutParams lp = new FrameLayout.LayoutParams(page.dp(320),
            ViewGroup.LayoutParams.MATCH_PARENT, Gravity.END);
        overlay.addView(slide, lp);
        return overlay;
    }

    private void openList() {
        if (open || overlay == null) {
            return;
        }
        open = true;
        unread = 0;
        paintBell();
        render();
        overlay.setVisibility(View.VISIBLE);
        scrim.setAlpha(0f);
        scrim.animate().alpha(1f).setDuration(180).start();
        slide.setTranslationX(page.dp(320));
        slide.animate().translationX(0).setDuration(220).start();
    }

    private void closeList() {
        if (!open || overlay == null) {
            return;
        }
        open = false;
        scrim.animate().alpha(0f).setDuration(160).start();
        slide.animate().translationX(page.dp(320)).setDuration(200)
            .withEndAction(() -> { if (overlay != null) overlay.setVisibility(View.GONE); }).start();
    }

    boolean onBack() {
        if (open) {
            closeList();
            return true;
        }
        return false;
    }

    private void clearAll() {
        items.clear();
        unread = 0;
        paintBell();
        render();
        save();
    }

    private void render() {
        if (list == null) {
            return;
        }
        list.removeAllViews();
        if (items.isEmpty()) {
            list.addView(empty);
            return;
        }
        long now = System.currentTimeMillis();
        for (Item item : items) {
            list.addView(row(item, now));
        }
    }

    private View row(Item item, long now) {
        LinearLayout row = new LinearLayout(page);
        row.setOrientation(LinearLayout.HORIZONTAL);
        row.setLayoutDirection(View.LAYOUT_DIRECTION_RTL);
        int line = "ok".equals(item.kind) ? 0xFF067647 : "bad".equals(item.kind) ? MainActivity.CLAY : MainActivity.PINE;
        row.setBackground(page.shape(MainActivity.SHEET, MainActivity.LINE, 12));
        row.setPadding(page.dp(12), page.dp(12), page.dp(12), page.dp(12));

        View dot = new View(page);
        GradientDrawable dotShape = new GradientDrawable();
        dotShape.setShape(GradientDrawable.OVAL);
        dotShape.setColor(line);
        dot.setBackground(dotShape);
        LinearLayout.LayoutParams dlp = new LinearLayout.LayoutParams(page.dp(10), page.dp(10));
        dlp.setMarginEnd(page.dp(10));
        dlp.topMargin = page.dp(5);
        row.addView(dot, dlp);

        LinearLayout col = new LinearLayout(page);
        col.setOrientation(LinearLayout.VERTICAL);
        TextView body = page.text(item.text, 14, MainActivity.INK, false);
        col.addView(body);
        TextView time = page.text(ago(item.when, now), 12, MainActivity.MUTED, false);
        time.setPadding(0, page.dp(4), 0, 0);
        col.addView(time);
        row.addView(col, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));

        LinearLayout.LayoutParams rlp = new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT,
            ViewGroup.LayoutParams.WRAP_CONTENT);
        rlp.topMargin = page.dp(8);
        row.setLayoutParams(rlp);
        return row;
    }

    private static String ago(long when, long now) {
        if (now - when < DateUtils.MINUTE_IN_MILLIS) {
            return "الآن";
        }
        return DateUtils.getRelativeTimeSpanString(when, now, DateUtils.MINUTE_IN_MILLIS,
            DateUtils.FORMAT_ABBREV_RELATIVE).toString();
    }

    // ---------------------------------------------------------------- الحفظ بين التشغيلات

    private void load() {
        String raw = store.getString("items", "[]");
        try {
            JSONArray arr = new JSONArray(raw);
            for (int i = 0; i < arr.length() && items.size() < MAX; i++) {
                JSONObject o = arr.optJSONObject(i);
                if (o == null) {
                    continue;
                }
                String t = o.optString("t", "").trim();
                if (t.isEmpty()) {
                    continue;
                }
                items.add(new Item(t, normalizeKind(o.optString("k", "info")), o.optLong("w", 0)));
            }
        } catch (Exception ignored) {
            // قائمة فاسدة: ابدأ فارغًا
        }
        unread = 0;      // لا يُعدّ القديم غير مقروء عند الإقلاع
    }

    private void save() {
        JSONArray arr = new JSONArray();
        for (Item item : items) {
            try {
                JSONObject o = new JSONObject();
                o.put("t", item.text);
                o.put("k", item.kind);
                o.put("w", item.when);
                arr.put(o);
            } catch (Exception ignored) {
            }
        }
        store.edit().putString("items", arr.toString()).apply();
    }
}
