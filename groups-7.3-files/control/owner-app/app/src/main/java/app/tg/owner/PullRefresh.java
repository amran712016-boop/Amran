package app.tg.owner;

import android.content.Context;
import android.content.res.ColorStateList;
import android.graphics.drawable.GradientDrawable;
import android.util.TypedValue;
import android.view.Gravity;
import android.view.MotionEvent;
import android.view.ViewConfiguration;
import android.view.ViewGroup;
import android.webkit.WebView;
import android.widget.FrameLayout;
import android.widget.ProgressBar;

/**
 * «اسحب للتحديث»: pulling the panel's page down from its top shows a small circle; let go far enough and the page
 * loads again (the circle turns until it has). A page scrolled down scrolls up as usual; a sideways move is left
 * to the page. No library: a frame around the WebView that takes the gesture only when the page is at its top.
 */
final class PullRefresh extends FrameLayout {
    interface Listener {
        void onRefresh();
    }

    private final WebView web;
    private final FrameLayout bubble;
    private final int slop;
    private final int trigger;
    private final int furthest;
    private float startX;
    private float startY;
    private boolean dragging;
    boolean refreshing;
    private Listener listener;
    private final Runnable giveUp = this::finish;              // (a page that never finishes loading)

    PullRefresh(Context context, WebView web) {
        super(context);
        this.web = web;
        if (web.getParent() instanceof ViewGroup) {
            ((ViewGroup) web.getParent()).removeView(web);
        }
        addView(web, new LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.MATCH_PARENT));

        bubble = new FrameLayout(context);
        GradientDrawable circle = new GradientDrawable();
        circle.setShape(GradientDrawable.OVAL);
        circle.setColor(MainActivity.CARD);
        circle.setStroke(dp(1), MainActivity.LINE);
        bubble.setBackground(circle);
        bubble.setElevation(dp(4));
        ProgressBar spinner = new ProgressBar(context);
        spinner.setIndeterminate(true);
        spinner.setIndeterminateTintList(ColorStateList.valueOf(MainActivity.TEAL));
        bubble.addView(spinner, new LayoutParams(dp(24), dp(24), Gravity.CENTER));
        addView(bubble, new LayoutParams(dp(42), dp(42), Gravity.TOP | Gravity.CENTER_HORIZONTAL));
        bubble.setTranslationY(-dp(50));
        bubble.setAlpha(0f);

        slop = ViewConfiguration.get(context).getScaledTouchSlop();
        trigger = dp(70);
        furthest = dp(120);
    }

    void setListener(Listener listener) {
        this.listener = listener;
    }

    @Override
    public boolean onInterceptTouchEvent(MotionEvent event) {
        if (refreshing) {
            return false;
        }
        switch (event.getActionMasked()) {
            case MotionEvent.ACTION_DOWN:
                startX = event.getX();
                startY = event.getY();
                dragging = false;
                break;
            case MotionEvent.ACTION_MOVE:
                float down = event.getY() - startY;
                float aside = Math.abs(event.getX() - startX);
                if (!dragging && event.getPointerCount() == 1 && down > slop && down > aside * 1.5f
                        && !web.canScrollVertically(-1)) {
                    dragging = true;                                 // (the page is at its top: the pull is ours)
                    startY = event.getY();
                    return true;
                }
                break;
            default:
                break;
        }
        return false;
    }

    @Override
    public boolean onTouchEvent(MotionEvent event) {
        if (!dragging) {
            return super.onTouchEvent(event);
        }
        float pulled = Math.max(0f, event.getY() - startY) * 0.55f;   // (resists a little, like a spring)
        switch (event.getActionMasked()) {
            case MotionEvent.ACTION_MOVE:
                show(Math.min(pulled, furthest));
                return true;
            case MotionEvent.ACTION_UP:
                dragging = false;
                if (pulled >= trigger) {
                    start();
                } else {
                    hide();
                }
                return true;
            case MotionEvent.ACTION_CANCEL:
                dragging = false;
                hide();
                return true;
            default:
                return true;
        }
    }

    private void show(float pulled) {
        bubble.animate().cancel();
        bubble.setAlpha(Math.min(1f, pulled / trigger));
        bubble.setTranslationY(pulled - dp(42));
        bubble.setRotation(pulled * 2);
    }

    private void start() {
        refreshing = true;
        bubble.animate().translationY(dp(14)).alpha(1f).setDuration(150).start();
        removeCallbacks(giveUp);
        postDelayed(giveUp, 25000);
        if (listener != null) {
            listener.onRefresh();
        }
    }

    /** The page finished loading (or failed): the circle goes. */
    void finish() {
        removeCallbacks(giveUp);
        if (refreshing) {
            refreshing = false;
            hide();
        }
    }

    private void hide() {
        bubble.animate().translationY(-dp(50)).alpha(0f).setDuration(180).start();
    }

    private int dp(float value) {
        return Math.round(TypedValue.applyDimension(TypedValue.COMPLEX_UNIT_DIP, value, getResources().getDisplayMetrics()));
    }
}
