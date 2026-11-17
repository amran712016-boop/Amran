package app.tg.groups;

import android.content.Context;
import android.view.View;
import android.view.ViewGroup;
import android.webkit.WebView;

/**
 * Where the tasks' browsers show, on the «المتصفح» tab. Each browser fills the phone's own screen:
 * its width and its height are not stretched.
 */
final class BrowserStage extends ViewGroup {
    BrowserStage(Context context) {
        super(context);
        setClipChildren(true);
    }

    int px(int css) {
        return Math.max(1, (int) Math.floor(css * getResources().getDisplayMetrics().density));
    }

    void add(BrowserHost.Browser browser) {
        addView(browser.view, new LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.MATCH_PARENT));
        restack();
        requestLayout();
    }

    /** The shown account's browser goes in front (a browser another account opens stays behind it). */
    void restack() {
        BrowserHost.Browser shown = BrowserHost.shownBrowser();
        if (shown != null) {
            front(shown);
        }
    }

    void sized(BrowserHost.Browser browser) {
        requestLayout();
        invalidate();
    }

    void remove(WebView view) {
        if (view.getParent() == this) {
            removeView(view);
        }
    }

    void front(BrowserHost.Browser browser) {
        if (browser.view != null && browser.view.getParent() == this) {
            bringChildToFront(browser.view);
            requestLayout();
            invalidate();
        }
    }

    /** A finger on the tab scrolls the tab, never the page inside a browser (which would move the buttons from
     * under the script's mouse); only with «الكتابة في المتصفح بيدي» do touches reach the page. */
    @Override
    public boolean onInterceptTouchEvent(android.view.MotionEvent event) {
        return !BrowserHost.manualTyping;
    }

    @Override
    @SuppressWarnings("ClickableViewAccessibility")
    public boolean onTouchEvent(android.view.MotionEvent event) {
        return false;
    }

    private static BrowserHost.Browser of(View child) {
        Object tag = child.getTag();
        return tag instanceof BrowserHost.Browser ? (BrowserHost.Browser) tag : null;
    }


    @Override
    protected void onMeasure(int widthSpec, int heightSpec) {
        int width = MeasureSpec.getSize(widthSpec);
        int height = MeasureSpec.getSize(heightSpec);
        if (MeasureSpec.getMode(heightSpec) != MeasureSpec.EXACTLY || height <= 0) {
            height = getResources().getDisplayMetrics().heightPixels;
        }
        for (int i = 0; i < getChildCount(); i++) {
            View child = getChildAt(i);
            child.measure(MeasureSpec.makeMeasureSpec(width, MeasureSpec.EXACTLY), MeasureSpec.makeMeasureSpec(height, MeasureSpec.EXACTLY));
        }
        setMeasuredDimension(width, Math.max(height, getSuggestedMinimumHeight()));
    }

    @Override
    protected void onLayout(boolean changed, int left, int top, int right, int bottom) {
        for (int i = 0; i < getChildCount(); i++) {
            View child = getChildAt(i);
            child.layout(0, 0, child.getMeasuredWidth(), child.getMeasuredHeight());
            child.setScaleX(1f);
            child.setScaleY(1f);
        }
    }
}
