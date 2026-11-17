package app.tg.groups;

import android.app.Notification;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.content.Context;
import android.content.Intent;
import android.os.Build;

/** A normal notification when a task finishes, so it is seen even if the app is in the background. */
public final class Alerts {
    static final String CHANNEL = "groups-result";
    static Context app;
    static int next = 21;

    private Alerts() {
    }

    static void attach(Context context) {
        app = context.getApplicationContext();
    }

    static final String NOTICE_CHANNEL = "groups-notices";

    /** A message from the owner's control panel, while the app is off the screen: tapping it opens the app, where
     * the notifications list opens by itself. */
    static void notice(String title, String message) {
        Context context = app;
        if (context == null) {
            return;
        }
        NotificationManager manager = context.getSystemService(NotificationManager.class);
        if (manager == null) {
            return;
        }
        if (Build.VERSION.SDK_INT >= 26) {
            NotificationChannel channel = new NotificationChannel(NOTICE_CHANNEL, "رسائل الإدارة", NotificationManager.IMPORTANCE_HIGH);
            channel.setShowBadge(true);
            manager.createNotificationChannel(channel);
        }
        String text = message == null ? "" : message.trim();
        Intent open = new Intent(context, MainActivity.class);
        open.setFlags(Intent.FLAG_ACTIVITY_NEW_TASK | Intent.FLAG_ACTIVITY_SINGLE_TOP);
        PendingIntent pending = PendingIntent.getActivity(
            context, 1, open, PendingIntent.FLAG_UPDATE_CURRENT | PendingIntent.FLAG_IMMUTABLE);
        Notification.Builder builder = Build.VERSION.SDK_INT >= 26
            ? new Notification.Builder(context, NOTICE_CHANNEL)
            : new Notification.Builder(context);
        int id;
        synchronized (Alerts.class) {
            id = next++;
        }
        manager.notify(id, builder
            .setSmallIcon(android.R.drawable.stat_notify_chat)
            .setContentTitle(title)
            .setContentText(text.length() > 180 ? text.substring(0, 180) : text)
            .setStyle(new Notification.BigTextStyle().bigText(text))
            .setAutoCancel(true)
            .setContentIntent(pending)
            .build());
    }

    /** Called from the script when a task is done. success picks اكتملت or فشلت. */
    public static void result(boolean success, String message) {
        Context context = app;
        if (context == null) {
            return;
        }
        NotificationManager manager = context.getSystemService(NotificationManager.class);
        if (manager == null) {
            return;
        }
        if (Build.VERSION.SDK_INT >= 26) {
            NotificationChannel channel = new NotificationChannel(CHANNEL, "نتيجة المهمة", NotificationManager.IMPORTANCE_HIGH);
            channel.setShowBadge(true);
            manager.createNotificationChannel(channel);
        }
        String text = message == null ? "" : message.trim();
        if (text.length() > 180) {
            text = text.substring(0, 180);
        }
        Intent open = new Intent(context, MainActivity.class);
        open.setFlags(Intent.FLAG_ACTIVITY_NEW_TASK | Intent.FLAG_ACTIVITY_SINGLE_TOP);
        PendingIntent pending = PendingIntent.getActivity(
            context, 0, open, PendingIntent.FLAG_UPDATE_CURRENT | PendingIntent.FLAG_IMMUTABLE);
        Notification.Builder builder = Build.VERSION.SDK_INT >= 26
            ? new Notification.Builder(context, CHANNEL)
            : new Notification.Builder(context);
        int id;
        synchronized (Alerts.class) {
            id = next++;
        }
        manager.notify(id, builder
            .setSmallIcon(android.R.drawable.stat_notify_chat)
            .setContentTitle(success ? "اكتملت المهمة" : "فشلت المهمة")
            .setContentText(text.isEmpty() ? (success ? "اكتمل التنفيذ" : "توقف التنفيذ") : text)
            .setAutoCancel(true)
            .setContentIntent(pending)
            .build());
    }
}
