package app.tg.owner;

import android.app.Notification;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.app.job.JobInfo;
import android.app.job.JobParameters;
import android.app.job.JobScheduler;
import android.app.job.JobService;
import android.content.ComponentName;
import android.content.Context;
import android.content.Intent;
import android.content.SharedPreferences;
import android.webkit.CookieManager;

import org.json.JSONArray;
import org.json.JSONObject;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

import javax.net.ssl.HttpsURLConnection;

/**
 * Every 15 minutes (the least Android allows), even with the app closed: asks the control server for the failures
 * and the users' messages newer than the ones seen, and shows a notification for each kind. Tapping it opens the
 * app on «الأعطال» or «الرسائل». It uses the login the app keeps (the server's cookie), so it needs no password.
 */
public class PulseJob extends JobService {
    static final int JOB = 7001;
    static final int NOTE_FAILURES = 31;
    static final int NOTE_MESSAGES = 32;

    static void schedule(Context context) {
        JobScheduler jobs = context.getSystemService(JobScheduler.class);
        if (jobs == null || jobs.getPendingJob(JOB) != null) {
            return;
        }
        jobs.schedule(new JobInfo.Builder(JOB, new ComponentName(context, PulseJob.class))
            .setPeriodic(15 * 60 * 1000L)
            .setRequiredNetworkType(JobInfo.NETWORK_TYPE_ANY)
            .setPersisted(true)
            .build());
    }

    @Override
    public boolean onStartJob(JobParameters params) {
        new Thread(() -> {
            try {
                check(this);
            } catch (Exception ignored) {
                // (no network, the server down, the login gone: asked again in 15 minutes)
            }
            jobFinished(params, false);
        }, "pulse").start();
        return true;
    }

    @Override
    public boolean onStopJob(JobParameters params) {
        return true;
    }

    static SharedPreferences prefs(Context context) {
        return context.getSharedPreferences("owner", Context.MODE_PRIVATE);
    }

    /** One look at the server. The first one only notes where things are (no notification for the old ones). */
    static void check(Context context) throws Exception {
        SharedPreferences prefs = prefs(context);
        Pin.Link link = Pin.parse(prefs.getString("link", ""));
        if (link == null) {
            return;
        }
        String cookies = CookieManager.getInstance().getCookie(link.panel() + "/pulse");
        if (cookies == null || !cookies.contains("gg_owner=")) {
            return;                                   // (not signed in from the app yet)
        }
        long seenF = prefs.getLong("seen_f", -1);
        long seenM = prefs.getLong("seen_m", -1);
        HttpsURLConnection connection = Pin.open(link, "/pulse?f=" + Math.max(0, seenF) + "&m=" + Math.max(0, seenM));
        connection.setRequestProperty("Cookie", cookies);
        connection.setRequestProperty("User-Agent", MainActivity.AGENT);
        connection.setRequestProperty("Accept", "application/json");
        try {
            if (connection.getResponseCode() != 200) {
                return;
            }
            JSONObject answer = new JSONObject(read(connection.getInputStream()));
            if (!answer.optBoolean("ok")) {
                return;
            }
            long lastF = answer.optLong("f_last");
            long lastM = answer.optLong("m_last");
            if (seenF >= 0 && lastF > seenF) {
                notifyNew(context, NOTE_FAILURES, "failures", "الأعطال", answer.optInt("failures_new"),
                    answer.optJSONArray("failures"), "عطل جديد عند ", " أعطال جديدة", "title");
            }
            if (seenM >= 0 && lastM > seenM) {
                notifyNew(context, NOTE_MESSAGES, "support", "رسائل المستخدمين", answer.optInt("messages_new"),
                    answer.optJSONArray("messages"), "رسالة جديدة من ", " رسائل جديدة", "text");
            }
            prefs.edit().putLong("seen_f", lastF).putLong("seen_m", lastM).apply();
        } finally {
            connection.disconnect();
        }
    }

    private static void notifyNew(Context context, int id, String tab, String channelName, int count, JSONArray items,
                                  String oneTitle, String manyTitle, String textKey) {
        NotificationManager manager = context.getSystemService(NotificationManager.class);
        if (manager == null || items == null || items.length() == 0) {
            return;
        }
        String channel = "owner-" + tab;
        NotificationChannel made = new NotificationChannel(channel, channelName, NotificationManager.IMPORTANCE_HIGH);
        made.setShowBadge(true);
        manager.createNotificationChannel(made);
        List<String> lines = new ArrayList<>();
        for (int i = 0; i < items.length(); i++) {
            JSONObject item = items.optJSONObject(i);
            if (item != null) {
                lines.add(item.optString("who") + ": " + item.optString(textKey));
            }
        }
        JSONObject first = items.optJSONObject(0);
        String title = count <= 1 && first != null ? oneTitle + first.optString("who") : count + manyTitle;
        String text = count <= 1 && first != null ? first.optString(textKey) : lines.get(0);
        Intent open = new Intent(context, MainActivity.class)
            .putExtra("tab", tab)
            .setFlags(Intent.FLAG_ACTIVITY_NEW_TASK | Intent.FLAG_ACTIVITY_SINGLE_TOP);
        PendingIntent pending = PendingIntent.getActivity(context, id, open,
            PendingIntent.FLAG_UPDATE_CURRENT | PendingIntent.FLAG_IMMUTABLE);
        Notification.InboxStyle inbox = new Notification.InboxStyle();
        for (String line : lines) {
            inbox.addLine(line);
        }
        if (count > lines.size()) {
            inbox.setSummaryText("و" + (count - lines.size()) + " غيرها");
        }
        manager.notify(id, new Notification.Builder(context, channel)
            .setSmallIcon(R.drawable.ic_stat)
            .setColor(0xFF0F6B66)
            .setContentTitle(title)
            .setContentText(text)
            .setStyle(count <= 1 ? new Notification.BigTextStyle().bigText(text) : inbox)
            .setNumber(count)
            .setAutoCancel(true)
            .setContentIntent(pending)
            .build());
    }

    static String read(InputStream in) throws Exception {
        try (InputStream stream = in) {
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            byte[] buffer = new byte[8192];
            for (int n = stream.read(buffer); n > 0; n = stream.read(buffer)) {
                out.write(buffer, 0, n);
            }
            return new String(out.toByteArray(), StandardCharsets.UTF_8);
        }
    }
}
