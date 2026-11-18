package app.tg.owner;

import android.net.http.SslCertificate;
import android.os.Build;
import android.os.Bundle;

import java.net.URL;
import java.security.MessageDigest;
import java.security.cert.CertificateException;
import java.security.cert.X509Certificate;
import java.util.Locale;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.net.ssl.HttpsURLConnection;
import javax.net.ssl.SSLContext;
import javax.net.ssl.TrustManager;
import javax.net.ssl.X509TrustManager;

/**
 * The owner's control server, from «رابط تطبيق المالك» (https://host:port/admin-path#fingerprint). The server's
 * certificate is its own (not from an authority), so it is trusted by its SHA-256 fingerprint only: any other
 * certificate — another server, someone in between — is refused, by the panel's page and by the 15-minute check.
 */
final class Pin {
    private static final Pattern LINK = Pattern.compile(
        "https://(\\[[0-9A-Fa-f:]{2,39}\\]|[A-Za-z0-9](?:[A-Za-z0-9.\\-]{0,251}[A-Za-z0-9])?)(?::(\\d{1,5}))?"
            + "/([A-Za-z0-9_\\-]{16,64})/?#([0-9a-fA-F]{64})");

    private Pin() {
    }

    static final class Link {
        final String host;
        final int port;
        final String path;
        final String pin;

        Link(String host, int port, String path, String pin) {
            this.host = host;
            this.port = port;
            this.path = path;
            this.pin = pin.toLowerCase(Locale.ROOT);
        }

        /** https://host:port */
        String origin() {
            return "https://" + host + (port == 443 ? "" : ":" + port);
        }

        /** The panel: https://host:port/admin-path */
        String panel() {
            return origin() + "/" + path;
        }

        String text() {
            return panel() + "#" + pin;
        }

        /** Whether a page's address is on this server (the panel's own pages stay in the app). */
        boolean owns(String url) {
            try {
                URL u = new URL(url);
                int p = u.getPort() == -1 ? u.getDefaultPort() : u.getPort();
                return "https".equalsIgnoreCase(u.getProtocol()) && bare(u.getHost()).equalsIgnoreCase(bare(host)) && p == port;
            } catch (Exception e) {
                return false;
            }
        }

        private static String bare(String name) {
            return String.valueOf(name).replace("[", "").replace("]", "");
        }
    }

    /** The link pasted by the owner, or null when it is not one. */
    static Link parse(String text) {
        Matcher m = LINK.matcher(String.valueOf(text == null ? "" : text).trim());
        if (!m.matches()) {
            return null;
        }
        int port = m.group(2) == null ? 443 : Integer.parseInt(m.group(2));
        if (port < 1 || port > 65535) {
            return null;
        }
        return new Link(m.group(1), port, m.group(3), m.group(4));
    }

    static String sha256(byte[] data) {
        try {
            byte[] digest = MessageDigest.getInstance("SHA-256").digest(data);
            StringBuilder out = new StringBuilder();
            for (byte b : digest) {
                out.append(Character.forDigit((b >> 4) & 0xF, 16)).append(Character.forDigit(b & 0xF, 16));
            }
            return out.toString();
        } catch (Exception e) {
            return "";
        }
    }

    /** The WebView met the server's certificate: whether it is the one the link names. */
    static boolean matches(SslCertificate certificate, String pin) {
        if (certificate == null) {
            return false;
        }
        byte[] der = null;
        try {
            if (Build.VERSION.SDK_INT >= 29) {
                X509Certificate x509 = certificate.getX509Certificate();
                der = x509 == null ? null : x509.getEncoded();
            } else {
                Bundle saved = SslCertificate.saveState(certificate);
                der = saved == null ? null : saved.getByteArray("x509-certificate");
            }
        } catch (Exception ignored) {
            der = null;
        }
        return der != null && sha256(der).equals(pin);
    }

    /** A request to the server that trusts only its pinned certificate. */
    static HttpsURLConnection open(Link link, String pathAndQuery) throws Exception {
        X509TrustManager pinned = new X509TrustManager() {
            @Override
            public void checkClientTrusted(X509Certificate[] chain, String authType) throws CertificateException {
                throw new CertificateException("not a server");
            }

            @Override
            public void checkServerTrusted(X509Certificate[] chain, String authType) throws CertificateException {
                if (chain == null || chain.length == 0 || !sha256(chain[0].getEncoded()).equals(link.pin)) {
                    throw new CertificateException("the server's certificate is not the one in the link");
                }
            }

            @Override
            public X509Certificate[] getAcceptedIssuers() {
                return new X509Certificate[0];
            }
        };
        SSLContext tls = SSLContext.getInstance("TLS");
        tls.init(null, new TrustManager[] {pinned}, null);
        HttpsURLConnection connection = (HttpsURLConnection) new URL(link.panel() + pathAndQuery).openConnection();
        connection.setSSLSocketFactory(tls.getSocketFactory());
        connection.setHostnameVerifier((name, session) -> true);       // (the certificate itself is pinned)
        connection.setConnectTimeout(15000);
        connection.setReadTimeout(20000);
        return connection;
    }
}
