/* Clock-skew shim for the chaos harness (LD_PRELOAD).
 *
 * Shifts CLOCK_REALTIME (clock_gettime, gettimeofday, time) by the integer number of
 * seconds written in the file named by $SIGIL_SKEW_FILE, re-read at most every 50 ms,
 * so the harness can change a running witness's clock. Monotonic clocks are untouched,
 * so socket timeouts and sleeps behave normally. Both witness implementations read the
 * wall clock through libc (Rust std SystemTime::now, CPython time.time), so one shim
 * skews either. Built on demand by clock.py; never part of the product.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <fcntl.h>
#include <stdlib.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>

static int (*real_cgt)(clockid_t, struct timespec *) = 0;
static volatile long cached = 0;
static volatile long long last_ns = 0;

static void init(void) {
    if (!real_cgt) real_cgt = (int (*)(clockid_t, struct timespec *))dlsym(RTLD_NEXT, "clock_gettime");
}

static long offset(void) {
    const char *path = getenv("SIGIL_SKEW_FILE");
    struct timespec now;
    long long ns;
    char buf[64];
    int fd;
    ssize_t n;
    if (!path) return 0;
    init();
    real_cgt(CLOCK_MONOTONIC, &now);
    ns = (long long)now.tv_sec * 1000000000LL + now.tv_nsec;
    if (last_ns && ns - last_ns < 50000000LL) return cached;
    last_ns = ns;
    fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return cached;
    n = read(fd, buf, sizeof buf - 1);
    close(fd);
    if (n > 0) {
        buf[n] = 0;
        cached = strtol(buf, 0, 10);
    }
    return cached;
}

int clock_gettime(clockid_t c, struct timespec *ts) {
    int r;
    init();
    r = real_cgt(c, ts);
    if (r == 0 && (c == CLOCK_REALTIME || c == CLOCK_REALTIME_COARSE)) ts->tv_sec += offset();
    return r;
}

int gettimeofday(struct timeval *tv, void *tz) {
    struct timespec ts;
    (void)tz;
    if (clock_gettime(CLOCK_REALTIME, &ts) != 0) return -1;
    if (tv) {
        tv->tv_sec = ts.tv_sec;
        tv->tv_usec = ts.tv_nsec / 1000;
    }
    return 0;
}

time_t time(time_t *t) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    if (t) *t = ts.tv_sec;
    return ts.tv_sec;
}
