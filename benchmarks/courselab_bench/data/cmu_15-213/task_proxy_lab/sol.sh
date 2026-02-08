#!/bin/bash
set -euo pipefail
# Reference solution for CS:APP Proxy Lab
# Writes a concurrent, caching HTTP proxy using pthreads and Rio I/O.

cat > proxy.c << 'SOLUTION_EOF'
/*
 * proxy.c - A concurrent caching HTTP proxy.
 *
 * Design
 * ------
 *   • Main thread accepts connections and spawns a detached pthread per client.
 *   • Each worker parses the GET request, checks the LRU cache, and either
 *     serves from cache or forwards to the origin server.
 *   • The cache is a doubly-linked list protected by a readers-writers lock
 *     (first-readers variant using POSIX semaphores from csapp.h).
 *   • Objects larger than MAX_OBJECT_SIZE are relayed but never cached.
 *   • SIGPIPE is ignored so that broken connections do not kill the process.
 */

#include "csapp.h"
#include <string.h>

/* Recommended max cache and object sizes */
#define MAX_CACHE_SIZE 1049000
#define MAX_OBJECT_SIZE 102400

/* You won't lose style points for including this long line in your code */
static const char *user_agent_hdr =
    "User-Agent: Mozilla/5.0 (X11; Linux x86_64; rv:10.0.3) "
    "Gecko/20120305 Firefox/10.0.3\r\n";

/* ================================================================
 * Cache data structures
 * ================================================================ */

typedef struct cache_block {
    char url[MAXLINE];
    char *data;
    size_t size;
    struct cache_block *prev;
    struct cache_block *next;
} cache_block_t;

typedef struct {
    cache_block_t *head;   /* MRU end   */
    cache_block_t *tail;   /* LRU end   */
    size_t total_size;
    int readcnt;
    sem_t mutex;           /* protects readcnt */
    sem_t w;               /* writer / global lock */
} cache_t;

static cache_t cache;

/* ---- lock helpers ---- */

static void cache_read_lock(void)
{
    P(&cache.mutex);
    if (++cache.readcnt == 1) P(&cache.w);
    V(&cache.mutex);
}

static void cache_read_unlock(void)
{
    P(&cache.mutex);
    if (--cache.readcnt == 0) V(&cache.w);
    V(&cache.mutex);
}

static void cache_write_lock(void)  { P(&cache.w); }
static void cache_write_unlock(void) { V(&cache.w); }

/* ---- list helpers (caller must hold write lock) ---- */

static void block_unlink(cache_block_t *b)
{
    if (b->prev) b->prev->next = b->next;
    else          cache.head = b->next;
    if (b->next) b->next->prev = b->prev;
    else          cache.tail = b->prev;
}

static void block_push_front(cache_block_t *b)
{
    b->prev = NULL;
    b->next = cache.head;
    if (cache.head) cache.head->prev = b;
    cache.head = b;
    if (!cache.tail) cache.tail = b;
}

/* ---- public cache API ---- */

static void cache_init(void)
{
    cache.head = cache.tail = NULL;
    cache.total_size = 0;
    cache.readcnt = 0;
    Sem_init(&cache.mutex, 0, 1);
    Sem_init(&cache.w, 0, 1);
}

/* Find url in cache (caller holds at least read lock). */
static cache_block_t *cache_find(const char *url)
{
    for (cache_block_t *p = cache.head; p; p = p->next)
        if (!strcmp(p->url, url)) return p;
    return NULL;
}

/* Evict LRU blocks until room for `need` bytes (write lock held). */
static void cache_evict(size_t need)
{
    while (cache.total_size + need > (size_t)MAX_CACHE_SIZE && cache.tail) {
        cache_block_t *v = cache.tail;
        block_unlink(v);
        cache.total_size -= v->size;
        free(v->data);
        free(v);
    }
}

/* Insert a new object (acquires write lock internally). */
static void cache_insert(const char *url, const char *data, size_t size)
{
    if (size > (size_t)MAX_OBJECT_SIZE) return;

    cache_write_lock();

    /* Remove stale duplicate if any */
    cache_block_t *old = cache_find(url);
    if (old) {
        block_unlink(old);
        cache.total_size -= old->size;
        free(old->data);
        free(old);
    }

    cache_evict(size);

    cache_block_t *b = malloc(sizeof(*b));
    strncpy(b->url, url, MAXLINE - 1);
    b->url[MAXLINE - 1] = '\0';
    b->data = malloc(size);
    memcpy(b->data, data, size);
    b->size = size;

    block_push_front(b);
    cache.total_size += size;

    cache_write_unlock();
}

/* ================================================================
 * HTTP helpers
 * ================================================================ */

/*
 * parse_uri – break "http://host[:port]/path" into components.
 * Default port is "80".
 */
static void parse_uri(const char *uri,
                      char *hostname, char *port, char *path)
{
    const char *ptr, *slash, *colon;
    int len;

    strcpy(port, "80");

    ptr = strstr(uri, "//");
    ptr = ptr ? ptr + 2 : uri;

    slash = strchr(ptr, '/');
    colon = strchr(ptr, ':');

    if (colon && (!slash || colon < slash)) {
        len = colon - ptr;
        memcpy(hostname, ptr, len);
        hostname[len] = '\0';
        colon++;
        len = slash ? (int)(slash - colon) : (int)strlen(colon);
        memcpy(port, colon, len);
        port[len] = '\0';
    } else {
        len = slash ? (int)(slash - ptr) : (int)strlen(ptr);
        memcpy(hostname, ptr, len);
        hostname[len] = '\0';
    }

    strcpy(path, slash ? slash : "/");
}

/*
 * forward_request – read remaining client headers via `rp`, build an
 * HTTP/1.0 GET request, and send it to `serverfd`.
 * Returns 0 on success, -1 on write failure.
 */
static int forward_request(int serverfd, rio_t *rp,
                           const char *hostname, const char *path)
{
    char buf[MAXLINE], req[MAXLINE * 4];
    int host_done = 0;

    sprintf(req, "GET %s HTTP/1.0\r\n", path);

    while (rio_readlineb(rp, buf, MAXLINE) > 0) {
        if (!strcmp(buf, "\r\n")) break;

        if (!strncasecmp(buf, "Host:", 5))             { strcat(req, buf); host_done = 1; continue; }
        if (!strncasecmp(buf, "User-Agent:", 11))      continue;
        if (!strncasecmp(buf, "Connection:", 11))      continue;
        if (!strncasecmp(buf, "Proxy-Connection:", 17)) continue;

        strcat(req, buf);
    }

    if (!host_done) {
        sprintf(buf, "Host: %s\r\n", hostname);
        strcat(req, buf);
    }
    strcat(req, user_agent_hdr);
    strcat(req, "Connection: close\r\n");
    strcat(req, "Proxy-Connection: close\r\n");
    strcat(req, "\r\n");

    return rio_writen(serverfd, req, strlen(req)) < 0 ? -1 : 0;
}

/* ================================================================
 * Per-connection handler
 * ================================================================ */

static void handle_request(int connfd)
{
    char buf[MAXLINE], method[MAXLINE], uri[MAXLINE], version[MAXLINE];
    char hostname[MAXLINE], port[MAXLINE], path[MAXLINE];
    rio_t rio_client, rio_server;

    /* ---- Read request line ---- */
    Rio_readinitb(&rio_client, connfd);
    if (rio_readlineb(&rio_client, buf, MAXLINE) <= 0) return;
    if (sscanf(buf, "%s %s %s", method, uri, version) != 3) return;
    if (strcasecmp(method, "GET")) return;   /* Only support GET */

    /* ---- Check cache ---- */
    cache_read_lock();
    cache_block_t *hit = cache_find(uri);
    if (hit) {
        rio_writen(connfd, hit->data, hit->size);
        cache_read_unlock();
        /* Promote to MRU under write lock */
        cache_write_lock();
        hit = cache_find(uri);
        if (hit) { block_unlink(hit); block_push_front(hit); }
        cache_write_unlock();
        return;
    }
    cache_read_unlock();

    /* ---- Connect to origin server ---- */
    parse_uri(uri, hostname, port, path);

    int serverfd = open_clientfd(hostname, port);
    if (serverfd < 0) return;

    if (forward_request(serverfd, &rio_client, hostname, path) < 0) {
        Close(serverfd);
        return;
    }

    /* ---- Relay response & optionally buffer for cache ---- */
    Rio_readinitb(&rio_server, serverfd);

    char obj_buf[MAX_OBJECT_SIZE];
    size_t obj_size = 0;
    int cacheable = 1;
    ssize_t n;

    while ((n = rio_readnb(&rio_server, buf, MAXLINE)) > 0) {
        if (rio_writen(connfd, buf, n) < 0) { Close(serverfd); return; }
        if (cacheable) {
            if (obj_size + (size_t)n <= (size_t)MAX_OBJECT_SIZE) {
                memcpy(obj_buf + obj_size, buf, n);
                obj_size += n;
            } else {
                cacheable = 0;
            }
        }
    }

    Close(serverfd);

    if (cacheable && obj_size > 0)
        cache_insert(uri, obj_buf, obj_size);
}

/* ================================================================
 * Thread routine
 * ================================================================ */

static void *thread_routine(void *vargp)
{
    int connfd = *(int *)vargp;
    free(vargp);
    Pthread_detach(Pthread_self());
    handle_request(connfd);
    Close(connfd);
    return NULL;
}

/* ================================================================
 * main
 * ================================================================ */

int main(int argc, char **argv)
{
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <port>\n", argv[0]);
        exit(1);
    }

    Signal(SIGPIPE, SIG_IGN);
    cache_init();

    int listenfd = Open_listenfd(argv[1]);
    struct sockaddr_storage clientaddr;
    socklen_t clientlen;
    pthread_t tid;

    while (1) {
        clientlen = sizeof(clientaddr);
        int *connfdp = malloc(sizeof(int));
        *connfdp = Accept(listenfd, (SA *)&clientaddr, &clientlen);
        Pthread_create(&tid, NULL, thread_routine, connfdp);
    }

    return 0;
}
SOLUTION_EOF

echo "Solution written to proxy.c"
