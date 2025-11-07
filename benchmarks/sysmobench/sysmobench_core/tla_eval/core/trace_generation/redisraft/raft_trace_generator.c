#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/select.h>
#include <arpa/inet.h>
#include <pthread.h>
#include <signal.h>

// Include RedisRaft's Raft library
#include "raft.h"

// Node structure - renamed to avoid conflict
typedef struct {
    int node_id;
    int port;
    raft_server_t *raft;
    pthread_t thread;
    int sock_fd;
    FILE *trace_file;
    time_t start_time;
    int running;
    time_t last_entry_time;
} my_raft_node_t;

// Global configuration
typedef struct {
    int node_count;
    int duration;
    my_raft_node_t *nodes;
    char *output_dir;
    FILE *merged_trace_file;  // Global merged trace file
} raft_cluster_t;

static raft_cluster_t cluster;
static volatile int shutdown_signal = 0;
static pthread_mutex_t trace_mutex = PTHREAD_MUTEX_INITIALIZER;

// Utility function to get timestamp
double get_timestamp() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec / 1e9;
}

// Log trace event to file
void log_trace_event(my_raft_node_t *node, const char *event_name, const char *data) {
    double timestamp = get_timestamp();

    // Create the JSON event
    char event_json[1024];
    if (data && strlen(data) > 0) {
        snprintf(event_json, sizeof(event_json),
                "{\"timestamp\":%.6f,\"name\":\"%s\",\"nid\":%d,%s}",
                timestamp, event_name, node->node_id, data);
    } else {
        snprintf(event_json, sizeof(event_json),
                "{\"timestamp\":%.6f,\"name\":\"%s\",\"nid\":%d}",
                timestamp, event_name, node->node_id);
    }

    // Write to individual node file
    fprintf(node->trace_file, "%s\n", event_json);
    fflush(node->trace_file);

    // Write to merged file with thread safety
    pthread_mutex_lock(&trace_mutex);
    if (cluster.merged_trace_file) {
        fprintf(cluster.merged_trace_file, "%s\n", event_json);
        fflush(cluster.merged_trace_file);
    }
    pthread_mutex_unlock(&trace_mutex);
}


// Simple network message structure
typedef struct {
    int type;
    int from;
    int to;
    raft_term_t term;
    char data[512];
    raft_index_t n_entries;
    raft_entry_t **entries;
} simple_message_t;

#define MSG_TYPE_REQUESTVOTE 1
#define MSG_TYPE_APPENDENTRIES 2
#define MSG_TYPE_REQUESTVOTE_RESPONSE 3
#define MSG_TYPE_APPENDENTRIES_RESPONSE 4
#define MSG_TYPE_PREVOTE 5
#define MSG_TYPE_PREVOTE_RESPONSE 6

// Per-node message queue for inter-node communication
typedef struct message_queue {
    simple_message_t messages[1000];
    int head;
    int tail;
    int count;
    pthread_mutex_t mutex;
} message_queue_t;

static message_queue_t node_queues[10]; // Support up to 10 nodes

// Message queue functions
int enqueue_message(simple_message_t *msg) {
    int target_node = msg->to - 1; // Convert to 0-based index
    if (target_node < 0 || target_node >= 10) return 0;

    message_queue_t *queue = &node_queues[target_node];
    pthread_mutex_lock(&queue->mutex);
    if (queue->count < 1000) {
        queue->messages[queue->tail] = *msg;
        queue->tail = (queue->tail + 1) % 1000;
        queue->count++;
        pthread_mutex_unlock(&queue->mutex);
        return 1;
    }
    pthread_mutex_unlock(&queue->mutex);
    return 0;
}

int dequeue_message(int node_id, simple_message_t *msg) {
    int node_index = node_id - 1; // Convert to 0-based index
    if (node_index < 0 || node_index >= 10) return 0;

    message_queue_t *queue = &node_queues[node_index];
    pthread_mutex_lock(&queue->mutex);
    if (queue->count > 0) {
        *msg = queue->messages[queue->head];
        queue->head = (queue->head + 1) % 1000;
        queue->count--;
        pthread_mutex_unlock(&queue->mutex);
        return 1;
    }
    pthread_mutex_unlock(&queue->mutex);
    return 0;
}

static void free_message_entries(simple_message_t *msg)
{
    if (msg->n_entries > 0 && msg->entries != NULL) {
        for (raft_index_t i = 0; i < msg->n_entries; i++) {
            if (msg->entries[i]) {
                raft_entry_release(msg->entries[i]);
            }
        }
        free(msg->entries);
        msg->entries = NULL;
        msg->n_entries = 0;
    }
}

// Simplified callback implementations
int send_requestvote(raft_server_t* raft, void *user_data, raft_node_t* node, raft_requestvote_req_t* msg) {
    (void)raft;
    my_raft_node_t *self_node = (my_raft_node_t*)user_data;
    int target_id = raft_node_get_id(node);

    // Log the event
    char trace_data[512];
    snprintf(trace_data, sizeof(trace_data),
            "\"msg\":{\"type\":\"MsgVote\",\"from\":%d,\"to\":%d,\"term\":%d,\"candidate_id\":%d,\"last_log_idx\":%d,\"last_log_term\":%d}",
            self_node->node_id, target_id, (int)msg->term, (int)msg->candidate_id,
            (int)msg->last_log_idx, (int)msg->last_log_term);
    log_trace_event(self_node, "RequestVote", trace_data);

    // Send message to queue for processing by target node
    simple_message_t net_msg = (simple_message_t){0};
    net_msg.type = msg->prevote ? MSG_TYPE_PREVOTE : MSG_TYPE_REQUESTVOTE; // Different types!
    net_msg.from = self_node->node_id;
    net_msg.to = target_id;
    net_msg.term = msg->term;
    snprintf(net_msg.data, sizeof(net_msg.data),
            "{\"candidate_id\":%d,\"last_log_idx\":%d,\"last_log_term\":%d}",
            (int)msg->candidate_id, (int)msg->last_log_idx, (int)msg->last_log_term);

    enqueue_message(&net_msg);

    return 0;
}

int send_appendentries(raft_server_t* raft, void *user_data, raft_node_t* node, raft_appendentries_req_t* msg) {
    (void)raft;
    my_raft_node_t *self_node = (my_raft_node_t*)user_data;
    int target_id = raft_node_get_id(node);

    // Log the event
    char trace_data[512];
    snprintf(trace_data, sizeof(trace_data),
            "\"msg\":{\"type\":\"MsgApp\",\"from\":%d,\"to\":%d,\"term\":%d,\"prev_log_idx\":%ld,\"prev_log_term\":%d,\"leader_commit\":%d,\"n_entries\":%ld}",
            self_node->node_id, target_id, (int)msg->term, (long)msg->prev_log_idx,
            (int)msg->prev_log_term, (int)msg->leader_commit, (long)msg->n_entries);
    log_trace_event(self_node, "AppendEntries", trace_data);

    // Send message to queue for processing by target node
    simple_message_t net_msg = {0};
    net_msg.type = MSG_TYPE_APPENDENTRIES;
    net_msg.from = self_node->node_id;
    net_msg.to = target_id;
    net_msg.term = msg->term;
    snprintf(net_msg.data, sizeof(net_msg.data),
            "{\"prev_log_idx\":%ld,\"prev_log_term\":%d,\"leader_commit\":%d,\"n_entries\":%ld}",
            (long)msg->prev_log_idx, (int)msg->prev_log_term, (int)msg->leader_commit, (long)msg->n_entries);
    if (msg->n_entries > 0) {
        net_msg.n_entries = msg->n_entries;
        net_msg.entries = calloc(msg->n_entries, sizeof(raft_entry_t*));
        if (!net_msg.entries) {
            net_msg.n_entries = 0;
        } else {
            for (raft_index_t i = 0; i < msg->n_entries; i++) {
                raft_entry_t *src = msg->entries[i];
                raft_entry_t *copy = raft_entry_new(src->data_len);
                if (!copy) {
                    for (raft_index_t j = 0; j < i; j++) {
                        raft_entry_release(net_msg.entries[j]);
                    }
                    free(net_msg.entries);
                    net_msg.entries = NULL;
                    net_msg.n_entries = 0;
                    break;
                }
                if (src->data_len > 0) {
                    memcpy(copy->data, src->data, src->data_len);
                }
                copy->term = src->term;
                copy->id = src->id;
                copy->session = src->session;
                copy->type = src->type;
                net_msg.entries[i] = copy;
            }
        }
    }

    if (!enqueue_message(&net_msg)) {
        free_message_entries(&net_msg);
    }

    return 0;
}

int apply_log(raft_server_t* raft, void *user_data, raft_entry_t *entry, raft_index_t entry_idx) {
    (void)raft;
    my_raft_node_t *node = (my_raft_node_t*)user_data;

    // Log the event
    char trace_data[256];
    snprintf(trace_data, sizeof(trace_data),
            "\"entry\":{\"index\":%ld,\"term\":%d,\"type\":%d,\"data_len\":%d}",
            (long)entry_idx, (int)entry->term, entry->type, (int)entry->data_len);
    log_trace_event(node, "CommitEntry", trace_data);

    return 0;
}

int persist_metadata(raft_server_t* raft, void *user_data, raft_term_t term, raft_node_id_t vote) {
    (void)raft;
    my_raft_node_t *node = (my_raft_node_t*)user_data;

    // Log the event
    char trace_data[128];
    snprintf(trace_data, sizeof(trace_data),
            "\"term\":%d,\"vote\":%d", (int)term, vote);
    log_trace_event(node, "PersistState", trace_data);

    return 0;
}

// Timestamp callback
raft_time_t get_time_callback(raft_server_t* raft, void *user_data) {
    (void)raft;
    (void)user_data;
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000000LL + ts.tv_nsec / 1000;
}

// Missing callback implementations
int send_snapshot(raft_server_t* raft, void *user_data, raft_node_t* node, raft_snapshot_req_t* msg) {
    (void)raft; (void)user_data; (void)node; (void)msg;
    return 0; // No snapshots for now
}

int load_snapshot(raft_server_t* raft, void *user_data, raft_index_t snapshot_index, raft_term_t snapshot_term) {
    (void)raft; (void)user_data; (void)snapshot_index; (void)snapshot_term;
    return 0; // No snapshots for now
}

raft_node_id_t get_node_id(raft_server_t* raft, void *user_data, raft_entry_t *entry, raft_index_t entry_idx) {
    (void)raft; (void)user_data; (void)entry; (void)entry_idx;
    return RAFT_NODE_ID_NONE; // No membership changes
}

int node_has_sufficient_logs(raft_server_t* raft, void *user_data, raft_node_t* node) {
    (void)raft; (void)user_data; (void)node;
    return 1; // Always sufficient for simplicity
}

// State change notification
void notify_state_event(raft_server_t* raft, void *user_data, raft_state_e state) {
    my_raft_node_t *node = (my_raft_node_t*)user_data;

    char trace_data[256];
    const char *state_str = "unknown";
    const char *event_name = "StateChange";

    switch (state) {
        case RAFT_STATE_FOLLOWER:
            state_str = "follower";
            event_name = "BecomeFollower";
            break;
        case RAFT_STATE_CANDIDATE:
            state_str = "candidate";
            event_name = "BecomeCandidate";
            break;
        case RAFT_STATE_LEADER:
            state_str = "leader";
            event_name = "BecomeLeader";
            break;
        case RAFT_STATE_PRECANDIDATE:
            state_str = "precandidate";
            event_name = "BecomePreCandidate";
            break;
    }

    snprintf(trace_data, sizeof(trace_data),
            "\"role\":\"%s\",\"term\":%d,\"leader\":%d",
            state_str, (int)raft_get_current_term(raft), raft_get_leader_id(raft));

    log_trace_event(node, event_name, trace_data);
}

// Main node thread function
void* node_thread(void *arg) {
    my_raft_node_t *node = (my_raft_node_t*)arg;

    printf("Node %d: Starting on port %d\n", node->node_id, node->port);

    // Initialize Raft
    node->raft = raft_new();

    // Set up callbacks - include ALL required callbacks
    raft_cbs_t cbs = {0};
    cbs.send_requestvote = send_requestvote;
    cbs.send_appendentries = send_appendentries;
    cbs.send_snapshot = send_snapshot;
    cbs.load_snapshot = load_snapshot;
    cbs.applylog = apply_log;
    cbs.persist_metadata = persist_metadata;
    cbs.get_node_id = get_node_id;
    cbs.node_has_sufficient_logs = node_has_sufficient_logs;
    cbs.timestamp = get_time_callback;
    cbs.notify_state_event = notify_state_event;

    raft_set_callbacks(node->raft, &cbs, node);

    // Balanced election timeouts - give each node different chances
    int election_timeout;
    if (node->node_id == 1) {
        election_timeout = 2000; // Node1: 2 seconds
    } else if (node->node_id == 2) {
        election_timeout = 4000; // Node2: 4 seconds
    } else {
        election_timeout = 6000; // Node3+: 6 seconds
    }

    raft_config(node->raft, RAFT_CONFIG_ELECTION_TIMEOUT, election_timeout);
    raft_config(node->raft, RAFT_CONFIG_REQUEST_TIMEOUT, 1000); // Long request timeout

    printf("Node %d: Balanced Election timeout = %dms\n", node->node_id, election_timeout);

    // Add all nodes to the Raft cluster
    for (int i = 1; i <= cluster.node_count; i++) {
        raft_add_node(node->raft, NULL, i, (i == node->node_id));
    }

    // Create trace file
    char trace_filename[256];
    snprintf(trace_filename, sizeof(trace_filename), "%s/node_%d_trace.ndjson",
             cluster.output_dir, node->node_id);
    node->trace_file = fopen(trace_filename, "w");
    if (!node->trace_file) {
        fprintf(stderr, "Failed to create trace file for node %d\n", node->node_id);
        return NULL;
    }

    // Log initial state
    char init_data[256];
    snprintf(init_data, sizeof(init_data),
            "\"role\":\"%s\",\"state\":{\"term\":%d,\"vote\":%d,\"commit\":%ld}",
            raft_get_state_str(node->raft), (int)raft_get_current_term(node->raft),
            raft_get_voted_for(node->raft), (long)raft_get_commit_idx(node->raft));
    log_trace_event(node, "InitState", init_data);

    // Main event loop
    node->running = 1;

    while (node->running && !shutdown_signal) {
        // Process incoming messages
        simple_message_t msg;
        while (dequeue_message(node->node_id, &msg)) {
            if (msg.to == node->node_id) {
                if (msg.type == MSG_TYPE_REQUESTVOTE || msg.type == MSG_TYPE_PREVOTE) {
                    // Parse RequestVote/PreVote message
                    raft_requestvote_req_t req;
                    sscanf(msg.data, "{\"candidate_id\":%d,\"last_log_idx\":%ld,\"last_log_term\":%d}",
                           &req.candidate_id, (long*)&req.last_log_idx, (int*)&req.last_log_term);
                    req.term = msg.term;
                    req.prevote = (msg.type == MSG_TYPE_PREVOTE) ? 1 : 0; // Set prevote based on message type

                    raft_requestvote_resp_t resp;
                    raft_recv_requestvote(node->raft, raft_get_node(node->raft, msg.from), &req, &resp);

                    // Log the response
                    char resp_data[256];
                    snprintf(resp_data, sizeof(resp_data),
                            "\"vote_granted\":%d,\"term\":%d,\"prevote\":%d", resp.vote_granted, (int)resp.term, req.prevote);
                    log_trace_event(node, req.prevote ? "PreVoteResponse" : "VoteResponse", resp_data);

                    // Send response back to requester
                    simple_message_t resp_msg = (simple_message_t){0};
                    resp_msg.type = req.prevote ? MSG_TYPE_PREVOTE_RESPONSE : MSG_TYPE_REQUESTVOTE_RESPONSE;
                    resp_msg.from = node->node_id;
                    resp_msg.to = msg.from;
                    resp_msg.term = resp.term;
                    snprintf(resp_msg.data, sizeof(resp_msg.data),
                            "{\"vote_granted\":%d,\"term\":%d}", resp.vote_granted, (int)resp.term);
                    enqueue_message(&resp_msg);

                } else if (msg.type == MSG_TYPE_APPENDENTRIES) {
                    // Parse AppendEntries message
                    raft_appendentries_req_t req;
                    memset(&req, 0, sizeof(req));
                    sscanf(msg.data, "{\"prev_log_idx\":%ld,\"prev_log_term\":%d,\"leader_commit\":%d,\"n_entries\":%ld}",
                           (long*)&req.prev_log_idx, (int*)&req.prev_log_term, (int*)&req.leader_commit, (long*)&req.n_entries);
                    req.term = msg.term;
                    req.leader_id = msg.from;
                    req.n_entries = msg.n_entries;
                    req.entries = msg.entries;

                    raft_appendentries_resp_t resp;
                    raft_recv_appendentries(node->raft, raft_get_node(node->raft, msg.from), &req, &resp);

                    free_message_entries(&msg);

                    // Log the response
                    char resp_data[256];
                    snprintf(resp_data, sizeof(resp_data),
                            "\"success\":%d,\"term\":%d,\"current_idx\":%ld",
                            resp.success, (int)resp.term, (long)resp.current_idx);
                    log_trace_event(node, "AppendEntriesResponse", resp_data);

                } else if (msg.type == MSG_TYPE_REQUESTVOTE_RESPONSE || msg.type == MSG_TYPE_PREVOTE_RESPONSE) {
                    // Parse RequestVote/PreVote response
                    int vote_granted, term;
                    sscanf(msg.data, "{\"vote_granted\":%d,\"term\":%d}", &vote_granted, &term);

                    raft_requestvote_resp_t resp;
                    resp.vote_granted = vote_granted;
                    resp.term = term;

                    raft_recv_requestvote_response(node->raft, raft_get_node(node->raft, msg.from), &resp);

                    // Manual check for Leader state after receiving vote response
                    if (raft_get_state(node->raft) == RAFT_STATE_LEADER) {
                        char leader_data[128];
                        snprintf(leader_data, sizeof(leader_data),
                                "\"role\":\"leader\",\"term\":%ld,\"leader\":%d",
                                raft_get_current_term(node->raft), node->node_id);
                        log_trace_event(node, "BecomeLeader", leader_data);
                    }

                    // Log the received response
                    char resp_data[256];
                    int is_prevote = (msg.type == MSG_TYPE_PREVOTE_RESPONSE);
                    snprintf(resp_data, sizeof(resp_data),
                            "\"from\":%d,\"vote_granted\":%d,\"term\":%d,\"prevote\":%d",
                            msg.from, vote_granted, term, is_prevote);
                    log_trace_event(node, is_prevote ? "ReceivedPreVoteResponse" : "ReceivedVoteResponse", resp_data);
                }
            }
        }

        // Periodic Raft processing (this triggers timeouts, elections, etc.)
        raft_periodic(node->raft);

        // Skip log entries for now to avoid crashes

        // Sleep for a bit to avoid busy waiting
        usleep(50000); // 50ms
    }

    // Cleanup
    fclose(node->trace_file);
    raft_destroy(node->raft);

    printf("Node %d: Shutting down\n", node->node_id);
    return NULL;
}

// Signal handler
void signal_handler(int sig) {
    (void)sig;
    shutdown_signal = 1;
}

// Initialize cluster
int init_cluster(int node_count, int duration, const char *output_dir) {
    cluster.node_count = node_count;
    cluster.duration = duration;
    cluster.output_dir = strdup(output_dir);
    cluster.nodes = malloc(sizeof(my_raft_node_t) * node_count);

    if (!cluster.nodes || !cluster.output_dir) {
        return -1;
    }

    // Create output directory if it doesn't exist
    char mkdir_cmd[512];
    snprintf(mkdir_cmd, sizeof(mkdir_cmd), "mkdir -p %s", output_dir);
    int system_rc = system(mkdir_cmd);
    (void)system_rc;

    // Open merged trace file
    char merged_path[512];
    snprintf(merged_path, sizeof(merged_path), "%s/merged_trace.ndjson", output_dir);
    cluster.merged_trace_file = fopen(merged_path, "w");
    if (!cluster.merged_trace_file) {
        fprintf(stderr, "Failed to open merged trace file: %s\n", merged_path);
        return -1;
    }

    // Initialize node message queues
    for (int i = 0; i < 10; i++) {
        node_queues[i].head = 0;
        node_queues[i].tail = 0;
        node_queues[i].count = 0;
        pthread_mutex_init(&node_queues[i].mutex, NULL);
    }

    // Initialize nodes
    for (int i = 0; i < node_count; i++) {
        cluster.nodes[i].node_id = i + 1;
        cluster.nodes[i].port = 7000 + i + 1;
        cluster.nodes[i].raft = NULL;
        cluster.nodes[i].trace_file = NULL;
        cluster.nodes[i].start_time = time(NULL);
        cluster.nodes[i].running = 0;
        cluster.nodes[i].last_entry_time = 0;
    }

    return 0;
}

// Start all nodes
int start_cluster() {
    for (int i = 0; i < cluster.node_count; i++) {
        if (pthread_create(&cluster.nodes[i].thread, NULL, node_thread, &cluster.nodes[i]) != 0) {
            fprintf(stderr, "Failed to create thread for node %d\n", i + 1);
            return -1;
        }
    }
    return 0;
}

// Stop all nodes
void stop_cluster() {
    for (int i = 0; i < cluster.node_count; i++) {
        cluster.nodes[i].running = 0;
    }

    for (int i = 0; i < cluster.node_count; i++) {
        pthread_join(cluster.nodes[i].thread, NULL);
    }
}

// Cleanup resources
void cleanup_cluster() {
    // Close merged trace file
    if (cluster.merged_trace_file) {
        fclose(cluster.merged_trace_file);
        cluster.merged_trace_file = NULL;
    }

    if (cluster.nodes) {
        free(cluster.nodes);
    }
    if (cluster.output_dir) {
        free(cluster.output_dir);
    }
}

int main(int argc, char *argv[]) {
    printf("Simplified Raft Trace Generator using RedisRaft Core Library\n");
    printf("=========================================================\n\n");

    // Configuration
    int node_count = 3;
    int duration = 30; // seconds
    const char *output_dir = "/tmp/raft_traces";

    if (argc > 1) node_count = atoi(argv[1]);
    if (argc > 2) duration = atoi(argv[2]);
    if (argc > 3) output_dir = argv[3];

    // Create output directory
    char mkdir_cmd[256];
    snprintf(mkdir_cmd, sizeof(mkdir_cmd), "mkdir -p %s", output_dir);
    if (system(mkdir_cmd) != 0) {
        fprintf(stderr, "Failed to create output directory\n");
    }

    // Set up signal handling
    signal(SIGINT, signal_handler);
    signal(SIGTERM, signal_handler);

    // Initialize random seed
    srand(time(NULL));

    printf("Starting %d-node Raft cluster...\n", node_count);
    printf("Duration: %d seconds\n", duration);
    printf("Output directory: %s\n\n", output_dir);

    // Initialize cluster
    if (init_cluster(node_count, duration, output_dir) != 0) {
        fprintf(stderr, "Failed to initialize cluster\n");
        return 1;
    }

    // Start all nodes
    if (start_cluster() != 0) {
        fprintf(stderr, "Failed to start cluster\n");
        cleanup_cluster();
        return 1;
    }

    // Run for specified duration
    time_t start_time = time(NULL);
    while (time(NULL) - start_time < duration && !shutdown_signal) {
        sleep(1);
        if ((time(NULL) - start_time) % 5 == 0) {
            printf("Running... %ld/%d seconds\n", time(NULL) - start_time, duration);
        }
    }

    printf("\nShutting down cluster...\n");
    shutdown_signal = 1;
    stop_cluster();

    // Count total events
    int total_events = 0;
    for (int i = 1; i <= node_count; i++) {
        char trace_filename[256];
        snprintf(trace_filename, sizeof(trace_filename), "%s/node_%d_trace.ndjson", output_dir, i);

        FILE *f = fopen(trace_filename, "r");
        if (f) {
            char line[1024];
            int node_events = 0;
            while (fgets(line, sizeof(line), f)) {
                node_events++;
            }
            fclose(f);
            total_events += node_events;
            printf("Node %d: %d events\n", i, node_events);
        }
    }

    printf("\nTrace generation complete!\n");
    printf("Total events generated: %d\n", total_events);
    printf("Traces saved to: %s/\n", output_dir);

    cleanup_cluster();
    return 0;
}
