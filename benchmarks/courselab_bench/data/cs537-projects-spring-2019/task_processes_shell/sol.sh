#!/bin/bash
set -e

cd ostep-projects/processes-shell

cat > wish.c << 'EOF'
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
#include <fcntl.h>

#define MAX_PATHS 100
#define MAX_ARGS 100
#define MAX_CMDS 100

char error_message[30] = "An error has occurred\n";
char *paths[MAX_PATHS];
int num_paths = 0;

void print_error() {
    write(STDERR_FILENO, error_message, strlen(error_message));
}

void free_args(char **args) {
    if (args == NULL) return;
    for (int i = 0; args[i] != NULL; i++) {
        free(args[i]);
    }
    free(args);
}

void init_paths() {
    paths[0] = strdup("/bin");
    num_paths = 1;
}

void clear_paths() {
    for (int i = 0; i < num_paths; i++) {
        free(paths[i]);
    }
    num_paths = 0;
}

char *find_executable(char *cmd) {
    static char path_buf[1024];

    for (int i = 0; i < num_paths; i++) {
        snprintf(path_buf, sizeof(path_buf), "%s/%s", paths[i], cmd);
        if (access(path_buf, X_OK) == 0) {
            return path_buf;
        }
    }
    return NULL;
}

int parse_command(char *line, char ***args_out, char **redirect_file) {
    *redirect_file = NULL;
    *args_out = NULL;

    // Check for redirection
    char *redirect_pos = strchr(line, '>');
    if (redirect_pos != NULL) {
        *redirect_pos = '\0';
        redirect_pos++;

        // Parse redirect filename
        char *token;
        char *temp = redirect_pos;
        char *filename = NULL;
        int file_count = 0;

        while ((token = strsep(&temp, " \t\n")) != NULL) {
            if (strlen(token) > 0) {
                file_count++;
                if (file_count > 1) {
                    print_error();
                    return -1;
                }
                filename = token;
            }
        }

        if (filename == NULL) {
            print_error();
            return -1;
        }

        *redirect_file = strdup(filename);
    }

    // Parse command and arguments
    char **args = malloc(MAX_ARGS * sizeof(char *));
    int argc = 0;
    char *token;

    while ((token = strsep(&line, " \t\n")) != NULL) {
        if (strlen(token) > 0) {
            args[argc++] = strdup(token);
            if (argc >= MAX_ARGS - 1) {
                break;
            }
        }
    }
    args[argc] = NULL;

    if (argc == 0) {
        free(args);
        if (*redirect_file) {
            // Redirection with no command is an error
            free(*redirect_file);
            *redirect_file = NULL;
            print_error();
            return -1;
        }
        return 0;
    }

    *args_out = args;
    return argc;
}

int execute_builtin(char **args) {
    if (strcmp(args[0], "exit") == 0) {
        if (args[1] != NULL) {
            print_error();
            return 1;
        }
        exit(0);
    } else if (strcmp(args[0], "cd") == 0) {
        if (args[1] == NULL || args[2] != NULL) {
            print_error();
            return 1;
        }
        if (chdir(args[1]) != 0) {
            print_error();
            return 1;
        }
        return 1;
    } else if (strcmp(args[0], "path") == 0) {
        clear_paths();
        for (int i = 1; args[i] != NULL; i++) {
            if (num_paths < MAX_PATHS) {
                paths[num_paths++] = strdup(args[i]);
            }
        }
        return 1;
    }
    return 0;
}

void execute_command(char **args, char *redirect_file) {
    if (args == NULL || args[0] == NULL) {
        return;
    }

    // Check if builtin
    if (execute_builtin(args)) {
        return;
    }

    // Find executable
    char *exec_path = find_executable(args[0]);
    if (exec_path == NULL) {
        print_error();
        return;
    }

    pid_t pid = fork();
    if (pid < 0) {
        print_error();
        return;
    } else if (pid == 0) {
        // Child process
        if (redirect_file != NULL) {
            int fd = open(redirect_file, O_WRONLY | O_CREAT | O_TRUNC, 0644);
            if (fd < 0) {
                print_error();
                exit(1);
            }
            dup2(fd, STDOUT_FILENO);
            dup2(fd, STDERR_FILENO);
            close(fd);
        }

        execv(exec_path, args);
        print_error();
        exit(1);
    }
    // Parent - will wait later
}

void process_line(char *line) {
    if (line == NULL) return;

    // Split by '&' for parallel commands
    char *commands[MAX_CMDS];
    int num_commands = 0;
    char *temp = line;
    char *token;

    while ((token = strsep(&temp, "&")) != NULL) {
        if (num_commands >= MAX_CMDS) break;
        commands[num_commands++] = token;
    }

    pid_t pids[MAX_CMDS];
    int pid_count = 0;

    for (int i = 0; i < num_commands; i++) {
        char **args;
        char *redirect_file;

        int result = parse_command(commands[i], &args, &redirect_file);

        if (result < 0) {
            // Error already printed
            if (redirect_file) free(redirect_file);
            continue;
        }

        if (result == 0) {
            // Empty command
            continue;
        }

        // Check if builtin
        if (execute_builtin(args)) {
            free_args(args);
            if (redirect_file) free(redirect_file);
            continue;
        }

        // Find executable
        char *exec_path = find_executable(args[0]);
        if (exec_path == NULL) {
            print_error();
            free_args(args);
            if (redirect_file) free(redirect_file);
            continue;
        }

        pid_t pid = fork();
        if (pid < 0) {
            print_error();
            free_args(args);
            if (redirect_file) free(redirect_file);
            continue;
        } else if (pid == 0) {
            // Child process
            if (redirect_file != NULL) {
                int fd = open(redirect_file, O_WRONLY | O_CREAT | O_TRUNC, 0644);
                if (fd < 0) {
                    print_error();
                    exit(1);
                }
                dup2(fd, STDOUT_FILENO);
                dup2(fd, STDERR_FILENO);
                close(fd);
            }

            execv(exec_path, args);
            print_error();
            exit(1);
        } else {
            // Parent
            pids[pid_count++] = pid;
        }

        free_args(args);
        if (redirect_file) free(redirect_file);
    }

    // Wait for all child processes
    for (int i = 0; i < pid_count; i++) {
        waitpid(pids[i], NULL, 0);
    }
}

void run_interactive() {
    char *line = NULL;
    size_t len = 0;

    while (1) {
        printf("wish> ");
        if (getline(&line, &len, stdin) == -1) {
            break;
        }
        process_line(line);
    }

    if (line) free(line);
}

void run_batch(char *filename) {
    FILE *fp = fopen(filename, "r");
    if (fp == NULL) {
        print_error();
        exit(1);
    }

    char *line = NULL;
    size_t len = 0;

    while (getline(&line, &len, fp) != -1) {
        process_line(line);
    }

    if (line) free(line);
    fclose(fp);
}

int main(int argc, char *argv[]) {
    init_paths();

    if (argc == 1) {
        // Interactive mode
        run_interactive();
    } else if (argc == 2) {
        // Batch mode
        run_batch(argv[1]);
    } else {
        print_error();
        exit(1);
    }

    clear_paths();
    return 0;
}
EOF
