#include "util.h"

void split_dirs_file(const char *path, char *dirname[], char *filename) {
    // Check for NULL or empty path
    if (path == NULL || path[0] == '\0') {
        return;
    }
    
    // Create a mutable copy of the path
    char *path_copy = malloc_string(path);
    if (path_copy == NULL) {
        return;
    }
    
    // Initialize variables for tokenization
    char *token;
    char *saveptr;
    int token_count = 0;
    
    // Temporary storage for all tokens
    char *tokens[MAX_PATH_LEN];
    
    // Tokenize the path by '/'
    token = strtok_r(path_copy, "/", &saveptr);
    
    while (token != NULL && token_count < MAX_PATH_LEN) {
        tokens[token_count] = malloc_string(token);
        if (tokens[token_count] == NULL) {
            // Handle allocation failure - clean up what we have
            for (int i = 0; i < token_count; i++) {
                free(tokens[i]);
            }
            free(path_copy);
            return;
        }
        token_count++;
        token = strtok_r(NULL, "/", &saveptr);
    }
    
    // If no tokens found, cleanup and return
    if (token_count == 0) {
        free(path_copy);
        return;
    }
    
    // Last token is the filename
    strncpy(filename, tokens[token_count - 1], MAX_FILE_LEN - 1);
    filename[MAX_FILE_LEN - 1] = '\0';
    
    // All previous tokens are directories
    for (int i = 0; i < token_count - 1; i++) {
        dirname[i] = tokens[i];
    }
    
    // Set the entry after last directory to NULL
    if (token_count > 1) {
        dirname[token_count - 1] = NULL;
    }
    
    // Free the last token (it was copied to filename)
    free(tokens[token_count - 1]);
    
    // Clean up the temporary path copy
    free(path_copy);
}