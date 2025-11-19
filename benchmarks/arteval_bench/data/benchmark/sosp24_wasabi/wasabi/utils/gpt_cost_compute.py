import os
import sys
import tiktoken

if len(sys.argv) != 2:
  print("Usage: python script.py <path_to_project>")
  sys.exit(1)

project_path = sys.argv[1]
token_price = 0.01 / 1000 # $0.01 per 1k prompt tokens per OpenaAI documentation
number_of_rounds = 5 # number of questions/interactions with GPT per source file

def count_tokens_in_file(file_path):
  encoder = tiktoken.encoding_for_model("gpt-4")
  with open(file_path, 'r', encoding='utf-8') as file:
    content = file.read()
  tokens = encoder.encode(content)
  return len(tokens)

def should_include_file(file_path):
  return not ('/test/' in file_path or file_path.split('/')[-1].startswith('Test'))

def calculate_project_cost(root_dir):
  total_tokens = 0
  for subdir, dirs, files in os.walk(root_dir):
    for file in files:
      if file.endswith('.java'):
        file_path = os.path.join(subdir, file)
        if should_include_file(file_path):
          file_tokens = count_tokens_in_file(file_path)
          total_tokens += file_tokens
          print(f"Processed {file}: {file_tokens} tokens")
  total_cost = total_tokens * token_price * (0.98 + 0.02 * number_of_rounds)
  return total_tokens, total_cost

total_tokens, total_cost = calculate_project_cost(project_path)

print(f"Total tokens: {total_tokens}")
print(f"Total cost at ${token_price*1000} per 1k tokens: ${total_cost:.4f}")