import json


def read_txt_file(file_path):
    with open(file_path, encoding='utf-8') as f:
        content = f.read()
    return content


cache_prompt = read_txt_file('cache_sys_prompt.txt')

for trace in ['alibaba-storage', 'ra-fwe', 'ra-multikey', 'tencentblock-storage']:
    out = {
        'id': 0,
        'sys_prompt': cache_prompt,
        'user_prompt': '',
        'response': '',
        'metadata': {
            'scenario': 'system_algorithm_design',
            'task': 'cache_algorithm',
        },
    }

with open('cache_benchmarks_with_traces.jsonl', 'w', encoding='utf-8') as f:
    json.dump(out, f, ensure_ascii=False)
    f.write('\n')  # Ensure each JSON object is on a new line
