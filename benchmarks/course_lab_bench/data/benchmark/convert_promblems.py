import csv
import json


def covert_to_dict():
    fw_all_tasks = open('system_lab_tasks.jsonl', 'w', encoding='utf-8')
    with open('lab_exam_data_20250529.csv', newline='', encoding='latin1') as csvfile:
        reader = csv.DictReader(csvfile)
        id = 0
        # instance_id,course,year,index,part_name,introduction,getting_started,The code,description,task,hint,rules,repo_location,test_method,test_results,difficluty,link
        for row in reader:
            if id > 100:  # Process up to 100 tasks
                break
            id += 1
            unique_id = row['instance_id'] + row['course'] + '_' + row['year'] + '_' + row['index']
            task = (
                '# Problem Context\n## Introduction\n'
                + row['introduction']
                + '\n## Getiting Started\n'
                + row['getting_started']
                + '\n## The Code\n'
                + row['The code']
                + '\n# Your Task \n'
                + row['description']
            )
            # "\n\n# Your Task\n" + row["task"] + "\n## Hits\n" + row["hint"]
            repo_name = 'projects/' + row['repo']
            test_method = row['test_method']
            test_results = row['test_results']
            difficulty = row['difficluty']
            link = row['link']
            task_name = 'problems/system_lab_' + row['instance_id'] + '.md'
            task_dict = {
                'task_id': 'system_lab_' + row['instance_id'],
                'task_name': task_name,
                'repo_name': repo_name,
                'task': task,
                'test_method': test_method,
                'test_results': test_results,
                'difficulty': difficulty,
                'link': link,
            }

            fw = open('problems/system_lab_' + row['instance_id'] + '.md', 'w', encoding='utf-8')
            fw.write(task + '\n')
            fw_all_tasks.write(json.dumps(task_dict) + '\n')


if __name__ == '__main__':
    covert_to_dict()
    print('Conversion completed successfully.')
