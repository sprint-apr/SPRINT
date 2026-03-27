import glob

def parse_file_to_set(file_path):
    result_set = set()

    with open(file_path, 'r') as file:
        lines = file.readlines()
        for line in lines:
            # split on ": " to separate prefix and number list
            try:
                prefix, numbers = line.split(': ')
            except:
                return set()
            # split number list into individual items and add to Set
            numbers_list = numbers.split(', ')
            result_set.update(f"{prefix.strip()}_{num.strip()}" for num in numbers_list)

    return result_set

result = set()
for tool_result in glob.glob("tool/resources/*.lst"):
    result = result.union(parse_file_to_set(tool_result))

result = list(result)
result.sort()
for bug in result:
    print(bug)