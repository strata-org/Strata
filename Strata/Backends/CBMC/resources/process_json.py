import json
import sys

from defaults import default_keys

def traverse_dict(data, max_depth, current_depth=0, path=""):
    if current_depth >= max_depth:
        return
    
    if isinstance(data, dict):
        for key in data:
            if path == "symbolTable" and key in default_keys:
                continue
            current_path = f"{path}.{key}" if path else key
            print(f"Level {current_depth + 1}: {current_path}")
            traverse_dict(data[key], max_depth, current_depth + 1, current_path)

def print_non_defaults(data):
    for key in data["symbolTable"]:
        if key not in default_keys:
            print(json.dumps(data["symbolTable"][key], indent=4))

def print_defaults(data):
    obj = {}
    for key in data["symbolTable"]:
        if key in default_keys:
            obj[key] = data["symbolTable"][key]
    final_obj = {"sybolTable": obj}
    print(json.dumps(final_obj, indent=4))

def combine(defaults_path, lean_out_path):
    with open(defaults_path) as f:
        defaults = json.load(f)
        with open(lean_out_path) as f_lean:
            lean = json.load(f_lean)

            for k,v in lean.items():
                defaults["symbolTable"][k] = v
    print(json.dumps(defaults, indent=2))

def compare_objs(o1, o2, path=""):
    diffs = []
    
    if type(o1) != type(o2):
        return [(path, o1, o2)]
    
    if isinstance(o1, dict):
        all_keys = set(o1.keys()) | set(o2.keys())
        for key in all_keys:
            # Ignore locations since we can't generate them from Strata
            if key == "#source_location" or key == "#end_location" or key == "file" or key == "working_directory" or key == "module":
                continue
            current_path = f"{path}.{key}" if path else key
            if key not in o1:
                diffs.append((current_path, None, o2[key]))
            elif key not in o2:
                diffs.append((current_path, o1[key], None))
            else:
                diffs.extend(compare_objs(o1[key], o2[key], current_path))
    elif isinstance(o1, list):
        max_len = max(len(o1), len(o2))
        for i in range(max_len):
            current_path = f"{path}[{i}]"
            if i >= len(o1):
                diffs.append((current_path, None, o2[i]))
            elif i >= len(o2):
                diffs.append((current_path, o1[i], None))
            else:
                diffs.extend(compare_objs(o1[i], o2[i], current_path))
    elif o1 != o2:
        diffs.append((path, o1, o2))
    
    return diffs

def compare(fp1, fp2):
    with open(fp1) as f1, open(fp2) as f2:
        obj1 = json.load(f1)
        obj2 = json.load(f2)
        diffs = compare_objs(obj1, obj2)
        
        if not diffs:
            print("No differences found")
            return
        
        # Find smallest diff by path length
        smallest_diff = min(diffs, key=lambda x: len(x[0]))
        path, val1, val2 = smallest_diff
        
        print(f"Smallest diff at path: {path}")
        print(f"Value 1: {json.dumps(val1, indent=2)}")
        print(f"Value 2: {json.dumps(val2, indent=2)}")


if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("Usage: python main.py {combine, compare} <json_file> <max_depth>")
        sys.exit(1)

    op = sys.argv[1]
    json_file = sys.argv[2]


    with open(json_file, 'r') as f:
        data = json.load(f)

    # max_depth = int(sys.argv[2])
    # traverse_dict(data, max_depth)

    # print_non_defaults(data)

    # print_defaults(data)

    if op == "combine":
        lean_json_file = sys.argv[3]
        combine(json_file, lean_json_file)
    elif op == "compare":
        compare(sys.argv[2], sys.argv[3])
    else:
        print("Usage: python main.py {combine, compare} <json_file> <max_depth>")
        sys.exit(1)