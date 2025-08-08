file = open("08.08.2025_print_debug_unify_calls.md", 'r')

res = {}
total = 0
identified = 0
for l in file.readlines():
    if l.startswith("Constraints.unify in "):
        if l in res:
            res[l] += 1
        else:
            res[l] = 1
        identified += 1
    if l.startswith("Add new constraint"):
        total += 1


for k, v in res.items():
    print(f"{k.strip()} : {v} calls")
print(f"Total constraints.unify calls : {total}")
print(f"Non identified calls : {total - identified}")