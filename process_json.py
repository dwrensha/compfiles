import json
from pathlib import Path

directory = Path("try-at-each-step-out")

results = []

for filepath in directory.iterdir():
    if filepath.is_file():
        #print(f"File: {filepath}")
        with open(filepath) as f:
            try:
                jarr = json.load(f)
                results.extend(jarr)
            except json.JSONDecodeError as e:
                pass #print(e)

results = list(filter(lambda x: x["fewerSteps"], results))
results = list(filter(lambda x: not x["message"] == "Try this: exact rfl", results))
results = list(filter(lambda x: x["goalIsProp"], results))
results.sort(key = lambda x : x["lengthReduction"], reverse = True)
print(json.dumps(results, indent = 2))
