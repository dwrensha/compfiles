import json
from pathlib import Path

directory = Path("tryAtEachStep-out")

results = []

for filepath in directory.iterdir():
    if filepath.is_file():
        with open(filepath) as f:
            try:
                jarr = json.load(f)
                results.extend(jarr)
            except json.JSONDecodeError as e:
                pass #print(e)

results = list(filter(lambda x: x["fewerSteps"], results))
results = list(filter(lambda x: not x["message"] == "Try this: exact rfl", results))
results = list(filter(lambda x: x["goalIsProp"], results))
for r in results:
    lengthReduction = len(r["oldProof"]) - len(r["newProof"])
    r['lengthReduction'] = lengthReduction
    del r["oldProof"] # these tend to be kind of unwieldy

results.sort(key = lambda x : x["lengthReduction"], reverse = True)
print(json.dumps(results, indent = 2))
