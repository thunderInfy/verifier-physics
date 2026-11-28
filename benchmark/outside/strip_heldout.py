"""Write the reader-facing view of the heldout split.

heldout_stripped.jsonl keeps only the fields a blind reader may see (item_id, sentence, scheme, hypotheses,
location); every expected_*, justification, property and note field is dropped. heldout_subset_a2.txt lists the
heldout items read a second time for reader agreement: int(sha256(item_id).hexdigest(), 16) % 4 == 0.

Run: python3 -I benchmark/outside/strip_heldout.py. Prints only counts.
"""

import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parent
ALLOWED = ("item_id", "sentence", "scheme", "hypotheses", "location")


def half(source_id):
    # Same rule as FROZEN.md and run_dev.py.
    return "dev" if int(hashlib.sha256(source_id.encode()).hexdigest(), 16) % 2 == 0 else "heldout"


def in_subset(item_id):
    return int(hashlib.sha256(item_id.encode("utf-8")).hexdigest(), 16) % 4 == 0


def stripped_rows(items_path=D / "items.jsonl"):
    rows = []
    for line in items_path.read_text().splitlines():
        if not line.strip():
            continue
        o = json.loads(line)
        if half(o["source_id"]) != "heldout":
            continue
        rows.append({"item_id": o["id"], "sentence": o["sentence"], "scheme": o["scheme"],
                     "hypotheses": o["hypotheses"], "location": o["location"]})
    return rows


def main():
    rows = stripped_rows()
    (D / "heldout_stripped.jsonl").write_text(
        "".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rows))
    subset = [r["item_id"] for r in rows if in_subset(r["item_id"])]
    (D / "heldout_subset_a2.txt").write_text("".join(i + "\n" for i in subset))
    print(f"heldout items: {len(rows)}; agreement subset: {len(subset)}")


if __name__ == "__main__":
    main()
