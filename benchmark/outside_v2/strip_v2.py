"""Write the reader-facing view of outside benchmark v2.

stripped.jsonl keeps only the fields a blind reader may see (id, sentence, scheme, hypotheses, location) for all 95
items; every expected_*, justification, property and source_id field is dropped. subset_a2.txt lists the items read
a second time for reader agreement: int(sha256(id).hexdigest(), 16) % 4 == 0, with id encoded as UTF-8.

Run: python3 -I benchmark/outside_v2/strip_v2.py. Prints only counts.
"""

import hashlib
import json
from pathlib import Path

D = Path(__file__).resolve().parent
ALLOWED = ("id", "sentence", "scheme", "hypotheses", "location")


def in_subset(item_id):
    return int(hashlib.sha256(item_id.encode("utf-8")).hexdigest(), 16) % 4 == 0


def stripped_rows(items_path=D / "items.jsonl"):
    rows = []
    for line in items_path.read_text().splitlines():
        if not line.strip():
            continue
        o = json.loads(line)
        rows.append({k: o[k] for k in ALLOWED})
    return rows


def main():
    rows = stripped_rows()
    (D / "stripped.jsonl").write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rows))
    subset = [r["id"] for r in rows if in_subset(r["id"])]
    (D / "subset_a2.txt").write_text("".join(i + "\n" for i in subset))
    print(f"items: {len(rows)}; agreement subset: {len(subset)}")


if __name__ == "__main__":
    main()
