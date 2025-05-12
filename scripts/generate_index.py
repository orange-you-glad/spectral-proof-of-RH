
#!/usr/bin/env python3
import os
import re
import json
import csv

ROOT_DIR = "src/chapters"
METADATA_DIR = "src/metadata"
os.makedirs(METADATA_DIR, exist_ok=True)

ITEM_TYPES = ["thms", "lems", "defs", "props", "cors", "rems"]

def collect_labels():
    index = []
    for section in os.listdir(ROOT_DIR):
        sec_path = os.path.join(ROOT_DIR, section)
        if not os.path.isdir(sec_path):
            continue
        for item_type in ITEM_TYPES:
            type_path = os.path.join(sec_path, item_type)
            if not os.path.isdir(type_path):
                continue
            for fname in os.listdir(type_path):
                if fname.endswith(".tex"):
                    base = os.path.splitext(fname)[0]
                    label_expected = f"{item_type[:-1]}:{base[len(item_type[:-1])+1:]}"
                    fpath = os.path.join(type_path, fname)
                    with open(fpath, "r", encoding="utf-8") as f:
                        content = f.read()
                        label_match = re.search(r"\\label\{([^}]+)\}", content)
                        if label_match:
                            label = label_match.group(1)
                            index.append({
                                "type": item_type[:-1],
                                "section": section,
                                "label": label,
                                "file": os.path.relpath(fpath)
                            })
    return index

def collect_proofs():
    mapping = []
    for section in os.listdir(ROOT_DIR):
        sec_path = os.path.join(ROOT_DIR, section, "proofs")
        if not os.path.isdir(sec_path):
            continue
        for fname in os.listdir(sec_path):
            if fname.startswith("prf_") and fname.endswith(".tex"):
                base = fname[4:-4]  # drop prf_ and .tex
                mapping.append({
                    "item": base,
                    "proof": os.path.relpath(os.path.join(sec_path, fname))
                })
    return mapping

def write_csv(data, path, headers):
    with open(path, "w", newline='', encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=headers)
        writer.writeheader()
        writer.writerows(data)

def write_json(data, path):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)

def main():
    labels = collect_labels()
    proofs = collect_proofs()

    write_csv(labels, os.path.join(METADATA_DIR, "label_map.csv"),
              ["type", "section", "label", "file"])
    write_csv(proofs, os.path.join(METADATA_DIR, "proof_map.csv"),
              ["item", "proof"])
    write_json({
        "labels": labels,
        "proofs": proofs
    }, os.path.join(METADATA_DIR, "index.json"))

    print("✅ Index generated in src/metadata/")

if __name__ == "__main__":
    main()
