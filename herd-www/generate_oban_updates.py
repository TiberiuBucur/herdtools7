#!/usr/bin/env python3
import json
import sys

def main(argv):
    updates = [a for a in argv if a.strip()]
    # Keep stable order for deterministic output
    updates = sorted(updates)
    json.dump(updates, sys.stdout)

if __name__ == '__main__':
    main(sys.argv[1:])
