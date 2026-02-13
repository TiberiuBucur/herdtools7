import os
from glob import glob
from pathlib import Path

record = "AArch64"

cats = [
    "cats/aarch64.cat"
]

def _list_files_under(path, pattern):
    matches = glob(os.path.join(path, pattern))
    return sorted(m.replace(os.sep, '/') for m in matches)

cfgs = _list_files_under('cfgs', '*.cfg')
illustrative_tests = _list_files_under('tests', '*.litmus')
