"""Export one clean Git commit with its tracked contents, full history and transport hashes."""
import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
import time
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "pure-s-universality"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def add_bytes(archive, name, data, mode, stamp):
    entry = ZipInfo(f"{PREFIX}/{name}", stamp)
    entry.create_system = 3
    entry.external_attr = mode << 16
    entry.compress_type = ZIP_DEFLATED
    archive.writestr(entry, data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    if git("status", "--porcelain"):
        raise SystemExit("Export needs a clean tracked checkout.")
    output = args.output.resolve()
    if output.is_relative_to(ROOT):
        raise SystemExit("Place the archive outside the checkout.")
    output.parent.mkdir(parents=True, exist_ok=True)
    commit = git("rev-parse", "HEAD").strip().decode()
    stamp = time.gmtime(int(git("show", "-s", "--format=%ct", commit)))[:6]
    with tempfile.TemporaryDirectory(dir=output.parent) as temp:
        scratch = Path(temp)
        bundle = scratch / "repository.bundle"
        git("bundle", "create", str(bundle), "HEAD", "refs/heads/main")
        extras = {"submission/RELEASE_COMMIT.txt": (commit+"\n").encode(),
                  "submission/repository.bundle": bundle.read_bytes()}
        extras["TRANSPORT_SHA256SUMS"] = "".join(
            f"{hashlib.sha256(data).hexdigest()}  {name}\n"
            for name, data in sorted(extras.items())).encode()
        archive_path = scratch / "release.zip"
        with ZipFile(archive_path, "w") as archive:
            for item in git("ls-tree", "-rz", "--full-tree", commit).split(b"\0"):
                if not item:
                    continue
                metadata, filename = item.split(b"\t", 1)
                mode, kind, object_id = metadata.decode().split()
                if kind != "blob":
                    raise SystemExit("A non-blob tree entry needs an explicit export rule.")
                data = git("cat-file", "blob", object_id)
                add_bytes(archive, os.fsdecode(filename), data, int(mode, 8), stamp)
            for name, data in sorted(extras.items()):
                add_bytes(archive, name, data, 0o100644, stamp)
        with ZipFile(archive_path) as archive:
            if archive.testzip() is not None:
                raise SystemExit("Archive integrity validation failed.")
        archive_path.replace(output)
    with output.open("rb") as frozen:
        digest = hashlib.file_digest(frozen, "sha256").hexdigest()
    print(f"{digest}  {output.name}")


if __name__ == "__main__":
    main()
