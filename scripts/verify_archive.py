"""Extract a release into an unused directory, check its manifests and compare the bundled Git commit."""
import argparse
import hashlib
from pathlib import Path, PurePosixPath
import stat
import subprocess
from zipfile import ZipFile

PREFIX = "pure-s-universality"
REQUIRED = ("LICENSE","THIRD_PARTY_NOTICES.md","THIRD_PARTY_INVENTORY.json","formal/PureS/Numerical.lean","formal/PureS/NumericalPrimitive.lean","formal/PureS/FifoArchive.lean","paper/Numerical_Certificate.tex","paper/Symbolic_Numerical.tex",
    "paper/Authors.tex", "paper/Universal_Pure_S.pdf", "paper/Universal_Pure_S.tex", "paper/references.bib",
    "paper/Symbolic_Complete_Proof.pdf", "paper/Symbolic_Complete_Proof.tex",
    "formal/PureS/Micro.lean", "formal/PureS/Certified.lean", "formal/PureS/Separation.lean",
    "formal/PureS/FiniteOutput.lean", "formal/CandidateCertificate.lean",
    "implementation/reference/micro.py", "implementation/wolfram/PureS.wl",
    "verification/clean_build.log", "verification/axioms_report.txt",
    "verification/independent_checks/lean4lean.log", "verification/theorem_ledger.json",
    "verification/coverage.json", "verification/test_results.json")


def check_manifest(directory, name):
    records = (directory / name).read_text().splitlines()
    for record in records:
        digest, rel = record.split("  ", 1)
        path = directory / rel
        if not path.resolve().is_relative_to(directory) or not path.is_file():
            raise ValueError(f"Invalid manifest entry {rel}")
        with path.open("rb") as f:
            if hashlib.file_digest(f, "sha256").hexdigest() != digest:
                raise ValueError(f"Hash mismatch in {rel}")
    return len(records)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("destination", type=Path, help="New directory for the extraction and independent clone")
    args = parser.parse_args()
    dest = args.destination.resolve()
    dest.mkdir(parents=True, exist_ok=False)
    with ZipFile(args.archive) as archive:
        if archive.testzip() is not None:
            raise ValueError("ZIP CRC failed.")
        names = archive.namelist()
        if len(set(names)) != len(names):
            raise ValueError("Duplicate ZIP pathname.")
        for item in archive.infolist():
            path = PurePosixPath(item.filename)
            if not path.parts or path.parts[0] != PREFIX or ".." in path.parts:
                raise ValueError(f"Unexpected path {path}")
            mode = item.external_attr >> 16
            if not stat.S_ISREG(mode):
                raise ValueError(f"Unexpected nonregular file {path}")
            target = Path(archive.extract(item, dest))
            target.chmod(mode & 0o777)
    tree = dest / PREFIX
    for rel in REQUIRED:
        if (tree / rel).stat().st_size == 0:
            raise ValueError(f"Empty required deliverable {rel}")
    frozen = check_manifest(tree, "SHA256SUMS")
    extras = check_manifest(tree, "TRANSPORT_SHA256SUMS")
    clone = dest / "review-checkout"
    bundle = tree / "submission/repository.bundle"
    subprocess.run(["git", "clone", "--quiet", str(bundle), str(clone)], check=True)
    commit = subprocess.check_output(["git", "-C", str(clone), "rev-parse", "HEAD"], text=True).strip()
    if (tree / "submission/RELEASE_COMMIT.txt").read_text().strip() != commit:
        raise ValueError("HEAD differs from the release receipt.")
    files = subprocess.check_output(["git", "-C", str(clone), "ls-files", "-z"]).decode().split("\0")[:-1]
    for rel in files:
        if (tree / rel).read_bytes() != (clone / rel).read_bytes():
            raise ValueError(f"Git and archive differ for {rel}")
    expected = set(files) | {"submission/RELEASE_COMMIT.txt", "submission/repository.bundle", "TRANSPORT_SHA256SUMS"}
    if {str(path.relative_to(tree)) for path in tree.rglob("*") if path.is_file()} != expected:
        raise ValueError("Unexpected file in extracted release.")
    print(f"PASS ZIP CRC, {frozen} frozen hashes, {extras} transport hashes, {len(files)} Git files and commit {commit}")


if __name__ == "__main__":
    main()
