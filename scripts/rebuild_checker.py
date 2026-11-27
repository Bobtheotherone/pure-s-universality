"""Build the pinned alternative kernel from upstream, retaining both upstream licenses."""
from pathlib import Path
import hashlib
import io
import subprocess
import sys
import tarfile
import urllib.request

root = Path(sys.argv[1]).resolve()
root.mkdir(parents=True, exist_ok=True)
pins = [
    ("digama0/lean4lean", "8223d223ed98661882e95d9d6a7126df7097cd76", "checker",
     "3997571396f3232cabbd784fff6cf527a99370dd5874df72e6ea256fc1ce1ba0"),
    ("leanprover-community/batteries", "76e1c118b0700b4ceafe99532e887d6431625e1a", "checker-batteries",
     "2c75b373ffa5c849fa040c356cc4b31ea292bcb349d267c34132f29acae0f8d5"),
]
for repo, commit, name, digest in pins:
    url = f"https://codeload.github.com/{repo}/tar.gz/{commit}"
    data = urllib.request.urlopen(url).read()
    if hashlib.sha256(data).hexdigest() != digest:
        raise ValueError(f"digest mismatch for {repo}")
    dest = root / name
    dest.mkdir(exist_ok=False)
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as archive:
        prefix = archive.getmembers()[0].name.strip("/") + "/"
        for entry in archive.getmembers():
            if not entry.isfile():
                continue
            if not entry.name.startswith(prefix):
                raise ValueError(entry.name)
            path = (dest / entry.name[len(prefix):]).resolve()
            if not path.is_relative_to(dest):
                raise ValueError(entry.name)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(archive.extractfile(entry).read())
cfg = root / "checker/lakefile.toml"
lines = cfg.read_text().splitlines()
lines = [('path = "../checker-batteries"' if l.startswith("git =") else l)
         for l in lines if not l.startswith("rev =")]
cfg.write_text("\n".join(lines) + "\n")
for command in [["lake", "update"], ["lake", "build", "lean4lean"]]:
    subprocess.run(command, cwd=cfg.parent, check=True)
print(cfg.parent / ".lake/build/bin/lean4lean")
