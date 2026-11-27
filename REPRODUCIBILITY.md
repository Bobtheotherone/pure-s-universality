# Reproducing the results

For the online edition, clone the public repository and verify its working files.

```sh
git clone https://github.com/Bobtheotherone/pure-s-universality.git review-checkout
cd review-checkout
sha256sum -c SHA256SUMS
```

The separate review ZIP includes a source checkout and a portable Git bundle of the public edition. From the extracted `pure-s-universality/` directory run

```sh
sha256sum -c SHA256SUMS
sha256sum -c TRANSPORT_SHA256SUMS
git clone submission/repository.bundle ../review-checkout
git -C ../review-checkout rev-parse HEAD
```

The printed hash should equal `submission/RELEASE_COMMIT.txt` in the archive. A bundle is the source for a fresh checkout. Compiled oleans, toolchain binaries, personal correspondence and operating-system caches are excluded.

### Lean proofs

Linux x86-64 was used for the recorded build. Install the exact release from the official archive or use the package's pinned elan toolchain. The official archive and the binary checksums are in [toolchain.json](verification/toolchain.json).

```sh
review_root="$(pwd)"
lean_install_dir="$(mktemp -d)"
cd "$lean_install_dir"
curl -fL -o lean-4.33.1-linux.tar.zst https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst
echo '890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235  lean-4.33.1-linux.tar.zst' | sha256sum -c
tar --zstd -xf lean-4.33.1-linux.tar.zst
export PATH="$PWD/lean-4.33.1-linux/bin:$PATH"
cd "$review_root"
python3 scripts/check_sources.py
bash scripts/proof_replay.sh
```

Start the install commands from the root of the checkout. The script builds the 22 local mathematical modules and their pinned source dependencies, executes the differential Lean example, re-derives the theorem ledger and axiom reports, and runs an official fresh kernel on the import closure. The formal project needs no online Lake dependencies. Inspect `formal/PureS/Certified.lean` for `universal_selected_halting`, `all_program_queues` and `all_terms_native`. The body of `formal/PureS/Micro.lean` gives one native contraction per call, including the normality fallback. Its final declaration, `universal_single_contractions`, tests a fixed guard after every primitive action and rules out intermediate false positives. The explicit finite-output theorem is in `formal/PureS/FiniteOutput.lean`.

The alternate checker uses the pinned upstream checker and Batteries sources. Create its two directories in a new empty build root. This step requires network access to GitHub.

```sh
python3 scripts/rebuild_checker.py ../alternate-build
python3 scripts/replay_alternate.py ../alternate-build/checker/.lake/build/bin/lean4lean
```

The driver replays the authored and vendored modules one at a time to bound memory. Each alternate replay imports the module's dependencies. The official fresh kernel checks the combined closure from scratch. Neither step audits the semantics of the kernel itself. Numeric resource limits and the independent Python comparison are distinct from the proof terms.

### Native execution

Python 3.12 was used. The standard library suffices for the reference implementation and tests.

```sh
python3 implementation/reference/evaluator.py '1,' 101 --limit 6
python3 tests/compare_bare_macro.py
python3 tests/test_micro.py
python3 scripts/replay.py --out /tmp/pure-s-replay.json
python3 benchmarks/measure.py
```

The first command displays the three live queues at indices 0, 4 and 6. The second compares every primitive address of the boundary evaluator and the independently restarted walker. The full replay also runs the two fixed numeric programs. The eight-mode reference entry point is `micro.step(mode, term)`. Only its contracting result and one of eight modes carry over to the next call. `micro.accepting(mode, term)` implements the guard. For the bare macro as a Python API use `bare_macro.action(term)` alongside the constructor `verify_selected_s.cyclic_seed`. The separate source interpreters supply expected results in tests. The full numerical experiment caches immutable menu facts and reports the number of native contractions separately.

```sh
mathics -q -f examples/CheckWolfram.wl
# Alternatively, on a system with a licensed Wolfram kernel:
wolframscript -file examples/CheckWolfram.wl
```

The first command was executed using Mathics3 10.0.1. The proprietary Wolfram kernel was unavailable here. The Wolfram Language example implements and tests binary cyclic compilation, selection, readout and initial-empty detection.

### Papers and underlying tables

The main paper uses the AMS article class. Tectonic 0.17.0 builds both PDFs. Its TeX distribution can download missing files on first use. The bibliography, numerical primitive table, symbolic automata, fixed cyclic production table and appendix sources are included.

```sh
bash scripts/build_papers.sh
cd formal
lake env lean --run PrintCook.lean
```

The last command prints the 114 source words that determine all 912 cyclic phases. The remaining 798 appendants are empty. The raw words also appear in `examples/cook_productions.json`. The historical register assembler regenerates and checks every one of the other interpreter's 446 primitive entries. Rebuilding PDFs and measured JSON in a working checkout may change font metadata, timings and output byte hashes. The released checksums apply to the frozen files in the archive.

### Re-export and verify the Git snapshot

From a clean local clone on the release main branch, the following commands produce a new ZIP and compare every tracked byte with a second clone from its embedded bundle. The extraction path must be new.

```sh
python3 scripts/package.py ../Pure_S_Wolfram_Review_Archive.zip
python3 scripts/verify_archive.py ../Pure_S_Wolfram_Review_Archive.zip ../check-extraction
```

## Numerical examples and source provenance

With the pinned Lean binaries on PATH and the source tree built, run these commands from the repository root.

```sh
(cd formal && lake env lean --run NumericalExamples.lean)
(cd formal && lake env lean NumericalCLI.lean)
python3 scripts/check_sources.py
python3 scripts/check_notices.py
python3 tests/test_numerical_data.py
```

The CLI accepts three natural arguments, machine code, unary input, and a demonstration fuel bound, using `lake env lean --run NumericalCLI.lean E X FUEL` in the formal directory. It calls the actual certified E, sigma, H and D. Materializing the universal compiled seeds can be impractical. The source-row regressions and separately executed native-menu runs have distinct labels. The full source interpretation never participates in the target evaluator. The display and audit scripts use Poppler, and optional visual review uses PyMuPDF and Pillow. To recreate page checks run `python3 scripts/inspect_papers.py --pages /tmp/pures-pages --report /tmp/pures-pages.json` after typesetting. The source provenance and tree identifiers for the earlier research editions are recorded in [ATTRIBUTION.md](ATTRIBUTION.md) and [the manuscript record](verification/independent_checks/manuscript_edition.json).
