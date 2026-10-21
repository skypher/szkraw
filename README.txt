Finite orthogonal polynomial linearization
=========================================

Public repository: https://github.com/skypher/szkraw
Lean CI: https://github.com/skypher/szkraw/actions/workflows/lean.yml

paper.tex and paper.pdf contain the manuscript. MISSION.md records the research
objective; RESEARCH.md records proof coverage, provenance and verification.
The manuscript includes a historical introduction, open problems and AI-use
disclosure. Historical priority is not claimed.

Build and verify
----------------
Required: Lean/Elan, GNU Make, Python 3, and pdfLaTeX with the packages listed in
paper.tex. The pinned toolchain is Lean 4.33.0; the exact mathlib revision is in
lean/lake-manifest.json. From the project root:

  make help
  make paper
  make lean
  make axioms
  make diagnostics
  make check

If lake is outside PATH, pass LAKE=/absolute/path/to/lake. For a fresh checkout, run `lake exe cache get` from the lean/ directory to
fetch the dependencies and mathlib artifacts using the committed manifest.
The resident REPL in tools/ is optional and is not required for any proof build.

Proof entry points
------------------
lean/Szkraw.lean imports the complete development.
lean/CheckAxioms.lean checks the exact principal statements and prints axioms.
Szkraw.geometric_criterion proves Stmt_geometric.
Szkraw.perturbation_criterion proves Stmt_perturbation, including the stated
radius, positive triangle margin and exact zeros outside the triangle.
Szkraw.full_krawtchouk_binomial_range identifies the explicit binomial measure.
Szkraw.nongeometric_perturbation_example and Szkraw.additional_geometric_class
supply the additional finite systems.
Szkraw.relatively_open_coefficient_neighborhood proves the neighborhood claim.
See RESEARCH.md for the full correspondence with manuscript statements.

Verification scope
------------------
The proofs use no sorry, admit or project-specific axioms. The audited declarations
depend only on Lean's propext, Classical.choice and Quot.sound. Exact Python checks
are diagnostics, not a substitute for all-size proofs.
deep_certificates.py, deep_order.py, path_model.py, endpoint_probe.py, rigidity_probe.py, smallr_probe.py, symmetric_probe.py, fixedr_probe.py, convexity_probe.py and signpattern_probe.py record probes of the open deep-triple problem;
none is part of make diagnostics; the linear programs need numpy and scipy and the symbolic checks sympy. The earlier independent
AI mathematical review is archived in REVIEW.md and reviews/; it is not human
peer review and is not a substitute for the Lean kernel checks.

GitHub CI
---------
The Lean proof workflow runs on pushes and pull requests. It hashes tracked Lean
sources (including CheckAxioms.lean), the toolchain and dependency configuration,
and CI implementation files. When a saved verdict for those exact inputs is
available, it returns the same green or red result before installing Lean or
restoring the large dependency cache. Paper/documentation-only changes reuse it.
Both successful and failed build verdicts are saved. Missing or invalid records
trigger a build. GitHub may evict caches; a cache miss safely rebuilds the proof.

Use Actions -> Lean proof -> Run workflow -> rebuild to force a new build. The
new result becomes the latest verdict for those inputs, including when a
transient failure has been resolved. The workflow uses the pinned Lean version,
fetches mathlib artifacts for the imported modules, builds Szkraw and elaborates
CheckAxioms.lean. Verdict-color and fingerprint behavior have isolated tests.

The public source tree omits local caches, broker state, scratch files and
third-party reference downloads; the paper provides stable source citations.
