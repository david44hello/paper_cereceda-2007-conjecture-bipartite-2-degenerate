# The Cereceda (2007) conjecture holds for bipartite 2-degenerate graphs — Lean 4 proof

The paper: https://doi.org/10.5281/zenodo.23731060

This folder is a Lean 4 proof of the paper's results.

## Directions to Reproduce

Install Git, Lean (https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone https://github.com/david44hello/paper_cereceda-2007-conjecture-bipartite-2-degenerate.git
cd paper_cereceda-2007-conjecture-bipartite-2-degenerate/lean
./check.sh
```

Its last lines look like:

```
stmt_diff: 96 pairs, 0 not allowed
PASS: project builds; source policy passes; audit OPEN 0 / VIOLATION 0; every X_proved has the type of X.
```

8 claims use results that the paper cites, and 3 take a fact about planar graphs as a hypothesis;
[AUDIT.md](AUDIT.md) names them, claim by claim.

Copyright (C) Dave Goel 2026--now. All rights reserved.
