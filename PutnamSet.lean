/-
PutnamSet — aggregator root that forces CI kernel compilation of the Putnam 2025
showcase and the SZL originals.

Wired into lakefile.lean as an `@[default_target] lean_lib «PutnamSet»` so that
`lake build` (both lean.yml and lake-build.yml) actually type-checks every file
below. Statements carry honest `REAL / DEMO / OPEN` labels in their own
docstrings; deferred proofs are explicit `sorry` (build warnings, not errors).

NOTE: BekensteinBound.lean / BekensteinBousso.lean are intentionally NOT imported
here (kept as separate experimental scaffolds).
-/
import Lutar.Putnam.P_A1
import Lutar.Putnam.P_A2
import Lutar.Putnam.P_A3
import Lutar.Putnam.P_A4
import Lutar.Putnam.P_A5
import Lutar.Putnam.P_A6
import Lutar.Putnam.P_B1
import Lutar.Putnam.P_B2
import Lutar.Putnam.P_B3
import Lutar.Putnam.P_B4
import Lutar.Putnam.P_B5
import Lutar.Putnam.P_B6
import Lutar.Putnam.SZL.LambdaEquiv
import Lutar.Putnam.SZL.ReceiptVerify
import Lutar.Putnam.SZL.Robustness
