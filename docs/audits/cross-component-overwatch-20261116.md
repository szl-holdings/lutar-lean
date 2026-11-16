# Cross-component formal specification repair

## Scope and source

The reviewed baseline is `lutar-lean@59d6b026b8418f59bd6535d532bdeb7551b398f0`.
This change concerns `Lutar/Doctrine/CrossComponentInvariant.lean`. It is not a
deployed-runtime security finding, a Lean-to-Python/TypeScript refinement
proof, a model qualification, or an addition to the locked eight formulas.

The baseline documented a three-way HUKLLA / OVERWATCH / DPI conjunction, but
its Boolean definition used only HUKLLA and DPI. The OVERWATCH mode and
operation parameters, and the corresponding proof hypothesis, were unused.
A local Lean witness at that baseline checked that an eligible trace with a
one-byte receipt and eight-bit capacity satisfied the composite predicate for
a write while `readOnlyMode` rejected that same operation.

## Corrected contract

`governanceAllow` now conjoins all three conditions. Its refusal theorem
includes failure of OVERWATCH allowability. This is an intentional statement
change: consumers of the old two-way refusal disjunction must account for the
third alternative. No other Lean reference to this predicate was found in the
baseline repository; downstream integrations still require separate review.

`OverwatchMode.allow` is an arbitrary proposition. The specification therefore
uses classical decidability and remains noncomputable. Decidability of equality
on its resulting Boolean is not a constructive runtime decision procedure.
No executable refinement or runtime authorization is inferred from these proofs.

## Semantic regression gate

`tools/lean/CrossComponentGuard.lean` is outside the counted `Lutar/` corpus.
The existing Lake workflow invokes it after the locked-eight axiom guard.
Its twelve named statements cover the three-premise equivalence; refusal of
unallowed, write, exec, ineligible and over-capacity cases; the allowed-operation
read-only invariant; policy refinement and preservation of refusal under a
stricter policy; and positive-read/concrete-write/concrete-exec controls.

For every statement, `Lean.collectAxioms` must stay within the existing core
trust base: `propext`, `Classical.choice`, `Quot.sound`. Unexpected dependencies
fail compilation. The explicit positive/negative statements are the semantic
controls; an allowed axiom set alone does not validate an informal claim.

## Local verification

On November 16, 2026, Lean 4.35.0 compiled the changed specification and all
twelve guard statements. All nine dependency revisions, including Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, matched the pinned manifest.
Existing dependency build caches were used; all of Mathlib was not rebuilt.
The same guard failed against the original compiled specification, including
unsolved goals and the forbidden `sorryAx` dependency from those failed proofs.

The existing canonical counter was run before and after: its declaration,
axiom-name and placeholder-token counts were unchanged. Those lexical counters
are not counts of fully proved mathematical claims. The locked formula source,
24-carrier guard, toolchain, manifest and trust policy are unchanged. A separate
fresh locked-carrier check using Lean `-t0` passed all 24 allowed-axiom records.

Hosted CI, independent review, merge, publication and deployed behavior are
separate acceptance gates. No runtime, training, authority, model or provider
setting is changed by this patch.
