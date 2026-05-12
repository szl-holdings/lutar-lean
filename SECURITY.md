# Security Policy

## Supported Versions

`lutar-lean` is a Lean 4 / Mathlib formalisation of the Lutar Invariant axioms. The project ships with no runtime surface, no network access, and no user data; the entire artefact is a set of `.lean` source files plus a CI workflow. Security risk is therefore narrowly scoped to (a) Lean toolchain integrity and (b) supply-chain integrity of the `Mathlib` and `Lean 4` dependencies pulled by `lake`.

| Version | Supported |
|---------|-----------|
| `main` (latest commit) | ✅ Yes — actively maintained |
| Tagged releases | ✅ Yes — supported for the lifetime of the corresponding Zenodo deposit |
| Forks and personal branches | ❌ No — please open a PR against `main` for any change you want supported |

## Reporting a Vulnerability

If you discover a security issue — for example, a build configuration that pulls a tampered `Mathlib`, a CI workflow that leaks secrets, a `lake` manifest that points at a typosquatted dependency, or a Lean proof that is admit/sorry-laundered in a way the README does not disclose — please report it privately to:

- **Email:** stephen@szlholdings.com
- **Subject prefix:** `[lutar-lean security]`
- **Encryption:** PGP optional; if you have it, fetch the public key from the `KEYS` file at the repository root (planned for v13).

Please include:

- A short description of the issue.
- Affected commit SHA(s).
- Reproduction steps.
- The impact you believe the issue has (e.g., "a fork of Mathlib could be substituted under build hash X").

I aim to respond within **72 hours** for an initial acknowledgement and within **30 days** for a fix or a public dated waiver. The project is single-maintainer; that is the honest SLA.

## Disclosure Policy

This project follows **coordinated disclosure**:

1. You report privately as above.
2. I acknowledge within 72 hours and propose a fix timeline.
3. Once a fix is merged, I publish a CHANGELOG entry and credit the reporter (unless they prefer to remain anonymous).
4. If a CVE is appropriate, I will request one via GitHub's advisory database.

## Scope

In-scope:

- The Lean source under `Lutar/*.lean`, `Lutar.lean`, `Main.lean`, `MainRef.lean`, `RefVectors.lean`.
- The build configuration in `lakefile.lean` and `lean-toolchain`.
- The CI workflow under `.github/workflows/`.
- The reference data file `reference-vectors.json` used by the Lean test surface.

Out-of-scope:

- Vulnerabilities in upstream `Lean 4` or `Mathlib` themselves — please report those to their respective maintainers.
- Theoretical disagreements with the axioms (please open a regular issue).
- The runtime TypeScript implementations in `packages/ouroboros-invariant/` of the broader SZL Holdings platform — those have their own security policy at `https://github.com/szl-holdings/szl-holdings-platform/security/policy`.

## Hardening Notes

The Lean source has no runtime side effects; the only execution surface is `lake exe check` in CI, which compiles the proofs and emits a count of remaining `sorry` sites. The CI workflow:

- Pins `lean-toolchain` to an explicit version.
- Uses `actions/checkout@v4` and `leanprover/lean-action@v1` (both pinned by SHA in the workflow file — a v13 hardening pass will replace any version-tag pins with full SHAs).
- Does not write to any external store, does not require any secrets, and runs entirely on the GitHub-hosted runner.

If you find a way to escape that envelope, that is a security report under this policy.

— Stephen P. Lutar Jr.
SZL Holdings
2026-05-12
