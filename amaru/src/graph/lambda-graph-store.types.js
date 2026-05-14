"use strict";
/**
 * lambda-graph-store.types.ts
 * Prisca-GraphRAG v2 — Λ_Ω graph hop type definitions
 *
 * Repo:    amaru/src/graph/lambda-graph-store.types.ts
 * Author:  Stephen P. Lutar Jr. <stephen@szlholdings.com>
 * Doctrine: v2 binding — no hallucinations, test×5, one-of-one
 *
 * References:
 *   - phd4_graph.md §3 Λ-receipt schema for graph hops
 *   - 99_synthesis_a11oy_rag.md §2.1 architecture
 *   - Prisca-GraphRAG v5 DOI: 10.5281/zenodo.20020846 (extend)
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.defaultDoctrineGrade = defaultDoctrineGrade;
/**
 * Convenience factory — default passing grade (all axes 9.0).
 * Replace individual axes with measured values at runtime.
 */
function defaultDoctrineGrade() {
    return {
        measurabilityHonesty: 9.0,
        cleanliness: 9.0,
        boundedness: 9.0,
        traceability: 9.0,
        falsifiability: 9.0,
        diversityWitness: 9.0,
        bekensteinBound: 9.0,
        parity: 9.0,
        dualWitness: 9.0,
    };
}
