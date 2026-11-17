"""Offline release-admission decision oracle for Lean ReleaseAdmissionWitness.

This is a conservative spec mirror, not a GitHub/HF readback or production
deployment authority. An external collector must authenticate API responses,
signature verification, run head and immutable source identity.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import isfinite
import re

_SHA = re.compile(r"[0-9a-f]{40}\Z", re.ASCII)


@dataclass(frozen=True)
class Snapshot:
    source_sha: str
    checked_sha: str | None
    published_sha: str | None
    runtime_sha: str | None
    required_ci_green: bool
    signature_verified: bool
    evidence_fresh: bool
    runtime_healthy: bool
    owner_approved: bool
    maintenance_open: bool


@dataclass(frozen=True)
class Decision:
    status: str
    holds: tuple[str, ...]

    @property
    def eligible(self) -> bool:
        return self.status == "ELIGIBLE_NOT_DEPLOYED"


def _valid_sha(sha: object) -> bool:
    return isinstance(sha, str) and _SHA.fullmatch(sha) is not None


def admit(e: Snapshot) -> Decision:
    """Fail closed on missing, malformed, mismatched, or stale observations."""
    holds: list[str] = []
    if not _valid_sha(e.source_sha):
        holds.append("SOURCE_UNVERIFIED")
    if not _valid_sha(e.checked_sha) or e.checked_sha != e.source_sha:
        holds.append("CHECKED_HEAD_MISMATCH")
    if not _valid_sha(e.published_sha) or e.published_sha != e.source_sha:
        holds.append("PUBLISHER_MISMATCH")
    if not _valid_sha(e.runtime_sha) or e.runtime_sha != e.source_sha:
        holds.append("RUNTIME_SOURCE_MISMATCH")
    for value, reason in (
        (e.required_ci_green, "REQUIRED_CI_NOT_GREEN"),
        (e.signature_verified, "SIGNED_RECEIPT_MISSING"),
        (e.evidence_fresh, "EVIDENCE_EXPIRED"),
        (e.runtime_healthy, "RUNTIME_READBACK_MISSING"),
        (e.owner_approved, "OWNER_APPROVAL_MISSING"),
        (e.maintenance_open, "MAINTENANCE_WINDOW_CLOSED"),
    ):
        if value is not True:  # reject truthy values, including 1 and "true"
            holds.append(reason)
    return Decision("HOLD" if holds else "ELIGIBLE_NOT_DEPLOYED", tuple(holds))


def effective_score(e: Snapshot, lambda_score: float) -> float:
    """A positive advisory score cannot override a hard admission HOLD."""
    if (type(lambda_score) not in (float, int)
            or not isfinite(lambda_score)
            or not 0.0 <= lambda_score <= 1.0):
        raise ValueError("lambda_score must be a finite number in [0, 1]")
    return float(lambda_score) if admit(e).eligible else 0.0
