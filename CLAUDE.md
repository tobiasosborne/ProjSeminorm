# CLAUDE.md -- ProjSeminorm

## Build Command

```bash
lake build ProjSeminorm 2>&1 | tail -40
```

**NEVER run bare `lake build`** -- it rebuilds all of mathlib (~2 hours).

## Project Structure

- `ProjSeminorm/` -- Lean 4 source files
- `HANDOFF.md` -- Full mathematical analysis + 8-step implementation plan

## The Problem

Can `h_bidual` be removed from `projectiveSeminorm_tprod_of_bidual_iso` in
mathlib4 PR #33969? See `HANDOFF.md` for complete details.

## Critical API Note

In current mathlib, `‖x‖` for `x : ⨂[𝕜] i, E i` uses **injectiveSeminorm**,
NOT projectiveSeminorm. Always use `projectiveSeminorm x` explicitly.

## Workflow

1. Read `HANDOFF.md` first -- it has the full plan
2. Follow Steps 1-8 at 10-50 LOC granularity
3. Build after every step: `lake build ProjSeminorm 2>&1 | tail -40`
4. Sorries with documented goal states = success
