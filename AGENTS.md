# Agent Instructions

This project uses **bd** (beads) for issue tracking. Run `bd onboard` to get started.

## Project Context

Lean 4 formalization project investigating whether `h_bidual` can be removed from
`projectiveSeminorm_tprod_of_bidual_iso` (mathlib4 PR #33969). See `HANDOFF.md` for
full mathematical analysis and session log.

## Quick Reference

```bash
bd ready              # Find available work
bd show <id>          # View issue details
bd update <id> --status in_progress  # Claim work
bd close <id>         # Complete work
bd sync               # Sync with git
```

## Build Command

```bash
lake build ProjSeminorm 2>&1 | tail -40
```

**NEVER run bare `lake build`** — it rebuilds all of mathlib (~2 hours).

## Critical API Note

`‖x‖` for `x : ⨂[𝕜] i, E i` uses **injectiveSeminorm**, NOT projectiveSeminorm.
Always use `projectiveSeminorm x` explicitly.

## Issue Tracker

- Epic: `ProjSeminorm-dtv` (22 sub-issues across 8 steps)
- Critical path: Steps 1→2→3→4→5 (linear dependency chain)
- Steps 6 & 7 branch after Step 5; Step 8 merges all
- Use `bd graph --all` to see the full dependency graph

## Landing the Plane (Session Completion)

**When ending a work session**, you MUST complete ALL steps below. Work is NOT complete until `git push` succeeds.

**MANDATORY WORKFLOW:**

1. **File issues for remaining work** - Create issues for anything that needs follow-up
2. **Run quality gates** (if code changed) - `lake build ProjSeminorm 2>&1 | tail -40`
3. **Update issue status** - Close finished work, update in-progress items
4. **Update HANDOFF.md session log** - Append what was done, current state, next steps
5. **PUSH TO REMOTE** - This is MANDATORY:
   ```bash
   git pull --rebase
   bd sync
   git push
   git status  # MUST show "up to date with origin"
   ```
6. **Verify** - All changes committed AND pushed
7. **Hand off** - Provide context for next session

**CRITICAL RULES:**
- Work is NOT complete until `git push` succeeds
- NEVER stop before pushing - that leaves work stranded locally
- NEVER say "ready to push when you are" - YOU must push
- If push fails, resolve and retry until it succeeds

