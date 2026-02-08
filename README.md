# ProjSeminorm

Lean 4 formalization investigating whether the projective tensor seminorm is
multiplicative on pure tensors **without** assuming isometric bidual embedding.

## The Question

Given a finite family of seminormed spaces `{E_i}` over a nontrivially normed field,
is it true that

```
projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖
```

for all `m : Π i, E i`, **without** assuming `‖inclusionInDoubleDual(m i)‖ = ‖m i‖`?

Over `ℝ` and `ℂ`, the answer is yes (by Hahn-Banach). Over general nontrivially normed
fields (e.g. non-archimedean), this is an open question.

## Context

- **Mathlib PR**: [#33969](https://github.com/leanprover-community/mathlib4/pull/33969)
  proves this with the `h_bidual` hypothesis
- **Lead**: Schneider's [NFA notes](https://ivv5hpp.uni-muenster.de/u/pschnei/publ/lectnotes/nfa.pdf),
  Prop 17.4 (ultrametric case)
- See `HANDOFF.md` for full mathematical analysis and implementation plan
- See `dgemail.txt` for the original problem statement

## Building

```bash
lake build ProjSeminorm 2>&1 | tail -40
```

## License

Apache 2.0
