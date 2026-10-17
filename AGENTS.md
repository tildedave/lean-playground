# AGENTS.md

Guidance for AI assistants (Claude and others) working in this repository.

## What this repo is

Solutions to exercises from Aluffi's *Algebra: Chapter 0*. Many are written up
in `solutions.tex` (compiled to `solutions.pdf`); others exist only in my paper
notebook. We are beginning to formalize some of these solutions in Lean 4
(with Mathlib).

The Lean project lives in `algebra-chapter-0/`:

- `lakefile.toml`, `lean-toolchain`: Lean and Mathlib versions are pinned
  (currently `v4.35.0`). `autoImplicit` is off.
- `AlgebraChapter0.lean`: the library root, which imports every module.
- `AlgebraChapter0/`: the formalized solutions.

Run Lean commands from inside `algebra-chapter-0/`: `lake build` builds
everything, and `lake env lean AlgebraChapter0/<File>.lean` checks a single
file.

## How we work together

**The human drives.** I write most of the Lean myself in VSCode. The point of
this project is for me to learn by doing the formalization, so the assistant is
a helper I call on when I'm stuck, not the primary author.

**Work in my checkout, not a worktree.** I edit files on `main` in the main
checkout while we talk, and you need to see those edits. Don't create
worktrees or branches. Re-read a file before answering questions about it,
since I may have changed it since you last looked. If you find yourself in a
worktree anyway, tell me, and read files from the main checkout instead.

When I ask for help:

- **Scope tightly.** Work on the specific `sorry`, lemma, or error I point to.
  Don't rewrite surrounding proofs, rename things, restructure files, or
  "clean up" code I didn't ask about.
- **Keep my statements fixed.** Don't change a theorem's statement to make it
  easier to prove. If you think the statement is wrong or awkwardly phrased,
  say so and explain why, and let me decide.
- **Explain the proof, not just the tactics.** Briefly say what the key idea
  is, which Mathlib lemmas you used and why, and how it lines up with the
  informal argument (in `solutions.tex` if it's written up there). A short
  explanation beats a long one.
- **Prefer readable proofs.** Favor structured proofs (`have`, `obtain`,
  `calc`, `constructor`) that mirror the paper argument over opaque one-liners.
  Using `simp`, `aesop`, `omega`, `ring`, `linarith`, etc. is fine. If a
  heavy-automation proof is the only thing that works, mention that.
- **Hints first when asked.** If I ask for a hint, give a hint: the next step,
  the relevant Mathlib lemma, or the right tactic. Don't give the full proof.
- **No spoilers.** Don't reveal the mathematical idea of a solution that I
  haven't told you: the key construction, the witness, the map, the trick.
  This holds even when I ask a narrower question (imports, statement syntax,
  a skeleton). If an answer would need the idea, leave a placeholder (`?_`,
  `sorry`) or ask me what I have in mind. The same goes for pointing out that
  Mathlib already has the result: ask before naming it.
- **Verify before claiming success.** Check that the proof compiles (e.g.
  `lake build` or `lake env lean <file>`) and report the actual result. Never
  say a proof works if you haven't checked it. If you couldn't check it, say
  so.
- **No cheating.** Don't introduce `sorry`, `admit`, new `axiom`s, or
  `native_decide` to close goals unless I explicitly ask for it.
- **Name real lemmas only.** Don't make up Mathlib lemma names. Search Mathlib
  (`exact?`, `apply?`, `rw?`, grepping `.lake/packages/mathlib`) or say you're
  unsure.

## Relationship to the informal solutions

- `solutions.tex` is not a complete record: some solutions are only in my
  paper notebook. If an exercise isn't in `solutions.tex`, don't assume it
  hasn't been solved or invent an informal argument. Ask me how I solved it,
  or work from what I tell you.
- Don't edit `solutions.tex` unless I ask.
- If formalizing exposes a gap or error in a written solution, point it out
  (citing the exercise number). Don't silently fix it in either place.
- Mathlib often phrases things differently than Aluffi (e.g. via
  `Function.Exact`, `Submodule`, `LinearMap.ker`, `CategoryTheory`). It's fine
  to use Mathlib's idioms. When the translation isn't obvious, add a short
  comment explaining how the Lean statement corresponds to the exercise.

## Conventions

- Organize Lean files by chapter under `AlgebraChapter0/`, import each new
  file from `AlgebraChapter0.lean`, and put the exercise number in a
  docstring on each theorem, e.g. `/-- Aluffi III.7.1 -/`.
- Match the existing style of whatever file you're editing.
- Don't add or upgrade dependencies (including bumping Mathlib or the Lean
  toolchain) without asking.
- Don't commit unless I ask.
