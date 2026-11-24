# TPP-2026: Presentation Plan

## Talk metadata

- Title: Implementing MLTT in Rocq with mutual inductive types: challenges and techniques
- Venue: TPP 2026 (TPP 2026 will be held on November 16 (Mon.)–17 (Tue.), 2026, at the Tokyo office of the RIKEN Center for Advanced Intelligence Project (RIKEN AIP).) I am presenting at 15:50 on November 16 (Mon.), 2026.
- Slot: 12–15 minutes → roughly 10–14 slides
- Speaker: Pierre-Emmanuel WULFMAN, Graduate School of Mathematics, Nagoya University. **Sole author:** the speaker wrote and submitted the abstract alone, and the programme lists only them.
- Supervisor: **Jacques Garrigue**. Not a co-author. No thank-you line on the slides (removed at the speaker's request). He pointed the speaker to `Guarded.` (he knew it from his work with coinductive types; he did not "find" it) and gave feedback on the central message He gives his own talk just before this one, so a one-sentence link to it at the start is optional.

## Audience

Academic workshop audience; familiar with proof assistants (mostly Rocq users, but not only), but not with this project. Many will never have used `with` for anything substantial. The speaker's own supervisor had not seen it used this way.

## Goal

An experience report from a Rocq user: share what was learned about using mutual inductive definitions (`with`), the **second method** below, to handle **cyclic definitions**. The lessons apply whenever definitions depend on each other cyclically, not only in type theory. The speaker's formalisation of dependent type theory is the running example, **not the subject** of the talk.

**Central message** (the supervisor's feedback, endorsed by the speaker): **mutual lemmas, `Lemma … with …`, are very powerful.** You work at another level, proving a whole family of statements together and calling any of them anywhere. Few people know about them; the supervisor didn't. Everything else in the talk builds up to this or qualifies it. **Storyline:** two ways to define the cycle, and how that design choice affects how you *state* and *prove* lemmas. The dead ends (well-formed-by-construction syntax, `Fixpoint` judgements) are **not** on the slides; they can come up in Q&A.
- **Key argument:** with `Inductive … with …`, `Scheme`/`Combined Scheme` also give you method 1's style of induction principle, while plain `induction` still works per sort. So `with` lets you work in **both** styles, and the speaker concludes it is strictly better. Present this as the speaker's conclusion from the verified comparison.
- **Expected question:** "But method 1 lets you write one function for all sorts, e.g. substitution." **Speaker's answer:** you still define substitution on every case of the syntax in both designs. With `with` you write `Fixpoint subst_ty … with subst_tm …`, and a wrapper that sends each sort to its operation (`match s with TY => subst_ty | TM => subst_tm end`) gives the single interface back. Put this in `speaker-notes.md`.
- **Readability:** the `with` definitions are more readable. This is the speaker's opinion, so present it as such.
- **The cost:** the more lemmas you put in one `Lemma … with …` clause, the longer the guard check takes, exponentially. That is the point of the "catch" slide; it's not about how the development scales.

The commonly recommended sort-indexed family (the **first method**) is the familiar baseline. Explain `with` from first principles, show the practical knowledge that the official documentation's few examples don't give, and give honest trade-offs. Don't oversell it.

## Narrative

### The problem

- In the simply typed λ-calculus, the grammar sorts depend on each other like a tree, so each can be defined on its own, one after another:

  ```coq
  Inductive preType := Base | Func : preType -> preType -> preType | ...
  Inductive preTerm := ... | Lamb : preType -> preTerm -> preTerm | ...
  Inductive preCtx  := One | Ext : preCtx -> preTerm -> preType -> preCtx.
  ```

- In dependent type theory the dependencies are **cyclic** (contexts ↔ types ↔ terms ↔ substitutions; same for the judgements), so the definitions cannot be given one at a time — they must be defined all at once.

### First method — the usual advice ("GADT-like")

- A single inductive family indexed by a sort:

  ```coq
  Inductive Sort := CTX | TYP | TERM.
  Inductive term : Sort -> Type :=
  | ctx_one  : term CTX
  | tm_lamb  : term TYP -> term TERM -> term TERM
  | ...
  ```

- Recommended by the supervisor, colleagues, and examples found online.
- **Not used anywhere in the current code.** On the slides (4, 13, and the supplement) it is a translation of the speaker's own judgements into one `Inductive J : Sort -> Prop` (`Sort` = one constructor per judgement form), checked by Rocq. `demo/method1.v` translates **all 8 judgements and all rules** of 2.3 the same way.
- Decided: **no citation** for method 1 on the slides (the speaker chose not to cite Kaposi & von Raumer; see Bibliography).

### Second method — the speaker's approach (`with`)

- Keep each sort as its own inductive, exactly as in STLC, and join the cyclic ones with Rocq's mutual-inductive keyword `with`. Each definition stays unchanged and reads like the paper's grammar.
- Applied (in 2.3) to the pre-syntax, only where it's truly cyclic (`preSubs … with preTerm`), and to all 8 judgements (`CtxJG … with SubsJG … with TypeJG … with TermJG … with eq_ctx … with eq_subs … with eq_type … with eq_term`).
- Used throughout the current code (see "Source of truth").
- Points to cover: lessons about **mutual definitions**, not about extensionality or conversion. The speaker's account, backed by the git history:
  1. **Dead end: syntax that is well-formed by construction.** Commits `ded8a9e`, `46ef803` and `f0559d5` ("cannot get the equality in the dependent term") show the attempts. The result was rigid and hard to write, and Rocq has no induction-induction. So: pre-syntax that can express anything, with separate judgements. The speaker likes this split.
  2. **Dead end: judgements as `Fixpoint`.** Commits `877e25b`, `2f2c924` (`Program Fixpoint … {measure}`, which gave an unreadable OCaml error) and `Def2.v` (mutual `Fixpoint … {struct}`) show the attempts. A judgement needs other judgements (a context needs its types, which need their context…), and termination couldn't be shown. Whether conversion was the cause is **uncertain**, so present it as the speaker's experience. **Inductive `Prop` with `with`** gives far more freedom: each rule is a constructor.
  3. **The real difficulty: proving lemmas over the cycle.** Example: the "presupposition" lemmas, called `*_press` in the code. The speaker calls them "coherence lemmas" (if a type is well-formed in Γ, then Γ is well-formed, and so on). Induction on one judgement brings up another, for example a `preSubs` inside `preTerm`. Strategies tried, in order:
     - (a) Nested second induction: this duplicates the same proof for each sort, so there's no longer a single source of truth.
     - (b) Prove the type lemma *assuming* the subs lemma, then prove the subs lemma using it, then restate the type lemma without the assumption. It works but needs boilerplate.
     - (c) One lemma stated with `/\`. **It does not work on its own:** after `split` you have two independent goals, each with its own non-mutual induction, so the other half is never available; there is nothing to do induction on *before* splitting. A mutual principle (`Combined Scheme`) applied *before* `split` is what makes it work.
     - (d) **Mutual lemmas: `Lemma A … with B … with C …`.** Documentation, checked online in the master reference manual on 2026-11-16:
       - It appears **only once**, in Definitions › "Assertions and proofs" (https://rocq-prover.org/doc/master/refman/language/core/definitions.html#assertions-and-proofs). There it is part of the `Theorem` grammar, followed by a short paragraph: *"useful for theorems that are proved by simultaneous induction over a mutually inductive assumption … equivalent to Fixpoint or CoFixpoint but using tactics"*. The same paragraph says the check happens only *"at the time of registering the lemma"* and mentions `Guarded`.
       - The **Inductive types** page, in its mutual-types section, says only *"the automatically generated induction principles do not provide induction hypotheses for the other mutually defined types. Use the Scheme command…"*. It **never mentions `Lemma … with`.** `Guarded` appears in "The Guard Condition" section.
       - The wording is strange. "Simultaneous induction over a mutually inductive assumption" means *a hypothesis `H` whose type belongs to the mutual block*, but it reads as if the inductive type were the assumption. It makes sense once you already use the technique, but you can't learn the technique from it. On the slide: quote the sentence, then give a plain translation (each lemma takes an `H` from the mutual block; the proofs may call each other on smaller `H`s).
       - Correct framing for the slides: "mentioned once, in a short paragraph on another page; the section on mutual inductive types points only to `Scheme`". Do **not** say it is undocumented, or that the manual never mentions mutual induction for it; it does, in one sentence. Each lemma can call the others, for example while proving `subs_press` you can call `type_press`. Real example: `subs_press with type_press with eq_ctx_press with eq_type_press` in 2.3 (around line 595). It is used about 30 times in 2.3.
     - **Power:** `Proof.` opens one goal per lemma, and *every* lemma is in the context as a hypothesis, so you can use any of them anywhere.
     - **Struggles** (speaker's experience; each point checked in Rocq 9.3 with toy files in the scratchpad):
       - Nothing stops `- apply (A n H).` inside the proof of A. Rocq says "No more goals". **Verified.**
       - The guard check only runs at `Qed`, and it fails with only `Error: Cannot guess decreasing argument of fix.` With 7 long mutual lemmas this is painful. **Verified** (exact message).
       - The supervisor knew `Guarded.` from his work with coinductive types and pointed the speaker to it (do not say he "found" it). The current master manual mentions it in "Assertions and proofs" and in "The Guard Condition", not only for coinductive types. The speaker remembers it being tied to coinduction, possibly from an older version, so don't claim "only for coinductive" on a slide. It checks the guard condition *now*, so it works as a checkpoint ("The condition holds up to here."). The speaker uses it to locate bad lines. **Verified.**
       - `Guarded.` tries every combination of candidate decreasing arguments, so the cost is exponential in the number of lemmas. The error lists every combination and why each one failed, which didn't help the speaker fix the proof. **Verified:** with 2 candidate arguments per lemma, N = 2…6 lemmas gives 4, 8, 16, 32, 64 combinations and 25 → 397 error lines. On slide 12 (2 lemmas, every inductive argument is a candidate: 3 × 4): **12 combinations, 64 lines** (measured with `rocq repl`, default width). An earlier figure of 114 lines was a measurement error.
       - You can't write `{struct H}` on `Lemma … with …`; Rocq gives a parse/typing error. **Verified.**
       - The derivation must be a **parameter** (`(H : TypeJG Γ A) : CtxJG Γ`), not after the colon (`: TypeJG Γ A -> CtxJG Γ`): the mutual `fix` only takes the binders before the colon as candidate decreasing arguments, so with `H -> goal` `Guarded.` always fails ("Not enough abstractions in the definition"). The speaker hit this at first. **Verified.** In the speaker notes' Q&A, not on the slides.
     - **Possible fix, found while preparing the talk (not the speaker's experience; the speaker decides whether to include it):** `Fixpoint A … (H : …) {struct H} : P with B … {struct H} : Q.` with **no body** also enters proof mode, just like `Lemma … with`. Stating the decreasing argument means only 1 combination is checked, and the error names that one case. **Verified:** N=6 gives 1 combination instead of 64, and a correct proof closes with `Qed`.
  4. **`Scheme … with` / `Combined Scheme`.** The manual's section on mutual inductives mentions only these. The speaker tried them (`definitions_preEq.v`, commit `0c2dbb5`) and couldn't work out from their types how to use them. Speaker's *hypothesis* (unverified, present it as such): Scheme produces something like method 1's single induction principle, yet you still write the lemma as in method 2. The speaker has not tried method 1 and doesn't know how lemmas would be written for it.
     - Trade-off of the `Fixpoint` fix: `{struct}` makes you choose the decreasing argument up front. The speaker doesn't always know in advance which hypothesis gets destructed first. `Lemma … with` lets Rocq find it afterwards, at an exponential cost.
  5. **Method 1 vs method 2 for single-sort lemmas** (the speaker has no hands-on experience with method 1; toy comparison checked in Rocq 9.3, using the same cyclic syntax `ty`/`tm` with `El : tm -> ty`, `lam : ty -> tm -> tm` in both styles):
     - Method 1, a function on one sort, `Fixpoint ty_size (A : syn TY)` listing only the TY constructors, is **accepted**. Don't claim functions are harder.
     - Method 1, a lemma on one sort, `induction A` on `A : syn TY` **fails**: "Abstracting over the terms s and A leads to a term … which is ill-typed". Workarounds: (i) restate the lemma for all sorts with a motive `match s with TY => … | TM => True end`, or (ii) `dependent induction` (Program.Equality). Both work but add overhead. **Verified.**
     - Method 2, the same lemma: plain `induction A` works directly with clean induction hypotheses. **Verified.** Flip side: the automatically generated `ty_ind` is *not* mutual (the `El a` case gives no induction hypothesis on `a`).
     - **The speaker's guess about `Scheme` is essentially right. Verified:** `Scheme … with` + `Combined Scheme` give `forall (P : ty -> Prop) (P0 : tm -> Prop), <one premise per constructor of both sorts> -> (forall t, P t) /\ (forall t, P0 t)`. That has the same shape as method 1's `syn_ind` (`P : forall s, syn s -> Prop`, one motive per sort), and its conclusion is exactly strategy (c), the `/\`. So `Combined Scheme` ≈ method 1's induction principle, and ≈ strategy (c) automated.
  6. **Method 1 vs method 2 on the judgements** (slide 6 for method 2, the supplement for method 1; verified in Rocq 9.3, `demo/method1.v`, `demo/method2.v`):
     - Plain (non-dependent) `induction` is **not discussed** in the talk (speaker's decision).
     - Lemma: a well-formed type lives in a well-formed context, `TypeJG Γ A -> CtxJG Γ`, with `dependent induction` on both sides.
     - Method 1: in the `type_subs` case the IHs are quantified and guarded by index equations, and Rocq **reuses the names** (`Γ` inside the IHs is a fresh variable). The IH of the substitution premise needs `SB … = TY …`: never true. The IH of the type premise (after `specialize (IHJ2 _ _ eq_refl)`) gives `J (CX Γ0)`, the context of the type premise, not the goal's `J (CX Γ)`.
     - Method 2: `IHTypeJG : CtxJG Γ` does not help (the goal is about `Δ`); what is missing is visibly `H -> goal`, i.e. `SubsJG Δ Γ y -> CtxJG Δ`.
     - Speaker's framing (on the slides): in method 1 the IHs are tempting, they look like a path to progress, but neither helps; in method 2 you see directly that the proof needs `H -> goal`. **The proof is the same in both methods** (a lemma on substitutions). Part of the readability gap may come from naming, so don't oversell it. Avoid the word "target context" (unclear).
     - How to prove it in method 1 is **not discussed on the slides** (speaker's decision; Q&A only). The style suggests one lemma on the whole structure: a motive by cases on the form (`match f with TY Γ _ => … | SB Δ Γ _ => … | _ => True end`) and `apply J_ind` (in `demo/method1.v`, `wf_all`). `Lemma … with` also works on method 1 **(verified)** with `remember` + `destruct` + `discriminate` + `injection`/`subst`; with `dependent destruction` instead, `Qed` fails with "Cannot guess decreasing argument of fix." **(verified)**.
  - Not relevant, leave out: the OCaml error and the issue the speaker meant to open.
- Framing: `with` isn't new, and this is the use it was designed for. The point is that it seems rarely used in practice, and the reference manual has only a few examples, which didn't help the speaker. The talk fills that gap with practical lessons. Present "rarely used" as the speaker's experience, not as a measured fact, unless a source backs it.
- Generality: draw the lessons so they carry over to any cyclic definitions. Type theory is one instance.

## The delivered deck (2026-11-16)

Storyline (the speaker's real path, after presenting both designs): method 2 is what I chose → stuck → the manual's `Scheme` (not understood) → tried (a) follow the cycle, (b) break the cycle, (c) combine the statements with `/\` (one common induction, e.g. on the context, needs a lot of extra structure: context conversion keeps the size, substitution blocks change it by at most one; a mutual principle avoids all that) → found (d) `Lemma … with` (combines the *proofs*: one mutual `fix`) → the catch, `Guarded.` → looking back at method 1: its natural proof, one lemma on the whole structure, is **(c) done right** and has the `Combined Scheme` shape. **Both methods can state and prove the same lemmas the same way; method 1 leans toward (c) done right (one induction principle, `J_ind` / `Combined Scheme`), method 2 toward (d) `Lemma … with`. The speaker **recommends** method 2 (on the takeaways, answering the advice to use method 1), **not** because of (d) but: no sort index; cycles easy to add or remove; with `Scheme`, both (c) and (d) are available.** Avoiding the termination check comes from using an induction principle, not from method 1 itself. Do not call `Lemma … with` a "conjunction of lemmas" (it is a mutual fixpoint; verified with `Print`).

Numbers as shown in the footer (title page not counted):

1. Context · 2. Simple types: no cycle · 3. Dependent types: a cycle ·
4. Method 1: one family indexed by a sort · 5. Method 2: one family per judgement, tied with `with` ·
6. Method 2: induction on a judgement (ends: "We need to prove both lemmas together.") ·
7. The manual's answer: `Scheme` / `Combined Scheme` · 8. What I tried next ((a), (b), (c)) ·
9. (d) Mutual lemmas: `Lemma … with …` (step by step) · 10. Another level ·
11. With great power comes great responsibility (step by step, error at `Qed`) · 12. Checking early: `Guarded.` (step by step) ·
13. Looking back: an induction principle, no termination check (method 1's one lemma on the whole structure via `J_ind`; the proof term has no `fix`, verified with `Print`; method 2 gets the same with `Combined Scheme`) (step by step) ·
14. Takeaways + thanks + Questions? · Supplements: `Fixpoint … {struct H}` with no body (step by step); method 1, induction on a judgement.

`slides.tex` blocks are marked `% --- [M2-def]`, `[M2-ind]`, `[Scheme]`, `[Tried]`, `[Mutual]`, `[Level]`, `[Power]`, `[Guarded]`, `[M1-def]`, `[M1-whole]`, `[Takeaways]`, `[Supp-Fix]`, `[Supp-M1-ind]`; `tools/insert_steps.py` uses them. The hidden presyntax block lives in `[M1-def]` (first Rocq slide), `Program.Equality` is imported in `[M2-ind]`.

## Source of truth for the formalisation

- `../` is a Rocq formalisation of Gratzer & Angiuli, _Principles of Dependent Type Theory_. `../Design.md` describes the split into pre-grammar / well-formedness judgements / equality judgements.
- **Primary source: `../2.3 - Calculus of Substitution/definitions.v`.** This is the most relevant and up-to-date work (the user says so, even though 2.4 has a newer file date). Take examples and lessons from here first. It still contains `Admitted`.
  - Pre-syntax: only `preSubs … with preTerm` is mutual. `preType` and `preCtx` are defined afterwards, one at a time, so the file groups only what is truly cyclic.
  - Judgements: 8 mutual inductive `Prop` families, `CtxJG with SubsJG with TypeJG with TermJG with eq_ctx with eq_subs with eq_type with eq_term`.
  - **Out of scope for this talk:** the `*_core_ind` principles, the `*_inv` lemmas and `Add Parametric Morphism`. They deal with **extensionality / working up to a quotient**: type conversion and context conversion produce repetitive goals during induction and inversion, and these tools factor those cases out. That is a separate problem from mutual definitions, so don't present them as lessons about `with`.
- No `Scheme`/`Combined Scheme` in the file.
- Secondary: `../2.4 - Internalising Pi,Sig,Eq/definitions.v` (Π, Σ, Eq, Void). Use it only if the user asks.
- Outdated: `../2.1 - STLC/STLC.v` — do not show it as is; write a fresh STLC example in `demo/`.
- Historical, ignore unless the user names them: `../Def*.v`, `../def_with_preExp.v`, `*_save.v`, `*_old.v`, `*_preEq.v`, `*_quotient.v`, `*_size_in_ctx.v`.

## Non-negotiable rules

- Do not invent results, citations, benchmarks, or proofs.
- Use “Rocq” consistently, except when quoting older Coq-specific material.
- Keep slides concise: one idea per slide.
- Mark uncertain claims as TODO rather than asserting them.
- Do not modify Rocq source files outside `TPP-2026-prez/` without explicit approval.

## Working preferences

- The speaker is new to Claude Code. Ask before generating slide content.
- Work incrementally: propose an outline first, get approval, then build slide by slide.
- After each batch, **stop and wait for an explicit "continue"**; answering a side question is not a go-ahead.
- Opinions stay opinions: "more readable" is not on the slides; "strictly better" is not on the slides (it can be said orally).

## Toolchain and build

- Rocq version: 9.3.0 (opam switch `default`).
- **Always build through the `Makefile`.** Don't call alectryon or latexmk by hand.
  - `make`: builds `slides.pdf`.
  - `make watch`: rebuilds whenever `slides.tex` changes.
  - `make check`: compiles the live-demo files `demo/*.v`.
  - `make setup`: creates `.venv/` with Alectryon (Alectryon 2.0.0 lives there; don't install it globally).
  - `make clean`: removes generated files.
- Rocq code that appears on slides goes **directly in `slides.tex`**, in `\begin{alectryon}{coq}{}` … `\end{alectryon}` blocks.
  - All blocks run in one Rocq session, so later slides see earlier definitions.
  - Alectryon (LaTeX frontend, `vsrocq` driver, which works with Rocq 9.3) writes `slides.annotated.tex` with the goals filled in, and latexmk compiles that file.
  - The preamble needs `\usepackage{alectryon}` and `\usepackage{pygments}`.
  - Never edit `slides.annotated.tex`, which is generated.
- This was tested with the Nagoya Beamer theme. A frame with a long proof overflows, so keep each block short or split it across frames.
- pdflatex needs `\DeclareUnicodeCharacter` for every Unicode symbol in code (Γ, Δ, ⊢ are declared in the preamble).
- Preamble macros for the step-by-step proofs: `\alectryonvscode`, `\rocqmsg`, `\mk`, `\popup`, `\alectryonscriptoutput`. The supplement uses `\appendix` + `appendixnumberbeamer` (not counted in the slide numbers).
- Render a page to check the layout: `gs -q -sDEVICE=png16m -r100 -dFirstPage=N -dLastPage=N -o out.png slides.pdf` (pages ≠ slide numbers because of overlays).
- `demo/` holds standalone `.v` files for the live editor demo only.

## Template

- Use `nagoyatheme.sty` and `nagoya-logo.png` / `nagoya-logo-16x9.png`.
- `midmaster_presentation.tex` is a **style reference only** (preamble, colours `ColorOne/Two/Three`, TikZ conventions). Never reuse its content.
- `nagoyatheme.sty` was restyled for this talk: flat dark-green header (`miniframes`, no subsection row) with three-state progress dots (shown / current ring / to come; the speaker likes the dots), slimmer frame title, and a three-box green footer (author | short title | "Nagoya University" + page). Keep the section dots.

## Proof interaction

- Static: proof states rendered by Alectryon on the slides (slides 4–8).
- **Step-by-step proofs** (slides 9, 11, 12, 13 and the `Fixpoint` supplement): code on the left with a green `>` cursor, the proof state on the right, one beamer overlay per line, one frame per proof (one navigation dot). The statement runs silently (first step is `Proof.`); the proof state is VS Code-like (hypotheses of goal 1 only, then `1 : …`, `2 : …`); messages Alectryon does not capture are typed by hand with the exact wording from `rocq repl`; the takeaways pop up on the last overlay. **Generated** by `tools/gen_steps.py` + `tools/insert_steps.py` (see the header of `gen_steps.py`); edit the step lists there, not the generated frames.
- **The slides show an abridged syntax and abridged proofs** (5 rules: `ctx_ext`, `type_subs`, `term_subs`, `subs_weak`, `subs_ext`; weakening was added so that slide 9 shows `subs_wf` calling `type_wf`; no base type; the speaker decided the base case need not appear). In step-by-step proofs, each `dependent induction` shows its one real case as a `+` sub-bullet and the other cases as `+ (* abridged *)` (displayed, never run: `TAIL` steps; or run invisibly when the case exists in the abridged syntax: `HIDDEN` steps, in `tools/gen_steps.py`); messages are those of the full proof ("Focus next goal with bullet +."). **Every technique on the slides must be checked on the full 2.3 syntax** in `demo/` (`make check`):
  - `demo/method2.v`: the four presupposition lemmas by `Lemma … with` + `dependent induction` (`subs_wf with type_wf with eqcx_wf with eqty_wf`, `Qed`); the circular proof accepted step by step, with `Fail Guarded.` / `Fail Qed.`.
  - `demo/method1.v`: the whole-structure lemma `press_all` (8-form motive, `induction` + automation, `Qed`); `Lemma … with` by `remember` + `destruct` (`Qed`); the same with `dependent destruction` (`Fail Qed.`: "Cannot guess decreasing argument of fix.").
- No `demo-plan.md` / live demo was made.

## Bibliography

- `slides.bib`, starting with Gratzer & Angiuli. Add an entry only after the user has confirmed it. For now, sources are cited in small text at the bottom of each slide; there is no biber step.
- **The speaker's example syntax may be wrong** (it was improvised). Base example code on published sources or on code that Rocq checks, never on the speaker's improvised snippets alone.
- No `slides.bib` was made. Sources used on the slides (small text at the bottom):
  - Slide 2 (STLC rules): Software Foundations, Vol. 2 *Programming Language Foundations*, chapter `Stlc` (https://softwarefoundations.cis.upenn.edu/plf-current/Stlc.html).
  - Slide 3 (the four rules and the cycle): Angiuli & Gratzer, *Principles of Dependent Type Theory*, Sec. 2.3.
  - Slides 4, 5: the speaker's own judgements from `../2.3 - Calculus of Substitution/definitions.v`, cut to 4 rules (method 2) and translated (method 1); checked by Rocq during `make`.
  - Slides 7, 10, 11: the reference manual (quotes in "Struggles" above).
  - Slide 10: the four `*_press` lemmas quoted verbatim from `../2.3 - Calculus of Substitution/definitions.v`.
- **Not cited on the slides, in the speaker notes (slide 4) as backup for "the usual advice":** Carneiro, *Lean4Lean: Verifying a Typechecker for Lean, in Lean*, 2024, arXiv:2403.14064 (checked in the full text on 2026-11-16): §2.2 merges typing and definitional equality into one inductive because "Lean does not have good support for mutual inductive predicates"; §4 "Theorems about mutual definitions also have to be mutual, so this has a tendency toward lack of modularity." The paper says **nothing** about how Lean 3 encoded mutual inductives (an earlier, unchecked idea; do not claim it).
- **Not cited (decided):** Kaposi & von Raumer, *A Syntax for Mutual Inductive Families*, FSCD 2020, doi:10.4230/LIPIcs.FSCD.2020.23 (calls the reduction of mutual inductive types to one indexed family "a folklore trick"; Agda). Background for Q&A only.

## Layout

```text
TPP-2026-prez/
├── CLAUDE.md
├── Makefile         # make / make watch / make check / make clean
├── slides.tex       # source: Beamer + inline Rocq (alectryon blocks)
├── slides.pdf       # output of `make`
├── speaker-notes.md # notes per slide + Q&A
├── demo/            # method1.v / method2.v: full 2.3 judgements in both methods
├── tools/           # gen_steps.py, insert_steps.py: step-by-step proof frames
├── nagoyatheme.sty
├── nagoya-logo*.png
└── midmaster_presentation.tex   # style reference only
```

## Deliverables

- `slides.tex`: LaTeX (Beamer) presentation.
- `speaker-notes.md`: notes per slide.
- ~~`demo-plan.md`~~: not made (no live demo).

## Definition of done

- Every factual claim is traceable to a repository file or citation.
- All `demo/` files compile and contain no `Admitted` (the WIP formalisation in `../` still does; that is expected).
- The slides compile without errors and without overfull boxes on code.
- The presentation fits in 12–15 minutes.
