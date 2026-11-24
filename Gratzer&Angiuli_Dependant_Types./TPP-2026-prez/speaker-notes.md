# Speaker notes — TPP 2026, 16 Nov, 15:50

Slot 12–15 min. Budget below ≈ 13 min, leaving time for questions.
Numbers are the footer numbers. "Next" = one click; step-by-step slides take several clicks.

---

## Title — (0:15)

- Jacques Garrigue speaks just before me: optional one-liner linking to his talk.

## 1. Context — (0:45)

- Angiuli & Gratzer did the maths (*Principles of Dependent Type Theory*); I'm implementing their extensional MLTT in Rocq.
- Different challenges arise, I am still looking for solutions
- One problem is : Dependent type theory = a set of **cyclic** definitions.
- This is a talk about implementation in Rocq : how to *define* such a cycle and how to *prove lemmas* about it.
- The lessons apply to any cyclic definitions, not only type theory.
- Extensional MLTT is particularly relevant: 4 judgements + 4 equality judgements = 8 mutually inductive judgements. Other dependent theories, and most other structures, are far less interwoven.

## 2. Simple types: no cycle — (0:45)

- STLC: types don't mention terms or contexts.
- The arrows form a DAG, so there's a definition order: types, then terms and contexts, then typing.
- Each definition can be its own `Inductive`, one after another.

## 3. Dependent types: a cycle — (1:00)

- Four rules from the book (Sec. 2.3), placed like the graph: context, type, substitution, term.
- Every judgement refers to the others: Γ.A needs `A type`, `A[γ]` needs a substitution, a substitution needs types and terms…
- Plus 4 equality judgements in the same cycle.
- **No definition order: everything at once.**
- Notation switch (bottom line): from the next slide on, the code writes Γ.A as `Γ # A`, because a `.` would end the Rocq sentence, and γ as `y`.

## 4. Method 1: one family indexed by a sort — (0:45)

- The usual advice (supervisor, colleagues, online): one `Sort` (one constructor per judgement form), one inductive `J : Sort -> Prop`; each rule says which sort it concludes.
- These are *my* rules, translated; Rocq checks them.
- If asked where "the usual advice" comes from (not on the slide):
  - mainly my experience: my supervisor, colleagues, examples online;
  - Kaposi & von Raumer, *A Syntax for Mutual Inductive Families*, FSCD 2020 (doi:10.4230/LIPIcs.FSCD.2020.23): reducing mutual inductive types to one indexed family is "a folklore trick" (Agda);
  - Carneiro, *Lean4Lean: Verifying a Typechecker for Lean, in Lean*, 2024 (arXiv:2403.14064), §2.2: typing and definitional equality, mutually inductive in earlier work, become one all-in-one relation, because "Lean does not have good support for mutual inductive predicates, so keeping it as a single inductive makes induction proofs easier". Also (§4): "Theorems about mutual definitions also have to be mutual, so this has a tendency toward lack of modularity." That is Lean, not Rocq.
  - My view on that modularity point (if it comes up): mutual definitions make things *more* modular, not less. The cycle forces the proofs to be mutual in both designs; what differs is the statements. With one inductive, a lemma about one judgement has to be stated over the whole structure (one motive for all forms, slide 13). With `with`, each judgement keeps its own definition and, with `Lemma … with`, each lemma keeps its own statement; mutuality only appears where the cycle demands it.

## 5. Method 2: one family per judgement, tied with `with` — (0:45)

- Transition: the rocq documentation contains a feature that make the transition from STLC more natural, mutual inductive types.
- Transition: why not the usual advice? To me, method 1 is *engineered* (an extra `Sort` type, every rule tagged with its sort), while method 2 is the *natural* step from STLC (slide 2): one inductive per judgement, as on paper, plus `with` to tie the cycle. Say it as my opinion.
- Say it as opinion if at all: I find it closer to the paper.

## 6. Method 2: induction on a judgement — (0:45)

- Lemma: a well-formed type lives in a well-formed context.
- `IHTypeJG : CtxJG Γ` doesn't help: the goal is about `Δ`.
- What is missing is visible: `H -> goal`, i.e. `SubsJG Δ Γ y -> CtxJG Δ`.
- But proving `SubsJG Δ Γ y -> CtxJG Δ` will require `TypeJG Γ A -> CtxJG Γ`: a cycle of lemmas. (In my code, the proof of `subs_press` calls `type_press`, e.g. for the weakening rule `[Γ ⊢ A type] -> [Γ # A ⊢ p ~ Γ]`.)
- Cycle of dependency reflected in the proof.
- **We need to prove both lemmas together.**

## 7. The manual's answer: `Scheme` / `Combined Scheme` — (0:45)

- First thing I did: the manual's section on mutual inductive types only points here.
- One property per judgement, one case per rule, a conjunction at the end.
- Honest beat: its conclusion is one conjunction over all judgements, while my lemmas are separate statements (`type_press`, `subs_press`, …). I could probably have made them fit, but with a lot of boilerplate, and I thought there would be a more natural, easier-to-understand solution. (We come back to it at the end.)
- If pressed: technically they do fit, by choosing `P0 := fun Γ A => CtxJG Γ`, `P2 := fun Δ Γ y => CtxJG Δ /\ CtxJG Γ`, and `True` for the judgements you don't care about, then projecting the conjunction. That is exactly method 1's natural proof (slide 13).
- The box is abridged by hand from the real `Check` output.

## 8. What I tried next — (1:00)

- (a) **Follow the cycle**: induct again on the `SubsJG` premise until it loops back to `TypeJG` and the IH applies.
	- Rocq only register the outside lemma, so we need to prove the other lemma a second time. 
	- Call to the audience : It you know of a way that you can make coq extra the lemma please tell me.
	- The proof is duplicated; no single source of truth.
- (b) **Break the cycle**: assume the other lemma, prove it, restate. Works, lots of boilerplate.
- Scalability (I only experimented with pairs of mutual lemmas): with more lemmas, (a) and (b) need their trick for every dependency, one copy or one assumption per edge of the cycle.
- (c) **Combine the statements** (with `/\`): to get one induction you need a common `forall`. The only thing the conjuncts share is the context. If asked: substitution (`Δ ⊢ y ~ Γ`) and context conversion move to other contexts, so a plain induction on the context fails; in practice context conversion keeps the size and the substitution building blocks change it by at most one, so an induction on the size might work, but you have to add all that structure. 

## 9. (d) Mutual lemmas: `Lemma … with …` — (1:30) — step by step

- **Central message.** Not a better (c): a different idea, (d).
- If asked how it works inside: the manual says it is "equivalent to Fixpoint … but using tactics"; `Print type_wf` shows a mutual `fix … with …` (checked while preparing; not something I investigated myself).
- Click through: after `Proof.` both lemmas, `type_wf` *and* `subs_wf`, are **in the context**.
- `dependent induction H`, as in my code; in the `type_subs` case there is no IH for `H : SubsJG Δ Γ y`, so call `subs_wf` on it (a smaller derivation).
- `exact` closes the bullet: Rocq says to focus the next bullet.
- Second bullet, weakening case `[Γ ⊢ A type] -> [Γ # A ⊢ p ~ Γ]`: call `type_wf` on `H : TypeJG Γ A` to get `⊢ Γ cx`, then `ctx_ext`. Both directions of the cycle are now used: types call substitutions, substitutions call types. (In my code, `subs_press` calls `type_press` exactly here.)
- The extension case is abridged (it uses its own `IHSubsJG`); `Qed` accepted.
- Each `dependent induction` has one `+` case per rule; only one is shown, the others are `+ (* abridged *)`. The messages ("Focus next goal with bullet +.") are those of the full proof.
- The syntax on the slides is abridged (no base type, 5 rules: `ctx_ext`, `type_subs`, `term_subs`, `subs_weak`, `subs_ext`). The same technique is checked on the full 2.3 syntax in `demo/method2.v` (all four `*_press`-style lemmas).
- Pop-up: combine only the lemmas that depend on each other (combining unrelated lemmas is a bad pattern, don't do it); they are all in the context; it scales (no duplication, no boilerplate).

## 10. Another level — (1:00)

- The title is Jacques's comment. What "another level" means:
  - the lemmas follow the shape of the judgements: one lemma per judgement of the cycle, joined by `with` like the definitions (`subs_press with type_press with eq_ctx_press with eq_type_press`, my 2.3);
  - in each proof the induction hypothesis is the **whole group**, not just the current lemma (on smaller derivations: that is what the guard checks, next slide).
- Each proof is `dependent induction H`, then calls the other lemmas where needed.
- Compared with what I tried before ((a)–(c), `Scheme`): each lemma keeps its own statement, no motive to write, no conjunction to set up. That is my modularity point (see the Lean4Lean counterpoint under slide 4).
- The manual mentions it **once**, in "Assertions and proofs" ("equivalent to Fixpoint or CoFixpoint but using tactics"); its section on mutual inductive types only points to `Scheme`. Don't say "undocumented".

## 11. With great power comes great responsibility — (1:00) — step by step

- Same lemmas, but a circular "proof": `exact (type_wf Γ A H)` calls itself on the same `H`.
- Rocq **accepts every step**, even says "No more goals".
- Only at `Qed`: `Cannot guess decreasing argument of fix.`
- While stepping through: all the goals are hypotheses, so a fair question is whether this hides an admitted lemma, or is broken, or breaks Rocq. In practice no: you can use any lemma, but Rocq still checks that the argument decreases. Only at `Qed` though ("at the time of registering the lemma"), and the error says neither which lemma nor which line: it would be nicer to check earlier (next slide). With 7 long mutual lemmas this hurts.
- Pop-up (takeaway only): more freedom, less guidance (the training wheels are off): termination is checked only at `Qed`; the error says neither which lemma nor which line.

## 12. Checking early: `Guarded.` — (1:00) — step by step

- Jacques knew `Guarded.` from his work with coinductive types and pointed me to it: it checks the guard condition *now*, a checkpoint.
- Put it right after the suspicious line: it fails there.
- But it tries every combination of decreasing arguments: here 3 × 4 = 12 combinations, 64 lines of error; exponential in the number of lemmas.
- The error lists every combination; it locates the line, it doesn't explain the fix.
- Transition: can we avoid this termination check altogether? Yes, with an induction principle, the route I set aside on slide 7. Looking back, that is exactly where the usual advice (slide 4) leads.

## 13. Looking back: an induction principle, no termination check — (1:15) — step by step

- "Looking back": if I had chosen method 1 (slide 4), how would this proof look? One lemma on the whole structure, proved by applying `J_ind`: the proof term contains no `fix`, so there is no termination check at `Qed` (checked with `Print`).
- What method 1 leads you to: a motive by cases on the sort (`wf_motive`), one lemma `wf_all f (H : J f) : wf_motive f`, plain `induction H; simpl in *`.
- In the `type_subs` case the IH of the substitution premise is now useful: `IHJ1 : J (CX Δ) /\ J (CX Γ)`; the last case uses `IHJ2`, `IHJ3`.
- **This is (c) done right**: the induction comes *before* looking at the cases. Same shape as `Combined Scheme`: now I see what the manual meant.
- The lemma on one judgement is a corollary: `exact (wf_all _ H)` (checked in the hidden part of the slide).
- Pop-up: no `fix` in the proof, so no termination check at `Qed`; method 2 gets the same with `Combined Scheme`; (c) done right.
- Say, not on the slide: what avoids the check is the induction principle, not method 1 itself. Both methods can state and prove the same lemmas the same way; they only lean differently.
- If asked: the one-judgement lemma is a corollary (`exact (wf_all _ H)`); `Lemma … with` also works in method 1 (`remember` + `destruct`), but with `dependent destruction` `Qed` fails because the guard can't see through its casts.

## 14. Takeaways — (0:45)

- One inductive per judgement with `with`.
- In both methods a lemma on one judgement needs the others.
- Two ways to prove them together, both available in both methods: (c) one induction principle on the *whole* syntax (`J_ind`, `Combined Scheme`), no termination check, as opposed to the smaller inductions of (d); (d) `Lemma … with`, little known, termination checked only at `Qed`, `Guarded.` to check early.
- On (d)'s drawback: writing the `Fixpoint … {struct H}` directly seems to fix it (one combination, the error names the bad call): supplement. Not tried on my real lemmas yet, so "seems".
- Method 1 leans toward (c), method 2 toward (d).
- I recommend method 2 (my answer to the advice I was given), and *not* because it leans toward (d): no `Sort` index to carry around; cycles are easy to add or remove (each judgement is its own inductive, only the `with` changes); once you use `Scheme`, both (c) and (d) are available; etc.
- Questions.

## Supplement: `Fixpoint … {struct H}` with no body (only if asked)

- Found while preparing the talk, **not from my experience**.
- A `Fixpoint … with …` with no body also enters proof mode.
- The decreasing argument is given: one combination checked, and the error names the lemma and the bad call ("principal argument equal to H instead of a subterm of H").
- `Guarded.` works here too, right after the circular line: one combination (the 3rd argument of `type_wf`, the 4th of `subs_wf`), 9 lines, names the bad call; `?Goal` in the error shows it checks a partial proof. Compare slide 12: 12 combinations, 64 lines.
- Trade-off: you must know the decreasing argument before the proof; `Lemma … with` lets Rocq find it, at an exponential cost.
- `{struct H}` cannot be written on `Lemma … with …` (Rocq rejects it).

## Supplement: method 1, induction on a judgement (only if asked)

- The index is always a constructor (`TY …`), so `dependent induction`.
- The IHs are tempting: they look like a path to progress. Neither helps:
  - `IHJ1` (substitution premise) needs `SB … = TY …`: **never true**;
  - `IHJ2` gives `J (CX Γ0)`, not the goal's `J (CX Γ)` (Rocq reuses the name `Γ` inside the IHs).
- Same missing lemma as in method 2; part of the readability gap is naming, so don't oversell it.

---

## Q&A

**"Method 1 lets you write one function for all sorts, e.g. substitution."**
You still define substitution on every case in both designs. With `with`: `Fixpoint subst_ty … with subst_tm …`, and a wrapper `match s with TY => subst_ty | TM => subst_tm end` gives the single interface back.

**"Could you use `Lemma … with` in method 1?"**

- Slide 13 shows method 1's natural proof (one lemma on the whole structure); it's also in `demo/method1.v` (`wf_all`).
- `Lemma … with` also works on method 1 (checked in Rocq 9.3): `Lemma type_wf … (H : J (TY Γ A)) … with subs_wf … (H : J (SB Δ Γ y)) …`, each case by `remember` + `destruct H` + `discriminate` + `injection`/`subst`, then the recursive call on the sub-derivation; `Qed` accepts it.
- Catch: with `dependent destruction` instead, `Qed` fails with "Cannot guess decreasing argument of fix." (the casts it inserts hide the subterm from the guard checker).

**"Why not syntax that is well-formed by construction?"**
Tried it (commits `ded8a9e`, `46ef803`, `f0559d5`): rigid, hard to write, and Rocq has no induction-induction. Pre-syntax that can express anything + separate judgements works better for me.

**"Why are the judgements inductive and not `Fixpoint`s?"**
Tried (commits `877e25b`, `2f2c924`, `Def2.v`): a judgement needs other judgements and I couldn't show termination. Whether conversion was the cause I'm not sure. An inductive `Prop` gives one constructor per rule.

**"Is `with` new?"**
No, it is what it was designed for. My point: it seems rarely used for this in practice (my experience), and the manual's few examples didn't teach me the technique.

**"Where does method 1 come from?"**
Folklore; see the sources under slide 4 (Kaposi & von Raumer 2020; Lean4Lean 2024, which merges two mutual judgements into one inductive because of Lean's weak support for mutual inductive predicates).

**"Did you use `Scheme` in the development?"**
No. I tried it first (`definitions_preEq.v`, commit `0c2dbb5`) and couldn't see from its type how to use it (slide 7). Slide 13 shows what it is for: method 1's whole-structure lemma has the same shape.

**"How many mutual lemmas do you have?"**
The `*_press` block has 4; there are blocks of up to 7 long lemmas, which is where the `Qed`-only check becomes painful.

**"Does it matter how the lemma is stated?"** (practical tip, from my experience)
Yes: the derivation must be a **parameter**, `Lemma type_wf Γ A (H : TypeJG Γ A) : CtxJG Γ with …`, not after the colon (`… : TypeJG Γ A -> CtxJG Γ`). At first I wrote `H -> goal` and `Guarded.` always failed. Reason (checked in Rocq 9.3): Rocq builds the mutual `fix` from the binders *before* the colon, and only those can be the decreasing argument; with `H` after the colon it only tries `Γ`, `A` (and `Δ`, `Γ`, `y`), and even reports "Not enough abstractions in the definition". Same rule as `{struct x}` on a `Fixpoint`. (It is also why slide 12 counts 3 × 4 combinations: every argument before the colon is a candidate.)

**Files to show if someone asks:** `demo/method1.v` and `demo/method2.v` (all 8 judgements and all rules of 2.3 in both methods).
