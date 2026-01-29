From Stdlib Require Import Nat String.
From Corelib.Program Require Import Basics Tactics Wf.
From Stdlib.Logic Require Import JMeq.

Require Export Setoid.
Require Export Relation_Definitions.

(* Implementation of Dependent Types in Rocq (From Gratzer's "Principles of Dependent Type Theory") *)
Inductive wfContext : Type :=
   I : wfContext
| Extend : wfContext -> wfType -> wfContext
with wfType : Type :=
  Base : wfType
| Func : wfType -> wfType -> wfType
| Prod : wfType -> wfType -> wfType.

Scheme context_type_rec := Induction for wfContext Sort Set
  with type_context_rec := Induction for wfType Sort Set.

Notation "ctx # A" := (Extend ctx A) (at level 50, left associativity).

Notation "A --> B" := (Func A B) (at level 55,  right associativity).
Notation "A ** B" := (Prod A B) (at level 60, right associativity).

Notation "⊢c ctx" := (ctx : wfContext) (at level 40).
Notation "ctx ⊢t A" := (A : wfType) (at level 40).


(* Example ex1 :  I ⊢t ((Base ** Base) --> Base).
Proof.
  simpl. auto.
Qed. *)


Inductive wfTerm : wfType -> Type :=
| const (n : nat) : wfTerm Base
| Pair (A B : wfType) : wfTerm A -> wfTerm B -> wfTerm (A ** B)
| Fst (A B : wfType) : wfTerm (A ** B) -> wfTerm A
| Snd (A B : wfType) : wfTerm (A ** B) -> wfTerm B
| Lam (A B : wfType) : wfTerm B -> wfTerm (A --> B)
| App (A B : wfType) : wfTerm (A --> B) -> wfTerm A -> wfTerm B.

Notation "ctx ⊢ t ; A" := (t : wfTerm A) (at level 40).

Fixpoint InContext (ctx : slContext) (x : slVariable) (t : slType) : Prop :=
  match ctx with
  | Empty => False
  | Extend c y ty => if String.eqb x y then  ty = t else InContext c x t
  end.

Definition eq_ctx (ctx1 ctx2 : slContext) : Prop :=
  forall x A, InContext ctx1 x A = InContext ctx2 x A.

Lemma eq_ctx_refl (ctx : slContext) : eq_ctx ctx ctx.
Proof.
   intros. intros x A. reflexivity.
Qed.

Lemma eq_ctx_sym (ctx1 ctx2 : slContext) : eq_ctx ctx1 ctx2 -> eq_ctx ctx2 ctx1.
Proof.
   intros. intros x A. symmetry. apply H.
Qed.

Lemma eq_ctx_trans (ctx1 ctx2 ctx3 : slContext) :
   eq_ctx ctx1 ctx2 -> eq_ctx ctx2 ctx3 -> eq_ctx ctx1 ctx3.
Proof.
   intros. intros x A. rewrite (H x A). apply H0.
Qed.

Add Relation slContext eq_ctx
  reflexivity proved by eq_ctx_refl
  symmetry proved by eq_ctx_sym
  transitivity proved by eq_ctx_trans
as eq_ctx_rel.

Lemma ctx_extend_eq (ctx : slContext) (x : slVariable) (A B: slType) :
   eq_ctx (Extend (Extend ctx x A) x B) (Extend ctx x B).
Proof.
   intros y C. simpl.
   destruct (String.eqb y x) eqn:Heq;
   reflexivity.
Qed.



Add Morphism well_formed with
  signature eq_ctx ==> eq ==> eq ==> eq as well_formed_mor.
Proof.
   intros ctx1 ctx2 Hctx A a.
   generalize dependent ctx2.
   generalize dependent ctx1.
   generalize dependent A.
   generalize dependent a.
   induction a; intros; simpl in *.
   - reflexivity.
   - apply Hctx.
   - destruct A; try reflexivity.
      rewrite (IHa1 A1 ctx1 ctx2 Hctx). rewrite (IHa2 A2 ctx1 ctx2 Hctx). reflexivity.
   - f_equal.
      apply functional_extensionality.
      intros B.
      apply IHa with (A:=A ** B); auto.
   - f_equal.
      apply functional_extensionality.
      intros B.
      apply IHa with (A:=B ** A); auto.
   - destruct A; try reflexivity.
      apply IHa.
      unfold eq_ctx in *. intros y C.
      simpl.
      specialize (Hctx y C).
      rewrite Hctx. reflexivity.
   - f_equal.
      apply functional_extensionality.
      intros A0.
      rewrite (IHa1 (A0 --> A) ctx1 ctx2 Hctx).
      rewrite (IHa2 A0 ctx1 ctx2 Hctx).
      reflexivity.
Qed.


Reserved Notation "b [ a // x ]" (at level 20).
Fixpoint Subs (a b: slTerm)(x : slVariable) {struct b} : slTerm :=
   match b with
   | const n => const n
   | Var y => if String.eqb y x then a else Var y
   | Pair t1 t2 => Pair (t1 [ a // x ]) (t2 [ a // x ])
   | Fst t => Fst (t [ a // x ])
   | Snd t => Snd (t [ a // x ])
   | Lam y t => if String.eqb x y then Lam y t else Lam y (t [ a // x ])
   | App f t => App (f [ a // x ]) (t [ a // x ])
   end
where "b [ a // x ]" := (Subs a b x).

Inductive eq_slTerm (ctx : slContext) (Ty : slType): relation slTerm :=
| eq_refl : forall t : slTerm,
    [ctx ⊢ t ; Ty] ->
    eq_slTerm ctx Ty t t
(* Beta_equivalence for Pairs *)
| eq_beta_left : forall a b B, [ctx ⊢ a ; Ty] -> [ctx ⊢ b ; B] -> eq_slTerm ctx Ty (Fst (Pair a b)) a
| eq_beta_right : forall a b A, [ctx ⊢ a ; A] ->  [ctx ⊢ b ; Ty] -> eq_slTerm ctx Ty (Snd (Pair a b)) b
(* Eta_equivalence for Pairs *)
| eq_eta_pair :
   forall p A B, Ty = A ** B ->
   [ctx ⊢ p ; Ty] -> eq_slTerm ctx Ty p (Pair (Fst p) (Snd p))
(* Beta_equivalence for Lambdas *)
| eq_beta_lam : forall t a x A,
    [Extend ctx x A ⊢ t ; Ty] ->
    [ctx ⊢ a ; A] ->
    eq_slTerm ctx Ty (App (Lam x t) a) (t [ a // x ])
(* Eta_equivalence for Lambdas *)
| eq_eta_lam :
   forall f x A B,
   Ty = A --> B ->
   [ctx ⊢ f ; Ty] ->
    eq_slTerm ctx Ty f (Lam x (App f (Var x))).

Axiom eq_slTerm_refl : forall (ctx : slContext) (A : slType),
    reflexive slTerm (eq_slTerm ctx A).
Axiom eq_slTerm_sym : forall (ctx : slContext) (A : slType),
    symmetric slTerm (eq_slTerm ctx A).
Axiom eq_slTerm_tans : forall (ctx : slContext) (A : slType),
    transitive slTerm (eq_slTerm ctx A).

Add Parametric Relation (ctx : slContext) (A : slType) : slTerm (eq_slTerm ctx A)
  reflexivity proved by (eq_slTerm_refl ctx A)
  symmetry proved by (eq_slTerm_sym ctx A)
  transitivity proved by (eq_slTerm_tans ctx A)
as eq_slTerm_rel.

Notation "[ ctx ⊢ t1 '==' t2 ';' A ]" := (eq_slTerm ctx A t1 t2) (at level 40).


Lemma Shadowing (ctx : slContext) (a : slTerm) (A C: slType) (x : slVariable) (B : slType) :
   [Extend ctx x B ⊢ a ; C] = [Extend (Extend ctx x A) x B ⊢ a ; C].
Proof.
   apply well_formed_mor.
   apply eq_ctx_sym.
   apply ctx_extend_eq.
   reflexivity.
   reflexivity.
Qed.

Instance Proper_eq_slTerm : subrelation eq (impl).
Proof.
   intros a b H.
   intros ctx.
   subst.
   auto.
Qed.

(* Lemma well_formed_extension (ctx : slContext) (a : slTerm) (A B : slType) (x : slVariable) :
   [ctx ⊢ a ; A] -> [Extend ctx x B ⊢ a ; A].
Proof.
   intros H.
   induction a; simpl in *; try assumption. *)


Lemma Substitution (ctx : slContext) (a b : slTerm) (A B : slType) (x : slVariable) :
   [Extend ctx x A ⊢ b ; B] /\ [ctx ⊢ a ; A] -> [ctx ⊢ (b [ a // x ]) ; B].
Proof.
   generalize dependent B.
   generalize dependent A.
   generalize dependent a.
   generalize dependent ctx.
   generalize dependent b.
   induction b;
   intros ctx a A B H;
   destruct H as [H1 H2]; auto.
   - simpl in *.
    destruct (String.eqb s x) eqn:Heq; subst; auto.
   - simpl in *. destruct B; try contradiction.
     destruct H1 as [Hl Hr].
     split; [ apply IHb1 with (A:=A) | apply IHb2 with (A:=A)]; auto.
   - simpl in *. destruct H1 as [C Ht].
       exists C. apply IHb with (A:=A); auto.
   - simpl in *. destruct H1 as [C Ht].
       exists C. apply IHb with (A:=A); auto.
   - simpl in H1. destruct B; try contradiction.
         simpl in *.
         destruct (String.eqb x x0) eqn:Heq; subst;
         simpl in *.
         +
         apply String.eqb_eq in Heq. subst.
         rewrite Shadowing with (A:=A). apply H1.
         +
         apply String.eqb_neq in Heq.
         apply IHb with (A:=A); auto.
         split.
         setoid_rewrite well_formed_mor in H1.
         apply H1.
         unfold eq_ctx.
         intros. simpl.
         destruct (String.eqb x1 x0) eqn:Heq1;
         destruct (String.eqb x1 x) eqn:Heq2; try reflexivity.
         apply String.eqb_eq in Heq1;
           apply String.eqb_eq in Heq2; subst; contradiction.
         reflexivity.
         reflexivity.
         (* Need the FreeVariable def to continue*)
         admit.
   - simpl in *. destruct H1 as [A' [Ht1 Ht2]].
         exists A'. split;
         [ apply IHb1 with (A:=A) | apply IHb2 with (A:=A)]; auto.
Admitted.


Instance Proper_Fst_eq (ctx : slContext) (A : slType) : Morphisms.Proper (eq_slTerm ctx A ==> eq) Fst.
Proof.
   intros a b H.
   inversion H; subst; simpl; try reflexivity.
Qed.

Add Parametric Morphism (ctx : slContext) (A : slType) : (well_formed ctx A) with
  signature (eq_slTerm ctx A) ==> eq as well_formed_eq_slTerm_mor.
Proof.
   induction A.
   induction x, y; intro H; inversion H; subst; try contradiction; try reflexivity.
   Set Rewrite Output Constraints.
   - rewrite H.
      all : shelve_unifiable.
      all : try typeclasses eauto.
   - apply Shadowing. auto.
   - destruct H0 as [Hl Hr].
     split; [ apply IHeq_slTerm1 | apply IHeq_slTerm2]; auto.
   - destruct H0 as [B' Ht].
       exists B'. apply IHeq_slTerm with (A:=A ** B'); auto.
   - destruct H0 as [A' Ht].
       exists A'. apply IHeq_slTerm with (A:=A --> B); auto.
   - destruct H0 as [Hl Hr].
     exists A0. split; [ apply IHeq_slTerm1 | apply IHeq_slTerm2]; auto.


Lemma eq_slTerm_well_formed (ctx : slContext) (a b : slTerm) (A : slType) :
   [ctx ⊢ a == b ; A] -> [ctx ⊢ a ; A] /\ [ctx ⊢ b ; A].
Proof.
   intros H.
   inversion H; split; auto.
   - setoid_rewrite eq_beta_left.
      all : shelve_unifiable.
      all : try typeclasses eauto.
   simpl. exists B; auto.
