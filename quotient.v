(*  Experiment on quotients in intensional type theory *)
From Stdlib Require Import Arith.PeanoNat.

Section Quotient.
	Variable A : Type.
	Variable R : A -> A -> Prop.

End Quotient.

Section Integers.
	Definition Z : Type := (nat * nat).
	Definition eqZ : Z -> Z -> Prop := fun x y => fst x + snd y = snd x + fst y.
End Integers.

Definition isNeg : Z -> Prop := fun z => fst z = 0.
Definition isPos : Z -> Prop := fun z => snd z = 0.



(* Class Quotient (A : Type) (R : A -> A -> Prop) := {
  class_eq : forall x y : A, R x y -> forall P : A -> Prop, P x -> P y;
}.

Instance Quotient_Z : Quotient Z eqZ.
Proof.
	constructor.
	intros x y H P Hx.
	inversion H. *)

(* Structure Quotient : Type := {
	carrier :>	Set;
	eq : carrier -> carrier -> Prop;
}. *)


Definition quotient_ind (z : Z) (P : Z -> Prop) :
	(exists x : Z, eqZ x z /\ P x) -> P z.
Proof.
	intros H.
	destruct H as [x [H1 H2]].
	inversion H1.
Admitted.


Lemma Z_pose_or_neg : forall z : Z, isNeg z \/ isPos z.
	intros z.
	destruct z as [n m] eqn:Hz.
	destruct (n - m) eqn:H.
	left.
	apply quotient_ind.
	exists (0, m - n).
	split.
	unfold eqZ.
	simpl.
	admit.
	reflexivity.
	right.
	apply quotient_ind.
	exists (n - m, 0).
	split.
	unfold eqZ.
	simpl.
	admit.
	reflexivity.
Abort.

Lemma subs_n_n : forall n : nat, n - n = 0.
	intros n.
	induction n.
	simpl. reflexivity.
	simpl. assumption.
Qed.

Lemma add_n_0 : forall n : nat, n + 0 = n.
	intros n.
	induction n.
	simpl. reflexivity.
	simpl. f_equal. assumption.
Qed.

Lemma subs_add_n : forall n m  : nat, m >= n -> m = m - n + n.
	intros n.
	induction n.
	intros m H.
	rewrite add_n_0.
	induction m.
	simpl. reflexivity.
	simpl. reflexivity.
	intros m H.
	induction m.
	inversion H.
	apply le_S_n in H.
	specialize (IHn m H).
	simpl.
	rewrite Nat.add_comm.
	simpl.
	rewrite Nat.add_comm.
	rewrite <- IHn.
	reflexivity.
Qed.

Class Quotient (A : Type) (R : A -> A -> Prop) := {
	quot :> Type;
	q_intro : A -> quot;
	q_ax : forall x y : A, R x y -> q_intro x = q_intro y;
	q_elim : forall (B : Type) (f : A -> B), quot -> B;
	q_comp : forall (x : A) (B : Type) (f : A -> B), q_elim B f (q_intro x) = f x;
	q_ind : forall (P : quot -> Prop), (forall x : A, P (q_intro x)) -> forall q : quot, P q;
}.


Definition QisNed `{Zq: Quotient Z eqZ} (q : Zq) := q_elim _ (fun z => isNeg z) q.
Definition QisPos `{Zq: Quotient Z eqZ} (q : Zq) := q_elim _ (fun z => isPos z) q.

Lemma Zq_pos_or_neg `{Zq: Quotient Z eqZ} : forall (q : Zq), QisNed q \/ QisPos q.
	inversion Zq.
	apply q_ind.
	intros z.
	destruct z as [n m] eqn:Hz.
	destruct (n - m) eqn:H2.
	left.
	rewrite q_ax with (y := (0, m - n)).
	unfold QisNed.
	rewrite q_comp.
	reflexivity.
	unfold eqZ.
	simpl.
	rewrite Nat.add_sub_assoc.
	rewrite Nat.add_comm.
	rewrite Nat.add_sub.
	rewrite Nat.add_0_r.
	tauto.
	now apply Nat.sub_0_le.
	right.
	rewrite q_ax with (y := (n - m, 0)).
	unfold QisPos.
	rewrite q_comp.
	reflexivity.
	unfold eqZ.
	simpl.
	rewrite H2.
	rewrite Nat.add_0_r.
	symmetry.
	now apply Nat.add_sub_eq_nz.







