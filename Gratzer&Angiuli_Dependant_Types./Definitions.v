From Stdlib Require Import Nat String.
From Corelib.Program Require Import Basics Tactics Wf.
From Stdlib.Logic Require Import JMeq.

Require Export Setoid.
Require Export Relation_Definitions.

(* Implementation of Dependent Types in Rocq (From Gratzer's "Principles of Dependent Type Theory") *)

Inductive preType :=
| Base : preType
| Func (A B : preType) : preType
| Prod (A B : preType) : preType.

Notation "A --> B" := (Func A B) (at level 55,  right associativity).
Notation "A ** B" := (Prod A B) (at level 60, right associativity).

Inductive preContext : nat -> Type :=
   Empty : preContext 0
| Extend : forall{n}, preContext n -> preType -> preContext (S n).

Notation "ctx # A" := (Extend ctx A) (at level 50, left associativity).

Inductive preTerm :=
| const (n : nat) : preTerm
| Pair (a b : preTerm) : preTerm
| Fst (p : preTerm) : preTerm
| Snd (p : preTerm) : preTerm
| Lam (b : preTerm) : preTerm
| App (f a : preTerm) : preTerm.
