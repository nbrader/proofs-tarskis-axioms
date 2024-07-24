Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Reals.Reals.
Open Scope R_scope.

Require Import Psatz.

Definition evenPart : (R -> R) -> (R -> R) := fun f => fun x => (f x + f (-x)) * /2.
Definition oddPart  : (R -> R) -> (R -> R) := fun f => fun x => (f x - f (-x)) * /2.

Definition isEven (f : R -> R) := forall (x : R), f (-x) =   (f x).
Definition isOdd  (f : R -> R) := forall (x : R), f (-x) = - (f x).

Theorem evenPartIsEven : forall (f : R -> R), isEven (evenPart f).
Proof.
  intros.
  unfold isEven.
  intros.
  unfold evenPart.
  rewrite Ropp_involutive with (r := x).
  rewrite Rplus_comm with (r1 := f x) (r2 := f (-x)).
  reflexivity.
Qed.

Theorem oddPartIsOdd : forall (f : R -> R), isOdd (oddPart f).
Proof.
  intros.
  unfold isOdd.
  intros.
  unfold oddPart.
  rewrite Ropp_involutive with (r := x).
  rewrite Rmult_minus_distr_r with (r1 := /2) (r2 := f x) (r3 := f (-x)).
  rewrite Ropp_minus_distr with (r1 := f x * /2) (r2 := f (-x) * /2).
  rewrite <- Rmult_minus_distr_r with (r1 := /2) (r2 := f (-x)) (r3 := f x).
  reflexivity.
Qed.

Theorem fIsEvenPlusOdd : forall (f : R -> R) (x : R), f x = evenPart f x + oddPart f x.
Proof.
  intros.
  (*
    f x = evenPart f x + oddPart f x
  *)

  unfold evenPart.
  unfold oddPart.
  (*
    f x = (f x + f (- x)) * /2 + (f x - f (- x)) * /2
  *)

  rewrite Rmult_plus_distr_r.
  rewrite Rmult_minus_distr_r.
  (*
    f x = f x * /2 + f (- x) * /2 + (f x * /2 - f (- x) * /2)
    f x = (f x * /2 + f (- x) * /2) + (f x * /2 - f (- x) * /2)
  *)

  unfold Rminus.
  (*
    f x = f x * /2 + f (- x) * /2 + (f x * /2 + - (f (- x) * /2))
  *)

  rewrite <- Rplus_assoc with (r1 := f x * /2 + f (- x) * /2) (r2 := f x * /2) (r3 := - (f (- x) * /2)).
  rewrite Rplus_assoc with (r1 := f x * /2) (r2 := f (- x) * /2) (r3 := f x * /2).
  rewrite Rplus_comm with (r1 := f (- x) * /2) (r2 := f x * /2).
  rewrite Rplus_assoc.
  rewrite Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  (*
    f x = f x * / 2 + f x * / 2
  *)

  rewrite <- Rmult_plus_distr_l with (r1 := f x) (r2 := /2) (r3 := /2).
  rewrite <- Rmult_1_l with (r := /2).
  rewrite <- Rmult_plus_distr_r.
  replace (1+1) with 2 by reflexivity.
  rewrite Rinv_r by (apply Rgt_not_eq; apply Rlt_gt; apply Rlt_0_2).
  rewrite Rmult_1_r.
  (*
    f x = f x
  *)

  reflexivity.
Qed.

Parameter Point : Type.
Parameter Between : Point -> Point -> Point -> Prop.
Parameter Congruent : Point -> Point -> Point -> Point -> Prop.

Axiom congruenceSym : forall x y : Point, Congruent x y y x.
Axiom congruenceId : forall x y z : Point, Congruent x y z z -> x = y.
Axiom congruenceTrans : forall u v w x y z : Point, (Congruent u v w x /\ Congruent u v y z) -> Congruent w x y z.

Theorem congruenceBinRefl : forall x y : Point, Congruent x y x y.
Proof.
  intros.
  apply congruenceTrans with (u := y) (v := x) (w := x) (x := y) (y := x) (z := y).
  split.
  - apply congruenceSym with (x := y) (y := x).
  - apply congruenceSym with (x := y) (y := x).
Qed.

(* Theorem congruenceBinTrans : forall u v w x y z : Point, (Congruent u v w x /\ Congruent w x y z) -> Congruent u v y z.
Proof.
  intros.
  destruct H.
  assert (Congruent u v u v) by apply congruenceBinRefl.
  apply congruenceTrans with (u := u) (v := v) (w := u) (x := v) (y := y) (z := z).
  split.
  - apply H1.
  - 
Qed. *)
