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
