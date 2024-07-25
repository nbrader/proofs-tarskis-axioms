Parameter Point : Type.
Parameter Congruent : Point -> Point -> Point -> Point -> Prop.
Parameter Between : Point -> Point -> Point -> Prop.

Axiom congruenceSym : forall x y, Congruent x y y x.
Axiom congruenceId : forall x y z, Congruent x y z z -> x = y.
Axiom congruenceTrans : forall u v w x y z, (Congruent u v w x /\ Congruent u v y z) -> Congruent w x y z.

Theorem congruenceBinRefl : forall x y, Congruent x y x y.
Proof.
  intros.
  apply congruenceTrans with (u := y) (v := x) (w := x) (x := y) (y := x) (z := y).
  split.
  - apply congruenceSym.
  - apply congruenceSym.
Qed.

Theorem congruenceBinSym : forall w x y z, Congruent w x y z -> Congruent y z w x.
Proof.
  intros.
  apply congruenceTrans with (u := w) (v := x) (w := y) (x := z) (y := w) (z := x).
  split.
  - apply H.
  - apply congruenceBinRefl.
Qed.

Theorem congruenceBinTrans : forall u v w x y z, (Congruent u v w x /\ Congruent w x y z) -> Congruent u v y z.
Proof.
  intros.
  destruct H.
  apply congruenceBinSym in H.
  apply congruenceTrans with (u := w) (v := x) (w := u) (x := v) (y := y) (z := z).
  split.
  - apply H.
  - apply H0.
Qed.

Theorem congruenceOrderIrrelevance1 : forall w x y z, Congruent w x y z -> Congruent w x z y.
Proof.
  intros.
  apply congruenceTrans with (u := y) (v := z) (w := w) (x := x) (y := z) (z := y).
  split.
  - apply congruenceBinSym.
    apply H.
  - apply congruenceSym.
Qed.

Theorem congruenceOrderIrrelevance2 : forall w x y z, Congruent w x y z -> Congruent x w y z.
Proof.
  intros.
  apply congruenceTrans with (u := w) (v := x) (w := x) (x := w) (y := y) (z := z).
  split.
  - apply congruenceSym.
  - apply H.
Qed.

Theorem congruenceOrderIrrelevance3 : forall w x y z, Congruent w x y z -> Congruent x w z y.
Proof.
  intros.
  apply congruenceOrderIrrelevance1.
  apply congruenceOrderIrrelevance2.
  apply H.
Qed.

Axiom betweenId : forall x y, Between x y x -> x = y.
Axiom betweenPasch : forall u v x y z, (Between u v x /\ Between y z x) -> exists a, Between u a z /\ Between v a y.
Axiom betweenContinuity : forall phi psi : Point -> Prop,
                          (exists a,
                          forall x y,
                          ((phi x /\ psi y) -> Between a x y)) ->
                          (exists b,
                          forall x y,
                          ((phi x /\ psi y) -> Between x b y)).

Axiom lowerDim : exists a b c, ~Between a b c /\ ~Between b c a /\ ~Between c a b.
Axiom upperDim : forall u v x y z, Congruent x y x v /\ Congruent y u y v /\ Congruent z u z v /\ u <> v -> Between x y z \/ Between y z x \/ Between z x y.
Axiom euclid : forall u v x y z, (Between x u v /\ Between y u z /\ x <> u) -> exists a b, Between x y a /\ Between x z b /\ Between a v b.
Axiom fiveSegment : forall x y z x' y' z' u u', (x <> y /\ Between x y z /\ Between x' y' z' /\ Congruent x y x' y' /\ Congruent y z y' z' /\ Congruent x u x' u' /\ Congruent y u y' u') -> Congruent z u z' u'.
Axiom segmentConstr : forall x y a b, exists z, Between x y z /\ Congruent y z a b.
