Require Import Classical.

Parameter Point : Type.
Parameter Congruent : Point -> Point -> Point -> Point -> Prop.
Parameter Between : Point -> Point -> Point -> Prop.

Axiom congruenceSym : forall x y, Congruent x y y x.
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

Print Assumptions congruenceBinRefl.
Print Assumptions congruenceBinSym.
Print Assumptions congruenceBinTrans.
Print Assumptions congruenceOrderIrrelevance1.
Print Assumptions congruenceOrderIrrelevance2.
Print Assumptions congruenceOrderIrrelevance3.

Axiom congruenceId : forall x y z, Congruent x y z z -> x = y.
Axiom segmentConstr : forall x y a b, exists z, Between x y z /\ Congruent y z a b.

Theorem congruenceZero : forall x y, Congruent x x y y.
Proof.
  intros.
  assert (exists z, Between y x z /\ Congruent x z y y) by apply segmentConstr.
  destruct H.
  destruct H.
  apply congruenceId in H0 as H1.
  rewrite <- H1 in H0.
  apply H0.
Qed.

Theorem congruenceIdRev : forall x y z, x = y -> Congruent x y z z.
Proof.
  intros.
  rewrite H.
  apply congruenceZero.
Qed.

Theorem congruenceIdentity : forall x y z, Congruent x y z z <-> x = y.
Proof.
  intros.
  split.
  - apply congruenceId.
  - apply congruenceIdRev.
Qed.

Theorem betweennessRefl1 : forall x y, Between y x x.
Proof.
  intros.
  assert (exists z, Between y x z /\ Congruent x z y y) by apply segmentConstr.
  destruct H.
  destruct H.
  apply congruenceIdentity in H0 as H1.
  rewrite <- H1 in H.
  apply H.
Qed.

Print Assumptions congruenceZero.
Print Assumptions congruenceIdRev.
Print Assumptions congruenceIdentity.
Print Assumptions betweennessRefl1.

Axiom betweennessId : forall x y, Between x y x -> x = y.

Theorem betweennessIdentity : forall x y, Between x y x <-> x = y.
Proof.
  intros.
  split.
  - apply betweennessId.
  - intros.
    rewrite H.
    apply betweennessRefl1.
Qed.

Print Assumptions betweennessIdentity.

Axiom betweennessPasch : forall u v x y z, (Between u v x /\ Between y z x) -> exists a, Between u a z /\ Between v a y.

Theorem betweennessSym : forall x y z, Between x y z -> Between z y x.
Proof.
  intros x y z H.
  specialize betweennessPasch with (u := y) (v := z) (x := z) (y := x) (z := y).
  intros.
  destruct H0.
  - split.
    + apply betweennessRefl1.
    + apply H.
  - destruct H0.
    apply betweennessIdentity in H0.
    rewrite <- H0 in H1.
    apply H1.
Qed.

Theorem betweennessRefl2 : forall x y, Between x x y.
Proof.
  intros.
  apply betweennessSym.
  apply betweennessRefl1.
Qed.

Theorem betweennessTrans : forall w x y z, (Between x y w /\ Between y z w) -> Between x y z.
Proof.
  intros w x y z H.
  specialize betweennessPasch with (u := x) (v := y) (x := w) (y := y) (z := z).
  intros.
  apply H0 in H.
  clear H0.
  destruct H.
  destruct H.
  apply betweennessIdentity in H0.
  rewrite <- H0 in H.
  apply H.
Qed.

Print Assumptions betweennessSym.
Print Assumptions betweennessRefl2.
Print Assumptions betweennessTrans.

Theorem betweennessConn : forall w x y z, (Between x y w /\ Between x z w) -> (Between x y z \/ Between x z y).
Proof.
  intros w x y z H.
  specialize betweennessPasch with (u := x) (v := y) (x := w) (y := x) (z := z).
  intros.
  apply H0 in H as Hx.
  clear H0.
  destruct Hx.
  destruct H0.
  apply betweennessSym in H1.
  destruct H.

  assert (x = w \/ x <> w) by apply classic.
  destruct H3.
  - rewrite <- H3 in *.
    apply betweennessIdentity in H, H2.
    rewrite <- H.
    rewrite <- H2.
    left.
    apply betweennessIdentity.
    reflexivity.
  - 
Admitted.

Axiom euclid : forall u v x y z, (Between x u v /\ Between y u z /\ x <> u) -> exists a b, Between x y a /\ Between x z b /\ Between a v b.

Theorem euclid2 : forall u v w x y z, ((Between x y w /\ Congruent x y y w) /\ (Between x u v /\ Congruent x u u v) /\ (Between y u z /\ Congruent y u u z)) -> Congruent y z v w.
Proof.
  
Admitted.

Theorem euclid3 : forall x y z, Between x y z \/ Between x y z \/ Between x y z \/ (exists a b : Point, (Congruent x a y a /\ Congruent x a z a)).
Proof.
  
Admitted.

Axiom betweennessContinuity : forall phi psi : Point -> Prop,
                          (exists a,
                          forall x y,
                          ((phi x /\ psi y) -> Between a x y)) ->
                          (exists b,
                          forall x y,
                          ((phi x /\ psi y) -> Between x b y)).

Axiom lowerDim : exists a b c, ~Between a b c /\ ~Between b c a /\ ~Between c a b.
Axiom upperDim : forall u v x y z, Congruent x y x v /\ Congruent y u y v /\ Congruent z u z v /\ u <> v -> Between x y z \/ Between y z x \/ Between z x y.
Axiom fiveSegment : forall x y z x' y' z' u u', (x <> y /\ Between x y z /\ Between x' y' z' /\ Congruent x y x' y' /\ Congruent y z y' z' /\ Congruent x u x' u' /\ Congruent y u y' u') -> Congruent z u z' u'.
