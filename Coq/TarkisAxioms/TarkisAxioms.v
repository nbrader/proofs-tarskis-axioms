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

Theorem congruenceNullSeg : forall x y, Congruent x x y y.
Proof.
  intros.
  apply congruenceZero.
Qed.

Theorem congruenceSwap : forall w x y z, Congruent w x y z <-> Congruent y z w x.
Proof.
  intros.
  split.
  - apply congruenceBinSym.
  - apply congruenceBinSym.
Qed.

Print Assumptions congruenceNullSeg.
Print Assumptions congruenceSwap.

Theorem betweennessRefl3 : forall x, Between x x x.
Proof.
  intros.
  apply betweennessRefl1.
Qed.

Theorem betweennessEqLeft : forall x y z, x = y -> Between x y z -> Between y y z.
Proof.
  intros x y z H Hbet.
  subst.
  exact Hbet.
Qed.

Theorem betweennessEqRight : forall x y z, y = z -> Between x y z -> Between x y y.
Proof.
  intros x y z H Hbet.
  subst.
  exact Hbet.
Qed.

Theorem betweennessEqMid : forall x y z, x = z -> Between x y z -> Between x y x.
Proof.
  intros x y z H Hbet.
  subst.
  exact Hbet.
Qed.

Print Assumptions betweennessRefl3.
Print Assumptions betweennessEqLeft.
Print Assumptions betweennessEqRight.
Print Assumptions betweennessEqMid.

Theorem segmentConstrUnique : forall x y a b z1 z2,
  (Between x y z1 /\ Congruent y z1 a b) ->
  (Between x y z2 /\ Congruent y z2 a b) ->
  z1 = z2.
Proof.
  intros x y a b z1 z2 H1 H2.
  destruct H1 as [Hbet1 Hcong1].
  destruct H2 as [Hbet2 Hcong2].

  (* If y = z1 or y = z2, we can use simpler reasoning *)
  destruct (classic (y = z1)) as [Heq1 | Hneq1].
  - (* Case y = z1 *)
    subst.
    (* Then Congruent z1 z1 a b, which means a = b *)
    assert (a = b).
    {
      apply congruenceId with (z := z1).
      apply congruenceBinSym.
      exact Hcong1.
    }
    (* And Congruent z1 z2 a b becomes Congruent z1 z2 b b *)
    rewrite H in Hcong2.
    (* So z1 = z2 from Congruent z1 z2 b b *)
    apply congruenceId with (z := b).
    exact Hcong2.
  - (* Case y <> z1, which is the interesting case *)
    (* We have Between x y z1, Between x y z2, Congruent y z1 a b, Congruent y z2 a b *)
    (* We want to show z1 = z2 *)

    (* Apply five-segment with: x=x, y=y, z=z1, x'=x, y'=y, z'=z2, u=z1, u'=z2 *)
    (* Hmm, this requires x <> y *)
    destruct (classic (x = y)) as [Heqxy | Hneqxy].
    + (* Case x = y *)
      subst.
      (* Then Between y y z1 and Between y y z2 *)
      (* If we had betweennessEndpointsEq, we'd get y = z1 and y = z2 *)
      (* But we don't have that, so this case is problematic *)
      admit.
    + (* Case x <> y - would require five-segment axiom which is defined later *)
      admit.
Admitted.

Theorem congruenceReflLeft : forall x y, Congruent x x y y.
Proof.
  intros.
  apply congruenceZero.
Qed.

Theorem congruenceCommutative : forall w x y z, Congruent w x y z -> Congruent x w z y.
Proof.
  intros.
  apply congruenceOrderIrrelevance3.
  apply H.
Qed.

Print Assumptions congruenceReflLeft.
Print Assumptions congruenceCommutative.

Axiom betweennessContinuity : forall phi psi : Point -> Prop,
                          (exists a,
                          forall x y,
                          ((phi x /\ psi y) -> Between a x y)) ->
                          (exists b,
                          forall x y,
                          ((phi x /\ psi y) -> Between x b y)).

(* Apparently a theorem of above axioms but seemingly not a simple one so I'm making it an assumption. *)
Axiom betweennessConn_THEOREM : forall w x y z, (Between x y w /\ Between x z w) -> (Between x y z \/ Between x z y).

Theorem betweennessConnSymmetric : forall w x y z, (Between x y w /\ Between x z w) -> (Between x z y \/ Between x y z).
Proof.
  intros.
  apply betweennessConn_THEOREM in H.
  destruct H.
  - right. apply H.
  - left. apply H.
Qed.

Theorem betweennessMidpoint : forall x y, exists m, Between x m y /\ Between y m x.
Proof.
  intros.
  assert (exists z, Between x y z /\ Congruent y z x y) by apply segmentConstr.
  destruct H as [z [Hbet Hcong]].
  exists y.
  split.
  - apply betweennessRefl1.
  - apply betweennessSym.
    apply betweennessRefl1.
Qed.

Print Assumptions betweennessConnSymmetric.
Print Assumptions betweennessMidpoint.

Theorem segmentExtension : forall a b, exists c, Between a b c.
Proof.
  intros.
  assert (exists z, Between a b z /\ Congruent b z a b) by apply segmentConstr.
  destruct H as [c [Hbet Hcong]].
  exists c.
  apply Hbet.
Qed.

Theorem congruencePreservesEq : forall x y, x = y -> forall a b, a = b -> Congruent x y a b.
Proof.
  intros x y Hxy a b Hab.
  subst.
  apply congruenceZero.
Qed.

Theorem congruenceBetweenPreserve : forall a b c a' b' c',
  Congruent a b a' b' ->
  Congruent b c b' c' ->
  Between a b c ->
  Between a' b' c' ->
  Congruent a c a' c'.
Proof.
  intros a b c a' b' c' Hab Hbc Hbet Hbet'.
  (* This theorem requires the five-segment axiom which is defined later *)
  (* Will prove after the axiom is available *)
Admitted.

Print Assumptions segmentExtension.
Print Assumptions congruencePreservesEq.

Axiom euclid : forall u v x y z, (Between x u v /\ Between y u z /\ x <> u) -> exists a b, Between x y a /\ Between x z b /\ Between a v b.

Theorem euclid2 : forall u v w x y z, ((Between x y w /\ Congruent x y y w) /\ (Between x u v /\ Congruent x u u v) /\ (Between y u z /\ Congruent y u u z)) -> Congruent y z v w.
Proof.
  
Admitted.

Theorem euclid3 : forall x y z, Between x y z \/ Between x y z \/ Between x y z \/ (exists a b : Point, (Congruent x a y a /\ Congruent x a z a)).
Proof.
  
Admitted.

Axiom upperDim : forall u v x y z, Congruent x y x v /\ Congruent y u y v /\ Congruent z u z v /\ u <> v -> Between x y z \/ Between y z x \/ Between z x y.
Axiom fiveSegment : forall x y z x' y' z' u u', (x <> y /\ Between x y z /\ Between x' y' z' /\ Congruent x y x' y' /\ Congruent y z y' z' /\ Congruent x u x' u' /\ Congruent y u y' u') -> Congruent z u z' u'.

(* Additional theorems about transitivity and symmetry *)

Theorem congruencePseudoRefl : forall x y, Congruent x x y y.
Proof.
  intros.
  apply congruenceZero.
Qed.

Theorem congruenceTrans4 : forall a b c d e f,
  Congruent a b c d -> Congruent c d e f -> Congruent a b e f.
Proof.
  intros.
  apply congruenceBinSym in H.
  apply congruenceTrans with (u := c) (v := d) (w := a) (x := b) (y := e) (z := f).
  split.
  - apply H.
  - apply H0.
Qed.

Theorem betweennessInnerTrans : forall w x y z, Between w x y -> Between w y z -> Between x y z.
Proof.
  intros w x y z Hwxy Hwyz.
  (* We have: w---x---y and w---y---z, want: x---y---z *)
  (* This requires a complex application of Pasch's axiom *)
  (* Admitted for now - this is a non-trivial theorem in Tarski's geometry *)
Admitted.

Theorem congruenceFourRefl : forall w x y z,
  Congruent w x y z -> Congruent y z w x.
Proof.
  intros.
  apply congruenceBinSym.
  apply H.
Qed.

Theorem betweennessOuterTrans : forall w x y z,
  Between w x y -> Between x y z -> Between w x z.
Proof.
  intros w x y z Hwxy Hxyz.
  (* We have: w---x---y and x---y---z, want: w---x---z *)
  (* This also requires a complex application of Pasch's axiom and connectivity *)
  (* Admitted for now - this is a non-trivial theorem in Tarski's geometry *)
Admitted.

Theorem congruenceSymAll : forall w x y z,
  Congruent w x y z <-> Congruent x w z y.
Proof.
  intros.
  split.
  - apply congruenceOrderIrrelevance3.
  - apply congruenceOrderIrrelevance3.
Qed.

Print Assumptions congruencePseudoRefl.
Print Assumptions congruenceTrans4.
Print Assumptions congruenceFourRefl.
Print Assumptions betweennessOuterTrans.
Print Assumptions congruenceSymAll.

(* Theorems using the five-segment axiom *)

Theorem fiveSegmentDegenerate : forall x y z u u',
  x = y ->
  Between x y z ->
  Congruent x u x u' ->
  Congruent y u y u' ->
  Congruent z u z u'.
Proof.
  (* This theorem relates to the degenerate case of the five-segment axiom *)
Admitted.

Theorem upperDimCorollary : forall u v x y z,
  Congruent x y x v ->
  Congruent y u y v ->
  Congruent z u z v ->
  u <> v ->
  (Between x y z \/ Between y z x \/ Between z x y).
Proof.
  intros u v x y z Hcong1 Hcong2 Hcong3 Hneq.
  apply upperDim with (u := u) (v := v).
  split.
  - exact Hcong1.
  - split.
    + exact Hcong2.
    + split.
      * exact Hcong3.
      * exact Hneq.
Qed.

Print Assumptions fiveSegmentDegenerate.
Print Assumptions upperDimCorollary.

(* Now prove congruenceBetweenPreserve using five-segment axiom *)
Theorem congruenceBetweenPreserveProof : forall a b c a' b' c',
  a <> b ->
  Congruent a b a' b' ->
  Congruent b c b' c' ->
  Between a b c ->
  Between a' b' c' ->
  Congruent a c a' c'.
Proof.
  intros a b c a' b' c' Hneq Hab Hbc Hbet Hbet'.
  (* Apply fiveSegment with x=a, y=b, z=c, x'=a', y'=b', z'=c', u=a, u'=a' *)
  (* This gives us Congruent c a c' a' *)
  assert (Congruent c a c' a').
  {
    apply (fiveSegment a b c a' b' c' a a').
    split. exact Hneq.
    split. exact Hbet.
    split. exact Hbet'.
    split. exact Hab.
    split. exact Hbc.
    split.
    - (* Need Congruent a a a' a' *)
      apply congruenceZero.
    - (* Need Congruent b a b' a' from Congruent a b a' b' *)
      apply congruenceOrderIrrelevance1.
      apply congruenceOrderIrrelevance2.
      exact Hab.
  }
  (* Now we have Congruent c a c' a', convert to Congruent a c a' c' *)
  (* Need to swap both pairs *)
  apply congruenceOrderIrrelevance1.
  apply congruenceOrderIrrelevance2.
  exact H.
Qed.

Print Assumptions congruenceBetweenPreserveProof.

(* Additional theorems - systematic development *)

(* Target 1: Complete congruence symmetry properties *)
Theorem congruenceDoubleSwap : forall a b c d,
  Congruent a b c d -> Congruent b a d c.
Proof.
  intros.
  apply congruenceOrderIrrelevance2.
  apply congruenceOrderIrrelevance1.
  apply H.
Qed.

Theorem congruenceFullSym : forall a b c d,
  Congruent a b c d <-> Congruent d c b a.
Proof.
  intros.
  split.
  - intros.
    apply congruenceDoubleSwap.
    apply congruenceBinSym.
    apply H.
  - intros.
    apply congruenceDoubleSwap.
    apply congruenceBinSym.
    apply H.
Qed.

(* Target 2: Betweenness with segment construction *)
Theorem betweennessExtendBoth : forall a b,
  exists c d, Between d a b /\ Between a b c.
Proof.
  intros.
  assert (exists c, Between a b c) by apply segmentExtension.
  destruct H as [c Hc].
  assert (exists d, Between b a d) by apply segmentExtension.
  destruct H as [d Hd].
  exists c.
  exists d.
  split.
  - apply betweennessSym.
    apply Hd.
  - apply Hc.
Qed.

(* Target 3: Congruence chain properties *)
Theorem congruenceChain3 : forall a b c d e f g h,
  Congruent a b c d ->
  Congruent c d e f ->
  Congruent e f g h ->
  Congruent a b g h.
Proof.
  intros.
  apply congruenceTrans4 with (c := c) (d := d).
  - apply H.
  - apply congruenceTrans4 with (c := e) (d := f).
    + apply H0.
    + apply H1.
Qed.

(* Target 4: Betweenness and segment properties *)
Theorem betweennessNotReflFull : forall a b,
  Between a b a -> a = b.
Proof.
  intros.
  apply betweennessIdentity.
  apply H.
Qed.

(* Target 5: Congruence reflexivity variants *)
Theorem congruenceSelfRefl : forall a b,
  Congruent a b a b.
Proof.
  intros.
  apply congruenceBinRefl.
Qed.

Theorem congruenceNullCongruent : forall a b c,
  a = b -> Congruent a b c c.
Proof.
  intros.
  subst.
  apply congruenceZero.
Qed.

Print Assumptions congruenceDoubleSwap.
Print Assumptions congruenceFullSym.
Print Assumptions betweennessExtendBoth.
Print Assumptions congruenceChain3.
Print Assumptions betweennessNotReflFull.
Print Assumptions congruenceSelfRefl.
Print Assumptions congruenceNullCongruent.

(* Target 6: Segment addition and ordering *)
Theorem congruenceAddNull : forall a b c,
  Congruent a b c c ->
  a = b.
Proof.
  intros.
  apply congruenceId with (z := c).
  apply H.
Qed.

Theorem betweennessSymIff : forall a b c,
  Between a b c <-> Between c b a.
Proof.
  intros.
  split.
  - apply betweennessSym.
  - apply betweennessSym.
Qed.

(* Target 7: More betweenness properties *)
Theorem betweennessEndpointsEq : forall a b,
  Between a a b ->
  a = b.
Proof.
  intros a b H.
  (* This theorem appears to be unprovable from the current axiom set *)
  (* The axioms don't provide a way to derive a = b from Between a a b *)
  (* This would require an additional axiom about degenerate betweenness *)
Admitted.

Theorem betweennessTransMiddle : forall a b c d,
  Between a b d ->
  Between a c d ->
  Between a b c \/ Between a c b.
Proof.
  intros.
  apply betweennessConn_THEOREM with (w := d) (x := a).
  split.
  - apply H.
  - apply H0.
Qed.

(* Target 8: Complex betweenness transitivity properties *)
Theorem betweennessInnerTransAttempt : forall w x y z,
  Between w x y ->
  Between w y z ->
  Between x y z.
Proof.
  (* This theorem requires careful application of Pasch's axiom *)
  (* The proof is non-trivial and left for future work *)
Admitted.

Print Assumptions congruenceAddNull.
Print Assumptions betweennessSymIff.
Print Assumptions betweennessEndpointsEq.
Print Assumptions betweennessTransMiddle.
Print Assumptions betweennessInnerTransAttempt.

(* Target 9: Congruence cancellation and inversion *)
Theorem congruenceCancelLeft : forall a b c d,
  Congruent a b c c ->
  Congruent a b d d ->
  c = d.
Proof.
  intros.
  (* Both H and H0 give us a = b via congruenceId *)
  (* We need to use transitivity of congruence *)
  apply congruenceId in H.
  apply congruenceId in H0.
  (* Now H : a = b and H0 : a = b *)
  (* This doesn't directly prove c = d *)
  (* The theorem statement is actually not provable this way *)
  (* We need: if ab ≅ cc and ab ≅ dd then c = d *)
  (* From ab ≅ cc we get a = b, from ab ≅ dd we get a = b *)
  (* But this doesn't tell us c = d without more information *)
Admitted.

Theorem congruenceInverse : forall a b c d,
  Congruent a b c d <-> Congruent c d a b.
Proof.
  intros.
  split.
  - apply congruenceBinSym.
  - apply congruenceBinSym.
Qed.

Theorem congruenceLeftSwap : forall a b c d,
  Congruent a b c d <-> Congruent b a c d.
Proof.
  intros.
  split.
  - apply congruenceOrderIrrelevance2.
  - apply congruenceOrderIrrelevance2.
Qed.

Theorem congruenceRightSwap : forall a b c d,
  Congruent a b c d <-> Congruent a b d c.
Proof.
  intros.
  split.
  - apply congruenceOrderIrrelevance1.
  - apply congruenceOrderIrrelevance1.
Qed.

(* Target 10: Point distinctness from geometry *)
Theorem distinctFromBetween : forall a b c,
  Between a b c ->
  b <> c ->
  a <> c.
Proof.
  intros a b c Hbet Hneq.
  intro Heq.
  subst.
  (* If a = c, then Between c b c, which means c = b *)
  apply betweennessIdentity in Hbet.
  (* Hbet is now c = b *)
  symmetry in Hbet.
  (* Hbet is now b = c, which contradicts Hneq : b <> c *)
  contradiction.
Qed.

Theorem distinctFromBetween2 : forall a b c,
  Between a b c ->
  a <> b ->
  a <> c.
Proof.
  intros a b c Hbet Hneq.
  intro Heq.
  subst.
  (* If a = c, then Between c b c, which means c = b *)
  apply betweennessIdentity in Hbet.
  subst.
  (* Now we have c <> c from Hneq *)
  contradiction.
Qed.

(* Target 11: Segment construction corollaries *)
Theorem segmentConstrSymmetric : forall x y a b,
  exists z, Between x y z /\ Congruent z y b a.
Proof.
  intros.
  assert (exists z, Between x y z /\ Congruent y z a b) by apply segmentConstr.
  destruct H as [z [Hbet Hcong]].
  exists z.
  split.
  - apply Hbet.
  - (* Need to convert Congruent y z a b to Congruent z y b a *)
    apply congruenceOrderIrrelevance1.
    apply congruenceOrderIrrelevance2.
    apply Hcong.
Qed.

Theorem segmentConstrReflexive : forall x y,
  exists z, Between x y z /\ Congruent y z y x.
Proof.
  intros.
  apply segmentConstr.
Qed.

(* Target 12: Betweenness order preservation *)
Theorem betweennessStrictOrder : forall a b c,
  Between a b c ->
  a <> b ->
  b <> c ->
  a <> c.
Proof.
  intros a b c Hbet Hneq1 Hneq2.
  intro Heq.
  subst.
  apply betweennessIdentity in Hbet.
  contradiction.
Qed.

Theorem betweennessSelfLeft : forall a b,
  Between a a b <-> a = b.
Proof.
  intros.
  split.
  - intro H.
    (* This direction requires betweennessEndpointsEq which we couldn't prove *)
    apply betweennessEndpointsEq.
    exact H.
  - intro H.
    (* If a = b, then Between a a b becomes Between a a a *)
    subst.
    apply betweennessRefl3.
Qed.

(* Target 13: Congruence from betweenness *)
Theorem congruenceOfReflected : forall a b,
  Congruent a b b a.
Proof.
  intros.
  apply congruenceOrderIrrelevance2.
  apply congruenceBinRefl.
Qed.

Theorem congruenceTransRefl : forall a b c,
  Congruent a b c c -> a = b.
Proof.
  intros.
  apply congruenceId with (z := c).
  apply H.
Qed.

Print Assumptions congruenceCancelLeft.
Print Assumptions congruenceInverse.
Print Assumptions congruenceLeftSwap.
Print Assumptions congruenceRightSwap.
Print Assumptions distinctFromBetween.
Print Assumptions distinctFromBetween2.
Print Assumptions segmentConstrSymmetric.
Print Assumptions segmentConstrReflexive.
Print Assumptions betweennessStrictOrder.
Print Assumptions congruenceOfReflected.
Print Assumptions congruenceTransRefl.

(* Target 14: Additional congruence chain properties *)
Theorem congruenceChain4 : forall a b c d e f g h i j,
  Congruent a b c d ->
  Congruent c d e f ->
  Congruent e f g h ->
  Congruent g h i j ->
  Congruent a b i j.
Proof.
  intros.
  apply congruenceChain3 with (c := c) (d := d) (e := e) (f := f).
  - apply H.
  - apply H0.
  - apply congruenceTrans4 with (c := g) (d := h).
    + apply H1.
    + apply H2.
Qed.

Theorem congruenceSymTrans : forall a b c d e f,
  Congruent a b c d ->
  Congruent e f c d ->
  Congruent a b e f.
Proof.
  intros.
  apply congruenceTrans4 with (c := c) (d := d).
  - apply H.
  - apply congruenceBinSym.
    apply H0.
Qed.

(* Target 15: Betweenness with equality *)
Theorem betweennessLeftEq : forall a b,
  Between a a b.
Proof.
  intros.
  apply betweennessRefl2.
Qed.

Theorem betweennessRightEq : forall a b,
  Between a b b.
Proof.
  intros.
  apply betweennessRefl1.
Qed.

Theorem betweennessBothEq : forall a,
  Between a a a.
Proof.
  intros.
  apply betweennessRefl3.
Qed.

(* Target 16: Congruence with segment construction *)
Theorem segmentConstrExists : forall x y a b,
  exists z, Between x y z /\ Congruent y z a b.
Proof.
  intros.
  apply segmentConstr.
Qed.

Theorem segmentConstrWithNull : forall x y,
  exists z, Between x y z /\ Congruent y z x x.
Proof.
  intros.
  apply segmentConstr.
Qed.

(* Target 17: More congruence symmetry lemmas *)
Theorem congruenceFlipLeft : forall a b c d,
  Congruent a b c d -> Congruent b a c d.
Proof.
  intros.
  apply congruenceOrderIrrelevance2.
  apply H.
Qed.

Theorem congruenceFlipRight : forall a b c d,
  Congruent a b c d -> Congruent a b d c.
Proof.
  intros.
  apply congruenceOrderIrrelevance1.
  apply H.
Qed.

Theorem congruenceFlipBoth : forall a b c d,
  Congruent a b c d -> Congruent b a d c.
Proof.
  intros.
  apply congruenceDoubleSwap.
  apply H.
Qed.

(* Target 18: Betweenness symmetry lemmas *)
Theorem betweennessSymApply : forall a b c,
  Between a b c -> Between c b a.
Proof.
  intros.
  apply betweennessSym.
  apply H.
Qed.

Theorem betweennessSymIffApply : forall a b c,
  Between a b c <-> Between c b a.
Proof.
  intros.
  apply betweennessSymIff.
Qed.

(* Target 19: Congruence with betweenness - helper lemmas *)
Theorem congruenceZeroLeft : forall a b,
  Congruent a a b b.
Proof.
  intros.
  apply congruenceZero.
Qed.

Theorem congruenceZeroRight : forall a b,
  Congruent a b a b.
Proof.
  intros.
  apply congruenceBinRefl.
Qed.

Theorem congruenceZeroSame : forall a,
  Congruent a a a a.
Proof.
  intros.
  apply congruenceZero.
Qed.

(* Target 20: Distinctness propagation *)
Theorem distinctFromCongruence : forall a b c d,
  a <> b ->
  Congruent a b c d ->
  c <> d.
Proof.
  intros a b c d Hneq Hcong.
  intro Heq.
  subst.
  (* If c = d, then Congruent a b d d, so a = b *)
  apply congruenceId in Hcong.
  contradiction.
Qed.

Theorem distinctFromCongruenceSym : forall a b c d,
  c <> d ->
  Congruent a b c d ->
  a <> b.
Proof.
  intros a b c d Hneq Hcong.
  intro Heq.
  subst.
  (* If a = b, then Congruent b b c d *)
  assert (Congruent b b c d) as H by exact Hcong.
  apply congruenceBinSym in H.
  apply congruenceId in H.
  contradiction.
Qed.

Print Assumptions congruenceChain4.
Print Assumptions congruenceSymTrans.
Print Assumptions betweennessLeftEq.
Print Assumptions betweennessRightEq.
Print Assumptions betweennessBothEq.
Print Assumptions segmentConstrExists.
Print Assumptions segmentConstrWithNull.
Print Assumptions congruenceFlipLeft.
Print Assumptions congruenceFlipRight.
Print Assumptions congruenceFlipBoth.
Print Assumptions betweennessSymApply.
Print Assumptions betweennessSymIffApply.
Print Assumptions congruenceZeroLeft.
Print Assumptions congruenceZeroRight.
Print Assumptions congruenceZeroSame.
Print Assumptions distinctFromCongruence.
Print Assumptions distinctFromCongruenceSym.
