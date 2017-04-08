Require Import List.

Module Type DecidableEqLe.

  Parameter A : Type.
  Parameter default : A.

  Parameter le : A -> A -> Prop.
  Infix "<=" := le.
  Parameter le_total : forall a b, a <= b \/ b <= a.
  Parameter leb : A -> A -> bool.
  Infix "<=?" := leb (at level 68).
  Parameter leb_le : forall a b, a <=? b = true <-> a <= b.
  Parameter eqb : A -> A -> bool.
  Infix "=?" := eqb (at level 68).
  Parameter eqb_eq : forall a b, a =? b = true <-> a = b.

End DecidableEqLe.


Module InsertionSort (M : DecidableEqLe).

  Import M.

  Lemma neqb_neq : forall a b, a =? b = false <-> a <> b.
  Proof.
    intros ; split ; intro.
    - intro.
      apply eqb_eq in H0.
      now rewrite H0 in H.
    - destruct (a =? b) as []eqn:?.
      now apply eqb_eq in Heqb0.
      reflexivity.
  Qed.

  Lemma eqb_refl : forall a, a =? a = true.
  Proof.
    intro.
    now apply eqb_eq.
  Qed.

  Lemma eqb_sym : forall a b, a =? b = b =? a.
  Proof.
    intros.
    destruct (b =? a) as []eqn:?.
    - apply eqb_eq in Heqb0.
      subst.
      now rewrite eqb_refl.
    - apply neqb_neq in Heqb0.
      apply neqb_neq.
      intro.
      now apply eq_sym in H.
  Qed.


  Fixpoint insert l n :=
    match l with
    | nil => n::nil
    | m::t => if n <=? m then n::l else m::(insert t n)
    end.

  Fixpoint sort l :=
    match l with
    | nil => nil
    | n::t => insert (sort t) n
    end.

  Fixpoint occ l n :=
    match l with
    | nil => 0
    | m::t => if m =? n then 1 + occ t n else occ t n
    end.


  Definition is_perm l l' := forall a, occ l a = occ l' a.

  Definition is_sorted l := forall n, S n < length l -> nth n l default <= nth (S n) l default.

  Lemma insert_occ : forall l a, occ (insert l a) a = S (occ l a).
  Proof.
    induction l.
    - intro a.
      simpl.
      now rewrite eqb_refl.

    - intro b.
      simpl.
      destruct (leb b a) ; simpl.
    -- destruct (a =? b) ; rewrite eqb_refl ; reflexivity.
    -- destruct (a =? b).
    --- now rewrite IHl.
    --- now rewrite IHl.
  Qed.

  Theorem insert_neq_occ : forall l a b, a <> b -> occ (insert l b) a = occ l a.
  Proof.
    intros.
    induction l ; simpl.
    - apply neqb_neq in H.
      rewrite eqb_sym.
      now rewrite H.

    - apply neqb_neq in H.
      rewrite eqb_sym in H.
      destruct (a0 =? a) as []eqn:? ; destruct (leb b a0) ; simpl ; rewrite Heqb0.
    -- now rewrite H.
    -- now rewrite IHl.
    -- now rewrite H.
    -- assumption.
  Qed.

  Lemma insert_length : forall l a, length (insert l a) = S (length l).
  Proof.
    induction l.
    - easy.

    - intro a0.
      simpl.
      destruct (a0 <=? a).
    -- easy.
    -- simpl.
       now rewrite IHl.
  Qed.


  Theorem sort_correct : forall l, is_perm (sort l) l.
  Proof.
    induction l.
    simpl.
    unfold is_perm.
    intro n.
    simpl.
    reflexivity.
    unfold is_perm.
    intro b.
    simpl.
    destruct (a =? b) as []eqn:?.
    destruct (eqb_eq a b) as [Hl Hr].
    apply Hl in Heqb0.
    rewrite Heqb0.
    rewrite insert_occ.
    now rewrite IHl.

    destruct (neqb_neq a b) as [Hl Hr].
    apply Hl in Heqb0.
    rewrite insert_neq_occ.
    apply IHl.
    intro.
    now apply eq_sym in H.
  Qed.


  Lemma insert_le : forall l n, exists m,
    (nth m (insert l n) default = n)
    /\ (m <= length l)%nat
    /\ (m < length l -> n <= nth (S m) (insert l n) default)
    /\ (forall p, p < length l ->
    (p < m -> 
      (nth p (insert l n) default = nth p l default)
      /\ (nth p (insert l n) default <= n))
    /\ ((m <= p)%nat -> nth (S p) (insert l n) default = nth p l default)).
  Proof.
    induction l.
    intro n.
    now exists 0.

    intro n.

    destruct (n <=? a) as []eqn:?.
    exists 0.
    split.
    simpl.
    now rewrite Heqb.
    split.
    now rewrite (PeanoNat.Nat.le_0_l (length (a::l))).
    split.
    intros.
    simpl.
    rewrite Heqb.
    simpl.
    destruct (leb_le n a) as [Hl _].
    now apply Hl in Heqb.
    intro p.
    split.
    easy.
    simpl.
    rewrite Heqb.
    intros.
    simpl.
    reflexivity.

    destruct (IHl n) as [m' IHl'].
    exists (S m').
    split.
    simpl.
    rewrite Heqb.
    simpl.
    easy.
    split.
    destruct IHl' as [_ [H _]].
    simpl.
    destruct (PeanoNat.Nat.succ_le_mono m' (length l)) as [Hl _].
    now apply Hl in H.
    split.
    simpl.
    intros.
    rewrite Heqb.
    simpl.
    destruct IHl' as [_ [_ [H' _]]].
    destruct (PeanoNat.Nat.succ_lt_mono m' (length l)) as [_ Hr].
    apply Hr in H.
    now apply H' in H.
    intro p.
    simpl.
    split.
    intros.
    split.
    rewrite Heqb.
    simpl.
    destruct p.
    reflexivity.
    destruct IHl' as [_ [_ [H']]].
    pose proof (H1 p) as H1'.
    destruct (PeanoNat.Nat.succ_lt_mono p (length l)) as [_ Hr].
    apply Hr in H.
    apply H1' in H.
    destruct H as [H _].
    destruct (PeanoNat.Nat.succ_lt_mono p m') as [_ Hr'].
    apply Hr' in H0.
    apply H in H0.
    now destruct H0 as [H0l _].
    rewrite Heqb.
    simpl.
    destruct p.
    destruct (le_total a n) as [Hle|Hle].
    easy.
    apply leb_le in Hle.
    now rewrite Hle in Heqb.
    destruct IHl' as [_ [_ [_ H']]].
    destruct (PeanoNat.Nat.succ_lt_mono p (length l)) as [_ Hr].
    apply Hr in H.
    apply (H' p) in H.
    destruct H as [H _].
    destruct (PeanoNat.Nat.succ_lt_mono p m') as [_ Hr'].
    apply Hr' in H0.
    apply H in H0.
    now destruct H0 as [_ H0].

    intros.
    rewrite Heqb.
    simpl.
    destruct p.
    easy.
    destruct (PeanoNat.Nat.succ_lt_mono p (length l)) as [_ Hr].
    destruct (PeanoNat.Nat.succ_le_mono m' p) as [_ Hr'].
    apply Hr in H.
    apply Hr' in H0.
    destruct (IHl') as [_ [_ [_ H1']]].
    pose proof (H1' p).
    intros.
    apply H1 in H.
    destruct H as [_ H].
    now apply H in H0.
  Qed.


  Theorem sort_correct2 : forall l, is_sorted (sort l).
  Proof.
    induction l.
    simpl.
    unfold is_sorted.
    unfold length.
    now intros.

    simpl.
    unfold is_sorted.
    intros.
    destruct (insert_le (sort l) a) as [m Hinsert].
    destruct Hinsert as [Ha_in [Hm_in [Hm_next Horder]]].
    rewrite (insert_length (sort l) a) in H.
    destruct (PeanoNat.Nat.succ_lt_mono n (length (sort l))) as [_ Hr].
    apply Hr in H as H'.
    apply Hr in H.
    clear Hr.
    destruct (PeanoNat.Nat.lt_trichotomy n m) as [H0|[H0|H0]].

    apply (Horder n) in H.
    destruct H as [H _].
    apply H in H0 as H1.
    destruct H1 as [H1 _].
    apply (PeanoNat.Nat.le_succ_l n m) in H0.
    apply (PeanoNat.Nat.le_lteq (S n) m) in H0.
    destruct H0 as [H0|H0].
    apply (PeanoNat.Nat.lt_le_trans (S n) m (length (sort l))) in H0 as H2.
    apply (Horder (S n)) in H2 as H3.
    destruct H3 as [H3 _].
    apply H3 in H0 as H4.
    clear H3.
    destruct H4 as [H4 _].
    rewrite H4.
    rewrite H1.
    now apply IHl.
    assumption.
    rewrite H0.
    rewrite Ha_in.
    assert (n < m).
    destruct (PeanoNat.Nat.le_succ_l n m).
    apply H2.
    rewrite H0.
    apply Peano.le_n.
    now apply (Horder n) in H2.

    rewrite H0 in H, H'.
    apply Hm_next in H.
    rewrite H0.
    now rewrite Ha_in.

    apply (Horder n) in H.
    destruct H as [_ H].
    apply (PeanoNat.Nat.lt_le_incl m n) in H0 as H1.
    apply H in H1.
    apply (PeanoNat.Nat.lt_le_pred m n) in H0 as H2.
    pose proof (PeanoNat.Nat.le_pred_l n) as H3.
    apply (PeanoNat.Nat.le_lt_trans (PeanoNat.Nat.pred n) n (length (sort l))) in H3.
    apply (Horder (PeanoNat.Nat.pred n)) in H3.
    destruct H3 as [_ H3].
    apply H3 in H2.
    clear H3.
    apply (PeanoNat.Nat.le_lt_trans 0 m n) in H0.
    apply (PeanoNat.Nat.lt_neq 0 n) in H0.
    apply (PeanoNat.Nat.neq_sym 0 n) in H0.
    apply (PeanoNat.Nat.succ_pred n) in H0 as H3.
    rewrite H3 in H2.
    rewrite H1, H2.
    rewrite <- H3 at 2.
    apply IHl.
    now rewrite H3.
    now pose proof (PeanoNat.Nat.le_0_l m) as H3.
    assumption.
  Qed.

End InsertionSort.


Module NatDecidableEqLe <: DecidableEqLe.

  Definition A := nat.
  Definition le := Peano.le.
  Definition le_total := PeanoNat.Nat.le_ge_cases.
  Definition leb := PeanoNat.Nat.leb.
  Definition leb_le := PeanoNat.Nat.leb_le.
  Definition eqb := PeanoNat.Nat.eqb.
  Definition eqb_eq := PeanoNat.Nat.eqb_eq.
  Definition default := 0.

End NatDecidableEqLe.


Module NatInsertionSort := InsertionSort NatDecidableEqLe.
