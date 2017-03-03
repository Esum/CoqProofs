Require Import List.

Definition repeats l := exists n m, n < m /\ m < length l /\ nth n l 0 = nth m l 0.

Definition in_list x l := exists n, n < length l /\ x = nth n l 0.

Lemma in_list_decidable : forall x l, in_list x l \/ ~(in_list x l).
Proof. 
  intro x.
  induction l.
  right.
  intro.
  destruct H as [n H].
  now destruct n ; simpl in H ; pose proof (PeanoNat.Nat.neq_succ_diag_r x).
  
  destruct IHl as [IHl|IHl].
  left.
  destruct IHl as [m [H H']].
  exists (S m).
  simpl.
  split.
  now apply (PeanoNat.Nat.succ_lt_mono m (length l)).
  easy.
  destruct (PeanoNat.Nat.eq_decidable x a) as [H|H].
  left.
  exists 0.
  simpl.
  split.
  now apply (PeanoNat.Nat.lt_0_succ (length l)).
  assumption.
  right.
  intro.
  destruct H0 as [m [H0 H0']].
  simpl in H0.
  simpl in H0'.
  destruct m.
  easy.
  apply IHl.
  exists m.
  split.
  now apply (PeanoNat.Nat.succ_lt_mono m (length l)).
  assumption.
Qed.

Lemma repeats_decidable : forall l, repeats l \/ ~ (repeats l).
Proof.
  induction l.
  right.
  intro.
  destruct H as [_ [m [_ [H _]]]].
  easy.

  destruct IHl as [IHl|IHl].
  left.
  destruct IHl as [n [m [H1[H2 H3]]]].
  exists (S n), (S m).
  simpl.
  split.
  now apply (PeanoNat.Nat.succ_lt_mono n m).
  split.
  now apply (PeanoNat.Nat.succ_lt_mono m (length l)).
  assumption.

  destruct (in_list_decidable a l) as [H|H].
  left.
  destruct H as [m [H H']].
  exists 0, (S m).
  simpl.
  split.
  now apply (PeanoNat.Nat.lt_0_succ m).
  split.
  now apply (PeanoNat.Nat.succ_lt_mono m (length l)).
  assumption.

  right.
  intro.
  destruct H0 as [n [m [H1[H2 H3]]]].
  destruct n.
  simpl in H2.
  simpl in H3.
  destruct m.
  easy.
  apply H.
  exists m.
  now applyz (PeanoNat.Nat.succ_lt_mono m (length l)) in H2.
  simpl in H3.
  destruct m.
  easy.
  apply IHl.
  exists n, m.
  simpl in H2.
  apply (PeanoNat.Nat.succ_lt_mono n m) in H1.
  now apply (PeanoNat.Nat.succ_lt_mono m (length l)) in H2.
Qed.

Fixpoint filter_neq x l :=
  match l with
  | nil => nil
  | a::t => if Nat.eqb a x
  	then filter_neq x t
  	else a::(filter_neq x t)
  end.

Lemma eqb_n_m_eq : forall n m, Nat.eqb n m = true <-> n = m.
Proof. 
  induction n.
  now destruct m.
  
  destruct m.
  easy.
  simpl.

  split.
  intro H.
  destruct (IHn m) as [IHnl _].

  now rewrite IHnl.

  destruct (IHn m) as [_ IHnr].
  intro H.
  destruct (PeanoNat.Nat.succ_inj_wd n m) as [H' _].
  apply IHnr.
  apply H'.
  assumption.
Qed.

Lemma eqb_n_m_neq : forall n m, Nat.eqb n m = false <-> n <> m.
Proof.
  induction n.
  now destruct m.

  destruct m.
  easy.
  simpl.
  destruct (IHn m) as [IHnl IHnr].
  split ; intro H.
  
  apply IHnl in H.
  now apply (PeanoNat.Nat.succ_inj_wd_neg n m) in H.
  
  apply (PeanoNat.Nat.succ_inj_wd_neg n m) in H.
  now apply IHnr in H.
Qed.

Lemma filter_le : forall a l, length (filter_neq a l) <= length l.
Proof.
  intro a.
  induction l.
  easy.

  simpl.
  destruct (Nat.eqb a0 a).
  pose proof (PeanoNat.Nat.le_succ_diag_r (length l)).
  now apply (PeanoNat.Nat.le_trans (length (filter_neq a l)) (length l) (S (length l))) in IHl.
  simpl.
  now apply (PeanoNat.Nat.succ_le_mono (length (filter_neq a l)) (length l)).
Qed.

Lemma filter_in : forall a l, in_list a l -> length (filter_neq a l) < length l.
Proof.
  intro a.
  induction l ; intro.
  destruct H as [n [H _]].
  simpl in H.
  easy.
  simpl.

  destruct (Nat.eqb a0 a) as []eqn:?.
  pose proof (filter_le a l).
  now apply (PeanoNat.Nat.lt_succ_r (length (filter_neq a l)) (length l)) in H0.
  apply (eqb_n_m_neq a0 a) in Heqb as Heqb'.
  simpl.
  assert (in_list a l).
  destruct H as [n [H H']].
  destruct n.
  simpl in H'.
  now pose proof (eq_sym H').
  simpl in H.
  simpl in H'.
  exists n.
  now apply (PeanoNat.Nat.succ_lt_mono n (length l)) in H.
  apply IHl in H0.
  now apply (PeanoNat.Nat.succ_lt_mono (length (filter_neq a l)) (length l)).
Qed.

Lemma filter_invar : forall x a, x <> a -> (forall l, in_list x l -> in_list x (filter_neq a l)).
Proof.
  intros x a.
  induction l ; intros.
  easy.

  simpl.
  destruct (Nat.eqb a0 a) as []eqn:?.
  apply (eqb_n_m_eq a0 a) in Heqb.
  rewrite Heqb in H0.
  destruct H0 as [n [H0 H0']].
  destruct n.
  now simpl in H0'.
  simpl in H0.
  simpl in H0'.
  apply IHl.
  exists n.
  now apply (PeanoNat.Nat.succ_lt_mono n (length l)) in H0.

  destruct (PeanoNat.Nat.eq_decidable x a0) as [H'|H'].
  exists 0.
  simpl.
  now pose proof (PeanoNat.Nat.lt_0_succ (length (filter_neq a l))).
  assert (in_list x l).
  destruct H0 as [n [H0 H0']].
  destruct n.
  now simpl in H0'.
  exists n.
  now apply (PeanoNat.Nat.succ_lt_mono n (length l)) in H0.
  apply IHl in H1.
  destruct H1 as [n [H1 H1']].
  exists (S n).
  simpl.
  now apply (PeanoNat.Nat.succ_lt_mono n (length (filter_neq a l))) in H1.
Qed.

Theorem pigeonhole : forall l1 l2, length l2 < length l1 -> (forall x, in_list x l1 -> in_list x l2) -> repeats l1.
Proof.
  induction l1.
  induction l2.
  easy.
  easy.
  intros l2 H1 H2.
  simpl in H1.
  apply (PeanoNat.Nat.lt_succ_r (length l2) (length l1)) in H1.
  apply (PeanoNat.Nat.lt_eq_cases (length l2) (length l1)) in H1.
  destruct H1 as [H1|H1].
  apply IHl1 in H1.
  destruct H1 as [n [m [H1 [H1' H1'']]]].
  exists (S n), (S m).
  simpl.
  apply (PeanoNat.Nat.succ_lt_mono n m) in H1.
  now apply (PeanoNat.Nat.succ_lt_mono m (length l1)) in H1'.
  
  intro x.
  pose proof (H2 x) as H2.
  intro.
  assert (in_list x (a::l1)).
  destruct H as [m [H H']].
  exists (S m).
  simpl.
  now apply (PeanoNat.Nat.succ_lt_mono m (length l1)) in H.
  now apply H2 in H0.
  destruct (in_list_decidable a l1) as [H|H].
  destruct H as [m [H H']].
  exists 0, (S m).
  simpl.
  split.
  now apply (PeanoNat.Nat.lt_0_succ m).
  split.
  now apply (PeanoNat.Nat.succ_lt_mono m (length l1)).
  assumption.

  destruct (repeats_decidable l1) as [H'|H'].
  destruct H' as [n [m [H1' [H2' H3']]]].
  exists (S n), (S m).
  simpl.
  apply (PeanoNat.Nat.succ_lt_mono n m) in H1'.
  now apply (PeanoNat.Nat.succ_lt_mono m (length l1)) in H2'.
  
  destruct (repeats_decidable (a::l1)) as [H0|H0].
  easy.
  assert (forall x, in_list x l1 -> in_list x l2).
  intros.
  destruct (PeanoNat.Nat.eq_decidable x a) as [Heq|Heq].
  now rewrite Heq in H3.
  assert (in_list x (a::l1)).
  destruct H3 as [n [H3 H3']].
  exists (S n).
  simpl.
  split.
  now apply (PeanoNat.Nat.succ_lt_mono n (length l1)).
  assumption.
  now apply (H2 x).
  assert (in_list a l2).
  pose proof (H2 a) as H4.
  assert (in_list a (a::l1)).
  exists 0.
  simpl.
  split.
  now apply (PeanoNat.Nat.lt_0_succ (length l1)).
  reflexivity.
  now apply H4 in H5.
  apply (filter_in a l2) in H4.
  rewrite H1 in H4.
  apply (IHl1 (filter_neq a l2)) in H4.
  easy.

  intros.
  destruct (PeanoNat.Nat.eq_decidable x a) as [Heq|Heq].
  now rewrite Heq in H5.
  apply (H3 x) in H5.
  pose proof (filter_invar x a Heq).
  now apply (H6 l2) in H5.
Qed.
