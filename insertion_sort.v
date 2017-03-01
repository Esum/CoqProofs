Require Import List.

Fixpoint insert l n :=
  match l with
  | nil => n::nil
  | m::t => if Nat.leb n m then n::l else m::(insert t n)
  end.

Fixpoint sort l :=
  match l with
  | nil => nil
  | n::t => insert (sort t) n
  end.

Fixpoint occ l n :=
  match l with
  | nil => 0
  | m::t => if Nat.eqb m n then 1 + occ t n else occ t n
  end.


Definition is_perm l l' := forall n, occ l n = occ l' n.

Definition is_sorted l := forall n, S n < length l -> nth n l 0 <= nth (S n) l 0.


Lemma eqb_eq : forall n, Nat.eqb n n = true.
Proof.
  now induction n.
Qed.

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

Lemma leb_n_m_le : forall n m, Nat.leb n m = true <-> n <= m.
Proof.
  induction n.
  intro m.
  now pose proof (PeanoNat.Nat.le_0_l m).
  
  intro m.
  destruct m.
  easy.
  simpl.
  split ; intro H.
  apply (IHn m) in H.
  now apply (PeanoNat.Nat.succ_le_mono n m).
  
  apply (PeanoNat.Nat.succ_le_mono n m) in H.
  now apply (IHn m) in H.
Qed.

Lemma nleb_n_m_gt : forall n m, Nat.leb n m = false <-> m < n.
Proof.
  induction n.
  easy.
  
  destruct m.
  simpl.
  split ; intro.
  now pose proof (PeanoNat.Nat.lt_0_succ n).
  reflexivity.
  
  simpl.
  split ; intro.
  apply (IHn m) in H.
  now apply (PeanoNat.Nat.succ_lt_mono m n) in H.

  apply (PeanoNat.Nat.succ_lt_mono m n) in H.
  now apply (IHn m) in H.
Qed.

Lemma succ_eq_lt : forall n m, S n = m -> n < m.
Proof. 
  intros.
  rewrite (eq_sym H).
  now pose proof (PeanoNat.Nat.lt_succ_diag_r n) as H'.
Qed.


Lemma insert_occ : forall l n, occ (insert l n) n = S (occ l n).
Proof.
  induction l.
  intro n.
  simpl.

  now rewrite eqb_eq.

  intro n.
  simpl.

  destruct (Nat.leb n a).
  simpl.
  destruct (Nat.eqb a n).
  rewrite eqb_eq.
  reflexivity.
  rewrite eqb_eq.
  reflexivity.
  simpl.
  destruct (Nat.eqb a n).
  now rewrite IHl.  
  now rewrite IHl.
Qed.

Theorem insert_neq_occ : forall l n m, m <> n -> occ (insert l m) n = occ l n.
Proof.
  intros.
  induction l.
  simpl.
  destruct (eqb_n_m_neq m n) as [Hl Hr].
  apply Hr in H.
  now rewrite H.

  simpl.

  destruct (eqb_n_m_neq m n) as [Hl Hr].
  apply Hr in H.
  destruct (Nat.eqb a n) as []eqn:? ; destruct (Nat.leb m a) as []eqn:?.
  simpl.
  rewrite Heqb.
  now rewrite H.
  simpl.
  rewrite Heqb.
  now rewrite IHl.
  simpl.
  rewrite H.
  now rewrite Heqb.
  simpl.
  rewrite Heqb.
  assumption.
Qed.

Lemma insert_length : forall l n, length (insert l n) = S (length l).
Proof.
  induction l.
  easy.

  intro n.
  simpl.
  destruct (Nat.leb n a).
  easy.
  simpl.
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
  intro n.
  simpl.
  destruct (Nat.eqb a n) as []eqn:?.
  destruct (eqb_n_m_eq a n) as [Hl Hr].
  apply Hl in Heqb.
  rewrite Heqb.
  rewrite insert_occ.
  now rewrite IHl.

  destruct (eqb_n_m_neq a n) as [Hl Hr].
  apply Hl in Heqb.
  now rewrite insert_neq_occ.
Qed.


Lemma insert_le : forall l n, exists m,
  (nth m (insert l n) 0 = n)
  /\ (m <= length l)
  /\ (m < length l -> n <= nth (S m) (insert l n) 0)
  /\ (forall p, p < length l ->
  (p < m -> 
    (nth p (insert l n) 0 = nth p l 0)
    /\ (nth p (insert l n) 0 <= n))
  /\ (m <= p -> nth (S p) (insert l n) 0 = nth p l 0)).
Proof.
  induction l.
  intro n.
  now exists 0.

  intro n.

  destruct (Nat.leb n a) as []eqn:?.
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
  destruct (leb_n_m_le n a) as [Hl _].
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
  destruct (nleb_n_m_gt n a) as [H1 _].
  apply H1 in Heqb.
  now apply (PeanoNat.Nat.lt_le_incl a n) in Heqb.
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
  now rewrite (IHl n).
  assumption.
  rewrite H0.
  rewrite Ha_in.
  apply (succ_eq_lt n m) in H0.
  now apply (Horder n) in H0.

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
  now rewrite (IHl (PeanoNat.Nat.pred n)) ; rewrite H3.
  now pose proof (PeanoNat.Nat.le_0_l m) as H3.
  assumption.
Qed.
