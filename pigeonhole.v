Require Import List.

Inductive in_list (X : Type) : X -> list X -> Prop :=
  | in_cons_l : forall x l, in_list X x (x::l)
  | in_cons_r : forall x y l, in_list X x l -> in_list X x (y::l).
Implicit Arguments in_list [X].

Lemma in_list_nth (X : Type) (default : X) : forall x l, in_list x l <-> exists n, n < length l /\ x = nth n l default.
Proof.
  intros.
  split.
  - induction l.
    + intro.
      inversion_clear H.
    + intro.
      inversion H ; subst.
      * exists 0.
        split.
        apply PeanoNat.Nat.lt_0_succ.
        reflexivity.
      * apply IHl in H2.
        destruct H2 as [n [H2 H3]].
        exists (S n).
        split.
        now apply (PeanoNat.Nat.succ_lt_mono n _).
        assumption.
  - induction l.
    + intro.
      now destruct H as [n [H _]].
    + intro.
      destruct H as [n [H H0]].
      destruct n.
      * simpl in H0.
        subst.
        apply in_cons_l.
      * apply in_cons_r.
        apply IHl.
        exists n.
        split.
        now apply PeanoNat.Nat.succ_lt_mono.
        assumption.
Qed.
Implicit Arguments in_list_nth [X].

Inductive repeats (X : Type) : list X -> Prop :=
  | repeats_cons_l : forall x l, in_list x l -> repeats X (x::l)
  | repeats_cons_r : forall x l, repeats X l -> repeats X (x::l).
Implicit Arguments repeats [X].

Fixpoint remove_nth (X : Type) n (l : list X) :=
  match n, l with
  | 0, a::l => l
  | S n, a::l => a::(remove_nth X n l)
  | _, nil => nil
  end.
Implicit Arguments remove_nth [X].

Lemma remove_nth_length (X : Type) : forall n (l : list X), n < length l -> length l = S (length (remove_nth n l)).
Proof.
  intros n l.
  revert n.
  induction l.
  - easy.
  - intros.
    simpl.
    apply PeanoNat.Nat.succ_inj_wd.
    + destruct n.
       * easy.
       * now apply IHl, PeanoNat.Nat.succ_lt_mono.
Qed.
Implicit Arguments remove_nth_length [X].

Lemma remove_nth_length_le (X : Type) : forall n (l : list X), length l <= S (length (remove_nth n l)).
Proof.
  intros n l.
  revert n.
  induction l as [|x l] ; intros.
  - apply le_0_n.
  - destruct n.
    + easy.
    + apply le_n_S, IHl.
Qed.
Implicit Arguments remove_nth_length_le [X].

Lemma remove_nth_left (X : Type) (default : X) : forall n l m, m < n -> nth m (remove_nth n l) default = nth m l default.
Proof.
  intros n l.
  revert n.
  induction l as [|x l] ; intros.
  - now destruct n.
  - induction n.
    + easy.
    + apply PeanoNat.Nat.succ_le_mono, PeanoNat.Nat.le_lteq in H.
      destruct H.
      * rewrite <- IHn ; try assumption.
        destruct m.
        -- now destruct n.
        -- simpl.
           destruct n.
           ++ easy.
           ++ simpl remove_nth at 2.
              simpl nth at 2.
              simpl in IHn.
              rewrite IHn ; try assumption.
              now apply IHl, PeanoNat.Nat.lt_le_incl.
      * subst.
        -- destruct n.
           ++ reflexivity.
           ++ assert (n < S n) by constructor.
              now apply IHl in H.
Qed.
Implicit Arguments remove_nth_left [X].

Lemma remove_nth_right (X : Type) (default : X) : forall n l m, n <= m -> nth m (remove_nth n l) default = nth (S m) l default.
Proof.
  intros n l.
  revert n.
  induction l as [|x l] ; intros.
  - now destruct n ; destruct m.
  - simpl.
    destruct m.
    + apply Le.le_n_0_eq in H.
      now subst.
    + destruct n.
      * reflexivity.
      * now apply IHl, PeanoNat.Nat.succ_le_mono.
Qed.
Implicit Arguments remove_nth_right [X].

Definition in_list_decidable (X : Type) := forall (x : X) l, in_list x l \/ ~ in_list x l.

Theorem pigeonhole_classic (X : Type) : in_list_decidable X -> forall (l1 l2 : list X), length l2 < length l1 -> (forall x, in_list x l1 -> in_list x l2) -> repeats l1.
Proof.
  intro H1.
  induction l1.
  - easy.
  - intros.
    pose proof (H1 a l1) as H1.
    destruct H1.
    + now constructor.
    + apply repeats_cons_r.
      assert (in_list a l2) by (apply H0 ; constructor).
      apply (in_list_nth a) in H2.
      destruct H2 as [n H2].
      apply (IHl1 (remove_nth n l2)).
      * unfold lt.
        destruct H2.
        apply remove_nth_length in H2.
        rewrite <- H2.
        now apply Lt.lt_n_Sm_le.
      * intros.
        assert (in_list x (a::l1)) by (now apply in_cons_r).
        apply H0, (in_list_nth a) in H4.
        destruct H4 as [m H4].
        destruct (PeanoNat.Nat.lt_trichotomy m n) as [?|[?|?]].
        -- apply (in_list_nth a).
           exists m.
           split.
           ++ destruct H2.
              apply (PeanoNat.Nat.le_lt_trans (S m) _ (length l2)) in H5 ; try assumption.
              pose proof (remove_nth_length_le n l2).
              now apply PeanoNat.Nat.succ_lt_mono, PeanoNat.Nat.lt_le_trans with (length l2).
           ++ destruct H4.
              subst.
              now apply eq_sym, remove_nth_left.
        -- subst.
           elim H1.
           destruct H2.
           destruct H4.
           rewrite H5.
           now rewrite <- H6.
        -- destruct m.
           ++ easy.
           ++ apply (in_list_nth a).
              exists m.
              split ; destruct H4.
              ** pose proof (remove_nth_length_le n l2).
                 apply (PeanoNat.Nat.lt_le_trans _ _ (S (length (remove_nth n l2)))) in H4 ; try assumption.
                 now apply PeanoNat.Nat.succ_lt_mono.
              ** subst.
                 now apply eq_sym, remove_nth_right, PeanoNat.Nat.succ_le_mono.
Qed.

Lemma pigeonhole_aux (X : Type) (default : X) : forall (l1 l2 : list X), 
  (forall x, in_list x l1 -> in_list x l2) ->
  (exists l3 : list nat, length l3 = length l1 /\ (forall n, n < length l3 -> nth n l3 0 < length l2) /\ (forall n, n < length l3 -> nth (nth n l3 0) l2 default = nth n l1 default) /\ (repeats l3 -> repeats l1)).
Proof.
  induction l1.
  - intros.
    now exists nil.
  - intros.
    destruct (IHl1 l2) as [l3 ?].
    + intros.
      apply H.
      now constructor.
    + assert (in_list a (a::l1)) by constructor.
      apply H, (in_list_nth default) in H1.
      destruct H1 as [n []].
      exists (n::l3).
      destruct H0 as [?[?[]]].
      assert ((forall n0 : nat, n0 < length (n :: l3) -> nth (nth n0 (n :: l3) 0) l2 default = nth n0 (a :: l1) default)).
        induction n0 ; intro.
        easy.
        now apply H4, PeanoNat.Nat.succ_lt_mono.
      repeat split.
      * simpl.
        now rewrite H0.
      * destruct n0 ; intro.
        -- assumption.
        -- now apply H3, PeanoNat.Nat.succ_lt_mono.
      * assumption.
      * intros.
        inversion_clear H7.
        -- apply repeats_cons_l, (in_list_nth default).
           apply (in_list_nth 0) in H8.
           destruct H8 as [m []].
           pose proof (H6 (S m)).
           apply PeanoNat.Nat.succ_lt_mono in H7 as ?.
           apply H9 in H10.
           simpl in H10.
           exists m.
           split.
           ++ now rewrite <- H0.
           ++ now rewrite <- H10, <- H8.
        -- now apply repeats_cons_r, H5.
Qed.
Implicit Arguments pigeonhole_aux [X].

Fixpoint enumerate (X : Type) (l : list X) n :=
  match l with
  | nil => nil
  | _::l => n::(enumerate X l (S n))
  end.
Implicit Arguments enumerate [X].

Lemma enumerate_length (X : Type) : forall (l : list X) n, length (enumerate l n) = length l.
Proof.
  induction l ; intros.
  - reflexivity.
  - simpl.
    cut (length (enumerate l (S n)) = length l).
    intro.
    now rewrite H.
    apply IHl.
Qed.

Lemma enumerate_nth (X : Type) : forall n m (l : list X), n < length l -> nth n (enumerate l m) 0 = n + m.
Proof.
  intros n m l.
  revert n m.
  induction l.
  - now intros.
  - induction n ; intros.
    + easy.
    + simpl.
      rewrite IHl.
      easy.
      now apply PeanoNat.Nat.succ_lt_mono.
Qed.
Implicit Arguments enumerate_nth [X].

Lemma in_list_nat_decidable : in_list_decidable nat.
Proof.
  intro n.
  induction l.
  - now right.
  - destruct (PeanoNat.Nat.eq_decidable n a).
    + left.
      subst.
      apply in_cons_l.
    + destruct IHl.
      * left.
        now constructor.
      * right.
        intro.
        apply H0.
        now inversion H1.
Qed.

Theorem pigeonhole (X : Type) : forall l1 l2 : list X,
  length l2 < length l1 ->
  (forall x, in_list x l1 -> in_list x l2) ->
  repeats l1.
Proof.
  intros.
  induction l1.
  - easy.
  - destruct (pigeonhole_aux a (a::l1) l2) as [l3 [?[]]].
    + intros.
      now apply H0.
    + apply H3.
      apply (pigeonhole_classic nat in_list_nat_decidable) with (enumerate l2 0).
      * now rewrite enumerate_length, H1.
      * intros.
        apply (in_list_nth 0) in H4.
        apply (in_list_nth 0).
        destruct H4 as [n []].
        exists x.
        split.
        -- rewrite H5, enumerate_length.
           now apply H2.
        -- induction x.
           now destruct l2.
           rewrite <- (PeanoNat.Nat.add_0_r (S x)) at 1.
           apply eq_sym, enumerate_nth.
           rewrite H5.
           now apply H2.
Qed.
