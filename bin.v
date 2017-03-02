Require Import Omega.

Inductive bin : Set :=
  | Zero : bin
  | Double : bin -> bin
  | DoubleOne : bin -> bin.


Fixpoint binS b :=
  match b with
  | Zero => DoubleOne Zero
  | Double d => DoubleOne d
  | DoubleOne d => Double (binS d)
  end.

Fixpoint f n :=
  match n with
  | 0 => Zero
  | S m => binS (f m)
  end.

Fixpoint g b :=
  match b with
  | Zero => 0
  | Double d => g d + g d
  | DoubleOne d => S (g d + g d)
  end.

Fixpoint h b :=
  match b with
  | Zero => Zero
  | Double d => 
    match h d with
    | Zero => Zero
    | d' => Double d'
    end
  | DoubleOne d => DoubleOne (h d)
  end.


Lemma g_succ : forall b, g (binS b) = S (g b).
Proof.
  induction b.
  easy.

  easy.

  simpl.
  rewrite IHb.
  omega.
Qed.


Theorem g_f_bij : forall n, g (f n) = n.
Proof.
  induction n.
  easy.

  simpl.
  destruct (f n) ; simpl.

  now rewrite <- IHn.

  now rewrite <- IHn.  

  rewrite <- IHn.
  simpl.
  rewrite (g_succ b).
  omega.
Qed.

Theorem h_invar : forall b, g b = g (h b).
Proof.
  induction b.
  easy.

  simpl.
  now destruct (h b) ; rewrite IHb.

  simpl.
  now rewrite IHb.
Qed.

Lemma neq_bins_0 : forall b, binS b <> Zero.
Proof.
  intros b H.
  pose proof (g_succ b).
  rewrite H in H0.
  now assert (g Zero = 1).
Qed.


Lemma f_0_zero : forall n, f n = Zero <-> n = 0.
Proof.
  induction n.
  easy.

  simpl.
  split; intro.
  now pose proof (neq_bins_0 (f n)).
  easy.
Qed.


Lemma f_add : forall n, n <> 0 -> f (n + n) = Double (f n).
Proof.
  induction n.
  easy.
  intro.
  simpl.
  rewrite <- (Nat.add_succ_comm n n).
  simpl.
  pose proof(Nat.eq_decidable n 0).
  unfold Decidable.decidable in H0.
  destruct H0 as [H0|H0].
  now rewrite H0.
  apply IHn in H0.
  now rewrite H0.
Qed.

Lemma add_g : forall b, g (Double b) = g b + g b.
Proof. 
  now induction b.
Qed.

Lemma h_double : forall b, Double b = h (Double b) -> b = h b.
Proof.
  intros.
  simpl in H.

  destruct (h b).
  easy.

  now injection H.
  now injection H.
Qed.

Lemma h_double_one : forall b, DoubleOne b = h (DoubleOne b) -> b = h b.
Proof.
  intros.
  simpl in H.

  now destruct (h b) ; injection H.
Qed.

Lemma neq_binS_zero : forall b, binS b <> Zero.
Proof.
  intro.
  now destruct b.
Qed.

Lemma binS_invar : forall b, h b = b -> h (binS b) = (binS b).
Proof.
  induction b.
  easy.
  intros.
  pose proof (eq_sym H) as H'.
  apply (h_double b) in H'.
  now rewrite H' at 2.

  intros.
  pose proof (eq_sym H) as H'.
  apply (h_double_one b) in H'.
  pose proof (eq_sym H') as H''.
  apply IHb in H''.
  simpl binS.
  destruct (binS b) as []eqn:?.
  now pose proof (neq_binS_zero b).
  rewrite <- Heqb0 at 1.
  simpl.
  rewrite Heqb0.
  now rewrite H''.
  
  rewrite <- Heqb0 at 1.
  simpl.
  rewrite Heqb0.
  now rewrite H''.
Qed.



Lemma h_f_invar : forall n, f n = h (f n).
Proof.
  induction n.
  easy.

  simpl.
  destruct (f n).
  easy.
  simpl.
  apply (h_double b) in IHn.
  now rewrite IHn at 1.
  simpl binS.
  apply (h_double_one b) in IHn.
  pose proof (eq_sym IHn) as H.
  apply (binS_invar b) in H.
  simpl.
  rewrite H.
  destruct (binS b) as []eqn:?.
  now pose proof (neq_binS_zero b).
  reflexivity.
  reflexivity.
Qed.

Lemma g_h_zero : forall b, g (h b) = 0 -> h b = Zero.
Proof.
  induction b ; intro.
  easy.
  simpl in H.
  destruct (h b) as []eqn:?.
  simpl.
  now rewrite Heqb0.
  rewrite <- Heqb0 in H.
  simpl in H.
  apply (Nat.eq_add_0 (g (h b)) (g (h b))) in H.
  destruct H as [H _].
  rewrite Heqb0 in H.
  apply IHb in H.
  rewrite H in Heqb0.
  simpl.
  now rewrite Heqb0.
  simpl in H.
  easy.
  simpl in H.
  easy.
Qed.


Theorem f_g_h_bij : forall b, f (g (h b)) = h b.
Proof.
  induction b.
  easy.

  simpl.
  destruct (h b) as []eqn:?.
  easy.
  simpl.
  destruct (Nat.eq_decidable (g b0 + g b0) 0) as [H|H].
  rewrite H.
  simpl.
  simpl in IHb.
  rewrite H in IHb.
  simpl in IHb.
  easy.
  apply (f_add (g b0 + g b0)) in H.
  rewrite H.
  rewrite <- (add_g b0).
  now rewrite IHb.

  rewrite (add_g (DoubleOne b0)).
  assert (g (DoubleOne b0) <> 0).
  easy.
  apply (f_add (g (DoubleOne b0))) in H.
  rewrite H.
  now rewrite IHb.

  simpl.
  destruct (Nat.eq_decidable (g (h b)) 0) as [H|H].
  rewrite H.
  simpl.
  apply (g_h_zero b) in H.
  now rewrite H.
  apply (f_add (g (h b))) in H.
  rewrite H.
  now rewrite IHb.
Qed.
