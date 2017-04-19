Require Import Omega.

Inductive bin : Set :=
  | Zero : bin
  | Double : bin -> bin
  | DoubleOne : bin -> bin.
(* A non negative integer can have many bin representation : 0 is represented by Zero, Double Zero, ... *)

(** binS : bin -> bin, successor of the binary number b *)
Fixpoint binS b :=
  match b with
  | Zero => DoubleOne Zero
  | Double d => DoubleOne d
  | DoubleOne d => Double (binS d)
  end.

(** f : nat -> bin, converts a nat to a bin by iterating binS *)
Fixpoint f n :=
  match n with
  | 0 => Zero
  | S m => binS (f m)
  end.

(** g : bin -> nat, converts a bin to a nat *)
Fixpoint g b :=
  match b with
  | Zero => 0
  | Double d => g d + g d
  | DoubleOne d => S (g d + g d)
  end.

(** h : bin -> bin, returns a bin in a unique form without trailing Double Zero *)
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
  - easy.
  - easy.

  - simpl.
    rewrite IHb.
    omega.
Qed.

Theorem g_f_bij : forall n, g (f n) = n.
Proof.
  induction n.
  - easy.

  - simpl.
    destruct (f n) ; simpl ; rewrite <- IHn.
    + easy.
    + easy.
    + simpl.
      rewrite g_succ.
      omega.
Qed.



Theorem h_invar : forall b, g b = g (h b).
Proof.
  induction b.
  - easy.

  - simpl.
    now destruct (h b) ; rewrite IHb.

  - simpl.
    now rewrite IHb.
Qed.



Lemma f_add : forall n, n <> 0 -> f (n + n) = Double (f n).
Proof.
  induction n.
  - easy.

  - intro.
    simpl.
    rewrite <- (Nat.add_succ_comm n n).
    simpl.
    destruct n.
    + now simpl.
    + assert (S n <> 0) by easy.
      apply IHn in H0.
      now rewrite H0.
Qed.

Lemma g_h_zero : forall b, g (h b) = 0 -> h b = Zero.
Proof.
  induction b ; intro.
  - easy.

  - simpl in H.
    destruct (h b) as []eqn:?.
    + simpl.
      now rewrite Heqb0.

    + rewrite <- Heqb0 in H.
      simpl in H.
      apply (Nat.eq_add_0 (g (h b)) (g (h b))) in H.
      destruct H as [H _].
      rewrite Heqb0 in H.
      apply IHb in H.
      rewrite H in Heqb0.
      simpl.
      now rewrite Heqb0.

    + now simpl in H.

  - now simpl in H.
Qed.

Theorem f_g_h_bij : forall b, f (g (h b)) = h b.
Proof.
  induction b.
  - easy.

  - simpl.
    destruct (h b) as []eqn:?.
    + easy.
    + simpl.
      destruct (g b0 + g b0) as []eqn:?.
      * simpl.
        simpl in IHb.
        now rewrite Heqn in IHb.
      * assert (S n <> 0) by easy.
        apply (f_add (S n)) in H.
        rewrite H.
        rewrite <- Heqn.
        assert (g b0 + g b0 = g (Double b0)) by easy.
        now rewrite H0, IHb.
    + assert (g (Double (DoubleOne b0)) = g (DoubleOne b0) + g (DoubleOne b0)) by easy.
      rewrite H.
      assert (g (DoubleOne b0) <> 0) by easy.
      apply (f_add (g (DoubleOne b0))) in H0.
      now rewrite H0, IHb.

  - simpl.
    destruct (g (h b)).
    + now rewrite <- IHb.
    + assert (S n <> 0) by easy.
      apply (f_add (S n)) in H.
      rewrite H.
      now rewrite <- IHb.
Qed.
