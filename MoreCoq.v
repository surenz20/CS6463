(** Attempted 3 optional exercises and completed 3 optional exercises. *)

(** Exercise 1 (apply_exercise1) *)
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  rewrite -> H. symmetry. apply rev_involutive.  
Qed.


(** Exercise 2 (optional (apply_rewrite)) *)
(**Rewrite finds matching subterms and replaces them with their corresponding
    term in a theorem. Apply takes a theorem and uses it to prove the current
    goal if possible. It will try to find instances for quantified variables in
    the hypothesis as needed. *)


(** Exercise 3 (optional (apply_with_exercise)) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with m. apply eq2. apply eq1.  Qed.
  

(** Exercise 4 (sillyex1) *)
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros.
  symmetry.
  inversion H0.
  reflexivity.
Qed.


(** Exercise 5 (sillyex2) *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  intros.
  inversion H.
Qed.


(** Exercise 6 (optional (practice)) *)
Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros. destruct n.
  Case "0". reflexivity.
  Case "S n". inversion H.
Qed.

Theorem beq_nat_0_r : forall n,
   beq_nat n 0 = true -> n = 0.
Proof.
  intros. destruct n.
  Case "0". reflexivity.
  Case "S n". inversion H.
Qed.


(** Exercise 7 (plus_n_n_injective) *)
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "0".
    intros.
    destruct m.
    SCase "0". reflexivity.
    SCase "S n". inversion H.
  Case "S n".
    intros. destruct m.
    SCase "0". inversion H.
    SCase "S m".
      simpl in H.
      rewrite <- plus_n_Sm in H.
      rewrite <- plus_n_Sm in H.
      inversion H.
      apply IHn' in H1.
      rewrite H1.
      reflexivity.
Qed.


(** Exercise 8 (beq_nat_true) *)
Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n. induction n.
  Case "0".
    intros. destruct m.
    SCase "0". reflexivity.
    SCase "S m". inversion H.
  Case "S n".
    intros. induction m.
    SCase "0". inversion H.
    SCase "S m". apply IHn in H. rewrite H. reflexivity.
Qed.


(** Exercise 9 (gen_dep_practice) *)
Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  intros.
  generalize dependent n.
  induction l as [|h t].
  Case "[]".
    intros.
    reflexivity.
  Case "x :: xs".
    destruct n.
    SCase "0".
      intros. inversion H.
    SCase "S n".
      intros. inversion H.
      simpl.
      rewrite H1.
      apply IHt.
      apply H1.
Qed.



(** Exercise 10 ( override_shadow) *)
Theorem override_shadow : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros.
  unfold override.
  destruct (beq_nat k1 k2).
  Case "true". reflexivity.
  Case "false". reflexivity.
Qed.


(** Exercise 11 (destruct_eqn_practice) *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros.
  destruct (f b) eqn:H.
  Case "true".
    destruct b eqn:I.
    SCase "true". rewrite H. apply H.
    SCase "false". destruct (f true) eqn:J. apply J. apply H.

  Case "false".
    destruct b eqn:I.
    SCase "true". destruct (f false) eqn:J. apply H. apply J.
    SCase "false". rewrite H. apply H.
Qed.


(** Exercise 12 (override_same) *)
Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
  intros.
  unfold override.
  destruct (beq_nat k1 k2) eqn:H0.
  Case "true".
    rewrite <- H.
    apply beq_nat_true in H0.
    inversion H0.
    reflexivity.
  Case "false". reflexivity.
Qed.


(** Exercise 13 (beq_nat_sym) *)
Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n.
  induction n.
  Case "0".
    intros m. induction m.
    SCase "0". reflexivity.
    SCase "S m". simpl. reflexivity.
  Case "S n".
    intros m. induction m.
    SCase "0". simpl. reflexivity.
    SCase "S m". simpl. apply IHn.
Qed.


(** Exercise 14 ( override_permute) *)
Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat->X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros.
  unfold override.
  destruct (beq_nat k1 k3) eqn:I.
  Case "true".
    apply beq_nat_true in I.
    rewrite <- I.
    rewrite H.
    reflexivity.
  Case "false".
    destruct (beq_nat k2 k3).
      reflexivity.
      reflexivity.
Qed.
