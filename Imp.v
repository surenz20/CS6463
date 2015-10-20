(** Exercise 1 (optimize_0plus_b) *)
Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot b1
  | BAnd b1 b2  => BAnd b1 b2
  end.
Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros b. induction b;
  simpl; repeat (rewrite -> optimize_0plus_sound); reflexivity.
Qed.

(** Exercise 2 (update_eq) *) 
Theorem update_eq : forall n x st,
  (update st x n) x = n.
Proof.
  intros.
  unfold update. apply eq_id.
Qed.

(** Exercise 3 (update_neq) *)
Theorem update_neq : forall x2 x1 n st,
  x2 <> x1 ->                        
  (update st x2 n) x1 = (st x1).
Proof.
  intros.
  unfold update. apply neq_id. apply H.
Qed.

(** Exercise 4 (update_example) *)
Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  intros. unfold update. simpl. unfold empty_state. reflexivity.
Qed.


(** Exercise 5 (update_shadow) *)
Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
   (update  (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
Proof.
  intros. unfold update. destruct (eq_id_dec x2 x1).
  reflexivity.
  reflexivity.
Qed.


(** Exercise 6 (update_same) *)
Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  intros. unfold update. destruct (eq_id_dec x1 x2).
  subst. reflexivity. reflexivity.
Qed.


(** Exercise 7 (update_permute) *)
Theorem update_permute : forall n1 n2 x1 x2 x3 st,
  x2 <> x1 -> 
  (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
  unfold update. intros. generalize dependent x2. destruct (eq_id_dec x1 x3).
  Case "x1 = x3".
    subst. intros. rewrite neq_id. reflexivity. apply H.
  Case "x1 <> x3".
    reflexivity.
Qed.


(** Exercise 8 (ceval_example2) *)
Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
  apply E_Seq with (update empty_state X 0).
  apply E_Ass. reflexivity.
  apply E_Seq with (update (update empty_state X 0) Y 1).
  apply E_Ass. reflexivity.
  apply E_Ass. reflexivity.
Qed.


