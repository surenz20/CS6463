(** attempted 1  optional and completed 1 optional *)

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

(** Exercise 9 (XtimesYinZ_spec) *)
(* Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y))*)
Theorem XtimesYinZ_spec : forall st x y st',
  st X = x ->
  st Y = y ->
  XtimesYinZ / st || st' ->
  st' Z = x * y.
Proof.
  intros st x y st' stX stY ev. 
  inversion ev. subst. simpl. 
  apply update_eq.
Qed.

(** Exercise 10 (loop_never_stops) *)
Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef.
  (* Proceed by induction on the assumed derivation showing that
     [loopdef] terminates.  Most of the cases are immediately
     contradictory (and so can be solved in one step with
     [inversion]). *)
  induction contra; try inversion Heqloopdef.
    rewrite -> H1 in H. inversion H.
    subst. apply IHcontra2. reflexivity.
Qed.

(** Exercise 11 (no_whilesR) *)
Inductive no_whilesR: com -> Prop := 
  | nw_skip : no_whilesR SKIP
  | nw_ass  : forall v e, no_whilesR (v ::= e)
  | nw_seq  : forall c1 c2, no_whilesR c1 -> no_whilesR c2 -> no_whilesR (c1 ; c2)
  | nw_if   : forall e c1 c2, no_whilesR c1 -> no_whilesR c2 -> no_whilesR (IFB e THEN c1 ELSE c2 FI).

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split.
    induction c; intros H; try constructor; try (apply IHc1); try (apply IHc2); 
    try (simpl in H; apply andb_true_iff in H; apply H).
      inversion H.
    intros r. induction r; try reflexivity;
      try (simpl; rewrite -> IHr1; rewrite -> IHr2; reflexivity).
Qed.

(** Exercise 12 (optional (neq_id)) *)
Theorem beq_id_sym: forall i1 i2,
  beq_id i1 i2 = beq_id i2 i1.
Proof.
  intros i1 i2. 
  destruct i1. destruct i2. 
  unfold beq_id. apply beq_nat_sym.
Qed.



