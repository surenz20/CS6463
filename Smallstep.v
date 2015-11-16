(** Exercise 1 (test_step_2) *)
Example test_step_2 : 
      P 
        (C 0)
        (P 
          (C 2) 
          (P (C 0) (C 3)))
      ==>
      P 
        (C 0)
        (P 
          (C 2) 
          (C (0 + 3))).
Proof. 
  apply ST_Plus2. apply ST_Plus2. apply ST_PlusConstConst.
Qed.

(** Exercise 2 (redo_determinism) *)
Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  step_cases (induction Hy1) Case; intros y2 Hy2.
    Case "ST_PlusConstConst". step_cases (inversion Hy2) SCase.
      SCase "ST_PlusConstConst". reflexivity.
      SCase "ST_Plus1". inversion H2.
      SCase "ST_Plus2". inversion H2.
    Case "ST_Plus1". step_cases (inversion Hy2) SCase.
      SCase "ST_PlusConstConst". rewrite <- H0 in Hy1. inversion Hy1.
      SCase "ST_Plus1".
        rewrite <- (IHHy1 t1'0).
        reflexivity. assumption.
      SCase "ST_Plus2". rewrite <- H in Hy1. inversion Hy1.
    Case "ST_Plus2". step_cases (inversion Hy2) SCase.
      SCase "ST_PlusConstConst". rewrite <- H1 in Hy1. inversion Hy1.
      SCase "ST_Plus1". inversion H2.
      SCase "ST_Plus2".
        rewrite <- (IHHy1 t2'0).
        reflexivity. assumption.  
Qed.

(** Exercise 3 (smallstep_bools) *)
Definition bool_step_prop1 :=
  tfalse ==> tfalse.

Theorem bool_step_prop1_false : ~ bool_step_prop1.
Proof.
  unfold bool_step_prop1. intros Contra. inversion Contra.
Qed.

Definition bool_step_prop2 :=
     tif
       ttrue
       (tif ttrue ttrue ttrue)
       (tif tfalse tfalse tfalse)
  ==> 
     ttrue.

Theorem bool_step_prop2_false : ~ bool_step_prop2.
Proof.
  unfold bool_step_prop2. intros Contra. inversion Contra.
Qed.

Definition bool_step_prop3 :=
     tif
       (tif ttrue ttrue ttrue)
       (tif ttrue ttrue ttrue)
       tfalse
   ==> 
     tif
       ttrue
       (tif ttrue ttrue ttrue)
       tfalse.

Theorem bool_step_prop3_true : bool_step_prop3.
Proof.
  unfold bool_step_prop3. apply ST_If. apply ST_IfTrue.
Qed.


(** Exercise 4 (smallstep_bool_shortcut) *)
Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tif ttrue t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      tif t1 t2 t3 ==> tif t1' t2 t3
  | ST_ShortCut : forall t1 t2,
      tif t1 t2 t2 ==> t2
  where " t '==>' t' " := (step t t').
  
Definition bool_step_prop4 :=
         tif
            (tif ttrue ttrue ttrue)
            tfalse
            tfalse
     ==> 
         tfalse.

Example bool_step_prop4_holds : 
  bool_step_prop4.
Proof.
  apply ST_ShortCut.
Qed.


(** Exercise 5 (test_multistep_4) *)
Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  ==>*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  eapply multi_step.
    apply ST_Plus2. constructor. apply ST_Plus2. constructor. apply ST_PlusConstConst.
    eapply multi_step.
      apply ST_Plus2. constructor. apply ST_PlusConstConst.
      apply multi_refl.
Qed.


(** Exercise 6 (multistep_congr_2) *)
Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     P t1 t2 ==>* P t1 t2'.
Proof.
  intros t1 t2 t2' V H. multi_cases (induction H) Case.
    apply multi_refl.
    eapply multi_step.
      apply ST_Plus2.
        assumption.
        apply H.
      apply IHmulti.
Qed.


(** Exercise 7 (eval__multistep) *)
Theorem eval__multistep : forall t n,
  t || n -> t ==>* C n.
  
Proof.
  intros t. induction t.
    intros n0 H. inversion H. apply multi_refl.
    intros n0 H. inversion H; subst.
      eapply multi_trans.
      apply multistep_congr_1. apply IHt1. apply H2.
      eapply multi_trans.
      apply multistep_congr_2. constructor. apply IHt2. apply H4.
      eapply multi_step. apply ST_PlusConstConst.
      apply multi_refl.
Qed.


(** Exercise 8 (step__eval) *)
Lemma step__eval : forall t t' n,
     t ==> t' ->
     t' || n ->
     t || n.
Proof.
  intros t t' n Hs. generalize dependent n.
  induction Hs; intros n G.
    inversion G. constructor; constructor.
    inversion G; subst. apply IHHs in H1. constructor; assumption.
    inversion G; subst. apply IHHs in H4. constructor; assumption.
Qed.


(** Exercise 9 (multistep__eval) *)
Theorem multistep__eval : forall t v,
  normal_form_of t v -> exists n, v = C n /\ t || n.
Proof.
  unfold normal_form_of. intros t v [MS NF]. induction MS.
    apply nf_is_value in NF. inversion NF. exists n. split. reflexivity. constructor.
    apply IHMS in NF. destruct NF as [n [A B]]. exists n. split. assumption. eapply step__eval. apply H. apply B.
Qed.

