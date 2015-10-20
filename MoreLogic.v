(** 1 optional exercise attempted and 1 completed *)

(** Exercise 1 (dist_not_exists) *)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros. unfold not. intros. inversion H0.
    apply H1. apply H.
Qed.


(** Exercise 2 (dist_exists_or) *)
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros. split. intros. inversion H. inversion H0.
  Case "L".
    left. exists witness. apply H1.
    right. exists witness. apply H1.
  Case "R".
   intros. inversion H.
     inversion H0. exists witness. left. apply H1.
     inversion H0. exists witness. right. apply H1.
Qed.

(** Exercise 3 (override_shadow') *)
Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  intros.
  unfold override'.
  destruct (eq_nat_dec k1 k2).
    reflexivity.
    reflexivity.
Qed.

(** Exercise 4 (all_forallb) *)
Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
  | a_nil : all P []
  | a_cons h t : P h -> all P t -> all P (h :: t).

Fixpoint forallb {X : Type} (test : X → bool) (l : list X) : bool :=
  match l with
    | [] ⇒ true
    | x :: l' ⇒ andb (test x) (forallb test l')
  end.
  
Theorem forallb_spec :
  forall X (test : X -> bool) (l : list X),
    forallb test l = true <-> all (fun x => test x = true) l.
Proof.
  intros. split. intros. induction l as [|h t].
    Case "1".
      apply a_nil.
    Case "2".
      apply a_cons.
      simpl in H.
      destruct (test h). reflexivity. apply H.
      apply IHt. simpl in H.
      destruct (test h). apply H. inversion H.
   Case "3".
    intros.
    induction H.
      reflexivity.
      simpl. rewrite H. simpl. apply IHall.
Qed.


(** Exercise 5 (nostutter) *)
Inductive nostutter:  list nat -> Prop :=
  ns_nil : nostutter []
| ns_one : forall x, nostutter [x]
| ns_two : forall x y l, x <> y -> nostutter (y :: l) -> nostutter (x :: (y :: l)).
Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.


Example test_nostutter_2:  nostutter [].
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.


Example test_nostutter_3:  nostutter [5]. 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.


Example test_nostutter_4:      not (nostutter [3;1;1;4]). 
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.
  

(Exercise 6 (optional (not_exists_dist) )*)
Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle. intros HEM X P. unfold not. intros HNE x.
  assert (P x \/ ~ P x). apply HEM.
  inversion H.
    apply H0.
    apply ex_falso_quodlibet. apply HNE. unfold not in H0. exists x. apply H0.
Qed.

