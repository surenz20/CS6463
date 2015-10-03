(** 4 optional exercises attempted and 4 completed *)

(** Exercise 1(and_assoc) *)
Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split. split. apply HP. apply HQ. apply HR.
Qed.


(** Exercise 2 (or_distributes_over_and_2) *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R. intros H. inversion H as [[HP | HQ] [HP' | HR]].
  apply or_introl. apply HP.
  apply or_introl. apply HP.
  apply or_introl. apply HP'.
  apply or_intror. split. apply HQ. apply HR.
Qed.


(** Exercise 3 (contrapositive) *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H. unfold not. intros HQF. 
  intros HP. apply H in HP. apply HQF in HP.
  apply HP.
Qed.


(** Exercise 4 ((false_beq_nat) *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  intros n. unfold not. induction n as [| n'].
  Case "n = 0".
    intros m H. destruct m as [| m'].
    SCase "m = 0". simpl in H. inversion H.
    SCase "m = S m'". intros. inversion H0.
  Case "n = S n'".
    intros m H. destruct m as [| m'].
    SCase "m = 0". intros. inversion H0.
    SCase "m = S m'". intros. simpl in H. apply IHn' in H. apply H. inversion H0. reflexivity.
Qed.

(** Exercise 5 (optional (proj2))*)
Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
  intros. inversion H. apply H1.
Qed.

(** Exercise 6 (optional (iff_properties)) *)
Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof.
  intros. unfold iff. split.
    intros. apply H.
    intros. apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R HPQ HQR.
  inversion HPQ.
  inversion HQR.
  unfold iff. split.
  intros. apply H in H3. apply H1 in H3. apply H3.
  intros. apply H2 in H3. apply H0 in H3. apply H3.
Qed.


(** Exercise 7 (optional (or_distributes_over_and)) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  apply or_distributes_over_and_1.
  apply or_distributes_over_and_2.
Qed.


(** Exercise 8 (optional (andb_false)) *)
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    destruct c.
    SCase "c = true". inversion H.
    SCase "c = false". right. apply H.
  Case "b = false".
    destruct c.
    SCase "c = true". left. apply H.
    SCase "c = false". left. apply H.
Qed.

(** Exercise 9 (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P. unfold not. 
  apply contradiction_implies_anything. 
Qed.

(** Exercise 10 (excluded_middle_irrefutable) *)
Theorem excluded_middle_irrefutable:  forall (P:Prop), ~ ~ (P \/ ~ P).
Proof.
  intros. unfold not. intros. apply H.
  right. intros. apply H.
  left. apply H0.
Qed.
