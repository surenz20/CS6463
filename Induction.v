(** Exercise 1 (andb_true_elim2) *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H. destruct c.
  Case "c = true".
    reflexivity.
  Case "c = false".
    rewrite <- H. destruct b.
    SCase "b = true".
      reflexivity.
    SCase "b = false".
      reflexivity.  Qed.
      
(** Exercise 2 (basic_induction) *)
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0".
    rewrite -> plus_0_r. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.  Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.
    

(** Exercise 3 (double_plus) *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.  Qed.


(** Exercise 4 (destruct_induction) *)
(** Induction does a destruct but also adds the induction hypothesis. 
      Destruct only destructurizes, but does not add any Induction hypothesis. *)


(** Exercise 5 (evenb_n__oddb_Sn) *)
Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    assert (H: evenb (S (S n')) = evenb n').
    SCase "Proof of assertion".
      reflexivity.
    rewrite -> H. rewrite -> IHn'.
    rewrite -> negb_involutive. reflexivity.  Qed.
    

(** Exercise 6 (more_exercises) *)
Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof. 
(* prediction: need induction *)
  intros n. induction n. reflexivity. simpl. rewrite <- IHn. reflexivity. Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
(* prediction: do not need induction, just reflexivity *)
Proof. reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
(* prediction: need destruct because b comes first in andb *)
Proof. intros b. destruct b. Case "b=true". reflexivity. Case "b=false". reflexivity. Qed.

Theorem plus_ble_compat_l : forall n m p : nat, 
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
(* prediction: need induction in p, because p comes first in the goal. *)
  Proof. intros n m p. intros H.  (* note: important to introduce H before starting the induction. *)
induction p.
Case "p=0". simpl. rewrite <- H. reflexivity.
Case "S p". simpl. rewrite <- IHp. reflexivity. Qed.


Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
(* prediction: do not need induction *)
  reflexivity. Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
(* prediction: do not need induction because 1 comes first in mult? Actually, we would need induction if we didn't use plus_0_r: mult is more difficult than plus to prove things about. *)
  intros n. simpl. rewrite -> plus_0_r. reflexivity. Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
(* prediction: need to destructure b since it comes first in andb. 
Actually, also need to destructure c, because can't compute negb c in general. 
Otherwise would have to prove many lemmas about orb x (negb x)= true etc. *)
 intros b c. destruct b.
Case "b=true". destruct c. 
SCase "c=true". reflexivity.
SCase "c=false". reflexivity.
Case "b=false". destruct c.
SCase "c=true". reflexivity.
SCase "c=false". reflexivity. Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
(* prediction: need induction in n because it comes first in goals. *)

  (n + m) * p = (n * p) + (m * p).
Proof. intros n m p. 
induction n. Case "n=0". reflexivity.
Case "S n". simpl. rewrite <- plus_assoc. rewrite <- IHn. reflexivity. Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
(* prediction: do not need induction, just rewriting.
This is wrong: we don't have any rewriting rules for this yet, only for plus with mult. 
So we have to use induction in n, at least. *)
Proof.
  intros n m p. induction n.
Case "n=0". reflexivity.
Case "S n".  simpl. rewrite -> mult_plus_distr_r. rewrite -> IHn. reflexivity. Qed.

(** Exercise 7 (beq_nat_refl) *)
Theorem beq_nat_refl : forall n : nat, 
  true = beq_nat n n.
Proof.
(* prediction: need induction in n *)

intros n. induction n. Case "n=0". reflexivity.
Case "S n". simpl. rewrite <- IHn. reflexivity. Qed.


(** Exercise 8 (plus_swap') *)
Theorem plus_swap' : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
 intros n m p. rewrite -> plus_comm. replace (n+p) with (p+n).
rewrite <- plus_assoc. reflexivity.
Case "p+n=n+p". rewrite -> plus_comm. reflexivity. Qed.

