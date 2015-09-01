(** Exercise 1 (nandb) *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => negb b2
  | false => true
  end.
  
Example test_nandb1:               (nandb true false) = true.
Proof. reflexivity.  Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. reflexivity.  Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. reflexivity.  Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. reflexivity.  Qed.


(** Exercise 2 (andb3) *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb (andb b1 b2) b3.

Example test_andb31:                 (andb3 true true true) = true.
Proof. reflexivity.  Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. reflexivity.  Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. reflexivity.  Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. reflexivity.  Qed.


(** Exercise 3 (factorial) *)
Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => mult n (factorial n')
  end.

Example test_factorial1:          (factorial 3) = 6.
Proof. reflexivity.  Qed.
Example test_factorial2:          (factorial 5) = (mult 10 12).
Proof. reflexivity.  Qed.


(** Exercise 4 (blt nat) *)
Definition blt_nat (n m : nat) : bool :=
  (andb (negb (beq_nat n m)) (ble_nat n m)).

Example test_blt_nat1:             (blt_nat 2 2) = false.
Proof. reflexivity.  Qed.
Example test_blt_nat2:             (blt_nat 2 4) = true.
Proof. reflexivity.  Qed.
Example test_blt_nat3:             (blt_nat 4 2) = false.
Proof. reflexivity.  Qed.


(** Exercise 5 (plus id) *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.  Qed.
  
(** Exercise 6 (mult s 1) *)
  Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m H.
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity.  Qed.
  
  
(** Exercise 7 (zero_nbeq_plus_1) *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity.  Qed.
    
    
(** Exercise 8 (boolean_functions) *)
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.  Qed.
  
(** negation_fn_applied_twice *)
Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  rewrite -> negb_involutive.
  reflexivity.  Qed.
  
  
(** Exercise 9 (andb_eq_orb) *)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c. destruct b as [| b'].
    simpl. intros H. rewrite -> H. reflexivity.
    simpl. intros H. rewrite -> H. reflexivity.  Qed.


(** Exercise 10 (binary) *)
Inductive bin : Type :=
  | Z : bin
  | T : bin -> bin
  | M : bin -> bin.

Fixpoint inc (b : bin) : bin :=
  match b with
  | Z    => M Z         (* 0      -> 1        *)
  | T b' => M b'        (* 2n     -> 2n + 1   *)
  | M b' => T (inc b')  (* 2n + 1 -> 2(n + 1) *)
  end.

Fixpoint bin2nat (b : bin) : nat :=
  match b with
  | Z    => O
  | T b' => (bin2nat b') * 2
  | M b' => S ((bin2nat b') * 2)
  end.

Example test_bin1: bin2nat (inc (T (M (M Z)))) = 7.
Proof. reflexivity.  Qed.
Example test_bin2: bin2nat (inc (T (M (T (T Z))))) = S (bin2nat (T (M (T (T Z))))).
Proof. reflexivity.  Qed.

