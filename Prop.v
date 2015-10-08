(** Exercise 1 (double_even) *)
Theorem double_even : forall n,
  ev (double n).
Proof.
  intros. induction n.
    Case "0". unfold double. apply ev_0.
    Case "S n". simpl. apply ev_SS. apply IHn.
Qed.


(** Exercise 2 (varieties_of_beauty) *)
(* How many different ways are there to show that 8 is beautiful? *)
(* There is an infinite number of proofs because axiom b_0 can be applied any number of times. *)


(** Exercise 3 (b_times2) *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
  intros. inversion H.
  Case "2*0". simpl. apply b_0.
  Case "2*3".
    simpl. apply b_sum with (n := 3) (m := 3).
    apply b_3. apply b_3.
  Case "2*5".
    simpl. apply b_sum with (n := 5) (m := 5).
    apply b_5. apply b_5.
  Case "2*(n+m)".
    simpl. rewrite H2. rewrite plus_0_r.
    apply b_sum with (n := n) (m := n).
    apply H. apply H.
Qed.


(** Exercise 4 (b_timesm) *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
  intros n m. induction m.
  Case "0 * n".
    intros. simpl. apply b_0.
  Case "S m * n".
    intros. simpl. apply b_sum.
    apply H.
    apply IHm. apply H.
Qed.


(** Exercise 5 (gorgeous_tree) *)
(* Write out the definition of [gorgeous] numbers using inference rule
    notation.
         
          ----------
          gorgeous 0
         
        
        gorgeous n
        --------------
        gorgeous (3+n)
         
        
          gorgeous n
        --------------
        gorgeous (5+n)
*)


(** Exercise 6 (gorgeous_plus13) *)
Theorem gorgeous_plus13: forall n,
  gorgeous n -> gorgeous (13+n).
Proof.
  intros. induction H.
  Case "13 + 0".
    simpl. apply g_plus5. apply g_plus5. apply g_plus3. apply g_0.
  Case "13 + n".
    simpl. apply g_plus3. apply IHgorgeous.
  Case "13 + 5 + n".
    simpl. apply g_plus5. apply IHgorgeous.
Qed.


(** Exercise 7 (gorgeous_sum) *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros. generalize dependent m.  induction H.
  Case "0 + m".
    intros. apply H0.
  Case "3 + n + m".
    intros. apply g_plus3. apply IHgorgeous. apply H0.
  Case "5 + n + m".
    intros. apply g_plus5. apply IHgorgeous. apply H0.
Qed.


(** Exercise 8 (ev__even) *)
(** Could this proof also be carried out by induction on [n] instead
    of [E]?  If not, why not? *)

(* No, because the naturals cannot be inductively shown to all be even. *)


(** Exercise 9 (l_fails) *)
(** The following proof attempt will not succeed.
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
   Intuitively, we expect the proof to fail because not every
   number is even. However, what exactly causes the proof to fail?
The inductive hypothesis proves that [n] is even. This does not allow us to make
progress in proving that [S n] is even for the induction. *)


(** Exercise 10 (ev_sum) *)
Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof.
  intros n m H. generalize dependent m. induction H.
    Case "0".
      intros. simpl. apply H.
    Case "S n".
      intros.
      simpl.
      apply ev_SS.
      apply IHev.
      apply H0.
Qed.


(** Exercise 11 (inversion_practice) *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros. inversion H. inversion H1. apply H3.
Qed.


(** Exercise 12 (total_relation) *)
(**Define an inductive binary relation total_relation that holds between every pair of natural numbers.
  Inductive total_relation : nat -> nat -> Prop :=
  | t_lte : forall n m : nat, n <= m -> total_relation n m
  | t_gt  : forall n m : nat, n > m -> total_relation n m. *)
  

(** Exercise 13 (empty_relation) *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Inductive empty_relation : nat -> nat -> Prop :=
| e_lte_and_gt : forall n m : nat, n <= m -> n > m -> empty_relation n m.

(** Exercise 14 (combine_odd_even) *)
Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => if oddb n then Podd n else Peven n.

(** To test your definition, see whether you can prove the following
    facts: *)

Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros. unfold combine_odd_even. destruct (oddb n) eqn:e1.
  apply H. reflexivity.
  apply H0. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros. unfold combine_odd_even in H. rewrite H0 in H. apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros. unfold combine_odd_even in H. rewrite H0 in H. apply H.
Qed.

