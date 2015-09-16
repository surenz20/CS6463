(** attempted 4 and completed 4 out of 4 optional exercises *)
(** attempted 3 and completed 3 out of 3 advanced exercises *)
(** Exercise 1 (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as (n, m). reflexivity.  Qed.


(** Exercise 2 (optional (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as (n, m). reflexivity.  Qed.
  

(** Exercise 3 (list_funs) *)
ixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | O :: t => nonzeros t
  | h :: t => h :: (nonzeros t)
  end.
Example test_nonzeros:          nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity.  Qed.
Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match oddb h with
              | true => h :: (oddmembers t)
              | false => oddmembers t
              end
  end.

Example test_oddmembers:        oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity.  Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1:  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers2:  countoddmembers [0;2;4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers3:  countoddmembers nil = 0.
Proof. reflexivity.  Qed.


(** Exercise 4 (advanced (alternate)) *)
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil, l2' => l2'
  | l1', nil => l1'
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
  end.

Example test_alternate1:        alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity.  Qed.
Example test_alternate2:        alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity.  Qed.
Example test_alternate3:        alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity.  Qed.
Example test_alternate4:        alternate [] [20;30] = [20;30].
Proof. reflexivity.  Qed.


(** Exercise 5 (bag_functions) *)
Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => O
  | h :: t => match (beq_nat h v) with
              | true => S (count v t)
              | false => count v t
              end
  end.
Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity.  Qed.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity.  Qed.


(** Exercise 6 (bag functions) *)
Definition sum : bag -> bag -> bag :=
  app.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity.  Qed.

Definition add (v:nat) (s:bag) : bag :=
  v :: s.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity.  Qed.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity.  Qed.

Definition member (v:nat) (s:bag) : bool :=
  match count v s with
  | O   => false
  | S _ => true
  end.

Example test_member1:             member 1 [1;4;1] = true.
Proof. reflexivity.  Qed.
Example test_member2:             member 2 [1;4;1] = false.
Proof. reflexivity.  Qed.

(** Exercise 7 (optional (bag_more_functions)) *)
Fixpoint remove_one (v:nat) (s:bag) : bag :=
  (* When remove_one is applied to a bag without the number to remove,
     it should return the same bag unchanged. *)
  match s with
  | nil => nil
  | h :: t => match beq_nat h v with
              | true => t
              | false => h :: (remove_one v t)
              end
  end.
Example test_remove_one1:         count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity.  Qed.
Example test_remove_one2:         count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity.  Qed.
Example test_remove_one3:         count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity.  Qed.
Example test_remove_one4:         count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity.  Qed.
Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match beq_nat h v with
              | true => remove_all v t
              | false => h :: (remove_all v t)
              end
  end.

Example test_remove_all1:          count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity.  Qed.
Example test_remove_all2:          count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity.  Qed.
Example test_remove_all3:          count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity.  Qed.
Example test_remove_all4:          count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity.  Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil => true
  | h :: t => match member h s2 with
              | true => subset t (remove_one h s2)
              | false => false
              end
  end.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
Proof. reflexivity.  Qed.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity.  Qed.


(** Exercise 8 (bag_theorem) *)
Theorem beq_nat_refl: forall n : nat,
  beq_nat n n = true.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem add_count: forall (n : nat) (s : bag),
  count n (add n s) = S (count n s).
Proof.
  intros n s. destruct s as [| m l'].
  Case "s = nil".
    simpl. rewrite -> beq_nat_refl. reflexivity.
  Case "s = cons".
    simpl. rewrite -> beq_nat_refl. reflexivity.  Qed.


(** Exercise 9 (list_exercises) *)
Theorem app_nil_end : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> IHl'. reflexivity.  Qed.

Theorem rev_snoc: forall n : nat, forall l : natlist,
  rev (snoc l n) = n :: rev l.
Proof.
  intros n l. induction l as [| m l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> IHl'. reflexivity.  Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> rev_snoc. rewrite -> IHl'. reflexivity.  Qed.
Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite -> app_ass. rewrite -> app_ass. reflexivity.  Qed.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros l n. induction l as [| m l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> IHl'. reflexivity.  Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2. induction l1 as [| n1 l1'].
  Case "l1 = nil".
    simpl. rewrite -> app_nil_end. reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> snoc_append. rewrite -> snoc_append.
    rewrite -> IHl1'. rewrite -> app_ass. reflexivity.  Qed.
Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| n1 l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'.
    destruct n1 as [| n1'].
    SCase "n1 = O".
      reflexivity.
    SCase "n1 = S n1'".
      reflexivity.  Qed.


(** Exercise 10 (beq_natlist) *)
Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
  | h1 :: t1 => match l2 with
                | h2 :: t2 => andb (beq_nat h1 h2) (beq_natlist t1 t2)
                | nil => false
                end
  | nil      => match l2 with
                | h2 :: t2 => false
                | nil => true
                end
  end.

Example test_beq_natlist1 :   (beq_natlist nil nil = true).
  Proof. reflexivity.  Qed.
Example test_beq_natlist2 :   beq_natlist [1;2;3] [1;2;3] = true.
  Proof. reflexivity.  Qed.
Example test_beq_natlist3 :   beq_natlist [1;2;3] [1;2;4] = false.
  Proof. reflexivity.  Qed.
Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros l. induction l as [| l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite <- IHl. rewrite <- beq_nat_refl. simpl. reflexivity.
  Qed.


(** Exercise 11 (list_design) *)
Theorem cons_snoc_append: forall (n1 n2 : nat), forall l : natlist,
  [n1] ++ (snoc l n2) = (cons n1 l) ++ [n2].
Proof.
  intros n1 n2 l. simpl. rewrite -> snoc_append. reflexivity.  Qed.


(** Exercise 12 (advanced (bag_proofs)) *)
Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  intros s.
  simpl. reflexivity. Qed.
Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s. induction s as [|n s'].
  Case "s = nil".
    simpl. reflexivity.
  Case "s = cons".
    simpl. destruct n.
    SCase "n = 0".
      simpl. rewrite ble_n_Sn. reflexivity.
    SCase "n = S n'".
      simpl. rewrite IHs'. reflexivity.
  Qed.


(** Exercise 13 (optional (bag_count_sum)) *)
Theorem bag_count_sum: forall n : nat, forall s1 s2 : bag,
  count n (sum s1 s2) = (count n s1) + (count n s2).
Proof.
  intros n s1 s2. induction s1 as [| m s1'].
  Case "s1 = nil".
    reflexivity.
  Case "s1 = cons".
    simpl. rewrite -> IHs1'.
    remember (beq_nat m n) as eq.
    destruct eq.
    SCase "eq = true".
      reflexivity.
    SCase "eq = false".
      reflexivity.  Qed.


(** Exercise 14 (advanced (rev_injective)) *)
Theorem rev_injective: forall l1 l2 : natlist,
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.  Qed.


(** Exercise 15 (hd_opt) *)
Definition hd_opt (l : natlist) : natoption :=
  match l with
  | h :: t => Some h
  | nil => None
  end.

Example test_hd_opt1 : hd_opt [] = None.
 Proof. reflexivity.  Qed.

Example test_hd_opt2 : hd_opt [1] = Some 1.
 Proof. reflexivity.  Qed.

Example test_hd_opt3 : hd_opt [5;6] = Some 5.
 Proof. reflexivity.  Qed.


(** Exercise 16 (optional (option_elim_hd)) *)
Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_opt l).
Proof.
  intros l default. destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    reflexivity.  Qed.
    

(** Exercise 17 (dictionary_invariant1) *)
Theorem dictionary_invariant1' : forall (d : dictionary) (k v: nat),
  (find k (insert k v d)) = Some v.
Proof.
  intros d k v. simpl. rewrite <- beq_nat_refl. reflexivity.
  Qed.
  

(** Exercise 18 (dictionary_invariant2) *)
Theorem dictionary_invariant2' : forall (d : dictionary) (m n o: nat),
  beq_nat m n = false -> find m d = find m (insert n o d).
Proof.
  intros d m n o h.
  simpl. rewrite h. reflexivity. Qed.
  


