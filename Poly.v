(** Attempted 3 optional and completed 3 *)

(** Exercise 1 (mumble_grumble) *)
Check d mumble c: grumble mumble.
Check b a 5 : mumble.
Check d mumble (b a 5) : grumble mumble.
Check d bool (b a 5) : grumble bool.
Check e bool true : grumble bool.
Check e mumble (b c 0): grumble mumble.
Check e mumble c: grumble mumble.
Check c : mumble.

(** Exercise 2 (baz_num_elts) *)
Check x _ : baz.
Check x (x _) : baz.
Check x (y _ true) : baz.
Check y _ _: baz.
Example baz_trivial : forall (b:baz)(q:bool), y b q = y b q.
Proof. reflexivity. Qed.
End MumbleBaz.

(** Exercise 3 (split) *)
Fixpoint split
           {X Y : Type} (l : list (X*Y))
           : (list X) * (list Y) :=
match l with
| [] => ([],[])
| (h,h') :: t => (h:: fst(split t), h':: snd (split t))
end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
reflexivity. Qed.

(** Exercise 4 (filter_even_gt7) *)
Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => andb (evenb x) (ble_nat 8 x) ) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

(** Exercise 5 (partition) *)
Definition partition {X : Type} (test : X -> bool) (l : list X)
                     : list X * list X :=
 (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

(** Exercise 6 (map_rev) *)
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros. induction l. reflexivity. simpl. 
  rewrite map_snoc. rewrite IHl. reflexivity. 
  Qed.

(** Exercise 7 (flat_map) *)
Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) :=
match l with
| [] => [] 
| h::t => (f h) ++ (flat_map f t)
end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 Proof. reflexivity. Qed.
 
 
(** Exercise 8 (override_example) *)
Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof.
  reflexivity. Qed.
  

(** Exercise 9 (override_neq) *)
Theorem override_neq : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
intros. unfold override. rewrite H0. rewrite H. reflexivity.
 Qed.

(** Exercise 10 (fold_length)
Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof. intros. induction l. Case "[]".  reflexivity.  
Case "x::l". unfold fold_length. simpl.  rewrite <- IHl.
reflexivity. Qed.

(** Exercise 11 (fold_map) *)
Theorem fold_map_is_fold: forall (X Y : Type)(f : X -> Y) (l : list X),
fold_map f l = map f l.
Proof.
intros.
induction l. Case "[]". reflexivity.
Case "x::l". unfold fold_map. simpl.
rewrite <- IHl. reflexivity. Qed.

(** Exercise 12 optional (poly_exercises) *)
Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  match count with
  | 0 => []
  | S c => n :: repeat n c
 end.

Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
 Proof. reflexivity. Qed.


Theorem nil_app : forall X:Type, forall l:list X,
  app [] l = l.

Proof. reflexivity. Qed.

Theorem rev_snoc : forall X : Type,
                     forall v : X,
                     forall s : list X,
  rev (snoc s v) = v :: (rev s).
Proof.
  intros. induction s. reflexivity. simpl.
rewrite IHs. reflexivity. Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
intros. induction l. reflexivity. simpl. rewrite rev_snoc. rewrite IHl. reflexivity. Qed.

Theorem snoc_with_append : forall X : Type,
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof. intros. induction l1. reflexivity. simpl. rewrite IHl1. reflexivity. Qed.


(** Exercise 13 (optional (combine_checks)) *)
 (* It prints X->Y->list X->list Y->list (X*Y)
    It prints [(1,false);(2,false)]. *)
Eval compute in (combine [1;2] [false;false;true;true]).
(** Yes, it prints  [(1, false); (2, false)] : list (nat * bool) *)


(** Exercise 14 optional (hd_opt_poly) *)
Definition hd_opt {X : Type} (l : list X)  : option X :=
  match l with
| [] => None
| h::_ => Some h
end.
Check @hd_opt.

Example test_hd_opt1 :  hd_opt [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt2 :   hd_opt  [[1];[2]]  = Some [1].
Proof. reflexivity. Qed.
