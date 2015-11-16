(** Exercise 1 (some_term_is_stuck) *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (tsucc ttrue). unfold stuck. split.
    intros [e' s].  inversion s. solve by inversion.
    intros s. inversion s. solve by inversion. inversion H. solve by inversion.
Qed.


(** Exercise 2 (step review) *)
(** Quick review.  Answer _true_ or _false_.  In this language...
      - Every well-typed normal form is a value.
        true
      - Every value is a normal form.
        true
      - The single-step evaluation relation is
        a partial function (i.e., it is deterministic).
        true
      - The single-step evaluation relation is a _total_ function.
        false
*)

(** Exercise 3 (finish_preservation) *)
Theorem preservation : forall t t' T,
  has_type t T ->
  t ==> t' ->
  has_type t' T.
Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  has_type_cases (induction HT) Case; 
         (* every case needs to introduce a couple of things *)
         intros t' HE; 
         (* and we can deal with several impossible
            cases all at once *)
         try (solve by inversion).
    Case "T_If". inversion HE; subst.
      SCase "ST_IFTrue". assumption.
      SCase "ST_IfFalse". assumption.
      SCase "ST_If". apply T_If; try assumption.
        apply IHHT1; assumption.
    Case "T_Succ". inversion HE. apply T_Succ. apply IHHT. assumption.
    Case "T_Pred". inversion HE; subst.
      apply T_Zero. 
      inversion HT. assumption.
      apply T_Pred. apply IHHT. assumption.
    Case "T_Iszero". inversion HE; subst.
      constructor.
      constructor.
      apply T_Iszero. apply IHHT. assumption.
Qed.


(** Exercise 4 (preservation_alternate_proof) *)
Theorem preservation' : forall t t' T,
  has_type t T ->
  t ==> t' ->
  has_type t' T.
Proof with eauto.
  intros t t' T HT HE.
  generalize dependent T.
  step_cases (induction HE) Case; intros T HT; inversion HT; subst; try assumption; try auto.
    Case "ST_PredSucc". inversion H1. assumption.
Qed.


(** Exercise 5 (subject_expansion) *)
Theorem subject_expansion : exists t t' T,
  t ==> t' /\ has_type t' T /\ ~ (has_type t T).
Proof.
  exists (tif ttrue tfalse tzero). exists tfalse. exists TBool.
  split.
    apply ST_IfTrue.
    split.
      auto.
      intros Contra. inversion Contra. inversion H5.
Qed.

(** Exercise 6 (variation1) *)
(** Suppose we add the following two new rules to the reduction
    relation:
      | ST_PredTrue : 
           (tpred ttrue) ==> (tpred tfalse)
      | ST_PredFalse : 
           (tpred tfalse) ==> (tpred ttrue)
   Which of the following properties remain true in the presence
   of these rules?  For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.
      - Determinism of [step]
        remains true
      - Progress
        remains true
      - Preservation
        remains true
*)
(** Exercise 7 (variation2) *)
(** Suppose, instead, that we add this new rule to the typing relation: 
      | T_IfFunny : forall t2 t3,
           has_type t2 TNat ->
           has_type (tif ttrue t2 t3) TNat
   Which of the following properties remain true in the presence of
   this rule?  (Answer in the same style as above.)
      - Determinism of [step]
        remains true
      - Progress
        remains true
      - Preservation
        remains true
*)
