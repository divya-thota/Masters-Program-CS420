(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)

Set Default Goal Selector "!".

Require Import Turing.Turing.
Require Import Turing.LangRed.
Require Import Turing.LangDec.
Require Import Turing.Problems.
Require Import Coq.Logic.FunctionalExtensionality.

(* ---------------------------------------------------------------------------*)

(* ------------------------ BEGIN UTILITY RESULTS ---------------------- *)
Ltac invc H := inversion H; subst; clear H.

Lemma a_tm_rw:
  forall M i,
  A_tm <[ M, i ]> <->
  Run (Call M i) true.
Proof.
  unfold A_tm.
  intros.
  run_simpl_all.
  reflexivity.
Qed.

(* -------------------------- END OF UTILITY RESULTS ---------------------- *)



(**

=== Background information on map-reducibility ===

First recall the definition of <=m .

  Notation "<=m".

outputs:

  Notation "x <=m y" := (Reducible x y) (default interpretation)

So, what is reducible:

  Print Reducible.
  
Which says:

  Reducible = 
  fun A B : lang => exists f : input -> input, Reduction f A B
      : lang -> lang -> Prop

  Arguments Reducible A B

The important bit here is

    exists f, Reduction f A B

After `Print Reduction.` we recall that a reduction relates any input i
in A whenever f(i) is in B.

    forall w, A w <-> B (f w)

=== Actual proof ===

We will follow the proof of Theorem 5.28 (which redirects to
the proof of 5.22).

This kind of result needs to be proved directly (without the
aid of any theorem, so let us open up both definitions: 

    unfold Reducible, Reduction in *.

At this point, our proof state is as follows:

  H : exists f, forall w : input, A w <-> B (f w)
  H0 : Recognizable B
  ______________________________________(1/1)
  Recognizable A

Let us access the function that maps from A to B with `destruct H as (f, H)`,
and the program that recognizes B `destruct H0 as (M, H0)`.

The pen & paper proof says the following:

  On input w:
  1. Compute f(w).
  2. Run M on input f(w) and output whatever M outputs    

Our next tactics must be as follows to state that `(fun w => M (f w))`
recognizes A.

  exists (fun w => M (f w)).

In Coq, the high-level description can be state as `(fun w => M (f w))`,
since `M` is a program parameterized by an input and
"running M on input f(w)" amounts to calling `M` with argument `f(w)`,
written as `M (f w)`.

Now we apply the theorem `recognizes_def` to show that our program
recognizes language `A`. Following we introduce the input as `i`.

Our goal is now to show:

  Run (M (f i)) true <-> A i

Recall that `M` recognizes `B` (assumption `H0`) and
since `M (f i)` returns `true`, then we have `B (f i)`;
using `rewrite (recognizes_rw H0)` to obtain that fact in the goal
--- if we use `recognizes_rw` without a parameter Coq will complain
that it requires more information.

Finally, we can get rid of `A i` on the right-hand side of the equivalence
by using our map-reducibly assumption, with `rewrite H`.


 *)
Theorem red1:
  forall A B,
  A <=m B ->
  Recognizable B ->
  Recognizable A.
Proof.
        intros.
        unfold Reducible, Reduction in *.
        destruct H as (f, H).
        destruct H0 as (M, H0).
        exists (fun w => M (f w)).
        apply recognizes_def.
        intros.
        rewrite (recognizes_rw H0).
        rewrite <- H.
        reflexivity.
Qed.

(**

We will follow the proof of Theorem 5.22.

First, we simplify `Decidable B` as in HW7 and we simplify our
remaining assumptions as suggested in `red1` until we get the following
proof state:

  H : forall w, A w <-> B (f w)
  H0 : Recognizes M B
  H1 : Decider M
  ______________________________________(1/1)
  Decidable A

We use the same program to decide `A` than we do in exercise `red1`.
Our proof state is now as follows

  Decides (fun w : input => M (f w)) A

We use theorem `decides_def` to continue. The first sub-goal proceeds
exactly like in exercise `red1`.

The second sub-goal we have the following relevant proof state:


  H1: Decider M
  ______________________________________(1/1)
  Decider (fun w : input => M (f w))

Recall that a decider halts for all inputs, `f w` is an arbitrary
input, thus `M` halts for `f w`. To conclude this goal,
write `unfold Decider in *` and use `H1` to conclude.


 *)
Theorem red2:
  forall A B,
  A <=m B ->
  Decidable B ->
  Decidable A.
Proof.
        intros.
        unfold Reducible, Reduction in H.
        destruct H as (f, H).
        destruct H0 as (M, H0).
        destruct H0.
        exists (fun w => M (f w)).
        apply decides_def.
        1: apply recognizes_def.
        1: intros.
        1: rewrite (recognizes_rw H0); rewrite <- H; reflexivity.
        unfold Decider. intros. apply H1.
Qed.

(**

We will follow Prof. Peter Fejer's proof of problem 5.22:

  https://www.cs.umb.edu/~fejer/cs420/hw11s.pdf

Since our goal is an equivalence, we should start with

  split; intros.

Prof. Fejer's proof starts with:

1. "Let M be a Turing machine that recognizes A."

The first goal, first obtain the parameterized program `p` and
assumption `H` from `H: Recognizable A`.

We can convert a parametric program, such as `p`, into an abstract
Turing machine with

    destruct (code_of p) as (M, Hp).

This tactics yields an abstract Turing machine `M` and an
assumption `Hp : CodeOf p M` which establishes the equivalence
between the parametric function `p` and the abstract Turing machine `M`.

We now have all of the ingredient's to continue Prof. Fejer's proof:

2. "The function f defined by f (w) =〈M, w〉is a reduction from A to A_tm"

We can state that with the tactics:

  apply reducible_iff with (f:=fun i => <[ M, i ]>).

Finally, the last step of Prof. Fejer's proof is as follows:

3. "because it is obviously computable and we have"

    "w ∈ A iff M accepts w iff〈M, w〉 ∈ A_tm iff f (w) ∈ A_tm"
We can show that "〈M, w〉 ∈ A_tm iff M accepts w" with rewriting
with `a_tm_rw`, since "M accepts w" is represented in
Coq by `Run (Call M w) true`.

We know that `M` represents function `p`; we replace `Run (Call M w) true`
by `Run (p w) true` by rewriting with `(code_of_run_rw Hp)`.

Finally, since `p` recognizes `A` we can replace `Run (p w) true` by
`A w` using `(recognizes_rw H)`.

The second case is trivial knowing what we proved so far, if you recall
that `A_tm` is recognizable, given by a_tm_recognizable. Read Prof. Fejer's
proof to get the remaining details.


 *)
Theorem red3:
  forall A, Recognizable A <-> A <=m A_tm.
Proof.
        intros.
        split.
        all:intros.
        1: destruct H as (p, H).
        1: destruct (code_of p) as (M, Hp).
        1: apply reducible_iff with (f:=fun i => <[ M, i ]>).
        1: intros.
        1: rewrite a_tm_rw.
        1: rewrite (code_of_run_rw Hp).
        1: rewrite (recognizes_rw H); reflexivity.
        Search ( Recognizable).
        apply red1 with (B:= A_tm) in H.
        1: assumption.
        apply a_tm_recognizable.
Qed.
(**

Prove Corollary 5.29.

 *)
Theorem red4:
  forall A B,
  A <=m B ->
  ~ Recognizable A ->
  ~ Recognizable B.
Proof.
        intros.
        intros N.
        contradict H0.
        apply red1 in H.
        1,2: assumption.
Qed.

(**

Let us solve Exercise 5.6 (solution in pp 242).

First, we simplify our assumptions to obtain.

  Hab : Reduction f A B
  Hbc : Reduction g B C
  ______________________________________(1/1)
  A <=m C

Now apply reducible_iff and with function `fun w => g (f w))`.

Next, we `unfold Reduction in *`.

The remainder should be trivial.


 *)
Theorem red5:
  forall A B C,
  A <=m B ->
  B <=m C ->
  A <=m C.
Proof.
        intros.
        unfold Reducible, Reduction in *.
        invc H; invc H0.
        exists (fun i => x0 (x i)).
        intros.
        rewrite <- H.
        rewrite <- H1.
        reflexivity.
Qed.

(**

Use theorem `co_red_co_1`, which states

  If A <=m B, then compl A <=m compl B.

and what we have learned so far to prove the following statement.


 *)
Theorem red6:
  forall A B,
  A <=m B ->
  Recognizable (compl B) ->
  Recognizable (compl A).
Proof.
        intros.
        apply co_red_co_1 in H.
        apply red1 in H.
        all: assumption.
Qed.

(**

Use the theorem `co_red_2`, which states:

  If A <=m compl B, then compl A <=m B

and what we have learned so far to prove the following statement.


 *)
Theorem red7:
  forall A B C,
  A <=m compl B ->
  compl B <=m C ->
  compl A <=m compl C.
Proof.
        intros.
        apply co_red_2 in H.
        apply co_red_co_1 in H0.
        rewrite co_co_rw in H0.
        apply red5 with (B:= B).
        1,2: assumption.
Qed.

(**

Use theorem dec_rec_co_rec which we learned in class and two other
theorems we established in this assignment to conclude this proof.


 *)
Theorem red8:
  forall A,
  Decidable A ->
  A <=m compl A_tm.
Proof.
        intros.
        apply dec_rec_co_rec in H.
        destruct H.
        apply red3 in H0.
        apply co_red_co_1 in H0.
        rewrite co_co_rw in H0.
        auto.
Qed.

(**

Recall that A_tm is not recognizable (co_a_tm_not_recognizable).
Show that if A_tm is map-reducible to A, then the complement of A is not
recognizable. Hint use: co_red_co_1.


 *)
Theorem red9:
  forall A,
  A_tm <=m A ->
  ~ Recognizable (compl A).
Proof.
        intros.
        intros N.
        apply co_red_co_1 in H.
        apply red4 in H.
        1: contradiction.
        Search A_tm.
        apply co_a_tm_not_recognizable.
Qed.

(**

Show A_tm is *not* map-reducible to decidable languages.

Start the proof by assuming that A_tm <= A and then reach a contradiction,
which is obtained because we can show that compl A is recognizable and
compl A is unrecognizable.

1. We can prove that compl A is recognizable from A decidable.
2. We can prove that compl A is unrecognizable as follows:
   We have `compl A_tm <=m compl A_tm` and that `compl A_tm` is unrecognizable,
   so `compl A` is unrecognizable (which is one of the exercises prove here).
   The proof is similar to red9. 


 *)
Theorem red10:
  forall A,
  Decidable A ->
  ~ (A_tm <=m A).
Proof.
        intros.
        intros I.
        apply red9 in I.
        Search Decidable.
        apply decidable_to_co_recognizable with (L:= A) in H.
        contradiction.
Qed.

(**

Show the following trivial statement.


 *)
Theorem red11:
  forall A,
  Decidable A ->
  A <=m A_tm.
Proof.
        intros.
        Search Decidable.
        apply decidable_to_recognizable with (L:= A) in H.
        apply red3 in H.
        1: assumption.
Qed.


Theorem red12:
  forall A B,
  Recognizable A ->
  A_tm <=m B ->
  A <=m B.
Proof.
        intros.
        apply red3 in H.
        apply red5 with (A:= A) (B:= A_tm) (C:= B) in H.
        all: auto.
Qed.

(**

Which language satisfies the following statement?
Ask for a hint if you are unsure. 


 *)
Theorem red13:
  exists A, (A_tm <=m A) /\ Recognizable A.
Proof.
        exists A_tm.
        split.
        1: unfold Reducible, Reduction.
        1: exists (fun i=> i).
        1: intros.
        1: reflexivity.
        apply a_tm_recognizable.
Qed.

(**

Solve Exercise 5.7 of the book. The solution given in pp 242 is as follows:

1. Suppose that A <=m compl A. Then compl A <=m A via co_red_2.
2. Because A is Turing-recognizable, red3 implies that compl A is
   Turing-recognizable, and then dec_rec_co_rec implies that A is decidable.


 *)
Theorem red14:
  forall A,
  Recognizable A ->
  A <=m compl A ->
  Decidable A.
Proof.
        intros.
        apply dec_rec_co_rec.
        split.
        1: auto.
        apply co_red_2 in H0.
        apply red1 in H0.
        all: intuition.
Qed.

