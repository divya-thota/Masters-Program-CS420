(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
(*
    You are only allowed to use these tactics:

    simpl, reflexivity, intros, rewrite, destruct, induction, apply, assert

    You are not allowed to use theorems outside this file *unless*
    explicitly recommended.
*)

(* ---------------------------------------------------------------------------*)




(**

Show that 5 equals 5.

 *)
Theorem ex1:
  5 = 5.
Proof.
reflexivity.
Qed.

(**

Show that equality for natural numbers is reflexive.

 *)
Theorem ex2:
  forall (x:nat), x = x.
Proof.
intros.
reflexivity.
Qed.

(**

Show that [1 + n] equals the successor of [n].

 *)
Theorem ex3:
  forall n, 1 + n = S n.
Proof.
intros.
simpl.
reflexivity.
Qed.

(**

Show that if [x = y], then [y = x].

 *)
Theorem ex4:
  forall x (y:nat), x = y -> y = x.
Proof.
intros.
rewrite H.
reflexivity.
Qed.

(**

Show that if the result of the conjunction and the disjunction equal,
then both boolean values are equal.


 *)
Theorem ex5:
  forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
intros b.
intros c.
destruct b.
- simpl.
  intros H.
  rewrite H.
  reflexivity.
- simpl.
  intros H.
  rewrite H.
  reflexivity.
Qed.

(**

In an addition, we can move the successor of the left-hand side to
the outer most.


 *)
Theorem ex6:
  forall n m, n + S m = S (n + m).
Proof.
intros.
induction n.
- simpl.
  reflexivity.
- simpl.
  rewrite <- IHn.
  reflexivity.
Qed.

(**

If two additions are equal, and the numbers to the left of each addition
are equal, then the numbers to the right of each addition must be equal.
To complete this exercise you will need to use the auxiliary
theorem: eq_add_S


 *)
Theorem ex7:
  forall x y n, n + x = n + y -> x = y.
Proof.
intros.
induction n.
- simpl in H.
  apply H.
- simpl in H.
  Check eq_add_S.
  apply eq_add_S in H.
  apply IHn.
  apply H.

Qed.

(**

Show that addition is commutative.
Hint: You might need to prove `x + 0 = x` and `S (y + x) = y + S x`
separately.


 *)

Lemma X0 : forall x, x + 0 = x.
Proof.
intros x.
induction x.
- simpl.
  reflexivity.
- simpl.
  rewrite IHx.
  reflexivity.
Qed.


Lemma SYX : forall x y, x + S y = S (x + y).
Proof.
intros x y.
induction x.
- simpl.
  reflexivity.
- simpl.
  rewrite IHx.
  reflexivity.
Qed.

Theorem ex8:
  forall x y, x + y = y + x.
Proof.
intros.
induction x.
- simpl.
  rewrite X0.
  reflexivity.
- simpl.
  rewrite IHx.
  rewrite SYX.
  reflexivity.
Qed.

(**

If two additions are equal, and the numbers to the right of each addition
are equal, then the numbers to the left of each addition must be equal.

Hint: Do not try to prove this theorem directly. You should be using
auxiliary results. You can use Admitted theorems.


 *)
Theorem ex9:
  forall x y n, x + n = y + n -> x = y.
Proof.
intros.
induction n.
- simpl.
  rewrite X0 in H.
  rewrite H.
  rewrite X0.
  reflexivity.
- simpl.
  apply IHn.
  Check eq_add_S.
  apply eq_add_S.
  rewrite <- ex6.
  rewrite H.
  apply ex6.
Qed.
