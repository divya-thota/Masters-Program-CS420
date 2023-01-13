(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
Require Turing.Util.
Require Import Coq.Lists.List.
Import ListNotations.

(* ---------------------------------------------------------------------------*)




(**

Study the definition of [Turing.Util.pow] and [Turing.Util.pow1]
and then show that [Turing.Util.pow1] can be formulated in terms of
[Turing.Util.pow].
Material: https://gitlab.com/umb-svl/turing/blob/main/src/Util.v


 *)
Theorem ex1:
  forall (A:Type) (x:A) n, Util.pow [x] n = Util.pow1 x n.
Proof.
  intros.
  induction n.
  -reflexivity.
  -simpl.
  rewrite IHn.
  reflexivity.
Qed.

(**

Study recursive definition of [List.In] and the inductive definition of
[List.Exists]. Then show that [List.In] can be formulated in terms
of [List.Exists].

Material: https://coq.inria.fr/library/Coq.Lists.List.html


 *)
Theorem ex2:
  forall (A:Type) (x:A) l, List.Exists (eq x) l <-> List.In x l.
Proof.
  intros.
  induction l. {
    simpl.
    apply Exists_nil.
  }
  split. {
    intros.
    induction H. subst. { 
      simpl.
      left.
      reflexivity.
    }
  subst.
  simpl.
  right.
  apply IHExists.
  }
  intros.
  induction H. {
    left.
    symmetry.
    apply H.
  }
  apply IHl in H.
  right.
  apply H.
Qed.
(**

Create an inductive relation that holds if, and only if, element 'x'
appears before element 'y' in the given list.
We can define `succ` inductively as follows:

                                (x, y) succ l
-----------------------R1     ------------------R2
(x, y) succ x :: y :: l       (x, y) succ z :: l

Rule R1 says that x succeeds y in the list that starts with [x, y].

Rule R2 says that if x succeeds y in list l then x succeeds y in a list
the list that results from adding z to list l.


 *)

Inductive succ {X : Type} (x:X) (y:X): list X -> Prop :=
  | R1: forall (l: list X),
      succ x y (x :: y :: l)
  | R2: forall (z:X) (l:list X),
      succ x y l -> succ x y (z::l).



Theorem succ1:
    (* Only one of the following propositions is provable.
       Replace 'False' by the only provable proposition and then prove it:
     1) succ 2 3 [1;2;3;4]
     2) ~ succ 2 3 [1;2;3;4]
     *)
    succ 2 3 [1;2;3;4].
Proof.
  apply R2.
  apply R1.
Qed.


Theorem succ2:
    (* Only one of the following propositions is provable.
       Replace 'False' by the only provable proposition and then prove it:
     1) succ 2 3 []
     2) ~ succ 2 3 []
     *)
    ~ succ 2 3 [].
Proof.
  unfold not.
  intros.
  inversion H.
Qed.


Theorem succ3:
    (* Only one of the following propositions is provable.
       Replace 'False' by the only provable proposition and then prove it:
     1) succ 2 4 [1;2;3;4]
     2) ~ succ 2 4 [1;2;3;4]
     *)
    ~ succ 2 4 [1;2;3;4].
Proof.
  unfold not.
  intros.
  inversion H; 
  subst; 
  clear H.
  inversion H1;
  subst; 
  clear H1.
  inversion H0;
  subst; 
  clear H0.
  inversion H1;
  subst; 
  clear H1.
  inversion H0;
  subst; 
  clear.
Qed.


Theorem succ4:
  forall (X:Type) (x y : Type), succ x y [x;y].
Proof.
  intros.
  apply R1.
Qed.


Theorem ex3:
  forall (X:Type) (l1 l2:list X) (x y:X), succ x y (l1 ++ (x :: y :: l2)).
Proof.
  intros.
  induction l1.
  - simpl.
    constructor.
  - simpl.
    induction l1. 
      + simpl.
        apply R2.
        apply R1.
      + simpl.
        simpl in IHl1.
        apply R2.
        apply IHl1.
Qed.

Theorem ex4:
  forall (X:Type) (x y:X) (l:list X), succ x y l -> exists l1 l2, l1 ++ (x:: y:: l2) = l.
Proof.
  intros.
  induction l.
  - inversion H.
  - inversion H. subst. 
    +  exists [],l0.
       simpl. reflexivity.
    +  subst. apply IHl in H1. destruct H1 as (n1,(n2,n3)).
       subst. exists  (a::n1),(n2) . reflexivity.
Qed.



Student
Divya Thota
Autograder Score
101.0 / 100.0
Question 2
Deductions
0.0 / 0.0 pts
