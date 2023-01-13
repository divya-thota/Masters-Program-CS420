(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
From Turing Require Import Lang.
From Turing Require Import Util.
From Turing Require Import Regex.
Import Lang.Examples.
Import LangNotations.
Import ListNotations.
Import RegexNotations.
Open Scope lang_scope.
Open Scope char_scope.

(* ---------------------------------------------------------------------------*)




(**

Show that 'aba' is accepted the the following regular expression.

 *)
Theorem ex1:
  ["a"; "b"; "a"] \in (r_star "a" ;; ("b" || "c") ;; r_star "a").
Proof.
  apply accept_app with (s1:=["a";"b"]) (s2:=["a"]).
  apply accept_app with (s1:=["a"]) (s2:=["b"]).
    - apply accept_star_eq.
      constructor.
    - apply accept_union_l.
      constructor.
    - simpl.
      constructor.
    - apply accept_star_eq.
      constructor.
    - simpl.
      constructor.
Qed.
 

(**

Show that 'bb' is rejected by the following regular expression.

 *)
Theorem ex2:
  ~ (["b"; "b"] \in (r_star "a" ;; ("b" || "c") ;; r_star "a")).
Proof.
 unfold not;
 intros H. 
 inversion H; subst; clear H.
 destruct s1. 
  - inversion H3; clear H3.
    rewrite H1 in H5.
    -- inversion H5.
        subst.
        inversion H5.
    -- inversion H0; subst; clear H0. 
       inversion H5. 
  - inversion H2; repeat subst; clear H2.
    rewrite H7 in H5.
    inversion H1; subst; clear H1.
   -- inversion H4; subst; clear H4.
    * inversion H2; subst; clear H2. 
      inversion H3; subst; clear H3.
    ** inversion H5. 
    ** inversion H0; subst; clear H0. 
       inversion H5.
    * inversion H2; subst; clear H2. 
      inversion H5. 
   -- inversion H0; subst; clear H0. 
inversion H5.
Qed.


(**

Function size counts how many operators were used in a regular
expression. Show that (c ;; {})* can be written using a single
regular expression constructor.


 *)
Theorem ex3:
  exists r, size r = 1 /\ (r_star ( "c" ;; r_void ) <==> r).
Proof.

 exists r_nil.
 split.
 - firstorder.
 - rewrite r_app_r_void_rw. 
   apply r_star_void_rw.
Qed.

(**

Given that the following regular expression uses 530 constructors
(because size r_all = 514).
Show that you can find an equivalent regular expression that uses
at most 6 constructors.


 *)
Theorem ex4:
  exists r, size r <= 6 /\  ((r_star ( (r_all || r_star "c" ) ;; r_void) ;; r_star ("a" || "b")) ;; r_star r_nil;; "c" <==> r).
Proof.
Search r_void.
exists (r_star ("a" || "b") ;; "c").
 constructor.
 - reflexivity.
 - rewrite r_app_r_void_rw,
           r_star_void_rw, 
           r_star_nil_rw,
           r_app_l_nil_rw,
           r_app_r_nil_rw. 
reflexivity.
Qed.

(**

The following code implements a function that given a string
it returns a regular expression that only accepts that string.

    Fixpoint r_word' l :=
    match l with
    | nil => r_nil
    | x :: l => (r_char x) ;; r_word' l
    end.

Prove that function `r_word'` is correct.
Note that you must copy/paste the function to outside of the comment
and in your proof state: exists r_word'.

The proof must proceed by induction.


 *)
Fixpoint r_word' l :=
  match l with
  | nil => r_nil
  | x :: l => (r_char x) ;; r_word' l
end.


Theorem ex5:
  forall l, exists (r_word:list ascii -> regex), Accept (r_word l) == fun w => w = l.
Proof.
 exists r_word'.
 induction l;unfold Equiv; split; intros .
 - inversion H.
   -- apply nil_in.
 - simpl.
   rewrite r_nil_rw.
   apply H.
 - inversion H; subst; clear H.
   inversion H2; subst; clear H2. 
   induction IHl with (w:=s2).
   intuition.
   rewrite H1.
   reflexivity. 
 - rewrite H.
   apply accept_app with (s1:=[a]) (s2:=l).
   * constructor.
   * apply IHl.
     constructor.
   * constructor.
Qed.

(**

Show that there exists a regular expression with 5 constructs that
recognizes the following language. The idea is to find the smallest
regular expression that recognizes the language.


 *)
Theorem ex6:
  exists r, (Accept r == fun w => w = ["a"; "c"] \/ w = ["b"; "c"]) /\ size r = 5.
Proof.
 exists (("a" || "b");;"c").
 unfold Equiv. 
 repeat split; intros.
   * apply r_app_union_distr_l in H.
     inversion H; subst; clear H .
    ** constructor. 
       inversion H3; clear H3.
       inversion H1; clear H1.
       inversion H2; clear H2.
       subst.
       reflexivity.
    ** right.
       inversion H3; clear H3.
       inversion H1; clear H1.
       inversion H2; clear H2.
       subst.
       reflexivity.
   * inversion H.
    ** apply r_app_union_distr_l.
       unfold In.
       apply accept_union_l, accept_app with (s1:=["a"]) (s2:=["c"]).
      - apply accept_char.
      - apply accept_char.
      - rewrite H0.
        simpl.
        auto.
    ** apply r_app_union_distr_l.
       unfold In. 
       apply accept_union_r, accept_app with (s1:=["b"]) (s2:=["c"]).
      - apply accept_char. 
      - apply accept_char. 
      - rewrite H0. 
        auto.
 Qed.

Student
Divya Thota
Autograder Score
100.0 / 100.0
