(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)

Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
From Turing Require Import Lang.
From Turing Require Import Util.
Import LangNotations.
Import ListNotations.
Import Lang.Examples.
Open Scope lang_scope.
Open Scope char_scope.

(* ---------------------------------------------------------------------------*)




(**

Show that any word that is in L4 is either empty or starts with "a".

 *)
Theorem ex1:
  forall w, L4 w -> w = [] \/ exists w', w = "a" :: w'.
Proof. 
  intros.
  destruct H.
  destruct x.
  - Search (_>>_). 
    apply pow_pow_in_inv in H.
    simpl in H.
    left.
    rewrite H.
    easy.
  - apply pow_pow_in_inv in H.
    simpl in H.
    right.
    exists (pow1 "a" x ++ "b" :: pow1 "b" x).
    apply H.
Qed.

(**

Show that the following word is accepted by the given language.

 *)
Theorem ex2:
  In ["a"; "b"; "b"; "a"] ("a" >> "b" * >> "a").
Proof.
  Search (_>>_).
  apply app_assoc_in_1.
  Search (_>>_).
  apply app_l_char_in.
  Search (_>>_).
  apply app_in with (w1:=["b";"b"]) (w2:=["a"]).
  - Search (_>>_).
    apply pow_to_star with (n:=2) .
    Search (In _ (_^^ _)).
    apply pow_char_in.
  - Search (In _ (_) ).
    apply char_in.
  - easy.
Qed.


(**

Show that the following word is rejected by the given language.

 *)
Theorem ex3:
  ~ In ["b"; "b"] ("a" >> "b" * >> "a").
Proof.
  intros s.
  Search (_>>_).
  apply app_assoc_in_2 in s.
  Search (_>>_).
  apply app_l_char_in_inv with (c:="a") in s.
  destruct s. 
  destruct H. 
  easy.
Qed.

(**

Show that the following language is empty.

 *)
Theorem ex4:
  "0" * >> {} == {}.
Proof.
 apply app_r_void_rw.
Qed.

(**

Rearrange the following terms. Hint use the distribution and absorption laws.

 *)
Theorem ex5:
  ("0" U Nil) >> ( "1" * ) == ( "0" >> "1" * ) U ( "1" * ).
Proof. 
  unfold Equiv; intros.
  - rewrite <- app_union_distr_l.
    Search (Nil).
    rewrite app_l_nil_rw.
    reflexivity.
Qed.

(**

Show that the following langue only accepts two words.

 *)
Theorem ex6:
  ("0" >> "1" U "1" >> "0") == fun w => (w = ["0"; "1"] \/ w = ["1"; "0"]).
Proof. unfold Equiv.
  split; intros.
  - unfold Union, In, App in *.
    destruct H. destruct H as (x, (x0, H)). 
    left.
    -- destruct H. rewrite H. inversion H0. 
       unfold Char in *. rewrite H1. rewrite H2. reflexivity.
    -- right. destruct H as (x, (x0, (H, (H0, H1)))).
       unfold Char in *.
       rewrite H, H0, H1.
       reflexivity.
  - unfold In, Union, App in *. destruct H.
    -- left. exists ["0"], ["1"]. split.
       * rewrite H. reflexivity.  
       * split. 
          ** unfold Char; reflexivity. 
          ** unfold Char; reflexivity.
    -- unfold In, Union, App. right. exists ["1"], ["0"]. split.
       * rewrite H. reflexivity. 
       * split. 
         ** unfold Char; reflexivity. 
         ** unfold Char; reflexivity.
Qed.



Theorem ex7:
  "b" >> ("a" U "b" U Nil) * >> Nil == "b" >> ("b" U "a") *.
Proof.
    split;intros A.
   Search(_ >> _).
  - rewrite app_r_nil_rw in A.
    Search(_ U _). 
    rewrite union_sym_rw in A.
     Search(_ U _). 
    rewrite  star_union_nil_rw in A.
    Search(_ U _).
    rewrite  union_sym_rw in A.
    apply A.
   - rewrite app_r_nil_rw.
    rewrite union_sym_rw.
    rewrite star_union_nil_rw.
    rewrite union_sym_rw in A.
    apply A.
Qed.


Theorem ex8:
  (("b" >> ("a" U {}) ) U (Nil >> {} >> "c")* ) * == ("b" >> "a") *.
Proof.
  split;intros.
- rewrite union_r_void_rw in H.
  rewrite app_r_void_rw in H.
  rewrite app_l_void_rw in H.
  rewrite star_void_rw in H.
  rewrite union_sym_rw in H.
  rewrite star_union_nil_rw in H.
  apply H.
- rewrite union_r_void_rw.
  rewrite app_r_void_rw.
  rewrite app_l_void_rw.
  rewrite star_void_rw.
  rewrite union_sym_rw.
  rewrite star_union_nil_rw.
  apply H.
Qed.




Student
Divya Thota
Autograder Score
100.0 / 100.0
