(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)

Require Import Turing.Turing.

(* ---------------------------------------------------------------------------*)




(**

If the program returns true, then running
that program should return true.
Use `constructor` or `apply run_ret` to conclude.


 *)
Theorem ret1:
  Run (Ret true) true.
Proof.
  constructor.
Qed.

(**

If the program returns false, then running
that program should return false.


 *)
Theorem ret2:
  Run (Ret false) false.
Proof.
  constructor.
Qed.

(**

If your program returns true and the result of running it
is an unknown variable, that variable must be true.

Remember that Run was defined inductively, so we must use
inversion (invc) to get that fact.  


 *)

Ltac invc H := inversion H; subst; clear H. 
Theorem ret3:
  forall b,
Run (Ret true) b ->
b = true.
Proof.
  intros.
  invc H.
  reflexivity.
Qed.

(**

If you execute `Print Run.` you will note that
Run returns _exactly_ what is in the argument of Ret.
In this case because the two are different if you write

  constructor.
 
That will fail.
Instead, make sure you rewrite assumption H before you
apply the constructor.


 *)
Theorem ret4:
  forall f (x:nat),
f x = true ->
Run (Ret (f x)) true.
Proof.
  intros.
  invc H.
  constructor.
Qed.

(**

We can generalize the idea behind ret4 with the following lemma.

 *)
Theorem ret5:
  forall x y,
x = y ->
Run (Ret x) y.
Proof.
  intros.
  invc H.
  constructor.
Qed.

(**

Returning a value means that the program terminates.
Use `constructor` or the constructor theorem `halt_ret`
to conclude.


 *)
Theorem ret6:
  Halt (Ret true).
Proof.
  constructor.
Qed.

(**

Print Recognizes to revise its meaning.

To show that a program recognizes a language, you must
show that for any input that the program returns true,
that input must be in the language, and vice-versa.

Start with

  split.
  all: intros.

To prove each direction of the equivalence.
In the first case we have that

  H : Run (Ret true) true
  ______________________________________(1/1)
  True
You can always prove True with constructor.
The second branch was a previous exercise.

Try proving the reverse and try to understand why it fails:

  Goal
    Recognizes (fun i => Ret true) (fun i => False).
  Proof.
  Admitted.


 *)
Theorem ret7:
  Recognizes (fun i => Ret true) (fun i => True).
Proof.
  split.
  all: intros.
  all: constructor.
Qed.

(**

Proving that a program decides a language means showing two things:
  1. Show that the program _recognizes_ the language.
  2. Show that the program halts for any input.
    Make sure you unfold/Print definition `Decider` first.

You have proved both goals in a previous exercise.


 *)
Theorem ret8:
  Decides (fun i => Ret true) (fun i => True).
Proof.
  split.
  all:constructor.
  all:constructor.
Qed.

(**

We now have all of the ingredients to show that a language
is decidable.

Print Decidable to proceed to understand what you need to do next.

Conclude with `exists (fun i => Ret true).


 *)
Theorem ret9:
  Decidable (fun i => True).
Proof.
  exists(fun i => Ret true).
 constructor.
- apply ret7.
- apply decider_def.
  intros.
  apply ret6.
Qed.

(**

Now try to prove the same result but for the language
that rejects all inputs. What should the program be?


 *)
Theorem ret10:
  Decidable (fun i => False).
Proof.
  exists(fun i => Ret false).
 constructor.
- split.
  all: intros.
  invc H.
  invc H.
- apply decider_def.
  intros.
  constructor.
Qed.

(**

If a program returns a boolean, then it cannot loop.
A proof of this kind can be solved in one of two ways:

1. As usual, assume that Loop (Ret b) holds (unfold not),
    and then invert the assumption with invc.
2. Use a theorem: halt_to_not_loop 


 *)
Theorem ret11:
  forall b, ~ Loop (Ret b).
Proof.
  intros.
  apply halt_to_not_loop.
  constructor.
Qed.

(**

Sequencing lets us chain two programs together.
The program

  mlet x <- Ret true in Ret x

Executes the program `Ret true` and if that program
terminates, it assign its return value to variable `x`.
The continuation is `Ret x` which returns whatever is
stored in variable `x`.

To prove this goal use `apply run_seq with (b1:=true)`.
We set `b1` to `true` because the result of `Ret true` is
`true`.

The first goal is to prove that the first program returns
indeed `true`. The continuation, in this case returns the
opposite of whatever is in `x` (see Print negb).
Using the tactic `constructor` in either case should conclude
the proof.


 *)
Theorem seq1:
  Run (mlet x <- Ret true in Ret (negb x)) false.
Proof.
  apply run_seq with (b1:=true).
  constructor.
  constructor.
Qed.

(**

Now try to prove a more general result.
If p1 returns b1, and p2 returns b2,
then running p1 followed by p2 returns b2.
The proof is very similar to the previous exercise.


 *)
Theorem seq2:
  forall p1 p2 b1 b2,
Run p1 b1 ->
Run p2 b2 ->
Run (mlet x <- p1 in p2) b2.
Proof.
  intros.
  apply run_seq with (b1:=b1).
  all: assumption.
Qed.

(**

If you run p1 followed by p2 and that returns b2,
then for sure p2 returns p2. To prove this, just invert
the assumption (invc) to obtain how it was proved.


 *)
Theorem seq3:
  forall p1 p2 b2,
Run (mlet x <- p1 in p2) b2 ->
Run p2 b2.
Proof.
  intros.
  invc H.
  all: assumption.
Qed.

(**

If we run p1 followed by p2, and we know that
p1 terminates, then we must be able to prove that p2
is looping.

*)
 
Theorem seq4:
  forall p1 p2,
Loop (mlet x <- p1 in p2) ->
Halt p1 ->
Loop p2.
Proof.
  intros.
  invc H.
  apply halt_to_not_loop in H0.
    contradiction. 
    assumption.
Qed.


(**

If a program p1 recognizes L1,
then what is the language of the program that runs p1
and then returns false?
*)
 
Theorem seq5:
  forall p1 L1,
Recognizes p1 L1 ->
exists L2,
Recognizes (fun i => mlet b <- p1 i in Ret false) L2.
Proof.
  intros.
  unfold Recognizes in H.
  exists (fun i=> False).
  split.
  +intros. invc H0. inversion H5; subst; clear H5.
  +intros. invc H0.
Qed.

(**

If a program p1 recognizes L1,
then what is the language of the program that runs p1
and then returns true?
*)

Ltac hsqt:= apply halt_seq with (b:= true).
Ltac hsqf:= apply halt_seq with (b:= false).
Ltac hrt:= apply halt_ret.
Ltac rsct:= apply run_seq with (b1:= true).
Ltac rscf:= apply run_seq with (b1:= false).
Ltac rrt:= apply run_ret.
 
Theorem seq6:
  forall p1 L1,
Recognizes p1 L1 ->
exists L2,
Recognizes (fun i => mlet b <- p1 i in Ret true) L2.
Proof.
  intros.
        exists (fun i=> Halt (mlet b <- p1 i in Ret true) ).
        split.
        all:intros.
        { invc H0.
          destruct b1.
          1: hsqt.
          all: try assumption; try hrt.
          1: hsqf.
          all: try assumption; try hrt. }
        { invc H0.
          destruct b.
          1: rsct.
          all: try assumption; try rrt.
          1: rscf.
          all: try assumption; try rrt. }
Qed.

(**

Exercise 6.1 of the book.

If program p decides language L, then
program

  mlet b <- p i in Ret (negb b))

recognizes the complement of that language.
Start with `Print Recognizes`.
Then do `split` followed by `all: intros.`

The first goal is to show:

  H: Decides p L
  H0: Run (mlet b <- p i in Ret (negb b)) true
  ______________________________________(1/1)
  compl L i

Start with `unfold compl` so that we have a more convenient goal.
Next, we want to simplify `H0` until it cannot be simplified any
further. After using `invc` a few times we get the following proof
state:

  H : Decides p L
  H3 : Run (p i) b1
  H2 : negb b1 = true
  ______________________________________(1/1)
  ~ L i

At this point, the only goal we can simplify is `H2` since `b1`
is a boolean, we can conclude that `b1 = false` (do a case analysis
on b1, and invert H2). Our goal is now simpler:

  H : Decides p L
  H3 : Run (p i) false
  H2 : negb false = true
  ______________________________________(1/1)
  ~ L i

If we use the Search command we find a helpful theorem
that allows us to conclude: `decides_run_false_to_not_in`


The second part of the proof is to show:

  H : Decides p L
  H0 : compl L i
  ______________________________________(1/1)
  Run (mlet b <- p i in Ret (negb b)) true

Start by unfolding `compl`. By using `Search Decides`
we can find a helpful theorem `decides_not_in_to_run_false`
that we apply to `H0`. Use the constructor theorems of `Run`
to conclude.


*)
Theorem seq7:
  forall p L,
Decides p L ->
Recognizes (fun i =>
  mlet b <- p i in Ret (negb b)) (compl L).
Proof.
  intros.
        split.
        all:intros.
        { invc H0.
          unfold compl.
          intros N.
          Search Decides.
          apply decides_run_false_to_not_in with (L:= L) (i:= i) in H.
          1: contradiction.
          destruct b1.
          1: simpl in H5; invc H5.
          assumption. }
        { unfold compl in H0.
          Search Decides.
          apply decides_not_in_to_run_false with (L:= L) (i:= i) in H.
          1:rscf.
          1:assumption.
          1: simpl.
          1: apply ret1.
          1: assumption.
         }
Qed. 
(**

This theorem is very similar to the previous one.

In the first case invert your goals until you obtain:

  H4 : Run (p1 i) b1
  H3 : Run (p2 i) b0
  H7 : Run (Ret (b1 && b0)) true

Conclude it with a case analysis on b1 and b0 and
theorem recognizes_run_true_to_in.

In the second case use recognizes_in_to_run_true in
your assumptions.


 *)
Theorem seq8:
  forall p1 L1 p2 L2,
Recognizes p1 L1 ->
Recognizes p2 L2 ->
Recognizes (fun i =>
  mlet x <- p1 i in
  mlet y <- p2 i in
  Ret (x && y)
) (fun i => L1 i /\ L2 i).
Proof.
        intros.
        split.
        all:intros.
        1: split.
        { invc H1.
          invc H6.
          { destruct b1.
            { destruct b0.
              { apply recognizes_run_true_to_in with (p:= p1) (L:= L1) (i:=i) in H.
                { assumption. }
                { assumption. } }
              { apply recognizes_run_true_to_in with (p:= p1) (L:= L1) (i:=i) in H.
                { assumption. }
                { assumption. } } }
            { destruct b0.
              { apply recognizes_run_true_to_in with (p:= p1) (L:= L1) (i:=i) in H.
                { assumption. }
                { invc H7. } }
              { apply recognizes_run_true_to_in with (p:= p1) (L:= L1) (i:=i) in H.
                { assumption. }
                { invc H7. } } } } }
       { invc H1.
         invc H6.
         { destruct b1.
           { destruct b0.
             { apply recognizes_run_true_to_in with (p:= p2) (L:= L2) (i:=i) in H0.
               { assumption. }
               { assumption. } }
             { apply recognizes_run_true_to_in with (p:= p2) (L:= L2) (i:=i) in H0.
               { assumption. }
               { inversion H7. } } }
          { destruct b0.
             { apply recognizes_run_true_to_in with (p:= p2) (L:= L2) (i:=i) in H0.
               { assumption. }
               { assumption. } }
             { apply recognizes_run_true_to_in with (p:= p2) (L:= L2) (i:=i) in H0.
               { assumption. }
               { invc H7. } } } } }
       { destruct H1.
         { apply recognizes_in_to_run_true with (p:= p1) (L:= L1) (i:= i) in H.
           { apply recognizes_in_to_run_true with (p:= p2) (L:= L2) (i:= i) in H0.
             { inversion H.
               { inversion H0.
                 { rsct.
                   { rrt. }
                     { rsct.
                       { rrt. }
                       { rrt. } } }
                 { rsct.
                   { rrt. }
                   { subst. rewrite H5. rsct.
                     { assumption. }
                     { rrt. } } }
                 { rsct.
                   { rrt. }
                   { subst. rewrite H5. rsct.
                     { assumption. }
                     { rrt. } }} }
             { inversion H0.
               { rsct.
                 { rewrite H3. assumption. }
                 { rsct.
                   { rrt. }
                   { rrt. } } }
               { rsct.
                 { rewrite H3. assumption. }
                 { rsct. 
                   { rewrite H6. assumption. }
                   { rrt. } } }
               { rsct.
                 { rewrite H3. assumption. }
                 { rewrite H6. rsct. 
                   { assumption. }
                   { rrt. } } } }
             { inversion H0.
               { rsct.
                 { rewrite H3. assumption. }
                 { rsct.
                   { rrt. }
                   { rrt. } } }
               { rsct.
                 { rewrite H3. assumption. }
                 { rsct.
                   { rewrite H7. assumption. }
                   { rrt. } } }
               { rsct.
                 { rewrite H3. assumption. }
                 { rewrite H7. rsct. 
                   { assumption. }
                   { rrt. } } } } }
          { assumption. } }
          { assumption. } } }
Qed.

(**

Print Decidable.
Start by getting the program that decides L, by doing
a destruct of the assumption.

Remember that the program in exercise seq7 recognizes
compl L. Thus, write exists (fun i =>
  mlet b <- p i in Ret (negb b)). 

Now we need to show that our program decides the `compl L`.
Print `Decides` and realize that you need to prove 2 facts:
1. The program recognizes (compl L), solved by applying seq7.
2. Showing that our program is a decider.
To prove that a program is a decider, we must show that
for any input, the program halts. Unfold `Decider` and intros.
We now search for `Decides` and find a helpful theorem
`decides_to_halt`, that is if a program decides a language,
then the program halts for any parameter.

We now have the following proof to show:

  H: Halt (p i)
  ______________________________________(1/1)
  Halt (mlet b <- p i in Ret (negb b))

If we print `Halt` we note that the constructor `halt_seq`
is expecting the first assumption to be a `Run`, but we have
a `Halt`. We can convert a `Halt` into a `Run` with
`rewrite halt_rw in H`. We are then ready to use the
constructor `halt_seq`.


 *)
Theorem seq9:
  forall L,
Decidable L ->
Decidable (compl L).
Proof.
  intros.
  destruct H as (p, H).
  exists (fun i => mlet b <- p i in Ret (negb b)).
  split.
  -apply seq7.
    apply H.
  -unfold Decider. 
    intros.
    apply decides_to_halt with (i:=i) in H.
    rewrite halt_rw in H.
    destruct H.
    apply halt_seq with (b:=x).
  apply H.
  apply halt_ret.
Qed.
(**

If you do not remember how to get from
Decides to Recognizes, print the definition of Decides.
The proof follows very similarly to seq9.


 *)
Theorem seq10:
  forall L1 L2,
Decidable L1 ->
Decidable L2 ->
Decidable (fun i => L1 i /\ L2 i).
Proof.
        intros.
        Print Decidable.
        unfold Decidable in *.
        invc H; invc H0.
        exists (fun i => mlet x <- x i in mlet y <- x0 i in Ret (x && y)).
        Print Decides.
        split.
        1: apply seq8.
        1: invc H1.
        1: assumption.
        1: invc H.
        1: assumption.
        Print Decider.
        unfold Decider.
        intros.
        apply decides_to_halt with (i:=i) in H.
        apply decides_to_halt with (i:=i) in H1.
        rewrite halt_rw in H, H1.
        inversion H; inversion H1.
        destruct x1; destruct x2.
        1: apply halt_seq with (b:= true).
        1: assumption.
        1: apply halt_seq with (b:= true).
        1,2: try assumption; try hrt.
        1: apply halt_seq with (b:= false).
        1: assumption.
        1: apply halt_seq with (b:= true).
        1,2: try assumption; try hrt.
        1: apply halt_seq with (b:= true).
        1: assumption.
        1: apply halt_seq with (b:= false).
        1,2: try assumption; try hrt.
        1: apply halt_seq with (b:= false).
        1: assumption.
        1: apply halt_seq with (b:= false).
        1,2: try assumption; try hrt.
Qed.
