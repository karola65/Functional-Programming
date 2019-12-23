(* term-project.v *)
(* YSC3236 2019-2020, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 07 Nov 2019 *)

(* ********** *)

(*
   name:KAROLINA BARGIEL
   student ID number:A0209985L
   e-mail address: e0454436@edu.nus.sg
*)

(* ********** *)

(*

The primary goal of this term project is to prove the following theorem:

  Theorem the_commutative_diagram :
    forall sp : source_program,
      interpret sp = run (compile sp).

for

* a source language of arithmetic expressions:

    Inductive arithmetic_expression : Type :=
    | Literal : nat -> arithmetic_expression
    | Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
    | Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.
    
    Inductive source_program : Type :=
    | Source_program : arithmetic_expression -> source_program.

* a target language of byte-code instructions:

    Inductive byte_code_instruction : Type :=
    | PUSH : nat -> byte_code_instruction
    | ADD : byte_code_instruction
    | SUB : byte_code_instruction.
    
    Inductive target_program : Type :=
    | Target_program : list byte_code_instruction -> target_program.

* a semantics of expressible values:

    Inductive expressible_value : Type :=
    | Expressible_nat : nat -> expressible_value
    | Expressible_msg : string -> expressible_value.

* a source interpreter

    interpret : source_program -> expressible_value

* a compiler

    compile : source_program -> target_program

* a target interpreter

    run : target_program -> expressible_value

* decode_execute
    

The source for errors is subtraction,
since subtracting two natural numbers does not always yield a natural number:
for example, 3 - 2 is defined but not 2 - 3.

You are expected, at the very least:

* to prove that the specification of the interpreter specifies at most one function

* to implement a source interpreter
  and to verify that it satisfies its specification

* to implement a target interpreter (i.e., a virtual machine)
  and to verify that it satisfies its specification

* to implement a compiler
  and to verify that it satisfies its specification

* to prove that the diagram commutes, i.e., to show that
  interpreting any given expression
  gives the same result as
  compiling this expression and then running the resulting compiled program

Beyond this absolute minimum, in decreasing importance, it would be good:

* to write an accumulator-based compiler and to prove that it satisfies the specification,

* to investigate byte-code verification,

* to investigate decompilation,

* to write a continuation-based interpreter and to prove that it satisfies the specification, and

* if there is any time left, to prove that each of the specifications specifies a unique function.

Also, feel free:

* to expand the source language and the target language with multiplication, quotient, and modulo, and/or

* to implement right-to-left language processors and to verify that the corresponding diagram commutes,
  as in the term project of Intro to CS.

*)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.
  
Require Import Arith Bool List String Ascii.

(* caution: only use natural numbers up to 5000 *)
Definition string_of_nat (q0 : nat) : string :=
  let s0 := String (ascii_of_nat (48 + (q0 mod 10))) EmptyString
  in if q0 <? 10
     then s0
     else let q1 := q0 / 10
          in let s1 := String (ascii_of_nat (48 + (q1 mod 10))) s0
             in if q1 <? 10
                then s1
                else let q2 := q1 / 10
                     in let s2 := String (ascii_of_nat (48 + (q2 mod 10))) s1
                        in if q2 <? 10
                           then s2
                           else let q3 := q2 / 10
                                in let s2 := String (ascii_of_nat (48 + (q3 mod 10))) s2
                        in if q3 <? 10
                           then s2
                           else "00000".

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Arithmetic expressions: *)

Inductive arithmetic_expression : Type :=
| Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Multiply : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Divide: arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Source programs: *)

Inductive source_program : Type :=
| Source_program : arithmetic_expression -> source_program.

(* ********** *)

(* Semantics: *)

Inductive expressible_value : Type :=
| Expressible_nat : nat -> expressible_value
| Expressible_msg : string -> expressible_value.

(* ********** *)

Definition specification_of_evaluate (evaluate : arithmetic_expression -> expressible_value) :=
  (forall n : nat,
     evaluate (Literal n) = Expressible_nat n)
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       evaluate (Plus ae1 ae2) = Expressible_nat (n1 + n2)))
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = true ->
       evaluate (Minus ae1 ae2) = Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = false ->
       evaluate (Minus ae1 ae2) = Expressible_nat (n1 - n2)))
  /\
    (((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Multiply ae1 ae2) = Expressible_msg s1))
  /\
     (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Multiply ae1 ae2) = Expressible_msg s2)
  /\
  (forall (ae1 ae2 : arithmetic_expression)
          (n1 n2 : nat),
      evaluate ae1 = Expressible_nat n1 ->
      evaluate ae2 = Expressible_nat n2 ->
      evaluate (Multiply ae1 ae2) = Expressible_nat (n1 * n2)))
  /\
    (((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Divide ae1 ae2) = Expressible_msg s1))
  /\
     (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Divide ae1 ae2) = Expressible_msg s2)
  /\
   (forall (ae1 ae2 : arithmetic_expression)
          (n1 n2 : nat),
      evaluate ae1 = Expressible_nat n1 ->
      evaluate ae2 = Expressible_nat n2 ->
      n2 =? 0 = true ->
      evaluate (Divide ae1 ae2) = Expressible_msg (String.append "division by 0 on" (string_of_nat (n1))))
  /\
  (forall (ae1 ae2 : arithmetic_expression)
          (n1 n2 : nat),
      evaluate ae1 = Expressible_nat n1 ->
      evaluate ae2 = Expressible_nat n2 ->
      n2 =? 0 = false ->
      evaluate (Divide ae1 ae2) = Expressible_nat (n1/n2))).

Definition specification_of_interpret (interpret : source_program -> expressible_value) :=
  forall evaluate : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate ->
    forall ae : arithmetic_expression,
      interpret (Source_program ae) = evaluate ae.

(* Task 1: 
   a. prove that each of the definitions above specifies at most one function;
   b. implement these two functions; and
   c. verify that each of your functions satisfies its specification.
 *)

(* a *)

Proposition there_is_at_most_one_specification_of_evaluate :
  forall f g,
    specification_of_evaluate f ->
    specification_of_evaluate g ->
    forall e,
      f e = g e.
Proof.
  intros f g.
  intros S_evaluate_f S_evaluate_g.  
  (*
  destruct S_evaluate_f as [H_f_lit [H_f_plus [H_f_minus [H_f_mul H_f_div]]]].
  destruct S_evaluate_g as [H_g_lit [H_g_plus [H_g_minus [H_g_mul H_g_div]]]].*)
  intro e.
  induction e as [n| ae1 IHae1 ae2 IHae2| ae1 IHae1 ae2 IHae2| ae1 IHae1 ae2 IHae2| ae1 IHae1 ae2 IHae2].

  - unfold specification_of_evaluate in S_evaluate_f.
    destruct S_evaluate_f as [H_f_lit _].
    destruct S_evaluate_g as [H_g_lit _].
    rewrite -> (H_f_lit).
    rewrite -> (H_g_lit).
    reflexivity.

  - (*destruct S_evaluate_f as [_ [[H_f_plus_msg_nat [H_f_plus_nat_msg H_f_plus_nat_nat]]_]_].
    destruct S_evaluate_g as [_ [[H_g_plus_msg_nat [H_g_plus_nat_msg H_g_plus_nat_nat]]_]_].*)
    destruct (f ae1) as [nf1|sf1] eqn: H_f_ae1;
      destruct (g ae1) as [ng1|sg1] eqn: H_g_ae1;
      destruct (f ae2) as [nf2|sf2] eqn: H_f_ae2;
      destruct (g ae2) as [ng2|sg2] eqn: H_g_ae2.

    + destruct S_evaluate_f as [_ [[_ [_ H_f_plus_nat_nat]]_]_].
      destruct S_evaluate_g as [_ [[_ [_ H_g_plus_nat_nat]]_]_].
      rewrite -> (H_f_plus_nat_nat ae1 ae2 nf1 nf2 H_f_ae1 H_f_ae2).
      rewrite -> (H_g_plus_nat_nat ae1 ae2 ng1 ng2 H_g_ae1 H_g_ae2).
      injection IHae1 as IHae1.
      rewrite -> IHae1.
      injection IHae2 as IHae2.
      rewrite -> IHae2.
      reflexivity.

    + discriminate IHae2.

    + discriminate IHae2.

    + destruct S_evaluate_f as [_ [[_ [H_f_plus_nat_msg _]]_]_].
      destruct S_evaluate_g as [_ [[_ [H_g_plus_nat_msg _]]_]_].
      rewrite -> (H_f_plus_nat_msg ae1 ae2 nf1 sf2 H_f_ae1 H_f_ae2).
      rewrite -> (H_g_plus_nat_msg ae1 ae2 ng1 sg2 H_g_ae1 H_g_ae2).
      injection IHae2 as IHae2.
      rewrite -> IHae2.
      reflexivity.

    + discriminate IHae1.

    + discriminate IHae2.

    + discriminate IHae2.

    + discriminate IHae1.

    + discriminate IHae1.

    + discriminate IHae1.

    + discriminate IHae1.

    + discriminate IHae1.

    + destruct S_evaluate_f as [_ [[H_f_plus_msg_nat [_ _]]_]_].
      destruct S_evaluate_g as [_ [[H_g_plus_msg_nat [_ _]]_]_].
      rewrite -> (H_f_plus_msg_nat ae1 ae2 sf1 H_f_ae1).
      rewrite -> (H_g_plus_msg_nat ae1 ae2 sg1 H_g_ae1).
      injection IHae1 as IHae1.
      rewrite -> IHae1.
      reflexivity.

    + discriminate IHae2.

    + discriminate IHae2.

    + destruct S_evaluate_f as [_ [[H_f_plus_msg_nat [_ _]]_]_].
      destruct S_evaluate_g as [_ [[H_g_plus_msg_nat [_ _]]_]_].
      rewrite -> (H_f_plus_msg_nat ae1 ae2 sf1 H_f_ae1).
      rewrite -> (H_g_plus_msg_nat ae1 ae2 sg1 H_g_ae1).
      injection IHae1 as IHae1.
      rewrite -> IHae1.
      reflexivity.

  - destruct (f ae1) as [nf1|sf1] eqn: H_f_ae1;
      destruct (g ae1) as [ng1|sg1] eqn: H_g_ae1;
      destruct (f ae2) as [nf2|sf2] eqn: H_f_ae2;
      destruct (g ae2) as [ng2|sg2] eqn: H_g_ae2.

    + (* destruct S_evaluate_f as [_ [_ [[H_f_minus_msg_nat [H_f_minus_nat_msg [H_f_minus_nat_nat_neg H_f_minus_nat_nat_pos]]][ _ _]]]]. *)
      destruct (nf1 <? nf2) eqn: H_nf1_nf2;
      destruct (ng1 <? ng2) eqn: H_ng1_ng2.

      -- destruct S_evaluate_f as [_ [_ [[_ [_ [H_f_minus_nat_nat_neg _]]][ _ _]]]].
         destruct S_evaluate_g as [_ [_ [[_ [_ [H_g_minus_nat_nat_neg _]]][ _ _]]]].   
      rewrite -> (H_f_minus_nat_nat_neg ae1 ae2 nf1 nf2 H_f_ae1 H_f_ae2 H_nf1_nf2).
      rewrite -> (H_g_minus_nat_nat_neg ae1 ae2 ng1 ng2 H_g_ae1 H_g_ae2 H_ng1_ng2).
      injection IHae1 as IHae1.
      injection IHae2 as IHae2.
      rewrite -> (IHae1).
      rewrite -> (IHae2).
      reflexivity.
      
      -- injection IHae1 as IHae1.
         injection IHae2 as IHae2.
         rewrite -> IHae1 in H_nf1_nf2.
         rewrite -> IHae2 in H_nf1_nf2.
         rewrite -> H_nf1_nf2 in H_ng1_ng2.
         discriminate H_ng1_ng2.
     

      -- injection IHae1 as IHae1.
         injection IHae2 as IHae2.
         rewrite -> IHae1 in H_nf1_nf2.
         rewrite -> IHae2 in H_nf1_nf2.
         rewrite -> H_nf1_nf2 in H_ng1_ng2.
         discriminate H_ng1_ng2.

      -- destruct S_evaluate_f as [_ [_ [[_ [_ [_ H_f_minus_nat_nat_pos]]][ _ _]]]].
         destruct S_evaluate_g as [_ [_ [[_ [_ [_ H_g_minus_nat_nat_pos]]][ _ _]]]].   
      rewrite -> (H_f_minus_nat_nat_pos ae1 ae2 nf1 nf2 H_f_ae1 H_f_ae2 H_nf1_nf2).
      rewrite -> (H_g_minus_nat_nat_pos ae1 ae2 ng1 ng2 H_g_ae1 H_g_ae2 H_ng1_ng2).
      injection IHae1 as IHae1.
      injection IHae2 as IHae2.
      rewrite -> (IHae1).
      rewrite -> (IHae2).
      reflexivity.

    + discriminate IHae2.

    + discriminate IHae2.

    + destruct S_evaluate_f as  [_ [_ [[_ [H_f_minus_nat_msg [_ _]]][ _ _]]]].
      destruct S_evaluate_g as  [_ [_ [[_ [H_g_minus_nat_msg [_ _]]][ _ _]]]].
      rewrite -> (H_f_minus_nat_msg ae1 ae2 nf1 sf2 H_f_ae1 H_f_ae2).
      rewrite -> (H_g_minus_nat_msg ae1 ae2 ng1 sg2 H_g_ae1 H_g_ae2).
      injection IHae2 as IHae2.
      rewrite -> (IHae2).
      reflexivity.

    + discriminate IHae1.
      
    + discriminate IHae2.
      
    + discriminate IHae1.

    + discriminate IHae1.

    + discriminate IHae1.

    + discriminate IHae1.

    + discriminate IHae1.

    + discriminate IHae1.

    + destruct S_evaluate_f as [_ [_ [[H_f_minus_msg_nat [_ [_ _]]][ _ _]]]].
      destruct S_evaluate_g as [_ [_ [[H_g_minus_msg_nat [_ [_ _]]][ _ _]]]].
      rewrite -> (H_f_minus_msg_nat ae1 ae2 sf1 H_f_ae1).
      rewrite -> (H_g_minus_msg_nat ae1 ae2 sg1 H_g_ae1).
      injection IHae1 as IHae1.
      rewrite -> (IHae1).
      reflexivity.

    + discriminate IHae2.

    + discriminate IHae2.

    + destruct S_evaluate_f as [_ [_ [[H_f_minus_msg_nat [_ [_ _]]][ _ _]]]].
      destruct S_evaluate_g as [_ [_ [[H_g_minus_msg_nat [_ [_ _]]][ _ _]]]].
      rewrite -> (H_f_minus_msg_nat ae1 ae2 sf1 H_f_ae1).
      rewrite -> (H_g_minus_msg_nat ae1 ae2 sg1 H_g_ae1).
      injection IHae1 as IHae1.
      rewrite -> (IHae1).
      reflexivity.
 

  - destruct (f ae1) as [nf1|sf1] eqn: H_f_ae1;
      destruct (g ae1) as [ng1|sg1] eqn: H_g_ae1;
      destruct (f ae2) as [nf2|sf2] eqn: H_f_ae2;
      destruct (g ae2) as [ng2|sg2] eqn: H_g_ae2.

    + (* destruct S_evaluate_f as [_ [_ [_ [[H_f_mul_msg_nat [H_f_mul_nat_msg H_f_mul_nat_nat]] _]]]].
      destruct S_evaluate_g as [_ [_ [_ [[H_g_mul_msg_nat [H_g_mul_nat_msg H_g_mul_nat_nat]] _]]]].*)
      destruct S_evaluate_f as [_ [_ [_ [[_ [_ H_f_mul_nat_nat]] _]]]].
      destruct S_evaluate_g as [_ [_ [_ [[_ [_ H_g_mul_nat_nat]] _]]]].
      rewrite -> (H_f_mul_nat_nat ae1 ae2 nf1 nf2 H_f_ae1 H_f_ae2).
      rewrite -> (H_g_mul_nat_nat ae1 ae2 ng1 ng2 H_g_ae1 H_g_ae2).
      injection IHae1 as IHae1.
      rewrite -> IHae1.
      injection IHae2 as IHae2.
      rewrite -> IHae2.
      reflexivity.

    + discriminate IHae2.

    + discriminate IHae2.

    + destruct S_evaluate_f as [_ [_ [_ [[_ [H_f_mul_nat_msg _]] _]]]].
      destruct S_evaluate_g as [_ [_ [_ [[_ [H_g_mul_nat_msg _]] _]]]].
      rewrite -> (H_f_mul_nat_msg ae1 ae2 nf1 sf2 H_f_ae1 H_f_ae2).
      rewrite -> (H_g_mul_nat_msg ae1 ae2 ng1 sg2 H_g_ae1 H_g_ae2).
      injection IHae2 as IHae2.
      rewrite -> IHae2.
      reflexivity.

    + discriminate IHae1.

    + discriminate IHae2.

    + discriminate IHae2.

    + discriminate IHae1.

    + discriminate IHae1.

    + discriminate IHae1.

    + discriminate IHae1.

    + discriminate IHae1.

    + destruct S_evaluate_f as [_ [_ [_ [[H_f_mul_msg_nat [_ _]] _]]]].
      destruct S_evaluate_g as [_ [_ [_ [[H_g_mul_msg_nat [_ _]] _]]]].
      rewrite -> (H_f_mul_msg_nat ae1 ae2 sf1 H_f_ae1).
      rewrite -> (H_g_mul_msg_nat ae1 ae2 sg1 H_g_ae1).
      injection IHae1 as IHae1.
      rewrite -> IHae1.
      reflexivity.

    + discriminate IHae2.

    + discriminate IHae2.

    + destruct S_evaluate_f as [_ [_ [_ [[H_f_mul_msg_nat [_ _]] _]]]].
      destruct S_evaluate_g as [_ [_ [_ [[H_g_mul_msg_nat [_ _]] _]]]].
      rewrite -> (H_f_mul_msg_nat ae1 ae2 sf1 H_f_ae1).
      rewrite -> (H_g_mul_msg_nat ae1 ae2 sg1 H_g_ae1).
      injection IHae1 as IHae1.
      rewrite -> IHae1.
      reflexivity.

  -  destruct (f ae1) as [nf1|sf1] eqn: H_f_ae1;
       destruct (g ae1) as [ng1|sg1] eqn: H_g_ae1;
       destruct (f ae2) as [nf2|sf2] eqn: H_f_ae2;
       destruct (g ae2) as [ng2|sg2] eqn: H_g_ae2.

    + (*destruct S_evaluate_f as [_ [ _ [ _ [_ [H_f_div_msg_nat [ H_f_div_nat_msg [ H_f_div_nat_nat_O H_f_div_nat_nat]]]]]]c.*)
      destruct (nf2 =? 0) eqn: H_nf1_nf2;
        destruct (ng2 =? 0) eqn: H_ng1_ng2.

      -- destruct S_evaluate_f as [_ [ _ [ _ [_ [_ [ _ [ H_f_div_nat_nat_O  _]]]]]]].
         destruct S_evaluate_g as [_ [ _ [ _ [_ [_ [ _ [ H_g_div_nat_nat_O  _]]]]]]].
         rewrite -> (H_f_div_nat_nat_O ae1 ae2 nf1 nf2 H_f_ae1 H_f_ae2 H_nf1_nf2).
         rewrite -> (H_g_div_nat_nat_O ae1 ae2 ng1 ng2 H_g_ae1 H_g_ae2 H_ng1_ng2).
         injection IHae1 as IHae1.
         rewrite -> (IHae1).
         reflexivity.

      -- injection IHae2 as IHae2.
         rewrite -> IHae2 in H_nf1_nf2.
         rewrite -> H_nf1_nf2 in H_ng1_ng2.
         discriminate H_ng1_ng2.

      -- injection IHae2 as IHae2.
         rewrite -> IHae2 in H_nf1_nf2.
         rewrite -> H_nf1_nf2 in H_ng1_ng2.
         discriminate H_ng1_ng2.

      -- destruct S_evaluate_f as [_ [ _ [ _ [_ [_ [ _ [ _  H_f_div_nat_nat ]]]]]]].
         destruct S_evaluate_g as [_ [ _ [ _ [_ [_ [ _ [ _  H_g_div_nat_nat ]]]]]]].
         rewrite -> (H_f_div_nat_nat ae1 ae2 nf1 nf2 H_f_ae1 H_f_ae2 H_nf1_nf2).
         rewrite -> (H_g_div_nat_nat ae1 ae2 ng1 ng2 H_g_ae1 H_g_ae2 H_ng1_ng2).
         injection IHae1 as IHae1.
         injection IHae2 as IHae2.
         rewrite -> (IHae1).
         rewrite -> (IHae2).
         reflexivity.

    + discriminate IHae2.

    + discriminate IHae2.

    + destruct S_evaluate_f as [_ [ _ [ _ [_ [_ [ H_f_div_nat_msg [ _ _]]]]]]].
      destruct S_evaluate_g as [_ [ _ [ _ [_ [_ [ H_g_div_nat_msg [ _ _]]]]]]].
      rewrite -> (H_f_div_nat_msg ae1 ae2 nf1 sf2 H_f_ae1 H_f_ae2 ).
      rewrite -> (H_g_div_nat_msg ae1 ae2 ng1 sg2 H_g_ae1 H_g_ae2 ).
      injection IHae2 as IHae2.
      rewrite -> (IHae2).
      reflexivity.

    + discriminate IHae1.

    + discriminate IHae1.

    + discriminate IHae2.

    + discriminate IHae1.

    + discriminate IHae1.

    + discriminate IHae2.

    + discriminate IHae2.

    + discriminate IHae1.

    + destruct S_evaluate_f as [_ [ _ [ _ [_ [H_f_div_msg_nat [ _ [ _ _]]]]]]].
      destruct S_evaluate_g as [_ [ _ [ _ [_ [H_g_div_msg_nat [ _ [ _ _]]]]]]].
      rewrite -> (H_f_div_msg_nat ae1 ae2 sf1 H_f_ae1 ).
      rewrite -> (H_g_div_msg_nat ae1 ae2 sg1 H_g_ae1 ).
      injection IHae1 as IHae1.
      rewrite -> (IHae1).
      reflexivity.

    + discriminate IHae2.

    + discriminate IHae2.

    + destruct S_evaluate_f as [_ [ _ [ _ [_ [H_f_div_msg_nat [ _ [ _ _]]]]]]].
      destruct S_evaluate_g as [_ [ _ [ _ [_ [H_g_div_msg_nat [ _ [ _ _]]]]]]].
      rewrite -> (H_f_div_msg_nat ae1 ae2 sf1 H_f_ae1 ).
      rewrite -> (H_g_div_msg_nat ae1 ae2 sg1 H_g_ae1 ).
      injection IHae1 as IHae1.
      rewrite -> (IHae1).
      reflexivity.
Qed.
(* 
induction over 5 different operators and each includes two different arithmetic expressions
included proof by case within each opeartor
within each case arithmetic expressions were destructed into natural number and string
in divide and minus, we also enumerated cases where errors occur (e.g. is n2 zero or not?)
ubsmade use of injection to reduce from Expression bla to bla
In error cases in minus and divide, we had to inject into the hypothesis, and then substitute
into condition and only then can we discriminate because the contradiction becomes obvious.
*)

 
Fixpoint evaluate (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
    Expressible_nat n
  | Plus ae1 ae2 =>
    match evaluate ae1 with
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end
  | Minus ae1 ae2 =>
    match evaluate ae1 with
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_nat n2 =>
        match n1 <? n2 with
        | true =>
          Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
        | false =>
          Expressible_nat (n1 - n2)
        end
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end
  | Multiply ae1 ae2 =>
    match evaluate ae1 with
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 * n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end
  | Divide ae1 ae2 =>
    match evaluate ae1 with
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_nat n2 =>
        match n2 =? 0 with
        | true =>
          Expressible_msg (String.append "division by 0 on" (string_of_nat (n1)))
        | false =>
          Expressible_nat (n1/n2)
        end
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end
  end.

Compute(evaluate (Literal 1)).
Compute(evaluate (Divide (Literal 1) (Literal 0) )).

Lemma fold_unfold_evaluate_literal:
  forall(n : nat),
    evaluate (Literal n) =
    Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_plus:
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Plus ae1 ae2) =
    match evaluate ae1 with
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 + n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_minus:
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Minus  ae1 ae2) =
      match evaluate ae1 with
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_nat n2 =>
        match n1 <? n2 with
        | true =>
          Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
        | false =>
          Expressible_nat (n1 - n2)
        end
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
      end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_multiply:
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Multiply  ae1 ae2) =
    match evaluate ae1 with
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_nat n2 =>
        Expressible_nat (n1 * n2)
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_divide:
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Divide  ae1 ae2) =
    match evaluate ae1 with
    | Expressible_nat n1 =>
      match evaluate ae2 with
      | Expressible_nat n2 =>
        match n2 =? 0 with
        | true =>
          Expressible_msg (String.append "division by 0 on" (string_of_nat (n1)))
        | false =>
          Expressible_nat (n1/n2)
        end
      | Expressible_msg s2 =>
        Expressible_msg s2
      end
    | Expressible_msg s1 =>
      Expressible_msg s1
    end.
Proof.
  fold_unfold_tactic evaluate.
Qed.
    
  

      
Theorem evaluate_satisfies_its_specification:
  specification_of_evaluate evaluate.
Proof.
  unfold specification_of_evaluate.
  split.
  - intro n.
    rewrite -> fold_unfold_evaluate_literal.
    reflexivity.

  - split.

    --split.

    +  intros ae1 ae2 s1.
       intro H.
       rewrite -> (fold_unfold_evaluate_plus ae1 ae2).
       rewrite -> H.
       reflexivity.

    + split.

      ++ intros ae1 ae2 n1 s2.
         intro H_1.
         intro H_2.
         rewrite -> fold_unfold_evaluate_plus.
         rewrite -> H_1.
         rewrite -> H_2.
         reflexivity.

      ++ intros ae1 ae2 n1 s2.
         intro H_1.
         intro H_2.
         rewrite -> fold_unfold_evaluate_plus.
         rewrite -> H_1.
         rewrite -> H_2.
         reflexivity.
         
      -- split.

    +  split.

       ++ intros ae1 ae2 s1.
          intro H.
          rewrite -> (fold_unfold_evaluate_minus ae1 ae2).
          rewrite -> H.
          reflexivity.
          


       ++ split.

          +++  intros ae1 ae2 n1 s2.
               intro H_1.
               intro H_2.
               rewrite -> fold_unfold_evaluate_minus.
               rewrite -> H_1.
               rewrite -> H_2.
               reflexivity.
         
          +++ split.

              ++++ intros ae1 ae2 n1 s2.
                   intro H_1.
                   intro H_2.
                   intro H_3.
                   rewrite -> fold_unfold_evaluate_minus.
                   rewrite -> H_1.
                   rewrite -> H_2.
                   rewrite -> H_3.
                   reflexivity.
                   
              ++++ intros ae1 ae2 n1 s2.
                   intro H_1.
                   intro H_2.
                   intro H_3.
                   rewrite -> fold_unfold_evaluate_minus.
                   rewrite -> H_1.
                   rewrite -> H_2.
                   rewrite -> H_3.
                   reflexivity.


    + split.

      ++ split.

         +++ intros ae1 ae2 s1.
             intro H.
             rewrite -> (fold_unfold_evaluate_multiply ae1 ae2).
             rewrite -> H.
             reflexivity.

         +++ split.

             ++++ intros ae1 ae2 n1 s2.
                  intro H_1.
                  intro H_2.
                  rewrite -> fold_unfold_evaluate_multiply.
                  rewrite -> H_1.
                  rewrite -> H_2.
                  reflexivity.

             ++++ intros ae1 ae2 n1 s2.
                  intro H_1.
                  intro H_2.
                  rewrite -> fold_unfold_evaluate_multiply.
                  rewrite -> H_1.
                  rewrite -> H_2.
                  reflexivity.
                  
      ++ split.

         +++  intros ae1 ae2 s1.
              intro H_1.
              rewrite -> fold_unfold_evaluate_divide.
              rewrite -> H_1.
              reflexivity.

         +++ split.

             ++++ intros ae1 ae2 n1 s2.
                  intro H_1.
                  intro H_2.
                  rewrite -> fold_unfold_evaluate_divide.
                  rewrite -> H_1.
                  rewrite -> H_2.
                  reflexivity.

             ++++ split.

                  +++++  intros ae1 ae2 n1 n2.
                         intro H_1. 
                         intro H_2.
                         intro H_3.
                         rewrite -> fold_unfold_evaluate_divide.
                         rewrite -> H_1.
                         rewrite -> H_2.
                         rewrite -> H_3.
                         reflexivity.

                  +++++ intros ae1 ae2 n1 n2.
                        intro H_1. 
                        intro H_2.
                        intro H_3.
                        rewrite -> fold_unfold_evaluate_divide.
                        rewrite -> H_1.
                        rewrite -> H_2.
                        rewrite -> H_3.
                        reflexivity.
Qed.
      
  
                             
      
Proposition there_is_at_most_one_specification_of_interpret :
  forall f g,
    specification_of_interpret f ->
    specification_of_interpret g ->
    forall sp : source_program,
      f sp = g sp .
Proof.
  intros f g.
  unfold specification_of_interpret.
  intros S_f S_g [ae].
  Check (S_f evaluate evaluate_satisfies_its_specification ae).
  rewrite -> (S_f evaluate evaluate_satisfies_its_specification ae).
  rewrite -> (S_g evaluate evaluate_satisfies_its_specification ae).
  reflexivity.
Qed.
     

   

Definition interpret (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae =>
    evaluate ae
  end.
  

Theorem interpret_satisfies_the_specification_of_interpret :
  specification_of_interpret interpret.
Proof.
  unfold specification_of_interpret.
  intros evaluate1 S_evaluate1 ae.
  Check (there_is_at_most_one_specification_of_evaluate evaluate1 evaluate S_evaluate1 evaluate_satisfies_its_specification ae).
  rewrite -> (there_is_at_most_one_specification_of_evaluate evaluate1 evaluate S_evaluate1 evaluate_satisfies_its_specification ae).
  unfold interpret.
  reflexivity.
Qed.

(*
in interpret_satisfies_the_specification_of_interpret we used the tacktic ti subsitute evaluate1 with avualte, because we know that evaluate meets the specification of evaluate.

additionaly in there_is_at_most_one_specification_of_interpret we used the evaluate_satisfies_its_specification

in evaluate_satisfies_its_specification we used proof by case where we split the goal until we reach single possibilty. we also used fold unfold lemmas there. on top of that when we had multiply infuction we intriduced hypothesis name H1 H2 etc to put whatever is on the left side on the induction to our assumtion. then by rewriting this hypothesis we lket to reflexivity.


implemented fold unfold lemma to the recursive defintion of evaluate - one per each operation. 


*)

(* ********** *)

(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
| PUSH : nat -> byte_code_instruction
| ADD : byte_code_instruction
| SUB : byte_code_instruction
| MUL : byte_code_instruction
| DIV : byte_code_instruction.

(* Target programs: *)

Inductive target_program : Type :=
| Target_program : list byte_code_instruction -> target_program.

(* Data stack: *)

Definition data_stack := list nat.

(* ********** *)

Inductive result_of_decoding_and_execution : Type :=
| OK : data_stack -> result_of_decoding_and_execution
| KO : string -> result_of_decoding_and_execution.

Definition specification_of_decode_execute (decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  (forall (n : nat)
          (ds : data_stack),
     decode_execute (PUSH n) ds = OK (n :: ds))
  /\
  ((decode_execute ADD nil = KO "ADD: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute ADD (n2 :: nil) = KO "ADD: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       decode_execute ADD (n2 :: n1 :: ds) = OK ((n1 + n2) :: ds)))
  /\
  ((decode_execute SUB nil = KO "SUB: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute SUB (n2 :: nil) = KO "SUB: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       n1 <? n2 = true ->
       decode_execute SUB (n2 :: n1 :: ds) = KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       n1 <? n2 = false ->
       decode_execute SUB (n2 :: n1 :: ds) = OK ((n1 - n2) :: ds)))
  /\
  ((decode_execute MUL nil = KO "MUL: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute MUL (n2 :: nil) = KO "MUL: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       decode_execute MUL (n2 :: n1 :: ds) = OK ((n1 * n2) :: ds)))
  /\
((decode_execute DIV nil = KO "DIV: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute DIV (n2 :: nil) = KO "DIV: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       n2 =? 0 = true ->
       decode_execute DIV (n2 :: n1 :: ds) = KO (String.append "division by 0 on" (string_of_nat (n1))))
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       n2 =? 0 = false ->
       decode_execute DIV (n2 :: n1 :: ds) = OK ((n1/n2) :: ds))).

(* Task 2:
   a. if there is time, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)



Definition decode_execute (bcis : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
  | PUSH n =>
    OK (n :: ds)
  | ADD =>
    match ds with
    | nil =>
      KO "ADD: stack underflow"
    | n2 :: nil =>
      KO "ADD: stack underflow"
    | n2 :: n1 :: ds'' =>
      OK ((n1 + n2) :: ds'')
    end
  | SUB =>
    match ds with
    | nil =>
      KO "SUB: stack underflow"
    | n2 :: nil =>
      KO "SUB: stack underflow"
    | n2 :: n1 :: ds =>
      match n1 <? n2 with
      | true =>
        KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
      | false =>
        OK ((n1 - n2) :: ds)
      end
    end
  | MUL =>
    match ds with
    | nil =>
      KO "MUL: stack underflow"
    | n2 :: nil =>
      KO "MUL: stack underflow"
    | n2 :: n1 :: ds =>
      OK ((n1 * n2) :: ds)
    end
  | DIV =>
    match ds with
    | nil =>
      KO "DIV: stack underflow"
    | n2 :: nil =>
      KO "DIV: stack underflow"
    | n2 :: n1 :: ds =>
      match n2 =? 0 with
      | true =>
        KO (String.append "division by 0 on" (string_of_nat (n1)))
      | false =>
        OK ((n1/n2) :: ds)
      end
    end
  end.


         
    

Theorem decode_execute_satisfies_its_specification :
  specification_of_decode_execute decode_execute.
Proof.
  unfold specification_of_decode_execute, decode_execute.
  split.

  - intros n ds.
    reflexivity.

  - split.

    + split.

      -- reflexivity.

      -- split.

         ++ intro nat.
            reflexivity.

         ++ intros n1 n2 ds.
            reflexivity.

    + split.

      -- split.

         ++ reflexivity.

         ++ split.

            --- intro nat.
                reflexivity.

            --- split.

                ++++ intros n1 n2 ds.
                     intro H_n1_n2.
                     rewrite H_n1_n2.
                     reflexivity.

                ++++ intros n1 n2 ds.
                     intro H_n1_n2.
                     rewrite H_n1_n2.
                     reflexivity.

      -- split.

         ++ split.

            --- reflexivity.

            --- split.

                +++ intro nat.
                    reflexivity.

                +++ intros n1 n2 ds.
                    reflexivity.

         ++ split.

            --- reflexivity.

            --- split.

                +++ intro nat.
                    reflexivity.

                +++ split.

                    ---- intros n1 n2 ds.
                         intro H_n2.
                         rewrite H_n2.
                         reflexivity.

                    ---- intros n1 n2 ds.
                         intros H_n2.
                         rewrite H_n2.
                         reflexivity.

Qed.
            


Proposition there_is_at_most_one_specification_of_decode_execute :
  forall f g,
    specification_of_decode_execute f ->
    specification_of_decode_execute g ->
    forall (bcis : byte_code_instruction)
           (ds : data_stack),
      f bcis ds = g bcis ds.
Proof.
  intros f g.
  intros S_decode_execute_f S_decode_execute_g.
  intros bcis.
  induction bcis as [n | ds IHds | ds IHds | ds IHds | ds IHds]; intro ds.

  - destruct S_decode_execute_f as [H_f_push _].
    destruct S_decode_execute_g as [H_g_push _].
    rewrite -> (H_f_push).
    rewrite -> (H_g_push).
    reflexivity.

  - destruct ds as [nil | n2].

    + (*destruct S_decode_execute_f as [_ [[H_f_plus_nil [H_f_plus_n2_nil H_f_plus_n2_n1_ds]] [_ [_ _]]]].
    destruct S_decode_execute_g as [_ [[H_g_plus_nil [H_g_plus_n2_nil H_g_plus_n2_n1_ds]] [_ [_ _]]]].*)
      destruct S_decode_execute_f as [_ [[H_f_plus_nil [_ _]] [_ [_ _]]]].
      destruct S_decode_execute_g as [_ [[H_g_plus_nil [_ _]] [_ [_ _]]]].
      rewrite H_f_plus_nil.
      rewrite H_g_plus_nil.
      reflexivity.

    + destruct ds as [nil| n1].

      -- destruct S_decode_execute_f as [_ [[_ [H_f_plus_n2_nil _]] [_ [_ _]]]].
         destruct S_decode_execute_g as [_ [[_ [H_g_plus_n2_nil _]] [_ [_ _]]]].
         rewrite H_f_plus_n2_nil.
         rewrite H_g_plus_n2_nil.
         reflexivity.

      -- destruct S_decode_execute_f as [_ [[_ [_ H_f_plus_n2_n1_ds]] [_ [_ _]]]].
         destruct S_decode_execute_g as [_ [[_ [_ H_g_plus_n2_n1_ds]] [_ [_ _]]]].
         rewrite H_f_plus_n2_n1_ds.
         rewrite H_g_plus_n2_n1_ds.
         reflexivity.

  - destruct ds as [nil | n2].

    + (*destruct S_decode_execute_f as [_ [_ [[H_f_sub_nil [H_f_sub_n2_nil [H_f_sub_n2_n1_ds_neg H_f_sub_n2_n1_ds_pos]]] [_ _]]]].*)
      destruct S_decode_execute_f as [_ [_ [[H_f_sub_nil [_ [_ _]]] [_ _]]]].
      destruct S_decode_execute_g as [_ [_ [[H_g_sub_nil [_ [_ _]]] [_ _]]]].
      rewrite H_f_sub_nil.
      rewrite H_g_sub_nil.
      reflexivity.

    + destruct ds as [nil|n1].

      -- destruct S_decode_execute_f as [_ [_ [[_ [H_f_sub_n2_nil [_ _]]] [_ _]]]].
         destruct S_decode_execute_g as [_ [_ [[_ [H_g_sub_n2_nil [_ _]]] [_ _]]]].
         rewrite H_f_sub_n2_nil.
         rewrite H_g_sub_n2_nil.
         reflexivity.

      -- destruct (n1 <? n2) eqn: H_n1_n2.

         ++ destruct S_decode_execute_f as [_ [_ [[_ [_ [H_f_sub_n2_n1_ds_neg _]]] [_ _]]]].
            destruct S_decode_execute_g as [_ [_ [[_ [_ [H_g_sub_n2_n1_ds_neg _]]] [_ _]]]].
            rewrite H_f_sub_n2_n1_ds_neg.
            rewrite H_g_sub_n2_n1_ds_neg.
            reflexivity.
            rewrite H_n1_n2.
            reflexivity.
            rewrite H_n1_n2.
            reflexivity.

         ++ destruct S_decode_execute_f as [_ [_ [[_ [_ [_ H_f_sub_n2_n1_ds_pos]]] [_ _]]]].
            destruct S_decode_execute_g as [_ [_ [[_ [_ [_ H_g_sub_n2_n1_ds_pos]]] [_ _]]]].
            rewrite H_f_sub_n2_n1_ds_pos.
            rewrite H_g_sub_n2_n1_ds_pos.
            reflexivity.
            rewrite H_n1_n2.
            reflexivity.
            rewrite H_n1_n2.
            reflexivity.

  - destruct ds as [nil| n2].

    + (*destruct S_decode_execute_f as [_ [_ [_ [[H_f_mul_nil [H_f_mul_n2_nil H_f_mul_n2_n1_ds]] _]]]].*)
      destruct S_decode_execute_f as [_ [_ [_ [[H_f_mul_nil [_ _]] _]]]].
      destruct S_decode_execute_g as [_ [_ [_ [[H_g_mul_nil [_ _]] _]]]].
      rewrite H_f_mul_nil.
      rewrite H_g_mul_nil.
      reflexivity.

    + destruct ds as [nil | n1].

      -- destruct S_decode_execute_f as [_ [_ [_ [[_ [H_f_mul_n2_nil _]] _]]]].
         destruct S_decode_execute_g as [_ [_ [_ [[_ [H_g_mul_n2_nil _]] _]]]].
         rewrite H_f_mul_n2_nil.
         rewrite H_g_mul_n2_nil.
         reflexivity.

      -- destruct S_decode_execute_f as [_ [_ [_ [[_ [_ H_f_mul_n2_n1_ds]] _]]]].
         destruct S_decode_execute_g as [_ [_ [_ [[_ [_ H_g_mul_n2_n1_ds]] _]]]].
         rewrite H_f_mul_n2_n1_ds.
         rewrite H_g_mul_n2_n1_ds.
         reflexivity.

  - destruct ds as [nil|n2].

    + (*destruct S_decode_execute_f as [_ [_ [_ [_ [H_f_div_nil [H_f_div_n2_nil [H_f_div_n2_n1_ds_O H_f_div_n2_n1_ds]]]]]]].*)
      destruct S_decode_execute_f as [_ [_ [_ [_ [H_f_div_nil [_ [_ _]]]]]]].
      destruct S_decode_execute_g as [_ [_ [_ [_ [H_g_div_nil [_ [_ _]]]]]]].
      rewrite H_f_div_nil.
      rewrite H_g_div_nil.
      reflexivity.

    + destruct ds as [nil | n1].

      -- destruct S_decode_execute_f as [_ [_ [_ [_ [_ [H_f_div_n2_nil [_ _]]]]]]].
         destruct S_decode_execute_g as [_ [_ [_ [_ [_ [H_g_div_n2_nil [_ _]]]]]]].
         rewrite H_f_div_n2_nil.
         rewrite H_g_div_n2_nil.
         reflexivity.

      -- destruct (n2 =? 0) eqn: H_n2.

         ++ destruct S_decode_execute_f as [_ [_ [_ [_ [_ [_ [H_f_div_n2_n1_ds_O _]]]]]]].
            destruct S_decode_execute_g as [_ [_ [_ [_ [_ [_ [H_g_div_n2_n1_ds_O _]]]]]]].
            rewrite H_f_div_n2_n1_ds_O.
            rewrite H_g_div_n2_n1_ds_O.
            reflexivity.
            rewrite H_n2.
            reflexivity.
            rewrite H_n2.
            reflexivity.

         ++ destruct S_decode_execute_f as [_ [_ [_ [_ [_ [_ [_ H_f_div_n2_n1_ds]]]]]]].
            destruct S_decode_execute_g as [_ [_ [_ [_ [_ [_ [_ H_g_div_n2_n1_ds]]]]]]].
             rewrite H_f_div_n2_n1_ds.
            rewrite H_g_div_n2_n1_ds.
            reflexivity.
            rewrite H_n2.
            reflexivity.
            rewrite H_n2.
            reflexivity.
Qed.
                     
      

    
      
      
   
    





(* ********** *)

(* Specification of the virtual machine: *)

Definition specification_of_fetch_decode_execute_loop (fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  forall decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_decode_execute decode_execute ->
    (forall ds : data_stack,
        fetch_decode_execute_loop nil ds = OK ds)
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds ds' : data_stack),
        decode_execute bci ds = OK ds' ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        fetch_decode_execute_loop bcis' ds')
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds : data_stack)
            (s : string),
        decode_execute bci ds = KO s ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        KO s).

(* Task 3:
   a. if there is time, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

Fixpoint fetch_decode_execute_loop (bcis : list byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
  |nil =>
   OK ds
  | bci :: bcis' =>
    match decode_execute bci ds with
    | OK ds' =>
      fetch_decode_execute_loop bcis' ds'
    | KO s =>
      KO s
    end
  end.

Compute(fetch_decode_execute_loop (PUSH 42 :: nil) (2 :: 1 :: nil)).
Compute(fetch_decode_execute_loop (PUSH 42 :: nil) (nil)).
Compute(fetch_decode_execute_loop (ADD :: nil) (2 :: 1 :: nil)).
Compute(fetch_decode_execute_loop (DIV :: nil) (0 :: 1 :: nil)).
Compute(fetch_decode_execute_loop (SUB :: nil) (3 :: 2 :: nil)).

Lemma fold_unfold_fetch_decode_execute_loop_nil :
  forall (ds : data_stack),
    fetch_decode_execute_loop nil ds = OK ds.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop (bci :: bcis') ds =
    match decode_execute bci ds with
    | OK ds' =>
      fetch_decode_execute_loop bcis' ds'
    | KO s =>
      KO s
    end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

Theorem fetch_decode_execute_loop_satisfies_its_specification :
  specification_of_fetch_decode_execute_loop fetch_decode_execute_loop.
Proof.
  unfold specification_of_fetch_decode_execute_loop.
  intros decode_execute' H_dec_exec.
  split.

  - intro ds.
    rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
    reflexivity.

  - split.

    -- intros bci bcis' ds ds'.
       intro H_OK.
       rewrite -> (fold_unfold_fetch_decode_execute_loop_cons).
       
       destruct (decode_execute bci ds) as [ds_OK | s_KO] eqn: H_ds.
       
       --- Check (there_is_at_most_one_specification_of_decode_execute decode_execute decode_execute' decode_execute_satisfies_its_specification H_dec_exec bci ds).
      rewrite <- (there_is_at_most_one_specification_of_decode_execute decode_execute decode_execute' decode_execute_satisfies_its_specification H_dec_exec bci ds) in H_OK.
      rewrite -> H_OK in H_ds.
      injection H_ds as H_ds.
      rewrite H_ds.
      reflexivity.
       
       --- rewrite <- (there_is_at_most_one_specification_of_decode_execute decode_execute decode_execute' decode_execute_satisfies_its_specification H_dec_exec bci ds) in H_OK.
            rewrite -> H_OK in H_ds.
            discriminate H_ds.

    -- intros bci bcis' ds s.
       intro H_KO.
       rewrite -> (fold_unfold_fetch_decode_execute_loop_cons).
       
       destruct (decode_execute bci ds) as [ds_OK | s_KO] eqn: H_ds.

       --- rewrite <- (there_is_at_most_one_specification_of_decode_execute decode_execute decode_execute' decode_execute_satisfies_its_specification H_dec_exec bci ds) in H_KO.
           rewrite -> H_KO in H_ds.
           discriminate H_ds.
       --- rewrite <- (there_is_at_most_one_specification_of_decode_execute decode_execute decode_execute' decode_execute_satisfies_its_specification H_dec_exec bci ds) in H_KO.
           rewrite <- H_KO.
           rewrite <- H_ds.
           reflexivity.
Qed.

Proposition there_is_at_most_one_fetch_decode_execute_loop_function :
  forall f g,
    specification_of_fetch_decode_execute_loop f ->
    specification_of_fetch_decode_execute_loop g ->
    forall (bcis : list byte_code_instruction)
           (ds : data_stack),
      f bcis ds = g bcis ds.
Proof.
  intros f g.
  unfold specification_of_fetch_decode_execute_loop.
  intros S_fetch_decode_execute_loop_f S_fetch_decode_execute_loop_g.
  intros bcis.
  induction bcis as[| bci bcis' IHbcis'].

  - intro ds.
    destruct (S_fetch_decode_execute_loop_f decode_execute decode_execute_satisfies_its_specification) as [H_f_nil_ds [ _ _]].
    destruct (S_fetch_decode_execute_loop_g decode_execute decode_execute_satisfies_its_specification) as [H_g_nil_ds [ _ _]].
    rewrite H_f_nil_ds.
    rewrite H_g_nil_ds.
    reflexivity.

  - intro ds.
    destruct (S_fetch_decode_execute_loop_f decode_execute decode_execute_satisfies_its_specification) as [_ [H_f_ds_bci_bcis'_OK  H_f_ds_bci_bcis'_KO]].
    destruct (S_fetch_decode_execute_loop_g decode_execute decode_execute_satisfies_its_specification) as [_ [H_g_ds_bci_bcis'_OK H_g_ds_bci_bcis'_KO]].
    destruct (decode_execute bci ds) as [ds' | s] eqn:H_ds.

      + rewrite -> (H_f_ds_bci_bcis'_OK bci bcis' ds ds' H_ds).
        rewrite -> (H_g_ds_bci_bcis'_OK bci bcis' ds ds' H_ds).
        rewrite IHbcis'.
        reflexivity.

      + rewrite -> (H_f_ds_bci_bcis'_KO bci bcis' ds s H_ds).
        rewrite -> (H_g_ds_bci_bcis'_KO bci bcis' ds s H_ds).
        reflexivity.

Qed.

(* 
strengthened the induction hypothesis by introducing ds later on
in the inducting step, using all ducks instead of only one e.g. [_[H _] vs [a[b c]]
*)
    

    
  
           
           
   

(* ********** *)

(* Task 4:
   Prove that for any lists of byte-code instructions bcis1 and bcis2,
   and for any data stack ds,
   executing the concatenation of bcis1 and bcis2 (i.e., bcis1 ++ bcis2) with ds
   gives the same result as
   (1) executing bcis1 with ds, and then
   (2) executing bcis2 with the resulting data stack, if there exists one.
*)

Lemma fold_unfold_append_nil :
  forall bcis2 : list byte_code_instruction,
    nil ++ bcis2 = bcis2.
Proof.
  fold_unfold_tactic List.app.
Qed.



Lemma fold_unfold_append_cons :
  forall (bci1 : byte_code_instruction)
         (bci1s bci2s : list byte_code_instruction),
    (bci1 :: bci1s) ++ bci2s =
    bci1 :: (bci1s ++ bci2s).
Proof.
  fold_unfold_tactic List.app.
Qed.

Proposition byte_code_append_property :
  forall (bcis1 bcis2 : list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop (bcis1 ++ bcis2) ds =
    match (fetch_decode_execute_loop bcis1 ds) with
    | OK ds' =>
      fetch_decode_execute_loop bcis2 ds'
    | KO s =>
      KO s
    end.
Proof.
  intros bcis1.
  induction bcis1 as [|bci1 bcis1' IHbcis1']; intros bcis2 ds.

  - rewrite -> (fold_unfold_fetch_decode_execute_loop_nil).
    rewrite -> (fold_unfold_append_nil).
    reflexivity.

  - rewrite -> (fold_unfold_append_cons).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_cons).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_cons).
    destruct (decode_execute bci1 ds) as [ds_OK|s_KO] eqn: H_ds.

    + rewrite -> (IHbcis1' bcis2 ds_OK).
      reflexivity.

    + reflexivity.

Qed.
    


(* ********** *)

Definition specification_of_run (run : target_program -> expressible_value) :=
  forall fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop ->
    (forall (bcis : list byte_code_instruction),
       fetch_decode_execute_loop bcis nil = OK nil ->
       run (Target_program bcis) = Expressible_msg "no result on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (n : nat),
       fetch_decode_execute_loop bcis nil = OK (n :: nil) ->
       run (Target_program bcis) = Expressible_nat n)
    /\
    (forall (bcis : list byte_code_instruction)
            (n n' : nat)
            (ds'' : data_stack),
       fetch_decode_execute_loop bcis nil = OK (n :: n' :: ds'') ->
       run (Target_program bcis) = Expressible_msg "too many results on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (s : string),
       fetch_decode_execute_loop bcis nil = KO s ->
       run (Target_program bcis) = Expressible_msg s).



(* Task 5:
   a. if there is time, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

Definition run  (tp : target_program) : expressible_value :=
  match tp with
  | Target_program bcis =>
    match fetch_decode_execute_loop bcis nil with
    | OK nil =>
      Expressible_msg "no result on the data stack"
    | OK (n :: nil) =>
      Expressible_nat n               
    | OK (n :: n' :: ds'') =>
      Expressible_msg "too many results on the data stack"
    | KO s =>
      Expressible_msg s
    end
  end.

Compute(run (Target_program (PUSH 2 :: PUSH 3 :: ADD :: nil))).

Theorem run_satisfies_its_specification :
  specification_of_run run.
Proof.
  unfold specification_of_run, run.
  intro fetch_decode_execute_loop'.
  intro S_fetch_decode_execute_loop'.
  Check ( there_is_at_most_one_fetch_decode_execute_loop_function fetch_decode_execute_loop fetch_decode_execute_loop' fetch_decode_execute_loop_satisfies_its_specification S_fetch_decode_execute_loop').
  assert( the_same_el:= ( there_is_at_most_one_fetch_decode_execute_loop_function fetch_decode_execute_loop fetch_decode_execute_loop' fetch_decode_execute_loop_satisfies_its_specification S_fetch_decode_execute_loop')).
  
  split;[ | split; [ | split]].

  - intro bcis.
    rewrite <- the_same_el.
    intro H_bcis.
    rewrite H_bcis.
    
    reflexivity.

  -  intros bcis n.
     rewrite <- the_same_el.
     intro H_bcis.
     rewrite H_bcis.
     reflexivity.
      
  - intros bcis n n' ds''.
    rewrite <- the_same_el.
    intro H_bcis.
    rewrite H_bcis.
    reflexivity.

  - intros bcis s .
    rewrite <- the_same_el.
    intro H_bcis.
    rewrite H_bcis.
    reflexivity.

   

Qed.

Proposition there_is_at_most_one_specification_of_run :
  forall f g,
    specification_of_run f ->
    specification_of_run g ->
    forall (tp : target_program ),
      f tp = g tp.
Proof.
  intros f g.
  unfold specification_of_run.
  intros S_run_f S_run_g.
  destruct (S_run_f fetch_decode_execute_loop fetch_decode_execute_loop_satisfies_its_specification) as [H_OK_0_f [ H_OK_1_f [H_OK_2_f H_KO_f]]].
  destruct (S_run_g fetch_decode_execute_loop fetch_decode_execute_loop_satisfies_its_specification) as [H_OK_0_g [ H_OK_1_g [H_OK_2_g H_KO_g]]].
  clear S_run_f S_run_g.
  intros [bcis].
  destruct (fetch_decode_execute_loop bcis nil) as [[ | n [ | n' ds'']] | s] eqn: H_bcis.

  - Check ( H_OK_0_f bcis H_bcis).
    rewrite ( H_OK_0_f bcis H_bcis).
    rewrite ( H_OK_0_g bcis H_bcis).
    reflexivity.

  - rewrite (H_OK_1_f bcis n H_bcis).
    rewrite (H_OK_1_g bcis n H_bcis).
    reflexivity.

  - rewrite (H_OK_2_f bcis n n' ds'').
    rewrite (H_OK_2_g bcis n n' ds'').
    reflexivity.
    exact H_bcis.
    exact H_bcis.
        
  - rewrite (H_KO_f bcis s).
    rewrite (H_KO_g bcis s).
    reflexivity.
    exact H_bcis.
    exact H_bcis.
    
Qed. 
   

(* ********** *)

Definition specification_of_compile_aux (compile_aux : arithmetic_expression -> list byte_code_instruction) :=
  (forall n : nat,
     compile_aux (Literal n) = PUSH n :: nil)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Plus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
      compile_aux (Minus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
      compile_aux (Multiply ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (MUL :: nil))
  /\
   (forall ae1 ae2 : arithmetic_expression,
       compile_aux (Divide ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (DIV :: nil)).



(* Task 6:
   a. if there is time, prove that the definition above specifies at most one function;
   b. implement this function using list concatenation, i.e., ++; and
   c. verify that your function satisfies the specification.
 *)

Fixpoint compile_aux (ae1 : arithmetic_expression) : list byte_code_instruction :=
  match ae1 with
  | Literal n =>
    PUSH n :: nil
  | Plus ae1 ae2 =>    
    ((compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil))
  | Minus ae1 ae2 =>
    ((compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil))
  | Multiply ae1 ae2 =>
   ((compile_aux ae1) ++ (compile_aux ae2) ++ (MUL :: nil))
  | Divide ae1 ae2 =>
    ((compile_aux ae1) ++ (compile_aux ae2) ++ (DIV :: nil))
  end.

Lemma fold_unfold_compile_aux_literal:
  forall (n : nat),
    compile_aux (Literal n) = PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_plus:
   forall (ae1 ae2 : arithmetic_expression),
     compile_aux (Plus ae1 ae2) = ((compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil)).
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_minus:
  forall (ae1 ae2: arithmetic_expression),
    compile_aux (Minus ae1 ae2 ) = ((compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)).
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_multiply:
  forall (ae1 ae2 : arithmetic_expression),
    compile_aux (Multiply ae1 ae2) = ((compile_aux ae1) ++ (compile_aux ae2) ++ (MUL :: nil)).
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_divide:
  forall (ae1 ae2 : arithmetic_expression),
    compile_aux (Divide ae1 ae2) = ((compile_aux ae1) ++ (compile_aux ae2) ++ (DIV :: nil)).
Proof.
  fold_unfold_tactic compile_aux.
Qed.

     
Theorem compile_aux_satisfies_its_specification :
  specification_of_compile_aux compile_aux.
Proof.
  unfold specification_of_compile_aux.
  split.
  -  exact fold_unfold_compile_aux_literal.

  - split.

    + exact fold_unfold_compile_aux_plus.

    + split.

      -- exact fold_unfold_compile_aux_minus.
         
      -- split.

         ++ exact fold_unfold_compile_aux_multiply.

         ++ exact fold_unfold_compile_aux_divide.

Qed.

Proposition there_is_at_most_one_compile_aux_function :
  forall f g,
    specification_of_compile_aux f ->
    specification_of_compile_aux g ->
    forall ae1,
      f ae1 = g ae1.
Proof.
  intros f g.
  intros S_compile_aux_f S_compile_aux_g.
  intro ae1.
  induction ae1 as [n| ae1 IHae1| ae1 IHae1 | ae1 IHae1| ae1 IHae1].

  - unfold specification_of_compile_aux in S_compile_aux_f.
    destruct S_compile_aux_f as [H_f_lit [ _ [ _ [ _ _ ]]]].
    destruct S_compile_aux_g as [H_g_lit [ _ [ _ [ _ _ ]]]].
    rewrite H_f_lit.
    rewrite H_g_lit.
    reflexivity.

  - unfold specification_of_compile_aux in S_compile_aux_f.
    destruct S_compile_aux_f as [_ [H_f_plus [ _ [ _ _ ]]]].
    destruct S_compile_aux_g as [_ [H_g_plus [ _ [ _ _ ]]]].
    rewrite H_f_plus.
    rewrite H_g_plus.
    rewrite IHae1.
    rewrite IHae1_1.
    reflexivity.

  - unfold specification_of_compile_aux in S_compile_aux_f.
    destruct S_compile_aux_f as [_ [_ [H_f_minus [ _ _ ]]]].
    destruct S_compile_aux_g as [_ [_ [H_g_minus [ _ _ ]]]].
    rewrite H_f_minus.
    rewrite H_g_minus.
    rewrite IHae1.
    rewrite IHae1_1.
    reflexivity.

  - unfold specification_of_compile_aux in S_compile_aux_f.
    destruct S_compile_aux_f as [_ [_ [ _ [H_f_multiply _ ]]]].
    destruct S_compile_aux_g as [_ [_ [ _ [H_g_multiply _ ]]]].
    rewrite H_f_multiply.
    rewrite H_g_multiply.
    rewrite IHae1.
    rewrite IHae1_1.
    reflexivity.

  - unfold specification_of_compile_aux in S_compile_aux_f.
    destruct S_compile_aux_f as [_ [_ [ _ [ _ H_f_div ]]]].
    destruct S_compile_aux_g as [_ [_ [ _ [ _ H_g_div ]]]].
    rewrite H_f_div.
    rewrite H_g_div.
    rewrite IHae1.
    rewrite IHae1_1.
    reflexivity.

Qed.
    


(************)

Definition specification_of_compile (compile : source_program -> target_program) :=
  forall compile_aux : arithmetic_expression -> list byte_code_instruction,
    specification_of_compile_aux compile_aux ->
    forall ae : arithmetic_expression,
      compile (Source_program ae) = Target_program (compile_aux ae).

(* Task 7:
   a. if there is time, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
*)


Definition compile (sc : source_program) : target_program :=
  match sc with
  | Source_program ae =>
      Target_program (compile_aux ae)
  end.

Theorem compile_satisfies_its_specification :
  specification_of_compile compile.
Proof.
  unfold specification_of_compile, compile.
  intro compile_aux'.
  intro H_compile_aux.
  intro ae.
  Check (there_is_at_most_one_compile_aux_function compile_aux compile_aux' compile_aux_satisfies_its_specification H_compile_aux ae).
  rewrite (there_is_at_most_one_compile_aux_function compile_aux compile_aux' compile_aux_satisfies_its_specification H_compile_aux ae).
  reflexivity.

Qed.

Proposition there_is_at_most_one_compile_function:
  forall f g,
    specification_of_compile f ->
    specification_of_compile g ->
    forall sc : source_program,
      f sc = g sc.
Proof.
  intros f g.
  intros S_f_compile S_g_compile.
  intros [ae].
  unfold specification_of_compile in S_f_compile.
  unfold specification_of_compile in S_g_compile.
  Check (S_f_compile compile_aux compile_aux_satisfies_its_specification ae).
  rewrite -> (S_f_compile compile_aux compile_aux_satisfies_its_specification ae).
  rewrite -> (S_g_compile compile_aux compile_aux_satisfies_its_specification ae).
  reflexivity.

Qed.



(* Task 8:
   implement an alternative compiler
   using an auxiliary function with an accumulator
   and that does not use ++ but :: instead,
   and prove that it satisfies the specification.

   Subsidiary question:
   Are your compiler and your alternative compiler equivalent?
   How can you tell?
 *)
Fixpoint compile_aux' (ae : arithmetic_expression) (bcis : list byte_code_instruction): list byte_code_instruction :=
  match ae with
  | Literal n =>
    PUSH n :: bcis
  | Plus ae1 ae2 =>
    compile_aux' ae1 (compile_aux' ae2 (ADD :: bcis))
  | Minus ae1 ae2 =>
    compile_aux' ae1 (compile_aux' ae2 (SUB :: bcis))
  | Multiply ae1 ae2 =>
    compile_aux' ae1 (compile_aux' ae2 (MUL :: bcis))
  | Divide ae1 ae2 =>
    compile_aux' ae1 (compile_aux' ae2 (DIV :: bcis))
  end.

Lemma fold_unfold_compile_aux'_literal:
  forall (n : nat)
         (bcis : list byte_code_instruction),
    compile_aux' (Literal n) bcis = PUSH n :: bcis.
Proof.
  fold_unfold_tactic compile_aux'.
Qed.

Lemma fold_unfold_compile_aux'_plus:
  forall (ae1 ae2 : arithmetic_expression)
         (bcis : list byte_code_instruction),
     compile_aux' (Plus ae1 ae2) bcis = compile_aux' ae1 (compile_aux' ae2 (ADD :: bcis)).
Proof.
  fold_unfold_tactic compile_aux'.
Qed.

Lemma fold_unfold_compile_aux'_minus:
  forall (ae1 ae2: arithmetic_expression)
         (bcis : list byte_code_instruction),
    compile_aux' (Minus ae1 ae2 ) bcis =  compile_aux' ae1 (compile_aux' ae2 (SUB :: bcis)).
Proof.
  fold_unfold_tactic compile_aux'.
Qed.

Lemma fold_unfold_compile_aux'_multiply:
  forall (ae1 ae2 : arithmetic_expression)
         (bcis : list byte_code_instruction),
    compile_aux' (Multiply ae1 ae2) bcis = compile_aux' ae1 (compile_aux' ae2 (MUL :: bcis)).
Proof.
  fold_unfold_tactic compile_aux'.
Qed.

Lemma fold_unfold_compile_aux'_divide:
  forall (ae1 ae2 : arithmetic_expression)
         (bcis : list byte_code_instruction),
    compile_aux' (Divide ae1 ae2) bcis =  compile_aux' ae1 (compile_aux' ae2 (DIV :: bcis)).
Proof.
  fold_unfold_tactic compile_aux'.
Qed.



Definition compile' (sp : source_program): target_program :=
  match sp with
  | Source_program ae =>
    Target_program (compile_aux' ae nil)
  end.

Lemma about_compile_aux'_and_compile_aux :
  forall (ae : arithmetic_expression)
         (bcis : list byte_code_instruction),
    compile_aux' ae bcis = compile_aux ae ++ bcis.
Proof.
  intros ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2| ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro bcis.

  - rewrite -> fold_unfold_compile_aux'_literal.
    rewrite -> fold_unfold_compile_aux_literal.
    rewrite -> (fold_unfold_append_cons).
    rewrite -> (fold_unfold_append_nil).
    reflexivity.

  - rewrite -> fold_unfold_compile_aux'_plus.
    rewrite -> fold_unfold_compile_aux_plus.
    rewrite -> (IHae1 (compile_aux' ae2 (ADD :: bcis))).
    rewrite -> (IHae2  (ADD :: bcis)).
    Check (List.app_assoc).
    rewrite -> (List.app_assoc (compile_aux ae1) (compile_aux ae2) (ADD :: nil)).
    rewrite <- (List.app_assoc (compile_aux ae1 ++ compile_aux ae2) (ADD :: nil) ).
    rewrite -> (fold_unfold_append_cons).
    rewrite -> (fold_unfold_append_nil).
    rewrite <- (List.app_assoc).
    reflexivity.

  - rewrite -> fold_unfold_compile_aux'_minus.
    rewrite -> fold_unfold_compile_aux_minus.
    rewrite -> (IHae1 (compile_aux' ae2 (SUB :: bcis))).
    rewrite -> (IHae2  (SUB :: bcis)).
    Check (List.app_assoc).
    rewrite -> (List.app_assoc (compile_aux ae1) (compile_aux ae2) (SUB :: nil)).
    rewrite <- (List.app_assoc (compile_aux ae1 ++ compile_aux ae2) (SUB :: nil) ).
    rewrite -> (fold_unfold_append_cons).
    rewrite -> (fold_unfold_append_nil).
    rewrite <- (List.app_assoc).
    reflexivity.

  - rewrite -> fold_unfold_compile_aux'_multiply.
    rewrite -> fold_unfold_compile_aux_multiply.
    rewrite -> (IHae1 (compile_aux' ae2 (_ :: bcis))).
    rewrite -> (IHae2  (_ :: bcis)).
    Check (List.app_assoc).
    rewrite -> (List.app_assoc (compile_aux ae1) (compile_aux ae2) (_ :: nil)).
    rewrite <- (List.app_assoc (compile_aux ae1 ++ compile_aux ae2) (_ :: nil) ).
    rewrite -> (fold_unfold_append_cons).
    rewrite -> (fold_unfold_append_nil).
    rewrite <- (List.app_assoc).
    reflexivity.

  - rewrite -> fold_unfold_compile_aux'_divide.
    rewrite -> fold_unfold_compile_aux_divide.
    rewrite -> (IHae1 (compile_aux' ae2 (_ :: bcis))).
    rewrite -> (IHae2  (_ :: bcis)).
    Check (List.app_assoc).
    rewrite -> (List.app_assoc (compile_aux ae1) (compile_aux ae2) (_ :: nil)).
    rewrite <- (List.app_assoc (compile_aux ae1 ++ compile_aux ae2) (_ :: nil) ).
    rewrite -> (fold_unfold_append_cons).
    rewrite -> (fold_unfold_append_nil).
    rewrite <- (List.app_assoc).
    reflexivity.

Qed.
    

Theorem compile'_satisfies_its_specification :
  specification_of_compile compile'.
Proof.
  unfold specification_of_compile, compile'.
  intro compile_aux0.
  intro H_compile_aux.
  intro ae.
  rewrite <- (there_is_at_most_one_compile_aux_function compile_aux compile_aux0 compile_aux_satisfies_its_specification H_compile_aux ae).
  rewrite -> (about_compile_aux'_and_compile_aux ae nil).
  rewrite -> (List.app_nil_r).
  reflexivity.
Qed.
    



(* ********** *)

(* Task 9 (the capstone):
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program.
 *)
(* expect the result of the last evaluation/operation to be on top of the stack
 *)

Lemma capstone_aux :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
    (forall (n : nat),
        evaluate ae = Expressible_nat n ->
    fetch_decode_execute_loop (compile_aux ae) ds = OK (n :: ds))
    /\
    (forall (s : string),
        evaluate ae = Expressible_msg s ->
        fetch_decode_execute_loop (compile_aux ae) ds = KO (s)).
Proof.
  intro ae.
  induction ae as [m | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro ds; (split; [intro n | intro s]).

  + rewrite -> (fold_unfold_evaluate_literal).
    intro H_n.
    injection H_n as H_n.
    rewrite -> H_n.
    rewrite -> fold_unfold_compile_aux_literal.
    rewrite -> (fold_unfold_fetch_decode_execute_loop_cons).
    unfold decode_execute.
    rewrite -> (fold_unfold_fetch_decode_execute_loop_nil).
    reflexivity.
    
  + rewrite -> (fold_unfold_evaluate_literal).
    intro H_absurd.
    discriminate H_absurd.
    
  + rewrite -> (fold_unfold_evaluate_plus).
    destruct (evaluate ae1) as [n1 | s1] eqn: H_ae1; destruct (evaluate ae2) as [n2 | s2] eqn: H_ae2.
    
  - intro H_n.
    injection H_n as H_n.
    rewrite <- H_n.
    rewrite -> (fold_unfold_compile_aux_plus).
    Check (byte_code_append_property).
    rewrite -> (byte_code_append_property).
    Check (IHae1 ds).
    destruct (IHae1 ds) as [H_IHae1n _].
    Check (H_IHae1n n1 (eq_refl (Expressible_nat n1))).
    rewrite -> (H_IHae1n n1 (eq_refl (Expressible_nat n1))).
    rewrite -> (byte_code_append_property).
    destruct (IHae2 (n1 :: ds)) as [H_IHae2n _].
    rewrite -> (H_IHae2n n2 (eq_refl (Expressible_nat n2))).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_cons).
    unfold decode_execute.
    apply fold_unfold_fetch_decode_execute_loop_nil.

  - intro H_n.
    discriminate H_n.

  - intro H_n.
    discriminate H_n.

  - intro H_n.
    discriminate H_n.
    
    + rewrite  -> (fold_unfold_evaluate_plus).
      destruct (evaluate ae1) as [n1 | s1] eqn: H_ae1; destruct (evaluate ae2) as [n2 | s2] eqn: H_ae2.
    
  - intro H_n.
    discriminate H_n.

  - intro H_s.
    injection H_s as H_s.
    rewrite <- H_s.
    rewrite -> (fold_unfold_compile_aux_plus).
    Check (byte_code_append_property).
    rewrite -> (byte_code_append_property).
    Check (IHae1 ds).
    destruct (IHae1 ds) as [H_IHae1n _].
    Check (H_IHae1n n1 (eq_refl (Expressible_nat n1))).
    rewrite -> (H_IHae1n n1 (eq_refl (Expressible_nat n1))).
    rewrite -> (byte_code_append_property).
    destruct (IHae2 (n1 :: ds)) as [_ H_IHae2s].
    rewrite -> (H_IHae2s s2 (eq_refl (Expressible_msg s2))).
    reflexivity.

  - intro H_s.
    injection H_s as H_s.
    rewrite <- H_s.
    rewrite -> (fold_unfold_compile_aux_plus).
    Check (byte_code_append_property).
    rewrite -> (byte_code_append_property).
    Check (IHae1 ds).
    destruct (IHae1 ds) as [_ H_IHae1s].
    rewrite -> (H_IHae1s s1 (eq_refl (Expressible_msg s1))).
    reflexivity.

  - intro H_s.
    injection H_s as H_s.
    rewrite <- H_s.
    rewrite -> (fold_unfold_compile_aux_plus).
    rewrite -> (byte_code_append_property).
    Check (IHae1 ds).
    destruct (IHae1 ds) as [_ H_IHae1s].
    rewrite -> (H_IHae1s s1 (eq_refl (Expressible_msg s1))).
    reflexivity.

    + rewrite  -> (fold_unfold_evaluate_minus).
      destruct (evaluate ae1) as [n1 | s1] eqn: H_ae1; destruct (evaluate ae2) as [n2 | s2] eqn: H_ae2.
      destruct (n1 <? n2) as [true | false] eqn: H_n1_n2.

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_n.
         injection H_n as H_n.
         rewrite -> fold_unfold_compile_aux_minus.
         rewrite -> byte_code_append_property.
         destruct (IHae1 ds) as [H_IHae1n _].
         rewrite -> (H_IHae1n n1 (eq_refl (Expressible_nat n1))).
         rewrite -> byte_code_append_property.
         destruct (IHae2 (n1 :: ds)) as [H_IHae2n _].
         rewrite -> (H_IHae2n n2 (eq_refl (Expressible_nat n2))).
         rewrite -> (fold_unfold_fetch_decode_execute_loop_cons).
         unfold decode_execute.
         rewrite -> H_n1_n2.
         rewrite -> (fold_unfold_fetch_decode_execute_loop_nil).
         rewrite -> H_n.
         reflexivity.

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_absurd.
         discriminate H_absurd.

    + rewrite  -> (fold_unfold_evaluate_minus).
      destruct (evaluate ae1) as [n1 | s1] eqn: H_ae1; destruct (evaluate ae2) as [n2 | s2] eqn: H_ae2.
      destruct (n1 <? n2) as [true | false] eqn: H_n1_n2.

      -- intro H_m.
         rewrite -> fold_unfold_compile_aux_minus.
         rewrite -> byte_code_append_property.
         destruct (IHae1 ds) as [H_IHae1n _].
         rewrite -> (H_IHae1n n1 (eq_refl (Expressible_nat n1))).
         rewrite -> byte_code_append_property.
         destruct (IHae2 (n1 :: ds)) as [H_IHae2n _].
         rewrite -> (H_IHae2n n2 (eq_refl (Expressible_nat n2))).
         rewrite -> (fold_unfold_fetch_decode_execute_loop_cons).
         unfold decode_execute.
         rewrite -> H_n1_n2.
          assert (harumph :
                   forall s1 s2 : string,
                     Expressible_msg s1 = Expressible_msg s2 ->
                     s1 = s2).
         { intros s1 s2 H_s1_s2.
           injection H_s1_s2 as H_s1_s2.
           exact H_s1_s2. }
         apply harumph in H_m.
         rewrite H_m.
         reflexivity.
         (* and now look at the type declaration %string in H_m *)

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_m.
         injection H_m as H_m.
         rewrite -> (fold_unfold_compile_aux_minus).
         rewrite -> byte_code_append_property.
         destruct (IHae1 ds) as [H_IHae1n _].
         rewrite -> (H_IHae1n n1 (eq_refl (Expressible_nat n1))).
         rewrite -> byte_code_append_property.
         destruct (IHae2 (n1 :: ds)) as [_ H_IHae2s].
         rewrite -> (H_IHae2s s2 (eq_refl (Expressible_msg s2))).
         rewrite -> H_m.
         reflexivity.

      -- intro H_m.
         injection H_m as H_m.
         rewrite -> (fold_unfold_compile_aux_minus).
         rewrite -> byte_code_append_property.
         destruct (IHae1 ds) as [_ H_IHae1s].
         rewrite -> (H_IHae1s s1 (eq_refl (Expressible_msg s1))).
         rewrite H_m.
         reflexivity.

      -- intro H_m.
         injection H_m as H_m.
         rewrite -> (fold_unfold_compile_aux_minus).
         rewrite -> byte_code_append_property.
         destruct (IHae1 ds) as [_ H_IHae1s].
         rewrite -> (H_IHae1s s1 (eq_refl (Expressible_msg s1))).
         rewrite H_m.
         reflexivity.

    + rewrite  -> (fold_unfold_evaluate_multiply).
      destruct (evaluate ae1) as [n1 | s1] eqn: H_ae1; destruct (evaluate ae2) as [n2 | s2] eqn: H_ae2.
    
      -- intro H_n.
         injection H_n as H_n.
         rewrite -> (fold_unfold_compile_aux_multiply).
         rewrite -> (byte_code_append_property).
         destruct (IHae1 ds) as [H_IHae1n _].
         rewrite -> (H_IHae1n n1 (eq_refl (Expressible_nat n1))).
         rewrite -> byte_code_append_property.
         destruct (IHae2 (n1 :: ds)) as [H_IHae2n _].
         rewrite -> (H_IHae2n n2 (eq_refl (Expressible_nat n2))).
         rewrite -> (fold_unfold_fetch_decode_execute_loop_cons).
         unfold decode_execute.
         rewrite -> (fold_unfold_fetch_decode_execute_loop_nil).
         rewrite -> H_n.
         reflexivity.

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_absurd.
         discriminate H_absurd.

    + rewrite  -> (fold_unfold_evaluate_multiply).
      destruct (evaluate ae1) as [n1 | s1] eqn: H_ae1; destruct (evaluate ae2) as [n2 | s2] eqn: H_ae2.

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_m.
         injection H_m as H_m.
         rewrite -> (fold_unfold_compile_aux_multiply).
         rewrite -> (byte_code_append_property).
         destruct (IHae1 ds) as [H_IHae1n _].
         rewrite -> (H_IHae1n n1 (eq_refl (Expressible_nat n1))).
         rewrite -> byte_code_append_property.
         destruct (IHae2 (n1 :: ds)) as [_ H_IHae2s].
         rewrite -> (H_IHae2s s2 (eq_refl (Expressible_msg s2))).
         rewrite -> (H_m).
         reflexivity.

      -- intro H_m.
         injection H_m as H_m.
         rewrite -> (fold_unfold_compile_aux_multiply).
         rewrite -> (byte_code_append_property).
         destruct (IHae1 ds) as [_ H_IHae1s].
         rewrite -> (H_IHae1s s1 (eq_refl (Expressible_msg s1))).
         rewrite -> (H_m).
         reflexivity.

      -- intro H_m.
         injection H_m as H_m.
         rewrite -> (fold_unfold_compile_aux_multiply).
         rewrite -> (byte_code_append_property).
         destruct (IHae1 ds) as [_ H_IHae1s].
         rewrite -> (H_IHae1s s1 (eq_refl (Expressible_msg s1))).
         rewrite -> (H_m).
         reflexivity.

    + rewrite  -> (fold_unfold_evaluate_divide).
      destruct (evaluate ae1) as [n1 | s1] eqn: H_ae1; destruct (evaluate ae2) as [n2 | s2] eqn: H_ae2.
      destruct (n2 =? 0) as [true | false] eqn: H_n1.

      -- intro H_m.
         discriminate H_m.

      -- intro H_n.
         injection H_n as H_n.
         rewrite -> (fold_unfold_compile_aux_divide).
         rewrite -> (byte_code_append_property).
          destruct (IHae1 ds) as [H_IHae1n _].
         rewrite -> (H_IHae1n n1 (eq_refl (Expressible_nat n1))).
         rewrite -> byte_code_append_property.
         destruct (IHae2 (n1 :: ds)) as [H_IHae2n _].
         rewrite -> (H_IHae2n n2 (eq_refl (Expressible_nat n2))).
         rewrite -> (fold_unfold_fetch_decode_execute_loop_cons).
         unfold decode_execute.
         rewrite -> H_n1.
         rewrite -> H_n.
         rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
         reflexivity.

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_absurd.
         discriminate H_absurd.

    + rewrite  -> (fold_unfold_evaluate_divide).
      destruct (evaluate ae1) as [n1 | s1] eqn: H_ae1; destruct (evaluate ae2) as [n2 | s2] eqn: H_ae2.
      destruct (n2 =? 0) as [true | false] eqn: H_n1.

      -- intro H_m.
         rewrite -> fold_unfold_compile_aux_divide.
         rewrite -> byte_code_append_property.
         destruct (IHae1 ds) as [H_IHae1n _].
         rewrite -> (H_IHae1n n1 (eq_refl (Expressible_nat n1))).
         rewrite -> byte_code_append_property.
         destruct (IHae2 (n1 :: ds)) as [H_IHae2n _].
         rewrite -> (H_IHae2n n2 (eq_refl (Expressible_nat n2))).
         rewrite -> (fold_unfold_fetch_decode_execute_loop_cons).
         unfold decode_execute.
         rewrite -> H_n1.
         assert (harumph :
                   forall s1 s2 : string,
                     Expressible_msg s1 = Expressible_msg s2 ->
                     s1 = s2).
         { intros s1 s2 H_s1_s2.
           injection H_s1_s2 as H_s1_s2.
           exact H_s1_s2. }
         apply harumph in H_m.
         rewrite -> H_m.
         reflexivity.
         (* and now look at the type declaration %string in H_m *)

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_m.
         injection H_m as H_m.
         rewrite -> fold_unfold_compile_aux_divide.
         rewrite -> byte_code_append_property.
         destruct (IHae1 ds) as [H_IHae1n _].
         rewrite -> (H_IHae1n n1 (eq_refl (Expressible_nat n1))).
         rewrite -> byte_code_append_property.
         destruct (IHae2 (n1 :: ds)) as [_ H_IHae2s].
         rewrite -> (H_IHae2s s2 (eq_refl (Expressible_msg s2))).
         rewrite -> H_m.
         reflexivity.

      -- intro H_m.
         injection H_m as H_m.
         rewrite -> fold_unfold_compile_aux_divide.
         rewrite -> byte_code_append_property.
         destruct (IHae1 ds) as [_ H_IHae1s].
         rewrite -> (H_IHae1s s1 (eq_refl (Expressible_msg s1))).
         rewrite -> H_m.
         reflexivity.

      -- intro H_m.
         injection H_m as H_m.
         rewrite -> fold_unfold_compile_aux_divide.
         rewrite -> byte_code_append_property.
         destruct (IHae1 ds) as [_ H_IHae1s].
         rewrite -> (H_IHae1s s1 (eq_refl (Expressible_msg s1))).
         rewrite -> H_m.
         reflexivity.

Qed.

     
  
 



Theorem capstone :
  forall (sp : source_program),
    interpret (sp) = run (compile (sp)).
Proof.
  intros [ae].
  unfold compile, interpret, run.
  Check (capstone_aux ae nil).
  destruct (capstone_aux ae nil) as [H_OK H_KO].
  
  destruct (evaluate ae) as [n|s] eqn: H_ae.
  - Check (H_OK n (eq_refl (Expressible_nat n))).
    rewrite -> (H_OK n (eq_refl (Expressible_nat n))).
    reflexivity.

  - Check (H_KO s (eq_refl (Expressible_msg s))).
    rewrite -> (H_KO s (eq_refl (Expressible_msg s))).
    reflexivity.
Qed.
  

(* ********** *)

(* Byte-code verification:
   the following verifier symbolically executes a byte-code program
   to check whether no underflow occurs during execution
   and whether when the program completes,
   there is one and one only natural number on top of the stack.
   The second argument of verify_aux is a natural number
   that represents the size of the stack.
*)

Fixpoint verify_aux (bcis : list byte_code_instruction) (n : nat) : option nat :=
  match bcis with
    | nil =>
      Some n
    | bci :: bcis' =>
      match bci with
        | PUSH _ =>
          verify_aux bcis' (S n)
        | _ =>
          match n with
            | S (S n') =>
              verify_aux bcis' (S n')
            | _ =>
              None
          end
      end
  end.

Lemma fold_unfold_verify_aux_nil :
  forall (n : nat),
    verify_aux nil n = Some n.
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Lemma fold_unfold_verify_aux_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (n : nat),
    verify_aux (bci :: bcis') n =
     match bci with
        | PUSH _ =>
          verify_aux bcis' (S n)
        | _ =>
          match n with
            | S (S n') =>
              verify_aux bcis' (S n')
            | _ =>
              None
          end
     end.
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Definition verify (p : target_program) : bool :=
  match p with
  | Target_program bcis =>
    match verify_aux bcis 0 with
    | Some n =>
      match n with
      | 1 =>
        true
      | _ =>
        false
      end
    | _ =>
      false
    end
  end.

(* Task 10 (if there is time):
   Prove that the compiler emits code
   that is accepted by the verifier.
*)

Lemma byte_code_append_property_verify:
  forall (bcis1 bcis2 : list byte_code_instruction)
         (h : nat),
    (forall h1 : nat,
        verify_aux bcis1 h = Some h1 ->
        verify_aux (bcis1 ++ bcis2) h = verify_aux bcis2 h1)
    /\
    (verify_aux bcis1 h = None ->
     verify_aux (bcis1 ++ bcis2) h = None).
Proof.
  intro bcis1.
  induction bcis1 as [ | [n | | | | ] bcis1' IHbcis1']; intros bcis2 h.

  - split.
    
    + intro h1.
      rewrite -> fold_unfold_verify_aux_nil.
      intro H_h.
      injection H_h as H_h.
      rewrite -> (List.app_nil_l).
      rewrite -> H_h.
      reflexivity.

    + rewrite -> fold_unfold_verify_aux_nil.
      intro H_h.
      discriminate H_h.

  - split.

    + intro h1.
      rewrite -> (fold_unfold_verify_aux_cons).
      intro H_h1.
      rewrite -> (fold_unfold_append_cons).
      rewrite -> (fold_unfold_verify_aux_cons).
      Check (IHbcis1' bcis2 h).
      destruct( IHbcis1' bcis2 (S h)) as [IHbcis1'_some _].
      Check (IHbcis1'_some h1 H_h1).
      rewrite -> (IHbcis1'_some h1 H_h1).
      reflexivity.

    + rewrite -> (fold_unfold_verify_aux_cons).
      intro H_h.
      rewrite -> (fold_unfold_append_cons).
      rewrite -> (fold_unfold_verify_aux_cons).
      Check (IHbcis1' bcis2 h).
      destruct( IHbcis1' bcis2 (S h)) as [_ IHbcis1'_none].
      Check (IHbcis1'_none H_h).
      exact (IHbcis1'_none H_h).

  - split.

    + intro h1.
      rewrite -> (fold_unfold_verify_aux_cons).
      destruct h as [|[| h'']].

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_h1.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         Check (IHbcis1' bcis2 (S h'')).
         destruct( IHbcis1' bcis2 (S h'')) as [IHbcis1'_some _].
         Check (IHbcis1'_some h1 H_h1).
         exact (IHbcis1'_some h1 H_h1).

    + rewrite -> (fold_unfold_verify_aux_cons).
      destruct h as [|[|h'']].

      -- intros _.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         reflexivity.

      -- intros _.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         reflexivity.

      -- intro H_h.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         destruct( IHbcis1' bcis2 (S h'')) as [_ IHbcis1'_none].
         Check (IHbcis1'_none H_h).
         exact (IHbcis1'_none H_h).

  - split.

    + intro h1.
      rewrite -> (fold_unfold_verify_aux_cons).
      destruct h as [|[| h'']].

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_h1.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         Check (IHbcis1' bcis2 (S h'')).
         destruct( IHbcis1' bcis2 (S h'')) as [IHbcis1'_some _].
         Check (IHbcis1'_some h1 H_h1).
         exact (IHbcis1'_some h1 H_h1).

    + rewrite -> (fold_unfold_verify_aux_cons).
      destruct h as [|[|h'']].

      -- intros _.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         reflexivity.

      -- intros _.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         reflexivity.

      -- intro H_h.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         destruct( IHbcis1' bcis2 (S h'')) as [_ IHbcis1'_none].
         Check (IHbcis1'_none H_h).
         exact (IHbcis1'_none H_h).

  - split.

    + intro h1.
      rewrite -> (fold_unfold_verify_aux_cons).
      destruct h as [|[| h'']].

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_h1.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         Check (IHbcis1' bcis2 (S h'')).
         destruct( IHbcis1' bcis2 (S h'')) as [IHbcis1'_some _].
         Check (IHbcis1'_some h1 H_h1).
         exact (IHbcis1'_some h1 H_h1).

    + rewrite -> (fold_unfold_verify_aux_cons).
      destruct h as [|[|h'']].

      -- intros _.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         reflexivity.

      -- intros _.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         reflexivity.

      -- intro H_h.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         destruct( IHbcis1' bcis2 (S h'')) as [_ IHbcis1'_none].
         Check (IHbcis1'_none H_h).
         exact (IHbcis1'_none H_h).

  - split.

    + intro h1.
      rewrite -> (fold_unfold_verify_aux_cons).
      destruct h as [|[| h'']].

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_absurd.
         discriminate H_absurd.

      -- intro H_h1.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         Check (IHbcis1' bcis2 (S h'')).
         destruct( IHbcis1' bcis2 (S h'')) as [IHbcis1'_some _].
         Check (IHbcis1'_some h1 H_h1).
         exact (IHbcis1'_some h1 H_h1).

    + rewrite -> (fold_unfold_verify_aux_cons).
      destruct h as [|[|h'']].

      -- intros _.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         reflexivity.

      -- intros _.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         reflexivity.

      -- intro H_h.
         rewrite -> (fold_unfold_append_cons).
         rewrite -> (fold_unfold_verify_aux_cons).
         destruct( IHbcis1' bcis2 (S h'')) as [_ IHbcis1'_none].
         Check (IHbcis1'_none H_h).
         exact (IHbcis1'_none H_h).

Qed.

      
        
      
      


Lemma about_verify_aux:
  forall (ae : arithmetic_expression)
         (h : nat),
    verify_aux (compile_aux ae ) h = Some (S h).
Proof.
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 |ae1 IHae1 ae2 IHae2 |ae1 IHae1 ae2 IHae2 ]; intro h.
  - rewrite -> fold_unfold_compile_aux_literal.
    rewrite -> fold_unfold_verify_aux_cons.
    rewrite -> fold_unfold_verify_aux_nil.
    reflexivity.

  - rewrite -> fold_unfold_compile_aux_plus.
    Check (byte_code_append_property_verify (compile_aux ae1) (compile_aux ae2) h).
    destruct (byte_code_append_property_verify (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) h) as [H1_some H1_none].
    Check (H1_some (S h) (IHae1 h)).
    rewrite (H1_some (S h) (IHae1 h)).
    destruct (byte_code_append_property_verify (compile_aux ae2) (ADD :: nil) (S h)) as [H2_some H2_none].
    Check (H2_some (S h)).
    Check (H2_some (S (S h)) (IHae2 (S h))).
    rewrite -> (H2_some (S (S h)) (IHae2 (S h))).
    rewrite -> (fold_unfold_verify_aux_cons).
    rewrite -> (fold_unfold_verify_aux_nil).
    reflexivity.

  - rewrite -> fold_unfold_compile_aux_minus.
    Check (byte_code_append_property_verify (compile_aux ae1) (compile_aux ae2) h).
    destruct (byte_code_append_property_verify (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) h) as [H1_some H1_none].
    Check (H1_some (S h) (IHae1 h)).
    rewrite (H1_some (S h) (IHae1 h)).
    destruct (byte_code_append_property_verify (compile_aux ae2) (SUB :: nil) (S h)) as [H2_some H2_none].
    Check (H2_some (S h)).
    Check (H2_some (S (S h)) (IHae2 (S h))).
    rewrite -> (H2_some (S (S h)) (IHae2 (S h))).
    rewrite -> (fold_unfold_verify_aux_cons).
    rewrite -> (fold_unfold_verify_aux_nil).
    reflexivity.

  - rewrite -> fold_unfold_compile_aux_multiply.
    Check (byte_code_append_property_verify (compile_aux ae1) (compile_aux ae2) h).
    destruct (byte_code_append_property_verify (compile_aux ae1) (compile_aux ae2 ++ MUL :: nil) h) as [H1_some H1_none].
    Check (H1_some (S h) (IHae1 h)).
    rewrite (H1_some (S h) (IHae1 h)).
    destruct (byte_code_append_property_verify (compile_aux ae2) (MUL :: nil) (S h)) as [H2_some H2_none].
    Check (H2_some (S h)).
    Check (H2_some (S (S h)) (IHae2 (S h))).
    rewrite -> (H2_some (S (S h)) (IHae2 (S h))).
    rewrite -> (fold_unfold_verify_aux_cons).
    rewrite -> (fold_unfold_verify_aux_nil).
    reflexivity.

  - rewrite -> fold_unfold_compile_aux_divide.
    Check (byte_code_append_property_verify (compile_aux ae1) (compile_aux ae2) h).
    destruct (byte_code_append_property_verify (compile_aux ae1) (compile_aux ae2 ++ DIV :: nil) h) as [H1_some H1_none].
    Check (H1_some (S h) (IHae1 h)).
    rewrite (H1_some (S h) (IHae1 h)).
    destruct (byte_code_append_property_verify (compile_aux ae2) (DIV :: nil) (S h)) as [H2_some H2_none].
    Check (H2_some (S h)).
    Check (H2_some (S (S h)) (IHae2 (S h))).
    rewrite -> (H2_some (S (S h)) (IHae2 (S h))).
    rewrite -> (fold_unfold_verify_aux_cons).
    rewrite -> (fold_unfold_verify_aux_nil).
    reflexivity.

Qed.




Theorem the_compiler_emits_well_behaved_code :
  forall sp : source_program,
    verify (compile sp) = true.
Proof.
  intros [ae].
  unfold verify, compile.
  Check ( about_verify_aux ae 0).
  rewrite -> ( about_verify_aux ae 0).
  reflexivity.
Qed.


  
  

(* Subsidiary question:
   What is the practical consequence of this theorem?
*)

(* ********** *)

(* Task 11:

   a. Write a Magritte interpreter for the source language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.

   b. Write a Magritte interpreter for the target language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.

   c. Prove that interpreting an arithmetic expression with the Magritte source interpreter
      gives the same result as first compiling it and then executing the compiled program
      with the Magritte target interpreter over an empty data stack.

   d. Prove that the Magritte target interpreter is (essentially)
      a left inverse of the compiler, i.e., it is a decompiler.
 *)


  
Fixpoint evaluate_magritte (ae : arithmetic_expression) : arithmetic_expression :=
  match ae with
  | Literal n =>
    Literal n
  | Plus ae1 ae2 =>
    Plus (evaluate_magritte ae1) (evaluate_magritte ae2)
  | Minus ae1 ae2 =>
    Minus (evaluate_magritte ae1)  (evaluate_magritte ae2)
  | Multiply ae1 ae2  =>
    Multiply (evaluate_magritte ae1) (evaluate_magritte ae2)
  | Divide ae1 ae2 =>
    Divide (evaluate_magritte ae1)  (evaluate_magritte ae2)
  end.


Lemma fold_unfold_evaluate_magritte_literal :
  forall (n : nat),
    evaluate_magritte ( Literal n ) = Literal n.
Proof.
  fold_unfold_tactic evaluate_magritte.
Qed.

Lemma fold_unfold_evaluate_magritte_plus:
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_magritte ( Plus ae1 ae2) =
    Plus (evaluate_magritte ae1) (evaluate_magritte ae2).
Proof.
  fold_unfold_tactic evaluate_magritte.
Qed.

Lemma fold_unfold_evaluate_magritte_minus:
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_magritte (Minus ae1 ae2) =
    Minus (evaluate_magritte ae1) (evaluate_magritte ae2).
Proof.
  fold_unfold_tactic evaluate_magritte.
Qed.

Lemma fold_unfold_evaluate_magritte_multiply:
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_magritte (Multiply ae1 ae2) =
    Multiply (evaluate_magritte ae1) (evaluate_magritte ae2).
Proof.
  fold_unfold_tactic evaluate_magritte.
Qed.

Lemma fold_unfold_evaluate_magritte_divide:
  forall (ae1 ae2 : arithmetic_expression),
    evaluate_magritte (Divide ae1 ae2) =
    Divide (evaluate_magritte ae1) (evaluate_magritte ae2).
Proof.
  fold_unfold_tactic evaluate_magritte.
Qed.

Lemma about_evaluate_magritte :
  forall ae : arithmetic_expression,
    evaluate_magritte ae = ae.
Proof.
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 |ae1 IHae1 ae2 IHae2 |ae1 IHae1 ae2 IHae2].

  - rewrite -> fold_unfold_evaluate_magritte_literal.
    reflexivity.

  - rewrite -> fold_unfold_evaluate_magritte_plus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.

  - rewrite -> fold_unfold_evaluate_magritte_minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.

  - rewrite -> fold_unfold_evaluate_magritte_multiply.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.

  - rewrite -> fold_unfold_evaluate_magritte_divide.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.

Qed.


Inductive expressible_value_magritte : Type :=
| Expressible_nat_magritte : arithmetic_expression -> expressible_value_magritte
| Expressible_msg_magritte : string -> expressible_value_magritte.

    
  

Compute (evaluate_magritte (Plus (Literal 2) (Minus (Literal 6) (Literal 5)))).

Definition interpret_magritte_s (sc : source_program) : expressible_value_magritte :=
  match sc with
  | Source_program ae =>
    Expressible_nat_magritte (evaluate_magritte ae)
  end.

Definition data_stack_magritte := list arithmetic_expression.

Inductive result_of_decoding_and_execution_magritte : Type :=
| OK_magritte : data_stack_magritte -> result_of_decoding_and_execution_magritte
| KO_magritte : string -> result_of_decoding_and_execution_magritte.


Definition decode_execute_magritte (bcis : byte_code_instruction) (ds : data_stack_magritte) : result_of_decoding_and_execution_magritte :=
match bcis with
  | PUSH n =>
    OK_magritte (Literal n :: ds)
  | ADD =>
    match ds with
    | nil =>
      KO_magritte "ADD: stack underflow"
    | ae1 :: nil =>
      KO_magritte "ADD: stack underflow"
    | ae2 :: ae1 :: ds'' =>
      OK_magritte ((Plus ae1 ae2 ) :: ds'')
    end
  | SUB =>
    match ds with
    | nil =>
      KO_magritte "SUB: stack underflow"
    | ae1  :: nil =>
      KO_magritte "SUB: stack underflow"
    | ae2  :: ae1 :: ds'' =>
        OK_magritte ((Minus ae1 ae2) :: ds'')
    end
  | MUL =>
    match ds with
    | nil =>
      KO_magritte "MUL: stack underflow"
    | ae1 :: nil =>
      KO_magritte "MUL: stack underflow"
    | ae2  :: ae1 :: ds'' =>
      OK_magritte ((Multiply ae1 ae2) :: ds'')
    end
  | DIV =>
    match ds with
    | nil =>
      KO_magritte "DIV: stack underflow"
    | ae1 :: nil =>
      KO_magritte "DIV: stack underflow"
    | ae2  :: ae1 :: ds'' =>
        OK_magritte ((Divide ae1 ae2) :: ds'')
    end
  end.




Fixpoint fetch_decode_execute_loop_magritte (bcis : list byte_code_instruction) (ds : data_stack_magritte) : result_of_decoding_and_execution_magritte :=
match bcis with
  |nil =>
   OK_magritte ds
  | bci :: bcis' =>
    match decode_execute_magritte bci ds with
    | OK_magritte ds' =>
      fetch_decode_execute_loop_magritte bcis' ds'
    | KO_magritte s =>
      KO_magritte s
    end
end.

Lemma fold_unfold_fetch_decode_execute_loop_magritte_nil :
  forall (ds : data_stack_magritte),
    fetch_decode_execute_loop_magritte nil ds = OK_magritte ds.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_magritte.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_magritte_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : data_stack_magritte),
    fetch_decode_execute_loop_magritte (bci :: bcis') ds =
    match decode_execute_magritte bci ds with
    | OK_magritte ds' =>
      fetch_decode_execute_loop_magritte bcis' ds'
    | KO_magritte s =>
      KO_magritte s
    end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop_magritte.
Qed.
    




Definition run_magritte (tp : target_program) : expressible_value_magritte :=
  match tp with
  | Target_program bcis =>
    match fetch_decode_execute_loop_magritte bcis nil with
    | OK_magritte nil =>
      Expressible_msg_magritte "no result on the data stack"
    | OK_magritte (ae :: nil) =>
      Expressible_nat_magritte ae               
    | OK_magritte (ae :: ae' :: ds'') =>
      Expressible_msg_magritte "too many results on the data stack"
    | KO_magritte s =>
      Expressible_msg_magritte s
    end
  end.

Proposition byte_code_append_property_magritte :
  forall (bcis1 bcis2 : list byte_code_instruction)
         (ds : data_stack_magritte),
    fetch_decode_execute_loop_magritte (bcis1 ++ bcis2) ds =
    match (fetch_decode_execute_loop_magritte bcis1 ds) with
    | OK_magritte ds' =>
      fetch_decode_execute_loop_magritte bcis2 ds'
    | KO_magritte s =>
      KO_magritte s
    end.
Proof.
  intros bcis1.
  induction bcis1 as [|bci1 bcis1' IHbcis1']; intros bcis2 ds.

  - rewrite -> (fold_unfold_fetch_decode_execute_loop_magritte_nil).
    rewrite -> (fold_unfold_append_nil).
    reflexivity.

  - rewrite -> (fold_unfold_append_cons).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_magritte_cons).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_magritte_cons).
    destruct (decode_execute_magritte bci1 ds) as [ds_OK|s_KO] eqn: H_ds.

    + rewrite -> (IHbcis1' bcis2 ds_OK).
      reflexivity.

    + reflexivity.

Qed.


Lemma capstone_aux_magritte :
  forall (ae : arithmetic_expression)
         (ds : data_stack_magritte),
    fetch_decode_execute_loop_magritte (compile_aux ae) ds = OK_magritte (ae :: ds).
Proof.
  intro ae.
  induction ae as [m | ae1 IHae1 ae2 IHae2| ae1 IHae1 ae2 IHae2| ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intros ds.

  - rewrite -> (fold_unfold_compile_aux_literal).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_magritte_cons).
    unfold decode_execute_magritte.
    rewrite -> (fold_unfold_fetch_decode_execute_loop_magritte_nil).
    reflexivity.

  - rewrite -> (fold_unfold_compile_aux_plus).
    Check (byte_code_append_property_magritte (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds).
    rewrite -> (byte_code_append_property_magritte (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) ds).
    Check ( IHae1 ds).
    rewrite -> ( IHae1 ds).
    rewrite -> (byte_code_append_property_magritte (compile_aux ae2)  (ADD :: nil) (ae1 :: ds)).
    rewrite -> (IHae2 (ae1 :: ds)).
    rewrite -> fold_unfold_fetch_decode_execute_loop_magritte_cons.
    unfold decode_execute_magritte.
    rewrite -> fold_unfold_fetch_decode_execute_loop_magritte_nil.
    reflexivity.

     - rewrite -> (fold_unfold_compile_aux_minus).
    Check (byte_code_append_property_magritte (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds).
    rewrite -> (byte_code_append_property_magritte (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) ds).
    Check ( IHae1 ds).
    rewrite -> ( IHae1 ds).
    rewrite -> (byte_code_append_property_magritte (compile_aux ae2)  (SUB :: nil) (ae1 :: ds)).
    rewrite -> (IHae2 (ae1 :: ds)).
    rewrite -> fold_unfold_fetch_decode_execute_loop_magritte_cons.
    unfold decode_execute_magritte.
    rewrite -> fold_unfold_fetch_decode_execute_loop_magritte_nil.
    reflexivity.

     - rewrite -> (fold_unfold_compile_aux_multiply).
    Check (byte_code_append_property_magritte (compile_aux ae1) (compile_aux ae2 ++ _ :: nil) ds).
    rewrite -> (byte_code_append_property_magritte (compile_aux ae1) (compile_aux ae2 ++ _ :: nil) ds).
    Check ( IHae1 ds).
    rewrite -> ( IHae1 ds).
    rewrite -> (byte_code_append_property_magritte (compile_aux ae2)  (_ :: nil) (ae1 :: ds)).
    rewrite -> (IHae2 (ae1 :: ds)).
    rewrite -> fold_unfold_fetch_decode_execute_loop_magritte_cons.
    unfold decode_execute_magritte.
    rewrite -> fold_unfold_fetch_decode_execute_loop_magritte_nil.
    reflexivity.

      - rewrite -> (fold_unfold_compile_aux_divide).
    Check (byte_code_append_property_magritte (compile_aux ae1) (compile_aux ae2 ++ _ :: nil) ds).
    rewrite -> (byte_code_append_property_magritte (compile_aux ae1) (compile_aux ae2 ++ _ :: nil) ds).
    Check ( IHae1 ds).
    rewrite -> ( IHae1 ds).
    rewrite -> (byte_code_append_property_magritte (compile_aux ae2)  (_ :: nil) (ae1 :: ds)).
    rewrite -> (IHae2 (ae1 :: ds)).
    rewrite -> fold_unfold_fetch_decode_execute_loop_magritte_cons.
    unfold decode_execute_magritte.
    rewrite -> fold_unfold_fetch_decode_execute_loop_magritte_nil.
    reflexivity.

Qed.

 (* aha wrong definition of decode, it should have been ae2 :: ae1 bc we deal with stack*)


Theorem capstone_magritte :
    forall (sp : source_program),
      interpret_magritte_s sp = run_magritte (compile sp).
Proof.
  intros [ae].
  unfold compile, interpret_magritte_s, run_magritte.
  Check (capstone_aux_magritte ae nil).
  rewrite -> (capstone_aux_magritte ae nil).
  rewrite -> (about_evaluate_magritte).
  reflexivity.
Qed.


  
Corollary run_magritte_is_a_left_inverse_of_compile :
  forall (ae : arithmetic_expression)
         (tp : target_program),
      compile (Source_program ae) = tp ->
      run_magritte tp = Expressible_nat_magritte ae.
Proof.
  intros ae tp H_tp.
  rewrite <- H_tp.
  Check (capstone_magritte (Source_program ae)).
  rewrite <- (capstone_magritte (Source_program ae)).
  unfold interpret_magritte_s.
  rewrite -> (about_evaluate_magritte).
  reflexivity.

Qed.
    


(* ********** *)

(* end of term-project.v *)
