Open Scope list.
Require Export List.
Import ListNotations.
Require Import Lia.
Parameter E: Set.
Inductive Form : Type :=
|Top : Form
|Bot : Form
|Symb:E -> Form
|Neg:Form -> Form
|And: Form -> Form -> Form
|Or: Form -> Form -> Form
|Imp: Form -> Form -> Form
|Equ: Form -> Form -> Form
.

Print Form_ind.




Fixpoint sub (l : Form) {struct l} : list Form :=
    match l with    
    |Top => [l]
    |Bot =>  [l]
    |Symb a => [l]
    |Neg f => l::(sub f)
    |And f q => l::(sub f)++(sub q)
    |Or f q=>  l::(sub f)++(sub q)
    |Imp f q=>  l::(sub f)++(sub q)
    |Equ f q => l::(sub f)++(sub q)
    end.


Fixpoint nbc (l : Form) {struct l} : nat :=
    match l with    
    |Top => 0
    |Bot =>  0
    |Symb a => 0
    |Neg f => 1+(nbc f)
    |And f q => 1+(nbc f)+(nbc q)
    |Or f q=>  1+(nbc f)+(nbc q)
    |Imp f q=>  1+(nbc f)+(nbc q)
    |Equ f q => 1+(nbc f)+(nbc q)
    end.


Inductive is_perm : list nat -> list nat ->  Prop :=
|is_perm_reflexive : forall l : list nat, is_perm l l 
|is_perm_cons : forall l1 l2 : list nat,forall e : nat, is_perm l1 l2 -> is_perm (e::l1) (e::l2)
|is_perm_append : forall e :nat ,forall l :list nat, is_perm (e::l) (l++[e])
|is_perm_sym : forall l1 l2 :list nat, is_perm l1 l2 -> is_perm l2 l1
|is_perm_trans :  forall l1 l2 l3 :list nat, is_perm l1 l2 -> is_perm l2 l3 -> is_perm l1 l3
.

Goal (is_perm [1;2;3] [3;2;1]).
Proof.
apply (is_perm_trans [1;2;3] [2;3;1] [3;2;1]).
apply is_perm_append.
apply (is_perm_trans [2;3;1] [3;1;2] [3;2;1]).
apply is_perm_append.
apply is_perm_cons.
apply is_perm_append.
Qed.

Inductive is_sorted : list nat -> Prop :=
|is_sorted_nil : is_sorted nil
|is_sorted_single : forall e :nat,is_sorted (e::nil)
|is_sorted_cons : forall e h : nat, forall q : list nat,e<=h-> is_sorted (h::q)-> is_sorted (e::(h::q))
.

Inductive is_fact : nat -> nat -> Prop :=
|is_fact_base : is_fact 0 1
|is_fact_induc : forall n m : nat,is_fact n m -> is_fact (S n) (mult (S n) m).

Fixpoint fact  (n : nat) {struct n}: nat :=
    match n with
    |0 => 1
    |S m => mult (S m) (fact m)
    end.

Goal is_fact 2 2.
Proof.
    apply (is_fact_induc 1 1). 
    apply (is_fact_induc 0 1). 
    apply is_fact_base.
Qed.


Goal is_fact 4 24.
Proof.
    apply (is_fact_induc 3 6). 
    apply (is_fact_induc 2 2). 
    apply (is_fact_induc 1 1). 
    apply (is_fact_induc 0 1). 
    apply is_fact_base.
Qed.

Print is_fact_ind.

Theorem Correction1 : forall n m : nat, fact n = m -> is_fact n m. (*correction*)
Proof.
induction n.
+
intro.
intro.
simpl.
rewrite <- H.
apply is_fact_base.
+
intro.
intro.
rewrite <- H.
simpl.
apply is_fact_induc .
apply IHn.
reflexivity.
Qed.


Theorem completude1: forall n m : nat,is_fact n m -> fact n = m . (*completude*)
Proof.
apply is_fact_ind.
+
simpl.
reflexivity.
+
intros.
simpl.
rewrite <- H0.
reflexivity.
Qed.

(*
Goal is_sorted [1;2;3].
Proof.
    apply is_sorted_cons.
    lia.
    apply is_sorted_cons.
    lia.
    apply is_sorted_single.
Qed.
*)

Require Import FunInd.
Functional Scheme fact_ind :=Induction for fact Sort Prop.
Print fact_ind.


Theorem Correction2 : forall n m : nat, fact n = m -> is_fact n m. (*correction*)
Proof.
induction n.
+
intro.
intro.
simpl.
rewrite <- H.
apply is_fact_base.
+
intro.
intro.
rewrite <- H.
simpl.
apply is_fact_induc .
apply IHn.
reflexivity.
Qed.
