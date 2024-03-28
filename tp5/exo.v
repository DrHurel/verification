Require Import Arith.
Require Import List.
Open Scope list_scope.
Import ListNotations.
Require Import Lia.


(* Exo 1 *)

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

Goal (is_perm [1;2;3;4] [3;1;4;2]).
Proof.
    apply (is_perm_trans  [1;2;3;4] [1;3;4;2] [3;1;4;2]).
    +
    apply is_perm_cons.    
    apply is_perm_append.
    +
    apply is_perm_sym.
    apply (is_perm_trans [3;1;4;2] [3;4;2;1] [1;3;4;2]).
    apply is_perm_cons.
    apply is_perm_append.
    apply is_perm_sym.
    apply is_perm_append.
Qed.



Inductive is_sorted : list nat -> Prop :=
|is_sorted_nil : is_sorted nil
|is_sorted_single : forall e :nat,is_sorted (e::nil)
|is_sorted_cons : forall e h : nat, forall q : list nat,e<=h-> is_sorted (h::q)-> is_sorted (e::(h::q))
.

Goal is_sorted [1;2;3].
Proof.
    apply (is_sorted_cons).
    +
    lia.
    +
    apply (is_sorted_cons).
    lia.
    apply is_sorted_single.
Qed.

(* EXO 2*)



