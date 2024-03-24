Open Scope type_scope.
Section Iso_axioms.
Variables A B C : Set.
Axiom Com : A * B = B * A.
Axiom Ass : A * (B * C) = A * B * C.
Axiom Cur : (A * B -> C) = (A -> B -> C).
Axiom Dis : (A -> B * C) = (A -> B) * (A -> C).
Axiom P_unit : A * unit = A.
Axiom AR_unit : (A -> unit) = unit.
Axiom AL_unit : (unit -> A) = A.
End Iso_axioms.
Lemma isos_ex1 : forall A B :Set, A * (B -> unit) = A.
Proof.
intros.
rewrite AR_unit.
rewrite P_unit.
reflexivity.
Qed.


Lemma isos_ex2 : forall A B : Set, A * unit * B = B * (unit * A).
Proof.
intros.
rewrite (Com unit A). 
rewrite P_unit.
rewrite Com.
reflexivity.
Qed.

Lemma isos_ex3 : forall A B C : Set,
(A * unit -> B * (C * unit)) =
(A * unit -> (C -> unit) * C) * (unit -> A -> B).
Proof.
intros.
rewrite P_unit.
rewrite P_unit.
rewrite AR_unit.
rewrite (Com unit C).
rewrite P_unit.
rewrite AL_unit.
rewrite Dis.
rewrite (Com (A -> B) (A -> C)).
reflexivity.
Qed.

Ltac intro_equa :=
  intros;
  repeat (rewrite P_unit || rewrite AR_unit || rewrite AL_unit || rewrite AR_unit || rewrite Dis);
  try reflexivity.

Ltac Com_unit x :=
   rewrite (Com unit x);
   intro_equa.

Goal forall A B :Set, A * (B -> unit) = A.
Proof.
intro_equa.
Qed.

Goal forall A B : Set, A * unit * B = B * (unit * A).
Proof.
intro_equa.
Com_unit A.
rewrite Com.
reflexivity.
Qed.

Goal forall A B C : Set,
(A * unit -> B * (C * unit)) =
(A * unit -> (C -> unit) * C) * (unit -> A -> B).
Proof.
intro_equa.
Com_unit (A->C).
rewrite (Com (A -> B) (A -> C)).
reflexivity.
Qed.



Section Peano.
Parameter N : Set.
Parameter o : N.
Parameter s : N -> N.
Parameters plus mult : N -> N -> N.
Variables x y : N.
Axiom ax1 : ~((s x) = o).
Axiom ax2 : exists z, ~(x = o) -> (s z) = x.
Axiom ax3 : (s x) = (s y) -> x = y.
Axiom ax4 : (plus x o) = x.
Axiom ax5 : (plus x (s y)) = s (plus x y).
Axiom ax6 : (mult x o) = o.
Axiom ax7 : (mult x (s y)) = (plus (mult x y) x).
End Peano.


Hint Rewrite  ax4 ax5 ax6 ax7 : peano.

Ltac Sum :=
  repeat (rewrite ax5|| rewrite ax4);
  try reflexivity.


Ltac Mult:=
  repeat (rewrite ax7 || Sum || rewrite ax6);
  reflexivity.

Ltac Auto:=
  repeat(Sum || Mult).


Goal (plus (s o) (s(s o ))) = s(s(s(o))).
Proof.
Auto.
Qed.

Goal (plus (s(s(o))) (s(s(o)))) = s(s(s(s(o)))).
Proof.
Sum.
Qed.

Goal (mult (s(s(o))) (s(s(o)))) = s(s(s(s(o)))).
Proof.
Mult.
Qed.


Goal (mult (s(s(o))) (s(s(o)))) = s(s(s(s(o)))).
Proof.
autorewrite with peano using try reflexivity.
Qed.

