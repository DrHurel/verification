Print plus.
Print Nat.add.

Print S.
Check S(S O).

Print nat.

Print nat_ind.


Compute plus 2.
Compute plus 2 1.

Fixpoint mult2 (n : nat) (m : nat) {struct n} : nat :=
match n with
|0 => 0
|S(k) => plus (mult2 k m) m
end.

Compute mult2 3 2.

Compute mult2 40 3.
