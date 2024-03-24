Open Scope list.
Require Export List.
Import ListNotations.

Print list.
Print list_ind. 

Check [2;3].

Check [].

Check cons 2 (cons (S 2) nil).

Print app.

Compute [2;3]++[32].



Fixpoint rev (l : list nat) {struct l} : list nat :=
    match l with
    | [] => l
    | h::t => (rev t)++[h]
    end.

Compute rev [2;3;4].

