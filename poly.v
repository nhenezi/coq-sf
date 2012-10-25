Require Export lists.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check nil.
Check cons.

Check cons nat 1 (cons nat 3 (nil nat)).

Fixpoint length {X:Type} (l:list X) : nat := 
  match l with
  | nil => 0
  | cons h t => S (length t)
  end.

Example test_length1 :
    length (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.

Example test_length2 :
    length (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app {X : Type} (l1 l2 : list X) 
                : (list X) := 
  match l1 with
  | nil => l2
  | cons h t => cons X h (app t l2)
  end.

Fixpoint snoc {X:Type} (l:list X) (v:X) : (list X) := 
  match l with
  | nil => cons X v (nil X)
  | cons h t => cons X h (snoc t v)
  end.

Fixpoint rev {X:Type} (l:list X) : list X := 
  match l with
  | nil => nil X
  | cons h t => snoc (rev t) h
  end.

Example test_rev1 :
    rev (cons nat 1 (cons nat 2 (nil nat))) 
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.

Example test_rev2: 
  rev (nil bool) = nil bool.
Proof. reflexivity. Qed.