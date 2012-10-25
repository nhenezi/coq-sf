Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Example test1_negb : (negb true) = false.
Proof. simpl. reflexivity. Qed.
Example test2_negb : (negb false) = true.
Proof. simpl. reflexivity. Qed.

Definition andb (b1 b2:bool) :=
  match b1 with
    | true => b2
    | false => false
  end.

Example test1_andb : (andb true true) = true.
Proof. simpl. reflexivity. Qed.
Example test2_andb : (andb true false) = false.
Proof. simpl. reflexivity. Qed.
Example test3_andb : (andb false true) = false.
Proof. simpl. reflexivity. Qed.
Example test4_andb : (andb false false) = false.
Proof. simpl. reflexivity. Qed.


Definition orb (b1 b2 :bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.

Example test1_orb : (orb true true) = true.
Proof. simpl. reflexivity. Qed.
Example test2_orb : (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test3_orb : (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test4_odb : (orb false false) = false.
Proof. simpl. reflexivity. Qed.


(* Excercise 1, nandb *)
Definition nandb (b1 b2:bool) :=
  match b1 with
    | true => b2
    | false => negb(b2)
  end.

Example test1_nandb: (nandb true true) = true.
Proof. simpl. reflexivity. Qed.
Example test2_nandb: (nandb true false) = false.
Proof. simpl. reflexivity. Qed.
Example test3_nandb: (nandb false true) = false.
Proof. simpl. reflexivity. Qed.
Example test4_nandb: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.


(* Excercise 2, andb3 *)
Definition andb3 (b1 b2 b3:bool) : bool :=
  match b1 with
    | true => andb b2 b3
    | false => false
  end.


Example test1_andb3: (andb3 true true true) = true.
Proof.  reflexivity. Qed.
Example test2_andb3: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test3_andb3: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test4_andb3: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Notation "x || y" := (orb x y).
Check true || false.

Eval simpl in (pred O).

Definition minustwo (n :nat): nat :=
  match n with
    | O => O
    | S(O) => O
    | S(S(n')) => n'
  end.

Eval simpl in (minustwo 4).

Fixpoint evenb (n: nat): bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n: nat): bool := negb(evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S 0))))) = false.
Proof. simpl. reflexivity. Qed.

(*pitati vukovica
Function plus (n m: nat) {struct n}: nat :=
  match n, m with
    | 0, _ => m
    | _, 0 => n
    | S n', _ => S (plus n' m)
  end.
*)

Module playground2.

Fixpoint plus (n m : nat): nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.


Eval compute in (plus (S (S (S 0))) (S 0)).

Fixpoint minus (n m:nat): nat :=
  match n, m with
    | 0, _ => 0
    | S _, 0 => n
    | S n', S m' => minus n' m'
  end.

Example test_minus1: (minus 4 3) = 1.
Proof. simpl. reflexivity. Qed.
Example test_minus2: (minus 3 3) = 0.
Proof. simpl. reflexivity. Qed.
Example test_minus3: (minus 1 4) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint mult (n m: nat): nat :=
  match n with
    | O => 0
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 4) = 12.
Proof. simpl. reflexivity. Qed.

End playground2.

Fixpoint exp (base power: nat) :nat :=
  match power with
    | 0 => S(O)
    | S n' => mult base (exp base n')
  end.

Eval simpl in (exp 3 3).

Fixpoint factorial (n :nat) :nat :=
  match n with
    | O => S O
    | S O => S O
    | S m => mult n (factorial m)
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
     | O => true
     | S m' => false
     end
  | S n' => match m with
        | O => false
        | S m' => beq_nat n' m'
        end
  end.

Example beq_nat1: (beq_nat 3 4) = false.
Proof. reflexivity. Qed.
Example beq_nat2: (beq_nat 3 3) = true.
Proof. reflexivity. Qed.
Example beq_nat3: (beq_nat 0 1) = false.
Proof. reflexivity. Qed.
Example beq_nat4: (beq_nat 0 0) = true.
Proof. reflexivity. Qed.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.


Example ble_nat1: (ble_nat 4 4) = true.
Proof. simpl. reflexivity. Qed.
Example ble_nat2: (ble_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.
Eval simpl in (minus 2 4).
Example ble_nat3: (ble_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.



Definition blt_nat (n m :nat) : bool :=
  match (minus m n) with
    | S n' => true
    | O => false
  end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.


Theorem plus_0_n : forall n:nat, 0 + n = n.
Proof.
  compute. reflexivity. Qed.


Eval simpl in (forall n:nat, n + 0 = n).
Eval simpl in (forall n:nat, 0 + n = n).

(* 2. tjedan *)

Theorem plus_0_n'' : forall n:nat, 0 + n = n.
Proof.
  intros. reflexivity. Qed.

Theorem mult_0_n' : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_n' : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example: forall n m:nat,
  n = m -> n + m = m + n.
Proof.
  intros n m H.
  rewrite <- H.
  reflexivity. Qed.

Theorem plus_id_excercise: forall n m o: nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o h1 h2.
  rewrite -> h1.
  rewrite -> h2.
  reflexivity. Qed.

Theorem mult_0_plus: forall n m: nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite <- plus_O_n.
  simpl.
  reflexivity. Qed.


Theorem mult_1_plus: forall n m: nat,
  (1 + n) * m = m + n * m.
Proof.
  intros n m.
  simpl.
  reflexivity. Qed.

Theorem plus_1_neq_0: forall n: nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n.
  reflexivity.
  compute.
  reflexivity. Qed.

Theorem negb_involutive: forall b:bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  compute.
  reflexivity.
  reflexivity. Qed.

Theorem zero_nbeq_plus : forall n:nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [| n'].
  reflexivity.
  reflexivity. Qed.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity. Qed.

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n.
  induction n.
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn.
    reflexivity. Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros. induction n.
  Case "n = 0".
    reflexivity.
  Case "n = S n".
    simpl. rewrite -> IHn. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n.
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = S n".
    simpl. rewrite -> IHn. reflexivity. Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n.
  simpl. rewrite -> plus_0_r.
  reflexivity.

  simpl. rewrite -> IHn.
  rewrite -> plus_n_Sm.
  reflexivity. Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n.
  simpl. reflexivity.
  simpl. rewrite -> IHn.
  rewrite -> plus_n_Sm.
  reflexivity. Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.


Theorem beq_nat_refl: forall n: nat,
  true = beq_nat n n .
Proof.
  intro n.
  induction n.
  (* base: n = 0 *)
  reflexivity.
  (* suppose n = S n where true = beq_nat n n *)
  simpl.
  rewrite <- IHn.
  reflexivity.
Qed.


Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)...
     it seems like plus_comm should do the trick!  *)
  rewrite -> plus_comm.
  (* Doesn't work...Coq rewrote the wrong plus! *)
Admitted.


Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.
Qed.

Theorem plus_swap: forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  simpl.
  rewrite -> plus_assoc.
  assert (H: m + n = n + m).
    rewrite -> plus_comm. reflexivity.
  rewrite -> plus_assoc.
  rewrite -> H. reflexivity.
Qed.

Theorem mult_n_Sm : forall n m : nat, n * S m = n + n * m.
  Proof.
    intros n m.
    induction n.
    reflexivity.
    simpl.
    rewrite -> IHn.
    rewrite plus_swap.
    reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros m n.
  simpl.
  induction n.
    induction m.
      reflexivity.
      simpl. rewrite -> IHm. reflexivity.
  simpl. rewrite -> mult_n_Sm. rewrite -> IHn. reflexivity.
Qed.



Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n.
  simpl. reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  replace (n + m) with (m + n).
  reflexivity.
  rewrite -> plus_comm.
  reflexivity.
Qed.

