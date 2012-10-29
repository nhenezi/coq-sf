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

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Definition list123 := cons 1 (cons 2 (cons 3 nil)).
Check list123.

Definition mynil := @nil nat.
Check @nil.


Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  match count with
    | 0 => nil
    | S m => n :: repeat n m
  end.

Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
Proof. simpl. reflexivity.

Theorem nil_app : forall X:Type, forall l:list X,
  app [] l = l.
Proof.
  simpl. reflexivity.
Qed.

Theorem rev_snoc : forall X : Type,
                     forall v : X,
                     forall s : list X,
  rev (snoc s v) = v :: (rev s).
Proof.
  intros.
  induction s.
  simpl. reflexivity.
  simpl. rewrite -> IHs. simpl. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros.
  induction l.
  reflexivity.
  simpl. rewrite -> rev_snoc.  rewrite -> IHl. reflexivity.
Qed.

Theorem snoc_with_append : forall X : Type,
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros.
  induction l1.
  simpl. reflexivity.
  simpl. rewrite -> IHl1. reflexivity.
Qed.




Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Implicit Arguments pair [[X] [Y]].
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.
Check @combine.
Eval simpl in (combine [1,2] [false,false,true,true]).


Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Implicit Arguments Some [[X]].
Implicit Arguments None [[X]].

Fixpoint index {X : Type} (n : nat)
               (l : list X) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1 : index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1],[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.




Definition doit3times {X:Type} (f:X -> X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.
Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.


Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.



Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f(fst p)(snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                               (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros. destruct p.
  reflexivity.
Qed.


Fixpoint filter {X:Type} (test: X -> bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.


Example test_filter1: filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity. Qed.



Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0,2,4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Notation "x <= y " := (beq_nat x y).
Example test_filter2':
    filter (fun l => (length l) <= 1)
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity. Qed.


Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (ble_nat 7 n)) l.
Check filter_even_gt7.
Eval simpl in evenb 5.
Eval compute in filter_even_gt7 [1, 4, 5, 6, 7, 8, 9, 10].
Example test_filter_even_gt7_1 :
  filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof. compute. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5,2,6,19,129] = [].
Proof. simpl. compute. reflexivity. Qed.

Fixpoint map {X Y:Type} (f:X -> Y) (l:list X)
             : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (plus 3) [2,0,2] = [5,3,5].
Proof. simpl. compute. reflexivity. Qed.
Example test_map2: map oddb [2,1,2,5] = [false,true,false,true].
Proof. simpl. compute. reflexivity. Qed.

Example test_map3:
    map (fun n => [evenb n,oddb n]) [2,1,2,5]
  = [[true,false],[false,true],[true,false],[false,true]].
Proof. simpl. compute. reflexivity. Qed.

Theorem map_rev_1 : forall (X Y: Type) (f: X -> Y) (l : list X) (x : X),
  map f (snoc l x) = snoc (map f l) (f x).
Proof.
  intros.
  induction l.
  reflexivity.
  simpl.
  rewrite -> IHl.
  reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l.
  reflexivity.
  simpl. rewrite map_rev_1. rewrite <- IHl. reflexivity.
Qed.


Fixpoint fold {X Y:Type} (f: X -> Y -> Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.


Check (fold plus).
Eval simpl in (fold plus [1,2,3,4] 0).

Example fold_example1 : fold mult [1,2,3,4] 1 = 24.
Proof. simpl. compute. reflexivity. Qed.

Example fold_example2 : fold andb [true,true,false,true] true = false.
Proof. simpl. compute. reflexivity. Qed.

Example fold_example3 : fold app [[1],[],[2,3],[4]] [] = [1,2,3,4].
Proof. reflexivity. Qed.


Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n,o] = [n,p] ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2. Qed.