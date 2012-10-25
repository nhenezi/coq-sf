Require Export numbers.

Module NatList.

Inductive natprod: Type :=
  pair : nat -> nat -> natprod.
Eval simpl in (pair 2 3).

Notation "( x , y )" := (pair x y).

Definition fst (p :natprod) :nat :=
  match p with
    | (x,y) => x
  end.
Definition snd (p :natprod) :nat :=
  match p with
    | (x,y) => y
  end.

Definition swap_pair (p :natprod) :natprod :=
  match p with
    | (x,y) => (y,x)
  end.

Example swap_pair_test1: swap_pair (3,4) = (4,3).
Proof. simpl. reflexivity. Qed.


Theorem surjective_pairing': forall (n m :nat),
  (n,m) = (fst (n,m), snd(n,m)).
Proof.
  simpl. reflexivity. Qed.

Theorem surjective_pairing: forall (p :natprod),
  p = (fst p, snd p).
Proof.
  intros. destruct p as (n,m). rewrite <- surjective_pairing'. reflexivity.
Qed.

Theorem snd_fst_is_swap: forall (p :natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros. destruct p as (n,m). simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros. destruct p as (n,m). simpl. reflexivity.
Qed.

Inductive natlist :Type :=
  | nil :natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count :nat) :natlist :=
  match count with
    | 0 => nil
    | S count' => n :: (repeat n count')
  end.

Fixpoint length (l :natlist) :nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 :natlist) :natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1: [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4,5] = [4,5].
Proof. reflexivity. Qed.
Example test_app3: [1,2,3] ++ nil = [1,2,3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tail (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1,2,3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tail: tail [1,2,3] = [2,3].
Proof. reflexivity. Qed.


Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
    | nil => nil
    | 0 :: t => nonzeros t
    | h :: t => h :: (nonzeros t)
  end.

Example test_nonzeros: nonzeros [0,1,0,2,3,0,0] = [1,2,3].
Proof.
  simpl. reflexivity.
Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t =>
      match (oddb h) with
        | true => h :: (oddmembers t)
        | false => (oddmembers t)
      end
  end.

Example test_oddmembers: oddmembers [0,1,0,2,3,0,0] = [1,3].
Proof.
  simpl. reflexivity.
Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  match l with
    | nil => 0
    | h :: t =>
      match (oddb h) with
        | true => S (countoddmembers t)
        | false => (countoddmembers t)
      end
  end.

Definition countodd (l :natlist) :nat :=
  length(oddmembers l).

Example test_countodd: countodd [1,0,3,1,4,5] = 4.
Proof.
  simpl. reflexivity.
Qed.

Example test_countoddmembers1: countoddmembers [1,0,3,1,4,5] = 4.
Proof.
  simpl. reflexivity.
Qed.

Example test_countoddmembers2: countoddmembers [0,2,4] = 0.
Proof.
  simpl. reflexivity.
Qed.

Example test_countoddmembers3: countoddmembers nil = 0.
Proof.
  simpl. reflexivity.
Qed.

Fixpoint alternate (l1 l2 :natlist) :natlist :=
  match l1, l2 with
    | nil, l => l
    | l , nil => l
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
  end.
(*
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
    | nil => l2
    | h1 :: t1 =>
      match l2 with
        | nil => l1
        | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
      end
  end.
*)

Example test_alternate1: alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
Proof.
  simpl. reflexivity.
Qed.
Example test_alternate2: alternate [1] [4,5,6] = [1,4,5,6].
Proof.
  simpl. reflexivity.
Qed.
Example test_alternate3: alternate [1,2,3] [4] = [1,4,2,3].
Proof.
  simpl. reflexivity.
Qed.
Example test_alternate4: alternate [] [20,30] = [20,30].
Proof.
  simpl. reflexivity.
Qed.

Definition bag := natlist.

Fixpoint count (n :nat) (s :bag) : nat :=
  match s with
    | nil => 0
    | h :: t =>
      match (beq_nat h n) with
        | true => S(count n t)
        | false => count n t
      end
  end.

Example test_count1: count 1 [1,2,3,1,4,1] = 3.
Proof.
  simpl. reflexivity.
Qed.
Example test_count2: count 6 [1,2,3,1,4,1] = 0.
Proof.
  simpl. reflexivity.
Qed.


Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
Proof.
  simpl. reflexivity.
Qed.

Definition add : nat -> bag ->  bag := cons.

Example test_add1: count 1 (add 1 [1,4,1]) = 3.
Proof.
  simpl. reflexivity.
Qed.
Example test_add2: count 5 (add 1 [1,4,1]) = 0.
Proof.
  simpl. reflexivity.
Qed.

Definition member (n:nat) (s:bag) : bool :=
  match (count n s) with
    | 0 => false
    | _ => true
  end.

Example test_member1: member 1 [1,4,1] = true.
Proof.
  simpl. reflexivity.
Qed.

Example test_member2: member 2 [1,4,1] = false.
Proof.
  simpl. reflexivity.
Qed.


Fixpoint remove_one (n:nat) (s:bag) : bag :=
  match s with
    | nil => nil
    | h :: t => 
      match (beq_nat n h) with
        | true => t
        | false => h :: (remove_one n t)
      end
  end.

Example test_remove_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
Proof.
  simpl. reflexivity.
Qed.

Example test_remove_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
Proof.
  simpl. reflexivity.
Qed.

Example test_remove_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
Proof.
  simpl. reflexivity.
Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
Proof.
  simpl. reflexivity.
Qed.

(*
Fixpoint remove_all (n :nat) (s :bag) : bag :=
  match (count n s) with
    | 0 => s
    | _ => remove_all n (remove_one n s)
  end.
*)
  
Fixpoint remove_all (n :nat) (s :bag) :bag :=
  match s with
    | nil => nil
    | h :: t =>
      match (beq_nat n h) with
        | true => remove_all n t
        | false => h :: remove_all n t
      end
  end.

Eval simpl in (remove_all 5 [1,2,3,4,5]).
Eval simpl in (remove_all 5 [1,2,5,5,5,5,4]).
Example test_remove_all1: count 5 (remove_all 5 [2,1,5,4,1]) = 0.
Proof.
  simpl. reflexivity.
Qed.

Example test_remove_all2: count 5 (remove_all 5 [2,1,4,1]) = 0.
Proof.
  simpl. reflexivity.
Qed.

Example test_remove_all3: count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
Proof.
  simpl. reflexivity.
Qed.

Example test_remove_all4: count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
Proof.
  simpl. reflexivity.
Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
    | nil => true
    | h :: t => 
      if (member h s2)
        then subset t (remove_one h s2)
      else
        false
  end.

Example test_subset1: subset [1,2] [2,1,4,1] = true.
Proof.
  simpl. reflexivity.
Qed.

Example test_subset2: subset [1,2,2] [2,1,4,1] = false.
Proof.
  simpl. reflexivity.
Qed.


Theorem nil_app: forall l:natlist,
  [] ++ l = l.
Proof.
  simpl. reflexivity.
Qed.

Theorem tl_length_pred: forall l:natlist,
  pred (length l) = length (tail l).
Proof.
  destruct l.
  (* list is empty *)
  simpl. reflexivity.
  (* non empty list *)
  simpl. reflexivity.
Qed.
(*
Proof.
  induction l.
   (* empty list *)
    simpl. reflexivity.
   (* non empty list *)
    simpl. reflexivity.
Qed.
*)
Theorem app_ass: forall l1 l2 l3 :natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros.
  induction l1.
  (* l1 is empty lis, i.e. nill *)
  simpl. reflexivity.
  (* li is non empty, i.e. in t :: h form *)
  simpl. rewrite -> IHl1. reflexivity.
Qed.

Theorem app_length: forall l1 l2 :natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros.
  induction l1.
  (* l1 is nill *)
  simpl. reflexivity.
  (* l1 = h :: t *)
  simpl. rewrite -> IHl1. reflexivity.
Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
    | nil => [v]
    | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l :natlist) :natlist :=
  match l with
    | nil => nil
    | h :: t => snoc (rev t) h
  end. 

Example test_rev1: rev [1,2,3] = [3,2,1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros. induction l.
  (* l = nil *)
  reflexivity.
  (* l = h :: t *)
  simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l.
  (* l = nil *)
  reflexivity.
  (* l = h :: t *)
  simpl. rewrite -> length_snoc.
  rewrite -> IHl. reflexivity.
Qed.

Theorem app_nil_end : forall l : natlist, 
  l ++ [] = l.
Proof.
  induction l.
  simpl. reflexivity.
  simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem rev_snoc : forall (n:nat) (l:natlist),
  rev (snoc l n)   = n :: (rev l).
Proof.
  intros n l.
  induction l.
  reflexivity.
  simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros. induction l.
  simpl. reflexivity.
  simpl. rewrite -> rev_snoc. rewrite -> IHl. reflexivity.
Qed.
 
Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  induction l1.
  simpl. rewrite -> app_ass. reflexivity.
  simpl. rewrite -> IHl1. rewrite -> app_ass. reflexivity.
Qed.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros.
  induction l.
  simpl. reflexivity.
  simpl. rewrite -> IHl. reflexivity.
Qed.

Lemma snoc_app: forall (l1 l2:natlist) (n:nat),
 snoc (l1 ++ l2) n = l1 ++ snoc l2 n.
Proof.
  intros l1 l2 n.
  induction l1.
  reflexivity.
  simpl. rewrite -> IHl1. reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros.
  induction l1.
  simpl. rewrite -> app_nil_end. reflexivity.
  simpl. rewrite -> IHl1. rewrite -> snoc_app. reflexivity.
Qed.

Lemma nonzeros_length : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| h l1].
  reflexivity.
  destruct h.
    simpl. rewrite -> IHl1. reflexivity.
    simpl. rewrite -> IHl1. reflexivity.
Qed.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None 
  | a :: l' => match beq_nat n O with 
               | true => Some a
               | false => index (pred n) l' 
               end
  end.


Example test_index1 : index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 3 [4,5,6,7] = Some 7.
Proof. reflexivity. Qed.
Example test_index3 : index 10 [4,5,6,7] = None.
Proof. reflexivity. Qed.

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None 
  | a :: l' => if beq_nat n O then Some a else index' (pred n) l'
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.


End NatList.