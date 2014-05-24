Add LoadPath "C:\Projects\Coq".

Require Export Induction.
Require Export Case.

Module NatList.

Inductive natprod :=
  | pair : nat -> nat -> natprod.

Definition fst a :=
  match a with
  | pair a _ => a
  end.

Definition snd v :=
  match v with
  | pair _ b => b
  end.

Eval compute in fst (pair 2 3).

Notation "( x , y )" := (pair x y).

Eval compute in fst(2, 3).

Definition fst' p :=
  match p with
  | (x, _) => x
  end.

Definition snd' p :=
  match p with
  | (_, y) => y
  end.

Definition swap_pair v :=
  match v with
  | (x, y) => (y, x)
  end.

Theorem surjective_pairing':
  forall n m, (n, m) = (fst (n, m), snd (n, m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing_stuck:
  forall p, p = (fst p, snd p).
Proof.
  destruct p.
  reflexivity.
Qed.

Theorem snd_fst_is_swap:
  forall p, (snd p, fst p) = swap_pair p.

  destruct p.
  reflexivity.
Qed.
  
Theorem fst_swap_is_snd:
  forall p, fst (swap_pair p) = snd p.
destruct p.
reflexivity.
Qed.

Inductive natlist :=
  | nil
  | cons: nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat n count :=
  match count with
  | O => nil
  | S count' => n :: repeat n count'
  end.

Eval compute in repeat 9 10.

Fixpoint length l :=
  match l with
  | nil => O
  | _ :: rest => S (length rest)
  end.

Fixpoint app l1 l2 :=
  match l1 with
  | [] => l2
  | x::rest => x :: app rest l2
  end.

Eval compute in app [1;2;3] (repeat 9 10).

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd default l :=
  match l with
  | [] => default
  | h :: _ => h
  end.

Definition tl l :=
  match l with
  | [] => []
  | _ :: t => t
  end.

Fixpoint nonzeros l :=
  match l with
  | [] => []
  | 0 :: rest => nonzeros rest
  | x :: rest => x :: nonzeros rest
  end.

Fixpoint oddmembers l :=
  match l with
  | [] => []
  | n :: rest =>
    if oddb n then
      n :: oddmembers rest
    else
      oddmembers rest
  end.

Definition countoddmembers l :=
  length (oddmembers l).

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
reflexivity. Qed.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
reflexivity. Qed.

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
reflexivity. Qed.

Fixpoint alternate l1 l2 :=
  match l1, l2 with
  | [], l
  | l, [] => l
  | x :: xs, y :: ys => x :: y :: alternate xs ys
  end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
reflexivity. Qed.
Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
reflexivity. Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
reflexivity. Qed.
Example test_alternate4: alternate [] [20;30] = [20;30].
reflexivity. Qed.

Definition bag := natlist.

Fixpoint count v s :=
  match s with
  | [] => O
  | x :: xs =>
    if beq_nat v x then
      S (count v xs)
    else
      count v xs
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
reflexivity. Qed.

Definition add v s : bag := v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
reflexivity. Qed.

Definition member v (s: bag) :=
  ble_nat 1 (count v s).

Example test_member1: member 1 [1;4;1] = true.
reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
reflexivity. Qed.

Fixpoint remove_one v s : bag :=
  match s with
  | [] => []
  | x :: xs =>
    if beq_nat x v
    then xs
    else x :: remove_one v xs
  end.



















































































