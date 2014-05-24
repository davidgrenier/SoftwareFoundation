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

Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
reflexivity. Qed.
Example test_remove_one_4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
reflexivity. Qed.

Fixpoint remove_all v (s: bag) :=
  match s with
  | [] => []
  | x :: xs =>
    if beq_nat x v
    then remove_all v xs
    else x :: remove_all v xs
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
reflexivity. Qed.

Fixpoint subset (s1: bag) (s2: bag) :=
  match s1 with
  | [] => true
  | x :: xs =>
    if member x s2
    then subset xs (remove_one x s2)
    else false
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
reflexivity. Qed.

Theorem beq_nat_refl:
  forall n, beq_nat n n = true.
induction n. reflexivity. simpl. rewrite -> IHn. reflexivity. Qed.

Theorem add_count:
  forall n s, count n (add n s) = S (count n s).
Proof.
  intros.
  induction s as [|s'].
  simpl.
  rewrite -> beq_nat_refl.
  reflexivity.
  simpl.
  rewrite -> beq_nat_refl.
  reflexivity.
Qed.

Theorem nil_app:
  forall l, [] ++ l = l.
reflexivity. Qed.

Theorem tl_length_pred:
  forall l, pred (length l) = length (tl l).
Proof.
  destruct l as [|n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    reflexivity.
Qed.

Theorem app_ass:
  forall l1 l2 l3, (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3.
Proof.
  intros.
  induction l1 as [|n l1'].
  Case "l1 = []".
    reflexivity.
  Case "l1 = n :: l1'".
    simpl. rewrite -> IHl1'.
    reflexivity.
Qed.

Theorem app_length:
  forall l1 l2, length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1 as [|n l1'].
  Case "l1 = []".
    reflexivity.
  Case "l1 = n :: l1'".
    simpl. rewrite -> IHl1'.
    reflexivity.
Qed.

Fixpoint snoc l v :=
  match l with
  | [] => [v]
  | h :: t => h :: snoc t v
  end.

Fixpoint rev l :=
  match l with
  | [] => []
  | h :: t => snoc (rev t) h
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
reflexivity. Qed.
Example test_rve2: rev [] = [].
reflexivity. Qed.

Theorem rev_length_firsttry:
  forall l, length (rev l) = length l.
Proof.
  intro.
  induction l as [| n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    rewrite <- IHl'.
Abort.

Theorem length_snoc:
  forall n l, length (snoc l n) = S (length l).
Proof.
  intros.
  induction l as [|n' l'].
  Case "l = []".
    reflexivity.
  Case "l = n' :: l'".
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem rev_length:
  forall l, length (rev l) = length l.
Proof.
  intro.
  induction l as [|n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    rewrite -> length_snoc.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem app_nil_end:
  forall l, l ++ [] = l.
Proof.
  intro.
  induction l as [|n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem app_ass4:
  forall l1 l2 l3 l4, l1 ++ l2 ++ l3 ++ l4 = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  rewrite -> app_ass.
  rewrite -> app_ass.
  reflexivity.
Qed.

Theorem snoc_append:
  forall l n, snoc l n = l ++ [n].
Proof.
  intros.
  induction l as [|n' l'].
  Case "l = []".
    reflexivity.
  Case "l = n' :: l'".
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem distr_rev:
  forall l1 l2, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1 as [|n l1'].
  Case "l1 = []".
    simpl.
    rewrite -> app_nil_end.
    reflexivity.
  Case "l1 = n :: l1'".
    simpl.
    rewrite -> IHl1'.
    rewrite -> snoc_append.
    rewrite -> snoc_append.
    rewrite -> app_ass.
    reflexivity.
Qed.

Lemma nonzeros_app:
  forall l1 l2, nonzeros (l1 ++ l2) = nonzeros l1 ++ nonzeros l2.
Proof.
  intros.
  induction l1 as [|n l1'].
  Case "l1 = []".
    reflexivity.
  Case "l1 = n :: l1'".
    destruct n as [|n'].
    SCase "n = 0".
      simpl.
      rewrite -> IHl1'.
      reflexivity.
    SCase "n = S n'".
      simpl.
      rewrite -> IHl1'.
      reflexivity.
Qed.

Theorem snoc_pow:
  forall n m l, cons n (snoc l m) = n :: l ++ [m].
Proof.
  intros.
  rewrite -> snoc_append.
  reflexivity.
Qed.

Theorem count_member_nonzero:
  forall (s: bag), ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  intro.
  reflexivity.
Qed.

Theorem ble_n_Sn:
  forall n, ble_nat n (S n) = true.
Proof.
  intro n.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem remove_decreases_count:
  forall (s: bag),
    ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intro s.
  induction s as [|n s'].
  Case "s = []".
    reflexivity.
  Case "s = n :: s'".
    destruct n as [|n'].
    simpl.
    rewrite -> ble_n_Sn.
    reflexivity.
    simpl.
    rewrite -> IHs'.
    reflexivity.
Qed.

Theorem count_distr:
  forall n l1 l2, count n (sum l1 l2) = count n l1 + count n l2.
Proof.
  intros.
  induction l1 as [|n' l1'].
  Case "l1 = []".
    reflexivity.
  Case "l1 = n' :: l1'".
    replace (sum (n' :: l1') l2) with (n' :: sum l1' l2).
    simpl.
    rewrite -> IHl1'.
    destruct (beq_nat n n').
    reflexivity.
    reflexivity.
    reflexivity.
Qed.

Theorem rev_involutive:
  forall l, rev (rev l) = l.
Proof.
  intro l.
  induction l as [|n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    rewrite -> snoc_append.
    rewrite -> distr_rev.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem rev_injective:
  forall l1 l2, rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2.
  intro H.
  induction l1 as [|n l1'].
  Case "l1 = []".
    replace l2 with (rev (rev l2)).
    rewrite <- H.
    reflexivity.
    rewrite -> rev_involutive.
    reflexivity.
  Case "l1 = n :: l1'".
    replace (n :: l1') with (rev (rev (n :: l1'))).
    rewrite <- rev_involutive.
    rewrite -> H.
    reflexivity.
    rewrite -> rev_involutive.
    reflexivity.
Qed.

Theorem rev_injective_easy:
  forall l1 l2, rev l1 = rev l2 -> l1 = l2.
Proof.
  intros.
  replace l1 with (rev (rev l1)).
  replace l2 with (rev (rev l2)).
  rewrite -> H.
  reflexivity.
  rewrite -> rev_involutive.
  reflexivity.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

Theorem rev_injective_easier:
  forall l1 l2, rev l1 = rev l2 -> l1 = l2.
Proof.
  intros.
  replace l1 with (rev (rev l1)).
  rewrite -> H.
  rewrite -> rev_involutive.
  reflexivity.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

Theorem rev_injective_easiest:
  forall l1 l2, rev l1 = rev l2 -> l1 = l2.
intros.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

(*
It would seem I skipped writing rev_involutive on first reading
and thus only came up with the idea of solving that first when
going through my first solution to rev_injective. As you can see
I took down a heavy path on my first go which took multiple attempts
to get to the simplest solution. Yet it might be possible that my
first solution (using involution anyway) could be easier than the
so call hard way.
*)

Inductive natoption :=
  | Some: nat -> natoption
  | None.

Fixpoint index_bad n l :=
  match l with
  | [] => 43
  | a :: l' =>
    if beq_nat n 0
    then a
    else index_bad (pred n) l'
  end.

Fixpoint index n l :=
  match n, l with
  | _, [] => None
  | 0, a :: l' => Some a
  | S n', _ :: l' => index n' l'
  end.

Example test_index1: index 0 [4;5;6;7] = Some 4.
reflexivity. Qed.
Example test_index2: index 3 [4;5;6;7] = Some 7.
reflexivity. Qed.
Example test_index3: index 10 [1;2;3] = None.
reflexivity. Qed.

Definition option_elim d o :=
  match o with
  | Some v => v
  | None => d
  end.

Definition hd_opt l :=
  match l with
  | [] => None
  | x :: _ => Some x
  end.

Example test_hd_opt1: hd_opt [] = None.
reflexivity. Qed.
Example test_hd_opt2: hd_opt [1] = Some 1.
reflexivity. Qed.
Example test_hd_opt3: hd_opt [5;6] = Some 5.
reflexivity. Qed.

Theorem option_elim_hd:
  forall l default, hd default l = option_elim default (hd_opt l).
Proof.
  intros.
  destruct l.
  reflexivity.
  reflexivity.
Qed.

Fixpoint beq_natlist l1 l2 :=
  match l1, l2 with
  | [], [] => true
  | [], _ | _, [] => false
  | a :: l1', b :: l2' =>
     andb (beq_nat a b) (beq_natlist l1' l2')
  end.

Example test_beq_natlist1: beq_natlist nil [] = true.
reflexivity. Qed.
Example test_beq_natlist2: beq_natlist [1;2;3] [1;2;3] = true.
reflexivity. Qed.
Example test_beq_natlist3: beq_natlist [1;2;3] [1;2;4] = false.
reflexivity. Qed.

Theorem beq_natlist_refl:
  forall l, true = beq_natlist l l.
Proof.
  intro l.
  induction l as [|n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    simpl. rewrite -> IHl'.
    rewrite -> beq_nat_refl.
    reflexivity.
Qed.

Module Dictionary.

Inductive dict :=
  | empty
  | record: nat -> nat -> dict -> dict.

Definition insert k v d := record k v d.

Fixpoint find k d :=
  match d with
  | empty => None
  | record k' v d' =>
    if beq_nat k k'
    then Some v
    else find k d'
  end.

Theorem dictionary_invariant1':
  forall d k v, find k (insert k v d) = Some v.
Proof.
  intros.
  simpl.
  rewrite -> beq_nat_refl.
  reflexivity.
Qed.

Theorem dictionary_invarian2':
  forall d m n o,
    beq_nat m n = false -> find m d = find m (insert n o d).
Proof.
  intros.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

End Dictionary.

End NatList.














































































