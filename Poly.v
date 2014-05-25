Add LoadPath "C:\Projects\Coq".

Require Export Lists.
Require Export Case.

Inductive boollist :=
  | bool_nil
  | bool_cons: bool -> boollist -> boollist.

Inductive list (X: Type) :=
  | nil
  | cons: X -> list X -> list X.

Check nil.
Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X: Type) (l: list X) :=
  match l with
  | nil => 0
  | cons h t => S (length X t)
  end.

Example test_length1: length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Example test_length2: length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
reflexivity. Qed.

Fixpoint app (X: Type) (l1 l2: list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X: Type) (l: list X) (v: X) :=
  match l with
  | nil => cons X v l
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X: Type) (l: list X) :=
  match l with
  | nil => l
  | cons h t => snoc X (rev X t) h
  end.

Example test_rev1:
  rev nat (cons nat 1 (cons nat 2 (nil nat)))
    = cons nat 2 (cons nat 1 (nil nat)).
reflexivity. Qed.

Example test_rev2: rev bool (nil bool) = nil bool.
reflexivity. Qed.

Module MumbleBaz.

Inductive mumble :=
  | a
  | b: mumble -> nat -> mumble
  | c.
Inductive grumble (X: Type) :=
  | d: mumble -> grumble X
  | e: X -> grumble X.

(*
  d (b a 5) -- no
  d mumble (b a 5) -- yes
  d bool (b a 5) -- yes
  e bool true -- yes
  e mumble (b c 0) -- yes
  e bool (b c 0) -- no
  c -- no (according to the question).
*)

Inductive baz :=
  | x: baz -> baz
  | y: baz -> bool -> baz.

(* None *)

End MumbleBaz.

Fixpoint app' X l1 l2 :=
  match l1 with
  | nil => l2
  | cons h t => cons X h (app' X t l2)
  end.

Check app'.

Fixpoint length' (X: Type) (l: list X) :=
  match l with
  | nil => 0
  | cons h t => S (length' _ t)
  end.

Definition list123 := cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Check list123.
Check list123'.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l.
Arguments snoc {X} l v.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

Fixpoint length'' {X: Type} (l: list X) :=
  match l with
  | nil => 0
  | cons h t => S (length'' t)
  end.

Definition mynil: list nat := nil.
Check mynil.

Check @nil.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Definition list123'''' := [1;2;3].

Fixpoint repeat {X: Type} n count: list X :=
  match count with
  | O => []
  | S count' => n :: repeat n count'
  end.

Example test_repeat1: repeat true 3 = [true;true;true].
reflexivity. Qed.

Theorem nil_app:
  forall X (l: list X), app [] l = l.
reflexivity. Qed.

Theorem rev_snoc:
  forall X v (s: list X), rev (snoc s v) = v :: rev s.
Proof.
  intros.
  induction s as [| n s'].
  Case "s = []".
    reflexivity.
  Case "s = n :: s'".
    simpl.
    rewrite -> IHs'.
    reflexivity.
Qed.

Theorem rev_involutive:
  forall X (l: list X), rev (rev l) = l.
Proof.
  intros.
  induction l as [|x l'].
  Case "l = []".
    reflexivity.
  Case "l = x l'".
    simpl.
    rewrite -> rev_snoc.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem snoc_with_append:
  forall X (l1 l2: list X) v,
    snoc (l1 ++ l2) v = l1 ++ snoc l2 v.
Proof.
  intros.
  induction l1 as [|x l1'].
  Case "l1 = []".
    reflexivity.
  Case "l1 = x :: l1'".
    simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.

Inductive prod (X Y: Type) :=
  | pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y: Type} (p : X * Y) :=
  match p with
  | (x, _) => x
  end.

Definition snd {X Y} (p: X * Y) :=
  match p with
  | (_, y) => y
  end.

Fixpoint combine {X Y} (lx: list X) (ly: list Y) :=
  match lx, ly with
  | [], _ | _, [] => []
  | x::tx, y::ty => (x,y) :: combine tx ty
  end.

Check @combine.
Eval compute in combine [1;2] [false;false;true;true].

Fixpoint split {X Y} (l: list (X * Y)) :=
  match l with
  | [] => ([], [])
  | (x,y)::t =>
    let (xs, ys) := split t in
    (x :: xs, y :: ys)
  end.

Example test_split: split [(1,false); (2,false)] = ([1;2],[false;false]).
reflexivity. Qed.

Inductive option (X: Type) :=
  | Some : X -> option X
  | None.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint index {X} n (l: list X) :=
  match l, n with
  | [], _ => None
  | x :: _, 0 => Some x
  | _ :: t, S n' => index n' t
  end.

Example test_index1: index 0 [4;5;6;7] = Some 4.
reflexivity. Qed.
Example test_index2: index 1 [[1];[2]] = Some [2].
reflexivity. Qed.
Example test_index3: index 2 [true] = None.
reflexivity. Qed.

Definition hd_opt {X} (l: list X) :=
  match l with
  | [] => None
  | x :: _ => Some x
  end.

Check @hd_opt.

Example test_hd_opt1: hd_opt [1;2] = Some 1.
reflexivity. Qed.
Example test_hd_opt2: hd_opt [[1];[2]] = Some [1].
reflexivity. Qed.

Definition doit3times {X} (f: X -> X) n :=
  f (f (f n)).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
reflexivity. Qed.
Example test_doit3times': doit3times negb true = false.
reflexivity. Qed.

Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3: plus3 4 = 7.
reflexivity. Qed.
Example test_plus3': doit3times plus3 0 = 9.
reflexivity. Qed.
Example test_plus3'': doit3times (plus 3) 0 = 9.
reflexivity. Qed.

Definition prod_curry {X Y Z} (f: X * Y -> Z) x y :=
  f (x, y).

Definition prod_uncurry {X Y Z} (f: X -> Y -> Z) (p: X * Y) :=
  f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

(*
prod_curr: forall X Y Z, (X * Y -> Z) -> X -> Y -> Z.
prod_uncurry: forall X Y Z, (X -> Y -> Z) -> (X * Y) -> Z.
*)

Theorem uncurry_curry:
  forall X Y Z (f: X -> Y -> Z) x y,
    prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros.
  reflexivity.
Qed.

Theorem curry_uncurry:
  forall X Y Z (f: X * Y -> Z) p,
    prod_uncurry (prod_curry f) p = f p.
Proof.
  intros.
  destruct p.
  reflexivity.
Qed.

Fixpoint filter {X} (test: _ -> bool) (l: list X) :=
  match l with
  | [] => []
  | h::t =>
    if test h
    then h :: filter test t
    else filter test t
  end.

Check @filter. (* forall X : Type, (X -> bool) -> list X -> list X. *)

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
reflexivity. Qed.

Definition length_is_1 {X} (l: list X) :=
  match l with
  | [_] => true
  | _ => false
  end.

Example test_filter2:
  filter length_is_1 [[1;2];[3];[4];[5;6;7];[];[8]] = [[3];[4];[8]].
reflexivity. Qed.

Definition countoddmembers' l :=
  length (filter oddb l).

Check countoddmembers'.

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' [] = 0.
reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
reflexivity. Qed.

Example test_filter2':
  filter (fun l => beq_nat (length l) 1) [[1;2];[3];[4];[5;6;7];[];[8]] = [[3];[4];[8]].
reflexivity. Qed.

Definition filter_even_gt7 l :=
  filter (fun x => andb (evenb x) (ble_nat 8 x)) l.

Example test_filter_even_gt7_1:
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
reflexivity. Qed.
Example test_filter_even_gt7_2:
  filter_even_gt7 [5;2;6;19;129] = [].
reflexivity. Qed.

Definition partition {X} (f: X -> bool) l :=
  (filter f l, filter (fun v => negb (f v)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5],[2;4]).
reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([],[5;9;0]).
reflexivity. Qed.

Fixpoint map {X Y} (f: X -> Y) l :=
  match l with
  | [] => []
  | x::t => f x :: map f t
  end.

Example test_map1: map (plus 3) [2;0;2] = [5;3;5].
reflexivity. Qed.

Example test_map2: map oddb [2;1;2;5] = [false; true; false; true].
reflexivity. Qed.

Example test_map3: map (fun n => [evenb n; oddb n]) [2;1;2;5]
  = [[true; false]; [false; true]; [true; false]; [false; true]].
reflexivity. Qed.

Theorem snoc_app:
  forall X (l: list X) v, snoc l v = l ++ [v].
Proof.
  intros.
  induction l as [|n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Lemma map_app:
  forall X Y (f: X -> Y) l v, map f (l ++ [v]) = map f l ++ [f v].
Proof.
  intros.
  induction l as [|n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem map_rev:
  forall X Y (f: X -> Y) l, map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l as [| n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    rewrite -> snoc_app.
    rewrite -> snoc_app.
    rewrite -> map_app.
    rewrite -> IHl'.
    reflexivity.
Qed.

Fixpoint flat_map {X Y} (f: X -> list Y) l :=
  match l with
  | [] => []
  | h::t => f h ++ flat_map f t
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1;1;1;5;5;5;4;4;4].
Proof. reflexivity. Qed.

Definition option_map {X Y} (f: X -> Y) o :=
  match o with
  | None => None
  | Some x => Some (f x)
  end.

Fixpoint fold {X Y} (f: X -> Y -> Y) l b :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)
  end.

Eval compute in fold plus [1;2;3;4] 0.

Check (fold andb).

Example fold_example: fold mult [1;2;3;4] 1 = 24.
reflexivity. Qed.

Example fold_example': fold andb [true;true;false;true] true = false.
reflexivity. Qed.

Example fold_example''': fold app [[1]; []; [2;3];[4]] [] = [1;2;3;4].
reflexivity. Qed.

(* When the aggregation would be different then the individual elements
an example would be a function alleven: (nat -> bool -> bool) -> list nat -> bool.
*)

Definition constfun {X} x : nat -> X :=
  fun k => x.

Definition ftrue := constfun true.

Example constfun_example1: ftrue 0 = true.
reflexivity. Qed.

Example constfun_example2: (constfun 5) 99 = 5.
reflexivity. Qed.

Definition override {X} (f: nat -> X) k x :=
  fun k' => if beq_nat k k' then x else f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1: fmostlytrue 0 = true.
reflexivity. Qed.
Example override_example2: fmostlytrue 1 = false.
reflexivity. Qed.
Example override_example3: fmostlytrue 2 = true.
reflexivity. Qed.
Example override_example4: fmostlytrue 3 = false.
reflexivity. Qed.

Theorem override_example:
  forall b, override (constfun b) 3 true 2 = b.
Proof.
  intros.
  reflexivity.
Qed.

Theorem unfold_example_bad:
  forall m n, 3 + n = m -> plus3 n + 1 = m + 1.
Proof.
  intros.
Abort.

Theorem unfold_example:
  forall m n, 3 + n = m -> plus3 n + 1 = m + 1.
Proof.
  intros.
  unfold plus3.
  rewrite -> H.
  reflexivity.
Qed.

Theorem override_eq:
  forall {X} x k (f: nat -> X), override f k x k = x.
Proof.
  intros.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Definition fold_length {X} (l: list X) :=
  fold (fun _ => S) l 0.

Example test_fold_lengt1: fold_length [4;7;0] = 3.
reflexivity. Qed.

Theorem fold_length_correct:
  forall X (l: list X), fold_length l = length l.
Proof.
  intros.
  induction l as [|n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    rewrite <- IHl'.
    unfold fold_length.
    reflexivity.
Qed.

Definition fold_map {X Y} (f: X -> Y) l :=
  fold (fun v l' => f v :: l') l [].

Theorem fold_map_correct:
  forall X Y (f: X -> Y) l, fold_map f l = map f l.
Proof.
  intros.
  induction l as [|n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    rewrite <- IHl'.
    unfold fold_map.
    reflexivity.
Qed.