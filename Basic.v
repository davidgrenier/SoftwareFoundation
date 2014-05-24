Definition negb b :=
  match b with
  | true => false
  | false => true
  end.

Definition andb b1 b2 :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb b1 b2 :=
  match b1 with
  | true => true
  | false => b2
  end.

Definition nandb b1 b2 :=
  match b1 with
  | true => negb b2
  | false => true
  end.

Example test_nandb1: nandb true false = true.
Proof. reflexivity. Qed.
Example test_nandb2: nandb false false = true.
Proof. reflexivity. Qed.
Example test_nandb3: nandb false true = true.
Proof. reflexivity. Qed.
Example test_nandb4: nandb true true = false.
Proof. reflexivity. Qed.

Definition andb3 b1 b2 b3 :=
  match b1 with
  | true => andb b2 b3
  | false => false
  end.

Check true.
Check andb.
Check andb3.

Definition minustwo n :=
  match n with
  | O | S O => O
  | S (S n') => n'
  end.

Eval simpl in minustwo 4.

Check S.
Check O.
Check pred.

Fixpoint evenb n :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb n := negb (evenb n).
Example test_oddb1: oddb (S O) = true.
Proof. reflexivity. Qed.
Example test_oddb2: oddb (S (S (S (S O)))) = false.
Proof. reflexivity. Qed.

Check plus.
Check mult.
Check minus.

Fixpoint exp base power :=
  match power with
  | O => S O
  | S p' => mult base (exp base p')
  end.

Example test_exp1: exp 2 3 = 8.
Proof. reflexivity. Qed.

Fixpoint factorial n :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: factorial 3 = 6.
Proof. reflexivity. Qed.
Example test_factorial2: factorial 5 = mult 10 12.
Proof. reflexivity. Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity): nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity): nat_scope.

Eval simpl in 0 - 1 + 2.

Fixpoint beq_nat n m :=
  match n, m with
  | O, O => true
  | O, _ | _, O => false
  | S n', S m' => beq_nat n' m'
  end.

Fixpoint ble_nat n m :=
  match n, m with
  | O, _ => true
  | _, O => false
  | S n', S m' => ble_nat n' m'
  end.

Example test_ble_nat1: ble_nat 2 2 = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: ble_nat 2 4 = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: ble_nat 4 2 = false.
Proof. reflexivity. Qed.

Theorem plus_O_n: forall n, 0 + n = n.
Proof.
  intro n.
  reflexivity.
Qed.

Theorem plus_1_l: forall n, 1 + n = S n.
Proof.
  intro n.
  reflexivity.
Qed.

Theorem mult_0_l: forall n, 0 * n = 0.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

Theorem plus_id_example:
  forall n m, n = m -> n + n = m + m.
Proof.
  intros n m.
  intro H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_exercise:
  forall n m o, n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intro h1.
  intro h2.
  rewrite -> h1.
  rewrite -> h2.
  reflexivity.
Qed.

Theorem mult_0_plus:
  forall n m, (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Theorem mult_S_1:
  forall n m,
    m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m.
  intro H.
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry:
  forall n, beq_nat (n + 1) 0 = false.
Proof.
  intro n.
  simpl.
Abort.

Theorem plus_1_neq_0:
  forall n, beq_nat (n + 1) 0 = false.
Proof.
  intro n.
  destruct n as [|n'].
  reflexivity.
  simpl.
  reflexivity.
Qed.

Theorem negb_involutive:
  forall b, negb (negb b) = b.
Proof.
  intro b.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem zero_nbeq_plus_1:
  forall n, beq_nat 0 (n + 1) = false.
Proof.
  intro n.
  destruct n.
  reflexivity.
  reflexivity.
Qed.

Theorem identity_fn_applied_twice:
  forall f, (forall x, f x = x) -> forall (b: bool), f (f b) = b.
Proof.
  intro f.
  intro H.
  intro b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice:
  forall f, (forall x, f x = negb x) -> forall (b: bool), f (f b) = b.
Proof.
  intro f.
  intro H.
  intro b.
  rewrite -> H.
  rewrite -> H.
  rewrite -> negb_involutive.
  reflexivity.
Qed.

Theorem orb_true_eq_true:
  forall b, orb b true = true.
Proof.
  intro b.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem andb_eq_orb:
  forall b c, (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  intro H.
  destruct c.
  destruct b.
  reflexivity.

Theorem and_f_t_f: andb false true = false.
Proof. reflexivity. Qed.

  rewrite <- and_f_t_f.
  rewrite -> H.
  reflexivity.
  destruct b.

Theorem and_t_f_f: andb true false = false.
Proof. reflexivity. Qed.

  rewrite <- and_t_f_f.
  rewrite -> H.
  reflexivity.
  reflexivity.
Qed.

Inductive bin :=
  | Z
  | T: bin -> bin
  | TPlus: bin -> bin.

Fixpoint incr n :=
  match n with
  | Z => TPlus Z
  | T n' => TPlus n'
  | TPlus n' => T (incr n')
  end.

Fixpoint toNat n :=
  match n with
  | Z => O
  | T n' => mult 2 (toNat n')
  | TPlus n' => S (mult 2 (toNat n'))
  end.

Eval simpl in toNat (TPlus (T (TPlus Z))).

Example nine_toNat_plus_eq: S (toNat (TPlus (T (T (TPlus Z))))) = toNat (incr (TPlus (T (T (TPlus Z))))).
Proof. reflexivity. Qed.

Fixpoint plus' n m :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.







































