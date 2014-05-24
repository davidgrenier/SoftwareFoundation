Add LoadPath "C:\Projects\Coq".

Require Export Basic.
Require Export Case.

Theorem andb_true_elim1:
  forall b c, andb b c = true -> b = true.
Proof.
  intros b c.
  intro H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H.
    reflexivity.
Qed.

Theorem andb_true_elim2:
  forall b c, andb b c = true -> c = true.
Proof.
  intros b c.
  intro H.
  destruct c.
  Case "c = true".
    reflexivity.
  Case "c = false".
    rewrite <- H.
    destruct b.
    SCase "b = false".
      reflexivity.
    SCase "b = true".
      reflexivity.
Qed.

Theorem plus_0_r_firsttry:
  forall n, n + 0 = n.
Proof.
  intros n.
  destruct n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
  simpl.
Abort.

Theorem plus_0_r:
  forall n, n + 0 = n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'.
    reflexivity.
Qed.

Theorem minus_diag:
  forall n, minus n n = 0.
Proof.
  intro n.
  induction n as [|n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'.
    reflexivity.
Qed.

Theorem mult_0_r:
  forall n, n * 0 = 0.
Proof.
  intro n.
  induction n as [|n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm:
  forall n m, S (n + m) = n + S m.
Proof.
  intros n m.
  induction n as [|n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_comm:
  forall n m, n + m = m + n.
Proof.
  intros n m.
  induction n as [|n'].
  Case "n = 0".
    rewrite -> plus_0_r.
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'.
    rewrite plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc:
  forall n m p, n + (m + p) = n + m + p.
Proof.
  intros n m p.
  induction n as [|n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'.
    reflexivity.
Qed.

Fixpoint double n :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus:
  forall n, double n = n + n.
Proof.
  intro n.
  induction n as [|n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

(*
Destructs attempts to demonstrate the property by solving cases
of the inductively defined type separately.
Induction attempts to demonstrate the property by showing how
the truth value for a value of the inductively defined set implies
the truth of the subsequent value.
*)

Theorem plus_0_plus':
  forall n m, (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (0 + n = n) as H.
  Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange_firsttry:
  forall n m p q, n + m + (p + q) = m + n + (p + q).
Proof.
  intros n m p q.
  rewrite -> plus_comm.
Abort.

Theorem plus_rearrange:
  forall n m p q, n + m + (p + q) = m + n + (p + q).
Proof.
  intros n m p q.
  assert (n + m = m + n) as H.
  Case "proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_swap:
  forall n m p, n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite -> plus_assoc.
  assert (n + m = m + n) as H.
    Case "proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

Theorem times_n_succm:
  forall n m, n * S m = n + n * m.
Proof.
  intros n m.
  induction n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> plus_swap.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem mult_comm:
  forall n m, n * m = m * n.
Proof.
  intros.
  induction n as [|n'].
  Case "n = 0".
    rewrite -> mult_0_r. reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    rewrite -> times_n_succm.
    reflexivity.
Qed.

Theorem evenb_n__oddb_Sn:
  forall n, evenb n = negb (evenb (S n)).
Proof.
  intro n.
  induction n.
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    assert (evenb (S (S n)) = evenb n).
      SCase "Proof of assertion".
      reflexivity.
    rewrite -> H.
    rewrite -> IHn.
    rewrite -> negb_involutive.
    reflexivity.
Qed.

Theorem ble_nat_refl:
  forall n, true = ble_nat n n.
Proof.
  intro.
  induction n.
  reflexivity.
  rewrite -> IHn.
  reflexivity.
Qed.

Theorem zero_nbeq_S:
  forall n, beq_nat 0 (S n) = false.
Proof.
  intro.
  reflexivity.
Qed.

Theorem andb_false_r:
  forall b, andb b false = false.
Proof.
  intro.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem plus_ble_compat_l:
  forall n m p, ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros.
  induction p as [|p'].
  Case "p = 0".
    simpl. rewrite -> H. reflexivity.
  Case "p = S p'".
    simpl.
    rewrite -> IHp'.
    reflexivity.
Qed.

Theorem S_nbeq_0:
  forall n, beq_nat (S n) 0 = false.
Proof.
  intro. reflexivity.
Qed.

Theorem mult_1_l:
  forall n, 1 * n = n.
Proof.
  intro. simpl.
  rewrite -> plus_0_r.
  reflexivity.
Qed.

Theorem all3_spec:
  forall b c,
    orb
      (andb b c)
      (orb
        (negb b)
        (negb c))
        = true.
Proof.
  intros.
  destruct b.
  destruct c.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

Theorem mult_plus_distr_r:
  forall n m p, (n + m) * p = n * p + m * p.
Proof.
  intros.
  induction n.
  induction m.
  reflexivity.
  reflexivity.
  simpl.
  rewrite -> IHn.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

Theorem mult_assoc:
  forall n m p, n * (m * p) = n * m * p.
Proof.
  intros.
  induction n.
  induction m.
  reflexivity.
  reflexivity.
  simpl.
  rewrite -> IHn.
  rewrite -> mult_plus_distr_r.
  reflexivity.
Qed.

Theorem beq_nat_refl:
  forall n, true = beq_nat n n.
Proof.
  intro n.
  induction n.
  reflexivity.
  rewrite -> IHn.
  reflexivity.
Qed.

Theorem plus_swap':
  forall n m p, n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite -> plus_assoc.
  replace (n + m) with (m + n).
  rewrite -> plus_assoc.
  reflexivity.
  rewrite -> plus_comm.
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

Theorem incr_toNat_comm:
  forall b, toNat (incr b) = S (toNat b).
Proof.
  intro.
  induction b as [|b'| b''].
  Case "b = Z".
    reflexivity.
  Case "b = T b'".
    simpl.
    rewrite -> plus_0_r.
    reflexivity.
  Case "b = TPlus b''".
    simpl.
    rewrite -> plus_0_r.
    rewrite -> plus_0_r.
    rewrite -> IHb''.
    simpl.
    rewrite -> plus_comm.
    reflexivity.
Qed.

Fixpoint toBin n :=
  match n with
  | O => Z
  | S n' => incr (toBin n')
  end.

Theorem toBin_toNat:
  forall n, toNat (toBin n) = n.
Proof.
  intro n.
  induction n.
  reflexivity.
  simpl.
  rewrite -> incr_toNat_comm.
  rewrite -> IHn.
  reflexivity.
Qed.
(*

Eval simpl in toBin 3.
Eval simpl in toBin 4.
Eval simpl in toBin 5.
Eval simpl in toBin 6.
Eval simpl in toBin 7.
Eval simpl in toBin 8.
Eval simpl in toBin 9.
Eval simpl in toBin 10.
Eval simpl in toBin 11.

Fixpoint normalize b:
  match b with
  | Z => Z
  | T b' => 

Theorem toNat_toBin:
  forall b, toBin (toNat b) = b.
Proof.
  intro b.
  induction b as [|b'|b''].
  Case "b = Z".
    reflexivity.
  Case "b = T b'".
    simpl.
    rewrite -> plus_0_r.

*)