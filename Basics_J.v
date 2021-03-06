Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_or3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_or4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Definition admit {T: Type} : T.  Admitted.

Definition nandb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true =>
    match b2 with
    | true => false
    | false => true
    end
  | false => true
  end.

Example test_nandb1:               (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => andb b2 b3
  | false => false
  end.

Example test_andb31:                 (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check (negb).
Check negb.

Module Playground1.

  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Fixpoint oddb (n : nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity. Qed.

Module Playground2.

  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  Eval simpl in (plus (S (S (S O))) (S (S O))).

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O   , _ => O
    | S  _, O => n
    | S n', S m' => minus n' m'
    end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1:          (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2:          (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1).

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

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
    match m with
    | O => false
    | S m' => ble_nat n' m'
    end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  andb (ble_nat n m) (negb (beq_nat n m)).

Example test_blt_nat1:             (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2:             (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3:             (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof.
  reflexivity.
Qed.

Eval simpl in (forall n:nat, n + 0 = n).
Eval simpl in (forall n:nat, 0 + n = n).

Theorem plus_O_n'' : forall n:nat, 0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_O_l : forall n:nat, 0 * n = O.
Proof.
  intros k.
  reflexivity.
Qed.

Theorem plus_id_example : forall n m:nat,
    n = m ->
    n + n = m + m.

Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
    (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Theorem plus_1_neq_0_fisttry : forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n.
  reflexivity.
  reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

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
    | fail 1 "because we are working on a differennt case"
    ].

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
  rewrite <- H.
  simpl.
  reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct b, c.
  Case "b = true, c = true".
    reflexivity.
  Case "b = true, c = false".
    rewrite <- H.
    simpl.
    reflexivity.
  Case "b = false, c = true".
    reflexivity.
  Case "b = false, c = false".
    rewrite <- H.
    simpl.
    reflexivity.
Qed.

Theorem plus_0 : forall n : nat,
    n + 0 = n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n,
    minus n n = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n'], m as [| m'].
  Case "n = 0, m = 0".
    simpl. reflexivity.
  Case "n = 0, m = S m'".
    simpl. reflexivity.
  Case "n = S n', m = 0".
    simpl. rewrite -> IHn'. reflexivity.
  Case "n = S n', m = S m'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
  intros.
  induction m as [| m'].
  Case "m = 0".
    simpl.
    induction n.
    reflexivity.
    rewrite -> plus_0. reflexivity.
  Case "m = S m".
    simpl. rewrite <- plus_n_Sm. rewrite <- IHm'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros. induction n.
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
  simpl. rewrite -> IHn. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros. induction n as [| n']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite <- IHn'. reflexivity.
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

Theorem plus_rearrange : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc'.
  assert (H: m + (n + p) = m + n + p).
    Case "Proof of assertion".
      rewrite <- plus_assoc'. reflexivity.
  rewrite -> H.
  assert (H1: n + m = m + n).
    Case "Proof of assertion".
      rewrite plus_comm. reflexivity.
  rewrite -> H1. reflexivity.
Qed.

Theorem mult_n_1 : forall n : nat,
    n * 1 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Lemma mult_1 : forall m n : nat,
    n + n * m = n * S m.
Proof.
  intros. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl.
    rewrite <- IHn'.
    rewrite -> plus_swap.
    reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros. induction m as [| m'].
  Case "m = 0".
    simpl. rewrite -> mult_0_r. reflexivity.
  Case "m = S m'".
    simpl. rewrite -> IHm'.
    rewrite -> mult_1. reflexivity.
Qed.

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    assert (H: forall b:bool, negb (negb b) = b).
      intros b. destruct b. reflexivity. reflexivity.
    rewrite -> IHn'.
    rewrite -> H.
    simpl.
    reflexivity.
Qed.

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  intros. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros. induction p as [| p'].
  Case "p = 0".
    simpl. rewrite H. reflexivity.
  Case "p = S p'".
    simpl. rewrite IHp'. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros. simpl. rewrite plus_0. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros. destruct b.
  Case "b = true".
    simpl. destruct c.
      simpl. reflexivity.
      simpl. reflexivity.
  Case "b = false".
    simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite plus_assoc'. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite mult_plus_distr_r. rewrite IHn'. reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite -> plus_assoc'.
  assert (H: m + (n + p) = m + n + p).
    Case "Proof of assertion".
      rewrite <- plus_assoc'. reflexivity.
  rewrite H.
  replace (n + m) with (m + n).
  reflexivity.
  rewrite plus_comm. reflexivity.
Qed.

Theorem de_morgan_a : forall a b : bool,
    negb (andb a b) = orb (negb a) (negb b).
Proof.
  intros. destruct a.
  Case "a = true".
    simpl. reflexivity.
  Case "a = false".
    simpl. reflexivity.
Qed.

Theorem de_morgan_o : forall a b : bool,
    negb (orb a b) = andb (negb a) (negb b).
Proof.
  intros. destruct a.
  Case "a = true".
    simpl. reflexivity.
  Case "a = false".
    simpl. reflexivity.
Qed.

Module binnat.
  Inductive bin : Type :=
  | Z : bin
  | I : bin -> bin
  | B : bin -> bin.

  Definition inc (b : bin) : bin :=
    match b with
    | Z => I Z
    | I n => B n
    | B n => I b
    end.

  Eval simpl in (inc Z).
  Eval simpl in (inc (I Z)).
  Eval simpl in (inc (B Z)).

  Fixpoint bin2nat (b : bin) : nat :=
    match b with
    | Z => (O : nat)
    | I n => S (bin2nat n)
    | B n => S (S (bin2nat n))
    end.

  Eval simpl in (bin2nat Z).
  Eval simpl in (bin2nat (I Z)).
  Eval simpl in (bin2nat (B Z)).
  Eval simpl in (bin2nat (I (B Z))).
  Eval simpl in (bin2nat (B (B Z))).

  Example test_b2n0: (bin2nat Z) = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_b2n1: (bin2nat (I Z)) = 1.
  Proof. simpl. reflexivity. Qed.
  Example test_b2n2: (bin2nat (B Z)) = 2.
  Proof. simpl. reflexivity. Qed.
  Example test_b2n3: (bin2nat (I (B Z))) = 3.
  Proof. simpl. reflexivity. Qed.
  Example test_b2n4: (bin2nat (B (B Z))) = 4.
  Proof. simpl. reflexivity. Qed.

  Theorem bin2nat_inc__S_bin2nat : forall b : bin,
      bin2nat (inc b) = S (bin2nat b).
  Proof.
    induction b as [| b' | b''].
    Case "b = Z".
      simpl. reflexivity.
    Case "b = I b'".
      simpl. reflexivity.
    Case "b = B b''".
      simpl. reflexivity.
  Qed.

  Theorem beq_b_inc__n_inc : forall b : bin,
      bin2nat (inc b) = S (bin2nat b).
  Proof.
    intros. induction b as [| b' | b''].
    Case "b = Z".
      simpl. reflexivity.
    Case "b = I b'".
      simpl. rewrite <- IHb'. rewrite -> bin2nat_inc__S_bin2nat. reflexivity.
    Case "b = B b".
      simpl. rewrite <- IHb''. rewrite -> bin2nat_inc__S_bin2nat. reflexivity.
  Qed.

  Fixpoint nat2bin (n : nat) : bin :=
    match n with
    | O => Z
    | S n' => inc (nat2bin n')
    end.

  Theorem nat2nat : forall n : nat,
      bin2nat (nat2bin n) = n.
  Proof.
    intros. induction n as [| n'].
    Case "n = O".
      simpl. reflexivity.
    Case "n = S n'".
      simpl.
      replace (S n') with(S (bin2nat (nat2bin n'))).
        rewrite -> beq_b_inc__n_inc. reflexivity.
      rewrite -> IHn'. reflexivity.
  Qed.
End binnat.
