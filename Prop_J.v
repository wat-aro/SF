Require Export Poly_J.

Check (2 + 2 = 4).
Check (ble_nat 3 2 = false).

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.

Definition strange_prop1 : Prop :=
  (2 + 2 = 5) -> (99 + 26 = 42).

Definition strange_prop2 :=
  forall n, (ble_nat n 17 = true) -> (ble_nat n 99 = true).

Definition even (n : nat) : Prop :=
  evenb n = true.

Check even.
Check (even 4).
Check (even 3).

Definition even_n__even_SSn (n : nat) : Prop :=
  (even n) -> (even (S (S n))).

Definition between (n m o : nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

Definition teen : nat -> Prop := between 13 19.

Definition true_for_zero (P : nat -> Prop) : Prop :=
  P 0.

Definition true_for_n__true_for_Sn (P : nat -> Prop) (n : nat) : Prop :=
  P n -> P (S n).

Definition preserved_by_S (P : nat -> Prop) : Prop :=
  forall n', P n' -> P (S n').

Definition true_for_all_numbers (P : nat -> Prop) : Prop :=
  forall n, P n.

Definition our_nat_induction (P : nat -> Prop) : Prop :=
  (true_for_zero P) ->
  (preserved_by_S P) ->
  (true_for_all_numbers P).

Inductive good_day : day -> Prop :=
| gd_sat : good_day saturday
| gd_sun : good_day sunday.

Theorem gds : good_day sunday.
Proof. apply gd_sun. Qed.

Inductive day_before : day -> day -> Prop :=
| db_tue : day_before tuesday monday
| db_wed : day_before wednesday tuesday
| db_thu : day_before thursday wednesday
| db_fri : day_before friday thursday
| db_sat : day_before saturday friday
| db_sun : day_before sunday saturday
| db_mon : day_before monday sunday.

Inductive fine_day_for_singing : day -> Prop :=
| fdfs_any : forall d : day, fine_day_for_singing d.

Theorem fdfs_wed : fine_day_for_singing wednesday.
Proof. apply fdfs_any. Qed.

Definition fdfs_wed' : fine_day_for_singing wednesday :=
  fdfs_any wednesday.
Check fdfs_wed.
Check fdfs_wed'.

Inductive ok_day : day -> Prop :=
| okd_gd : forall d,
    good_day d ->
    ok_day d
| okd_before : forall d1 d2,
    ok_day d2 ->
    day_before d2 d1 ->
    ok_day d1.

Definition okdw : ok_day wednesday :=
  okd_before wednesday thursday
             (okd_before thursday friday
                         (okd_before friday saturday
                                     (okd_gd saturday gd_sat)
                                     db_sat)
                         db_fri)
             db_thu.
Theorem okdw' : ok_day wednesday.
Proof.
  apply okd_before with (d2 := thursday).
  apply okd_before with (d2 := friday).
  apply okd_before with (d2 := saturday).
  apply okd_gd. apply gd_sat.
  apply db_sat.
  apply db_fri.
  apply db_thu. Qed.

Print okdw'.

Definition okd_before2 := forall d1 d2 d3,
    ok_day d3 ->
    day_before d2 d1 ->
    day_before d3 d2 ->
    ok_day d1.

Theorem okd_before2_valid : okd_before2.
Proof.
  unfold okd_before2.
  intros d1 d2 d3 ok b0 b1.
  apply okd_before with (d2 := d2).
  apply okd_before with (d2 := d3).
  apply ok.
  apply b1.
  apply b0. Qed.

Definition okd_before2_valid' : okd_before2 :=
  fun (d1 d2 d3 : day) =>
    fun (H : ok_day d3) =>
      fun (H0 : day_before d2 d1) =>
        fun (H1 : day_before d3 d2) =>
          okd_before d1 d2 (okd_before d2 d3 H H1) H0.

Print okd_before2_valid.

Check nat_ind.

Theorem mult_0_r' : forall n : nat,
    n * 0 = 0.
Proof.
  apply nat_ind.
  Case "O". reflexivity.
  Case "S". simpl. intros n IHn. rewrite -> IHn.
    reflexivity. Qed.

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  Case "0". reflexivity.
  Case "S n". intros n H. simpl. apply eq_remove_S. apply H. Qed.

Inductive yesno : Type :=
| yes : yesno
| no : yesno.

Check yesno_ind.

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.

Inductive natlist : Type :=
| nnil : natlist
| ncons : nat -> natlist -> natlist.

Check natlist_ind.

Inductive natlist1 : Type :=
| nnil1 : natlist1
| nsnoc1 : natlist1 -> nat -> natlist1.
Check natlist1_ind.

Inductive ExSet : Type :=
| con1 : bool -> ExSet
| con2 : nat -> ExSet -> ExSet.
Check ExSet_ind.

Inductive tree (X : Type) : Type :=
| leaf : X -> tree X
| node : tree X -> tree X -> tree X.
Check tree_ind.
(*
  tree_ind :
    forall (X : Type) (P : tree X -> Prop),
      (forall x : X, P (leaf X x)) ->
      (forall t : tree X, P t -> forall t0 : tree X, P t0 -> P (node X t t0)) ->
      forall t : tree X, P t
 *)

Inductive mytype (X : Type) : Type :=
| constr1 : X -> mytype X
| constr2 : nat -> mytype X
| constr3 : mytype X -> nat -> mytype X.
(*
   mytype_ind :
     forall (X : Type) (P : mytype X -> Prop),
       (forall x : X, P (constr1 X x)) ->
       (forall n : nat, P (constr2 X n)) ->
       (forall m : mytype X, P m ->
         forall n : nat, P (constr3 X m n)) ->
       forall m : mytype X, P m

 *)

Check mytype_ind.

Inductive foo (X Y : Type) : Type :=
| bar : X -> foo X Y
| baz : Y -> foo X Y
| quux : (nat -> foo X Y) -> nat -> foo X Y.

Check foo_ind.

Inductive foo' (X : Type) : Type :=
| C1 : list X -> foo' X -> foo' X
| C2 : foo' X.
Check foo'_ind.
(*
   foo'_ind :
     forall (X : Type) (P : foo' X -> Prop),
       (forall (l : list X) (f : foo' X),
         P f -> P (C1 X l f)) ->
       P (C2 X) ->
       forall f1 : foo' X, P f1
 *)

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Definition P_m0r' : nat->Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  Case "n = O". reflexivity.
  Case "n = S n'".

    unfold P_m0r. simpl. intros n' IHn'.
    apply IHn'.  Qed.

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

Theorem four_ev' :
  ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

Definition four_ev : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Theorem ev_plus4' : forall n,
  ev n -> ev (4 + n).
Proof.
  simpl.
  intros n Hev.
  apply ev_SS. apply ev_SS. apply Hev. Qed.

Definition ev_plus4 : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) (Hev : ev n) => ev_SS (S (S n)) (ev_SS n Hev).

Theorem double_even : forall n,
  ev (double n).
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". simpl. apply ev_0.
  Case "n = S n'".
    simpl. apply ev_SS. apply IHn'. Qed.

Definition double_even' : forall n, ev (double n) :=
  nat_ind
    (fun (n : nat) => ev (double n))
    ev_0
    (fun (n' : nat) (IHn' : ev (double n')) => ev_SS (double n') IHn').

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0". simpl.
  apply ev_0.
  Case "E = ev_SS". simpl. apply E'. Qed.

Definition ev_minus2' : forall (n : nat), ev n -> ev (pred (pred n)) :=
  ev_ind
    (fun (n' : nat) => ev (pred (pred n')))
    ev_0
    (fun (n'' : nat) (E' : ev n'') =>  (fun (E'' : ev (pred (pred n''))) => E')).

Theorem ev_minus2'' : forall n,
    ev n -> ev (pred (pred n)).
Proof.
  intros n E. destruct n as [| n'].
  Case "n = 0". simpl. apply E.
  Case "n = S n'". inversion E. simpl. apply H0. Qed.

Theorem ev_even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0". reflexivity.
  Case "E = ev_SS n' E'".
    unfold even. apply IHE'. Qed.

Theorem ev_even_n : forall n,
    ev n -> even n.
Proof.
  intros n E. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    inversion E. unfold even.
  Admitted.

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof.
  intros n m En Em. induction En as [| n' En'].
  Case "En = ev_0".
    simpl. apply Em.
  Case "En = ev_SS n' En'".
    simpl. apply ev_SS. apply IHEn'. Qed.

Definition ev_sum' : forall n m, ev n -> ev m -> ev (n + m) :=
  fun (n m : nat) (En : ev n) (Em : ev m) =>
    (ev_ind
      (fun (n' : nat) => ev (n' + m))
      Em
      (fun (n' : nat) (En' : ev n') (Enm : ev (n' + m)) => ev_SS (n' + m) Enm))
      n En.

Theorem SSev_ev_firsttry : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  destruct E as [| n' E'].

Admitted.

Theorem SSev_even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E']. apply E'. Qed.

Theorem SSSSev_even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E. inversion E as [| n' E']. inversion E' as [| n'' E'']. apply E''. Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros E. inversion E. inversion H0. inversion H2. Qed.

Theorem ev_minus2''': forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E. inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'. Qed.

Theorem ev_ev_even : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m Enm E.
  generalize dependent Enm.
  generalize dependent m.
  induction E as [| n' E'].
  Case "ev n = ev_0".
    intros m Enm. apply Enm.
  Case "ev n = ev_SS n' E'".
    simpl. intros m Em. inversion Em as [| nm Em'].
    apply IHE'. apply Em'. Qed.
