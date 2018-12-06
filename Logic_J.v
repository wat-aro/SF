Require Export Prop_J.

Definition funny_prop1 := forall n, forall (E : ev n), ev (n+4).
Definition funny_prop1' := forall n, forall (_ : ev n), ev (n+4).
Definition funny_prop1'' := forall n, ev n -> ev (n+4).

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Check conj.

Theorem and_example :
  (ev 0) /\ (ev 4).
Proof.
  apply conj.
  apply ev_0.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

Print and_example.

Theorem and_example' :
  (ev 0) /\ (ev 4).
Proof.
  split.
  Case "left". apply ev_0.
  Case "right". apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP. Qed.

Theorem proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HQ. Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  split.
    apply HQ.
    apply HP. Qed.

Print and_commut.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
  split.
  apply HP.
  apply HQ.
  apply HR. Qed.

Theorem even_ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    split.
    SCase "left".
      intros E0. apply ev_0.
    SCase "right".
      intros E0. inversion E0.
  Case "n = S n'".
    split.
    SCase "left".
      apply IHn'.
    SCase "right".
      intros E0. apply ev_SS. apply IHn'. inversion E0. apply H0. Qed.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) H0 H1 =>
    match H0 with
    | conj _ _ HP HQ =>
      match H1 with
      | conj _ _ HQ HR => conj P R HP HR
      end
    end.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                        (at level 95, no associativity) : type_scope.

Theorem iff_implies : forall P Q : Prop,
  (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H as [HAB HBA]. apply HAB.  Qed.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.

  intros P Q H.
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.  Qed.

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split.
    Case "->". intros P1. apply P1.
    Case "<-". intros P1. apply P1. Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H0 H1.
  inversion H0 as [H0AB H0BA].
  inversion H1 as [H1AB H1BA].
  split.
    Case "->".
      intros H2. apply H1AB. apply H0AB. apply H2.
    Case "<-".
      intros H2. apply H0BA. apply H1BA. apply H2. Qed.

Definition MyProp_iff_ev : forall n, MyProp n <-> ev n :=
  fun (n : nat) => conj (MyProp n -> ev n) (ev n -> MyProp n) (ev_MyProp n) (MyProp_ev n).

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Check or_introl.
Check or_intror.

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "right". apply or_intror. apply HP.
    Case "left". apply or_introl. apply HQ.  Qed.

Definition or_commut' : forall P Q : Prop, P \/ Q  -> Q \/ P :=
  fun (P Q : Prop) H =>
    match H with
    | or_introl _ _ P => or_intror _ _ P
    | or_intror _ _ Q => or_introl _ _ Q
    end.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. inversion H as [HP | [HQ HR]].
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.  Qed.

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R. intros H. inversion H as [[HP0 | HQ] [HP1 | HR]].
    Case "left left". left. apply HP0.
    Case "left right". left. apply HP0.
    Case "right left". left. apply HP1.
    Case "right right". right. split.
      SCase "right". apply HQ.
      SCase "left". apply HR. Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  Case "->". apply or_distributes_over_and_1.
  Case "<-". apply or_distributes_over_and_2. Qed.

Theorem andb_true__and : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.  Qed.

Theorem and__andb_true : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b.
    Case "b = true". simpl in H. right. apply H.
    Case "= = false". left. reflexivity. Qed.

Theorem orb_true : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H. destruct b.
  Case "b = true". left. reflexivity.
  Case "b = false". simpl in H. right. apply H. Qed.

Theorem orb_false : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H. destruct b.
  Case "b = true". inversion H.
  Case "b = false". simpl in H. split.
    SCase "left". reflexivity.
    SCase "right".apply H. Qed.

Inductive False : Prop := .

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra.  Qed.

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

Inductive True : Prop :=
| T : True.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.

  intros P Q H. inversion H as [HP HNA]. unfold not in HNA.
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.

  intros P H. unfold not. intros G. apply G. apply H.  Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H R.
  unfold not. unfold not in R. intros HP.
  apply R. apply H. apply HP. Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P.
  unfold not. intros HP.
  inversion HP as [HP0 HP1]. apply HP1. apply HP0. Qed.

Theorem five_not_even :
  ~ ev 5.
Proof.

  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn].
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1.  Qed.

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof.
  unfold not. intros n H. induction H.
  Case "ev_0".
    intros contra. inversion contra.
  Case "ev_SS". intros contra. inversion contra. apply IHev. apply H1. Qed.

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  unfold not. intros P H.
  Admitted.

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.
Definition classic := forall P:Prop,
  ~~P -> P.
Definition excluded_middle := forall P:Prop,
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
    b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity. Qed.

Check ex_falso_quodlibet.

Theorem not_eq_beq_false : forall n n' : nat,
    n <> n' ->
    beq_nat n n' = false.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  Case "m = 0".
    destruct n as [| n'].
    SCase "n = 0".
      intros H. simpl. apply ex_falso_quodlibet.
      unfold not in H. apply H. reflexivity.
    SCase "n = S n'".
      intros H. simpl. reflexivity.
  Case "m = S m'".
    destruct n as [| n'].
    SCase "n = 0".
      intros H. simpl. reflexivity.
    SCase "n = S n'".
      intros H. simpl. apply (IHm' n').
      assert (S n' <> S m' -> n' <> m') as not_eq_S_not_eq.
      SSCase "proof of assertion".
        unfold not. intros H0. intros H1. apply H0. rewrite <- H1. reflexivity.
      apply not_eq_S_not_eq. apply H. Qed.

Theorem beq_false_not_eq : forall n m,
  false = beq_nat n m -> n <> m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  Case "m = 0".
    destruct n as [| n'].
    SCase "n = 0". simpl. intros H. inversion H.
    SCase "n = S n'".
      simpl. intros H.
      unfold not. intros contra. inversion contra.
  Case "m = S m'".
    destruct n as [| n'].
    SCase "n = 0".
      simpl. intros H.
      unfold not. intros contra. inversion contra.
    SCase "n = S n'".
      unfold not. intros H0 H1. simpl in H0. inversion H1.
      unfold not in IHm'. apply (IHm' n').
      apply H0. apply H2. Qed.

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

Definition some_nat_is_even : Prop :=
  ex nat ev.

Definition snie : some_nat_is_even :=
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2).
  reflexivity.  Qed.

Example exists_example_1' : exists n,
     n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity.  Qed.

Theorem exists_example_2 : forall n,
     (exists m, n = 4 + m) ->
     (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  exists (2 + m).
  apply Hm.  Qed.

Definition p : ex nat (fun n => ev (S n)) :=
  ex_intro _ (fun n => ev (S n)) 1 (ev_SS _ ev_0).

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H0. unfold not. intros H1.
  inversion H1 as [x Hx].
  apply Hx.
  apply (H0 x). Qed.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros ex X P H0 x.
  destruct (ex (P x)) as [XP | NXP].
  Case "P x". apply XP.
  Case "~ P x".
    apply ex_falso_quodlibet.
    unfold not in H0. unfold not in NXP.
    apply H0.
    exists x. apply NXP. Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  Case "->".
    intros H. inversion H. destruct H0 as [HP | HQ].
    SCase "P witness". left. exists witness. apply HP.
    SCase "Q witness". right. exists witness. apply HQ.
  Case "<-".
    intros H. destruct H as [HP | HQ].
    SCase "exists x : X, P x". inversion HP. exists witness. left. apply H.
    SCase "exists x : X, Q x". inversion HQ. exists witness. right. apply H. Qed.

Module MyEquality.
  Inductive eq (X:Type) : X -> X -> Prop :=
    refl_equal : forall x, eq X x x.

  Notation "x = y" := (eq _ x y)
                    (at level 70, no associativity) : type_scope.

  Inductive eq' (X:Type) (x:X) : X -> Prop :=
    refl_equal' : eq' X x x.

  Notation "x =' y" := (eq' _ x y)
                         (at level 70, no associativity) : type_scope.

  Theorem two_defs_of_eq_coincide : forall (X:Type) (x y : X),
      x = y <-> x =' y.
  Proof.
    intros X x y. split.
    Case "->".
      intros H. inversion H. apply (refl_equal' X y).
    Case "<-".
      intros H. inversion H. apply (refl_equal X y). Qed.

  Check eq'_ind.

  Definition four : 2 + 2 = 1 + 3 :=
    refl_equal nat 4.
  Definition singleton : forall (X:Set) (x:X), []++[x] = x::[]  :=
    fun (X:Set) (x:X) => refl_equal (list X) [x].

End MyEquality.

Module LeFirstTry.
  Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

  Check le_ind.
End LeFirstTry.

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Check le_ind.

Theorem test_le1 :
  3 <= 3.
Proof.

  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.

  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  ~ (2 <= 1).
Proof.

  intros H. inversion H. inversion H1.  Qed.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation (R : nat -> nat -> Prop) (n m : nat) : Prop :=
| tr : R n m \/ R m n -> total_relation R n m.

