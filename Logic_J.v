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
