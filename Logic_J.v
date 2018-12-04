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
