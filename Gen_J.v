Require Export Poly_J.

Theorem double_injective' : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". simpl. intros m eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'".
    simpl. intros m eq. induction m as [| m'].
    SCase "m = O". inversion eq.
    SCase "m = S m'".
      assert (n' = m') as H.
      SSCase "Proof of assertion". apply IHn'.
        inversion eq. reflexivity.
      rewrite -> H. reflexivity. Qed.

Theorem double_injective_take2 : forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  Case "m = O".
    intros n. induction n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'".
      intros eq. inversion eq.
  Case "m = S m'".
    intros n eq. induction n as [| n'].
    SCase "n = O".
      inversion eq.
    SCase "n = S n'".
      assert (n' = m') as H.
      SSCase "Proof of assertion".
        apply IHm'. inversion eq. reflexivity.
      rewrite -> H. reflexivity. Qed.

Theorem plus_n_n_injective_take2 : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n m H.
  generalize dependent n.
  induction m as [| m'].
  Case "m = O".
    intros n eq. induction n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = Sn'". inversion eq.
  Case "m = S m'".
    intros n eq. induction n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'".
      rewrite <- plus_n_Sm in eq. rewrite <- plus_n_Sm in eq. inversion eq.
      apply eq_remove_S. apply IHm'. apply H0. Qed.
