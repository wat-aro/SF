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

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index (S n) l = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| x l'].
  Case "l = []".
    intros n. induction n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". intros eq. inversion eq.
  Case " l = x :: l'".
    intros n. induction n as [| n'].
    SCase "n = O". intros eq. inversion eq.
    SCase "n = S n'".
      intros eq. apply IHl'. inversion eq. reflexivity. Qed.

Theorem length_snoc''' : forall (n : nat) (X : Type)
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros n X v l.
  generalize dependent n.
  induction l as [| x l'].
  Case "l = []".
    intros n eq. induction n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "l = x :: l'".
    intros n eq. induction n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'".
      simpl. apply eq_remove_S.
      apply IHl'. inversion eq. reflexivity. Qed.

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X)
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x.
  induction l1 as [| v l'].
  Case "l = []".
    simpl. intros n eq. apply eq.
  Case "l = v :: l'".
    destruct n as [| n'].
    SCase "n = O".
      intros eq. inversion eq.
    SCase "n = S n'".
      simpl. intros eq. inversion eq.
      rewrite -> (IHl' n'). symmetry. apply eq. apply H0. Qed.

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  intros X n l.
  generalize dependent n.
  induction l as [| x l'].
  Case "l = []".
    simpl. intros n eq. inversion eq. reflexivity.
  Case "l = x :: l'".
    destruct n as [| n'].
    SCase "n = O".
      intros eq. inversion eq.
    SCase "n = S n'".
      intros eq. simpl in eq. inversion eq.
      apply IHl' in H0. inversion eq.
      simpl. apply eq_remove_S. rewrite <- plus_n_Sm.
      assert (forall (X : Type) (l1 l2 : list X) (x : X), length (l1 ++ x :: l2) = S (length (l1 ++ l2))) as H.
        intros X0 l1 l2 x0.
        generalize dependent l2.
        induction l1 as [| x1 l1'].
        SSCase "l = []". reflexivity.
        SSCase "l = x1 :: l1'".
          simpl. intros l2. apply eq_remove_S. apply IHl1'.
      rewrite -> H. apply eq_remove_S. rewrite -> H0. rewrite -> H1. reflexivity. Qed.
