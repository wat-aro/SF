Require Export Basics_J.

Module NatList.
  Inductive natprod : Type :=
    pair : nat -> nat -> natprod.

  Definition fst (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.

  Definition snd (p : natprod) : nat :=
    match p with
    | pair x y => y
    end.

  Notation "( x , y )" := (pair x y).

  Eval simpl in (fst (3, 4)).

  Definition fst' (p : natprod) : nat :=
    match p with
    | (x, y) => x
    end.

  Definition snd' (p : natprod) : nat :=
    match p with
    | (x, y) => y
    end.

  Definition swap_pair (p : natprod) : natprod :=
    match p with
    | (x, y) => (y, x)
    end.


  Theorem surjective_pairing' : forall (n m : nat),
      (n, m) = (fst (n, m), snd (n, m)).
  Proof.
    reflexivity.
  Qed.

  Theorem subjective_pairing : forall (p : natprod),
      p = (fst p, snd p).
  Proof.
    intros. destruct p as (n, m). simpl. reflexivity.
  Qed.

  Theorem snd_fst_is_swap : forall (p : natprod),
      (snd p, fst p) = swap_pair p.
  Proof.
    intros p. destruct p as (n, m). simpl. reflexivity.
  Qed.

  Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

  Notation "x :: l" := (cons x l) (at level 60, right associativity).
  Notation "[]" := nil.
  Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => nil
    | S count' => n :: (repeat n count')
    end.

  Fixpoint length (l : natlist) : nat :=
    match l with
    | nil => O
    | h :: t => S (length t)
    end.

  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.

  Notation "x ++ y" := (app x y) (right associativity, at level 60).

  Example test_app1 : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5].
  Proof. reflexivity. Qed.
  Example test_app2 : nil ++ [4, 5] = [4, 5].
  Proof. reflexivity. Qed.
  Example test_app3 : [1, 2, 3] ++ nil = [1, 2, 3].
  Proof. reflexivity. Qed.

  Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | nil => default
    | h :: t => h
    end.

  Definition tail (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => t
    end.

  Example test_hd1:             hd 0 [1,2,3] = 1.
  Proof. reflexivity.  Qed.
  Example test_hd2:             hd 0 [] = 0.
  Proof. reflexivity.  Qed.
  Example test_tail:            tail [1,2,3] = [2,3].
  Proof. reflexivity.  Qed.

  Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => match h with
                | O => nonzeros t
                | _ => cons h (nonzeros t)
                end
    end.

  Example test_nonzeros:            nonzeros [0,1,0,2,3,0,0] = [1,2,3].
  Proof. reflexivity. Qed.

  Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => match oddb h with
                | true => cons h (oddmembers t)
                | false => oddmembers t
                end
    end.

  Example test_oddmembers:            oddmembers [0,1,0,2,3,0,0] = [1,3].
  Proof. reflexivity. Qed.

  Fixpoint countoddmembers (l:natlist) : nat :=
    match l with
    | nil => O
    | h :: t => match oddb h with
                | true => S (countoddmembers t)
                | false => countoddmembers t
                end
    end.

  Example test_countoddmembers1:    countoddmembers [1,0,3,1,4,5] = 4.
  Proof. reflexivity. Qed.
  Example test_countoddmembers2:    countoddmembers [0,2,4] = 0.
  Proof. reflexivity. Qed.
  Example test_countoddmembers3:    countoddmembers nil = 0.
  Proof. reflexivity. Qed.

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h1 :: t1 => match l2 with
                  | nil => l1
                  | h2 :: t2 => cons h1 (cons h2 (alternate t1 t2))
                  end
    end.

  Example test_alternate1:        alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
  Proof. reflexivity. Qed.
  Example test_alternate2:        alternate [1] [4,5,6] = [1,4,5,6].
  Proof. reflexivity. Qed.
  Example test_alternate3:        alternate [1,2,3] [4] = [1,4,2,3].
  Proof. reflexivity. Qed.
  Example test_alternate4:        alternate [] [20,30] = [20,30].
  Proof. reflexivity. Qed.

  Definition bag := natlist.

  Fixpoint count (v:nat) (s:bag) : nat :=
    match s with
    | nil => O
    | h :: t => match beq_nat h v with
                | true => S (count v t)
                | false => count v t
                end
    end.

  Example test_count1:              count 1 [1,2,3,1,4,1] = 3.
  Proof. reflexivity. Qed.
  Example test_count2:              count 6 [1,2,3,1,4,1] = 0.
  Proof. reflexivity. Qed.

  Definition sum : bag -> bag -> bag := app.

  Example test_sum1:              count 1 (sum [1,2,3] [1,4,1]) = 3.
  Proof. reflexivity. Qed.

  Definition add (v:nat) (s:bag) : bag := cons v s.

  Example test_add1:                count 1 (add 1 [1,4,1]) = 3.
  Proof. reflexivity. Qed.
  Example test_add2:                count 5 (add 1 [1,4,1]) = 0.
  Proof. reflexivity. Qed.

  Definition member (v:nat) (s:bag) : bool :=
    blt_nat 0 (count v s).

  Example test_member1:             member 1 [1,4,1] = true.
  Proof. reflexivity. Qed.
  Example test_member2:             member 2 [1,4,1] = false.
  Proof. reflexivity. Qed.

  Fixpoint remove_one (v:nat) (s:bag): bag :=
    match s with
    | nil => nil
    | h :: t => match beq_nat v h with
                | true => t
                | false => h :: (remove_one v t)
                end
    end.

  Example test_remove_one1:         count 5 (remove_one 5 [2,1,5,4,1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_one2:         count 5 (remove_one 5 [2,1,4,1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_one3:         count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
  Proof. reflexivity. Qed.
  Example test_remove_one4:
    count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
  Proof. reflexivity. Qed.

  Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | h :: t => match beq_nat v h with
                | true => remove_all v t
                | false => h :: (remove_all v t)
                end
    end.

  Example test_remove_all1:          count 5 (remove_all 5 [2,1,5,4,1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_all2:          count 5 (remove_all 5 [2,1,4,1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_all3:          count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
  Proof. reflexivity. Qed.
  Example test_remove_all4:          count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
  Proof. reflexivity. Qed.

  Fixpoint subset (s1:bag) (s2:bag) : bool :=
    match s1 with
    | nil => true
    | h :: t => match member h s2 with
                | true => subset t (remove_one h s2)
                | false => false
                end
    end.

  Example test_subset1:              subset [1,2] [2,1,4,1] = true.
  Proof. reflexivity. Qed.
  Example test_subset2:              subset [1,2,2] [2,1,4,1] = false.
  Proof. reflexivity. Qed.

  Theorem nil_app : forall l : natlist,
      [] ++ l = l.
  Proof.
    reflexivity.
  Qed.

  Theorem tl_length_pred : forall l : natlist,
      pred (length l) = length (tail l).
  Proof.
    intros l. destruct l as [| n l'].
    Case "l = nil".
      reflexivity.
    Case "l = cons n l'".
      reflexivity.
  Qed.

  Theorem app_ass : forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3. induction l1 as [| n l'].
    Case "l1 = nil".
      reflexivity.
    Case "l1 = cons n l1".
      simpl. rewrite -> IHl'. reflexivity.
  Qed.

  Theorem app_length : forall l1 l2 : natlist,
      length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    intros l1 l2. induction l1 as [| n l'].
    Case "l = nil".
      reflexivity.
    Case "l = cons n l'".
      simpl.  rewrite -> IHl'. reflexivity.
  Qed.

  Fixpoint snoc (l :natlist) (v : nat) : natlist :=
    match l with
    | nil => [v]
    | h :: t => cons h (snoc t v)
    end.

  Fixpoint rev (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => snoc (rev t) h
    end.

  Example test_rev1:            rev [1,2,3] = [3,2,1].
  Proof. reflexivity.  Qed.
  Example test_rev2:            rev nil = nil.
  Proof. reflexivity.  Qed.

  Theorem length_snoc : forall n : nat, forall l : natlist,
        length (snoc l n) = S (length l).
  Proof.
    intros n l. induction l as [| n' l'].
    Case "l = nil".
      reflexivity.
    Case "l = n' l'".
      simpl. rewrite -> IHl'. reflexivity.
  Qed.

  Theorem rev_length_firsttry : forall l : natlist,
      length (rev l) = length l.
  Proof.
    intros l. induction l as [| n l'].
    Case "l = nil".
      reflexivity.
    Case "l = n l'".
      simpl. rewrite -> length_snoc. rewrite <- IHl'. reflexivity.
  Qed.

  Theorem app_nil_end : forall l : natlist,
      l ++ [] = l.
  Proof.
    intros l. induction l as [| n l'].
    Case "l = nil".
      reflexivity.
    Case "l = n l'".
      simpl. rewrite -> IHl'. reflexivity.
  Qed.

  Theorem rev_snoc : forall l : natlist, forall n : nat,
      rev (snoc l n) = n :: (rev l).
  Proof.
    intros. induction l as [| n' l'].
    Case "l = nil".
      reflexivity.
    Case "l = n' l'".
      simpl. rewrite -> IHl'. simpl. reflexivity.
  Qed.

  Theorem rev_involutive : forall l : natlist,
      rev (rev l) = l.
  Proof.
    intros l. induction l as [| n l'].
    Case "l = nil".
      reflexivity.
    Case "l = n l'".
      simpl. rewrite -> rev_snoc. rewrite -> IHl'. reflexivity.
  Qed.

  Theorem snoc_append : forall l1 l2 : natlist, forall n : nat,
      snoc (l1 ++ l2) n = l1 ++ snoc l2 n.
  Proof.
    intros l1 l2 n. induction l1 as [| n' l1'].
    Case "l1 = nil".
      reflexivity.
    Case "l1 = n' ++ l1'".
      simpl. rewrite IHl1'. reflexivity.
  Qed.

  Theorem distr_rev : forall l1 l2 : natlist,
      rev (l1 ++ l2) = (rev l2) ++ (rev l1).
  Proof.
    intros l1 l2. induction l1 as [| n l1'].
    Case "l1 = nil".
      simpl. rewrite -> app_nil_end. reflexivity.
    Case "l1 = n l1'".
      simpl. rewrite IHl1'. rewrite snoc_append. reflexivity.
  Qed.

  Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4. rewrite -> app_ass. rewrite -> app_ass. reflexivity.
  Qed.

  Theorem snoc_appended : forall (l : natlist) (n : nat),
      snoc l n = l ++ [n].
  Proof.
    intros l n. induction l as [| n' l'].
    Case "l = nil".
      reflexivity.
    Case "l = n' :: l'".
      simpl. rewrite -> IHl'. reflexivity.
    Qed.

  Lemma nonzeros_length : forall l1 l2 : natlist,
      nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros l1 l2. induction l1 as [| n' l1'].
    Case "l1 = nil".
      reflexivity.
    Case "l1 = n' :: l1'".
      simpl. induction n' as [| n''].
      rewrite -> IHl1'. reflexivity.
      simpl. rewrite IHl1'. reflexivity.
  Qed.

  Theorem count_member_nonzero : forall (s : bag),
      ble_nat 1 (count 1 (1 :: s)) = true.
  Proof.
    intros s. reflexivity.
  Qed.

  Theorem ble_n_Sn : forall n,
      ble_nat n (S n) = true.
  Proof.
    intros n. induction n as [| n'].
    Case "O".
      simpl. reflexivity.
    Case "S n".
      simpl. rewrite -> IHn'. reflexivity.
  Qed.

  Theorem remove_decreases_count: forall (s : bag),
      ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
  Proof.
    intros s. induction s as [| n s'].
    Case "s = 0".
      reflexivity.
    Case "s = n :: s'".
      simpl. induction n as [| n'].
      simpl. rewrite -> ble_n_Sn. reflexivity.
      simpl. rewrite IHs'. reflexivity.
  Qed.
