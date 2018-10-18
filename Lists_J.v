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