Require Import Arith Ascii Compare List NSub.
Require Nat.

Fixpoint leftpad (c : ascii) (n : nat) (s : list ascii) :=
  match n with
  | O => s
  | S p =>
      match n ?= length s with
      | Gt => c :: leftpad c p s
      | _ => leftpad c p s
      end
  end
.

Definition holepad c n s (cond : comparison) :=
  match n with
  | O => s
  | S p =>
      match cond with
      | Gt => c :: leftpad c p s
      | _ => leftpad c p s
      end
  end
.

Example foo := "f"%char :: "o"%char :: "o"%char :: nil.
Compute (leftpad "!"%char 0 foo).
Compute (leftpad "!"%char 5 foo).

Lemma yespad' : forall c p s,
  S p > length s ->
  leftpad c (S p) s = c :: leftpad c p s
.
Proof.
  !: intros c p s Hgt.
  !: unfold leftpad at 1.
  !: fold leftpad.
  !: rewrite -> (proj1 (nat_compare_gt _ _) Hgt).
  !: reflexivity.
Qed.

Definition yespad c p s
  (Hgt : S p > length s) :
  leftpad c (S p) s = c :: leftpad c p s
:=
  f_equal (holepad c (S p) s) (proj1 (nat_compare_gt _ _) Hgt)
.

Lemma nopad' : forall c n s,
  n <= length s ->
  leftpad c n s = s
.
Proof.
  !: intros c n s Hle.
  !: induction n as [| p Hind].
  - !: reflexivity.
  - !: unfold leftpad at 1.
    !: fold leftpad.
    !: destruct (proj1 (Nat.le_lteq _ _) Hle) as [Hlt | Heq].
    + !: rewrite -> (proj1 (nat_compare_lt _ _) Hlt).
      !: apply Hind.
      !: apply (Nat.le_trans p (S p) (length s)).
      * !: apply le_S.
        !: apply le_n.
      * !: exact Hle.
    + !: rewrite -> (proj2 (Nat.compare_eq_iff _ _) Heq).
      !: apply Hind.
      !: apply (Nat.le_trans p (S p) (length s)).
      * !: apply le_S.
        !: apply le_n.
      * !: exact Hle.
Qed.

Definition nopad c n s :
  n <= length s ->
  leftpad c n s = s
:=
  (nat_ind
    (fun n => n <= length s -> leftpad c n s = s) 
    (fun _ => eq_refl)
    (fun p Hind Hle =>
      eq_trans
        (match (proj1 (Nat.le_lteq _ _) Hle) with
          | or_introl Hlt =>
              f_equal
                (holepad c (S p) s)
                (proj1 (nat_compare_lt _ _) Hlt)
          | or_intror Heq =>
              f_equal
                (holepad c (S p) s)
                (proj2 (Nat.compare_eq_iff _ _) Heq)
          end)
        (Hind (Nat.le_trans _ _ _ (le_S _ _ (le_n _)) Hle))))
  n
.

Theorem len' : forall c n s,
  length (leftpad c n s) = Nat.max n (length s)
.
Proof.
  !: intros c n s.
  !: destruct (le_gt_dec n (length s)) as [Hle | Hgt].
  - !: rewrite -> (Nat.max_r _ _ Hle).
    !: apply f_equal.
    !: apply nopad.
    !: exact Hle.
  - !: rewrite -> (Nat.max_l _ _ (ltac:(
      [> unfold gt in Hgt];
      [> unfold lt in Hgt];
      [> apply (le_S_n _ _ (le_S _ _ Hgt))]
    ))).
    !: induction n as [| p Hind].
    + !: inversion Hgt.
    + !: rewrite -> (yespad _ _ _ Hgt).
      !: simpl length.
      !: apply eq_S.
      !: assert (Hle : length s <= p). {
        !: unfold gt in Hgt.
        !: unfold lt in Hgt.
        !: apply (le_S_n _ _ Hgt).
      }
      !: destruct (le_decide _ _ Hle) as [Hlt | Heq].
      * !: apply Hind.
        !: exact Hlt.
      * !: rewrite -> (nopad c p s (ltac:(
          [> rewrite -> Heq];
          [> reflexivity]
        ))).
        !: exact Heq.
Qed.

Definition len c n s :
  length (leftpad c n s) = Nat.max n (length s)
:=
  (nat_ind
    (fun n => _)
    (eq_sym (Nat.max_r _ _ (Nat.le_0_l _)))
    (fun p Hind =>
      match le_gt_dec (S p) (length s) with
      | left Hle =>
          eq_trans
            (f_equal _ (nopad _ _ _ Hle))
            (eq_sym (Nat.max_r _ _ Hle))
      | right Hgt =>
          eq_trans
            (eq_trans
              (f_equal (length (A:=ascii)) (yespad _ _ _ Hgt))
              (eq_S _ _
                (eq_trans Hind (Nat.max_l _ _ (le_S_n _ _ Hgt)))))
            (eq_sym (Nat.max_l _ _ (le_S_n _ _ (le_S _ _ Hgt))))
      end))
  n
.

Theorem pre' : forall c n s,
  Forall (eq c) (firstn (n - length s) (leftpad c n s))
.
Proof.
  !: intros c n s.
  !: induction n as [| p Hind].
  - !: apply Forall_nil.
  - !: destruct (le_gt_dec (S p) (length s)) as [Hle | Hgt].
    + !: rewrite -> (proj2 (Nat.sub_0_le _ _) Hle).
      !: apply Forall_nil.
    + !: rewrite -> (yespad _ _ _ Hgt).
      !: unfold gt in Hgt.
      !: unfold lt in Hgt.
      !: rewrite -> (Nat.sub_succ_l (length s) p (le_S_n _ _ Hgt)).
      !: apply Forall_cons.
      * !: reflexivity.
      * !: exact Hind.
Qed.

Definition pre c n s :
  Forall (eq c) (firstn (n - length s) (leftpad c n s))
:=
  (nat_ind
    (fun n => _)
    (Forall_nil _)
    (fun p Hind =>
      match le_gt_dec (S p) (length s) with
      | left Hle =>
          eq_ind_r
            _
            (Forall_nil _)
            (f_equal
              (fun i => firstn i _)
              (proj2 (Nat.sub_0_le _ _) Hle))
      | right Hgt =>
          eq_ind_r
            _
            (Forall_cons _ eq_refl Hind)
            (f_equal2
              (firstn (A:=ascii))
              (Nat.sub_succ_l (length s) p (le_S_n _ _ Hgt))
              (yespad _ _ _ Hgt))
      end))
  n
.

Theorem suf' : forall c n s,
  skipn (n - length s) (leftpad c n s) = s
.
Proof.
  !: intros c n s.
  !: induction n as [| p Hind].
  - !: reflexivity.
  - !: destruct (le_gt_dec (S p) (length s)) as [Hle | Hgt].
    + !: rewrite -> (nopad _ _ _ Hle).
      !: rewrite -> (proj2 (Nat.sub_0_le _ _) Hle).
      !: reflexivity.
    + !: rewrite -> (yespad _ _ _ Hgt).
      !: unfold gt in Hgt.
      !: unfold lt in Hgt.
      !: rewrite -> (Nat.sub_succ_l (length s) p (le_S_n _ _ Hgt)).
      !: exact Hind.
Qed.


Definition suf c n s :
  skipn (n - length s) (leftpad c n s) = s
:=
  (nat_ind
    (fun n => _)
    eq_refl
    (fun p Hind =>
      match le_gt_dec (S p) (length s) with
      | left Hle =>
          eq_trans
            (f_equal
              (fun i => skipn i _)
              (proj2 (Nat.sub_0_le _ _) Hle))
            (nopad _ _ _ Hle)
      | right Hgt =>
          eq_trans
            (f_equal2
              (skipn (A:=ascii))
              (Nat.sub_succ_l (length s) p (le_S_n _ _ Hgt))
              (yespad _ _ _ Hgt))
            Hind
      end))
  n
.
