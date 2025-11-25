(* Coq 8.12.2 (https://jscoq.github.io/scratchpad.html) *)

Require Import Ascii List PeanoNat.
Import ListNotations.

Inductive val: Set :=
| Char (_: ascii)
| Nat (_: nat)
| Bool (_: bool)
| Null
.

Inductive stmt: Set :=
| Val (vl: val) (* +1 *)
| Var (* 0 *)
| Get (var: nat) (* +1 *)
| Put (var: nat) (* -1 *)
| GetAt (var: nat) (* -1 +1 *)
| PutAt (var: nat) (* -2 *)
| LengthOf (var: nat) (* +1 *)
| NewArray (var: nat) (* -1 *)
| LessThan (* -2 +1 *)
| Minus (* -2 +1 *)
| If (thn: list stmt) (els: list stmt) (* -1 *)
| While (cond: list stmt) (body: list stmt) (* 0 *)
.

Inductive step: list (list val) -> list val -> list stmt -> list (list val) -> list val -> list stmt -> Prop :=
| stepVal: forall env stack vl stmts,
  step
    env stack (Val vl :: stmts)
    env (vl :: stack) stmts
| stepVar: forall env stack stmts,
  step
    env stack (Var :: stmts)
    (env ++ [[]]) stack stmts
| stepGet: forall env stack var stmts vl
  (Henv: nth_error env var = Some [vl]),
  step
    env stack (Get var :: stmts)
    env (vl :: stack) stmts
| stepPut: forall env vl stack var stmts old rest
  (Henv: skipn var env = old :: rest),
  step
    env (vl :: stack) (Put var :: stmts)
    (firstn var env ++ [vl] :: rest) stack stmts
| stepGetAt: forall env idx stack var stmts vl tail array
  (Henv: nth_error env var = Some array)
  (Harray: skipn idx array = vl :: tail),
  step
    env (Nat idx :: stack) (GetAt var :: stmts)
    env (vl :: stack) stmts
| stepPutAt: forall env idx vl stack var stmts old tail array rest
  (Henv: skipn var env = array :: rest)
  (Harray: skipn idx array = old :: tail),
  step
    env (vl :: Nat idx :: stack) (PutAt var :: stmts)
    (firstn var env ++ (firstn idx array ++ vl :: tail) :: rest) stack stmts
| stepLengthOf: forall env stack var stmts array
  (Henv: nth_error env var = Some array),
  step
    env stack (LengthOf var :: stmts)
    env (Nat (length array) :: stack) stmts
| stepNewArray: forall env size stack var stmts old rest
  (Henv: skipn var env = old :: rest),
  step
    env (Nat size :: stack) (NewArray var :: stmts)
    (firstn var env ++ repeat Null size :: rest) stack stmts
| stepLessThan: forall env m n stack stmts,
  step
    env (Nat n :: Nat m :: stack) (LessThan :: stmts)
    env (Bool (m <? n) :: stack) stmts
| stepMinus: forall env m n d stack stmts
  (Hd: S m - n = S d),
  step
    env (Nat n :: Nat m :: stack) (Minus :: stmts)
    env (Nat d :: stack) stmts
| stepIf: forall env cond stack thn els stmts,
  step
    env (Bool cond :: stack) (If thn els :: stmts)
    env stack ((if cond then thn else els) ++ stmts)
| stepWhile: forall env stack cond body stmts,
  step
    env stack (While cond body :: stmts)
    env stack (cond ++ If (body ++ [While cond body]) [] :: stmts)
.

Lemma stepDet env0 stack0 stmts0 env1 stack1 stmts1 env2 stack2 stmts2
  (Hstep1: step env0 stack0 stmts0 env1 stack1 stmts1)
  (Hstep2: step env0 stack0 stmts0 env2 stack2 stmts2):
  env1 = env2 /\ stack1 = stack2 /\ stmts1 = stmts2.
Proof.
  destruct Hstep1; inversion Hstep2; subst; auto;
    try (rewrite -> Henv in *; inversion Henv0; subst);
    try (rewrite -> Harray in *; inversion Harray0; subst);
    try (rewrite -> Hd in *; inversion Hd0; subst);
    auto.
Qed.

Lemma stepConcat env0 stack0 stmts0 env1 stack1 stmts1 stmts2
  (Hstep: step env0 stack0 stmts0 env1 stack1 stmts1):
  step env0 stack0 (stmts0 ++ stmts2) env1 stack1 (stmts1 ++ stmts2).
Proof.
  destruct Hstep; simpl; try (rewrite <- app_assoc);
  econstructor; eassumption.
Qed.

Inductive stepIters: nat -> list (list val) -> list val -> list stmt -> list (list val) -> list val -> list stmt -> Prop :=
| stepItersDone: forall env stack stmts,
  stepIters 0 env stack stmts env stack stmts
| stepItersCont: forall iters env0 stack0 stmts0 env1 stack1 stmts1 env2 stack2 stmts2
  (Hstep: step env0 stack0 stmts0 env1 stack1 stmts1)
  (HstepIters: stepIters iters env1 stack1 stmts1 env2 stack2 stmts2),
  stepIters (S iters) env0 stack0 stmts0 env2 stack2 stmts2
.

Lemma stepItersDet iters env0 stack0 stmts0 env1 stack1 stmts1 env2 stack2 stmts2
  (HstepIters1: stepIters iters env0 stack0 stmts0 env1 stack1 stmts1)
  (HstepIters2: stepIters iters env0 stack0 stmts0 env2 stack2 stmts2):
  env1 = env2 /\ stack1 = stack2 /\ stmts1 = stmts2.
Proof.
  revert env0 stack0 stmts0 env1 stack1 stmts1 env2 stack2 stmts2 HstepIters1 HstepIters2.
  induction iters; intros.
  - inversion HstepIters1. inversion HstepIters2. subst. auto.
  - inversion HstepIters1. inversion HstepIters2. subst.
    destruct (stepDet _ _ _ _ _ _ _ _ _ Hstep Hstep0) as [? [? ?]]. subst.
    destruct (IHiters _ _ _ _ _ _ _ _ _ HstepIters HstepIters0) as [? [? ?]]. subst. auto.
Qed.

Lemma stepItersDelay iters env0 stack0 stmts0 env2 stack2 stmts2
  (HstepIters: stepIters (S iters) env0 stack0 stmts0 env2 stack2 stmts2):
  exists env1 stack1 stmts1,
  stepIters iters env0 stack0 stmts0 env1 stack1 stmts1 /\
  step env1 stack1 stmts1 env2 stack2 stmts2.
Proof.
  revert env0 stack0 stmts0 env2 stack2 stmts2 HstepIters.
  induction iters; intros; inversion HstepIters; subst.
  - inversion HstepIters0. subst. repeat econstructor. eassumption.
  - destruct (IHiters _ _ _ _ _ _ HstepIters0) as [? [? [? [? ?]]]].
    repeat econstructor; eassumption.
Qed.

Lemma stepItersTermWlog iters2 env0 stack0 stmts0 env1 stack1 stmts1 iters3 env2 stack2
  (HstepIters1: stepIters iters2 env0 stack0 stmts0 env1 stack1 stmts1)
  (HstepIters2: stepIters iters3 env0 stack0 stmts0 env2 stack2 []):
  iters2 <= iters3.
Proof.
  apply Nat.le_ngt. intro Hiters.
  revert env0 stack0 stmts0 env1 stack1 stmts1 env2 stack2 HstepIters1 HstepIters2.
  induction Hiters; intros; destruct (stepItersDelay _ _ _ _ _ _ _ HstepIters1) as [? [? [? [? ?]]]].
  - destruct (stepItersDet _ _ _ _ _ _ _ _ _ _ HstepIters2 H) as [? [? ?]].
    subst.
    inversion H0.
  - eapply IHHiters; eassumption.
Qed.

Lemma stepItersTerm iters2 env0 stack0 stmts0 env1 stack1 iters3 env2 stack2
  (HstepIters1: stepIters iters2 env0 stack0 stmts0 env1 stack1 [])
  (HstepIters2: stepIters iters3 env0 stack0 stmts0 env2 stack2 []):
  iters2 = iters3.
Proof.
  apply Nat.le_antisymm; eapply stepItersTermWlog; eassumption.
Qed.

Lemma stepItersConcat iters env0 stack0 stmts0 env1 stack1 stmts1 stmts2
  (HstepIters: stepIters iters env0 stack0 stmts0 env1 stack1 stmts1):
  stepIters iters env0 stack0 (stmts0 ++ stmts2) env1 stack1 (stmts1 ++ stmts2).
Proof.
  induction HstepIters.
  - constructor.
  - pose proof (stepConcat _ _ _ _ _ _ stmts2 Hstep).
    econstructor; eassumption.
Qed.

Lemma stepItersArrow iters1 env0 stack0 stmts0 env1 stack1 stmts1 iters2 env2 stack2 stmts2
  (HstepIters1: stepIters iters1 env0 stack0 stmts0 env1 stack1 stmts1)
  (HstepIters2: stepIters iters2 env1 stack1 stmts1 env2 stack2 stmts2):
  stepIters (iters1 + iters2) env0 stack0 stmts0 env2 stack2 stmts2.
Proof.
  induction HstepIters1.
  - intros. assumption.
  - econstructor; eauto.
Qed.

Definition steps env0 stack0 stmts0 env1 stack1 stmts1 :=
  exists iters, stepIters iters env0 stack0 stmts0 env1 stack1 stmts1.

Lemma stepsConcat env0 stack0 stmts0 env1 stack1 stmts1 stmts2
  (Hsteps: steps env0 stack0 stmts0 env1 stack1 stmts1):
  steps env0 stack0 (stmts0 ++ stmts2) env1 stack1 (stmts1 ++ stmts2).
Proof.
  destruct Hsteps. eexists.
  eapply stepItersConcat. eassumption.
Qed.

Lemma stepsArrow env0 stack0 stmts0 env1 stack1 stmts1 env2 stack2 stmts2
  (Hsteps1: steps env0 stack0 stmts0 env1 stack1 stmts1)
  (Hsteps2: steps env1 stack1 stmts1 env2 stack2 stmts2):
  steps env0 stack0 stmts0 env2 stack2 stmts2.
Proof.
  destruct Hsteps1. destruct Hsteps2.
  eexists. eapply stepItersArrow; eassumption.
Qed.

Definition returns stmts env res :=
  exists rest stack, steps ([] :: env) [] stmts (res :: rest) stack [].
  
Lemma retDet stmts0 env0 res2 res3
  (Hrets1: returns stmts0 env0 res2)
  (Hrets2: returns stmts0 env0 res3):
  res2 = res3.
Proof.
  destruct Hrets1 as [? [? [? HstepIters1]]].
  destruct Hrets2 as [? [? [? HstepIters2]]].
  rewrite -> (stepItersTerm _ _ _ _ _ _ _ _ _ HstepIters1 HstepIters2) in HstepIters1.
  destruct (stepItersDet _ _ _ _ _ _ _ _ _ _ HstepIters1 HstepIters2) as [H [? ?]].
  inversion H.
  auto.
Qed.


(* function leftpad(c, n, s) { *)
(* let r; *)

Definition setup :=
  (* let l = s.length; *)
  [Var; LengthOf 3; Put 4;
  (* if (n < l) *)
  Get 2; Get 4; LessThan;
  (* { n = l; } *)
  If [Get 4; Put 2] [];
  (* r = Array(n); *)
  Get 2; NewArray 0].

Definition copyLoop :=
  (* while (0 < l) { *)
  While [Val (Nat 0); Get 4; LessThan]
  (* l = l - 1; *)
  [Get 4; Val (Nat 1); Minus; Put 4;
  (* n = n - 1; *)
  Get 2; Val (Nat 1); Minus; Put 2;
  (* r[n] = s[l]; *)
  Get 2; Get 4; GetAt 3; PutAt 0].
  (* } *)

Definition padLoop :=
  (* while (0 < n) { *)
  While [Val (Nat 0); Get 2; LessThan]
  (* n = n - 1; *)
  [Get 2; Val (Nat 1); Minus; Put 2;
  (* r[n] = c; *)
  Get 2; Get 1; PutAt 0].
  (* } *)

Definition leftpad :=
  setup ++ [copyLoop] ++ [padLoop].

(* return r; *)
(* } *)


Fact example1:
  returns leftpad
    [[Char "!"]; [Nat 5]; [Char "f"; Char "o"; Char "o"]]
    [Char "!"; Char "!"; Char "f"; Char "o"; Char "o"].
Proof.
  repeat (econstructor; simpl; eauto).
Qed.

Fact example2:
  returns leftpad
    [[Char "!"]; [Nat 0]; [Char "f"; Char "o"; Char "o"]]
    [Char "f"; Char "o"; Char "o"].
Proof.
  repeat (econstructor; simpl; eauto).
Qed.


Lemma setted c n s stack:
  steps
    [[]; [Char c]; [Nat n]; s] stack setup
    [repeat Null ((if n <? length s then 0 else n - length s) + length s) ++ skipn (length s) s; [Char c]; [Nat ((if n <? length s then 0 else n - length s) + length s)]; s; [Nat (length s)]] stack [].
Proof.
  rewrite -> skipn_all.
  rewrite -> app_nil_r.
  destruct (n <? length s) eqn:Hlt.
  - repeat (econstructor; simpl; try (rewrite -> Hlt); eauto).
  - assert (Hsa: n - length s + length s = n). {
      apply Nat.sub_add.
      apply Nat.nlt_ge.
      apply (not_iff_compat (Nat.ltb_lt _ _)).
      rewrite -> Hlt.
      auto.
    }
    rewrite -> Hsa.
    repeat (econstructor; simpl; try (rewrite -> Hlt); eauto).
Qed.

Lemma skipnS {A: Set} count (full: list A)
  (Hlen: count < length full):
  exists elem, nth_error full count = Some elem /\
  skipn count full = elem :: skipn (S count) full.
Proof.
  revert count Hlen. induction full; intros.
  - inversion Hlen.
  - destruct count.
    + simpl. eauto.
    + apply IHfull. apply le_S_n. auto.
Qed.

Lemma skipnRepeat {A: Set} count (elem: A) tail:
  skipn count (repeat elem count ++ tail) = tail.
Proof.
  revert elem tail. induction count; intros.
  - auto.
  - eapply IHcount.
Qed.

Lemma firstnRepeat {A: Set} count (elem: A) tail:
  firstn count (repeat elem count ++ tail) =
    repeat elem count.
Proof.
  revert elem tail. induction count; intros.
  - auto.
  - simpl. f_equal. eapply IHcount.
Qed.

Lemma copyRest c d l s stack
  (Hlen: l <= length s):
  steps
    [repeat Null (d + l) ++ skipn l s; [Char c]; [Nat (d + l)]; s; [Nat l]] stack [copyLoop]
    [repeat Null d ++ s; [Char c]; [Nat d]; s; [Nat 0]] stack [].
Proof.
  revert s Hlen.
  induction l; intros.
  - rewrite -> Nat.add_0_r.
    repeat (econstructor; simpl; eauto).
  - rewrite -> Nat.add_succ_r.
    destruct (skipnS _ _ Hlen) as [? [? Hskip]].
    simpl repeat.
    rewrite -> repeat_cons.
    rewrite <- app_assoc.
    eapply stepsArrow.
    2: { eapply IHl. apply Nat.lt_le_incl. auto. }
    rewrite -> Hskip.
    repeat (try (rewrite -> firstnRepeat); econstructor; simpl; try (rewrite -> Nat.sub_0_r); eauto).
    eapply skipnRepeat.
Qed.

Lemma padRest c n s done stack:
  steps
    [repeat Null n ++ done; [Char c]; [Nat n]; s; [Nat 0]] stack [padLoop]
    [repeat (Char c) n ++ done; [Char c]; [Nat 0]; s; [Nat 0]] stack [].
Proof.
  revert done.
  induction n; intros.
  - repeat (econstructor; simpl; eauto).
  - simpl repeat.
    rewrite -> repeat_cons.
    rewrite -> repeat_cons.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    eapply stepsArrow.
    2: { eapply IHn. }
    repeat (try (rewrite -> firstnRepeat); econstructor; simpl; try (rewrite -> Nat.sub_0_r); eauto).
    eapply skipnRepeat.
Qed.


Definition leftpadSpec c n s :=
  repeat (Char c) (if n <? length s then 0 else n - length s) ++ s.

Theorem leftpadEquiv c n s:
  returns leftpad
    [[Char c]; [Nat n]; s]
    (leftpadSpec c n s).
Proof.
  unfold leftpad.
  unfold leftpadSpec.
  eexists. eexists.
  eapply stepsArrow. {
    eapply stepsConcat.
    eapply setted.
  }
  rewrite -> app_nil_l.
  eapply stepsArrow. {
    eapply stepsConcat.
    eapply copyRest.
    eauto.
  }
  eapply padRest.
Qed.


Fact example1Equiv:
  returns leftpad
    [[Char "!"]; [Nat 5]; [Char "f"; Char "o"; Char "o"]]
    [Char "!"; Char "!"; Char "f"; Char "o"; Char "o"].
Proof.
  eapply leftpadEquiv.
Qed.

Fact example2Equiv:
  returns leftpad
    [[Char "!"]; [Nat 0]; [Char "f"; Char "o"; Char "o"]]
    [Char "f"; Char "o"; Char "o"].
Proof.
  eapply leftpadEquiv.
Qed.


Lemma yesClamp {A: Set} n (s: list A) (H: n < length s):
  (if n <? length s then 0 else n - length s) = 0.
Proof.
  assert (E: n <? length s = true). {
    apply Nat.ltb_lt. auto.
  }
  rewrite -> E.
  auto.
Qed.

Lemma noClamp {A: Set} n (s: list A) (H: n >= length s):
  (if n <? length s then 0 else n - length s) = n - length s.
Proof.
  assert (E: n <? length s = false). {
    apply Bool.not_true_iff_false.
    intro C.
    apply Nat.ltb_lt in C.
    revert C.
    apply Nat.le_ngt.
    assumption.
  }
  rewrite -> E.
  auto.
Qed.

Theorem leftpadLen c n s:
  length (leftpadSpec c n s) = max n (length s).
Proof.
  unfold leftpadSpec.
  destruct (Nat.lt_ge_cases n (length s)).
  - rewrite -> (Nat.max_r _ _ (Nat.lt_le_incl _ _ H)).
    rewrite -> (yesClamp _ _ H).
    auto.
  - rewrite -> (Nat.max_l _ _ H).
    rewrite -> (noClamp _ _ H).
    rewrite -> app_length.
    rewrite -> repeat_length.
    apply Nat.sub_add.
    assumption.
Qed.

Theorem leftpadPre c n s i (Hi: i < n - length s):
  nth_error (leftpadSpec c n s) i = Some (Char c).
Proof.
  unfold leftpadSpec.
  destruct (Nat.lt_ge_cases n (length s)).
  - rewrite -> (proj2 (Nat.sub_0_le _ _) (Nat.lt_le_incl _ _ H)) in Hi.
    inversion Hi.
  - rewrite -> (noClamp _ _ H).
    rewrite <- (repeat_length (Char c) (n - length s)) in Hi.
    rewrite -> (nth_error_app1 _ _ Hi).
    rewrite -> (repeat_length _ _) in Hi.
    revert Hi.
    generalize (n - length s) as count.
    clear H n s.
    revert c.
    induction i; intros; destruct count.
    + inversion Hi.
    + auto.
    + inversion Hi.
    + simpl. eapply IHi. apply Nat.succ_lt_mono. assumption.
Qed.

Theorem leftpadSuf c n s i (Hi: i < length s):
  exists sc,
  nth_error (leftpadSpec c n s) (max (n - length s) 0 + i) = Some sc /\
  nth_error s i = Some sc.
Proof.
  unfold leftpadSpec.
  destruct (Nat.lt_ge_cases n (length s)).
  - rewrite -> (yesClamp _ _ H).
    rewrite -> (proj2 (Nat.sub_0_le _ _) (Nat.lt_le_incl _ _ H)).
    simpl.
    apply nth_error_Some in Hi.
    destruct (nth_error s i).
    + eauto.
    + contradiction.
  - rewrite -> (noClamp _ _ H).
    rewrite <- (Nat.sub_add _ _ H) in H.
    revert H.
    replace (le (length s)) with (le (0 + length s)) by (f_equal; auto).
    intros.
    apply Nat.add_le_mono_r in H.
    rewrite -> (Nat.max_l _ _ H).
    assert (E: length (repeat (Char c) (n - length s)) <= (n - length s + i)). {
      rewrite -> (repeat_length _ _).
      replace (le (n - length s)) with (le (n - length s + 0))
        by (f_equal; apply Nat.add_0_r).
      apply Nat.add_le_mono_l.
      apply Nat.le_0_l.
    }
    rewrite -> (nth_error_app2 _ _ E).
    rewrite -> (repeat_length _ _).
    rewrite -> Nat.add_comm.
    rewrite -> Nat.add_sub.
    apply nth_error_Some in Hi.
    destruct (nth_error s i).
    + eauto.
    + contradiction.
Qed.