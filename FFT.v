Require Import Complex Program.Equality Classes.Morphisms.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local Open Scope C_scope.

Inductive slist (T : Set) : nat -> Set :=
  | Elem : T -> slist T O
  | Join : forall n, slist T n -> slist T n -> slist T (S n).

Definition elem_destruct (T : Set) (xs : slist T O) : T :=
  let 'Elem x := xs in x.
Definition join_destruct_l (T : Set) n (xs : slist T (S n)) : slist T n :=
  let 'Join _ l _ := xs in l.
Definition join_destruct_r (T : Set) n (xs : slist T (S n)) : slist T n :=
  let 'Join _ _ r := xs in r.

Fixpoint smap (T U : Set) n (f : T -> U) (xs : slist T n) : slist U n :=
  match xs with
    | Elem x => Elem (f x)
    | Join _ xs ys => Join (smap f xs) (smap f ys)
  end.

Fixpoint sfold (T : Set) (f : T -> T -> T) n (xs : slist T n) : T :=
  match xs with
    | Elem x => x
    | Join _ xs ys => f (sfold f xs) (sfold f ys)
  end.

Fixpoint scombine (T U : Set) n (xs : slist T n) (ys : slist U n) : slist (T * U) n :=
  match xs, ys with
    | Elem x, ys => Elem (x, elem_destruct ys)
    | Join _ xs0 xs1, ys => Join (scombine xs0 (join_destruct_l ys))
                                 (scombine xs1 (join_destruct_r ys))
  end.

Fixpoint sseq (v n : nat) : slist nat n :=
  match n with
    | O => Elem v
    | S n' => Join (sseq v n') (sseq (v + 2^n') n')
  end.

Fixpoint alternate_split (T : Set) n (xs : slist T (S n)) : slist T n * slist T n :=
  match xs in slist _ m return (match m with
                                  | O => unit
                                  | S m' => slist T m' * slist T m'
                                end) with
    | Elem _ => tt
    | Join O xs ys => (xs, ys)
    | Join (S _) xs ys =>
        let xsl_xsr := alternate_split xs in
        let ysl_ysr := alternate_split ys in
        (Join (fst xsl_xsr) (fst ysl_ysr), Join (snd xsl_xsr) (snd ysl_ysr))
  end.

Fixpoint interleave (T : Set) n (xs ys : slist T n) : slist T (S n) :=
  match xs, ys with
    | Elem x, ys => Join (Elem x) ys
    | Join _ xs0 xs1, ys => Join (interleave xs0 (join_destruct_l ys))
                                 (interleave xs1 (join_destruct_r ys))
  end.

Definition dft Nlog2 (xs : slist C Nlog2) : slist C Nlog2 :=
  smap (fun k =>
    sfold Cadd
      (smap (fun x_n : C * nat =>
         let (x, n) := x_n in
         x * Cexp (Cmake 0 (-2 * PI * INR n * INR k / INR (2^Nlog2)))
       ) (scombine xs (sseq 0 Nlog2)))
  ) (sseq 0 Nlog2).

Fixpoint fft Nlog2 (xs : slist C Nlog2) : slist C Nlog2 :=
  match Nlog2, xs with
  | O, xs => xs
  | S Nlog2m1, xs =>
    let (evens, odds) := alternate_split xs in
    let fft_evens := fft evens in
    let fft_odds := fft odds in
    let twiddled := smap (fun x_k : C * nat =>
        let (x, k) := x_k in
        Cexp (Cmake 0 (-2 * PI * INR k / INR (2^Nlog2))) * x
      ) (scombine fft_odds (sseq 0 Nlog2m1)) in
    Join (smap (fun x_y : C * C => let (x, y) := x_y in x + y)
          (scombine fft_evens twiddled))
         (smap (fun x_y : C * C => let (x, y) := x_y in x - y)
          (scombine fft_evens twiddled))
  end.

Global Instance smap_morphism : forall A B n, Proper ((pointwise_relation _ eq) ==> eq ==> eq) (@smap A B n).
Proof.
  simpl_relation. induction y0.
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite IHy0_1, IHy0_2. reflexivity.
Qed.

Section slist_pairwise_ind.
  Variable T : Set.
  Variable P : forall n, slist T n -> slist T n -> Prop.
  Hypothesis Elem_case : forall x y, P (Elem x) (Elem y).
  Hypothesis Join_case :
    forall n (xs0 xs1 : slist T n), P xs0 xs1 ->
      forall (ys0 ys1 : slist T n), P ys0 ys1 -> P (Join xs0 xs1) (Join ys0 ys1).
  Hypothesis Join_case2 :
    forall n (xs0 xs1 : slist T n), P xs0 xs1 ->
      forall (ys0 ys1 : slist T n), P ys0 ys1 -> P (Join xs0 ys0) (Join xs1 ys1).
  Fixpoint slist_pairwise_ind n (xs ys : slist T n) {struct n} : P xs ys.
  Proof.
    destruct n; dependent destruction xs; dependent destruction ys.
    apply Elem_case.
    apply Join_case; apply slist_pairwise_ind.
  Qed.
  Fixpoint slist_pairwise_ind2 n (xs ys : slist T n) {struct n} : P xs ys.
  Proof.
    destruct n; dependent destruction xs; dependent destruction ys.
    apply Elem_case.
    apply Join_case2; apply slist_pairwise_ind2.
  Qed.
End slist_pairwise_ind.

Lemma alternate_split_parts :
  forall (T : Set) n (xs ys : slist T (S n)),
    alternate_split (Join xs ys) =
    (Join (fst (alternate_split xs)) (fst (alternate_split ys)),
     Join (snd (alternate_split xs)) (snd (alternate_split ys))).
Proof.
  unfold alternate_split. fold alternate_split. reflexivity.
Qed.

Lemma interleave_alternate :
  forall (T : Set) n (xs : slist T (S n)), interleave (fst (alternate_split xs))
                                                      (snd (alternate_split xs)) = xs.
Proof.
  intros. dependent destruction xs.
  induction T, n, xs1, xs2 using slist_pairwise_ind.
  - reflexivity.
  - intros. rewrite alternate_split_parts.
    unfold interleave. simpl. fold interleave.
    unfold alternate_split in IHxs2_1, IHxs2_2.
    fold alternate_split in IHxs2_1, IHxs2_2.
    rewrite IHxs2_1, IHxs2_2.
    reflexivity.
Qed.

Lemma alternate_interleave :
  forall (T : Set) n (xs ys : slist T n), alternate_split (interleave xs ys) = (xs, ys).
Proof.
  intros.
  induction T, n, xs, ys using slist_pairwise_ind2.
  - reflexivity.
  - unfold interleave. fold interleave. simpl. rewrite IHys1, IHys2. simpl. reflexivity.
Qed.

Section slist_alternate_ind.
  Variable T : Set.
  Variable P : forall n, slist T n -> Prop.
  Hypothesis Elem_case : forall x, P (Elem x).
  Hypothesis Join_case :
    forall n (xs : slist T n), P xs -> forall ys : slist T n, P ys -> P (interleave xs ys).
  Fixpoint slist_alternate_ind n (xs : slist T n) {struct n} : P xs.
  Proof.
    destruct n.
    - dependent destruction xs. apply Elem_case.
    - refine (let s := alternate_split xs in
              _ (Join_case (slist_alternate_ind _ (fst s)) (slist_alternate_ind _ (snd s)))).
      subst s. dependent destruction xs. rewrite interleave_alternate. trivial.
  Qed.
End slist_alternate_ind.

Lemma Csum_alternate_split :
  forall n (xs : slist C (S n)),
    sfold Cadd xs = sfold Cadd (fst (alternate_split xs)) +
                    sfold Cadd (snd (alternate_split xs)).
Proof.
  dependent destruction xs.
  induction C, n, xs1, xs2 using slist_pairwise_ind; subst S.
  - reflexivity.
  - intros. unfold sfold at 1. fold sfold.
    unfold sfold at 1 in IHxs2_1. fold sfold in IHxs2_1.
    unfold sfold at 1 in IHxs2_2. fold sfold in IHxs2_2.
    rewrite IHxs2_1, IHxs2_2. simpl. ring.
Qed.

Lemma alternate_split_smap :
  forall (T U : Set) n (f : T -> U) (xs : slist T (S n)),
    alternate_split (smap f xs) = (smap f (fst (alternate_split xs)),
                                   smap f (snd (alternate_split xs))).
Proof.
  dependent destruction xs.
  induction T, n, xs1, xs2 using slist_pairwise_ind.
  - reflexivity.
  - simpl. simpl in IHxs2_1, IHxs2_2. rewrite IHxs2_1, IHxs2_2. reflexivity.
Qed.

Section slist_pairwise_dual_ind.
  Variables T U : Set.
  Variable P : forall n, slist T n -> slist T n -> slist U n -> slist U n -> Prop.
  Hypothesis Elem_case : forall w x y z, P (Elem w) (Elem x) (Elem y) (Elem z).
  Hypothesis Join_case : forall n (xs1 xs2 : slist T n) (ys1 ys2 : slist U n),
    P xs1 xs2 ys1 ys2 ->
    forall (xs1' xs2' : slist T n) (ys1' ys2' : slist U n),
    P xs1' xs2' ys1' ys2' ->
    P (Join xs1 xs2) (Join xs1' xs2') (Join ys1 ys2) (Join ys1' ys2').
  Fixpoint slist_pairwise_dual_ind n (xs1 xs2 : slist T n) (ys1 ys2 : slist U n) :
    P xs1 xs2 ys1 ys2.
  Proof.
    destruct n; dependent destruction xs1; dependent destruction xs2;
                dependent destruction ys1; dependent destruction ys2.
    - apply Elem_case.
    - apply Join_case; apply slist_pairwise_dual_ind.
  Qed.
End slist_pairwise_dual_ind.

Lemma alternate_split_scombine :
  forall (T U : Set) n (xs : slist T (S n)) (ys : slist U (S n)),
    alternate_split (scombine xs ys) =
      (scombine (fst (alternate_split xs)) (fst (alternate_split ys)),
       scombine (snd (alternate_split xs)) (snd (alternate_split ys))).
Proof.
  dependent destruction xs. dependent destruction ys.
  induction T, U, n, xs1, xs2, ys1, ys2 using slist_pairwise_dual_ind.
  - reflexivity.
  - simpl. simpl in IHys2_1, IHys2_2. rewrite IHys2_1, IHys2_2. reflexivity.
Qed.

Lemma smap_smap :
  forall (T U V : Set) n (f : T -> U) (g : U -> V) (h : T -> V) (xs : slist T n),
  (forall x, g (f x) = h x) -> smap g (smap f xs) = smap h xs.
Proof.
  intros. induction xs.
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite IHxs1, IHxs2. reflexivity.
Qed. 

Lemma smap_smap2 :
  forall (T U V W : Set) n
    (f : T -> U) (g : U -> W) (h : T -> V) (i : V -> W) (xs : slist T n),
  (forall x, g (f x) = i (h x)) -> smap g (smap f xs) = smap i (smap h xs).
Proof.
  intros. induction xs.
  - simpl. f_equal. apply H.
  - simpl. f_equal; [apply IHxs1 | apply IHxs2].
Qed.

Lemma sseq_base : forall n m, sseq m n = smap (fun x => x + m)%nat (sseq 0 n).
Proof.
  induction n.
  - reflexivity.
  - simpl. intro m. rewrite (IHn m), (IHn (m + 2 ^ n))%nat, (IHn (2 ^ n)).
    f_equal. symmetry. apply smap_smap. intro. ring.
Qed.

Lemma sseq_alt_def : forall n,
  sseq 0 (S n) = Join (sseq 0 n) (smap (fun x => x + 2 ^ n)%nat (sseq 0 n)).
Proof.
  simpl. intro. rewrite (sseq_base n (2 ^ n)). reflexivity.
Qed.

Lemma alternate_split_sseq : forall n,
  alternate_split (sseq 0 (S n)) =
    (smap (fun n => n * 2)%nat (sseq 0 n),
     smap (fun n => n * 2 + 1)%nat (sseq 0 n)).
Proof.
  induction n.
  - reflexivity.
  - rewrite sseq_alt_def at 1. rewrite sseq_alt_def at 3 4.
    change (alternate_split (Join (sseq 0 (S n))
      (smap (fun x : nat => (x + 2 ^ S n)%nat) (sseq 0 (S n)))))
    with (let xsl_xsr := alternate_split (sseq 0 (S n)) in
      let ysl_ysr := alternate_split (smap (fun x : nat => (x + 2 ^ S n)%nat) (sseq 0 (S n))) in
      (Join (fst xsl_xsr) (fst ysl_ysr), Join (snd xsl_xsr) (snd ysl_ysr))).
    rewrite alternate_split_smap. rewrite IHn. simpl.
    do 2 f_equal.
    + do 2 rewrite (smap_smap _ _ (fun x => x * 2 + 2 ^ S n))%nat by (intro; simpl; ring).
      reflexivity.
    + do 2 rewrite (smap_smap _ _ (fun x => x * 2 + 2 ^ S n + 1))%nat by (intro; simpl; ring).
      reflexivity.
Qed.

Lemma scombine_smap_r :
  forall (U V : Set) (f : U -> V) (T : Set) n (xs : slist T n) (ys : slist U n),
  scombine xs (smap f ys) = smap (fun x_y : T * U => let (x, y) := x_y in (x, f y))
                              (scombine xs ys).
Proof.
  induction n; dependent destruction xs; dependent destruction ys.
  - reflexivity.
  - simpl. do 2 rewrite IHn. reflexivity.
Qed.

Lemma INR_2pow_gt_zero : forall n, (INR (2 ^ n) > 0)%R.
Proof.
  induction n.
  - simpl. prove_sup.
  - simpl. do 2 rewrite plus_INR. simpl. rewrite Rplus_0_r. prove_sup; assumption.
Qed.

Lemma INR_2pow_not_zero : forall n, INR (2 ^ n) <> 0%R.
Proof.
  intro. apply Rlt_dichotomy_converse. right. apply INR_2pow_gt_zero.
Qed.

Lemma Cmul_dist_sum : forall s n (xs : slist C n),
  s * sfold Cadd xs = sfold Cadd (smap (fun x => s * x) xs).
Proof.
  induction xs.
  - reflexivity.
  - simpl. rewrite <- IHxs1, <- IHxs2. ring.
Qed.

Theorem fft_correct : forall Nlog2 (xs : slist C Nlog2), fft xs = dft xs.
Proof.
  apply slist_alternate_ind.
  - unfold dft. simpl. replace (-2 * PI * 0 * 0 / 1)%R with 0%R by field.
    unfold Cexp. simpl. rewrite exp_0, cos_0, sin_0. destruct x. unfold Cmul. simpl.
    do 2 f_equal; ring.
  - intros. unfold fft. fold fft. rewrite alternate_interleave. unfold dft.
    rewrite H, H0.
    setoid_rewrite Csum_alternate_split.
    setoid_rewrite alternate_split_smap.
    rewrite alternate_split_scombine.
    rewrite alternate_interleave.
    rewrite alternate_split_sseq.
    unfold fst, snd.
    rewrite (scombine_smap_r _ xs), (scombine_smap_r _ ys).
    assert (forall sn (ss : slist nat sn),
      smap (fun k : nat =>
        sfold Cadd
          (smap (fun x_m : C * nat =>
                 let (x, m) := x_m in
                 x * Cexp (Cmake 0 (-2 * PI * INR m * INR k / INR (2 ^ S n))))
                (smap (fun x_m : C * nat =>
                       let (x, m) := x_m in (x, (m * 2)%nat))
                      (scombine xs (sseq 0 n)))) +
        sfold Cadd
          (smap (fun x_m : C * nat =>
                 let (x, m) := x_m in
                 x * Cexp (Cmake 0 (-2 * PI * INR m * INR k / INR (2 ^ S n))))
                (smap (fun x_m : C * nat =>
                       let (x, m) := x_m in (x, (m * 2 + 1)%nat))
                      (scombine ys (sseq 0 n))))
      ) ss
    =
      smap (fun k : nat =>
        sfold Cadd
          (smap (fun x_m : C * nat =>
                 let (x, m) := x_m in
                 x * Cexp (Cmake 0 (-2 * PI * INR m * INR k / INR (2 ^ n))))
                (scombine xs (sseq 0 n))) +
        Cexp (Cmake 0 (-2 * PI * INR k / INR (2 ^ S n))) *
        sfold Cadd
          (smap (fun x_m : C * nat =>
                 let (x, m) := x_m in
                 (x * Cexp (Cmake 0 (-2 * PI * INR m * INR k / INR (2 ^ n)))))
                (scombine ys (sseq 0 n)))
      ) ss
    ).
    + induction ss.
      * simpl.
        { do 2 f_equal.
          - f_equal. apply smap_smap. intro x_m. destruct x_m. do 3 f_equal.
            replace (INR (2 ^ n + (2 ^ n + 0))) with (INR (2 ^ n) * 2)%R.
            + rewrite mult_INR. simpl. field. apply INR_2pow_not_zero.
            + replace 2%R with (INR 2) by reflexivity.
              rewrite <- mult_INR. f_equal. ring.
          - rewrite Cmul_dist_sum. f_equal.
            apply smap_smap2. intro x_m. destruct x_m.
            replace (Cmake 0 (-2 * PI * INR (n0 * 2 + 1) * INR t / INR (2 ^ n + (2 ^ n + 0))))%R
            with (Cmake 0 (-2 * PI * INR t / INR (2 ^ n + (2 ^ n + 0)))%R +
                  Cmake 0 (-2 * PI * INR n0 * INR t / INR (2 ^ n))%R).
            + rewrite Cexp_add. ring.
            + unfold Cadd. simpl. f_equal.
              * ring.
              * rewrite (plus_INR (n0 * 2) 1). rewrite mult_INR. simpl.
                { replace (-2 * PI * (INR n0 * (1 + 1) + 1) * INR t / INR (2 ^ n + (2 ^ n + 0)))%R
                  with (-2 * PI * INR t / INR (2 ^ n + (2 ^ n + 0)) +
                        -2 * PI * INR n0 * 2 * INR t / INR (2 ^ n + (2 ^ n + 0)))%R.
                  - f_equal.
                    replace (INR (2 ^ n + (2 ^ n + 0))) with (INR (2 ^ n) * 2)%R.
                    + field. apply INR_2pow_not_zero.
                    + replace 2%R with (INR 2) by reflexivity.
                      rewrite <- mult_INR. f_equal. ring.
                  - field. apply (INR_2pow_not_zero (S n)). } }
      * unfold smap. fold smap. rewrite IHss1, IHss2. reflexivity.
    + rewrite H1. clear H1. unfold sseq. fold sseq. unfold smap. fold smap.
      replace (0 + 2 ^ n)%nat with (2 ^ n) by reflexivity.
      rewrite (sseq_base n (2 ^ n)).
      rewrite (smap_smap _ _ (fun k : nat =>
        sfold Cadd
          (smap (fun x_m : C * nat =>
                 let (x, m) := x_m in
                 x * Cexp (Cmake 0 (-2 * PI * INR m * INR k / INR (2 ^ n))))
                (scombine xs (sseq 0 n))) -
        Cexp (Cmake 0 (-2 * PI * INR k / INR (2 ^ S n))) *
        sfold Cadd
          (smap (fun x_m : C * nat =>
                 let (x, m) := x_m in
                 x * Cexp (Cmake 0 (-2 * PI * INR m * INR k / INR (2 ^ n))))
                (scombine ys (sseq 0 n)))
      )).
      * unfold dft.
        { assert (forall sn (ss : slist nat sn),
            Join
              (smap (fun x_y : C * C => let (x, y) := x_y in x + y)
                    (scombine
                       (smap (fun k : nat =>
                              sfold Cadd
                                (smap (fun x_m : C * nat =>
                                       let (x, m) := x_m in
                                       x * Cexp (Cmake 0 (-2 * PI * INR m * INR k /
                                                          INR (2 ^ n))))
                                      (scombine xs (sseq 0 n))))
                             ss)
                       (smap (fun x_k : C * nat =>
                              let (x, k) := x_k in
                              Cexp (Cmake 0 (-2 * PI * INR k / INR (2 ^ S n))) * x)
                             (scombine
                                (smap (fun k : nat =>
                                       sfold Cadd
                                         (smap (fun x_m : C * nat =>
                                                let (x, m) := x_m in
                                                x * Cexp (Cmake 0
                                                          (-2 * PI * INR m * INR k /
                                                           INR (2 ^ n))))
                                               (scombine ys (sseq 0 n))))
                                      ss)
                                ss))))
              (smap (fun x_y : C * C => let (x, y) := x_y in x - y)
                    (scombine
                       (smap (fun k : nat =>
                              sfold Cadd
                                (smap (fun x_m : C * nat =>
                                       let (x, m) := x_m in
                                       x * Cexp (Cmake 0 (-2 * PI * INR m * INR k /
                                                          INR (2 ^ n))))
                                      (scombine xs (sseq 0 n))))
                             ss)
                       (smap (fun x_k : C * nat =>
                              let (x, k) := x_k in
                              Cexp (Cmake 0 (-2 * PI * INR k / INR (2 ^ S n))) * x)
                             (scombine
                                (smap (fun k : nat =>
                                       sfold Cadd
                                         (smap (fun x_m : C * nat =>
                                                let (x, m) := x_m in
                                                x * Cexp (Cmake 0
                                                          (-2 * PI * INR m * INR k /
                                                           INR (2 ^ n))))
                                               (scombine ys (sseq 0 n))))
                                      ss)
                                ss))))
          =
            Join
              (smap (fun k : nat =>
                     sfold Cadd
                       (smap (fun x_m : C * nat =>
                              let (x, m) := x_m in
                              x * Cexp (Cmake 0 (-2 * PI * INR m * INR k /
                                                 INR (2 ^ n))))
                             (scombine xs (sseq 0 n))) +
                     Cexp (Cmake 0 (-2 * PI * INR k / INR (2 ^ S n))) *
                     sfold Cadd
                       (smap (fun x_m : C * nat =>
                              let (x, m) := x_m in
                              x * Cexp (Cmake 0 (-2 * PI * INR m * INR k /
                                                 INR (2 ^ n))))
                             (scombine ys (sseq 0 n))))
                    ss)
              (smap (fun k : nat =>
                     sfold Cadd
                       (smap (fun x_m : C * nat =>
                              let (x, m) := x_m in
                              x * Cexp (Cmake 0 (-2 * PI * INR m * INR k /
                                                 INR (2 ^ n))))
                             (scombine xs (sseq 0 n))) -
                     Cexp (Cmake 0 (-2 * PI * INR k / INR (2 ^ S n))) *
                     sfold Cadd
                       (smap (fun x_m : C * nat =>
                              let (x, m) := x_m in
                              x * Cexp (Cmake 0 (-2 * PI * INR m * INR k /
                                                 INR (2 ^ n))))
                             (scombine ys (sseq 0 n))))
                    ss)
          ).
          - intros. f_equal.
            + induction ss.
              * reflexivity.
              * simpl. simpl in IHss1, IHss2. rewrite IHss1, IHss2. reflexivity.
            + induction ss.
              * reflexivity.
              * simpl. simpl in IHss1, IHss2. rewrite IHss1, IHss2. reflexivity.
          - apply H1. }
      * intro k.
        { replace (Cexp (Cmake 0 (-2 * PI * INR (k + 2 ^ n) / INR (2 ^ S n))))
          with (-Cexp (Cmake 0 (-2 * PI * INR k / INR (2 ^ S n)))).
          - assert (forall a b c, a + - b * c = a - b * c) by (intros; ring).
            rewrite H1. clear H1.
            assert (forall sn (ss : slist (C * nat) sn),
              smap (fun x_m : C * nat =>
                    let (x, m) := x_m in
                    x * Cexp (Cmake 0 (-2 * PI * INR m * INR (k + 2 ^ n) / INR (2 ^ n))))
                   ss =
              smap (fun x_m : C * nat =>
                    let (x, m) := x_m in
                    x * Cexp (Cmake 0 (-2 * PI * INR m * INR k / INR (2 ^ n))))
                   ss
            ).
            + intros. induction ss.
              * simpl. destruct t. do 2 f_equal. rewrite plus_INR.
                { replace (-2 * PI * INR n0 * (INR k + INR (2 ^ n)) / INR (2 ^ n))%R
                  with (- (2 * PI * INR n0 * INR k / INR (2 ^ n) + 2 * INR n0 * PI))%R.
                  - unfold Cexp. simpl.
                    rewrite cos_neg, sin_neg, cos_period, sin_period,
                            <- cos_neg, <- sin_neg.
                    do 3 f_equal; field; apply INR_2pow_not_zero.
                  - field. apply INR_2pow_not_zero. }
              * unfold smap. fold smap. rewrite IHss1, IHss2. reflexivity.
            + do 2 rewrite H1. reflexivity.
          - rewrite plus_INR.
            replace (Cexp (Cmake 0 (-2 * PI * (INR k + INR (2 ^ n)) / INR (2 ^ S n))))
            with (Cexp (Cmake 0 (-2 * PI * INR (2 ^ n) / INR (2 ^ S n))) *
                  Cexp (Cmake 0 (-2 * PI * INR k / INR (2 ^ S n)))).
            + replace (-2 * PI * INR (2 ^ n) / INR (2 ^ S n))%R with (- PI)%R.
              * unfold Cexp at 2. simpl.
                rewrite exp_0, cos_neg, sin_neg, cos_PI, sin_PI.
                unfold Cneg, Cmul. simpl. f_equal; ring.
              * { replace (INR (2 ^ S n)) with (INR (2 ^ n) * 2)%R.
                  - field. apply INR_2pow_not_zero.
                  - replace 2%R with (INR 2) by reflexivity.
                    rewrite <- mult_INR. f_equal. simpl. ring. }
            + rewrite <- Cexp_add. unfold Cadd. simpl. do 2 f_equal; field.
              apply (INR_2pow_not_zero (S n)). }
Qed.
