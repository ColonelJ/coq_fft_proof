Require Export Reals.

Set Implicit Arguments.
Set Asymmetric Patterns.

Record C : Set := Cmake {real: R; imag: R}.

Declare Scope C_scope.
Delimit Scope C_scope with C.
Local Open Scope C_scope.

Definition Czero : C := Cmake 0 0.
Definition Cone : C := Cmake 1 0.
Definition Cadd (a b : C) : C := Cmake (real a + real b) (imag a + imag b).
Definition Csub (a b : C) : C := Cmake (real a - real b) (imag a - imag b).
Definition Cneg (c : C) : C := Cmake (- real c) (- imag c).
Definition Cmul (a b : C) : C :=
  Cmake (real a * real b - imag a * imag b) (real a * imag b + real b * imag a).
Definition Cexp (c : C) : C := let real_exp := exp (real c) in
  Cmake (real_exp * cos (imag c)) (real_exp * sin (imag c)).

Notation "0" := Czero : C_scope.
Notation "1" := Cone : C_scope.
Infix "+" := Cadd : C_scope.
Infix "-" := Csub : C_scope.
Notation "- x" := (Cneg x) : C_scope.
Infix "*" := Cmul : C_scope.

Lemma Cadd_zero : forall c : C, 0 + c = c.
Proof.
  intros.
  unfold Cadd.
  destruct c.
  f_equal; simpl; ring.
Qed.

Lemma Cadd_comm : forall a b : C, a + b = b + a.
Proof.
  intros.
  unfold Cadd.
  f_equal; ring.
Qed.

Lemma Cadd_assoc : forall a b c : C, a + (b + c) = (a + b) + c.
Proof.
  intros.
  unfold Cadd.
  simpl.
  f_equal; ring.
Qed.

Lemma Cmul_one : forall c : C, 1 * c = c.
Proof.
  intros.
  unfold Cmul.
  destruct c.
  simpl.
  f_equal; ring.
Qed.

Lemma Cmul_comm : forall a b : C, a * b = b * a.
Proof.
  intros.
  unfold Cmul.
  f_equal; ring.
Qed.

Lemma Cmul_assoc : forall a b c : C, a * (b * c) = (a * b) * c.
Proof.
  intros.
  unfold Cmul.
  simpl.
  f_equal; ring.
Qed.

Lemma Cmul_dist : forall a b c : C, (a + b) * c = a * c + b * c.
Proof.
  intros.
  unfold Cmul, Cadd.
  simpl.
  f_equal; ring.
Qed.

Lemma Cadd_neg : forall a b : C, a - b = a + -b.
Proof.
  reflexivity.
Qed.

Lemma Cneg_def : forall c : C, c + -c = 0.
Proof.
  intros.
  unfold Cadd, Czero.
  destruct c.
  simpl.
  f_equal; ring.
Qed.

Add Ring C_ring : (mk_rt _ _ _ _ _ _ _ Cadd_zero Cadd_comm Cadd_assoc Cmul_one Cmul_comm Cmul_assoc Cmul_dist Cadd_neg Cneg_def).

Lemma Cexp_add : forall a b : C, Cexp (a + b) = Cexp a * Cexp b.
Proof.
  intros.
  unfold Cexp, Cmul.
  simpl.
  rewrite cos_plus, sin_plus, exp_plus.
  f_equal; ring.
Qed.
