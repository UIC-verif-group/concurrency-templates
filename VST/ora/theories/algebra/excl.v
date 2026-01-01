From iris.algebra Require Import excl.
From iris_ora.algebra Require Export ora.
From iris.prelude Require Import options.

Section excl.
Context {A : ofe}.

Instance excl_orderN : OraOrderN (excl A) := dist.
Instance excl_order : OraOrder (excl A) := equiv.

Definition excl_ora_mixin : OraMixin (excl A).
Proof.
  split; try apply _; try done.
  - intros ???? Hv Ho.
    by rewrite -Ho in Hv; apply exclusiveN_r in Hv.
  - eauto.
  - apply dist_S.
  - by intros ???? ->.
  - apply equiv_dist.
  - inversion 1.
Qed.

End excl.

Canonical Structure exclR (A : ofe) := Ora (excl A) (@excl_ora_mixin A).

#[export] Instance excl_ora_discrete A : OfeDiscrete A → OraDiscrete (exclR A).
Proof.
  intros (? & ?)%excl_cmra_discrete.
  constructor; done.
Qed.
