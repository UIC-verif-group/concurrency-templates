From iris.algebra.lib Require Export excl_auth.
From iris_ora.algebra Require Export excl auth.
From iris.prelude Require Import options.

Lemma excl_rel_order : ∀ {A : ofe} n (x y : optionUR (exclR A)), ✓{n} y → x ≼ₒ{n} y → x ≼{n} y.
Proof.
  intros ????? [(-> & ?) | (? & ? & -> & -> & H)]%option_orderN'.
  - rewrite option_includedN; auto.
  - rewrite option_includedN; eauto 7.
Qed.

Definition excl_authR (A : ofe) := authR _ (@excl_rel_order A).
Definition excl_authUR (A : ofe) := authUR _ (@excl_rel_order A).
