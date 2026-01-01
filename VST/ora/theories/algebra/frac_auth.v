From iris.algebra Require Export frac_auth.
From iris_ora.algebra Require Export auth.
From iris_ora.algebra Require Import ext_order.
From iris.prelude Require Import options.

(* As long as this (or any) algebra isn't used in a core resource construction,
   it's sufficient to define it as an inclR wrapper over a standard cmra. *)
Section frac_auth.

Context (A : cmra).

Canonical Structure frac_authR := inclR (frac_authR A).
Canonical Structure frac_authUR := Uora frac_authR (ucmra_mixin (frac_authUR A)).

End frac_auth.

Lemma frac_auth_frag_op : forall {A : cmra} (q1 q2 : Qp) (a1 a2 : A),
  ◯F{q1 + q2} (a1 ⋅ a2) ≡ ◯F{q1} a1 ⋅ ◯F{q2} a2.
Proof.
  intros; apply frac_auth_frag_op.
Qed.
