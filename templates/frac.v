Set Warnings "-hiding-delimiting-key, -redundant-canonical-projection".
From iris.algebra Require Import frac.
From iris_ora.algebra Require Export ora.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments pcore _ _ !_ /.

Section ora.
  Local Instance frac_order : OraOrder frac := λ a b, a = b.

  Definition frac_ora_mixin : DORAMixin frac.
  Proof.
    split; auto.
    - rewrite /pcore /frac_pcore_instance. inversion 1; apply _.
    - inversion 1; hnf; auto. subst. intros ?. exists cx. done.
    - intros ??? H1 H2. by rewrite H1 H2.
    - intros ??? H. by rewrite H.
    - intros ?? H1 H2. hnf in H2. by rewrite H2.
    - destruct x; inversion 1; subst; destruct y; eexists; split; hnf; eauto.
  Qed.

  Canonical Structure dfracR := discreteOra frac frac_ora_mixin.

  Global Instance frac_ora_discrete : OraDiscrete fracR.
  Proof. apply discrete_ora_discrete. Qed.
End ora.
