From iris.algebra Require Import dfrac.
From iris_ora.algebra Require Export ora.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments pcore _ _ !_ /.

Section ora.

  Local Instance dfrac_order : OraOrder dfrac := λ a b, a = b ∨ a ⋅ DfracDiscarded = b.

  Local Instance discard_increasing : Increasing DfracDiscarded.
  Proof.
    intros ?.
    rewrite /op /dfrac_op_instance; destruct y; hnf; auto.
  Qed.

  Definition dfrac_ora_mixin : DORAMixin dfrac.
  Proof.
    split.
    - rewrite /pcore /dfrac_pcore_instance; intros [| |]; inversion 1; apply _.
    - inversion 1; hnf; auto.
    - intros ??? [?|?] ?; subst.
      + eexists; split; [|hnf]; eauto.
      + destruct x; try discriminate; eexists; split; hnf; eauto.
    - intros ??? [?|?] [?|?]; subst; hnf; auto.
      destruct x; auto.
    - intros ??? [?|?]; subst; hnf; auto.
      right; by rewrite -assoc (comm _ y) assoc.
    - intros ??? [?|?]; subst; auto.
      eapply cmra_valid_op_l; eauto.
    - destruct x; inversion 1; subst; destruct y; eexists; split; hnf; eauto.
  Qed.

  Canonical Structure dfracR := discreteOra dfrac dfrac_ora_mixin.

  Global Instance dfrac_discarded_oracore_id : OraCoreId DfracDiscarded.
  Proof. by constructor. Qed.

  Global Instance dfrac_ora_discrete : OraDiscrete dfracR.
  Proof. apply discrete_ora_discrete. Qed.

End ora.
