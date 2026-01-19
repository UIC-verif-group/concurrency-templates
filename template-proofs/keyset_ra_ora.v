Set Warnings "-hiding-delimiting-key, -redundant-canonical-projection".
Require Import flows.keyset_ra.
From iris_ora Require Export ora.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _ !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments pcore _ _ !_ /.

Section keyset_ra.
  Context (K : Type) `{Countable K} `{EqDecision K}.

 Local Instance keyset_ra_order: OraOrder (prodT(K := K)) :=
   fun (a b: prodT(K := K)) => a = b \/ b = prodTop.

 Lemma Increasing_key_ra : forall a, Increasing a <-> a = ε \/ a = prodTop.
 Proof.
   split; intros Ha.
   - specialize (Ha ε).
     rewrite right_id in Ha.
     inversion Ha; auto. 
   - intros ?; destruct Ha.
     + subst a. rewrite left_id; hnf; auto. 
     + hnf. subst a. 
       destruct y.
       destruct p; simpl; auto.
       simpl; auto.
       simpl; auto.
 Qed.

 Definition keyset_ra_ora_mixin : DORAMixin prodT.
 Proof.
   split; try apply _; try done.
   - intros ???; rewrite Increasing_key_ra; destruct x; inversion H0; auto.
   - intros x y Hxy; inversion Hxy; hnf; auto.
   - intros x y cx Hxy HS. inversion HS.
     exists prodBot. split; [try done | hnf]; auto.
   - unfold Transitive.
     intros x y z Hxy Hyz; inversion Hxy; subst; inversion Hyz; subst; auto.
   - intros ??? Hxx; inversion Hxx; subst; hnf; auto.
   - intros ??? Hv. inversion Hv; subst; auto; inversion H0. 
   - intros ???;
       destruct cx; unfold pcore; destruct x; intros H1;
       inversion H1; subst; try eauto; eexists; inversion H3; subst;
       instantiate (1 := prodBot); split; auto; hnf; auto.
     Unshelve. auto. auto. auto. auto. auto. auto.
 Qed.

 Canonical Structure KsetRA := discreteOra (prodT(K := K)) keyset_ra_ora_mixin.
 Global Instance keyset_ora_discrete : OraDiscrete (prodT(K := K)).
 Proof.
   apply discrete_ora_discrete.
 Qed.
 Canonical Structure keysetUR : uora := Uora (prodT(K := K)) (keyset_ra.prod_ucmra_mixin (K := K)).
End keyset_ra.
