From stdpp Require Export list gmap.
From iris.algebra Require Export list cmra.
From iris.algebra Require Import gset gmap.
From iris.algebra Require Import updates local_updates proofmode_classes big_op.
From iris.prelude Require Import options.
From iris_ora.algebra Require Export ora.

Lemma list_choice : forall {A B} (P : A -> B -> Prop) l, Forall (fun a => exists b, P a b) l ->
  exists l', Forall2 P l l'.
Proof.
  induction l.
  - exists nil; constructor.
  - inversion 1 as [| ?? [??]]; subst.
    destruct IHl; eauto.
Qed.

Section ora.

Context `{Countable K} {A : ora}.
Implicit Types m : gmap K A.

Instance gmap_orderN : OraOrderN (gmap K A) := λ n, map_relation (λ _, ora_orderN A n) (λ _ _, False) (λ _, Increasing).
Instance gmap_order : OraOrder (gmap K A) := map_relation (λ _, ora_order A) (λ _ _, False) (λ _, Increasing).

Lemma lookup_increasing : forall m i, Increasing m -> Increasing (m !! i).
Proof.
  intros ?? Hincr [a|].
  - specialize (Hincr {[ i := a ]} i).
    by rewrite lookup_op lookup_singleton in Hincr.
  - specialize (Hincr ε i).
    by rewrite lookup_op lookup_empty in Hincr.
Qed.

Definition gmap_ora_mixin : OraMixin (gmapR K A).
Proof.
  apply ora_total_mixin; try apply _; try done.
  - intros ???; simpl.
    rewrite lookup_op lookup_core.
    eapply (@ora_core_increasing (optionR A)), _.
  - intros ??? Hincr Hord z i.
    rewrite lookup_op; eapply (@ora_increasing_closed (optionR A)), Hord.
    by apply lookup_increasing.
  - intros ??? Hord i.
    rewrite !lookup_core.
    specialize (Hord i).
    apply (ora_core_monoN n (x !! i)); auto.
  - intros ???? Hx Hord.
    hnf in Hord.
    destruct (list_choice (λ '(i, a) yy,
      yy.1 ⋅ yy.2 ≼ₒ{S n} Some a ∧ yy.1 ≡{n}≡ y1 !! i ∧ yy.2 ≡{n}≡ y2 !! i) (map_to_list x)) as [gg Hgg].
    { rewrite (Forall_iff _ _ (uncurry (λ i a, (∃ yy,
        yy.1 ⋅ yy.2 ≼ₒ{S n} Some a ∧ yy.1 ≡{n}≡ y1 !! i ∧ yy.2 ≡{n}≡ y2 !! i)))); last by intros (?, ?).
      rewrite -map_Forall_to_list; intros ? a Ha.
      destruct (ora_op_extend n (Some a) (y1 !! i) (y2 !! i)) as (z1&z2&Hz).
      * by specialize (Hx i); rewrite Ha in Hx.
      * rewrite -lookup_op; specialize (Hord i); rewrite Ha in Hord; apply Hord.
      * exists (z1, z2); eauto. }
    exists (map_imap (λ i _, (list_find(A := (_ * ora_car A) * _) (λ e, e.1.1 = i) (zip (map_to_list x) gg)) ≫= (fun e => e.2.2.1)) x),
           (map_imap (λ i _, (list_find(A := (_ * ora_car A) * _) (λ e, e.1.1 = i) (zip (map_to_list x) gg)) ≫= (fun e => e.2.2.2)) x).
    assert (forall i a, x !! i = Some a -> exists ni yy1 yy2, list_find (λ e, e.1.1 = i) (zip (map_to_list x) gg) =
      Some (ni, ((i, a), (yy1, yy2))) /\ yy1 ⋅ yy2 ≼ₒ{S n} Some a ∧ yy1 ≡{n}≡ y1 !! i ∧ yy2 ≡{n}≡ y2 !! i) as Hgg'.
    { intros ?? Hxi.
      pose proof (proj2 (elem_of_map_to_list _ _ _) Hxi) as Helem.
      apply elem_of_list_lookup_1 in Helem as (ni & Hmap).
      eapply Forall2_lookup_l in Hgg as ((yy1, yy2) & ? & Hgg); eauto; simpl in *.
      exists ni, yy1, yy2.
      rewrite (proj2 (list_find_Some _ _ ni ((i, a), (yy1, yy2)))) /=; first done.
      rewrite lookup_zip_with_Some; split; [|split]; eauto.
      intros ? (? & ? & ?) Hzip ??; subst; simpl in *.
      apply lookup_zip_with_Some in Hzip as (e & ? & Heq & Hj & ?); inversion Heq; subst.
      pose proof (NoDup_lookup _ j ni e.1 (NoDup_fst_map_to_list x)) as Hnodup.
      rewrite !list_lookup_fmap Hmap Hj in Hnodup; destruct Hnodup; try done; lia. }
    split.
    + intros i.
      rewrite lookup_op !map_lookup_imap.
      destruct (x !! i) eqn: Hxi; rewrite Hxi /= //.
      destruct (Hgg' _ _ Hxi) as (? & ? & ? & -> & ? & _); auto.
    + split; intros i; rewrite map_lookup_imap; destruct (x !! i) eqn: Hxi; rewrite Hxi /=.
      * destruct (Hgg' _ _ Hxi) as (? & ? & ? & -> & ? & ? & ?); auto.
      * specialize (Hord i); rewrite Hxi lookup_op in Hord.
        destruct (op _ _) eqn: Hop; try done.
        rewrite op_None in Hop; destruct Hop as [Hy1 _].
        by rewrite Hy1.
      * destruct (Hgg' _ _ Hxi) as (? & ? & ? & -> & ? & ? & ?); auto.
      * specialize (Hord i); rewrite Hxi lookup_op in Hord.
        destruct (op _ _) eqn: Hop; try done.
        rewrite op_None in Hop; destruct Hop as [_ Hy2].
        by rewrite Hy2.
  - intros ??? Hx Hord.
    destruct (list_choice (λ '(i, a) yy, yy ≼ₒ{S n} Some a ∧ yy ≡{n}≡ y !! i) (map_to_list x)) as [gg Hgg].
    { rewrite (Forall_iff _ _ (uncurry (λ i a, (∃ yy, yy ≼ₒ{S n} Some a ∧ yy ≡{n}≡ y !! i)))); last by intros (?, ?).
      rewrite -map_Forall_to_list; intros ? a Ha.
      destruct (ora_extend n (Some a) (y !! i)) as (z&Hz).
      * by specialize (Hx i); rewrite Ha in Hx.
      * specialize (Hord i); rewrite Ha in Hord; apply Hord.
      * exists z; eauto. }
    exists (map_imap (λ i _, (list_find(A := (_ * ora_car A) * _) (λ e, e.1.1 = i) (zip (map_to_list x) gg)) ≫= (fun e => e.2.2)) x).
    assert (forall i a, x !! i = Some a -> exists ni yy, list_find (λ e, e.1.1 = i) (zip (map_to_list x) gg) =
      Some (ni, ((i, a), yy)) /\ yy ≼ₒ{S n} Some a ∧ yy ≡{n}≡ y !! i) as Hgg'.
    { intros ?? Hxi.
      pose proof (proj2 (elem_of_map_to_list _ _ _) Hxi) as Helem.
      apply elem_of_list_lookup_1 in Helem as (ni & Hmap).
      eapply Forall2_lookup_l in Hgg as (yy & ? & Hgg); eauto; simpl in *.
      exists ni, yy.
      rewrite (proj2 (list_find_Some _ _ ni ((i, a), yy))) /=; first done.
      rewrite lookup_zip_with_Some; split; [|split]; eauto.
      intros ? (? & ?) Hzip ??; subst; simpl in *.
      apply lookup_zip_with_Some in Hzip as (e & ? & Heq & Hj & ?); inversion Heq; subst.
      pose proof (NoDup_lookup _ j ni e.1 (NoDup_fst_map_to_list x)) as Hnodup.
      rewrite !list_lookup_fmap Hmap Hj in Hnodup; destruct Hnodup; try done; lia. }
    split.
    + intros i.
      rewrite !map_lookup_imap.
      destruct (x !! i) eqn: Hxi; rewrite Hxi /= //.
      destruct (Hgg' _ _ Hxi) as (? & ? & -> & ? & _); auto.
    + intros i; rewrite map_lookup_imap; destruct (x !! i) eqn: Hxi; rewrite Hxi /=.
      * destruct (Hgg' _ _ Hxi) as (? & ? & -> & ? & ?); auto.
      * specialize (Hord i); rewrite Hxi in Hord.
        destruct (y !! i) eqn: Hy; rewrite Hy in Hord |- *; done.
  - intros ?????.
    apply (@ora_dist_orderN (optionR A)); auto.
  - intros ??? Hord i.
    apply (@ora_orderN_S (optionR A)), Hord.
  - intros ???? Hxy Hyz i.
    eapply (@ora_orderN_trans (optionR A)); [apply Hxy | apply Hyz].
  - intros ???? Hord i.
    rewrite !lookup_op.
    eapply (@ora_orderN_op (optionR A)), Hord.
  - intros ???? Hord i.
    eapply (@ora_validN_orderN (optionR A)), Hord; auto.
  - split; intros; intros i; eapply (@ora_order_orderN (optionR A)).
    + apply H0.
    + intros; apply H0.
  - intros ??? Hcx.
    eexists; split; [constructor; reflexivity|].
    inversion Hcx as [?? Heq|]; subst.
    intros i.
    rewrite -Heq !lookup_omap lookup_op.
    edestruct (ora_pcore_order_op (x !! i)) as (? & Hcore & ?).
    { constructor; reflexivity. }
    inversion Hcore as [?? Hxy|]; subst.
    by rewrite Hxy.
Qed.
Canonical Structure gmapR : ora := Ora (gmap K A) gmap_ora_mixin.

Global Instance gmap_ora_discrete : OraDiscrete A → OraDiscrete gmapR.
Proof. split; [apply _|..].
  - intros m ? i. by apply: ora_discrete_valid.
  - intros ?? Hord i.
    specialize (Hord i).
    by apply (ora_discrete_order(A := optionR A)).
Qed.

Global Instance gmap_ora_total : OraTotal gmapR.
Proof. rewrite /OraTotal; eauto. Qed.

Canonical Structure gmapUR : uora := Uora (gmap K A) (gmap_ucmra_mixin(H := H)(A := A)).

End ora.

Global Arguments gmapR _ {_ _} _.
Global Arguments gmapUR _ {_ _} _.

Section properties.
Context `{Countable K} {A : ora}.
Implicit Types m : gmap K A.
Implicit Types i : K.
Implicit Types x y : A.

Global Instance gmap_core_id m : (∀ x : A, OraCoreId x) → OraCoreId m.
Proof.
  intros; apply core_id_total=> i.
  rewrite lookup_core oracore_id_core //.
Qed.
Global Instance gmap_singleton_core_id i (x : A) :
  OraCoreId x → OraCoreId {[ i := x ]}.
Proof. intros. by apply core_id_total, (singleton_core'(A := A)). Qed.

End properties.

Global Instance gmap_fmap_ora_morphism `{Countable K} {A B : ora} (f : A → B)
  `{!OraMorphism f} : OraMorphism (fmap f : gmap K A → gmap K B).
Proof.
  split; try apply _.
  - intros ??? Hord ?.
    rewrite !lookup_fmap.
    apply option_fmap_ora_morphism, Hord; auto.
  - intros ? Hincr ??.
    rewrite lookup_op lookup_fmap.
    apply option_fmap_ora_morphism; auto.
    by apply lookup_increasing.
Qed.

Program Definition gmapURF K `{Countable K} (F : OrarFunctor) : uorarFunctor := {|
  uorarFunctor_car A _ B _ := gmapUR K (orarFunctor_car F A B);
  uorarFunctor_map A1 _ A2 _ B1 _ B2 _ fg := gmapO_map (orarFunctor_map F fg)
|}.
Next Obligation.
  by intros K ?? F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply gmapO_map_ne, orarFunctor_map_ne.
Qed.
Next Obligation.
  intros K ?? F A ? B ? x. rewrite /= -{2}(map_fmap_id x).
  apply map_fmap_equiv_ext=>y ??; apply orarFunctor_map_id.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -map_fmap_compose.
  apply map_fmap_equiv_ext=>y ??; apply orarFunctor_map_compose.
Qed.

Global Instance gmapURF_contractive K `{Countable K} F :
  OrarFunctorContractive F → uorarFunctorContractive (gmapURF K F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply gmapO_map_ne, orarFunctor_map_contractive.
Qed.

Program Definition gmapRF K `{Countable K} (F : OrarFunctor) : OrarFunctor := {|
  orarFunctor_car A _ B _ := gmapR K (orarFunctor_car F A B);
  orarFunctor_map A1 _ A2 _ B1 _ B2 _ fg := gmapO_map (orarFunctor_map F fg)
|}.
Solve Obligations with apply gmapURF.

Global Instance gmapRF_contractive K `{Countable K} F :
  OrarFunctorContractive F → OrarFunctorContractive (gmapRF K F).
Proof. apply gmapURF_contractive. Qed.
