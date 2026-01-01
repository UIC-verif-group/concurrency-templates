From iris.algebra Require Import agree.
From iris_ora.algebra Require Export ora.
(* From iris_ora.algebra Require Import list. *)
From iris_ora.logic Require Import oupred.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments pcore _ _ !_ /.

Local Coercion agree_car : agree >-> list.

Section agree.
Local Set Default Proof Using "Type".
Context {A : ofe}.
Implicit Types a b : A.
Implicit Types x y : agree A.

Instance agree_orderN : OraOrderN (agree A) :=
  λ n x y, ∀ a, a ∈ agree_car x → ∃ b, b ∈ agree_car y ∧ a ≡{n}≡ b.
Instance agree_order : OraOrder (agree A) := λ x y, ∀ n, x ≼ₒ{n} y.

Lemma agree_order_dist n x y : ✓{n} y → x ≼ₒ{n} y → x ≡{n}≡ y.
Proof.
  intros Hnv Hxy; split => a Ha.
  - by apply Hxy.
  - destruct x as [[|xh xc] xnn]; first done.
    destruct (Hxy xh) as [z [Hz1 Hz2]]; simpl; auto using elem_of_list_here.
    exists xh; split; first apply elem_of_list_here.
    etrans; first apply Hz2.
    eapply agree_validN_def; eauto.
Qed.

Lemma agree_increasing x : Increasing x.
Proof.
  intros y n a Ha. exists a; split; last done.
  apply elem_of_list_lookup in Ha; destruct Ha as [i Ha].
  apply elem_of_list_lookup. exists (length x + i).
  rewrite lookup_app_r; last lia.
  by replace (length x + i - length x) with i by lia.
Qed.

Lemma agree_dist_orderN n x y : x ≡{n}≡ y → x ≼ₒ{n} y.
Proof. by intros Hxy a Ha; apply Hxy. Qed.

Instance agree_orderN_proper n :
  Proper ((dist n) ==> (dist n) ==> iff) (agree_orderN n).
Proof.
  intros x y [Hxy1 Hxy2] x' y' [Hx'y'1 Hx'y'2]; split => Hs z Hz.
  - destruct (Hxy2 _ Hz) as [u [Hu1 Hu2]].
    destruct (Hs _ Hu1) as [w [Hw1 Hw2]].
    destruct (Hx'y'1 _ Hw1) as [q [Hq1 Hq2]].
    exists q; split; auto.
    rewrite -Hu2; etrans; eauto.
  - destruct (Hxy1 _ Hz) as [u [Hu1 Hu2]].
    destruct (Hs _ Hu1) as [w [Hw1 Hw2]].
    destruct (Hx'y'2 _ Hw1) as [q [Hq1 Hq2]].
    exists q; split; auto.
    rewrite Hu2; etrans; eauto.
Qed.

Instance agree_orderN_proper' n :
  Proper ((≡) ==> (≡) ==> iff) (agree_orderN n).
Proof.
  intros x y Hxy x' y' Hx'y'; split => Hs.
  - eapply agree_orderN_proper; try symmetry; eauto.
  - eapply agree_orderN_proper; eauto.
Qed.

Instance agree_order_proper :
  Proper ((≡) ==> (≡) ==> iff) agree_order.
Proof.
  intros x y Hxy x' y' Hx'y'; split => Hs n.
  - eapply agree_orderN_proper; try symmetry; eauto.
    apply Hs.
  - eapply agree_orderN_proper; eauto.
    apply Hs.
Qed.

Instance agree_orderN_Trans n : Transitive (agree_orderN n).
Proof.
  intros x y z Hxy Hyz u Hu.
  destruct (Hxy _ Hu) as [w [Hw1 Hw2]].
  destruct (Hyz _ Hw1) as [q [Hq1 Hq2]].
  exists q; split; auto.
  etrans; eauto.
Qed.

Instance agree_order_Trans : Transitive agree_order.
Proof.
  intros x y z Hxy Hyz n u Hu.
  eapply agree_orderN_Trans; eauto; apply Hxy || apply Hyz.
Qed.

Definition agree_ora_mixin : OraMixin (agree A).
Proof.
  apply ora_total_mixin; try apply _ ||
    by eauto using agree_increasing, agree_dist_orderN.
  - intros n x y1 y2 Hx Hysx.
    pose proof (agree_order_dist _ _ _ Hx Hysx) as Hysx'.
    eapply agree_validN_ne in Hx; last by symmetry.
    exists x, x. split; last split.
    + apply agree_dist_orderN. by rewrite agree_idemp.
    + rewrite -Hysx'. by rewrite (agree_op_invN _ _ _ Hx) agree_idemp.
    + rewrite -Hysx'. by rewrite (agree_op_invN _ _ _ Hx) agree_idemp.
  - intros n x y Hx Hyx. exists x; split.
    + by apply agree_dist_orderN.
    + symmetry. eapply agree_order_dist; eauto.
  - intros n x y. intros Hxy a Ha.
    destruct (Hxy _ Ha) as [z [Hz1 Hz2]].
    eexists z; split; auto. by apply dist_S.
  - intros n x x' y Hxx' a Ha.
    apply elem_of_app in Ha. destruct Ha as [Ha|Ha].
    + destruct (Hxx' _ Ha) as [z [Hz1 Hz2]].
      exists z; split; auto. by apply elem_of_app; left.
    + exists a; split; auto. by apply elem_of_app; right.
  - intros n x y Hx Hxy. apply agree_validN_def => a b Ha Hb.
    destruct (Hxy _ Ha) as [z1 [Hz11 Hz12]].
    destruct (Hxy _ Hb) as [z2 [Hz21 Hz22]].
    rewrite Hz12 Hz22. eapply agree_validN_def; eauto.
  - intros x cx y; inversion 1 as [?? Hcx|]; subst.
    exists (x ⋅ y); split; auto. rewrite Hcx.
    intros n a Ha. exists a; split; auto. by apply elem_of_app; left.
Qed.
Canonical Structure agreeR : ora := Ora (agree A) agree_ora_mixin.

Global Instance agree_ora_total : OraTotal agreeR.
Proof. rewrite /OraTotal; eauto. Qed.
Global Instance agree_core_id (x : agree A) : OraCoreId x.
Proof. by constructor. Qed.

Global Instance agree_ora_discrete : OfeDiscrete A → OraDiscrete agreeR.
Proof.
  intros HD. split.
  - intros x y [H H'] n; split=> a; setoid_rewrite <-(discrete_iff_0 _ _); auto.
  - intros x; rewrite agree_validN_def=> Hv n. apply agree_validN_def=> a b ??.
    apply discrete_iff_0; auto.
  - intros x y Hxy n a Ha.
    destruct (Hxy _ Ha) as [z [Hz1 Hz2]].
    exists z; split; auto. by setoid_rewrite <-(discrete_iff_0 _ _).
Qed.

Lemma to_agree_order a b : to_agree a ≼ₒ to_agree b ↔ a ≡ b.
Proof.
  split; last by intros ->.
  intros Hab. apply equiv_dist=>n.
  destruct (Hab n a) as [z [Hz1 Hz2]]; first by apply elem_of_list_singleton.
  by apply elem_of_list_singleton in Hz1; subst.
Qed.

Global Instance agree_cancelable x : OraCancelable x.
Proof.
  intros n y z Hv Heq.
  destruct (to_agree_uninjN n x) as [x' EQx]; first by eapply cmra_validN_op_l.
  destruct (to_agree_uninjN n y) as [y' EQy]; first by eapply cmra_validN_op_r.
  destruct (to_agree_uninjN n z) as [z' EQz].
  { eapply (cmra_validN_op_r n x z). by rewrite -Heq. }
  assert (Hx'y' : x' ≡{n}≡ y').
  { apply (inj to_agree), agree_op_invN. by rewrite EQx EQy. }
  assert (Hx'z' : x' ≡{n}≡ z').
  { apply (inj to_agree), agree_op_invN. by rewrite EQx EQz -Heq. }
  by rewrite -EQy -EQz -Hx'y' -Hx'z'.
Qed.

(** Internalized properties *)
Lemma agree_equivI {M} a b : to_agree a ≡ to_agree b ⊣⊢ (a ≡ b : ouPred M).
Proof.
  rewrite /internal_eq /bi_internal_eq_internal_eq /=. ouPred.unseal. do 2 split.
  - intros Hx. exact: to_agree_injN.
  - intros Hx. exact: to_agree_ne.
Qed.
Lemma agree_validI {M} x y : ✓ (x ⋅ y) ⊢ (x ≡ y : ouPred M).
Proof.
  rewrite /internal_eq /bi_internal_eq_internal_eq /=.
  ouPred.unseal; split=> r n _ ?; by apply: agree_op_invN.
Qed.
End agree.

Arguments agreeR : clear implicits.

Section agree_map.
  Context {A B : ofe} (f : A → B) `{Hf: NonExpansive f}.

  Global Instance agree_map_morphism : OraMorphism (agree_map f).
  Proof using Hf.
    split; first apply _.
    - intros n x y Hxy a; setoid_rewrite elem_of_list_fmap; intros [z [-> Hz]].
      destruct (Hxy _ Hz) as [w [Hw1 Hw2]].
      exists (f w); split; eauto.
      by rewrite Hw2.
    - intros x Hx. apply agree_increasing.
  Qed.
End agree_map.

Program Definition agreeRF (F : oFunctor) : OrarFunctor := {|
  orarFunctor_car A _ B _ := agreeR (oFunctor_car F A B);
  orarFunctor_map A1 _ A2 _ B1 _ B2 _ fg := agreeO_map (oFunctor_map F fg)
|}.
Next Obligation.
  intros ? A1 ? A2 ? B1 ? B2 ? n ???; simpl. by apply agreeO_map_ne, oFunctor_map_ne.
Qed.
Next Obligation.
  intros F A ? B ? x; simpl. rewrite -{2}(agree_map_id x).
  apply (agree_map_ext _)=>y. by rewrite oFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl. rewrite -agree_map_compose.
  apply (agree_map_ext _)=>y; apply oFunctor_map_compose.
Qed.

#[export] Instance agreeRF_contractive F :
  oFunctorContractive F → OrarFunctorContractive (agreeRF F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n ???; simpl.
  by apply agreeO_map_ne, oFunctor_map_contractive.
Qed.
