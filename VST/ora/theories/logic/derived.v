From iris.bi Require Export bi updates.
From iris_ora.logic Require Export oupred.
Import bi.bi logic.oupred.ouPred.
From iris.prelude Require Import options.

(** Derived laws for Iris-specific primitive connectives (own, valid).
    This file does NOT unseal! *)

Infix "~~>" := (cmra_update(A := ora_cmraR _)) (at level 70).

Module ouPred.
Section derived.
Context {M : uora}.
Implicit Types φ : Prop.
Implicit Types P Q : ouPred M.
Implicit Types A : Type.

(* Force implicit argument M *)
Notation "P ⊢ Q" := (bi_entails (PROP:=ouPredI M) P Q).
Notation "P ⊣⊢ Q" := (equiv (A:=ouPredI M) P%I Q%I).

(** Propers *)
Global Instance ownM_proper: Proper ((≡) ==> (⊣⊢)) (@ouPred_ownM M) := ne_proper _.
Global Instance ora_valid_proper {A : ora} :
  Proper ((≡) ==> (⊣⊢)) (@ouPred_ora_valid M A) := ne_proper _.

(** Own and valid derived *)
Global Instance ownM_mono : Proper (flip (≼ₒ) ==> (⊢)) (@ouPred_ownM M).
Proof. by intros ???; apply ownM_order. Qed.
Global Instance ownM_unit_affine : Affine(PROP:=ouPredI M) (ouPred_ownM ε).
Proof. apply ownM_unit_discard. Qed.
Global Instance ownM_increasing_affine a {H : Increasing a} : Affine (PROP:=ouPredI M) (ouPred_ownM a).
Proof. apply uora_unit_order_increasing in H. rewrite /Affine ownM_mono //. apply ownM_unit_discard. Qed.
Global Instance ownM_core_affine a : Affine (PROP:=ouPredI M) (ouPred_ownM (core a)).
Proof. apply ownM_core_discard. Qed.
Lemma persistently_ora_valid_1 {A : ora} (a : A) : ✓ a ⊢@{ouPredI M} <pers> (✓ a).
Proof. by rewrite {1}plainly_ora_valid_1 plainly_elim_persistently. Qed.
Lemma intuitionistically_ownM (a : M) : OraCoreId a → ouPred_ownM a ⊢ □ ouPred_ownM a.
Proof. intros; rewrite /bi_intuitionistically -{1}(oracore_id_core a) -{1}(affine_affinely (ouPred_ownM (core a))).
  rewrite oracore_id_core -{2}(oracore_id_core a).
  apply affinely_mono, persistently_ownM_core.
Qed.
Lemma ownM_invalid (a : M) : ¬ ✓{0} a → ouPred_ownM a ⊢ False.
Proof. by intros; rewrite ownM_valid ora_valid_elim. Qed.
Lemma ownM_unit' : ouPred_ownM ε ⊣⊢ emp.
Proof. apply (anti_symm _); [apply ownM_unit_discard | apply ownM_unit]. Qed.
Instance absorbing_valid {A : ora} (a : A) : Absorbing(PROP:=ouPredI M) (✓ a).
Proof.
  rewrite /Absorbing /bi_absorbingly.
  unseal.
  constructor.
  intros ??? (? & ? & ? & ? & ?); auto.
Qed.
Lemma plainly_ora_valid {A : ora} (a : A) : ■ ✓ a ⊣⊢ ✓ a.
Proof. apply (anti_symm _), plainly_ora_valid_1. apply plainly_elim, _. Qed.
(*Lemma intuitionistically_ora_valid {A : ora} (a : A) : □ ✓ a ⊣⊢ ✓ a.
Proof.
  rewrite /bi_intuitionistically affine_affinely. intros; apply (anti_symm _);
    first by rewrite persistently_elim.
  apply:persistently_ora_valid_1.
Qed.*)

Lemma bupd_ownM_update (x y : M) : x ~~> y → ouPred_ownM x ⊢ |==> ouPred_ownM y.
Proof.
  intros; rewrite (bupd_ownM_updateP _ (y =.)); last by apply @cmra_update_updateP.
  by apply ouPred.bupd_mono, exist_elim=> y'; apply pure_elim_l=> ->.
Qed.

(** Timeless instances *)
Global Instance valid_timeless {A : ora} `{!OraDiscrete A} (a : A) :
  Timeless (✓ a : ouPred M)%I.
Proof. rewrite /Timeless !discrete_valid. apply (timeless _). Qed.
Global Instance ownM_timeless (a : M) : Discrete a → Timeless (ouPred_ownM a).
Proof.
  intros ?. rewrite /Timeless later_ownM. apply exist_elim=> b.
  rewrite (timeless (a≡b)) (except_0_intro (ouPred_ownM b)) -except_0_and.
  apply except_0_mono. rewrite internal_eq_sym.
  apply (internal_eq_rewrite' b a (ouPred_ownM) _);
    auto using and_elim_l, and_elim_r.
Qed.

(** Plainness *)
Global Instance ora_valid_plain {A : ora} (a : A) :
  Plain (✓ a : ouPred M)%I.
Proof. rewrite /Persistent. apply plainly_ora_valid_1. Qed.

(** Persistence *)
Global Instance ora_valid_persistent {A : ora} (a : A) :
  Persistent (✓ a : ouPred M)%I.
Proof. rewrite /Persistent. apply persistently_ora_valid_1. Qed.
Global Instance ownM_persistent a : OraCoreId a → Persistent (@ouPred_ownM M a).
Proof.
  intros. rewrite /Persistent -{2}(oracore_id_core a). apply persistently_ownM_core.
Qed.

(** For big ops *)
Global Instance ouPred_ownM_sep_homomorphism :
  MonoidHomomorphism op ouPred_sep (≡) (@ouPred_ownM M).
Proof. split; [split|]; try apply _; [apply ownM_op | apply ownM_unit']. Qed.

(** Consistency/soundness statement *)
Lemma uora_unit_refl (A : uora) n : (ε : A) ≼ₒ{n} ε.
Proof.
  rewrite -{2}(oracore_id_core ε); apply ora_order_orderN, uora_unit_order_core.
Qed.

Lemma pure_soundness φ : (emp ⊢ ⌜ φ ⌝) → φ.
Proof.
  unseal=> -[H]. apply (H 0 ε); eauto using uora_unit_validN.
  apply uora_unit_refl.
Qed.

Lemma internal_eq_soundness {A : ofe} (x y : A) : (True ⊢ x ≡ y) → x ≡ y.
Proof.
  unseal=> -[H]. apply equiv_dist=> n.
  by apply (H n ε); eauto using uora_unit_validN.
Qed.

Lemma later_soundness P : (emp ⊢ ▷ P) → (emp ⊢ P).
Proof.
  unseal=> -[HP]; split=> n x Hx ?.
  apply ouPred_mono with n ε; eauto.
  apply (HP (S n)); eauto using uora_unit_validN.
  apply uora_unit_refl.
Qed.

Lemma laterN_soundness P n : (⊢ ▷^n P) → ⊢ P.
Proof.
  induction n; auto.
  intros; apply IHn, later_soundness; done.
Qed.

Lemma bupd_plain P `{!Plain P} `{!Absorbing P} : (|==> P) ⊢ P.
Proof.
  rewrite {1}(plain P). setoid_rewrite bupd_plainly.
  apply plainly_elim, _.
Qed.

Lemma bupd_plain_soundness P `{!Plain P} : (⊢ |==> P) → ⊢ P.
Proof.
  split=> n x Hx ?.
  apply ouPred_mono with n ε; eauto.
  generalize (bupd_plainly P); rewrite /plainly /bi_plainly_plainly /= ouPred_plainly_eq /ouPred_plainly_def.
  intros Hplain; eapply (ouPred_in_entails _ _ Hplain); eauto.
  eapply bupd_mono, H; auto.
  etrans; [apply Plain0|].
  by unseal.
Qed.

Lemma bupdN_plain n P `{!Plain P} `{!Absorbing P} : Nat.iter n (λ Q, |==> ▷ Q)%I P ⊢ |==> ▷^n P.
Proof.
  induction n; simpl.
  - apply bupd_intro.
  - rewrite IHn.
    etrans; last apply updates.bupd_trans.
    apply bupd_mono.
    rewrite bupd_plain; apply bupd_intro.
Qed.

Lemma bupd_laterN_soundness P `{!Plain P} `{!Absorbing P} n : (⊢ Nat.iter n (λ Q, |==> ▷ Q) P) → ⊢ P.
Proof.
  rewrite bupdN_plain.
  intros ?%bupd_plain_soundness%laterN_soundness; auto.
  apply _.
Qed.

Corollary soundness φ n : (⊢@{ouPredI M} ▷^n ⌜ φ ⌝) → φ.
Proof.
  induction n as [|n IH]=> /=.
  - apply pure_soundness.
  - intros H. by apply IH, later_soundness.
Qed.

Corollary consistency_modal n : ¬ ⊢@{ouPredI M} ▷^n False.
Proof. exact (soundness False n). Qed.

Corollary consistency : ¬ ⊢@{ouPredI M} False.
Proof. exact (consistency_modal 0). Qed.
End derived.
End ouPred.
