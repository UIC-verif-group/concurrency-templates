From stdpp Require Import finite.
From iris.algebra Require Import cmra updates functions.
From iris_ora.algebra Require Export ora.
From iris.prelude Require Import options.

Section ora.
  Context {A : Type} `{Hfin : Finite A} {B : A → uora}.
  Implicit Types x : A.
  Implicit Types f g : discrete_fun B.

  Global Instance discrete_funR_ora_discrete:
    (∀ i, OraDiscrete (B i)) → OraDiscrete (discrete_funR B).
  Proof. intros HB. split; first apply _.
    - intros x Hv i. apply HB, Hv.
    - intros ?? Hord ?. apply HB, Hord.
  Qed.

  Local Notation discrete_fun_singleton := (discrete_fun_singleton(B := B)).

  Global Instance discrete_fun_singleton_ne x :
    NonExpansive (discrete_fun_singleton x : B x → _).
  Proof.
    intros n y1 y2 ?; apply discrete_fun_insert_ne; [done|].
    by apply equiv_dist.
  Qed.
  Global Instance discrete_fun_singleton_proper x :
    Proper ((≡) ==> (≡)) (discrete_fun_singleton x) := ne_proper _.

  Global Instance discrete_fun_singleton_core_id x (y : B x) :
    OraCoreId y → OraCoreId (discrete_fun_singleton x y).
  Proof. by rewrite !oracore_id_total discrete_fun_singleton_core=> ->. Qed.

(*  Lemma discrete_fun_singleton_op (x : A) (y1 y2 : B x) :
    discrete_fun_singleton x y1 ⋅ discrete_fun_singleton x y2 ≡ discrete_fun_singleton x (y1 ⋅ y2).
  Proof.
    intros x'; destruct (decide (x' = x)) as [->|].
    - by rewrite discrete_fun_lookup_op !discrete_fun_lookup_singleton.
    - by rewrite discrete_fun_lookup_op !discrete_fun_lookup_singleton_ne // left_id.
  Qed.

  Lemma discrete_fun_insert_updateP x (P : B x → Prop) (Q : discrete_fun B → Prop) g y1 :
    y1 ~~>: P → (∀ y2, P y2 → Q (discrete_fun_insert x y2 g)) →
    discrete_fun_insert x y1 g ~~>: Q.
  Proof.
    intros Hy1 HP; apply cmra_total_updateP.
    intros n gf Hg. destruct (Hy1 n (Some (gf x))) as (y2&?&?).
    { move: (Hg x). by rewrite discrete_fun_lookup_op discrete_fun_lookup_insert. }
    exists (discrete_fun_insert x y2 g); split; [auto|].
    intros x'; destruct (decide (x' = x)) as [->|];
      rewrite discrete_fun_lookup_op ?discrete_fun_lookup_insert //; [].
    move: (Hg x'). by rewrite discrete_fun_lookup_op !discrete_fun_lookup_insert_ne.
  Qed.

  Lemma discrete_fun_insert_updateP' x (P : B x → Prop) g y1 :
    y1 ~~>: P →
    discrete_fun_insert x y1 g ~~>: λ g', ∃ y2, g' = discrete_fun_insert x y2 g ∧ P y2.
  Proof. eauto using discrete_fun_insert_updateP. Qed.
  Lemma discrete_fun_insert_update g x y1 y2 :
    y1 ~~> y2 → discrete_fun_insert x y1 g ~~> discrete_fun_insert x y2 g.
  Proof.
    rewrite !cmra_update_updateP; eauto using discrete_fun_insert_updateP with subst.
  Qed.

  Lemma discrete_fun_singleton_updateP x (P : B x → Prop) (Q : discrete_fun B → Prop) y1 :
    y1 ~~>: P → (∀ y2, P y2 → Q (discrete_fun_singleton x y2)) →
    discrete_fun_singleton x y1 ~~>: Q.
  Proof. rewrite /discrete_fun_singleton; eauto using discrete_fun_insert_updateP. Qed.
  Lemma discrete_fun_singleton_updateP' x (P : B x → Prop) y1 :
    y1 ~~>: P →
    discrete_fun_singleton x y1 ~~>: λ g, ∃ y2, g = discrete_fun_singleton x y2 ∧ P y2.
  Proof. eauto using discrete_fun_singleton_updateP. Qed.
  Lemma discrete_fun_singleton_update x (y1 y2 : B x) :
    y1 ~~> y2 → discrete_fun_singleton x y1 ~~> discrete_fun_singleton x y2.
  Proof. eauto using discrete_fun_insert_update. Qed.

  Lemma discrete_fun_singleton_updateP_empty x (P : B x → Prop) (Q : discrete_fun B → Prop) :
    ε ~~>: P → (∀ y2, P y2 → Q (discrete_fun_singleton x y2)) → ε ~~>: Q.
  Proof.
    intros Hx HQ; apply cmra_total_updateP.
    intros n gf Hg. destruct (Hx n (Some (gf x))) as (y2&?&?); first apply Hg.
    exists (discrete_fun_singleton x y2); split; [by apply HQ|].
    intros x'; destruct (decide (x' = x)) as [->|].
    - by rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton.
    - rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton_ne //; by apply Hg.
  Qed.
  Lemma discrete_fun_singleton_updateP_empty' x (P : B x → Prop) :
    ε ~~>: P → ε ~~>: λ g, ∃ y2, g = discrete_fun_singleton x y2 ∧ P y2.
  Proof. eauto using discrete_fun_singleton_updateP_empty. Qed.
  Lemma discrete_fun_singleton_update_empty x (y : B x) :
    ε ~~> y → ε ~~> discrete_fun_singleton x y.
  Proof.
    rewrite !cmra_update_updateP;
      eauto using discrete_fun_singleton_updateP_empty with subst.
  Qed.*)
End ora.
