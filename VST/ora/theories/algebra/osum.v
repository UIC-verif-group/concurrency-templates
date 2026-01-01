From iris.algebra Require Import csum.
From iris_ora.algebra Require Export ora.
Set Default Proof Using "Type".
Local Arguments pcore _ _ !_ /.
Local Arguments csum_pcore_instance _ _ !_/.
Local Arguments cmra_car _ /.
Local Arguments cmra_pcore _ / _.
Local Arguments ora_pcore _ !_ /.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments cmra_validN _ / _ _.
Local Arguments ora_validN _ _ !_ /.
Local Arguments ora_valid _  !_ /.

Section ora.
Context {A B : ora}.
Implicit Types a : A.
Implicit Types b : B.

(* ORA *)
Instance csum_order : OraOrder (csum A B) := λ x y,
  match x, y with
  | Cinl a, Cinl a' => a ≼ₒ a'
  | Cinr b, Cinr b' => b ≼ₒ b'
  | _, CsumBot => True
  | _, _ => False
  end.

Instance csum_orderN : OraOrderN (csum A B) := λ n x y,
  match x, y with
  | Cinl a, Cinl a' => a ≼ₒ{n} a'
  | Cinr b, Cinr b' => b ≼ₒ{n} b'
  | _, CsumBot => True
  | _, _ => False
  end.

Lemma csum_order' x y :
  x ≼ₒ y ↔ y = CsumBot ∨ (∃ a a', x = Cinl a ∧ y = Cinl a' ∧ a ≼ₒ a')
                       ∨ (∃ b b', x = Cinr b ∧ y = Cinr b' ∧ b ≼ₒ b').
Proof.
  destruct x; destruct y; split; rewrite /Oraorder /=; intuition;
  repeat match goal with
    | H : ∃ x, _ |- _ => destruct H
    | H : _ ∧ _ |- _ => destruct H
  end; simplify_eq; eauto; try (right; left; eauto; fail);
    try (right; right; eauto; fail).
Qed.

Lemma csum_orderN' n x y :
  x ≼ₒ{n} y ↔ y = CsumBot ∨ (∃ a a', x = Cinl a ∧ y = Cinl a' ∧ a ≼ₒ{n} a')
                          ∨ (∃ b b', x = Cinr b ∧ y = Cinr b' ∧ b ≼ₒ{n} b').
Proof.
  destruct x; destruct y; split; rewrite /OraorderN /=; intuition;
  repeat match goal with
    | H : ∃ x, _ |- _ => destruct H
    | H : _ ∧ _ |- _ => destruct H
  end; simplify_eq; eauto; try (right; left; eauto; fail);
    try (right; right; eauto; fail).
Qed.

Lemma Increasing_CsumBot : Increasing CsumBot.
Proof. intros [?|?|]; done. Qed.

Lemma Increasing_cinl a : Increasing a ↔ Increasing (Cinl a).
Proof.
  split.
  - intros Ha [zl|zr|]; try done; apply Ha.
  - intros Ha z; apply (Ha (Cinl z)).
Qed.

Lemma Increasing_cinr b : Increasing b ↔ Increasing (Cinr b).
Proof.
  split.
  - intros Hb [zl|zr|]; try done; apply Hb.
  - intros Hb z; apply (Hb (Cinr z)).
Qed.

Lemma Cinl_orderN n x y : x ≼ₒ{n} y ↔ (Cinl x) ≼ₒ{n} (Cinl y).
Proof. done. Qed.

Lemma Cinr_orderN n x y : x ≼ₒ{n} y ↔ (Cinr x) ≼ₒ{n} (Cinr y).
Proof. done. Qed.

Lemma Cinl_order x y : x ≼ₒ y ↔ (Cinl x) ≼ₒ (Cinl y).
Proof. done. Qed.

Lemma Cinr_order x y : x ≼ₒ y ↔ (Cinr x) ≼ₒ (Cinr y).
Proof. done. Qed.

Lemma csum_ora_mixin : OraMixin (csum A B).
Proof.
  split.
  - intros [xl|xr|] [cxl|cxr|] Hcx [zl|zr|]; simpl in *;
      try destruct (pcore xl) eqn:Heq; try destruct (pcore xr) eqn:Heq;
        simpl in *; simplify_eq; try eapply ora_pcore_increasing; eauto.
  - intros n [xl|xr|] [yl|yr|]; intros Hi Ho; try inversion Ho;
      try (intros [zl|zr|]; done); rewrite /Oraorder /=;
      try apply Increasing_cinl in Hi; try apply Increasing_cinr in Hi;
    try apply Increasing_cinl; try apply Increasing_cinr;
      eauto using ora_increasing_closed.
  - intros n [xl|xr|] [yl|yr|] [cxl|cxr|] Ho Hcx; try done;
      simpl in *; try destruct (pcore xl) eqn:Heq;
        try destruct (pcore xr) eqn:Heq; simpl in *; simplify_eq; eauto.
    + destruct (ora_pcore_monoN n xl yl cxl) as [z [Heqy ?]]; auto.
      exists (Cinl z); by rewrite Heqy.
    + destruct (ora_pcore_monoN n xr yr cxr) as [z [Heqy ?]]; auto.
      exists (Cinr z); by rewrite Heqy.
  - intros n [xl|xr|] [y1l|y1r|] [y2l|y2r|] Hx Hyx; try done.
    + destruct (ora_op_extend n xl y1l y2l) as (z1 & z2 & Hz1 & Hz2 & Hz3); auto.
      exists (Cinl z1), (Cinl z2); repeat split; by try constructor.
    + destruct (ora_op_extend n xr y1r y2r) as (z1 & z2 & Hz1 & Hz2 & Hz3); auto.
      exists (Cinr z1), (Cinr z2); repeat split; by try constructor.
  - intros n [xl|xr|] [yl|yr|] Hx Hyx; try done.
    + destruct (ora_extend n xl yl) as (z & Hz1 & Hz2); auto.
      exists (Cinl z); repeat split; by try constructor.
    + destruct (ora_extend n xr yr) as (z & Hz1 & Hz2); auto.
      exists (Cinr z); repeat split; by try constructor.
  - intros n [xl|xr|] [yl|yr|] Hyx; inversion Hyx; simplify_eq; try done;
      apply ora_dist_orderN; auto.
  - intros n [xl|xr|] [yl|yr|] Hyx; try done; apply ora_orderN_S; auto.
  - intros n [xl|xr|] [yl|yr|] [zl|zr|] Hxy Hyz; try done;
        eapply ora_orderN_trans; eauto.
  - intros n [xl|xr|] [x'l|x'r|] [yl|yr|] Hxx'; try done; auto;
        eapply ora_orderN_op; eauto.
  - intros n [xl|xr|] [yl|yr|] Hx Hyx; try done;
      eapply ora_validN_orderN; eauto; apply Hx.
  - intros [xl|xr|] [yl|yr|]; split => Hx; try intros n;
    try done; try (by (pose proof (Hx 0) as Hx0; inversion Hx0));
    apply ora_order_orderN; auto.
  - intros [xl|xr|] [cxl|cxr|] [yl|yr|]; simpl in *;
      try destruct (pcore xl) as [cxl'|] eqn:Heq;
      try destruct (pcore xr) as [cxr'|] eqn:Heq;
      simpl in *; inversion 1 as [? ? Heq'|];
        inversion Heq' as [? ? Heq''|? ? Heq''|]; simplify_eq; eauto.
    + destruct (ora_pcore_order_op xl cxl' yl) as [cxy [Hcxy1 Hcxy2]];
        first by rewrite Heq.
      revert Hcxy2; rewrite Heq'' => Hcxy2.
      exists (Cinl cxy); rewrite Hcxy1 /=; auto.
    + destruct (ora_pcore_order_op xr cxr' yr) as [cxy [Hcxy1 Hcxy2]];
        first by rewrite Heq.
      revert Hcxy2; rewrite Heq'' => Hcxy2.
      exists (Cinr cxy); rewrite Hcxy1 /=; auto.
Qed.
Canonical Structure csumR := Ora (csum A B) csum_ora_mixin.

Global Instance csum_ora_discrete :
  OraDiscrete A → OraDiscrete B → OraDiscrete csumR.
Proof.
  split; first apply _.
  by move=>[a|b|] HH /=; try apply ora_discrete_valid.
  move=>[a|b|] [a'|b'|] HH /=; try done.
  - by apply (ora_discrete_order a a').
  - by apply (ora_discrete_order b b').
Qed.

Global Instance Cinl_oracore_id a : OraCoreId a → OraCoreId (Cinl a).
Proof. rewrite /OraCoreId /=. inversion_clear 1; by repeat constructor. Qed.
Global Instance Cinr_oracore_id b : OraCoreId b → OraCoreId (Cinr b).
Proof. rewrite /OraCoreId /=. inversion_clear 1; by repeat constructor. Qed.

Global Instance Cinl_exclusive a : OraExclusive a → OraExclusive (Cinl a).
Proof. by move=> H[]? =>[/H||]. Qed.
Global Instance Cinr_exclusive b : OraExclusive b → OraExclusive (Cinr b).
Proof. by move=> H[]? =>[|/H|]. Qed.

Global Instance Cinl_cancelable a : OraCancelable a → OraCancelable (Cinl a).
Proof.
  move=> ?? [y|y|] [z|z|] ? EQ //; inversion_clear EQ.
  constructor. by eapply (oracancelableN a).
Qed.
Global Instance Cinr_cancelable b : OraCancelable b → OraCancelable (Cinr b).
Proof.
  move=> ?? [y|y|] [z|z|] ? EQ //; inversion_clear EQ.
  constructor. by eapply (oracancelableN b).
Qed.

Global Instance Cinl_id_free a : OraIdFree a → OraIdFree (Cinl a).
Proof. intros ? [] ? EQ; inversion_clear EQ. by eapply oraid_free0_r. Qed.
Global Instance Cinr_id_free b : OraIdFree b → OraIdFree (Cinr b).
Proof. intros ? [] ? EQ; inversion_clear EQ. by eapply oraid_free0_r. Qed.

(** Updates *)
(* Lemma csum_update_l (a1 a2 : A) : a1 ~~> a2 → Cinl a1 ~~> Cinl a2. *)
(* Proof. *)
(*   intros Ha n [[a|b|]|] ?; simpl in *; auto. *)
(*   - by apply (Ha n (Some a)). *)
(*   - by apply (Ha n None). *)
(* Qed. *)
(* Lemma csum_update_r (b1 b2 : B) : b1 ~~> b2 → Cinr b1 ~~> Cinr b2. *)
(* Proof. *)
(*   intros Hb n [[a|b|]|] ?; simpl in *; auto. *)
(*   - by apply (Hb n (Some b)). *)
(*   - by apply (Hb n None). *)
(* Qed. *)
(* Lemma csum_updateP_l (P : A → Prop) (Q : csum A B → Prop) a : *)
(*   a ~~>: P → (∀ a', P a' → Q (Cinl a')) → Cinl a ~~>: Q. *)
(* Proof. *)
(*   intros Hx HP n mf Hm. destruct mf as [[a'|b'|]|]; try by destruct Hm. *)
(*   - destruct (Hx n (Some a')) as (c&?&?); naive_solver. *)
(*   - destruct (Hx n None) as (c&?&?); naive_solver eauto using cmra_validN_op_l. *)
(* Qed. *)
(* Lemma csum_updateP_r (P : B → Prop) (Q : csum A B → Prop) b : *)
(*   b ~~>: P → (∀ b', P b' → Q (Cinr b')) → Cinr b  ~~>: Q. *)
(* Proof. *)
(*   intros Hx HP n mf Hm. destruct mf as [[a'|b'|]|]; try by destruct Hm. *)
(*   - destruct (Hx n (Some b')) as (c&?&?); naive_solver. *)
(*   - destruct (Hx n None) as (c&?&?); naive_solver eauto using cmra_validN_op_l. *)
(* Qed. *)
(* Lemma csum_updateP'_l (P : A → Prop) a : *)
(*   a ~~>: P → Cinl a ~~>: λ m', ∃ a', m' = Cinl a' ∧ P a'. *)
(* Proof. eauto using csum_updateP_l. Qed. *)
(* Lemma csum_updateP'_r (P : B → Prop) b : *)
(*   b ~~>: P → Cinr b ~~>: λ m', ∃ b', m' = Cinr b' ∧ P b'. *)
(* Proof. eauto using csum_updateP_r. Qed. *)

(* Lemma csum_local_update_l (a1 a2 a1' a2' : A) : *)
(*   (a1,a2) ~l~> (a1',a2') → (Cinl a1,Cinl a2) ~l~> (Cinl a1',Cinl a2'). *)
(* Proof. *)
(*   intros Hup n mf ? Ha1; simpl in *. *)
(*   destruct (Hup n (mf ≫= maybe Cinl)); auto. *)
(*   { by destruct mf as [[]|]; inversion_clear Ha1. } *)
(*   split. done. by destruct mf as [[]|]; inversion_clear Ha1; constructor. *)
(* Qed. *)
(* Lemma csum_local_update_r (b1 b2 b1' b2' : B) : *)
(*   (b1,b2) ~l~> (b1',b2') → (Cinr b1,Cinr b2) ~l~> (Cinr b1',Cinr b2'). *)
(* Proof. *)
(*   intros Hup n mf ? Ha1; simpl in *. *)
(*   destruct (Hup n (mf ≫= maybe Cinr)); auto. *)
(*   { by destruct mf as [[]|]; inversion_clear Ha1. } *)
(*   split. done. by destruct mf as [[]|]; inversion_clear Ha1; constructor. *)
(* Qed. *)
End ora.

Arguments csumR : clear implicits.

(* Functor *)
#[export] Instance csum_map_ora_morphism {A A' B B' : ora} (f : A → A') (g : B → B') :
  OraMorphism f → OraMorphism g → OraMorphism (csum_map f g).
Proof.
  split; try apply _.
  - intros n [a|b|] [a'|b'|]; simpl; try done;
        rewrite -?Cinl_orderN -?Cinr_orderN; by apply ora_morphism_orderN.
  - intros [a|b|]; rewrite /= -?Increasing_cinl -?Increasing_cinr => ?;
      last apply Increasing_CsumBot; by apply ora_morphism_increasing.
Qed.

Program Definition csumRF (Fa Fb : OrarFunctor) : OrarFunctor := {|
  orarFunctor_car A _ B _ := csumR (orarFunctor_car Fa A B) (orarFunctor_car Fb A B);
  orarFunctor_map A1 _ A2 _ B1 _ B2 _ fg := csumO_map (orarFunctor_map Fa fg) (orarFunctor_map Fb fg)
|}.
Next Obligation.
  by intros Fa Fb A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply csumO_map_ne;
    try apply orarFunctor_map_ne.
Qed.
Next Obligation.
  intros Fa Fb A ? B ? x. rewrite /= -{2}(csum_map_id x).
  apply csum_map_ext=>y; apply orarFunctor_map_id.
Qed.
Next Obligation.
  intros Fa Fb A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -csum_map_compose.
  apply csum_map_ext=>y; apply orarFunctor_map_compose.
Qed.

#[export] Instance csumRF_contractive Fa Fb :
  OrarFunctorContractive Fa → OrarFunctorContractive Fb →
  OrarFunctorContractive (csumRF Fa Fb).
Proof.
  by intros ?? A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply csumO_map_ne;
    try apply orarFunctor_map_contractive.
Qed.
