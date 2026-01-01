From stdpp Require Export coPset.
From iris_ora.algebra Require Import gmap agree.
From iris.proofmode Require Import proofmode.
From iris_ora.logic Require Export own wsat later_credits.
From iris.prelude Require Import options.
Export wsatGS.
Import ouPred le_upd_if bi.

Inductive has_lc := HasLc | HasNoLc.

Class invGpreS (Σ : gFunctors) : Set := InvGpreS {
  invGpreS_wsat : wsatGpreS Σ;
  invGpreS_lc : lcGpreS Σ;
}.

Class invGS_gen (hlc : has_lc) (Σ : gFunctors) : Set := InvG {
  invGS_wsat : wsatGS Σ;
  invGS_lc : lcGS Σ;
}.
Global Hint Mode invGS_gen - - : typeclass_instances.
Global Hint Mode invGpreS - : typeclass_instances.
Local Existing Instances invGpreS_wsat invGpreS_lc.
(* [invGS_lc] needs to be global in order to enable the use of lemmas like [lc_split]
   that require [lcGS], and not [invGS].
   [invGS_wsat] also needs to be global as the lemmas in [invariants.v] require it. *)
Global Existing Instances invGS_lc invGS_wsat.

Notation invGS := (invGS_gen HasLc).

Definition invΣ : gFunctors :=
  #[wsatΣ; lcΣ].
Global Instance subG_invΣ {Σ} : subG invΣ Σ → invGpreS Σ.
Proof. solve_inG. Qed.

Local Definition ouPred_fupd_def `{!invGS_gen hlc Σ} (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  wsat ∗ ownE E1 -∗ le_upd_if (if hlc is HasLc then true else false) (◇ (wsat ∗ ownE E2 ∗ P)).
Local Definition ouPred_fupd_aux : seal (@ouPred_fupd_def). Proof. by eexists. Qed.
Definition ouPred_fupd := ouPred_fupd_aux.(unseal).
Global Arguments ouPred_fupd {hlc Σ _}.
Local Lemma ouPred_fupd_unseal `{!invGS_gen hlc Σ} : @fupd _ ouPred_fupd = ouPred_fupd_def.
Proof. rewrite -ouPred_fupd_aux.(seal_eq) //. Qed.

Lemma ouPred_fupd_mixin `{!invGS_gen hlc Σ} : BiFUpdMixin (ouPredI (iResUR Σ)) ouPred_fupd.
Proof.
  split.
  - rewrite ouPred_fupd_unseal. solve_proper.
  - intros E1 E2 (E1''&->&?)%subseteq_disjoint_union_L.
    rewrite ouPred_fupd_unseal /ouPred_fupd_def ownE_op //.
    by iIntros "($ & $ & HE) !> !> [$ $] !> !>" .
  - rewrite ouPred_fupd_unseal.
    iIntros (E1 E2 P) ">H [Hw HE]". iApply "H"; by iFrame.
  - rewrite ouPred_fupd_unseal.
    iIntros (E1 E2 P Q HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
  - rewrite ouPred_fupd_unseal. iIntros (E1 E2 E3 P) "HP HwE".
    iMod ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
  - intros E1 E2 Ef P HE1Ef. rewrite ouPred_fupd_unseal /ouPred_fupd_def ownE_op //.
    iIntros "Hvs (Hw & HE1 &HEf)".
    iMod ("Hvs" with "[Hw HE1]") as ">($ & HE2 & HP)"; first by iFrame.
    iDestruct (ownE_op' with "[HE2 HEf]") as "[? $]"; first by iFrame.
    iIntros "!> !>". by iApply "HP".
  - rewrite ouPred_fupd_unseal /ouPred_fupd_def. by iIntros (????) "[HwP $]".
Qed.
Global Instance ouPred_bi_fupd `{!invGS_gen hlc Σ} : BiFUpd (iProp Σ) :=
  {| bi_fupd_mixin := ouPred_fupd_mixin |}.

Global Instance ouPred_bi_bupd_fupd `{!invGS_gen hlc Σ} : BiBUpdFUpd (iProp Σ).
Proof. rewrite /BiBUpdFUpd ouPred_fupd_unseal. by iIntros (E P) ">? [$ $] !> !>". Qed.

(** Later credits: the laws are only available when we opt into later credit support.*)

(** [lc_fupd_elim_later] allows to eliminate a later from a hypothesis at an update.
  This is typically used as [iMod (lc_fupd_elim_later with "Hcredit HP") as "HP".],
  where ["Hcredit"] is a credit available in the context and ["HP"] is the
  assumption from which a later should be stripped. *)
Lemma lc_fupd_elim_later `{!invGS_gen HasLc Σ} E P :
   £ 1 -∗ (▷ P) -∗ |={E}=> P.
Proof.
  iIntros "Hf Hupd".
  rewrite ouPred_fupd_unseal /ouPred_fupd_def.
  iIntros "[$ $]". iApply (le_upd_later with "Hf").
  iNext. by iModIntro.
Qed.

(** If the goal is a fancy update, this lemma can be used to make a later appear
  in front of it in exchange for a later credit.
  This is typically used as [iApply (lc_fupd_add_later with "Hcredit")],
  where ["Hcredit"] is a credit available in the context. *)
Lemma lc_fupd_add_later `{!invGS_gen HasLc Σ} E1 E2 P :
  £ 1 -∗ (▷ |={E1, E2}=> P) -∗ |={E1, E2}=> P.
Proof.
  iIntros "Hf Hupd". iApply (fupd_trans E1 E1).
  iApply (lc_fupd_elim_later with "Hf Hupd").
Qed.


Lemma fupd_soundness_no_lc0 `{!invGpreS Σ} E1 E2 (P: iProp Σ) `{!Plain P} `{!Absorbing P}:
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, ⊢ |={E1,E2}=> P) → ⊢ P.
Proof.
  iIntros (Hfupd). apply later_soundness, bupd_plain_soundness; first apply _. iMod wsat_alloc as (Hw) "[Hw HE]".
  (* We don't actually want any credits, but we need the [lcGS]. *)
  iMod (later_credits.le_upd.lc_alloc 0) as (Hc) "[_ Hc]".
  set (Hi := InvG HasNoLc _ Hw Hc).
  iAssert (|={⊤,E2}=> P)%I with "[Hc]" as "H".
  { iMod (fupd_mask_subseteq E1) as "_"; first done. iApply Hfupd. }
  rewrite ouPred_fupd_unseal /ouPred_fupd_def /=.
  iMod ("H" with "[$]") as "[_ [_ >H']]"; by iFrame.
Qed.

Lemma fupd_soundness_no_lc `{!invGpreS Σ} E1 E2 (P : iProp Σ) `{!Plain P} `{!Absorbing P} m :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, £ m ={E1,E2}=∗ P) → ⊢ P.
Proof.
  iIntros (Hfupd). apply later_soundness, bupd_plain_soundness; first apply _. iMod wsat_alloc as (Hw) "[Hw HE]".
  (* We don't actually want any credits, but we need the [lcGS]. *)
  iMod (later_credits.le_upd.lc_alloc m) as (Hc) "[_ Hc]".
  set (Hi := InvG HasNoLc _ Hw Hc).
  iAssert (|={⊤,E2}=> P)%I with "[Hc]" as "H".
  { iMod (fupd_mask_subseteq E1) as "_"; first done. iApply Hfupd; last done. }
  rewrite ouPred_fupd_unseal /ouPred_fupd_def.
  iMod ("H" with "[$]") as "[_ [_ >H']]"; by iFrame.
Qed.

Lemma fupd_soundness_lc `{!invGpreS Σ} n E1 E2 (P: iProp Σ) `{!Plain P} `{!Absorbing P}:
  (∀ `{Hinv: !invGS_gen HasLc Σ}, ⊢ £ n ={E1,E2}=∗ P) → ⊢ P.
Proof.
  iIntros (Hfupd). eapply (lc_soundness (S n)); [done..|].
  intros Hc. rewrite lc_succ.
  iIntros "[Hone Hn]". rewrite -le_upd_trans. iApply bupd_le_upd.
  iMod wsat_alloc as (Hw) "[Hw HE]".
  set (Hi := InvG HasLc _ Hw Hc).
  iAssert (|={⊤,E2}=> P)%I with "[Hn]" as "H".
  { iMod (fupd_mask_subseteq E1) as "_"; first done. by iApply (Hfupd Hi). }
  rewrite ouPred_fupd_unseal /ouPred_fupd_def.
  iModIntro. iMod ("H" with "[$Hw $HE]") as "H".
  iPoseProof (bi.except_0_into_later with "H") as "H".
  iApply (le_upd_later with "Hone"). iNext.
  iDestruct "H" as "(_ & _ & $)".
Qed.

(* an alternative to using BiBUpdPlainly/BiFUpdPlainly, which don't hold in linear logics *)
Section fupd_plain.

Context `{!invGS_gen HasNoLc Σ}.
Implicit Types (P : iProp Σ).

Lemma bupd_plainly P `{!Absorbing P}: (|==> ■ P) ⊢ P.
Proof.
  rewrite -{2}(absorbing P).
  rewrite /bi_absorbingly; ouPred.unseal; split => n x Hnx /= Hng.
  destruct (Hng n ε) as [? [_ Hng']]; try rewrite right_id; auto.
  eexists _, _; split; last by split; [apply I | apply Hng'].
  rewrite right_id //.
Qed.

Lemma fupd_plainly_mask_empty E `{!Absorbing P}: (|={E,∅}=> ■ P) ⊢ |={E}=> P.
Proof.
  rewrite -{2}(absorbing P).
  rewrite ouPred_fupd_unseal /ouPred_fupd_def. iIntros "H [Hw HE]".
  iAssert (◇ ■ P)%I as "#>HP".
  { iApply bupd_plainly. iMod ("H" with "[$]") as "(_ & _ & #HP)".
  by iIntros "!> !>". }
  by iFrame.
Qed.

Lemma fupd_plainly_mask E E' P `{!Absorbing P}: (|={E,E'}=> ■ P) ⊢ |={E}=> P.
Proof.
  rewrite -(fupd_plainly_mask_empty).
  apply fupd_elim, (fupd_mask_intro_discard _ _ _). set_solver.
Qed.

Lemma fupd_plain_mask E E' P `{!Plain P} `{!Absorbing P}: (|={E,E'}=> P) ⊢ |={E}=> P.
Proof. by rewrite {1}(plain P) fupd_plainly_mask. Qed.

Lemma fupd_plainly_elim E P `{!Absorbing P}: ■ P ⊢ |={E}=> P.
Proof. by rewrite (fupd_intro E (■ P)) fupd_plainly_mask. Qed.

Lemma fupd_plainly_later E P `{!Absorbing P}: (▷ |={E}=> ■ P) ⊢ |={E}=> ▷ ◇ P.
Proof.
  rewrite ouPred_fupd_unseal /ouPred_fupd_def. iIntros "H [Hw HE]".
  iAssert (▷ ◇ ■ P)%I as "#HP".
  { iNext. iApply bupd_plainly. iMod ("H" with "[$]") as "(_ & _ & #HP)".
    by iIntros "!> !>". }
  iFrame. iIntros "!> !> !>". by iMod "HP".
Qed.

Lemma fupd_plain_later E P `{!Plain P} `{!Absorbing P}: (▷ |={E}=> P) ⊢ |={E}=> ▷ ◇ P.
Proof. by rewrite {1}(plain P) fupd_plainly_later. Qed.

Lemma fupd_plainly_keep_l E R P : (R ={E}=∗ ■ P) ∗ R ⊢ |={E}=> ■ P ∗ R.
Proof.
  rewrite ouPred_fupd_unseal /ouPred_fupd_def. iIntros "[H HQ] [Hw HE]".
  iAssert (◇ ■ P)%I as "#>HP".
  { iApply bupd_plainly. iMod ("H" with "HQ [$]") as "(_ & _ & #HP)".
    by iIntros "!> !>". }
  by iFrame.
Qed.

Lemma fupd_plain_keep_l E R P `{!Plain P} `{!Absorbing P}: (R ={E}=∗ P) ∗ R ⊢ |={E}=> P ∗ R.
Proof.
  rewrite {1}(plain P) fupd_plainly_keep_l plainly_elim //.
Qed.

Lemma fupd_plainly_forall_2 E {A} (P : A → iProp Σ) `{!∀x, Absorbing (P x)}: (∀x, |={E}=> ■ P x) ⊢ |={E}=> ∀x, P x.
Proof.
  rewrite ouPred_fupd_unseal /ouPred_fupd_def. iIntros "HP [Hw HE]".
  iAssert (◇ ■ ∀ x : A, P x)%I as "#>HP'".
  { iIntros (x). rewrite -(bupd_plainly (◇ ■ P x)%I).
    iMod ("HP" with "[$Hw $HE]") as "(_&_&#?)". by iIntros "!> !>". }
  by iFrame.
Qed.

Lemma fupd_plain_forall_2 E {A} (P : A → iProp Σ) `{!∀x, Plain (P x)} `{!∀x, Absorbing (P x)}: (∀x, |={E}=> P x) ⊢ |={E}=> ∀x, P x.
Proof. rewrite -fupd_plainly_forall_2. apply bi.forall_mono; intros x; rewrite {1}(plain (P x)) //. Qed.

Lemma fupd_plain_forall E1 E2 {A} (Φ :  A → iProp Σ) `{!∀ x, Plain (Φ x)} `{!∀ x, Absorbing (Φ x)} :
  E2 ⊆ E1 →
  (|={E1,E2}=> ∀ x, Φ x) ⊣⊢ (∀ x, |={E1,E2}=> Φ x).
Proof.
  intros. apply (anti_symm _); first apply fupd_forall.
  trans (∀ x, |={E1}=> Φ x)%I.
  { apply bi.forall_mono=> x. by rewrite fupd_plain_mask. }
  rewrite fupd_plain_forall_2. apply fupd_elim.
  rewrite {1}(plain (∀ x, Φ x)) (fupd_mask_intro_discard E1 E2 (■ _)) //.
  apply fupd_elim. by rewrite fupd_plainly_elim.
Qed.

Lemma fupd_plain_forall' E {A} (Φ : A → iProp Σ) `{!∀ x, Plain (Φ x)} `{!∀ x, Absorbing (Φ x)}:
  (|={E}=> ∀ x, Φ x) ⊣⊢ (∀ x, |={E}=> Φ x).
Proof. by apply fupd_plain_forall. Qed.

Lemma step_fupd_plain Eo Ei P `{!Plain P} `{!Absorbing P}: (|={Eo}[Ei]▷=> P) ⊢ |={Eo}=> ▷ ◇ P.
Proof.
  rewrite -(fupd_plain_mask _ Ei (▷ ◇ P)).
  apply fupd_elim. by rewrite fupd_plain_mask -fupd_plain_later.
Qed.

Lemma step_fupdN_plain Eo Ei n P `{!Plain P} `{!Absorbing P}: (|={Eo}[Ei]▷=>^n P) ⊢ |={Eo}=> ▷^n ◇ P.
Proof.
  induction n as [|n IH].
  - by rewrite -fupd_intro -bi.except_0_intro.
  - rewrite Nat.iter_succ step_fupd_fupd IH !fupd_trans step_fupd_plain.
    apply fupd_mono. destruct n as [|n]; simpl.
    * by rewrite bi.except_0_idemp.
    * by rewrite bi.except_0_later.
Qed.

Lemma step_fupd_plain_forall Eo Ei {A} (Φ : A → iProp Σ) `{!∀ x, Plain (Φ x)} `{!∀ x, Absorbing (Φ x)} :
      Ei ⊆ Eo →
      (|={Eo}[Ei]▷=> ∀ x, Φ x) ⊣⊢ (∀ x, |={Eo}[Ei]▷=> Φ x).
Proof.
  intros. apply (anti_symm _).
  {  apply bi.forall_intro=> x. by rewrite (bi.forall_elim x). }
  trans (∀ x, |={Eo}=> ▷ ◇ Φ x)%I.
  { apply bi.forall_mono=> x. by rewrite step_fupd_plain. }
  rewrite -fupd_plain_forall'. apply fupd_elim.
  rewrite -(fupd_except_0 Ei Eo) -step_fupd_intro //.
  by rewrite -bi.later_forall -bi.except_0_forall.
Qed.

Lemma step_fupdN_plain_forall Eo Ei n {A} (Φ : A → iProp Σ) `{!∀ x, Plain (Φ x)} `{!∀ x, Absorbing (Φ x)} :
      Ei ⊆ Eo →
      (|={Eo}[Ei]▷=>^n ∀ x, Φ x) ⊣⊢ (∀ x, |={Eo}[Ei]▷=>^n Φ x).
Proof.
  intros.
  iSplit.
  - iIntros; iApply step_fupdN_mono; last done; eauto.
  - destruct n; first by eauto.
    rewrite bi.forall_mono.
    2: { intros; apply step_fupdN_plain; apply _. }
    iIntros "H".
    rewrite fupd_plain_forall_2 /=.
    iMod "H".
    rewrite -(Nat.iter_succ n (λ P, |={Eo}[Ei]▷=> P)%I) Nat.iter_succ_r.
    iApply step_fupdN_intro; first done.
    iInduction n as [|] "IH"; simpl.
    + iApply fupd_mask_intro; first done; iIntros "Hclose !>"; iMod "Hclose" as "_".
      iApply fupd_plain_forall_2; iIntros (x).
      by iMod ("H" $! x).
    + iNext; by iApply "IH".
Qed.

End fupd_plain.

Lemma step_fupdN_soundness_no_lc `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} `{!Absorbing P} n m :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, £ m ={⊤,∅}=∗ |={∅}▷=>^n P) →
  ⊢ P.
Proof.
  intros Hiter.
  apply (laterN_soundness _  (S n)); simpl.
  apply (fupd_soundness_no_lc ⊤ ⊤ _ m)=> Hinv. iIntros "Hc".
  iPoseProof (Hiter Hinv) as "H". clear Hiter.
  iApply fupd_plainly_mask_empty. iSpecialize ("H" with "Hc").
  iMod (step_fupdN_plain with "H") as "H". iMod "H". iModIntro.
  rewrite -later_plainly -laterN_plainly -later_laterN laterN_later.
  iNext. iMod "H" as "#H". auto.
Qed.

Lemma step_fupdN_soundness_no_lc' `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} `{!Absorbing P} n m :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, £ m ={⊤}[∅]▷=∗^n P) →
  ⊢ P.
Proof.
  iIntros (Hiter). eapply (step_fupdN_soundness_no_lc _ n m)=>Hinv.
  iIntros "Hcred". destruct n as [|n].
  { by iApply fupd_mask_intro_discard; last iApply (Hiter Hinv). }
   simpl in Hiter |- *. iMod (Hiter with "Hcred") as "H". iIntros "!>!>!>".
  iMod "H". clear -Absorbing0. iInduction n as [|n] "IH"; [by iApply fupd_mask_intro_discard|].
  simpl. iMod "H". iIntros "!>!>!>". iMod "H". by iApply "IH".
Qed.

Lemma step_fupdN_soundness_lc `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} `{!Absorbing P} n m :
  (∀ `{Hinv: !invGS_gen HasLc Σ}, £ m ={⊤,∅}=∗ |={∅}▷=>^n P) →
  ⊢ P.
Proof.
  intros Hiter.
  eapply (fupd_soundness_lc (m + n)); [apply _..|].
  iIntros (Hinv) "Hlc". rewrite lc_split.
  iDestruct "Hlc" as "[Hm Hn]". iMod (Hiter with "Hm") as "Hupd".
  clear Hiter.
  iInduction n as [|n] "IH"; simpl.
  - by iModIntro.
  - rewrite lc_succ. iDestruct "Hn" as "[Hone Hn]".
    iMod "Hupd". iMod (lc_fupd_elim_later with "Hone Hupd") as "> Hupd".
    by iApply ("IH" with "Hn Hupd").
Qed.

Lemma step_fupdN_soundness_lc' `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} `{!Absorbing P} n m :
  (∀ `{Hinv: !invGS Σ}, £ m ={⊤}[∅]▷=∗^n P) →
  ⊢ P.
Proof.
  intros Hiter.
  eapply (fupd_soundness_lc (m + n) ⊤ ⊤); [apply _..|].
  iIntros (Hinv) "Hlc". rewrite lc_split.
  iDestruct "Hlc" as "[Hm Hn]". iPoseProof (Hiter with "Hm") as "Hupd".
  clear Hiter.
  (* FIXME can we reuse [step_fupdN_soundness_lc] instead of redoing the induction? *)
  iInduction n as [|n] "IH"; simpl.
  - by iModIntro.
  - rewrite lc_succ. iDestruct "Hn" as "[Hone Hn]".
    iMod "Hupd". iMod (lc_fupd_elim_later with "Hone Hupd") as "> Hupd".
    by iApply ("IH" with "Hn Hupd").
Qed.

(** Generic soundness lemma for the fancy update, parameterized by [use_credits]
  on whether to use credits or not. *)
Lemma step_fupdN_soundness_gen `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} `{!Absorbing P}
  (hlc : has_lc) (n m : nat) :
  (∀ `{Hinv : invGS_gen hlc Σ},
    £ m ={⊤,∅}=∗ |={∅}▷=>^n P) →
  ⊢ P.
Proof.
  destruct hlc.
  - apply step_fupdN_soundness_lc; apply _.
  - apply step_fupdN_soundness_no_lc; apply _.
Qed.
