Require Import flows.multiset_flows.
Require Import flows.flows.
Require Import tmpl.data_struct.

Context `{Countable K}.

Local Instance nzmap_filter: Filter (Z * nat) (@multiset_flows.K_multiset Key Z.eq_dec Z_countable).
Proof.
  intros ?? Hfl.
  eapply (NZMap (filter P (nzmap_car Hfl)) _). Unshelve.
  rewrite / bool_decide.
  destruct (nzmap_wf_decision Key (filter P (nzmap_car Hfl))); try done.
  apply n. clear n.
  rewrite / nzmap_wf /map_Forall.
  intros i x Hf.
  assert (nzmap_wf (nzmap_car Hfl)) as wfH by (apply nzmap_is_wf).
  apply map_lookup_filter_Some_1_1 in Hf.
  rewrite /nzmap_wf /map_Forall in wfH. naive_solver.
Defined.

Lemma nzmap_lookup_filter_Some `{Countable K} `{CCM A}
  (P : Z * nat → Prop) (H7 : ∀ x : Z * nat, Decision (P x)) (m : nzmap Z nat) (i : Z) (x : nat):
  filter P m !! i = Some x <-> m !! i = Some x /\ P (i, x).
Proof.
  rewrite /lookup /nzmap_lookup. split; intros Hx; destruct m;
    [by rewrite /filter /= map_lookup_filter_Some in Hx |
      by rewrite /filter map_lookup_filter_Some].
Qed.

Lemma nzmap_dom_filter_subseteq (P : Z * nat → Prop) `{!∀ x, Decision (P x)} (m : nzmap Z nat):
  dom (filter P m) ⊆ dom m.
Proof. destruct m. rewrite / filter /nzmap_dom /=. apply dom_filter_subseteq. Qed.

Lemma nzmap_filter_dom_L (P : Z → Prop) `{!∀ x, Decision (P x)} (m : nzmap Z nat):
  filter P (dom m) = dom (filter (λ kv : Z * nat, P kv.1) m).
Proof. destruct m. rewrite / filter /nzmap_dom /=. apply filter_dom_L. Qed.

Lemma nzmap_empty_dom (m : nzmap Z nat):
  m = (∅ : nzmap Z nat) <-> dom m ≡ ∅.
Proof.
  destruct m. rewrite /nzmap_dom /= dom_empty_iff.
  split.
  - intros H1. inversion H1. auto.
  - intros. by apply nzmap_gmap_eq.
Qed.

Lemma nzmap_lookup_filter_None (P : Z * nat → Prop) `{!∀ x, Decision (P x)} (m : nzmap Z nat) (i : Z):
  filter P m !! i = None ↔ m !! i = None ∨ ∀ x, m !! i = Some x → ¬ P (i, x).
Proof.
  destruct m. rewrite / filter.
  rewrite eq_None_not_Some /is_Some. setoid_rewrite nzmap_lookup_filter_Some. naive_solver.
Qed.

Lemma nzmap_filter_strong_ext (P Q: Z * nat → Prop) `{!∀ x, Decision (P x)}
  `{!∀ x, Decision (Q x)} (m1 m2: nzmap Z nat):
  filter P m1 = filter Q m2 <->
    ∀ (i : Z) (x : nat), P (i, x) ∧ m1 !! i = Some x ↔ Q (i, x) ∧ m2 !! i = Some x.
Proof.
  pose proof (nzmap_is_wf (filter P m1)) as Hm1_wf.
  pose proof (nzmap_is_wf (filter Q m2)) as Hm2_wf.
  rewrite nzmap_eq.
  setoid_rewrite -> option_eq.
  split.
  - intros Hf i x. specialize (Hf i).
    rewrite ! nzmap_lookup_total_alt in Hf.
    rewrite /default /id in Hf.
    destruct (filter P m1 !! i) eqn: HfP.
    destruct (filter Q m2 !! i) eqn: HfQ.
    rewrite nzmap_lookup_filter_Some in HfQ.
    rewrite nzmap_lookup_filter_Some in HfP.
    subst.
    split; auto.
    + intros (HP & HPm).
      specialize (HPm x).
      pose proof (eq_refl (Some x)) as Hsome.
      apply HPm in Hsome.
      destruct HfP as (HfPm1 & _).
      destruct HfQ as (HfQm1 & HQ).
      rewrite Hsome in HfPm1. inversion HfPm1; subst.
      split; auto.
      split.
      { intros Hm2. rewrite Hm2 in HfQm1. inversion HfQm1; auto. }
      { intros Hx. by inversion Hx; subst. }
    + intros (HQ & HQm).
      specialize (HQm x).
      pose proof (eq_refl (Some x)) as Hsome.
      apply HQm in Hsome.
      destruct HfQ as (HfQm1 & _).
      destruct HfP as (HfPm1 & HP).
      rewrite Hsome in HfQm1. inversion HfQm1; subst.
      split; auto.
      split.
      { intros Hm1. rewrite Hm1 in HfPm1. inversion HfQm1; auto. }
      { intros Hx. by inversion Hx; subst. }
    + apply nzmap_lookup_filter_None in HfQ.
      split.
      { intros (? & HPm1). subst.
        rewrite /nzmap_wf /map_Forall in Hm1_wf.
        assert (nzmap_car (filter P m1) !! i = Some 0%CCM) as HnzmapP by auto.
        apply Hm1_wf in HnzmapP. easy. }
      { intros (HQ & HQm1).
        pose proof (eq_refl (Some x)) as Hsome.
        apply HQm1 in Hsome.
        destruct HfQ as [HfQ1 | HfQ2].
        rewrite Hsome in HfQ1. easy.
        apply HfQ2 in Hsome. easy. }
    + destruct (filter Q m2 !! i) eqn: HfQ; subst.
      split.
      { intros (? & HQm1). 
        rewrite /nzmap_wf /map_Forall in Hm2_wf.
        assert (nzmap_car (filter Q m2) !! i = Some 0%CCM) as HnzmapQ by auto.
        apply Hm2_wf in HnzmapQ. easy. }
      { intros (HQ & HQm1).
        apply nzmap_lookup_filter_None in HfP.
        pose proof (eq_refl (Some x)) as Hsome.
        apply HQm1 in Hsome.
        rewrite /nzmap_wf /map_Forall in Hm2_wf.
        assert (nzmap_car (filter Q m2) !! i = Some 0%CCM) as HnzmapQ by auto.
        apply Hm2_wf in HnzmapQ. easy. }
      { split.
        { intros (HP & Hm).
          apply nzmap_lookup_filter_None in HfP.
          pose proof (eq_refl (Some x)) as Hsome.
          apply Hm in Hsome.
          destruct HfP as [HfPm1 | Hm1].
          rewrite Hsome in HfPm1. inversion HfPm1; auto.
          apply Hm1 in Hsome. easy.
        }
        { intros (HQ & HQm1).
          apply nzmap_lookup_filter_None in HfQ.
          pose proof (eq_refl (Some x)) as Hsome.
          apply HQm1 in Hsome.
          destruct HfQ as [HfQm2 | Hm2].
          rewrite Hsome in HfQm2. inversion HfQm2; auto.
          apply Hm2 in Hsome. easy. }
      }
    - intros Heq.
      apply nzmap_eq, nzmap_gmap_eq.
      setoid_rewrite <- option_eq in Heq.
      rewrite /filter /= in Heq.
      apply map_filter_strong_ext.
      intros i x.
      specialize (Heq i x).
      destruct m1, m2.
      destruct Heq as (HP & HQ).
      split; intros HP'; by [apply HP in HP' | apply HQ in HP'].
Qed.

Lemma nzmap_filter_filter (P: Z * nat → Prop) `{!∀ x, Decision (P x)}
  (Q: Z * nat → Prop) `{!∀ x, Decision (Q x)} (m : nzmap Z nat):
  filter P (filter Q m) = filter (λ '(i, x), (P (i, x) ∧ Q (i, x))%type) m.
Proof. apply nzmap_filter_strong_ext. intros ??.
       rewrite nzmap_lookup_filter_Some. naive_solver.
Qed.

Local Instance nzmap_union: Union (nzmap Z nat) :=
  nzmap_merge (λ x y, if decide (x = 0) then y else x).

Lemma nzmap_filter_union_complement (P : Z * nat → Prop) `{!∀ x, Decision (P x)} (m : nzmap Z nat):
    filter P m ∪ filter (λ v : Z * nat, (¬ P v)%type) m = m.
Proof.
  apply nzmap_gmap_eq.
  rewrite / filter /= /merge.
  erewrite <- map_filter_union_complement with (P := P).
  apply map_eq.
  intros i.
  rewrite lookup_merge lookup_union /diag_None.
  destruct (filter P (nzmap_car m) !! i) eqn: E1.
  rewrite E1.
  simpl.
  destruct (decide(0%CCM = _)) as [Hz | Hz].
  - destruct (decide (0%CCM = n)) as [Hn | Hn]; auto.
    pose proof (nzmap_is_wf (filter P m)) as Hm1_wf.
    rewrite /nzmap_wf /map_Forall in Hm1_wf.
    replace (filter P (nzmap_car m)) with (nzmap_car (filter P m)) in E1 by set_solver.
    apply Hm1_wf in E1. rewrite Hn in E1. easy.
    rewrite decide_False in Hz; auto. easy.
  - destruct (decide (0%CCM = n)) as [Hn | Hn]; auto.
    pose proof (nzmap_is_wf (filter P m)) as Hm1_wf.
    rewrite /nzmap_wf /map_Forall in Hm1_wf.
    replace (filter P (nzmap_car m)) with (nzmap_car (filter P m)) in E1 by set_solver.
    apply Hm1_wf in E1. rewrite Hn in E1. easy.
    rewrite decide_False in Hz; auto.
    rewrite decide_False; auto.
    assert (filter (λ v : Z * nat, (¬ P v)%type) (nzmap_car m) !! i = None) as ->; auto.
    {
      apply map_lookup_filter_None.
      right.
      apply map_lookup_filter_Some in E1.
      intros ? Hx.
      destruct E1 as (Hx' & HE1).
      rewrite Hx' in Hx. inversion Hx; subst. auto.
    }
  - rewrite E1.
    destruct (filter (λ v : Z * nat, (¬ P v)%type) (nzmap_car m) !! i) eqn: E2;
    rewrite E2 /=; try done.
    destruct (decide (0%CCM = n)) as [Hn | Hn].
    pose proof (nzmap_is_wf (filter (λ v : Z * nat, (¬ P v)%type) m)) as Hm1_wf.
    rewrite /nzmap_wf /map_Forall in Hm1_wf.
    replace (filter (λ v : Z * nat, (¬ P v)%type) _) with
      (nzmap_car (filter (λ v : Z * nat, (¬ P v)%type) m)) in E2 by set_solver.
    apply Hm1_wf in E2. rewrite Hn in E2. easy. auto.
Qed.

Ltac filter_tac :=
  rewrite !nzmap_filter_dom_L; f_equal;
  try rewrite nzmap_filter_filter;
  rewrite nzmap_filter_strong_ext;
  intros; split; intros Hneq; split; try lia; by destruct Hneq.

Lemma union_filter2 x x0 (S : multiset_flows.K_multiset):
  (x < x0)%Z ->
  filter (λ k : Z, (x < k <= x0)%Z) (dom S) ∪ filter (λ k : Z, (x0 < k)%Z) (dom S) =
    filter (λ k : Z, (x < k)%Z) (dom S).
Proof.
  intros HLe.
  assert (filter (λ k : Z, (x < k)%Z) (dom S) =
          filter (λ k : Z, (x < k ≤ x0)%Z) (filter (λ k : Z, (x < k)%Z) (dom S)) ∪
          filter (λ x1 : Z, (¬ (x < x1 ≤ x0)%Z)%type) (filter (λ k : Z, (x < k)%Z) (dom S))) as ->.
  { symmetry.
    apply (filter_union_complement_L (C := gset Key) _ _ (filter (λ k : Z, (x < k)%Z) (dom S))).
  }
  assert (filter (λ k : Z, (x0 < k)%Z) (dom S) =
      filter (λ x1 : Z, (¬ (x < x1 ≤ x0)%Z)%type) (filter (λ k : Z, (x < k)%Z) (dom S))) as ->.
  { filter_tac. }
  assert (filter (λ k : Z, (x < k ≤ x0)%Z) (dom S) =
            filter (λ k : Z, (x < k ≤ x0)%Z)
              (filter (λ k : Z, (x < k)%Z) (dom S))) as -> by filter_tac; auto.
Qed.

(* For list *)
Lemma union_filter x0 (S : multiset_flows.K_multiset):
 filter (λ y : Z, (y < x0)%Z) (dom S) ∪
           filter (λ y : Z, (x0 < y)%Z) (dom S) ∪
           filter (λ y : Z, (y = x0)%Z) (dom S) = dom S.
Proof.
  assert (filter (λ y : Z, (y < x0)%Z) (dom S) ∪
           filter (λ x : Z, (¬ (x < x0)%Z)%type) (dom S) = dom S) as Hx.
  { eapply (filter_union_complement_L _ _ (dom S)); auto. }
  rewrite <- Hx at 4.
  assert (filter (λ x1 : Z, (¬ (x1 < x0)%Z)%type) (dom S) =
           filter (λ y : Z, (x0 < y)%Z) (dom S) ∪
            filter (λ y : Z, y = x0) (dom S)) as ->.
  { rewrite - (filter_union_complement_L (C := gset Key) (λ y : Z, (y <= x0)%Z)
                (filter (λ x1 : Z, (¬ (x1 < x0)%Z)%type) (dom S))
                  (filter (λ x1 : Z, (¬ (x1 < x0)%Z)%type) (dom S))).
    assert (filter (λ x1 : Z, (¬ (x1 ≤ x0)%Z)%type)
             (filter (λ x1 : Z, (¬ (x1 < x0)%Z)%type) (dom S)) =
               filter (λ x1 : Z, ( (x0 < x1)%Z)%type) (dom S)) as Hn. by filter_tac.
    assert (filter (λ y : Z, (y ≤ x0)%Z)
              (filter (λ x1 : Z, (¬ (x1 < x0)%Z)%type) (dom S)) =
                filter (λ x1 : Z, ( (x1 = x0)%Z)%type) (dom S)) as Hn1. by filter_tac.
    rewrite Hn Hn1. clear. set_solver.
  }
  clear. set_solver.
Qed.

(* For bst *)
Lemma union_filter_dom x0 (S : multiset_flows.K_multiset):
  dom (filter (λ kv : Z * nat, (kv.1 < x0)%Z) S)
  ∪ dom (filter (λ kv : Z * nat, (kv.1 > x0)%Z) S)
  ∪ dom (filter (λ kv : Z * nat, kv.1 = x0) S) = dom S.
Proof.
  assert (filter (λ y : Z, (y < x0)%Z) (dom S) ∪ filter (λ y : Z, (y > x0)%Z) (dom S) ∪
          filter (λ y : Z, (y = x0)%Z) (dom S) = dom S) as H_union.
  {
    pose proof (union_filter x0 S).
    assert (filter (λ y : Z, (y > x0)%Z) (dom S) = filter (λ y : Z, (x0 < y)%Z) (dom S)) as ->; auto.
    { filter_tac. }
  }
  rewrite ! nzmap_filter_dom_L in H_union; auto.
Qed.
        
(* For list *)
Lemma disjoin_filter x0 (S : multiset_flows.K_multiset): 
  (filter (λ y : Z, (y < x0)%Z) (dom S) ## filter (λ y : Z, (x0 < y)%Z) (dom S)) /\
    (filter (λ y : Z, (y < x0)%Z) (dom S) ## filter (λ y : Z, (x0 = y)%Z) (dom S)) /\
    (filter (λ y : Z, (y = x0)%Z) (dom S) ## filter (λ y : Z, (x0 < y)%Z) (dom S)).
Proof.
  repeat split; intros ? Hfl1 Hfl2; apply elem_of_filter in Hfl1, Hfl2; lia.
Qed.

(* For BST *)
Lemma disjoin_filter1 x0 (S : multiset_flows.K_multiset): 
  (filter (λ y : Z, (y < x0)%Z) (dom S) ## filter (λ y : Z, (y > x0)%Z) (dom S)) /\
    (filter (λ y : Z, (y < x0)%Z) (dom S) ## filter (λ y : Z, (y = x0)%Z) (dom S)) /\
    (filter (λ y : Z, (y = x0)%Z) (dom S) ## filter (λ y : Z, (y > x0)%Z) (dom S)).
Proof.
  repeat split; intros ? Hfl1 Hfl2; apply elem_of_filter in Hfl1, Hfl2; lia.
Qed.

Lemma union_complement x (S : multiset_flows.K_multiset):
  dom S ∖ dom (filter (λ kv : Z * nat, (x < kv.1)%Z) S)  =
          dom (filter (λ kv : Z * nat, (kv.1 < x)%Z) S) ∪
            dom (filter (λ kv : Z * nat, kv.1 = x) S).
Proof.
  pose proof (disjoin_filter x S) as (Hdisj1 & Hdisj2 & Hdisj3).
  pose proof (union_filter x S) as H_union1.
  assert (dom (filter (λ kv : Z * nat, (x < kv.1)%Z) S) ## dom (filter (λ kv : Z * nat, (kv.1 < x)%Z) S)) as Hdisj4.
  { rewrite ! nzmap_filter_dom_L in Hdisj1. auto. }
  assert (dom (filter (λ kv : Z * nat, (x < kv.1)%Z) S) ## dom (filter (λ kv : Z * nat, kv.1 = x) S)) as Hdisj5.
  { rewrite ! nzmap_filter_dom_L in Hdisj3. auto. }
  rewrite ! nzmap_filter_dom_L in H_union1.
  clear - H_union1 Hdisj2 Hdisj4 Hdisj5.
  rewrite ! nzmap_filter_dom_L in Hdisj2.
  rewrite -H_union1.
  rewrite ! difference_union_distr_l_L difference_diag_L union_empty_r_L.
  set_solver.
Qed.


Definition flowint_T := @flowintT (@multiset_flows.K_multiset Key Z.eq_dec Z_countable) _ _ _.

Lemma cxt_helper_list (Ip: flowint_T) (p next : val) x x0:
  let ks := filter (λ '(k, _), (x < k)%Z) (default 0%CCM (inf_map Ip !! p)) : multiset_flows.K_multiset in
  (x < x0)%Z ->
  filter (λ y : Z, (x0 < y)%Z) (inset _ _ _ Ip p) = 
    outset _ _ _ Ip next ->
  dom (inf Ip p) ∖ dom ks ∪ dom ks ∖ dom (out Ip next) ≡ dom (inf Ip p) ∖ dom (out Ip next).
Proof.
  intros ks HLe Hfl_in.
  rewrite /outset /inset in Hfl_in.
  assert (filter (λ k : Z, (k <= x)%Z) (dom (inf Ip p)) ∪
           filter (λ k : Z, (x < k ≤ x0)%Z) (dom (inf Ip p)) =
            filter (λ k : Z, (k ≤ x0)%Z) (dom (inf Ip p))) as H_union0.
  {
    assert (filter (λ k : Z, (k ≤ x)%Z) (dom (inf Ip p)) =
              filter (λ k : Z, (k ≤ x)%Z) (filter (λ k : Z, (k ≤ x0)%Z) (dom (inf Ip p))))
      as -> by filter_tac.
    assert (filter (λ k : Z, (x < k ≤ x0)%Z) (dom (inf Ip p)) =
      filter (λ k : Z, (¬ (k ≤ x)%Z)%type) (filter (λ k : Z, (k ≤ x0)%Z) (dom (inf Ip p))))
      as -> by filter_tac.
    apply (filter_union_complement_L
             (C := gset Key) _ _ (filter (λ k : Z, (k ≤ x0)%Z) (dom (inf Ip p)))).
  }
  rewrite ! nzmap_filter_dom_L in H_union0.
  assert (filter (λ k : Z, (k <= x)%Z) (dom (inf Ip p)) ∪
                       filter (λ k : Z, (x < k)%Z) (dom (inf Ip p)) = dom (inf Ip p)) as H_union1.
  { assert (filter (λ k : Z, (x < k)%Z) (dom (inf Ip p)) =
                         filter (λ k : Z, (¬ (k ≤ x)%Z)%type) (dom (inf Ip p))) as -> by filter_tac.
    apply (filter_union_complement_L (C := gset Key) _ _ (dom (inf Ip p))). }
    rewrite ! nzmap_filter_dom_L in H_union1.
    assert (filter (λ k : Z, (x < k <= x0)%Z) (dom (inf Ip p)) ∪
                       filter (λ k : Z, (x0 < k)%Z) (dom (inf Ip p)) =
                       filter (λ k : Z, (x < k)%Z) (dom (inf Ip p))) as H_union2.
    { apply union_filter2; auto. }
    rewrite ! nzmap_filter_dom_L in H_union2.
    assert (dom (filter (λ kv : Z * nat, (x < kv.1)%Z) (inf Ip p)) =
                       filter (λ k : Z, (x < k)%Z) (dom (inf Ip p))) as HB by filter_tac.
    rewrite ! nzmap_filter_dom_L in HB.
    rewrite <- HB in H_union2.
    assert (filter (λ k : Z, (k <= x0)%Z) (dom (inf Ip p)) ∪
                     filter (λ k : Z, (x0 < k)%Z) (dom (inf Ip p)) = dom (inf Ip p)) as H_union3.
    { assert (filter (λ k : Z, (x0 < k)%Z) (dom (inf Ip p)) =
            filter (λ k : Z, (¬ (k ≤ x0)%Z)%type) (dom (inf Ip p))) as -> by filter_tac.
        apply (filter_union_complement_L (C := gset Key) _ _ (dom (inf Ip p))).
    }
    rewrite ! nzmap_filter_dom_L in H_union3.
    assert (dom (filter (λ kv : Z * nat, (x < kv.1)%Z) (inf Ip p)) = dom ks) as Hdom_ks by auto.
    assert (filter (λ y : Z, (x0 < y)%Z) (dom (inf Ip p)) =
           dom (filter (λ kv : Z * nat, (x0 < kv.1)%Z) (inf Ip p))) as HC by filter_tac.
    rewrite -Hfl_in HC.
    rewrite Hdom_ks in H_union1, H_union2.
    set A := dom (inf Ip p).
    set B := dom ks.
    set C := dom (filter (λ kv : Z * nat, (x0 < kv.1)%Z) (inf Ip p)).
      (* B ## X *)
    assert (filter (λ k : Z, (x < k)%Z) (dom (inf Ip p)) ##
                     filter (λ k : Z, (k <= x)%Z) (dom (inf Ip p))) as Hdisj1.
    { intros ? Hfl1 Hfl2. apply elem_of_filter in Hfl1, Hfl2. lia. }
    rewrite ! nzmap_filter_dom_L in Hdisj1.
      (* C ## Y *)
      assert (filter (λ k : Z, (x0 < k)%Z) (dom (inf Ip p)) ##
                     filter (λ k : Z, (x < k <= x0)%Z) (dom (inf Ip p))) as Hdisj2.
      { intros ? Hfl1 Hfl2. apply elem_of_filter in Hfl1, Hfl2. lia. }
      rewrite ! nzmap_filter_dom_L in Hdisj2.
      (* C ## Z *)
      assert (filter (λ k : Z, (x0 < k)%Z) (dom (inf Ip p)) ##
                     filter (λ k : Z, (k <= x0)%Z) (dom (inf Ip p))) as Hdisj3.
      { intros ? Hfl1 Hfl2. apply elem_of_filter in Hfl1, Hfl2. lia. }
      rewrite ! nzmap_filter_dom_L in Hdisj3.
      set X := dom (filter (λ kv : Z * nat, (kv.1 ≤ x)%Z) (inf Ip p)).
      set Y := dom (filter (λ kv : Z * nat, (x < kv.1 ≤ x0)%Z) (inf Ip p)).
      set Z := dom (filter (λ kv : Z * nat, (kv.1 ≤ x0)%Z) (inf Ip p)).
      (*A ∖ B ≡ X*)
      assert (A ∖ B ≡ X) as Hdif_AB. clear -Hdisj1 H_union1. set_solver.
      assert (B ∖ C ≡ Y) as Hdif_BC. clear -Hdisj2 H_union2. set_solver.
      assert (A ∖ C ≡ Z) as Hdif_AC. clear -Hdisj3 H_union3. set_solver.
      assert (X ∪ Y ≡ Z) as HXYZ. clear -H_union0. set_solver.
      repeat rewrite leibniz_equiv_iff in Hdif_AB, Hdif_BC, Hdif_AC.
      by rewrite Hdif_AB Hdif_BC Hdif_AC.
Qed.
