Require Import VST.concurrency.conclib.
From iris.algebra Require Import excl auth gmap agree gset csum.
Require Import flows.inset_flows.
Require Import flows.multiset_flows.
Require Import flows.flows.
Require Import iris_ora.algebra.gmap.
Require Import iris_ora.algebra.osum.
Require Import iris_ora.logic.own.
Require Import iris_ora.algebra.ext_order.
Require Import iris_ora.algebra.frac_auth.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import tmpl.flows_ora.
Require Import tmpl.keyset_ra_ora.
Require Export tmpl.data_struct.

Section interface_more.
  
  Context `{N: NodeRep } `{EqDecision K} `{Countable K}.
  Context `{!flowintG Σ, !nodesetG Σ, !nodemapG Σ, !keymapG Σ, !keysetG Σ}.

  Lemma flowint_update_result γ I I_n I_n' x :
    ⌜flowint_update_P _ I I_n I_n' x⌝ ∧ own γ x ⊢
                                          ∃ I', ⌜contextualLeq _ I I' /\ (∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o)⌝ ∧ own γ (● I' ⋅ ◯ I_n').
  Proof.
    unfold flowint_update_P.
    case_eq (view_auth_proj x); last first.
    - intros Hx. iIntros "(% & ?)". iExFalso. done.
    - intros [q a] Hx.
      iIntros "[HI' Hown]". iDestruct "HI'" as %HI'.
      destruct HI' as [I' HI'].
      destruct HI' as [Hagree [Hq [HIn [Hcontxl HIo]]]].
      iExists I'.
      iSplit. by iPureIntro.
      destruct x.
      simpl in Hx, HIn.
      rewrite Hx - HIn Hq Hagree.
      assert (● I' ⋅ ◯ I_n' = View (Some (DfracOwn 1, to_agree I')) I_n') as H'.
      { rewrite /(● I' ⋅ ◯ I_n') /ora_op /= /view_op_instance /=.
        replace (ε ⋅ I_n') with I_n'.
        2 : { by rewrite left_id. }
        done. }
      by rewrite H'.
  Qed.


  (* We can use auth_ks_local_update_insert from keyset_ra, no need to create a new one *)
  Lemma auth_ks_local_update p x v (m : gmap Key KValue) Ip (Cp :gmap Key KValue)
    (Hx_KS: x ∈ KS) (Hx_nin_C: x ∉ dom Cp) (Hx_in_KS: x ∈ keyset _ _ _ Ip p) :
    ✓ (prod (KS, dom m)) ∧ ✓ (prod (keyset _ _ _ Ip p, dom Cp)) ->
    (prod (KS, dom m), prod (keyset _ _ _ Ip p, dom Cp)) ~l~>
    (prod (KS, dom (<[x:=v]> m)), prod (keyset _ _ _ Ip p, dom Cp ∪ {[x]})).
  Proof.
    intros (H1 & H2).
    apply local_update_discrete.
    intros z _ Hprd.
    split.
    rewrite /(✓ prod (KS, dom (<[x:=v]> m))) /(cmra_valid keyset_ra.KsetRA) /=.
    set_solver.
    rewrite /opM /= in Hprd.
    destruct z.
    rewrite /opM /=.
    destruct c.
    destruct p0.
    rewrite /op /(cmra_op keyset_ra.KsetRA) /= in Hprd.
    destruct (decide (dom Cp ⊆ keyset _ _ _ Ip p)).
    destruct (decide (g0 ⊆ g)).
    destruct (decide (keyset _ _ _ Ip p ## g)).
    destruct (decide (dom Cp ## g0)).
    inversion Hprd; subst.
    rename H3 into HKS. (* KS = keyset Node_EqDecision Node_countable Key Ip p ∪ g *)
    rename H4 into Hdomm. (* dom m = dom Cp ∪ g0 *)
    rewrite /op /(cmra_op keyset_ra.KsetRA) /=.
    destruct (decide (dom Cp ∪ {[x]} ⊆ keyset _ _ _ Ip p)).
    destruct (decide (g0 ⊆ g)).
    destruct (decide (keyset _ _ _ Ip p ## g)).
    destruct (decide (dom Cp ∪ {[x]} ## g0)).
    assert (dom Cp ∪ g0 ∪ {[x]} = dom Cp ∪ {[x]} ∪ g0) as <-. set_solver.
    rewrite HKS - Hdomm.
    assert (dom (<[x:=v]> m) = dom m ∪ {[x]}) as Hinsert.
    { rewrite dom_insert_L. set_solver. }
    rewrite Hinsert; done.
    exfalso; apply n; set_solver.
    exfalso; apply n; set_solver.
    exfalso; apply n; set_solver.
    exfalso; apply n; set_solver.
    exfalso; apply n; set_solver.
    exfalso; apply n; set_solver.
    exfalso; apply n; set_solver.
    exfalso; apply n; set_solver.
    rewrite /op /(cmra_op keyset_ra.KsetRA) /= in Hprd.
    inversion Hprd; subst.
    rewrite /op /(cmra_op keyset_ra.KsetRA) /= in Hprd.
    inversion Hprd; subst.
    rewrite dom_insert_L.
    assert ({[x]} ∪ dom m = dom m ∪ {[x]}) as ->. clear. set_solver. auto.
    rewrite /opM /=.
    inversion Hprd; subst.
    rewrite dom_insert_L.
    assert ({[x]} ∪ dom m = dom m ∪ {[x]}) as ->. clear. set_solver. auto.
 Qed.

  Lemma key_new_node_fresh γ_k p x (C Cp : gmap Key KValue) Ip (Hx_not_in_domC: x ∉ dom Cp):
    ⌜x ∈ keyset _ _ _ Ip p ∧ x ∈ KS⌝ ∧ own γ_k (● prod (KS, dom C) : keyset_authR Key) ∗
    own γ_k (◯ prod (keyset _ _ _ Ip p, dom Cp) : keyset_authR Key) ⊢ ⌜x ∉ dom C⌝.
  Proof.
    iIntros "(%Hc & Ha & Hf)".
    iDestruct (own_valid_2 γ_k (● prod (KS, dom C) : keyset_authR _)
                with "[$] [$]") as %Hown%auth_both_valid_discrete.
    destruct Hown as (Io & Ha).
    iDestruct (own_valid γ_k (◯ prod (keyset _ _ _ Ip p, dom Cp) : keyset_authR _)
                with "[$]") as %Hf.
    rewrite auth_frag_valid in Hf.
    pose proof (auth_ks_included (keyset _ _ _ Ip p) KS (dom Cp) (dom C)) as Hkey.
    specialize (Hkey Hf Ha Io).
    destruct Hkey as [Hkey1 | Hkey2].
    - destruct Hkey1 as (? & Hdom). rewrite Hdom in Hx_not_in_domC; try done.
    - destruct Hkey2 as (a & b & HKS & HdomC & Hkeyset & HdomCp_disj &
                           HdomCp_subset &HdomC_subset & Hsubset).
      destruct Hc as (Hx_in_key & Hx_in_KS).
      assert (x ∉ b) as Hx_notin_b.
      { rewrite elem_of_disjoint in Hkeyset.
        specialize (Hkeyset x Hx_in_key).
        intros Hcontra.
        apply Hkeyset. clear Hkeyset. clear -Hsubset Hcontra. set_solver. }
      clear -Hx_notin_b HdomC Hx_not_in_domC. iPureIntro. set_solver.
   Qed.

  Lemma ghost_insert_keyset γ_k p x v (C Cp : gmap Key KValue) Ip
    (Hx_not_in_domC: x ∉ dom Cp):
    ⌜x ∈ keyset _ _ _ Ip p ∧ x ∈ KS⌝ ∧
    own γ_k (● prod (KS, dom C) : keyset_authR Key) ∗
      own γ_k (◯ prod (keyset _ _ _ Ip p, dom Cp) : keyset_authR Key)
    ==∗ own γ_k (● prod (KS, dom (<[x:=v]> C)): keyset_authR Key) ∗
        own γ_k (◯ prod (keyset _ _ _ Ip p, dom Cp ∪ {[x]}): keyset_authR Key).
  Proof.
    iIntros "(%Hc & Ha & Hf)".
    iDestruct (own_valid_2 γ_k (● prod (KS, dom C) : keyset_authR _)
                  with "[$Ha] [$Hf]") as "%Hown".
    rewrite auth_both_valid_discrete in Hown.
    destruct Hown as [Io I_incl].
    iDestruct (own_valid _ (● prod (KS, dom C) : keyset_authR _) with "Ha") as %Ha.
    iDestruct (own_valid _ (◯ prod (keyset _ _ _ Ip p, dom Cp) : keyset_authR _)
                with "Hf") as %Hf.
    iMod (own_update_2 γ_k
            (● prod (KS, dom C) : keyset_authR _) (◯ prod (keyset _ _ _ Ip p, dom Cp))
            (● prod (KS, dom (<[x:=v]> C)) ⋅ ◯ prod (keyset _ _ _ Ip p, dom Cp ∪ {[x]}))
           with "[$Ha] [$Hf]") as "(Ha & Hf)"; try done; try by iFrame.
    { destruct Hc as (? & ?).
      apply auth_update, auth_ks_local_update; try done.
      repeat split; try done.
      eapply cmra_valid_included; try done.
    }
  Qed.

  Lemma update_singleton {A : Type} (Cp : gmap Z A) (x : Z) (v : A) :
    dom Cp = {[x]} -> <[x := v]> Cp = {[x := v]}.
  Proof.
    intros Hdom.
    apply map_eq.
    intros y.
    destruct (decide (y = x)) as [Heq|Hneq]; subst; try by rewrite ! lookup_insert.
    apply dom_singleton_inv_L in Hdom.
    destruct Hdom as (? & ->).
    by rewrite ! lookup_insert_ne.
  Qed.

  Lemma ghost_insert_map_exist γ_m x v (C Cp : gmap Key KValue) (Hx_domCp: x ∈ dom Cp):
    own γ_m (● (Excl <$> C) : keymap_authR _ _) ∗ own γ_m (◯ (Excl <$> Cp) : keymap_authR _ _)
    ==∗ ⌜x ∈ dom C⌝ ∧ own γ_m (● (Excl <$> (<[x := v]> C)) : keymap_authR _ _) ∗
        own γ_m (◯ (Excl <$> (<[x := v]> Cp)) : keymap_authR _ _).
  Proof.
    iIntros "(Ha & Hf)".
    iDestruct (own_valid_2 γ_m (●(Excl <$> C) : keymap_authR _ _)
                         (◯ (Excl <$> Cp)) with "[$Ha] [$Hf]") as %Hownr.
    move: Hownr => /auth_both_valid_discrete [Hsub Hv].
    rewrite lookup_included in Hsub.
    specialize (Hsub x).
    rewrite ! lookup_fmap in Hsub.
    assert (exists y, Cp !! x = Some y) as (x0 & HSome_Cp).
    { by rewrite elem_of_dom /is_Some in Hx_domCp. }
    rewrite HSome_Cp in Hsub.
    pose proof Hsub as Hsub'.
    assert (exists y, C !! x = Some y) as (y0 & HSome_C).
    { destruct (C !! x) eqn: Heq.
      { eexists ; eauto. }
      move: Hsub => /option_included [|Hsub]; try done.
      destruct Hsub as (a & b & HEx1 & HEx2 & ?); try done.
    }
    assert (x ∈ dom C) as Hdomx_C.
    { rewrite elem_of_dom /is_Some. eexists; eauto. }
    iMod (own_update_2 _ (● (Excl <$> C) : keymap_authR _ _) (◯ (Excl <$> Cp))
          (● (Excl <$> (<[x:=v]> C)) ⋅ ◯ (Excl <$> (<[x := v]>Cp))) with "[$Ha] [$Hf]")
      as "(Ha & Hf)"; try done; try by iFrame.
    apply auth_update; rewrite !fmap_insert; eapply insert_local_update; try rewrite lookup_fmap;
    [ rewrite HSome_C; eauto | rewrite HSome_Cp; eauto | apply exclusive_local_update; done ].
  Qed.

  Lemma ghost_insert_map γ_m p x v (C Cp : gmap Key KValue) Ip
    (Hx_not_domCp: x ∉ dom Cp) (Hx_not_domC: x ∉ dom C):
    ⌜x ∈ keyset _ _ _ Ip p ∧ x ∈ KS⌝ ∧
     own γ_m (● (Excl <$> C) : keymap_authR _ _) ∗ own γ_m (◯ (Excl <$> Cp) : keymap_authR _ _)
      ==∗ own γ_m (● (Excl <$> (<[x:=v]> C)) : keymap_authR _ _) ∗
          own γ_m (◯ (Excl <$> (<[x := v]>Cp)) : keymap_authR _ _).
  Proof.
    iIntros "(%Hc & Ha & Hf)".
    iDestruct (own_valid_2 _ (● (Excl <$> C) : keymap_authR _ _)
                with "[$][$]") as %Hown%auth_both_valid_discrete.
    destruct Hown as (Io & I_incl).
    iDestruct (own_valid _ (● (Excl <$> C) : keymap_authR _ _) with "[$]") as %Ha.
    iDestruct (own_valid _ (◯ (Excl <$> Cp) : keymap_authR _ _) with "[$]") as %Hf.
    rewrite auth_frag_valid in Hf.
    assert (map_disjoint C {[x := v]}) as Hdisj_C.
    { apply map_disjoint_dom_2. clear -Hx_not_domC. set_solver. }
    assert (map_disjoint Cp {[x := v]}) as Hdisj_Cp.
    { apply map_disjoint_dom_2. clear -Hx_not_domCp. set_solver. }
    iMod (own_update_2 _ (● (Excl <$> C) : keymap_authR _ _) (◯ (Excl <$> Cp))
            (● (Excl <$> (<[x:=v]> C)) ⋅ ◯ (Excl <$> (<[x := v]>Cp)))
           with "[$Ha] [$Hf]") as "(Ha & Hf)"; try done; try by iFrame.
    { destruct Hc as (? & ?).
      apply auth_update, local_update_discrete.
      intros z _ H_agree.
      assert (Excl <$> C !! x = None /\ Excl <$> Cp !! x = None) as (HNone_C & HNone_Cp).
      { split; apply fmap_None; auto;
        [eapply map_disjoint_Some_r in Hdisj_C | eapply map_disjoint_Some_r in Hdisj_Cp]; eauto;
          by rewrite lookup_insert.
      }
      split.
      + intros i.
        specialize (I_incl i).
        destruct (decide (i = x)); subst.
        { rewrite lookup_fmap in I_incl. by rewrite lookup_fmap lookup_insert. }
        { rewrite !lookup_fmap in I_incl. by rewrite !lookup_fmap lookup_insert_ne. }
      + rewrite /opM in H_agree.
        destruct z; last first.
        rewrite !fmap_insert H_agree; auto.
        { rewrite /opM !fmap_insert H_agree.
          intros i.
          destruct (decide (x = i)); subst.
          { rewrite ! lookup_insert lookup_op lookup_insert.
            destruct (c !! i) eqn: E; last first; try by rewrite E.
            { specialize (H_agree i).
              rewrite lookup_op ! lookup_fmap HNone_Cp HNone_C E in H_agree.
              inversion H_agree.
            }
          }
          { rewrite !lookup_insert_ne; auto.
            rewrite !lookup_op !lookup_fmap lookup_insert_ne; auto.
            rewrite !lookup_fmap; auto.
          }
       }
  }
  Qed.

  Lemma ghost_insert_keyset_add_node γ_k γ_m p new x v (C Cp : gmap Key KValue) Ip I_new I0
    (Hx_not_domCp: x ∉ dom Cp) (Hx_not_domC: x ∉ dom C):
    ⌜{[x]} ⊆ keyset _ _ _ I_new new /\ dom Cp ⊆ keyset _ _ _ I0 p /\ 
      x ∈ keyset _ _ _ Ip p ∧ x ∈ KS ∧
     keyset _ _ _ I0 p ∪ keyset _ _ _ I_new new = keyset _ _ _ Ip p ∧
     keyset _ _ _ I0 p ## keyset _ _ _ I_new new⌝ ∧
    own γ_k (● prod (KS, dom C) : keyset_authR Key) ∗
      own γ_k (◯ prod (keyset _ _ _ Ip p, dom Cp) : keyset_authR Key) ∗
      own γ_m (● (Excl <$> C) : keymap_authR _ _) ∗
      own γ_m (◯ (Excl <$> Cp) : keymap_authR _ _)
    ==∗ own γ_k (● prod (KS, dom (<[x:=v]> C)): keyset_authR Key) ∗
        own γ_k (◯ prod (keyset _ _ _ I0 p, dom Cp) : keyset_authR Key) ∗
        own γ_k (◯ prod (keyset _ _ _ I_new new, {[x]}): keyset_authR Key) ∗
        own γ_m (● (Excl <$> (<[x:=v]> C)) : keymap_authR _ _) ∗
        own γ_m (◯ (Excl <$> Cp) : keymap_authR _ _) ∗
        own γ_m (◯ (Excl <$> {[x := v]}) : keymap_authR _ _).
  Proof.
    iIntros "(%Hc & Ha & Hf & Ha1 & Hf1)".
    destruct Hc as (? & ? & ? & ? & Hks & ?).
    iDestruct (own_valid_2 γ_k (● prod (KS, dom C) : keyset_authR _)
                  with "[$] [$]") as %Hown%auth_both_valid_discrete.
    destruct Hown as (Io & I_incl).
    iDestruct (own_valid_2 γ_m (● (Excl <$> C) : keymap_authR _ _)
                with "[$] [$]") as %Hown1%auth_both_valid_discrete.
    destruct Hown1 as (Io1 & I_incl1).
    iDestruct (own_valid γ_k (● prod (KS, dom C) : keyset_authR _) with "[$]") as %Hown_a.
    iDestruct (own_valid γ_k (◯ prod (keyset _ _ _ Ip p, dom Cp) : keyset_authR _)
                 with "[$]") as %Hown_f.
    iDestruct (own_valid γ_m (● (Excl <$> C) : keymap_authR _ _)
                 with "[$]") as %Hown_a1.
    iMod (ghost_insert_keyset _ _ x v C Cp Ip with "[$Ha $Hf]") as "(Ha & Hf)"; try done.
    iMod (ghost_insert_map _ _ x v C Cp Ip with "[$Ha1 $Hf1]") as "(Ha1 & Hf1)"; try done.
    rewrite - Hks.
    iFrame "Ha ∗".
    assert (prod (keyset _ _ _ I0 p, dom Cp) ⋅ prod (keyset _ _ _ I_new new, {[x]}) =
            prod (keyset _ _ _ I0 p ∪ keyset _ _ _ I_new new, dom Cp ∪ {[x]})) as Hprd.
    { rewrite /op /prodOp. repeat case_decide; try done.
      exfalso. apply H8. clear -Hx_not_domCp. set_solver. }
    assert (map_disjoint Cp {[x := v]}) as Hdisj_Cp.
    { apply map_disjoint_dom_2. clear -Hx_not_domCp. set_solver. }
    assert ((Excl <$> Cp) ⋅ (Excl <$> {[x := v]}) = Excl <$> <[x := v]>Cp) as Hprd1.
    { rewrite insert_union_singleton_r; auto.
      2: { by eapply map_disjoint_singleton_r. }
      rewrite map_fmap_union gmap_op_union; auto.
      rewrite map_disjoint_fmap; auto.
    }
    assert (◯ (prod (keyset _ _ _ I0 p, dom Cp) ⋅ prod (keyset _ _ _ I_new new, {[x]})) =
            ◯ prod (keyset _ _ _ I0 p ∪ keyset _ _ _ I_new new, dom Cp ∪ {[x]}))
                   as Hauth; try by rewrite Hprd.
    rewrite - Hprd1 -Hauth.
    iDestruct "Hf" as "(? & ?)".
    iDestruct "Hf1" as "(? & ?)".
    by iFrame.
  Qed.

  Lemma ghost_insert_keyset_add_node_between γ_k γ_m p new x v
    (C Cp: gmap Key KValue) Ip I_new I0
    (Hx_not_domCp: x ∉ dom Cp) (Hx_not_domC: x ∉ dom C):
    ⌜{[x]} ⊆ keyset _ _ _ I0 p /\ dom Cp ⊆ keyset _ _ _ I_new new /\ x ∈ keyset _ _ _ Ip p ∧
      x ∈ KS ∧ keyset _ _ _ I0 p ∪ keyset _ _ _ I_new new = keyset _ _ _ Ip p  ∧
     keyset _ _ _ I0 p ## keyset _ _ _ I_new new ⌝ ∧
    own γ_k (● prod (KS, dom C) : keyset_authR Key) ∗
      own γ_k (◯ prod (keyset _ _ _ Ip p, dom Cp) : keyset_authR Key) ∗
      own γ_m (● (Excl <$> C) : keymap_authR _ _) ∗
      own γ_m (◯ (Excl <$> Cp) : keymap_authR _ _)
    ==∗ own γ_k (● prod (KS, dom (<[x:=v]> C)): keyset_authR Key) ∗
        own γ_k (◯ prod (keyset _ _ _ I0 p, {[x]}) : keyset_authR Key) ∗
        own γ_k (◯ prod (keyset _ _ _ I_new new, dom Cp): keyset_authR Key) ∗
        own γ_m (● (Excl <$> (<[x:=v]> C)) : keymap_authR _ _) ∗
        own γ_m (◯ (Excl <$> Cp) : keymap_authR _ _) ∗
        own γ_m (◯ (Excl <$> {[x := v]}) : keymap_authR _ _).
  Proof.
    iIntros "(%Hc & (Ha & Hf & Ha1 & Hf1))".
    destruct Hc as (? & ? & ? & ? & Hks & ?).
    iDestruct (own_valid_2 γ_k (● prod (KS, dom C) : keyset_authR _)
                with "[$] [$]") as %Hown%auth_both_valid_discrete.
    destruct Hown as (Io & I_incl).
    iDestruct (own_valid_2 γ_m (● (Excl <$> C) : keymap_authR _ _)
                with "[$] [$]") as %Hown1%auth_both_valid_discrete.
    destruct Hown1 as (Io1 & I_incl1).
    iDestruct (own_valid γ_k (● prod (KS, dom C) : keyset_authR _) with "[$]") as %Hown_a.
    iDestruct (own_valid γ_k (◯ prod (keyset _ _ _ Ip p, dom Cp) : keyset_authR _)
                 with "[$]") as %Hown_f.
    iDestruct (own_valid γ_m (● (Excl <$> C) : keymap_authR _ _)
                 with "[$]") as %Hown_a1.
    iMod (ghost_insert_keyset γ_k p x v C Cp Ip with "[$Ha $Hf]") as "(Ha & Hf)"; auto.
    iMod (ghost_insert_map γ_m p x v C Cp Ip with "[$Ha1 $Hf1]") as "(Ha1 & Hf1)"; auto.
    rewrite - Hks.
    iFrame "Ha ∗".
    assert (prod (keyset _ _ _ I0 p, {[x]}) ⋅ prod (keyset _ _ _ I_new new, dom Cp ) =
            prod (keyset _ _ _ I0 p ∪ keyset _ _ _ I_new new, dom Cp ∪ {[x]})) as Hprd.
    { rewrite /op /prodOp. repeat case_decide; try done.
      rewrite (union_comm_L (dom Cp) {[x]}); auto.
      exfalso. apply H8. clear -Hx_not_domCp. set_solver.
    }
    assert (map_disjoint Cp {[x := v]}) as Hdisj_Cp.
    { apply map_disjoint_dom_2. clear -Hx_not_domCp. set_solver. }
    assert ((Excl <$> Cp) ⋅ (Excl <$> {[x := v]}) = Excl <$> <[x := v]>Cp) as Hprd1.
    { rewrite insert_union_singleton_r; auto.
      2: { eapply map_disjoint_singleton_r; eauto. }
      rewrite map_fmap_union gmap_op_union; auto.
      rewrite map_disjoint_fmap; auto.
    }
    assert (◯ (prod (keyset _ _ _ I0 p, {[x]}) ⋅ prod (keyset _ _ _ I_new new, dom Cp)) =
              ◯ prod (keyset _ _ _ I0 p ∪ keyset _ _ _ I_new new, dom Cp ∪ ({[x]} : gset Key)))
      as Hauth; try by rewrite Hprd.
    rewrite - Hprd1 -Hauth.
    iDestruct "Hf" as "(? & ?)".
    iDestruct "Hf1" as "(? & ?)".
    by iFrame.
  Qed.

  
  
  Lemma update_flows_nullval
    I Ip I0 I_new new_node (Hneq_new_null : new_node <> nullval):
    Ip = I -> ✓ Ip -> ✓ (I0 ⋅ I_new) -> dom Ip = {[nullval]} -> dom I_new = {[new_node]} ->
    ● I ⋅ ◯ Ip ~~> (● (I0 ⋅ I_new) ⋅ ◯ (I0 ⋅ I_new)).
  Proof.
    intros HIIp HIvalid HVI0Inew HI0 HI_new.
    pose proof HIvalid as HIvalid'.
    apply intValid_unfold in HIvalid.
    destruct HIvalid as (? & ? & ?).
    apply cmra_discrete_total_update.
    intros z Hv.
    pose proof Hv as Hincl.
    apply cmra_valid_op_l in Hincl.
    assert (● Ip ⋅ ◯ Ip =  View (Some (DfracOwn 1%Qp, to_agree Ip )) Ip) as Hdest.
    { unfold op at 1, ora_op. simpl.
      rewrite /view_op_instance /=.
      assert (ε ⋅ Ip = Ip) as HIp.
      { apply (ucmra_unit_left_id Ip). }
      by rewrite HIp.
    }
    rewrite -HIIp in Hincl.
    rewrite Hdest in Hincl.
    destruct z as [auth_z frag_z] eqn: Hz.
    destruct auth_z as [ [q Iq] | ] eqn: Hauth_q.
    - exfalso.
      repeat (destruct Hv).
      rename H3 into HDfracOwn.
      rewrite /valid /cmra_valid /= /frac_valid_instance /= in HDfracOwn.
      by apply dfrac_full_exclusive in HDfracOwn.
    - rename frag_z into Iz'.
      unfold op at 1 in Hv.
      rewrite /cmra_op /view_op_instance /= /ora_op /= /view_op_instance /= in Hv.
      unfold op at 1 in Hv.
      rewrite /cmra_op /= in Hv.
      assert (ε ⋅ Ip = Ip) as HIp; try (apply (ucmra_unit_left_id Ip); done).
      rewrite HIp in Hv.
      assert (View (Some (DfracOwn 1, to_agree Ip)) (Ip ⋅ Iz') = ● Ip ⋅ ◯ (Ip ⋅ Iz')) as H'.
      { rewrite /op /= /ora_op /= /view_op_instance /=.
        assert (ε ⋅ intComp Ip Iz' = intComp Ip Iz') as H'.
        { by rewrite left_id. }
        by rewrite H'. }
      rewrite -HIIp in Hv.
      rewrite H' in Hv.
      apply (auth_both_valid_discrete Ip (Ip ⋅ Iz')) in Hv.
      destruct Hv as [Hcompz HI1].
      destruct Hcompz as [Iy Hcompz].
      clear H'.
      assert (I_empty = Iz' ⋅ Iy) as Hozy.
      { apply (@intComp_cancelable _ _ _ _ Ip).
        rewrite intComp_unit; done.
        by rewrite intComp_unit cmra_assoc. }
      repeat split; try done.
      intros n.
      exists (I0 ⋅ I_new).
      split; try done.
      rewrite /view_frag_proj /= /auth_view_rel_raw.
      split; try done.
      exists Iy.
      rewrite -cmra_assoc -Hozy ! cmra_assoc.
      assert (ε ⋅ I0 = I0) as Hϵ.
      { apply (ucmra_unit_left_id I0). }
      by rewrite Hϵ intComp_unit.
  Qed.

  (* update interface for the case of p = nullval *)
  Lemma ghost_update_interface_nullval γ_I γ_f r I Ip I0 I_new new_node new lock md
    (Hpt: is_pointer_or_null new /\ is_pointer_or_null lock /\ is_pointer_or_null new_node)
    (Hlen: (0 ≤ f nullval < Zlength md)%Z /\ (0 ≤ f new_node < Zlength md)%Z):
    ⌜new_node ∉ dom I /\ globalinv _ _ _ r I /\ I ≡ Ip /\ ✓ Ip /\ ✓ (I0 ⋅ I_new) /\
      out_map I0 = ∅ /\ out_map I_new = ∅ /\ dom Ip = {[nullval]} /\ dom I0 = {[nullval]} /\
      dom I_new = {[new_node]} /\ dom (inf I_new new_node) = KS⌝ ∧
      own γ_I (● I) ∗ own γ_I (◯ (Ip)) ∗ own_nodes γ_f I md
      ==∗ ∃ I' md', ⌜globalinv _ _ _ new_node I' /\ dom I' = dom I ∪ {[new_node]} ∧
                      dom I' ∖ {[new_node]} = dom I /\ md' = (upd_Znth (f new_node) md new)⌝ ∧
                      own γ_I (● I') ∗ own γ_I (◯ (I0)) ∗ own γ_I (◯ (I_new)) ∗
                        own_nodes γ_f I' md' ∗ inFP γ_f new_node new lock.
  Proof.
    iIntros "(%HH & HI & HIp & Hown)".
    iPoseProof (own_valid_2 with "[$HI] [$HIp]") as "%Hv".
    apply auth_both_valid_discrete in Hv.
    destruct Hv as [[Iz Ipn_incl_I] Valid_I].
    destruct HH as (H_neq_new & Hglob & HIIp & VI & VI0I_new &
                     HoutI0 & HoutI_new & HdomIp & HdomI0 & HdomI_new & HKS).
    rewrite HIIp in Ipn_incl_I.
    destruct Hglob as (_ & Hgroot & Hgout & Hgin).
    iMod (own_update_2 γ_I (● I) (◯ Ip) (● (I0 ⋅ I_new) ⋅ ◯ (I0 ⋅ I_new))
           with "[$HI] [$HIp]") as "(Ha & Hf)"; try done.
    { eapply (update_flows_nullval _ _ _ _ new_node); eauto. set_solver. } 
    assert (dom (I0 ⋅ I_new) = dom I0 ∪ {[new_node]}) as domIp_Inew.
    { rewrite intComp_dom; try done. set_solver. }
    set I' := (I0 ⋅ I_new).
    assert (globalinv _ _ _ new_node I') as Hglob_I.
    { rewrite /globalinv.
      repeat (split; auto).
      - rewrite /I'. rewrite domIp_Inew. clear. set_solver.
      - rewrite /closed /outset /out.
        intros k n.
        rewrite /closed /outset /out in Hgout.
        assert (✓ I') as HVI'.
        { by rewrite /I'. }
        apply flowint_valid_unfold in HVI'.
        destruct HVI' as [Ir' (I'_def & I'_disj & _)].
        destruct (decide (n ∈ dom I')) as [Hin | Hnin].
        * assert (out_map I' !!! n = 0%CCM) as HoutI'.
          { rewrite /out_map I'_def.
            assert (¬ (n ∈ dom (out_map I'))) as Hnot.
            { rewrite I'_def /=.
              rewrite /= in I'_disj.
              rewrite I'_def in Hin.
              clear -I'_disj Hin. set_solver.
            }
            rewrite I'_def nzmap_elem_of_dom_total /= in Hnot.
            by apply dec_stable in Hnot.
          }
          rewrite HoutI'. clear. set_solver.
        * rewrite /I' in Hnin.
          apply intComp_unfold_out in Hnin; auto.
          rewrite /out in Hnin.
          rewrite /I' Hnin HoutI0 HoutI_new nzmap_lookup_empty ccm_right_id. clear. set_solver.
      - intros.
        specialize (Hgin k H0).
        rewrite /I' /inset intComp_inf_2; auto; last first. rewrite HdomI_new. clear. set_solver.
        rewrite /out HoutI0 nzmap_lookup_empty ccm_pinv_unit HKS; auto.
    }
    iDestruct "Hown" as (N1) "(%Hc & Hown)".
    destruct Hc as (Hdom & Hc).
    iMod (own_update γ_f (● (to_agree <$> N1) : gmap_authR Node _)
           (● (to_agree <$> <[ new_node := (new, lock)]> N1) ⋅
            ◯ (to_agree <$> <[ new_node := (new, lock)]> ∅)) with "[$Hown]") as "(Hown & Hown')".
     { rewrite ! fmap_insert.
       apply auth_update_alloc, alloc_local_update; try done.
       rewrite -Hdom in H_neq_new; auto.
       rewrite lookup_fmap fmap_None not_elem_of_dom_1; auto.
    }
    iModIntro.
    iExists I', (upd_Znth (f new_node) md new).
    iSplit.
    { iPureIntro. do 2 (split; auto).
      rewrite /I' domIp_Inew. rewrite HdomI0 HIIp HdomIp. clear. set_solver.
      split. rewrite /I' domIp_Inew HIIp HdomIp HdomI0. set_solver. done.
    }
    rewrite auth_frag_op.
    iDestruct "Hf" as "(HI0 & HI_new)".
    iFrame "Ha ∗".
    iSplitL; last first; iPureIntro; try split; auto; try by rewrite lookup_insert.
    do 1 (split; auto).
    { rewrite /I' domIp_Inew HdomI0 dom_insert_L Hdom HIIp HdomIp; clear; set_solver. }
    intros ? ? ? Hnew.
    destruct Hpt as (? & ? & ?).
    destruct Hlen as (? & ?).
    destruct (decide (new_node = n)); subst.
    + rewrite lookup_insert in Hnew.
      inversion Hnew; subst.
      do 4 (split; auto). 
      rewrite upd_Znth_same; auto.
      rewrite Zlength_upd_Znth; auto.
    + rewrite lookup_insert_ne in Hnew; auto.
      rewrite upd_Znth_diff'; auto.
      apply Hc in Hnew.
      destruct Hnew as (? & ? & ? & ? & ?).
      do 4 (split; auto).
      rewrite Zlength_upd_Znth; auto.
      by intros Hcontra; apply f_injective in Hcontra.
  Qed.

  (* update interface for the case of p <> nullval *)
  Lemma ghost_update_interface γ_I γ_f r I Ip I0 I_new p new_node new lock md
    (Hpt: is_pointer_or_null new /\ is_pointer_or_null lock /\ is_pointer_or_null new_node)
    (Hlen: (0 ≤ f p < Zlength md)%Z /\ (0 ≤ f new_node < Zlength md)%Z):
   ⌜new_node ∉ dom I /\ globalinv _ _ _ r I /\ contextualLeq _ Ip (I0 ⋅ I_new) /\
     inf (I0 ⋅ I_new) new_node = 0%CCM /\ dom Ip = {[p]} /\ dom I0 = {[p]} /\
     dom I_new = {[new_node]}⌝ ∧ own γ_I (● I) ∗ own γ_I (◯ (Ip)) ∗ own_nodes γ_f I md
   ==∗ ∃ I' md',
         ⌜contextualLeq _ I I' /\ globalinv _ _ _ r I' /\ dom I' = dom I ∪ {[new_node]} ∧
           dom I' ∖ {[new_node]} = dom I /\ md' = (upd_Znth (f new_node) md new) /\
           p ∈ dom I⌝ ∧
               own γ_I (● I') ∗ own γ_I (◯ I0) ∗ own γ_I (◯ I_new) ∗ own_nodes γ_f I' md' ∗
                 inFP γ_f new_node new lock.
  Proof.
    iIntros "(%HH & HI & HIp & Hown)".
    iPoseProof (own_valid_2 with "[$HI] [$HIp]") as "%Hv".
    apply auth_both_valid_discrete in Hv.
    destruct Hv as [[Iz Ipn_incl_I] Valid_I].
    destruct HH as (H_neq_new & Hglob & HcontLeq & Hinf & HdomIp & HdomI0 & HdomI_new).
    destruct HcontLeq as (Valid_Ipn & Valid_Ipnm & Hsub & Hinf_pn & Hout).
    assert (dom (I0 ⋅ I_new) = dom I0 ∪ dom I_new) as Dom_eq.
    { by apply intComp_dom. }
    rewrite HdomI0 HdomI_new in Dom_eq.
    assert (new_node ∉ dom Iz) as H_neq_new_Iz.
    { rewrite Ipn_incl_I intComp_dom in H_neq_new; auto; last first.
      by rewrite - Ipn_incl_I.
      clear -H_neq_new. set_solver.
    }
    destruct Hglob as (_ & Hgroot & Hgout & Hgin).
    assert (out Iz new_node = 0%CCM) as out_Iz_zero.
    { apply (intComp_out_zero Ip Iz new_node); rewrite -Ipn_incl_I; auto.
      apply nzmap_eq; intros km.
      pose proof (Hgout km new_node) as km_out.
      rewrite /outset nzmap_elem_of_dom_total in km_out.
      apply dec_stable in km_out.
      by rewrite km_out nzmap_lookup_empty.
    }
    iMod (own_updateP (flowint_update_P _ I Ip (I0 ⋅ I_new)) γ_I (● I ⋅ ◯ Ip)
           with "[HI HIp]") as (Io) "H0".
    { rewrite Ipn_incl_I.
      apply (flowint_update K_multiset (Iz) (Ip) (I0 ⋅ I_new)).
      - repeat (split; auto).
      - pose proof Valid_I as Valid_I'.
        rewrite Ipn_incl_I in Valid_I'.
        apply intComposable_valid in Valid_I'.
        rewrite /intComposable in Valid_I'.
        destruct Valid_I' as (? & ? & ? & ?).
        assert (dom Ip ## dom Iz) as Hdisj; auto.
        rewrite Dom_eq. set_solver.
      - intros n Hn.
        assert (n = new_node) as ->; auto.
        { rewrite Dom_eq HdomIp in Hn. clear -Hn. set_solver. }
    }
    try repeat rewrite own_op; iFrame.
    iPoseProof ((flowint_update_result γ_I I Ip (I0 ⋅ I_new))
                 with "[$H0]") as (I'') "(%ContLeq_I & HIIpnm)".
    destruct ContLeq_I as (ContLeq_I & HfI0).
    destruct HfI0 as (I0' & I_eq & I''_eq).
    assert (I0' = Iz) as H_eq_I0'_Iz.
    { rewrite Ipn_incl_I in I_eq.
      apply intComp_cancelable in I_eq; try done. by rewrite - Ipn_incl_I. }
    subst I0'.
    assert (dom I'' = dom I ∪ {[new_node]}) as domm_I''.
    { assert (dom I'' = {[p]} ∪ {[new_node]} ∪ dom Iz) as Dom_I''.
      { rewrite I''_eq ! intComp_dom; auto. set_solver.
        apply leibniz_equiv_iff in I''_eq.
        rewrite -I''_eq.
        rewrite /contextualLeq in ContLeq_I.
        by destruct ContLeq_I as (? & ? & ?). }
      rewrite Dom_I'' I_eq ! intComp_dom; auto.
      2 : { by rewrite -I_eq. }
      set_solver. }
    assert (globalinv _ _ _ r I'') as Hglob_I''.
    { apply (contextualLeq_impl_globalinv I I'').
      all : trivial.
      repeat (split; auto).
      { intros n Hn.
        assert (n = new_node) as ->. { clear -domm_I'' Hn. set_solver. }
        rewrite /inset /inf.
        destruct (inf_map I'' !! new_node) eqn: E; last first; try by rewrite E.
        rewrite E /default /id.
        assert (inf (I0 ⋅ I_new ⋅ Iz) new_node =
                  inf (I0 ⋅ I_new) new_node - out Iz new_node)%CCM as Hinf'.
        { rewrite intComp_inf_1; auto.
          rewrite -I''_eq.
          rewrite /contextualLeq in ContLeq_I.
          by destruct ContLeq_I as (? & ? & ?).
          rewrite Dom_eq. clear. set_solver. }
        rewrite Hinf out_Iz_zero /inf - I''_eq E /= in Hinf'.
        rewrite Hinf'. clear. set_solver. }
    }
    assert (p ∈ dom I).
    { rewrite Ipn_incl_I intComp_dom; auto. clear -HdomIp. set_solver.
      by rewrite - Ipn_incl_I.
    }
    iDestruct "Hown" as (N1) "(%Hc & Hown)".
    destruct Hc as (Hdom & Hc).
    iMod (own_update γ_f (● (to_agree <$> N1) : gmap_authR Node _)
                  (● (to_agree <$> <[ new_node := (new, lock)]> N1) ⋅
                  ◯ (to_agree <$> <[ new_node := (new, lock)]> ∅))
           with "[$Hown]") as "(Hown & Hown')".
    { apply auth_update_alloc.
      rewrite ! fmap_insert.
      apply alloc_local_update; try done.
      rewrite lookup_fmap fmap_None not_elem_of_dom_1; auto.
      rewrite -Hdom in H_neq_new; auto. }
    iModIntro.
    iExists I'', _.
    iSplit.
    { iPureIntro.
      do 4 (split; auto).
      rewrite domm_I''. clear -H_neq_new. set_solver.
    }
    iDestruct "HIIpnm" as "(HI'' & HI0_new)".
    rewrite auth_frag_op.
    iDestruct "HI0_new" as "(HI0 & HI_new)".
    rewrite /inFP.
    iFrame "HI'' ∗".
    iSplitL; last first; try by rewrite lookup_insert.
    - iPureIntro.
      do 2 (split; auto).
      { rewrite dom_insert_L Hdom domm_I''. clear; set_solver. }
      intros ? ? ? Hnew.
      destruct Hlen as (? & ?).
      destruct Hpt as (? & ? & ?).
      destruct (decide (new_node = n)); subst.
      + rewrite lookup_insert in Hnew.
        inversion Hnew; subst.
        do 4 (split; auto). 
        rewrite upd_Znth_same; eauto.
        rewrite Zlength_upd_Znth; auto.
      + rewrite lookup_insert_ne in Hnew; auto.
        rewrite upd_Znth_diff'; auto.
        apply Hc in Hnew.
        destruct Hnew as (? & ? & ? & ? & ?).
        do 4 (split; auto).
        rewrite Zlength_upd_Znth; auto.
        by intros Hcontra; apply f_injective in Hcontra.
  Qed.

  (* Prove Ip = I from dom Ip = dom I *)
  Lemma flowEq γ_I (I Ip: @flowintT (@multiset_flows.K_multiset Key Z.eq_dec Z_countable) _ _ _):
    ⌜dom Ip = dom I /\ dom Ip = {[nullval]} /\ globalinv _ _ _ nullval I⌝ ∧
      own γ_I (● I) ∗ own γ_I (◯ Ip) ⊢ ⌜Ip ≡ I⌝.
  Proof.
    iIntros "(%Hcon & Hown1 & Hown2 )".
    destruct Hcon as (Hdom & HdomIp & Hglob).
    iDestruct (own_valid_2 γ_I (● I) (◯ Ip) with "[$] [$]")
      as %Hown%auth_both_valid_discrete.
    destruct Hown as ((Iz & HI) & Hv).
    rewrite HI in Hv.
    pose proof Hv as Hv1.
    pose proof Hv as Hv2.
    apply intComp_dom_disjoint in Hv1.
    apply intComp_dom in Hv2.
    rewrite HI in Hdom.
    assert (dom Iz ≡ ∅) as HdomIz. set_solver.
    apply intComp_valid_proj2 in Hv.
    pose proof (intEmp_unique Iz) as HintE.
    specialize (HintE Hv HdomIz).
    rewrite HintE in HI.
    assert (I ≡ Ip ⋅ I_empty) as ->. set_solver.
    by rewrite intComp_unit.
  Qed.

  Lemma exists_union {A} {B} `{Countable A} `{Countable B} k (P : A -> gset B) (S : gset A):
  (k ∈ [^union set] x ∈ S, P x) -> exists x, x ∈ S /\ k ∈ P x.
  Proof.
    intros Hk.
    induction S as [|x S Hx IH] using set_ind_L.
    - rewrite big_opS_empty /= in Hk; try done.
    - rewrite (big_opS_delete _ _ x) in Hk; last first.
      clear. set_solver.
      assert (({[x]} ∪ S) ∖ {[x]} = S) as HS.
      clear -Hx. set_solver.
      rewrite HS in Hk.
      apply elem_of_union in Hk.
      destruct Hk as [Hk | Hk].
      + eexists; esplit; eauto. clear. set_solver.
      + apply IH in Hk.
        destruct Hk as (? & (Hx0 & Hk)).
        eexists; esplit; eauto. clear -Hx0. set_solver.
  Qed.
  
  Lemma outset_in_outsets1 (I : flowint_T) (k : Z) :
    in_outsets _ _ _ k I <-> k ∈ outsets I.
  Proof.
    split.
    - intros Hk.
      rewrite /in_outsets in Hk.
      destruct Hk as (n & Hk).
      rewrite /in_outset in Hk.
      assert (n ∈ dom (out_map I)) as Hn.
      { rewrite nzmap_elem_of_dom.
        destruct (out_map I !! n) eqn: H'; try done.
        rewrite /out in Hk.
        rewrite nzmap_lookup_total_alt in Hk.
        simpl in Hk.
        rewrite H' in Hk. done.
      }
      rewrite /outsets (big_opS_delete _ _ n); try done.
      set_solver.
    - rewrite /in_outsets /outsets /outset /in_outset.
      intros Hk.
      eapply exists_union in Hk.
      destruct Hk as (? & Hk).
      destruct Hk as (? & ?).
      eexists; try done.
  Qed.

  Lemma NoDup_map_injective {A B : Type} (f : A → B) (l : list A) :
    NoDup l → (∀ x y, f x = f y → x = y) → NoDup (map f l).
  Proof.
    induction l as [|x xs IH]; simpl; intros Hnd Hinj.
    - constructor.
    - inversion Hnd as [|? xs' Hnotin Hnd']; subst.
      constructor. set_solver. set_solver.
  Qed.
  
  Lemma NoDup_Z_of_nat_seq (sz : Z) : NoDup (map Z.of_nat (seq 1 (Z.to_nat sz))).
  Proof.
    apply NoDup_map_injective.
    - apply NoDup_seq.
    - intros x y H1. now apply Nat2Z.inj in H1.
  Qed.

  Lemma upto_seq (n : nat) : upto n = map Z.of_nat (seq 0 n).
  Proof.
    induction n as [| n' IH]; simpl.
    - reflexivity.
    - rewrite IH /=.
      assert (forall len start, map S (seq start len) = seq (S start) len).
      { induction len; try done.
        intros; simpl.
        rewrite (IHlen (S start)) //=.
      }
      f_equal.
      rewrite - H0 !map_map.
      f_equal. extensionality x. lia.
  Qed.

  Lemma succ_upto_size (sz : Z) :
    map Z.succ (upto (Z.to_nat sz)) = map Z.of_nat (seq 1 (Z.to_nat sz)).
  Proof.
    rewrite upto_seq -seq_shift !map_map. apply map_ext; intros k. lia.
  Qed.

  Lemma list_to_set_map_seq0_remove_zero (sz : Z) :
    list_to_set (C := gset Z)(map Z.of_nat (seq 0 (Z.to_nat sz))) ∖ {[0%Z]} =
    list_to_set (C := gset Z) (map Z.of_nat (seq 1 (Z.to_nat (sz - 1)))).
  Proof.
    apply set_eq.
    intros.
    rewrite ! elem_of_list_to_set elem_of_list_In in_map_iff.
    split; intros Hx.
    - rewrite elem_of_difference in Hx.
      destruct Hx as (Hin & Hne).
      rewrite elem_of_list_to_set elem_of_list_In in_map_iff in Hin.
      destruct Hin as (y & <- & Hin).
      destruct y.
      + rewrite not_elem_of_singleton in Hne. easy.
      + rewrite not_elem_of_singleton in Hne.
        exists (S y). split; auto.
        rewrite in_seq.
        rewrite in_seq in Hin. lia.
    - rewrite elem_of_difference.
      destruct Hx as (y & <- & Hin).
      rewrite in_seq in Hin.
      destruct y.
      + lia.
      + rewrite ! elem_of_list_to_set elem_of_list_In in_map_iff.
        split.
        { exists (S y). split; auto. rewrite in_seq. lia. }
        rewrite not_elem_of_singleton. lia.
  Qed.

  Definition Zseq (start len: Z) : list Z := map Z.of_nat (seq (Z.to_nat start) (Z.to_nat len)).

  Definition upto_gset (size : Z) : gset Z := list_to_set (Zseq 0 size).

  Lemma In_upto_gset: forall (size i : Z), i ∈ (upto_gset size) <-> (0 <= i < size)%Z.
  Proof.
    intros size i.
    rewrite /upto_gset /Zseq.
    split.
    - intros Hset.
      apply elem_of_list_to_set, elem_of_list_In in Hset.
      apply in_map_iff in Hset as (? & Hx & Hin).
      apply in_seq in Hin. subst. lia.
    - intros Hrng.
      apply elem_of_list_to_set, elem_of_list_In, in_map_iff.
      exists (Z.to_nat i).
      split.
      + rewrite Z2Nat.id; lia.
      + apply in_seq. lia.
  Qed.

  Lemma In_upto_gset_new: forall (size i : Z) (Hne: i <> 0%Z),
      i ∈ upto_gset size ∖ {[0%Z]} <-> (0 < i < size)%Z.
  Proof.
    intros size i Hne.
    split.
    - intros Hset.
      rewrite elem_of_difference in Hset.
      destruct Hset as (Hset & Hnin).
      apply In_upto_gset in Hset. lia.
    - intros Hrng.
      rewrite elem_of_difference.
      split.
      { apply In_upto_gset. lia. }
      set_solver.
  Qed.

End interface_more.

