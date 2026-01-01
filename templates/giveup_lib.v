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
Require Import VST.atomics.verif_lock_atomic.
Require Import tmpl.flows_ora.
Require Import tmpl.keyset_ra_ora.
Require Export tmpl.data_struct.
Require Export tmpl.interface_more.
Require Export tmpl.template_class. (* template class *)
Require Export tmpl.giveup. (* AST of giveup.c *)

Definition t_md_entry := Tstruct _md_entry noattr.

Section give_up.
  #[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
  Definition Vprog : varspecs. mk_varspecs prog. Defined.

  Context `{NR: NodeRep } `{EqDecision K} `{Countable K}.
  Context `{!cinvG Σ, atom_impl : !atomic_int_impl (Tstruct _atom_int noattr), !flowintG Σ,
        !nodesetG Σ, !nodemapG Σ, !keymapG Σ, !keysetG Σ, !inG Σ (excl_authR (leibnizO val)) }.

  (* Define CSS *)

  Record NodeR := { min : Z; max : Z; Cp : gmap Key KValue; Ip : flowint_T; }.
  
  Definition belongs (x : Z) (nr : NodeR) := (min nr < x < max nr)%Z.
  
  Definition is_root (γ_n : gname) (r : val) : mpred := emp.

  Definition md_entry_rep γ_I γ_k γ_m γ_n p1 (p : Node) (nr : NodeR) (css r : val) : mpred :=
    ⌜repable_signed (min nr) ∧ repable_signed (max nr) /\
      is_pointer_or_null p /\ is_pointer_or_null p1 ∧
      (p <> nullval -> (∀ k, ((min nr) < k < (max nr))%Z -> in_inset _ _ _ k (Ip nr) p)) ∧
      dom (Ip nr) = {[p]} /\ forall k, k ∈ dom (Cp nr) -> ((min nr) < k < (max nr))%Z⌝ ∧
      malloc_token Ews t_md_entry p1 ∗
      field_at Ews t_md_entry [StructField _min] (vint (min nr)) p1 ∗
      field_at Ews t_md_entry [StructField _max] (vint (max nr)) p1 ∗
      node p (Ip nr) (Cp nr) ∗ own γ_I (◯ (Ip nr)) ∗
      own γ_k (◯ prod (keyset _ _ _ nr.(Ip) p, dom (Cp nr)): keyset_authR Key) ∗
      own γ_m (◯ (Excl <$> (Cp nr)) : keymap_authR _ _) ∗
      if eq_dec p nullval then
         ⌜is_pointer_or_null r⌝ ∧
         own γ_n (◯E r : excl_authR (leibnizO val)) ∗
           field_at (cs := CompSpecs) Ews t_struct_css [StructField _root] r css else emp.

  Definition ltree γ_I γ_k γ_f γ_m γ_n p1 p css r: mpred :=
    ∃ lsh lock (nr : NodeR),
      ⌜field_compatible t_md_entry nil p1 /\ readable_share lsh /\
        is_pointer_or_null lock⌝ ∧
        field_at lsh t_md_entry [StructField _lock] lock p1 ∗ inFP γ_f p p1 lock ∗
          inv_for_lock lock (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r).

  Definition globalGhost γ_I γ_f γ_k γ_m r (C : gmap Key KValue)
    (I: @flowintT _ K_multiset_ccm _ _) md :=
    ⌜globalinv _ _ _ r I /\ (r = nullval -> dom I = {[nullval]} /\ C = ∅)⌝ ∧
    own γ_I (● I) ∗ own γ_k (● prod (KS, dom C) : keyset_authR Key) ∗
    own γ_m (● (Excl <$> C) : keymap_authR _ _) ∗ own_nodes γ_f I md.

  (* (I: @flowintT _ (@K_multiset_ccm Key _ _ ) _ _) *)

  Definition nodeFull γ_I γ_k γ_f γ_m γ_n (domI : gset Node) (md : list val) css r: mpred :=
    [∗ set] p ∈ domI, ∃ p1 sh,
      ⌜(0 ≤ f p < Zlength md)%Z /\ p1 = (Znth (f p) md) /\
        readable_share sh /\ is_pointer_or_null (Znth (f p) md)⌝ ∧
      field_at sh t_struct_css [ArraySubsc (f p); StructField _metadata] (Znth (f p) md) css ∗
      ltree γ_I γ_k γ_f γ_m γ_n p1 p css r.

  Definition md_slot (i : Z) (css : val) : mpred :=
    (field_at_ Ews t_struct_css [ArraySubsc i; StructField _metadata] css) ∨
      (∃ p, ⌜f p = i⌝ ∧ malloc_token (cs := (@DS_compspecs Σ VSTGS0 NR)) Ews1 t_struct_node p).

  Definition CSSi (γ_I γ_f γ_k γ_g γ_m γ_n : gname) r C css
    (I : @flowintT (@multiset_flows.K_multiset Key Z.eq_dec Z_countable) _ _ _)
    (md : list val): mpred :=
    ⌜Zlength md = size /\ nullval ∈ dom I⌝ ∧ globalGhost γ_I γ_f γ_k γ_m r C I md ∗
    malloc_token Ews t_struct_css css ∗ ([∗ set] i ∈ upto_gset size ∖ {[0%Z]} , md_slot i css) ∗
    nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css r ∗ own γ_n (●E r : excl_authR (leibnizO val)).

  Definition CSS γ_I γ_f γ_k γ_g γ_m γ_n C css : mpred :=
    ∃ (I : @flowintT (@multiset_flows.K_multiset Key Z.eq_dec Z_countable) _ _ _) md r,
      CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I md.

  Lemma get_field_at (p c : val) (Hsz: (0 < @sizeof (@DS_compspecs Σ VSTGS0 NR) t_struct_node)%Z):
    malloc_token (cs := (@DS_compspecs Σ VSTGS0 NR)) Ews1 t_struct_node p ∗
      md_slot (f p) c ⊢ 
      md_slot (f p) c ∗ field_at_ Ews t_struct_css [ArraySubsc (f p); StructField _metadata] c.
  Proof.
    iIntros "H".
    iDestruct "H" as "(H & [H1 | H2])".
    - iFrame "H1". iRight. iExists p.
      iFrame "H". done.
    - iDestruct "H2" as (new) "(% & H2)".
      apply f_injective in H0; subst.
      iPoseProof (malloc_token_conflict (cs := (@DS_compspecs Σ VSTGS0 NR)) Ews1 t_struct_node
                   with "[$]") as "?"; auto.
  Qed.

  Lemma data_at_array_elems: forall sh t n l p,
      data_at sh (tarray t n) l p ⊢
        [∗ list] i ∈ upto (Z.to_nat n), field_at sh (tarray t n) [ArraySubsc i] (Znth i l) p.
  Proof.
    intros.
    rewrite /data_at /field_at /at_offset data_at_rec_eq /=.
    destruct p; try by iIntros "((% & _) & _)".
    rewrite offset_val_zero_Vptr.
    rewrite /array_pred /aggregate_pred.array_pred /unfold_reptype /=.
    replace (0 `max` n)%Z with (Z.of_nat (Z.to_nat n)) by lia.
    remember (Z.to_nat n) as m; revert i; generalize dependent l; generalize dependent n;
      induction m; simpl; intros.
    { iIntros "(_ & _ & $)". }
    rewrite ! Zpos_P_of_succ_nat SuccNat2Pos.id_succ /=.
    rewrite /at_offset Z.add_0_l /=.
    iIntros "(% & %Hlen & $ & H)".
    iSplit.
    { rewrite field_compatible_cons /=; iPureIntro; split; auto; split; auto; lia. }
    rewrite big_sepL_fmap.
    iApply big_sepL_mono; last iApply (IHm (n - 1)%Z ltac:(lia) (tl l) (Ptrofs.add i (Ptrofs.repr (sizeof t)))).
    - intros ?? ?%elem_of_list_lookup_2%elem_of_list_In%In_upto; simpl.
      rewrite !field_compatible_cons /=.
      iIntros "((% & %) & H)"; iSplit.
      { iPureIntro; split; auto; lia. }
      iStopProof; f_equiv.
      + rewrite /Z.succ -Znth_skipn //; lia.
      + f_equal.
        rewrite Ptrofs.add_assoc ptrofs_add_repr; f_equal; f_equal; lia.
    - iSplit.
      { iPureIntro.
        pose proof H0 as Hcompat.
        rewrite (field_compatible_Tarray_split _ 1) in H0; last lia.
        rewrite /field_address0 if_true /= in H0.
        rewrite Z.add_0_l Z.mul_1_r in H0; apply H0.
        { rewrite field_compatible0_cons /=; split; auto; lia. } }
      rewrite Z.sub_0_r.
      iSplit.
      { iPureIntro; destruct l;
          [rewrite -> Zlength_nil in * | rewrite -> Zlength_cons in *]; simpl; try lia.
        apply Z.succ_inj in Hlen; done.
      }
      rewrite Nat2Z.id.
      iApply (aggregate_pred.rangespec_shift_derives with "H").
      intros j i' ??.
      assert (j = i' + 1)%Z by lia; subst.
      rewrite !Z.sub_0_r.
      rewrite /at_offset /=; f_equiv.
      + rewrite /Z.succ -Znth_skipn //; lia.
      + f_equal.
        rewrite Ptrofs.add_assoc ptrofs_add_repr; f_equal; f_equal; lia.
  Qed.

  Lemma css_array_to_nested_field new css (sz : Z)
    (Hc : isptr (field_address t_struct_css (DOT _metadata) css))
    (Hlen: (0 ≤ 0 < Zlength (Zrepeat Vundef sz))%Z):
    field_at (cs := CompSpecs) Ews (tarray (tptr (Tstruct _md_entry noattr)) sz)
      [ArraySubsc 0] (Znth 0 (upd_Znth (f nullval) (Zrepeat Vundef sz) new))
      (field_address t_struct_css (DOT _metadata) css) ⊢
      field_at (cs := CompSpecs) Ews t_struct_css
      [ArraySubsc (f nullval); StructField _metadata] new css.
  Proof.
    pose proof f_0 as ->.
    rewrite (upd_Znth_same 0 (Zrepeat Vundef sz) new); auto.
    rewrite /data_at /field_at /at_offset data_at_rec_eq isptr_offset_val_zero /=; auto.
    rewrite field_compatible_field_address /=; auto.
    entailer !.
  Qed.

  Lemma new_node_fresh γ_I γ_f γ_k γ_m γ_n new new_node css
    (I: @multiset_flowint_ur Key _ _) r (md : list val) lock b
    (Hpt: is_pointer_or_null lock /\ is_pointer_or_null new) :
    field_at Ews t_struct_css [ArraySubsc (f new_node); StructField _metadata] new css ∗
    field_at Ews t_md_entry (DOT _lock) lock new ∗ atomic_int_at Ews b lock ∗
      nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css r ⊢ ⌜new_node ∉ dom I⌝.
  Proof.
    iIntros "(Hf_css & Hf_new & Hl & Hbigstar)". 
    rewrite /nodeFull.
    destruct (decide (new_node ∈ dom I)); last first; try done.
    rewrite (big_sepS_elem_of_acc _ (dom I) new_node); last by eauto.
    iDestruct "Hbigstar" as "(Hn & Hbigstar)".
    iDestruct "Hn" as (p' sh) "(%Hc & Hf & Hlt)".
    iDestruct "Hlt" as (lsh lk nr') "(%Hc1 & Hf1 & HinFP1 & Hlt)".
    destruct Hpt as (? & ?).
    destruct Hc as (Hrg_new & Hznth_p' & ? & ?).
    iDestruct (field_at_values_cohere _ _ t_struct_css
      [ArraySubsc (f new_node); StructField _metadata] _ _ css with "[$]") as %Hznth_new; auto.
    assert (p' = new) as -> by list_solve.
    destruct Hc1 as (? & ? & ?).
    iDestruct (field_at_values_cohere _ _ t_md_entry (DOT _lock) with "[$]") as %->; auto.
    iDestruct "Hlt" as (b') "(Hl1 & Hm1)".
    iDestruct (atomic_int_conflict with "[$]") as "?"; auto.
  Qed.

  Lemma md_entry_rep_conflict γ_I γ_k γ_m γ_n (p : Node) p1 a b css r1 r2:
    md_entry_rep γ_I γ_k γ_m γ_n p1 p a css r1 ∗
      md_entry_rep γ_I γ_k γ_m γ_n p1 p b css r2 ⊢ False.
  Proof.
    iIntros "((_ & _ & H1 & _) & (_ & _ & K1 & _))".
    iPoseProof (field_at_conflict _ t_md_entry (DOT _min) p1 with "[$H1 $K1]") as "HF";
      simpl; eauto. lia.
  Qed.

  Lemma md_entry_rep_pred_exclusive γ_I γ_k γ_m γ_n (p : Node) p1 nr css r:
    exclusive_mpred (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r).
  Proof. rewrite /exclusive_mpred. sep_apply md_entry_rep_conflict. entailer !. Qed.

  Lemma inv_lock a b c γ_I γ_k γ_m γ_n (p : Node) p1 lock_in css r:
    md_entry_rep γ_I γ_k γ_m γ_n p1 p a css r ∗
    inv_for_lock lock_in (md_entry_rep γ_I γ_k γ_m γ_n p1 p b css r) ⊢
    md_entry_rep γ_I γ_k γ_m γ_n p1 p a css r ∗
    inv_for_lock lock_in (md_entry_rep γ_I γ_k γ_m γ_n p1 p c css r).
  Proof.
    iIntros "(H1 & H2)".
    iDestruct "H2" as (b0) "(H2 & H3)".
    destruct b0.
    - iFrame "H1". iExists _. iFrame.
    - iExFalso. iPoseProof (md_entry_rep_conflict with "[$H1 $H3]") as "?"; auto.
  Qed.

  Lemma inv_lock1 r1 r2 r3 a b c γ_I γ_k γ_m γ_n (p : Node) p1 lock_in css :
    md_entry_rep γ_I γ_k γ_m γ_n p1 p a css r1 ∗
      inv_for_lock lock_in (md_entry_rep γ_I γ_k γ_m γ_n p1 p b css r2) ⊢
      md_entry_rep γ_I γ_k γ_m γ_n p1 p a css r1 ∗
      inv_for_lock lock_in (md_entry_rep γ_I γ_k γ_m γ_n p1 p c css r3).
  Proof.
    iIntros "(H1 & H2)".
    iDestruct "H2" as (b0) "(H2 & H3)".
    destruct b0.
    - iFrame "H1". iExists _. iFrame.
    - iExFalso. iPoseProof (md_entry_rep_conflict with "[$H1 $H3]") as "?"; auto.
  Qed.

  Lemma share_divided lsh t gfs v p:
    ⌜readable_share lsh⌝ ∧ field_at lsh t gfs v p ⊢
     (∃ lsh, ⌜readable_share lsh⌝ ∧ field_at lsh t gfs v p) ∗
     (∃ lsh, ⌜readable_share lsh⌝ ∧ field_at lsh t gfs v p).
  Proof.
    iIntros "(%Hr & H1)".
    assert(sepalg.join (fst (slice.cleave lsh)) (snd (slice.cleave lsh)) lsh).
    apply slice.cleave_join.
    iDestruct (field_at_share_join (fst (slice.cleave lsh)) (snd (slice.cleave lsh))
                with "[$]") as "(H11 & H12)"; try done.
    pose proof Hr as Kr.
    apply cleave_readable1 in Hr. apply cleave_readable2 in Kr.
    iSplitL "H11"; iExists _; by iFrame.
  Qed.

  Lemma share_join lsh1 lsh2 t gfs v p (Hsz : (0 < sizeof (nested_field_type t gfs))%Z) :
    ⌜readable_share lsh1 /\ readable_share lsh2⌝ ∧
    field_at lsh1 t gfs v p ∗ field_at lsh2 t gfs v p ⊢
      ∃ lsh : share, ⌜readable_share lsh⌝ ∧ field_at lsh t gfs v p.
  Proof.
    iIntros "(%Hc & Hf1 & Hf2)".
    destruct Hc as (Hr1 & Hr2).
    iDestruct (field_at_share_joins _ _ t with "[$Hf1 $Hf2]") as %(lsh & Hsj); try done.
    iExists lsh.
    iStopProof.
    rewrite (field_at_share_join lsh1 lsh2 lsh) //=.
    entailer !.
    apply (@join_readable1 lsh1 lsh2 lsh); auto.
  Qed.

  Definition flow_int I:=
    @flows.int (@multiset_flows.K_multiset Key Z.eq_dec Z_countable) K_multiset_ccm _ _ I.

  Lemma in_tree_inv1 (γ_I γ_f γ_k γ_g γ_m γ_n : gname) p p1 l md css r
    (I: @multiset_flowint_ur Key _ _):
    inFP γ_f p p1 l ∗ (nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css r ∗ own_nodes γ_f I md) ⊢
    (∃ nr : NodeR,
        inv_for_lock l (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r) ∗
          (inv_for_lock l (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r)
           -∗ (nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css r ∗ own_nodes γ_f I md))) ∧
      (inFP γ_f p p1 l ∗ ltree γ_I γ_k γ_f γ_m γ_n p1 p css r ∗
         (ltree γ_I γ_k γ_f γ_m γ_n p1 p css r
          -∗ (nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css r ∗ own_nodes γ_f I md))).
  Proof.
    iIntros "(#HinFP & (HNF & Hown))".
    iPoseProof (node_exist_inFP with "[$HinFP $Hown]") as "%Hp_in_dom".
    rewrite {1} /nodeFull (big_sepS_elem_of_acc _ (dom I) p) //=.
    iDestruct "HNF" as "(HNF & HR)".
    iDestruct "HNF" as (q sh) "(%Hc & Hf & Hlt)".
    destruct Hc as (Hlen & HZnth_q & ?).
    iDestruct (node_exist_md with "[$HinFP $Hown]") as %HZnth; try done.
    iSplit.
    { iDestruct "Hlt" as (lsh lock nr) "(% & Hf' & #HinFP' & Hinv)".
      iDestruct (in_FP_equiv _ _ _ _ l lock with "[$HinFP $HinFP']") as %(Hp & Hl); subst.
      iExists _.
      iFrame.
      iIntros "Hinv".
      iApply "HR".
      iExists _, _. iFrame "∗". iSplit; auto.
    }
    { iFrame "HinFP ∗".
      iDestruct "Hlt" as (lsh lock nr) "(% & Hf' & #HinFP' & Hinv)".
      iDestruct (in_FP_equiv _ _ _ _ l lock with "[$HinFP $HinFP']") as %(Hp & Hl); subst.
      iSplitL "Hf' Hinv".
      - iExists _, _. by iFrame.
      - iIntros "Hl".
        iApply "HR".
        iExists _, _. iFrame "∗". iSplit; auto.
    }
  Qed.

  Lemma in_tree_inv2 (γ_I γ_f γ_k γ_g γ_m γ_n : gname) p p1 l md C css r
    (I: @multiset_flowint_ur Key _ _):
    inFP γ_f p p1 l ∗ CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I md ⊢
      (∃ nr, inv_for_lock l (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r) ∗
                 (inv_for_lock l (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r)
                  -∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C css)) ∧
      (inFP γ_f p p1 l ∗ ltree γ_I γ_k γ_f γ_m γ_n p1 p css r ∗
              (ltree γ_I γ_k γ_f γ_m γ_n p1 p css r -∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C css)).
  Proof.
    iIntros "(#HinFP & Hcssi)".
    iDestruct "Hcssi" as "(%HZnth & (%H1 & H2 & H3 & Hown_m & Hown_nodes) &
                                H4 & Hl_idx & HNF & Hn)".
    iDestruct (in_tree_inv1 with "[$HinFP $Hown_nodes $HNF]") as "HNR"; auto.
    iSplit.
    { iDestruct "HNR" as "(HNR & _)".
      iDestruct "HNR" as (nr) "(Hinv & HNR)".
      iExists nr.
      iFrame "Hinv".
      iIntros "Hinv".
      iSpecialize ("HNR" with "[$Hinv]").
      iDestruct "HNR" as "(HNF & Hown_nodes)".
      iExists _, _, _.
      iFrame "∗". done.
    }
    { iDestruct "HNR" as "(_ & (HinFP' & Hl & Hl1))".
      iFrame.
      iIntros "Hl".
      iSpecialize ("Hl1" with "Hl").
      iDestruct "Hl1" as "(HNF & Hown_nodes)".
      iExists I, md, r.
      iFrame "∗". done.
    }
  Qed.

  Lemma in_tree_inv (γ_I γ_f γ_k γ_g γ_m γ_n : gname) p p1 l C css:
    inFP γ_f p p1 l ∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C css ⊢
      (∃ r nr, inv_for_lock l (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r) ∗
                 (inv_for_lock l (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r)
                  -∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C css)) ∧
      (∃ r, inFP γ_f p p1 l ∗ ltree γ_I γ_k γ_f γ_m γ_n p1 p css r ∗
              (ltree γ_I γ_k γ_f γ_m γ_n p1 p css r -∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C css)).
  Proof.
    iIntros "(#HinFP & Hcss)".
    iDestruct "Hcss" as (I md r) "Hcss".
    iDestruct "Hcss" as "(%HZnth & (H1 & H2 & H3 & Hown_m & Hown_nodes) & H4 & Hl_idx & HNF & Hn)".
    iDestruct (in_tree_inv1 with "[$HinFP $Hown_nodes $HNF]") as "HNR"; auto.
    iSplit.
    { iDestruct "HNR" as "(HNR & _)".
      iDestruct "HNR" as (nr) "(Hinv & HNR)".
      iExists r, nr.
      iFrame "Hinv".
      iIntros "Hinv".
      iSpecialize ("HNR" with "[$Hinv]").
      iDestruct "HNR" as "(HNF & Hown_nodes)".
      iExists _, _, _.
      iFrame "∗". done.
    }
    { iDestruct "HNR" as "(_ & (HinFP' & Hl & Hl1))".
      iFrame.
      iIntros "Hl".
      iSpecialize ("Hl1" with "Hl").
      iDestruct "Hl1" as "(HNF & Hown_nodes)".
      iExists I, md, r.
      by iFrame "∗".
    }
  Qed.
               
  Lemma lock_alloc {A} (b: gmap Key KValue → A → iPropI Σ) (Q : A -d> iProp Σ)
    γ_I γ_f γ_k γ_g γ_m γ_n (p: Node) (p1 l css: val) :
    atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗ inFP γ_f p p1 l ⊢
      (|={⊤}=> atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗ inFP γ_f p p1 l ∗
          (∃ lsh : share, ⌜readable_share lsh⌝ ∧
                            field_at lsh t_md_entry [StructField _lock] l p1)).
  Proof.
    iIntros "(AU & #HinFP)".
    iMod "AU" as (m) "[Hm HClose]".
    iPoseProof (in_tree_inv  with "[$HinFP $Hm]") as "HInvLock"; auto.
    iDestruct "HInvLock" as "(_ & HInvLock)".
    iDestruct "HInvLock" as (r) "(_ & Hl & Hcss)".
    rewrite {1} /ltree.
    iDestruct "Hl" as (lsh lock nr) "(%Hf & Hf & #HinFP' & Hinv)".
    destruct Hf as (Hf & Hr & Hpt).
    iDestruct (share_divided _ t_md_entry (DOT _lock) with "[$Hf]") as "(Hf1 & Hf2)"; eauto.
    iDestruct "Hf1" as (lsh1) "Hf1".
    iDestruct "Hf2" as (lsh2) "Hf2".
    iDestruct (in_FP_equiv _ _ _ _ l lock with "[$HinFP $HinFP']") as %(Hp & Hl); subst.
    iFrame.
    iAssert (ltree γ_I γ_k γ_f γ_m γ_n p1 p css r ) with "[Hf1 Hinv]" as "Hl".
    { iExists lsh1, lock, nr.
      iDestruct "Hf1" as "(%Hr' & Hf1)". iFrame "HinFP ∗". iSplit; auto. }
    iSpecialize ("Hcss" with "Hl").
    iSpecialize ("HClose" with "Hcss").
    iFrame "HinFP ∗".
  Qed.

  Lemma push_lock_back {A} (b: gmap Key KValue → A → iPropI Σ) (Q : A -d> iProp Σ)
    γ_I γ_f γ_k γ_g γ_m γ_n (p: Node) (p1 l css: val) lsh
    (Hrs: readable_share lsh):
    atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗ inFP γ_f p p1 l ∗
      field_at lsh t_md_entry [StructField _lock] l p1 ⊢
      (|={⊤}=> atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗ inFP γ_f p p1 l ).
  Proof.
    iIntros "(AU & #HinFP & Hf)".
    iMod "AU" as (m) "(Hm & HClose)".
    iDestruct (in_tree_inv with "[$HinFP $Hm]") as "InvLock"; auto.
    iDestruct "InvLock" as "(_ & InvLock)".
    iDestruct "InvLock" as (r) "(_ & Hl & Hcss)".
    rewrite {1} /ltree.
    iDestruct "Hl" as (lsh1 lock nr) "(%Hc & Hf' & HinFP' & HInv)".
    iDestruct (in_FP_equiv _ _ _ _ lock l with "[$HinFP $HinFP']") as %(? & Hl).
    destruct Hc as (Hf & Hrs1 & Hpt).
    rewrite / ltree.
    iAssert (∃ (lsh0 : share) (lock0: val) (nr0 : NodeR),
         ⌜field_compatible t_md_entry [] p1 ∧ readable_share lsh0 /\ is_pointer_or_null lock0⌝ ∧
         field_at (cs := CompSpecs) lsh0 t_md_entry (DOT _lock) lock0 p1 ∗
         inFP γ_f p p1 lock0 ∗ inv_for_lock lock0 (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr0 css r))
      with "[Hf Hf' HInv]" as "H1".
    { rewrite Hl.
      iDestruct (share_join _ _ t_md_entry (DOT _lock)
                  with "[$Hf $Hf']") as (sh) "(% & Hf)"; try iSplit; try done.
      iExists _, _, nr. iFrame "∗". iSplit; auto. try done. subst. done. }
    iSpecialize ("Hcss" with "H1").
    iDestruct "HClose" as "(HClose & _)".
    iSpecialize ("HClose" with "Hcss").
    iMod "HClose". by iFrame "HinFP".
  Qed.

  Lemma CSSi_unfold_nodeFull γ_I γ_f γ_k γ_g γ_m γ_n r C I p1 p l css md :
    inFP γ_f p p1 l ∗ CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I md
      ⊢ ⌜p ∈ dom I⌝ ∧
      (nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css r ∗
         (nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css r
          -∗ CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I md)).
  Proof.
    iIntros "(#HinFP & Hcss)".
    iDestruct "Hcss" as
      "(%Hznth & (HI & Hglob & Hks & Hown_m & Hown_nodes) & (Hml & (Hidx & Hbigstar & Hn)))".
    iDestruct (node_exist_inFP with "[$]") as %Hdom.
    rewrite {1} /nodeFull (big_opS_delete _ _ p) //=.
    iDestruct "Hbigstar" as "(Hp & Hbigstar)".
    iFrame "HI ∗".
    rewrite {1} /nodeFull.
    setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
    iFrame "Hbigstar ∗".
    iSplit; auto.
  Qed.

  Lemma CSS_unfold_nodeFull (γ_I γ_f γ_k γ_g γ_m γ_n : gname) p p1 l C css:
    inFP γ_f p p1 l ∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C css -∗
       ∃ (I : flowint_T) (md : list val) (r : val),
         ⌜p ∈ dom I⌝ ∧ nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css r ∗
         (nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css r -∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C css).
  Proof.
    iIntros "(#HinFP & Hcss)".
    iDestruct "Hcss" as (I md r) "Hcss".
    iDestruct (CSSi_unfold_nodeFull with "[$]") as "(%Hc & Hn & Hnf)".
    iExists I, _.
    iFrame "Hn".
    iSplit; auto.
    iIntros "Hn".
    iSpecialize ("Hnf" with "Hn").
    iDestruct "Hnf" as "(Hglob & Hml & Hdom & Hnf)".
    iExists _, _, _.
    iFrame "∗".
  Qed.

  Lemma CSSi_unfold_md_slot γ_I γ_f γ_k γ_g γ_m γ_n r C I p1 p l css md :
    inFP γ_f p p1 l ∗ CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I md
      ⊢ (([∗ set] i ∈ upto_gset size ∖ {[0%Z]}, md_slot i css) ∗
           (([∗ set] i ∈ upto_gset size ∖ {[0%Z]}, md_slot i css)
            -∗ CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I md)).
  Proof.
    iIntros "(#HinFP & Hcss)".
    iDestruct "Hcss" as "(%Hznth & (HI & Hglob & Hks & Hdom) & (Hml & (Hidx & Hbigstar)))".
    iFrame "Hidx".
    iIntros "Hidx".
    iFrame "∗".
    by iPureIntro.
  Qed.

  Lemma CSS_unfold_md_slot (γ_I γ_f γ_k γ_g γ_m γ_n : gname) p p1 l C c:
    inFP γ_f p p1 l ∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C c -∗
       (([∗ set] i ∈ upto_gset size ∖ {[0%Z]}, md_slot i c) ∗
          (([∗ set] i ∈ upto_gset size ∖ {[0%Z]}, md_slot i c)
               -∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C c)).
  Proof.
    iIntros "(#HinFP & Hcss)".
    iDestruct "Hcss" as (I md r) "Hcss".
    iDestruct (CSSi_unfold_md_slot with "[$]") as "(Hidx & Hr)".
    iFrame "Hidx".
    iIntros "Hidx".
    iSpecialize ("Hr" with "Hidx").
    iExists _, _, _.
    iFrame "∗".
  Qed.

  Lemma md_lock_alloc {A} (b: gmap Key KValue → A → iPropI Σ)
    (Q : A -d> iProp Σ) γ_I γ_f γ_k γ_g γ_m γ_n (p: Node) (p1 l css : val):
    atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗ inFP γ_f p p1 l ⊢
      (|={⊤}=> atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗ inFP γ_f p p1 l ∗
       (∃ (lsh : share) (md : list val),
          ⌜readable_share lsh /\ Znth (f p) md = p1 /\ is_pointer_or_null (Znth (f p) md)⌝ ∧
           field_at lsh t_struct_css [ArraySubsc (f p); StructField _metadata] (Znth (f p) md) css) ∗
       (∃ (lsh : share),
              ⌜readable_share lsh⌝ ∧ field_at lsh t_md_entry [StructField _lock] l p1)).
  Proof.
    iIntros "(AU & #HinFP)".
    iMod (lock_alloc with "[$HinFP $AU]") as "(AU & HinFP' & Hf)"; auto.
    iFrame "Hf".
    iMod "AU" as (m) "[Hm HClose]".
    iClear "HinFP'".
    iDestruct (CSS_unfold_nodeFull with "[$]") as "HNF"; auto.
    iDestruct "HNF" as (I md r) "(% & HNF & HNF')".
    rewrite {1} /nodeFull (big_opS_delete _ _ p) //=.
    iDestruct "HNF" as "(HNF & HNF1)".
    iDestruct "HNF" as (q sh) "(%Hc & Hf & Hlt)".
    destruct Hc as (Hrg & Hznth & ? & ?).
    iDestruct (share_divided _ t_struct_css [ArraySubsc (f p); StructField _metadata]
                with "[$Hf]") as "(Hf1 & Hf2)"; try done.
    iDestruct "Hf1" as (lsh1) "Hf1".
    iDestruct "Hf2" as (lsh2) "Hf2".
    rewrite /ltree.
    iDestruct "Hlt" as (lsh lock nr) "(% & Hf & #HinFP' & HInv)".
    iDestruct (in_FP_equiv _ _ _ _ lock l with "[$]") as %(Hp & Hl).
    iAssert (∃ (lsh : share) (md : list val),
         ⌜readable_share lsh ∧ Znth (f p) md = p1 ∧ is_pointer_or_null (Znth (f p) md)⌝ ∧
         field_at (cs := CompSpecs) lsh t_struct_css [ArraySubsc (f p); StructField _metadata]
           (Znth (f p) md) css) with "[Hf2]" as "Hf'".
    { iExists lsh2, md; iDestruct "Hf2" as "(% & Hf2)"; iFrame; subst; iSplit; auto. }
    iFrame "Hf'".
    iAssert (nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css r) with "[Hf HInv Hf1 HNF1]" as "Hl".
    { rewrite /nodeFull.
      setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
      iFrame "HNF1".
      iDestruct "Hf1" as "(%Hr & Hf1)".
      iExists _, _. by iFrame "HinFP' ∗".
    }
    iSpecialize ("HNF'" with "Hl").
    iSpecialize ("HClose" with "HNF'").
    by iFrame "HinFP".
  Qed.

  Lemma md_push_back (b: gmap Key KValue → val → iPropI Σ)
    (Q : val -d> iProp Σ) γ_I γ_f γ_k γ_g γ_m γ_n (p : Node) (p1 l css : val) lsh md
    (Hrs : readable_share lsh)
    (Hpnt : is_pointer_or_null (Znth (f p) md)) :
    atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗ inFP γ_f p p1 l ∗
      field_at lsh t_struct_css [ArraySubsc (f p); StructField _metadata] (Znth (f p) md) css ⊢
      (|={⊤}=> atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗ inFP γ_f p p1 l ).
  Proof.
    iIntros "(AU & #HinFP & Hf)".
    iMod "AU" as (m) "(Hm & HClose)".
    iPoseProof (CSS_unfold_nodeFull with "[$HinFP $Hm]") as "HNF"; auto.
    iDestruct "HNF" as (I md' r) "(% & HNF & HNF')".
    unfold nodeFull at 1.
    rewrite (big_opS_delete _ _ p); auto.
    iDestruct "HNF" as "(HNF & HNF1)".
    iDestruct "HNF" as (q sh) "(%Hc & HNF & Hlt)".
    destruct Hc as (? & ? & ? & ?).
    iDestruct (field_at_values_cohere _ _ t_struct_css
                  [ArraySubsc (f p); StructField _metadata] with "[$]") as %Hz; auto.
    rewrite Hz.
    iAssert(∃ lsh0 : share, ⌜readable_share lsh0⌝ ∧
                 field_at (cs := CompSpecs) lsh0 t_struct_css
                   [ArraySubsc (f p); StructField _metadata] (Znth (f p) md) css)
      with "[Hf HNF]" as "Hf".
    {
      iDestruct (share_join lsh sh t_struct_css [ArraySubsc (f p); StructField _metadata] _ css 
                   with "[$Hf $HNF]") as "Hf"; try iSplit; try done.
    }
    iAssert (nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md' css r) with "[Hlt HNF1 Hf]" as "HNF".
    { rewrite /nodeFull.
      setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
      iFrame "HNF1".
      iDestruct "Hf" as (?) "(% & Hf)".
      rewrite Hz.
      iExists _, _.
      iFrame "Hlt Hf".
      iPureIntro. repeat (split; list_solve).
    }
    iSpecialize ("HNF'" with "HNF").
    iDestruct "HClose" as "(HClose & _)".
    iSpecialize ("HClose" with "HNF'").
    iMod "HClose"; try auto.
  Qed.
  
  Lemma int_domm γ_I γ_f γ_k γ_g γ_m γ_n r C css I md n In:
    ⌜dom In = {[n]}⌝ ∧ own γ_I (◯ In) ∗ CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I md ⊢ ⌜n ∈ dom I⌝.
  Proof.
    iIntros "(%Dom_In & Hi & Hcss)".
    iDestruct "Hcss" as "(Hznth & (Hglob & HI & Hks & Hdom) & (Hd & Hbigstar))".
    iDestruct (own_valid_2  with "HI Hi") as %Hown%auth_both_valid_discrete.
    destruct Hown as [[Io Io1] I_incl].
    iPureIntro.
    rewrite Io1 intComp_dom; last first; try rewrite <- Io1; auto.
    set_solver.
  Qed.

  Lemma CSS_unfold1 γ_I γ_f γ_k γ_g γ_m γ_n r C I p css md :
    CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I md ∧ ⌜p ∈ dom I⌝ ⊢
    (globalGhost γ_I γ_f γ_k γ_m r C I md ∗ nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css r ∗
    (∀ C', globalGhost γ_I γ_f γ_k γ_m r C' I md ∗ nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css r
               -∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C' css)).
  Proof.
    iIntros "(Hcss & %)".
    iDestruct "Hcss" as "(Hznth & (HI & Hglob & Hks & Hdom) & (Hml & (Hd & Hbigstar & Hn)))".
    rewrite {1} /nodeFull (big_opS_delete _ _ p); auto.
    iDestruct "Hbigstar" as "(Hp & Hbigstar)".
    iFrame "HI Hglob Hks Hdom ".
    setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
    iFrame "Hbigstar Hp".
    iIntros (C') "((HI & (Hks & (Hown & Hown_nodes))) & Hglob)".
    iFrame "Hml ∗".
  Qed.

  Lemma ghost_update_step (γ_I γ_f γ_k γ_g γ_m γ_n: gname) p p1 (q : Node) I C nr css md r x
    (Hlen: Zlength md = size) (Hne_p_null: p <> nullval) :
    CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I md ∗ md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r ∧
    ⌜in_inset _ _ Key x (Ip nr) p ∧ in_outset _ _ Key x (Ip nr) q⌝
    ==∗ ∃ q1 l, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css ∗ md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r ∗
        (inFP γ_f q q1 l ∧
          ⌜is_pointer_or_null q /\ is_pointer_or_null q1 /\ is_pointer_or_null l /\
           (0 <= f q < size)%Z⌝).
  Proof.
    iIntros "(Hcssi & (Hnp & (%Hin & %Hout)))".
    iDestruct "Hnp" as "(%Hc & Hml & Hmin & Hmax & Hn & HfI & Hfk & Hfm & Hrest)".
    rewrite -> if_false; auto.
    destruct Hc as (? & ? & ? & ? & ? & Hdom & ?).
    iDestruct (int_domm with "[$HfI $Hcssi]") as %HdomI; auto.
    iDestruct (CSS_unfold1 with "[$Hcssi]") as "(Hglob & (Hnf & Hcss))"; auto.
    iDestruct "Hglob" as "(Hglob & HaI & Hak & Ham & Hown_nodes)".
    iDestruct "Hglob" as %Hglob.
    iDestruct (own_valid_2 γ_I  (● I) (◯ Ip nr) with "[$HaI] [$HfI]") as
      %Hincl%auth_both_valid_discrete.
    destruct Hincl as ((I0 & I_incl) & Hv).
    assert (✓ (Ip nr ⋅ I0)) as Hvc.
    { rewrite I_incl in Hv; auto. }
    assert (q ∈ dom I0) as Hp1_dom.
    { apply (flowint_step I (Ip nr) I0 x q); auto.
      rewrite /globalinv in Hglob.
      destruct Hglob as ((? & ? & ? & ?) & ?); auto.
    }
    assert (dom I = dom (Ip nr) ∪ dom I0) as Hdom_union. 
    { rewrite I_incl intComp_dom; auto. }
    assert (q ∈ dom I) as Hq_dom.
    { clear -Hp1_dom Hdom_union. set_solver. }
    iMod (ghost_snapshot_fp with "[$Hown_nodes]") as "(Hown_nodes & HinFP')"; auto.
    iDestruct "HinFP'" as (? ?) "(HinFP' & %Hc)".
    iModIntro.
    iExists q1, l.
    iAssert (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r)
      with "[$Hml $Hmin $Hmax $Hn $HfI $Hfk $Hfm]" as "Hmd".
    { rewrite -> if_false; auto. }
    iFrame "HinFP' Hmd".
    iSplit; auto.
    { iApply "Hcss".
      iFrame "Hnf ∗".
      iPureIntro.
      split; auto.
    }
    iPureIntro.
    destruct Hc as (? & ? & ? & ? & ?).
    rewrite Hlen in H10.
    repeat (split; auto).
  Qed.
  
  Lemma CSS_unfold γ_I γ_f γ_k γ_g γ_m γ_n r C I p p1 l css md:
    inFP γ_f p p1 l ∗ CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I md ∧ ⌜p ∈ dom I⌝ 
    ⊢ (globalGhost γ_I γ_f γ_k γ_m r C I md ∗ ltree γ_I γ_k γ_f γ_m γ_n p1 p css r ∗
       (∀ C', globalGhost γ_I γ_f γ_k γ_m r C' I md ∗ ltree γ_I γ_k γ_f γ_m γ_n p1 p css r
               -∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C' css)).
  Proof.
    iIntros "(#HinFP & Hcss & %)".
    iDestruct "Hcss" as "(Hznth & (HI & Hglob & Hks & Hdom) & (Hml & Hi & Hbigstar & Hn))".
    rewrite {1} /nodeFull (big_sepS_elem_of_acc _ (dom I) p); auto.
    iDestruct "Hbigstar" as "(Hp & Hbigstar)".
    iDestruct "Hp" as (q sh) "(% & Hf & Hlt)".
    unfold ltree at 1.
    iDestruct "Hlt" as (lsh lock nr) "(% & Hf' & #HinFP' & HInv)".
    iDestruct (in_FP_equiv _ _ _ _ lock l with "[$HinFP $HinFP']") as "%Heq".
    destruct Heq; subst.
    iFrame "HI HinFP' ∗".
    iSplit; auto.
    iIntros (C') "((HI & (Hks & (Hown & Hown_nodes))) & Hglob)".
    iExists _, _, _.
    iFrame.
    iApply "Hbigstar".
    iExists _, _. iFrame. iSplit; auto.
  Qed.

  Lemma in_tree_inv' γ_I γ_f γ_k γ_g γ_m γ_n I C md p p1 l nr css r:
    inFP γ_f p p1 l ∗ md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r ∗
      CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I md ⊢
      (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r ∗
         (inv_for_lock l (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r) ∗
            (inv_for_lock l (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r)
             -∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C css))).
  Proof.
    iIntros "(#HinFP & Hme & Hcssi)".
    iDestruct "Hcssi" as "(Hznth & (Hg & (HI & (Hk & Hown_m & Hown_nodes))) &
(Hml & (Hl_idx & HNF & Hn)))".
    iDestruct (node_exist_inFP with "[$HinFP $Hown_nodes]") as %Hp_in_dom.
    rewrite /nodeFull (big_sepS_elem_of_acc _ (dom I) p); auto.
    iDestruct "HNF" as "(HNF & HR)".
    iDestruct "HNF" as (q sh) "(%Hc & Hf1 & Hlt)".
    iDestruct "Hlt" as (lsh lock nr1) "(% & Hf2 & #HinFP1 & Hinv)".
    iDestruct (in_FP_equiv _ _ _ _ lock l with "[$HinFP $HinFP1]") as %(Hp & ->).
    rewrite Hp.
    iDestruct "Hme" as "(Hmy & Hme)".
    iDestruct (inv_lock _ nr1 nr with "[$Hmy $Hme $Hinv]") as "(Hme & Hinv)".
    iFrame "Hme Hinv".
    iIntros "Hinv".
    iFrame "Hg ∗".
    iApply "HR".
    iExists _, _.
    iSplit; auto.
    iFrame.
    iExists _, l, nr.
    rewrite -Hp.
    by iFrame "HinFP ∗".
 Qed.

 Lemma nodeFullEq_nullval: forall (γ_I γ_k γ_f γ_m γ_n : gname) new_node css md r 
    (I : @flowintT (@multiset_flows.K_multiset Key Z.eq_dec Z_countable) _ _ _),
      ⌜dom I = {[nullval]}⌝ ∧
        field_at Ews t_struct_css (DOT _root) new_node css ∗
        nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css r ⊢
        field_at Ews t_struct_css (DOT _root) new_node css ∗
        nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css new_node.
  Proof.
    intros.
    iIntros "(%Hdom & Hf & HnodeFull)".
    assert (nullval ∈ dom I) as Hp. set_solver.
    rewrite /nodeFull Hdom.
    rewrite ! big_opS_singleton.
    iDestruct "HnodeFull" as (p1 lsh) "(%Hc & ? & Hlt)".
    iDestruct "Hlt" as (lsh1 lock nr) "(%Hc1 & ? & HinFP & Hinv)".
    iDestruct "Hinv" as (b) "(Hinv & Hif)".
    destruct b.
    - iFrame.
      iSplit; auto.
    - iExFalso.
      rewrite /md_entry_rep.
      rewrite -> if_true; auto.
      iDestruct "Hif" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hf_css)".
      iDestruct (field_at_conflict with "[$Hf $Hf_css]") as "?"; try auto; simpl; try lia.
  Qed.

  Lemma AS_to_AS {A} (b: gmap Key KValue → A → mpred)
    (Q : A -d> mpred)
    γ_I γ_f γ_k γ_g γ_m γ_n css:
    atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q  ⊢
      atomic_shift (λ C : gmap Key KValue, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) (⊤ ∖ ∅) ∅
    (λ (C : gmap Key KValue) (_ : val), CSS γ_I γ_f γ_k γ_g γ_m γ_n C css ∗ emp)
      (λ _ : val, atomic_shift (λ C : gmap Key KValue, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q).
  Proof.
    iIntros "AU".
    unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
    iMod "AU" as (m) "(Hm & HClose)".
    iModIntro.
    iExists _.
    iFrame.
    iSplit.
    iIntros "l"; iApply "HClose"; iFrame.
    iIntros (?) "[inv _]".
    iDestruct "HClose" as "(HClose & _)".
    iSpecialize ("HClose" with "inv").
    iMod ("HClose").
    iFrame "HClose". done.
  Qed.

  Lemma AS_to_css_metadata_update {A} (b: gmap Key KValue → A → mpred) (Q : A -d> mpred)
    γ_I γ_f γ_k γ_g γ_m γ_n p p1 l new_node css (Hne: f new_node <> 0%Z):
    (0 < @sizeof (@DS_compspecs Σ VSTGS0 NR) t_struct_node)%Z ->
    (0 ≤ f new_node < size)%Z ->
    atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗ inFP γ_f p p1 l ∗
      malloc_token (cs := (@DS_compspecs Σ VSTGS0 NR)) Ews1 t_struct_node new_node
    ⊢ |={⊤}=>
    atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗ inFP γ_f p p1 l ∗
    field_at_ Ews t_struct_css [ArraySubsc (f new_node); StructField _metadata] css.
  Proof.
    intros Hszof Hnew_range.
    iIntros "(AU & (#HinFP & Hml))".
    iMod "AU" as (m) "(Hm & HClose)".
    iPoseProof (CSS_unfold_md_slot with "[$HinFP $Hm]") as "(Hl & HNF)"; auto.
    setoid_rewrite (big_opS_delete _ _ (f new_node)) at 1; auto.
    iDestruct "Hl" as "(Hmd & Hl)".
    iPoseProof (get_field_at new_node css with "[$Hml $Hmd]") as "(Hmd & Hf)"; auto.
    iFrame "Hf".
    2 : { apply In_upto_gset_new; auto. lia. }
    iAssert (([∗ set] i ∈ upto_gset size ∖ {[0%Z]}, md_slot i css)) with "[Hl Hmd]" as "HS".
    { setoid_rewrite (big_opS_delete _ _ (f new_node)) at 2; auto.
      iFrame. apply In_upto_gset_new. lia. lia. }
    iSpecialize ("HNF" with "HS").
    iSpecialize ("HClose" with "HNF").
    iFrame "HinFP HClose".
  Qed.

  Lemma insertOp_helper_gain_md_entry_rep (I_new I0 : @flowintT (@multiset_flows.K_multiset Key Z.eq_dec Z_countable) _ _ _) (Cp' C_new : gmap Key KValue) (Q : mpred)
    (γ_I γ_f γ_k γ_g γ_m γ_n : gname) p p1 l new new_node lock css nr (r : val) x v key
    (fmin fmax : Z) (Hp_non_null : p ≠ nullval) (Hnew_non_null: new_node ≠ nullval)
    (Hx_lt_gt : ((x < key)%Z /\ fmin = min nr /\ fmax = key) \/
                  ((x > key)%Z /\ fmin = key /\ fmax = max nr))
    (Hp_p: is_pointer_or_null p) (Hp_p1: is_pointer_or_null p1) (Hp_lock: is_pointer_or_null lock)
    (Hp_new: is_pointer_or_null new) (Hp_new_node: is_pointer_or_null new_node)
    (Hfcmp_new: field_compatible t_md_entry [] new) (Hf_rg: (0 ≤ f p < size)%Z)
    (Hr_min : repable_signed (min nr)) (Hr_max : repable_signed (max nr))
    (Hx_rg : (Int.min_signed < x < Int.max_signed)%Z)
    (Hkey_rg : (Int.min_signed < key < Int.max_signed)%Z)
    (Hsz : size = 16384%Z) (Hx_not_in_dom: x ∉ dom (Cp nr)) (Hx_in_KS: x ∈ KS)
    (Hx_inset_Ip : in_inset Node_EqDecision Node_countable Key x (Ip nr) p)
    (Hnew_bound : (0 ≤ f new_node < 16384)%Z) (HdomIp : dom (Ip nr) = {[p]})
    (HdomI0 : dom I0 = {[p]}) (HdomI_new : dom I_new = {[new_node]})
    (HCp_dom_keys_range : ∀ k : Z, k ∈ dom (Cp nr) → (min nr < k < max nr)%Z)
    (HinfI0Ip : inf_map I0 = inf_map (Ip nr))
    (Hnonnull_inset_range : p ≠ nullval → ∀ k : Z, (min nr < k < max nr)%Z →
                                                   in_inset _ _ _  k (Ip nr) p)
    (HcxtLeq : cxtLeq (Ip nr) I_new I0 p new_node)
    (Hx_in_ks_new : {[x]} ⊆ keyset _ _ _ I_new new_node) (HdomCp : dom (Cp nr) ⊆ keyset _ _ _ I0 p)
    (HCp : Cp' = Cp nr ∧ C_new = {[x := v]}) (HdomCp'_key : dom Cp' = {[key]})
    (Hkey_property1 : key_property1 p new_node (Ip nr) I_new (Cp nr) x)
    (Hbelongs : p ≠ nullval → belongs x nr):
    let nr_p := {| min := min nr; max := max nr; Cp := Cp'; Ip := I0 |} in
    let AS := atomic_shift (λ C : gmap Key KValue, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅
                (λ (C : gmap Key KValue) (_ : ()),
                  CSS γ_I γ_f γ_k γ_g γ_m γ_n (<[x:=v]> C) css ∗ emp) (λ _ : (), Q)  in

    (□ inFP γ_f p p1 l ∗ node new_node I_new C_new ∗
       field_at Ews t_md_entry (DOT _min) (vint fmin) new ∗
       field_at Ews t_md_entry (DOT _max) (vint fmax) new ∗
       field_at Ews t_struct_css [ArraySubsc (f new_node); StructField _metadata] new css ∗
       malloc_token Ews t_md_entry new) ∗ AS ∗ atomic_int_at Ews (vint 1) lock ∗
      field_at Ews t_md_entry (DOT _lock) lock new ∗ inFP γ_f p p1 l ∗
      field_at Ews t_md_entry (DOT _min) (vint (min nr)) p1 ∗
      field_at Ews t_md_entry (DOT _max) (vint (max nr)) p1 ∗ node p I0 Cp' ∗ own γ_I (◯ Ip nr) ∗
      own γ_k (◯ prod (keyset _ _ _ (Ip nr) p, dom (Cp nr))  : keyset_authR Key) ∗
      own γ_m (◯ (Excl <$> Cp nr) : keymap_authR _ _) ∗ malloc_token Ews t_md_entry p1
      ⊢ atomic_shift (λ _ : (), atomic_int_at Ews (vint 1) lock) (⊤ ∖ ∅) ∅
      (λ _ _ : (), atomic_int_at Ews (vint 0) lock ∗ emp)
      (λ _ : (), inFP γ_f p p1 l ∗
                   atomic_shift (λ _ : (), atomic_int_at Ews (vint 1) l) (⊤ ∖ ∅) ∅
                   (λ _ _ : (), atomic_int_at Ews (vint 0) l ∗ emp) (λ _ : (), Q)).
  Proof.
    intros; destruct HcxtLeq as (HcxtLeq & Hinf & Hk_union & Hk_disj).
    iIntros "(Hmd_new & Hmd_p)".
    unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
    iDestruct "Hmd_p" as "(HAS & Htm & Hl_new & #HinFP & Hmin &
                   Hmax & Hn_p & HI & Hk & Hm & Hml_p)".
    iDestruct "Hmd_new" as "(_ & Hn_new & Hmin_new & Hmax_new & Hf_css_new & Hml_new)".
    iMod "HAS" as (m) "(Hcss & HClose)".
    rewrite /=.
    iModIntro.
    iExists ().
    iFrame "Htm".
    iSplit.
    { iIntros "Htm".
      iDestruct "HClose" as "(HClose & _)".
      iFrame "HinFP ∗".
      iApply "HClose". by iFrame.
    }
    iIntros (_) "(Htm & _)".
    iDestruct "HClose" as "(HClose & _)".
    iSpecialize ("HClose" with "Hcss").
    iMod ("HClose").
    iFrame "HinFP".
    iModIntro.
    unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
    clear dependent m.
    iMod "HClose" as (m) "[Hcss HClose]".
    iExists ().
    iModIntro.
    (*prove atomic_int_at *)
    iDestruct "Hcss" as (I md r') "Hcssi".
    iDestruct "Hcssi" as "(%Hznth & Hglob & Hml & Hidx & HNF & Hownr')".
    iAssert (⌜p ∈ dom I⌝) with "[Hglob HI]" as "%HpInDom".
    { iDestruct "Hglob" as "(%Hglob & HauthI & Hauthk & Hauthm & Hown_nodes)".
      destruct Hglob as (Hglob & Hr).
      iDestruct (own_valid_2 with "[$HauthI] [$HI]") as "%HvIp".
      apply auth_both_valid_discrete in HvIp.
      destruct HvIp as (Hle & Valid_I).
      destruct Hle as [Io I_incl].
      assert (p ∈ dom (Ip nr)) as Hdomp.
      { clear -HdomIp. set_solver. }
      iPureIntro.
      rewrite I_incl in Valid_I.
      rewrite I_incl.
      rewrite intComp_dom; auto.
      clear -Hdomp. set_solver.
    }
    destruct Hznth as (Hznth & Hnull_in_domI).
    assert ((0 ≤ f new_node < Zlength md)%Z) as Hfnew.
    { rewrite -Hsz in Hnew_bound. rewrite Hznth; auto. }
    setoid_rewrite (big_opS_delete _ _ p) at 1; auto.
    iDestruct "HNF" as "(HNF & Hrest)".
    iDestruct "HNF" as (q qsh) "(% & Hf & Hlt)".
    rewrite {1} /ltree.
    iDestruct "Hlt" as (lsh1 lk1 nr1') "(% & Hf1 & HinFP1 & Hinv)".
    iAssert (⌜q = p1 /\ lk1 = l⌝) with "[HinFP HinFP1]" as "%Hpk".
    { iDestruct (in_FP_equiv _ p q p1 lk1 l with "[$HinFP $HinFP1]") as "?"; auto. }
    destruct Hpk as (Hpt & Hlk).
    rewrite Hpt Hlk.
    (* new_node ∉ dom I *)
    iDestruct (new_node_fresh γ_I γ_f γ_k γ_m γ_n new new_node css I
                          with "[$Htm $Hl_new $Hf_css_new Hf Hf1 HinFP1 Hinv Hrest]")
                as %Hnew_notin_domI; auto.
    { setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
      iFrame.
      iSplit; auto.
      iPureIntro.
      subst. auto.
      subst. auto.
    }
    iDestruct "Hinv" as (b) "(Htm1 & Hmd1)".
    destruct b.
    2 : {
      iDestruct "Hmd1" as "(? & Hml1 & ?)".
      iPoseProof (malloc_token_conflict with "[$Hml1 $Hml_p]") as "HF";
                  simpl; eauto. lia.
    }
    iFrame "Htm1".
    iSplit.
    iIntros "Htm1".
    iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css) with
                "[$Hglob $Hml $Hidx $Hownr' Hf Hf1 HinFP1 Htm1 Hmd1 Hrest]" as "Hcss".
    { iSplit; auto.
      setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
      iFrame.
      iSplit; auto.
      iPureIntro.
      subst; auto.
      iExists nr.
      iSplit; auto. subst. auto.
      rewrite /inv_for_lock.
      iExists true. iFrame.
    }
    iSpecialize ("HClose" with "Hcss").
    by iFrame.
    iIntros (_) "Hinv".
    iDestruct "Hinv" as "(Htm1 & _)".
    assert (x ∈ keyset _ _ _ (Ip nr) p) as Hx_in_keyset.
    { destruct HcxtLeq as (? & ? & ? & ?).
      rewrite -Hk_union.
      clear -Hx_in_ks_new. set_solver.
    }
    iDestruct "Hglob" as "(%Hglob & HownI & Hownk & Hownm & Hown_nodes)".
    (* x ∉ dom m *)
    iDestruct (key_new_node_fresh _ _ x with "[$Hownk $Hk]") as %Hx_notin_dom_m; auto.
    (* ghost_insert_keyset' *)
    iMod (ghost_insert_keyset_add_node γ_k γ_m p new_node x v m (Cp nr) (Ip nr) I_new I0
           with "[$Hownk $Hownm $Hk $Hm]")
               as "(Hownk & HkI0 & HkI_new & Hownm & HmI0 & HmI_new)"; try done.
    destruct Hglob as (Hglob & HdomI).
    iMod (ghost_update_interface _ _ r' I (Ip nr) I0 I_new p new_node new lock
                     with "[$HownI $Hown_nodes $HI]") as "Hflow"; auto.
    { split; auto; rewrite Hznth; auto. }
    iDestruct "Hflow" as (I1 md1) "(%Hctx & HI & HI1 & HI2 & Hown1 & #HinFP_new)".
    destruct Hctx as (Hctx & Hglobinv).
    iDestruct "HClose" as "(_ & HClose)".
    iAssert (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr_p css r)
                with "[$Hmin $Hmax HmI0 $Hn_p $HI1 HkI0 $Hml_p]" as "Hmd".
    { destruct HCp as (HCp' & HCnew).
      rewrite /md_entry_rep /nr_p HCp' /=.
      rewrite -> if_false; auto.
      iFrame.
      iPureIntro.
      repeat (split; auto).
      by rewrite /in_inset /inf HinfI0Ip.
    }
    iAssert (nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css r')
                with "[Hrest Hmd Htm1 Hf HinFP1 Hf1]" as "HNF".
    { iAssert (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr_p css r') with "[Hmd]" as "Hmd".
      { rewrite /md_entry_rep ! if_false; auto. }
      setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
      rewrite {2} /ltree.
      iFrame.
      iSplit; subst; try done.
      iExists nr_p.
      iSplit; subst; try done.
      iExists false. subst. iFrame "Hmd ∗".
    }
    iApply ("HClose" $! tt).
    rewrite bi.sep_emp.
    iExists I1 ,_ , r'.
    iFrame "∗".
    setoid_rewrite (big_opS_delete _ _ new_node) at 2; auto.
    destruct Hglobinv as (Hglob1 & HdomI1 & HdomI1' & Hmd1 & Hdomp).
    rewrite HdomI1' Hmd1 /nodeFull !upd_Znth_same.
    repeat iSplit; auto.
    { by rewrite Zlength_upd_Znth. }
    { rewrite HdomI1. clear -Hnull_in_domI. iPureIntro. set_solver. }
    iPureIntro.
    { do 2 split; auto.
      intros Hr'.
      specialize (HdomI Hr').
      destruct HdomI as (HdomI & ?).
      rewrite HdomI in Hdomp.
      apply elem_of_singleton_1 in Hdomp. try done.
    }
    iAssert (ltree γ_I γ_k γ_f γ_m γ_n new new_node css r')
      with "[Hl_new Htm Hmin_new Hmax_new Hn_new HI2 HmI_new HkI_new Hml_new]" as "Hltree".
    { rewrite /ltree.
      destruct Hx_lt_gt as [Hlt_x_key | Hgt_x_key].
      + destruct Hlt_x_key as (Hlt_x_key & Hfmin & Hfmax).
        set (nr_new := {| min := (min nr); max := Int.signed (Int.repr key);
                                                   Cp := C_new; Ip := I_new;|}).
        iExists _, _, nr_new.
        iFrame "Hl_new HinFP_new".
        iSplit; auto.
        rewrite /inv_for_lock.
        iExists false. iFrame "Htm".
        rewrite /md_entry_rep /nr_new /=.
        destruct HCp as (HCp' & HCnew).
        rewrite HCnew dom_singleton_L.
        assert (vint (Int.signed (Int.repr key)) = vint key) as ->; auto.
        { rewrite Int.signed_repr; auto. lia. }
        iFrame.
        iSplit; auto.
        { iPureIntro.
          assert (key ∈ dom (Cp nr)) as Hkey_in_dom. set_solver.
          assert (Int.signed (Int.repr key) = key) as Hkey_int.
          { rewrite Int.signed_repr; auto. lia. }
          rewrite /key_property1 in Hkey_property1.
          destruct Hkey_property1 as (? & Hdom & (HLe & HGe)).
          assert (x0 = key) as Hkey.
          { subst. rewrite Hdom in Hkey_in_dom. clear -Hkey_in_dom. set_solver. }
          subst.
          specialize (HLe Hlt_x_key) as Hk.
          repeat (split; auto; try lia).
          intros _ ? Hk1.
          specialize (HLe Hlt_x_key).
          assert ((min nr < key < max nr)%Z) as Hkey_range.
          { apply HCp_dom_keys_range. set_solver. }
          apply HLe.
          { split; try eapply Hnonnull_inset_range; eauto; try lia. }
          rewrite /belongs in Hbelongs.
          specialize (Hbelongs Hp_non_null).
          apply elem_of_singleton_1 in H2; subst; try lia.
          apply elem_of_singleton_1 in H2; subst; try lia.
        }
        rewrite if_false; auto.
        subst. iFrame.
      + destruct Hgt_x_key as (Hgt_x_key & Hfmin & Hfmax).
        set (nr_new := {| min := Int.signed (Int.repr key); max := (max nr);
                                  Cp := C_new; Ip := I_new;|}).
        iExists _, _, nr_new.
        iFrame "Hl_new HinFP_new".
        iSplit; auto.
        rewrite /inv_for_lock.
        iExists false. iFrame "Htm".
        rewrite /md_entry_rep /nr_new /=.
        destruct HCp as (HCp' & HCnew).
        rewrite HCnew dom_singleton_L.
        assert (vint (Int.signed (Int.repr key)) = vint key) as ->; auto.
        { rewrite Int.signed_repr; auto. lia. }
        iFrame.
        iSplit; auto.
        { iPureIntro.
          assert (key ∈ dom (Cp nr)) as Hkey_in_dom. set_solver.
          assert (Int.signed (Int.repr key) = key) as Hkey_int.
          { rewrite Int.signed_repr; auto. lia. }
          rewrite /key_property1 in Hkey_property1.
          destruct Hkey_property1 as (? & Hdom & (HLe & HGe)).
          assert (x0 = key) as Hkey.
          { subst. rewrite Hdom in Hkey_in_dom. clear -Hkey_in_dom. set_solver. }
          subst.
          specialize (HGe Hgt_x_key) as Hk.
          rewrite /belongs in Hbelongs.
          specialize (Hbelongs Hp_non_null).
          repeat (split; auto; try lia).
          intros _ ? Hk1.
          specialize (HGe Hgt_x_key).
          assert ((min nr < key < max nr)%Z) as Hkey_range.
          { apply HCp_dom_keys_range. set_solver. }
          apply HGe.
          { split; try eapply Hnonnull_inset_range; eauto; try lia. }
          apply elem_of_singleton_1 in H2; subst; try lia.
          apply elem_of_singleton_1 in H2; subst; try lia.
        }
        rewrite if_false; auto.
        subst. iFrame.
     }
     iSplitL "Hltree Hf_css_new".
     { iFrame "Hltree Hf_css_new". iPureIntro.
       rewrite Zlength_upd_Znth; try repeat (split; auto).
     }
     iApply (big_sepS_mono with "[$HNF]").
     intros x0 ?.
     iIntros "H".
     iDestruct "H" as (? ?) "(%Hc & H1 & H2)".
     iFrame "H2".
     rewrite Zlength_upd_Znth upd_Znth_diff; auto; try by destruct Hc.
     intros Hcontra.
     apply f_injective in Hcontra. set_solver. auto.
     destruct Hglobinv as (? & HdomI1 & ? & ?).
     rewrite HdomI1; clear. set_solver.
 Qed.
  
 Lemma inv_lock2 r1 r2 nr γ_I γ_k γ_m γ_n (p : Node) p1 lock_in css (Hne_p_null: p <> nullval):
    md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r1 ∗
    inv_for_lock lock_in (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r1) ⊢
    md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r2 ∗
    inv_for_lock lock_in (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r2).
 Proof.
   iIntros "(Hmd & Hinv)".
   iAssert(md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r2) with "[Hmd]" as "Hmd".
   { rewrite /md_entry_rep. rewrite -> ! if_false; auto. }
   iDestruct "Hinv" as (b) "(Htm & Hinv)".
   destruct b.
   - iFrame.
   - iExFalso.
     iPoseProof (md_entry_rep_conflict with "[$Hinv $Hmd]") as "?"; auto.
 Qed.

 Lemma inv_lock3 r r' nr γ_I γ_k γ_m γ_n (p : Node) p1 lock_in css (Hne_p_null: p <> nullval):
   inv_for_lock lock_in (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r) ⊢
   inv_for_lock lock_in (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r').
 Proof.
   iIntros "Hinv".
   iDestruct "Hinv" as (b) "(Htm & Hinv)".
   destruct b.
   - iExists true. iFrame.
   - iExists false.
     iAssert(md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r') with "[Hinv]" as "Hinv".
     { rewrite /md_entry_rep. rewrite -> ! if_false; auto. }
     iFrame.
 Qed.

 Lemma valid_flow {A} (b: gmap Key KValue → A → iPropI Σ) (Q : A -d> iProp Σ)
   γ_I γ_f γ_k γ_g γ_m γ_n (p p1 css : val) nr r:
   atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗
     md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r ⊢
     (|={⊤}=> ⌜✓ (Ip nr)⌝ ∧
     atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗
     md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r).
 Proof.
   iIntros "(AU & Hmd)".
   iMod "AU" as (m) "(Hm & HClose)".
   iDestruct "Hm" as (I md r') "Hcssi".
   iDestruct "Hcssi" as "(%Hznth & (%Hg & (HI & (Hk & Hown_m & Hown_nodes))) &
(Hml & (Hl_idx & HNF & Hn)))".
   destruct Hznth as (Hznth & ?).
   simpl.
   destruct Hg as ((Hv & ?) & ?).
   rewrite {1} /md_entry_rep.
   iDestruct "Hmd" as "(%Hc & Hml1 & Hmin & Hmax & Hnode &
                      HfI & Hfk & Hfm & Hrest)".

   iDestruct (own_valid_2 with "[$HI] [$HfI]") as "%HvIp".
   apply auth_both_valid_discrete in HvIp.
   destruct HvIp as [[Iz Ipn_incl_I] Valid_I].
   rewrite Ipn_incl_I in Valid_I.
   apply intComp_valid_proj1 in Valid_I.
   iFrame "∗ %".
   iApply "HClose".
   iFrame.
   iPureIntro. repeat (split; auto).
 Qed.


 Lemma root_inFP {A} (b: gmap Key KValue → A → iPropI Σ) (Q : A -d> iProp Σ)
   γ_I γ_f γ_k γ_g γ_m γ_n (p p1 css : val) nr r (Heq_p_null: p = nullval):
   atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗
     md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r ⊢
     (|={⊤}=> ∃ p2 l2, ⌜is_pointer_or_null p2 ∧ is_pointer_or_null l2 /\ (0 <= f r < size)%Z⌝ ∧
                        inFP γ_f r p2 l2 ∗
     atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗
     md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r).
 Proof.
   iIntros "(AU & Hmd)".
   iMod "AU" as (m) "(Hm & HClose)".
   iDestruct "Hm" as (I md r') "Hcssi".
   iDestruct "Hcssi" as "(%Hznth & (%Hg & (HI & (Hk & Hown_m & Hown_nodes))) &
(Hml & (Hl_idx & HNF & Hn)))".
   destruct Hznth as (Hznth & ?).
   rewrite {1} /md_entry_rep.
   rewrite -> if_true; auto.
   iDestruct "Hmd" as "(%Hc & Hml1 & Hmin & Hmax & Hnode &
                      HfI & Hfk & Hfm & His & Hfn & Hf_css)".
   iDestruct (own_valid_2 γ_n (●E r' : excl_authR (leibnizO val)) (◯E r)
                 with "[$Hn] [$Hfn]") as %Hownr%@excl_auth_agree_L.
   destruct Hg as ((? & Hdomr & ?) & ?).
   subst r' p.
   iMod (ghost_snapshot_fp γ_f I md r with "[$Hown_nodes]")
       as "(Hown_nodes & HinFP1)"; auto.
   iDestruct "HinFP1" as (p2 l2) "(HinFP1 & %Hc1)".
   destruct Hc1 as (? & ? & ? & ? & Hlen).
   rewrite Hznth in Hlen.
   iAssert (md_entry_rep γ_I γ_k γ_m γ_n p1 nullval nr css r)
       with "[$Hml1 $Hmin $Hmax $Hnode $HfI $Hfk $Hfm $His $Hfn $Hf_css]" as "Hmd"; auto.
   iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css)
       with "[$HI $Hk $Hown_m $Hml $Hl_idx $Hn $Hown_nodes $HNF]"as "HCSS"; auto.
   iMod ("HClose" with "HCSS").
   iExists p2, l2.
   iFrame.
   iModIntro.
   iPureIntro. repeat (split; auto).
 Qed.

 Lemma release_lock {A} (b: gmap Key KValue → A → iPropI Σ) (Q : A -d> iProp Σ)
   γ_I γ_f γ_k γ_g γ_m γ_n (p p1 l css : val) nr r:
   inFP γ_f p p1 l ∗ atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗
   md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r ⊢
   (atomic_shift (λ _ : (), md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r ∗
                              inv_for_lock l (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r))
      (⊤ ∖ ∅) ∅ (λ _ _ : (), inv_for_lock l (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r) ∗ emp)
       (λ _ : (), atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q)).
  Proof.
    iIntros "(#HinFP & AU & Hmd)".
    unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
    iMod "AU" as (m) "(Hm & HClose)".
    iIntros "!>".
    iExists tt.
    iDestruct "Hm" as (I md r') "Hcssi".
    iDestruct "Hcssi" as "(%Hznth & (Hg & (HI & (Hk & Hown_m & Hown_nodes))) &
(Hml & (Hl_idx & HNF & Hn)))".
    rewrite {1} /md_entry_rep.
    destruct (decide (p = nullval)); subst.
    + rewrite -> if_true; auto.
      iDestruct "Hmd" as "(%Hc & Hml1 & Hmin & Hmax & Hnode &
              HfI & Hfk & Hfm & His & Hfn & Hf_css)".
      iDestruct (own_valid_2 γ_n (●E r' : excl_authR (leibnizO val)) (◯E r)
                  with "[$Hn] [$Hfn]") as %Hownr%@excl_auth_agree_L.
      rewrite Hownr.
      iDestruct (in_tree_inv' _ _ _ _ _ _ I m md nullval p1 l nr css r
         with "[$Hml1 $Hmin $Hmax $Hnode $HfI $Hfk $Hfm $His $Hfn $Hf_css $Hg $HI $Hk $Hown_m
          $Hown_nodes $Hml $Hl_idx $HNF $Hn]") as "(Hmd & Hinv & Hinv1)"; auto.
      iFrame "Hmd Hinv".
      iSplit.
      { iIntros "(Hmd & Hinv)".
        iSpecialize ("Hinv1" with "Hinv").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "Hinv1"); auto.
        iFrame.
      }
      iIntros (_) "(Hinv & _)".
      iSpecialize ("Hinv1" with "Hinv").
      iDestruct "HClose" as "(HClose & _)".
      iSpecialize ("HClose" with "Hinv1"); auto.
    + rewrite -> if_false; auto.
      iDestruct "Hmd" as "(%Hc & Hml1 & Hmin & Hmax & Hnode & HfI & Hfk & Hfm & _)".
      iAssert(md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r') with "[$Hml1 $Hmin $Hmax
            $Hnode $HfI $Hfk $Hfm]" as "Hmd"; try rewrite -> if_false; auto.
      iDestruct (in_tree_inv' _ _ _ _ _ _ I m md p p1 l nr css r' with "[$Hmd $Hg $HI
            $Hk $Hown_m $Hown_nodes $Hml $Hl_idx $HNF $Hn]") as "(Hmd & Hinv & Hinv1)"; auto.
      iDestruct (inv_lock2 r' r nr with "[$Hmd $Hinv]") as "(Hmd & Hinv)"; auto.
      iFrame "Hmd Hinv".
      iSplit.
      { iIntros "(Hmd & Hinv)".
        iDestruct (inv_lock1 r r r' nr nr nr with "[$Hmd $Hinv]") as "(Hmd & Hinv)"; auto.
        iFrame "Hmd".
        iSpecialize ("Hinv1" with "Hinv").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "Hinv1"); auto.
      }
      iIntros (_) "(Hinv & _)".
      iDestruct (inv_lock3 r r' with "Hinv") as "Hinv"; auto.
      iSpecialize ("Hinv1" with "Hinv").
      iDestruct "HClose" as "(HClose & _)".
      iSpecialize ("HClose" with "Hinv1"); auto.
  Qed.
  
  Lemma acquire_lock {A} (s: option (val -> NodeR -> A)) (Q : discrete_fun (λ _ : A, mpred))
    γ_I γ_f γ_k γ_g γ_m γ_n (p p1 l c : val) :
    inFP γ_f p p1 l ∗ atomic_shift (λ C : gmap Key KValue, CSS γ_I γ_f γ_k γ_g γ_m γ_n C c) ⊤ ∅
      (λ (C : gmap Key KValue) (_ : A), CSS γ_I γ_f γ_k γ_g γ_m γ_n C c ∗ emp) Q
      ⊢ atomic_shift (λ R : mpred, inv_for_lock l R) (⊤ ∖ ∅) ∅
      (λ (R : mpred) (_ : ()), (inv_for_lock l R ∗ R) ∗ emp)
      (λ _ : (), ∃ (r : val) (nr : NodeR), ⌜is_pointer_or_null r⌝ ∧ inFP γ_f p p1 l ∗
            (match s with
             | None => atomic_shift (λ C : gmap Key KValue, CSS γ_I γ_f γ_k γ_g γ_m γ_n C c) ⊤ ∅
                        (λ (C : gmap Key KValue) (_ : A), CSS γ_I γ_f γ_k γ_g γ_m γ_n C c ∗ emp) Q
             | Some f => Q (f r nr)
             end) ∗ md_entry_rep γ_I γ_k γ_m γ_n p1 p nr c r).
  Proof.
    iIntros "(#HinFP & AU)".
    unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
    iMod "AU" as (m) "(Hm & HClose)".
    iPoseProof (in_tree_inv with "[$HinFP $Hm]") as "InvLock"; auto.
    iDestruct "InvLock" as "(InvLock & _)".
    iDestruct "InvLock" as (r nr) "(HInv1 & HInv2)".
    iExists _.
    iFrame "HInv1".
    iModIntro.
    iSplit; iFrame.
    iIntros "HInv1".
    iSpecialize ("HInv2" with "HInv1").
    iDestruct "HClose" as "(HClose & _)".
    iSpecialize ("HClose" with "HInv2"); auto.
    iIntros (m') "((HInv1 & Hmd) & _)".
    iDestruct "Hmd" as "(Hc & Hml_p & Hmin & Hmax & HI & Hk & Hm & Hownr & Hrest)".
    iSpecialize ("HInv2" with "HInv1").
    iAssert (∃ (r0 : val)(nr0 : NodeR),
                ⌜is_pointer_or_null r0⌝ ∧ md_entry_rep γ_I γ_k γ_m γ_n p1 p nr0 c r0)
      with "[$Hc $Hml_p $Hmin $Hmax $HI $Hk $Hm $Hownr Hrest]" as "Hmd"; auto.
    { destruct (eq_dec p nullval); subst.
      + iExists r.
        rewrite -> ! if_true; auto.
        iDestruct "Hrest" as "(%His & Hfn & Hf_css)".
        iFrame. iPureIntro. split; auto.
      + iExists nullval. rewrite -> ! if_false; auto.
    }
    iDestruct "Hmd" as (r1 nr1) "(%His & Hmd)".
    iExists r1, nr1.
    iFrame "HinFP Hmd %".
    destruct s; iApply "HClose"; iFrame.
 Qed.

  Lemma get_inFP_not_null {A} (b: gmap Key KValue → A → mpred) (Q : discrete_fun (λ _ : A, mpred))
    γ_I γ_f γ_k γ_g γ_m γ_n p p1 nr r c x q (Hne_p_null: p <> nullval)
    (Hin_inset: in_inset Node_EqDecision Node_countable Key x (Ip nr) p)
    (Hin_outset: in_outset Node_EqDecision Node_countable Key x (Ip nr) q):
    atomic_shift (λ C : gmap Key KValue, CSS γ_I γ_f γ_k γ_g γ_m γ_n C c) ⊤ ∅ b Q ∗
     md_entry_rep γ_I γ_k γ_m γ_n p1 p nr c r
    ⊢ |={⊤}=> ∃ q1 l : val,
    atomic_shift (λ C : gmap Key KValue, CSS γ_I γ_f γ_k γ_g γ_m γ_n C c) ⊤ ∅ b Q ∗
      md_entry_rep γ_I γ_k γ_m γ_n p1 p nr c r ∗ inFP γ_f q q1 l ∧
      ⌜is_pointer_or_null q /\ is_pointer_or_null q1 ∧ is_pointer_or_null l ∧ (0 ≤ f q < size)%Z⌝.
  Proof.
    iIntros "(AU & Hmd)".
    iMod "AU" as (m) "(Hm & HClose)".
    rewrite {1} /CSS.
    iDestruct "Hm" as (I md r1) "(%Hc & Hglob & Hml & Hidx & HNF & Hown)".
    iAssert (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr c r1) with "[Hmd]" as "Hmd".
    { rewrite /md_entry_rep !if_false; auto. }
    iAssert (CSSi γ_I γ_f γ_k γ_g γ_m γ_n r1 m c I md)
      with "[$Hglob $Hml $Hidx $HNF $Hown]" as "HCSSi"; auto.
    destruct Hc as (Hlen & ?).
    iMod (ghost_update_step with "[$HCSSi $Hmd]") as "Hrest"; auto.
    iDestruct "Hrest" as (q1 l) "(HCSS & Hmd & HinFP & %Hc)".
    
    iAssert (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr c r) with "[Hmd]" as "Hmd".
    { rewrite /md_entry_rep !if_false; auto. }
    iExists q1, l.
    iFrame "∗ %".
    by iApply "HClose".
  Qed.

  Lemma get_inFP_null {A} (b: gmap Key KValue → A → mpred) (Q : discrete_fun (λ _ : A, mpred))
    γ_I γ_f γ_k γ_g γ_m γ_n c:
    atomic_shift (λ C : gmap Key KValue, CSS γ_I γ_f γ_k γ_g γ_m γ_n C c) ⊤ ∅ b Q
      ⊢ |={⊤}=> atomic_shift (λ C : gmap Key KValue, CSS γ_I γ_f γ_k γ_g γ_m γ_n C c) ⊤ ∅ b Q ∗
    ∃ q1 l : val, inFP γ_f nullval q1 l ∧
                    ⌜is_pointer_or_null q1 ∧ is_pointer_or_null l ∧ (0 ≤ f nullval < size)%Z⌝.
  Proof.
    iIntros "AU".
    iMod "AU" as (m) "(Hm & HClose)".
    rewrite {1} /CSS /CSSi.
    iDestruct "Hm" as (I md r1) "(%Hc & Hglob & Hml & Hidx & HNF & Hown)".
    iDestruct "Hglob" as "(%Hglob & HauthI & Hauthk & Hauthm & Hown_nodes)".
    destruct Hc as (HZlen & Hnull_in_domI).
    iMod (ghost_snapshot_fp γ_f I md nullval with "[$Hown_nodes]")
      as "(Hown_nodes & HinFP)"; auto.
    iDestruct "HinFP" as (q lk) "(HinFP & %Hc1)".
    destruct Hc1 as (? & ? & ? & ? & Hzth).
    rewrite HZlen in Hzth.
    iAssert (∃ q1 l : val, inFP γ_f nullval q1 l ∧ ⌜is_pointer_or_null q1 ∧
          is_pointer_or_null l ∧ (0 ≤ f nullval < size)%Z⌝) with "[$HinFP]" as "Hc".
    { iPureIntro. split; auto. }
    iFrame.
    iDestruct "HClose" as "(HClose & _)".
    iApply "HClose".
    iFrame.
    iPureIntro.
    repeat (split; auto).
  Qed.
  
  (* root is in footprint *)
  Lemma ghost_update_root γ_I γ_f γ_k γ_g γ_m γ_n r I C md css:
    CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I md
    ==∗ ∃ pr lkr, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css ∗ inFP γ_f r pr lkr ∧
                    ⌜is_pointer_or_null r /\ is_pointer_or_null pr /\
                    is_pointer_or_null lkr /\ Znth (f r) md = pr /\ (0 <= f r < size)%Z⌝.
  Proof.
    iIntros "Hcss".
    iDestruct "Hcss" as "(%Hc & Hglob & Hml & Hidx & HNF & Hn)".
    iDestruct "Hglob" as "(%Hglob & HaI & Hak & Ham & Hown_nodes)".
    destruct Hglob as (Hglob & Hr).
    destruct Hc as (Hc & Hnull_in_domI).
    specialize ((globalinv_root_fp I r) Hglob); intros.
    rewrite /nodeFull (big_sepS_elem_of_acc _ (dom I) r); auto.
    iMod (ghost_snapshot_fp _ _ _ r with "[$Hown_nodes]") as "(Hown & HinFP)"; auto.
    iDestruct "HNF" as "(Hn1 & HNF)".
    iDestruct "HinFP" as (pr lkr) "(HinFP & %Hc1)".
    destruct Hc1 as (? & ? & ? & ? & Hlen).
    iModIntro.
    iExists pr, lkr.
    iFrame.
    repeat (iSplit; auto).
    by iApply "HNF".
    iPureIntro.
    rewrite Hc in Hlen.
    repeat (split; auto).
  Qed.

  Lemma unify_root γ_I γ_f γ_k γ_g γ_m γ_n r1 r p1 pnN nr I C md c (Heq_null: pnN = nullval):
    CSSi γ_I γ_f γ_k γ_g γ_m γ_n r1 C c I md ∗
      md_entry_rep γ_I γ_k γ_m γ_n p1 pnN nr c r ⊢ ⌜r = r1⌝.
  Proof.
    iIntros "(HCSSi & Hmd)".
    rewrite /CSSi.
    iDestruct "HCSSi" as "(%Hc & ? & ? & ? & ? & Hown)".
    rewrite /md_entry_rep.
    rewrite -> if_true; auto.
    iDestruct "Hmd" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & Hown1 & ?)".
    iDestruct (own_valid_2 γ_n (●E r1 : excl_authR (leibnizO val)) (◯E r)
                with "[$Hown] [$Hown1]") as %Hownr%@excl_auth_agree_L; try done.
  Qed.

  Lemma in_out_nullval_node {A} (b: gmap Key KValue → A → mpred) (Q : A -d> mpred)
   γ_I γ_f γ_k γ_g γ_m γ_n (p p1 css : val) nr r x
   (HKS: x ∈ KS)
   (Heq_null: p = nullval) (Heq_r_null: r = nullval):
   atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗
     md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r ⊢
     (|={⊤}=> ⌜x ∉ dom (Cp nr) /\ in_inset _ _ _ x (Ip nr) p
             ∧ ¬ in_outsets _ _ _ x (Ip nr) ∧ ✓ Ip nr⌝ ∧
     atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗
     md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r).
 Proof.
   iIntros "(AU & Hmd)".
   iMod "AU" as (m) "(Hm & HClose)".
   iDestruct "Hm" as (I md r') "Hcssi".
   simpl.
   iDestruct "Hcssi" as "(%Hznth & (%Hglob & (HaI & (Hk & Hown_m & Hown_nodes))) &
(Hml1 & (Hl_idx & HNF & Hown)))".
   destruct Hznth as (Hznth & ?).
   simpl.
   rewrite {1} /md_entry_rep.
   rewrite -> if_true; auto.
   iDestruct "Hmd" as "(%Hc_md & Hml & Hmin & Hmax & Hn & HfI & Hfk & Hfm & % & Hown1 & Hf)".
   iDestruct (own_valid_2 γ_n (●E r' : excl_authR (leibnizO val)) (◯E r)
                with "[$Hown] [$Hown1]") as %->%@excl_auth_agree_L; try done.
    destruct Hglob as ((Hv & Hr_in_domI & Hclosed & Hkey) & Hrc).
    pose proof Heq_r_null as Heq_r_null'.
    apply Hrc in Heq_r_null.
    destruct Heq_r_null as (HdomI & Hmap).
    destruct Hc_md as (? & ? & ? & ? & ? & ? & HdomIp).
    iDestruct (own_valid_2 γ_m (●(Excl <$> m) : keymap_authR _ _)
                 (◯ (Excl <$> Cp nr)) with "[$Hown_m] [$Hfm]") as %Hownr.
    move: Hownr => /auth_both_valid_discrete [Hsub _].
    rewrite lookup_included in Hsub.
    specialize (Hsub x).
    rewrite ! lookup_fmap Hmap lookup_empty in Hsub.
    assert (x ∉ dom (Cp nr)) as Hnin_x_Cp.
    {
      destruct (Cp nr !! x) eqn: E; auto.
      rewrite E in Hsub.
      rewrite option_included in Hsub.
      destruct Hsub as [Hcontra | (? & ? & ? & Hcontra & ?)]; try easy.
      apply not_elem_of_dom in E; auto.
    } 
    iDestruct (flowEq with "[$HaI $HfI]") as %HflowEq.
    { iPureIntro. repeat split; auto; subst; set_solver. }
    assert (x ∉ dom (Cp nr) /\ in_inset _ _ _ x (Ip nr) p /\
              ¬ in_outsets _ _ _ x (Ip nr) ∧ ✓ Ip nr)
      as Hin_inset; auto.
    { specialize (Hkey x HKS).
      rewrite /in_inset /inset -HflowEq in Hkey.
      rewrite /closed /outset in Hclosed.
      rewrite /in_inset /in_outsets /in_outset.
      repeat split; subst; auto.
      set_solver. 
      rewrite HflowEq; auto.
    }
    iAssert (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r)
      with "[$Hml $Hmin $Hmax $Hn $HfI $Hfk $Hfm Hown1 Hf]" as "H_md".
    { rewrite -> if_true; auto. iFrame "% Hown1 Hf". iPureIntro. repeat (split; auto). }
    iFrame "% ∗".
    iApply "HClose".
    iFrame.
    iPureIntro. repeat (split; auto).
 Qed.

 Lemma ltree_imply γ_I γ_k γ_f γ_m γ_n p1 p css new_node (Hne: p <> nullval):
   ltree γ_I γ_k γ_f γ_m γ_n p1 p css nullval ⊢ 
     ltree γ_I γ_k γ_f γ_m γ_n p1 p css new_node.
 Proof.
   iIntros "Hlt".
   rewrite /ltree.
   iDestruct "Hlt" as (lsh lock nr) "(%Hc & Hf & HinFP & Hinv)".
   iDestruct "Hinv" as (b) "(Htm & Hmd)".
   destruct b.
   - iExists _, _, nr. iFrame.
     iSplit; auto.
   - iExists _, _, nr. iFrame.
     iSplit; auto.
     rewrite /md_entry_rep.
     rewrite -> ! if_false; auto.
 Qed.

End give_up.
Global Hint Resolve md_entry_rep_pred_exclusive : core.
