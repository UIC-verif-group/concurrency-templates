Set Warnings "-abstract-large-number, -redundant-canonical-projection".
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
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.
Require Import tmpl.flows_ora.
Require Import tmpl.frac.
Require Import tmpl.keyset_ra_ora.
Require Export tmpl.data_struct.
Require Export tmpl.template_class.
Require Export tmpl.coarse_lib.
Require Export tmpl.coarse. (* AST of coarse.c *)

Section verif_coarse_grained_template.
  Existing Instance coarse_lib.CompSpecs.
  Definition Vprog : varspecs. mk_varspecs prog. Defined.

  Context `{N: NodeRep } `{EqDecision K} `{Countable K}.
  Context `{!cinvG Σ, atom_impl : !atomic_int_impl (Tstruct _atom_int noattr), !flowintG Σ,
        !nodesetG Σ, !nodemapG Σ, !keymapG Σ, !keysetG Σ, !one_shotG Σ}.

  #[local] Program Instance specific_template : Template := {
      NodeRt := NodeR;
      CSSt := CSS;
      md_entry_rep_t := nodeFull2; (* now md_entry_rep_t is nodeFull rather than md_entry_rep *)
      belongs_t := belongs;
      is_root_t := is_root;
      Ip_of := Ip;
      Cp_of := Cp;
    }.

  Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec; surely_malloc_spec;
                             hash_spec; insertOp_spec; findnext_spec;  get_value_spec]).

  Lemma shot_duplicate γ_n r:
    own γ_n (inG0 := one_shot_inG) (Cinr (to_agree r)) ⊢
      own (inG0 := one_shot_inG) γ_n (Cinr (to_agree r)) ∗
      own (inG0 := one_shot_inG) γ_n (Cinr (to_agree r)).
  Proof. by rewrite -own_op -Cinr_op agree_idemp. Qed.

  Arguments Qp.div : simpl never.

  Instance cce : change_composite_env tmpl.template_class.CompSpecs coarse_lib.CompSpecs.
  Proof.
    make_cs_preserve tmpl.template_class.CompSpecs coarse_lib.CompSpecs.
  Defined.

  Instance cce2 : change_composite_env (@DS_compspecs Σ VSTGS0 N) coarse_lib.CompSpecs.
  Proof.
    make_cs_preserve (@DS_compspecs Σ VSTGS0 N) coarse_lib.CompSpecs.
  Defined.
  
  Lemma get_root: semax_body Vprog Gprog f_get_root get_root_spec.
  Proof.
    start_function.
    set (AS := atomic_shift _ _ _ _ _ ).
    set Q1:= fun (v : val ) => AS.
    gather_SEP AS.
    (* gain inFP γ_f nullval q1 l, before calling lookup_md *)
    viewshift_SEP 0 (AS ∗ ∃ l, inFP γ_f nullval nullval l ∧ ⌜is_pointer_or_null l⌝).
    { go_lowerx. rewrite bi.sep_emp. iApply get_inFP_null. }
    Intros l.
    gather_SEP AS (inFP γ_f _ _ _).
    viewshift_SEP 0 (AS ∗ inFP γ_f nullval nullval l ∗
         ∃ lsh : share, ⌜readable_share lsh⌝ ∧
              field_at (cs := coarse_lib.CompSpecs) lsh t_struct_css [StructField _lock] l c).
    { go_lowerx. rewrite bi.sep_emp. iApply lock_alloc. }
    Intros.
    forward.
    forward_call acquire_inv_atomic (l, ∃ (r : val) nr,
          ⌜is_pointer_or_null r⌝ ∧ inFP γ_f nullval nullval l ∗ AS ∗
                                     nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr c r).
    { iIntros "(AU & HinFP & Hf & Hgv)".
      iCombine "HinFP AU" as "HAU".
      iCombine "Hgv Hf" as "Hrst".
      iStopProof.
      apply bi.sep_mono; [|cancel].
      iIntros "(#HinFP & AU)".
      rewrite /rev_curry /=.
      unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
      iMod "AU" as (m) "(Hm & HClose)".
      iPoseProof (in_tree_inv with "[$HinFP $Hm]") as "InvLock"; auto.
      iDestruct "InvLock" as (r nr) "((% & %) & HInv1 & HInv2)".
      iExists _.
      iFrame "HInv1".
      iModIntro.
      iSplit; iFrame.
      iIntros "HInv1".
      iSpecialize ("HInv2" with "HInv1").
      iDestruct "HClose" as "(HClose & _)".
      iSpecialize ("HClose" with "HInv2"); auto.
      iIntros (m') "((HInv1 & Hmd) & _)".
      iSpecialize ("HInv2" with "HInv1").
      iMod ("HClose" with "HInv2").
      iExists r, nr.
      by iFrame "HinFP ∗".
    }
    simpl.
    Intros ab.
    destruct ab as (r & nr).
    simpl.
    sep_apply nodeFull_extract.
    Intros.
    rewrite {1} /md_entry_rep.
    rewrite -> (if_true _ (eq_dec nullval nullval)); auto.
    Intros.
    forward.
    forward.
    gather_SEP AS (if eq_dec r nullval then _ else _ ).
    (* gain inFP γ_f r p1 l1 for post condition *)
    viewshift_SEP 0 (∃ l1,
          ⌜is_pointer_or_null r ∧ is_pointer_or_null l1⌝ ∧
            AS ∗
              (if eq_dec r nullval  then own (inG0 := one_shot_inG) γ_n (Cinl (1 / 2)%Qp) 
               else own (inG0 := one_shot_inG) γ_n (Cinr (to_agree r))) ∗ inFP γ_f r nullval l1).
    {
      go_lowerx. rewrite bi.sep_emp.
      iIntros "(AU & Hown1)".
      iMod "AU" as (m) "(Hm & HClose)".
      simpl.
      rewrite {1} /CSS /CSSi.
      iDestruct "Hm" as (I r1 ???) "(%Hc & Hglob & Hml & Hf & Hinv & Hml1 & Hown)".
      destruct (eq_dec r1 nullval); destruct (eq_dec r nullval); subst; auto.
      2 : { iDestruct (shot_not_pending with "[$Hown $Hown1]") as %[]. }
      2 : { iDestruct (shot_not_pending with "[$Hown $Hown1]") as %[]. }
      * iMod (ghost_update_root with "[$Hglob $Hml $Hf $Hinv $Hml1 $Hown]") as "HCSSi"; auto.
        iDestruct "HCSSi" as (lr) "(HCSSi & HinFP & %Hc1)".
        subst.
        iFrame.
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "HCSSi").
        iMod ("HClose").
        by iFrame "HClose".
      * iDestruct (shot_agree with "[$Hown $Hown1]") as %->.
        iMod (ghost_update_root with "[$Hglob $Hml $Hf $Hinv $Hml1 Hown]") as "HCSSi"; auto.
        { rewrite ->if_false; auto. }
        iDestruct "HCSSi" as (lr) "(HCSSi & HinFP & %Hc1)".
        iFrame.
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "HCSSi").
        iMod ("HClose").
        by iFrame "HClose".
    }
    Intros l1.
    (* push back lock into invariant *)
    gather_SEP AS (inFP γ_f nullval nullval l) (field_at (cs := CompSpecs) lsh _ _ _ c).
    viewshift_SEP 0 (AS ∗ (inFP γ_f nullval nullval l)).
    { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
    (* end - push back lock into invariant *)
    (* release *)
    destruct (eq_dec r nullval); subst.
    - gather_SEP (node _ _ _) (own γ_I _) (own γ_k _) (own γ_m _) (own γ_n _) (field_at _ _ _ _ _).
      viewshift_SEP 0 (md_entry_rep γ_I γ_k γ_m γ_n nullval nr c nullval).
      { go_lowerx. rewrite bi.sep_emp.
        iIntros "(Hn & HfI & Hfk & Hfm & Hfn & Hf_css)". by iFrame.  
      }
      gather_SEP (md_entry_rep _ _ _ _ _ _ _ _)
        (bi_wand (md_entry_rep _ _ _ _ _ _ _ _) (nodeFull2 _ _ _ _ _ _ _ _ _)).
      sep_apply (bi.wand_elim_r (md_entry_rep γ_I γ_k γ_m γ_n nullval nr c nullval)).
      forward_call release_inv (l, nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr c nullval, AS).
      { rewrite /rev_curry /=. lock_props.
        iIntros "(HNF & HAU & HinFP & HinFP1 & Hgv )".
        iCombine "HAU HinFP HNF" as "?".
        iCombine "HinFP1 Hgv" as "?".
        iStopProof.
        apply bi.sep_mono; [|cancel].
        rewrite /AS -release_lock.
        iIntros "(? & ? & ?)".
        iFrame.
      }
      simpl.
      gather_SEP AS (inFP γ_f _ _ _).
      viewshift_SEP 0 (∃ q1 l, ⌜is_pointer_or_null q1 /\ is_pointer_or_null l⌝ ∧
                                 Q (nullval, q1, l) ∗ inFP γ_f nullval q1 l).
      { go_lowerx; rewrite bi.sep_emp.
        iIntros "(AU & #HinFP)".
        iMod "AU" as (m) "(Hm & HClose)".
        iDestruct "HClose" as "(_ & HClose)".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        by iFrame "HinFP ∗".
      }
      Intros q2 l2.
      forward.
      Exists (nullval, q2, l2).
      entailer !.
    - sep_apply shot_duplicate.
      Intros.
      gather_SEP (node _ _ _) (own γ_I _) (own γ_k _) (own γ_m _) (own γ_n _) (field_at _ _ _ _ _).
      viewshift_SEP 0 (md_entry_rep γ_I γ_k γ_m γ_n nullval nr c r).
      { go_lowerx. rewrite bi.sep_emp.
        iIntros "(Hn & HfI & Hfk & Hfm &Hfn & Hf_css)".
        iFrame. rewrite -> if_false; auto. 
      }
      gather_SEP (md_entry_rep _ _ _ _ _ _ _ _)
        (bi_wand (md_entry_rep _ _ _ _ _ _ _ _) (nodeFull2 _ _ _ _ _ _ _ _ _)).
      sep_apply (bi.wand_elim_r (md_entry_rep γ_I γ_k γ_m γ_n nullval nr c r)).
      forward_call release_inv (l, nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr c r, AS).
      { rewrite /rev_curry /=. lock_props.
        iIntros "(HNF & Hfn & HAU & HinFP & HinFP1 & Hgv )".
        iCombine "HAU HinFP HNF" as "?".
        iCombine "Hfn HinFP1 Hgv" as "?".
        iStopProof.
        apply bi.sep_mono; [|cancel].
        rewrite /AS -release_lock.
        iIntros "(? & ? & ?)".
        iFrame.
      }
      simpl.
      gather_SEP AS (inFP γ_f _ _ _).
      viewshift_SEP 0 (∃ q1 l,
            ⌜is_pointer_or_null q1 /\ is_pointer_or_null l⌝ ∧ Q (r, q1, l) ∗ inFP γ_f r q1 l).
      { go_lowerx; rewrite bi.sep_emp.
        iIntros "(AU & #HinFP)".
        iMod "AU" as (m) "(Hm & HClose)".
        iDestruct "HClose" as "(_ & HClose)".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        by iFrame "HinFP ∗".
      }
      Intros q2 l2.
      forward.
      Exists (r, q2, l2).
      rewrite /is_root_t /= /is_root.
      rewrite -> if_false; auto.
      entailer !.
  Qed.
  
  (** Traverse function proof **)
 
  Definition traverse_inv (γ_I γ_f γ_k γ_g γ_m γ_n : gname)
    (pn p p1 l c : val) (sh : share) (x : Z) gv AS : environ -> mpred :=
    ∃ (pnN pnP: Node) (pn1 l1 : val) (lshN: share) (nr1 : NodeR) (r1 : val),
      PROP (is_pointer_or_null pnN; is_pointer_or_null l1)
        LOCAL (temp _status (vint 2); temp _pn__2 pn; temp _c c; temp _x (vint x);
               gvars gv)
        SEP (⌜pnN <> nullval /\ (* (0 ≤ f pnN < size)%Z /\ *) readable_share lshN /\
               in_inset _ _ _ x (Ip nr1) pnN⌝ ∧ inFP γ_f pnN pn1 l1;
             nodeFull2 γ_I γ_k γ_m γ_n pn1 pnN nr1 c r1;
             data_at sh (t_struct_pn) (pnP, pnN) pn; inFP γ_f p p1 l; AS; mem_mgr gv).

  Definition traverse_inv_NF
    (γ_I γ_f γ_k γ_m γ_n : gname) pn pnN ptn1 lock (nr1 : NodeR) r c x :=
    ∃ pnN', ⌜pnN ≠ nullval /\ x ∉ dom (Cp nr1) /\
              is_pointer_or_null pnN /\ is_pointer_or_null lock /\ 
      in_inset _ _ _ x (Ip nr1) pnN /\ ¬ in_outsets _ _ _  x (Ip nr1) /\
      (pnN ≠ nullval -> belongs x nr1) /\ ✓ (Ip nr1) /\ (pnN = nullval -> r = nullval)⌝ ∧
              inFP γ_f pnN ptn1 lock ∗ data_at Ews (t_struct_pn) (pnN, pnN') pn ∗
                nodeFull2 γ_I γ_k γ_m γ_n ptn1 pnN nr1 c r.
  
  Definition traverse_inv_F
    (γ_I γ_f γ_k γ_m γ_n : gname) pn pnN ptn1 lock (nr1 : NodeR) r c x :=
    ⌜ pnN ≠ nullval /\ (dom (Cp nr1) = {[x]}) /\
      is_pointer_or_null pnN /\ is_pointer_or_null lock /\ 
      in_inset _ _ _ x (Ip nr1) pnN /\ 
      ¬ in_outsets _ _ _  x (Ip nr1) /\ (pnN ≠ nullval -> belongs x nr1) /\
      ✓ (Ip nr1) /\ (pnN = nullval -> r = nullval)⌝ ∧
      inFP γ_f pnN ptn1 lock ∗ data_at Ews (t_struct_pn) (pnN, pnN) pn ∗ 
        nodeFull2 γ_I γ_k γ_m γ_n ptn1 pnN nr1 c r. 
  
  Ltac change_compspecs' cs cs' :=
  lazymatch goal with
  | |- context [data_at(cs := cs') ?sh ?t ?v1] => erewrite (data_at_change_composite(cs_from := cs')(cs_to := cs) (CCE := _) sh t); [| apply JMeq_refl | prove_cs_preserve_type]
  | |- context [field_at(cs := cs') ?sh ?t ?gfs ?v1] => erewrite (field_at_change_composite(cs_from := cs')(cs_to := cs) (CCE := _) sh t gfs); [| apply JMeq_refl | prove_cs_preserve_type]
  | |- context [data_at_(cs := cs') ?sh ?t] => erewrite (data_at__change_composite(cs_from := cs')(cs_to := cs) (CCE := _) sh t); [| prove_cs_preserve_type]
  | |- context [field_at_(cs := cs') ?sh ?t ?gfs] => erewrite (field_at__change_composite(cs_from := cs')(cs_to := cs) (CCE := _) sh t gfs); [| prove_cs_preserve_type]
  | |- _ => 
    match goal with 
  | |- context [?A cs'] => 
     change_compspecs_warning A cs cs';
         change (A cs') with (A cs)
  | |- context [?A cs' ?B] => 
     change_compspecs_warning A cs cs';
         change (A cs' B) with (A cs B)
  | |- context [?A cs' ?B ?C] => 
     change_compspecs_warning A cs cs';
         change (A cs' B C) with (A cs B C)
  | |- context [?A cs' ?B ?C ?D] => 
     change_compspecs_warning A cs cs';
         change (A cs' B C D) with (A cs B C D)
  | |- context [?A cs' ?B ?C ?D ?E] => 
     change_compspecs_warning A cs cs';
         change (A cs' B C D E) with (A cs B C D E)
  | |- context [?A cs' ?B ?C ?D ?E ?F] => 
     change_compspecs_warning A cs cs';
         change (A cs' B C D E F) with (A cs B C D E F)
   end
 end.

  Lemma traverse_global_lock: semax_body Vprog Gprog f_traverse traverse_spec.
  Proof.
    start_function.
    rewrite /is_root_t /= /is_root.
    (* change_compspecs' cs cs'. *)
    set (AS := atomic_shift _ _ _ _ _ ).
    set Q1:= fun (v : val ) => AS.
    forward.
    gather_SEP AS (inFP γ_f _ _ _).
    viewshift_SEP 0 (AS ∗ inFP γ_f pnN nullval l ∗ ∃ lsh : share, ⌜readable_share lsh⌝ ∧
               field_at (cs := coarse_lib.CompSpecs) lsh t_struct_css [StructField _lock] l c).
    { go_lowerx. rewrite bi.sep_emp. iApply lock_alloc. }
    Intros lsh.
    set cs := coarse_lib.CompSpecs.
    set cs' := template_class.CompSpecs.
    change_compspecs' cs cs'.
    forward.
    clear dependent cs'.
    rewrite /cs.
    forward_call acquire_inv_atomic (l, ∃ (r : val) nr, ⌜is_pointer_or_null r⌝ ∧
         inFP γ_f pnN nullval l ∗ AS ∗ nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr c r).
    { iIntros "(AU & HinFP & Hf & Hd & Hgv)".
      iCombine "HinFP AU" as "HAU".
      iCombine "Hgv Hf Hd" as "Hrst".
      iStopProof.
      apply bi.sep_mono; [|cancel].
      iIntros "(#HinFP & AU)".
      rewrite /rev_curry /=.
      unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
      iMod "AU" as (m) "(Hm & HClose)".
      iPoseProof (in_tree_inv with "[$HinFP $Hm]") as "InvLock"; auto.
      iDestruct "InvLock" as (r nr) "((% & %) & HInv1 & HInv2)".
      iExists _.
      iFrame "HInv1".
      iModIntro.
      iSplit; iFrame.
      iIntros "HInv1".
      iSpecialize ("HInv2" with "HInv1").
      iDestruct "HClose" as "(HClose & _)".
      iSpecialize ("HClose" with "HInv2"); auto.
      iIntros (m') "((HInv1 & Hmd) & _)".
      iSpecialize ("HInv2" with "HInv1").
      iMod ("HClose" with "HInv2").
      iExists r, nr.
      by iFrame "HinFP ∗".
    }
    simpl.
    Intros nrv.
    destruct nrv as (r & nr).
    forward.
    assert_PROP (is_pointer_or_null r). entailer !.
    (* if(!pn->n) *)
    forward_if (PROP ( )
      LOCAL (temp _status (vint 2); gvars gv; temp _c c; temp _pn__2 pn; temp _x (vint x))
      SEP (AS; mem_mgr gv; ∃ (n : Node) (l: val) (nr : NodeR), ⌜n <> nullval /\ is_pointer_or_null n /\
        is_pointer_or_null l (* /\ (0 ≤ f n < size)%Z *) ⌝ ∧
            inFP γ_f n nullval l ∗ data_at Ews t_struct_pn (nullval, n) pn ∗
            nodeFull2 γ_I γ_k γ_m γ_n nullval n nr c r ∗
      (if eq_dec n nullval then emp else own (inG0 := one_shot_inG) γ_n (Cinr (to_agree n))))).
    - destruct (decide (pnN = nullval)); subst.
      entailer !.
      rewrite -> if_false; auto.
      sep_apply (nodeFull_switch_node γ_I γ_k γ_m γ_n nullval nr c r pnN nullval).
      set dummy := (own γ_n (Cinr (to_agree pnN)) ∗ _).
      sep_apply (bi.and_elim_r dummy (valid_pointer pnN)).
      auto with valid_pointer.
    - sep_apply nodeFull_extract.
      Intros.
      unfold md_entry_rep at 1.
      rewrite -> if_true; auto.
      Intros.
      (* node *r = c->root; *)
      forward.
      (* hash (r) *)
      forward_call (r).
      forward.
      forward_call (pnN).
      forward_if.
      + (* CONTINUE *)
        subst pnN. (* pnN = nullval *)
        (* obtain r = nullval *)
        destruct H14 as (Hfrange & Hrep).
        apply repr_inj_signed, f_injective in H13; auto.
        (* push back lock into invariant *)
        gather_SEP AS (inFP γ_f nullval nullval l)
          (field_at (cs := CompSpecs) _ _ [StructField _lock] _ c).
        viewshift_SEP 0 (AS ∗ (inFP γ_f nullval nullval l)).
        { go_lowerx. rewrite bi.sep_emp. iApply push_lock_back; auto. }
        (* end - push back lock into invariant *)        
        Intros.
        rewrite -> if_true; auto.
        gather_SEP (node _ _ _) (own γ_I _) (own γ_k _) (own γ_m _) (own γ_n _)
          (field_at _ _ _ _ _).
        simpl.
        viewshift_SEP 0 (md_entry_rep γ_I γ_k γ_m γ_n nullval nr c r).
        { go_lowerx. rewrite bi.sep_emp.
          iIntros "(Hn & HfI & Hfk & Hfm & Hfn & Hf_css)".
          iFrame.
          rewrite -> if_true; auto.
        }
        gather_SEP AS (inFP γ_f nullval nullval l).
        Intros.
        gather_SEP AS (md_entry_rep γ_I γ_k γ_m γ_n nullval nr c r).
        viewshift_SEP 0 (⌜x ∉ dom (Cp nr) /\ in_inset _ _ _ x (Ip nr) nullval ∧
                           ¬ in_outsets _ _ _ x (Ip nr) ∧ ✓ Ip nr⌝ ∧
                           AS ∗ (md_entry_rep γ_I γ_k γ_m γ_n nullval nr c r)).
        { go_lowerx; rewrite bi.sep_emp -in_out_nullval_node; auto. }
        Intros.
        gather_SEP AS (inFP _ _ _ _).
        viewshift_SEP 0 (Q (CNT, nullval, nullval, l, nr, r) ∗ inFP γ_f nullval nullval l).
        { go_lowerx; rewrite bi.sep_emp.
          iIntros "(AU & #HinFP)".
          iMod "AU" as (m) "(Hm & HClose)".
          iDestruct "HClose" as "(_ & HClose)".
          iMod ("HClose" with "[Hm]") as "Hm".
          iFrame "Hm". by iFrame "HinFP ∗".
        }
        forward.
        (* return CONTINUE; *)
        (* Q (CNT, nullval, pr, lr, nr0, r0) *)
        Exists (CNT, nullval, nullval, l, nr, nullval).
        Exists nullval.
        rewrite /md_entry_rep_t /=.
        set cs' := template_class.CompSpecs.
        change_compspecs' cs cs'.
        entailer !.
        iIntros "(H1 & H2)".
        iSpecialize ("H2" with "H1").
        iFrame.
      + (*obtain r <> nullval *)
        destruct H14 as (Hfrange & Hrep).
        apply repr_neq_e in H13; auto.
        assert (r <> nullval) as Hne_r_null.
        { intros Hcontra. subst r pnN. easy. }
        (* push back lock into invariant *)
        gather_SEP AS (inFP γ_f pnN _ _) (field_at _ _ [StructField _lock] _ _).
        viewshift_SEP 0 (AS ∗ (inFP γ_f pnN nullval l)).
        { go_lowerx. rewrite bi.sep_emp. iApply push_lock_back; auto. }
        (* end - push back lock into invariant *)
        Intros.
        rewrite -> (if_false _ (eq_dec r nullval)); auto.
        rewrite -> if_true; auto.
        simpl.
        sep_apply shot_duplicate.
        Intros.
        gather_SEP (node _ _ _) (own γ_I _) (own γ_k _) (own γ_m _)
          (own γ_n _) (field_at _ _ _ _ _).
        viewshift_SEP 0 (md_entry_rep γ_I γ_k γ_m γ_n nullval nr c r).
        { go_lowerx. rewrite bi.sep_emp.
          iIntros "(Hn & HfI & Hfk & Hfm & Hfn & Hf_css)".
          iFrame.
          rewrite -> if_false; auto.
        }
        simpl.
        gather_SEP AS (md_entry_rep γ_I γ_k γ_m γ_n nullval nr c r).
        viewshift_SEP 0 (∃ lr,
            AS ∗ (md_entry_rep γ_I γ_k γ_m γ_n nullval nr c r) ∗ inFP γ_f r nullval lr ∧
              ⌜is_pointer_or_null lr (* /\ (0 <= f r < size)%Z *) ⌝).
        { go_lowerx. rewrite bi.sep_emp.
          iIntros "(HAU & Hmd)".
          iMod "HAU" as (m) "(Hm & HClose)".
          rewrite /CSSt /=.
          rewrite {1} /CSS.
          iDestruct "Hm" as (I r1) "HCSSi".
          iDestruct (unify_root with "[$HCSSi $Hmd]") as %<-; auto.
          iMod (ghost_update_root with "[$HCSSi]") as "inFP".
          iDestruct "inFP" as (lr) "(HCSS & inFP & %Hc)".
          iExists lr.
          iMod ("HClose" with "HCSS") as "HClose".
          iFrame "inFP ∗". iIntros "!>". by destruct Hc.
        }
        Intros lr.
        gather_SEP (md_entry_rep _ _ _ _ _ _ _ _)
          (bi_wand (md_entry_rep _ _ _ _ _ _ _ _) (nodeFull2 _ _ _ _ _ _ _ _ _)).
        sep_apply (bi.wand_elim_r (md_entry_rep γ_I γ_k γ_m γ_n nullval nr c r)).
        (* switch nodeFull to root*)
        sep_apply (nodeFull_switch_root γ_I γ_k γ_m γ_n  nullval nullval nr c r).
        Intros nr1.
        forward.
        entailer !.
        Exists r lr nr1.
        entailer !.
        rewrite -> if_false; auto.
        cancel.
        by iIntros "_".
      - simpl.
        (* push back lock into invariant *)
        gather_SEP AS (inFP _ _ _ _) (field_at (cs := CompSpecs) _ _ [StructField _lock] _ c).
        viewshift_SEP 0 (AS ∗ (inFP γ_f pnN nullval l)).
        { go_lowerx. rewrite bi.sep_emp. iApply push_lock_back; auto. }
        (* end - push back lock into invariant *)
        Intros.
        rewrite -> if_false; auto.
        sep_apply (nodeFull_switch_node γ_I γ_k γ_m γ_n nullval nr c r pnN nullval).
        set dummy := (own γ_n (Cinr (to_agree pnN)) ∗ _).
        sep_apply (bi.and_elim_l dummy (valid_pointer pnN)).
        unfold dummy. clear dummy.
        Intros nr1.
        forward.
        Exists pnN l nr1.
        rewrite -> if_false; auto.
        entailer !.
   - (** main program **)
     clear dependent pnN.
     Intros n lkn nr1.
     rewrite /cs.
     sep_apply nodeFull_extract.
     Intros.
     (* in_inset from root node, we know n is a root (pn->n = r;)
        in_inset is used for findNext *)
     rewrite if_false; auto.
     gather_SEP AS (md_entry_rep γ_I γ_k γ_m γ_n n nr1 c r) (own γ_n _).
     viewshift_SEP 0 (AS ∗ (md_entry_rep γ_I γ_k γ_m γ_n n nr1 c r) ∗
                        (own (inG0 := one_shot_inG) γ_n (Cinr (to_agree n))) ∧
                        ⌜in_inset _ _ _ x (Ip nr1) n⌝).
     { go_lowerx. rewrite bi.sep_emp.
       rewrite @inset_from_root; eauto.
     }
     Intros.
     gather_SEP (md_entry_rep _ _ _ _ _ _ _ _)
       (bi_wand (md_entry_rep _ _ _ _ _ _ _ _) (nodeFull2 _ _ _ _ _ _ _ _ _)).
     sep_apply (bi.wand_elim_r (md_entry_rep γ_I γ_k γ_m γ_n n nr1 c r)).
     sep_apply inFP_duplicate.
     forward_loop (traverse_inv γ_I γ_f γ_k γ_g γ_m γ_n pn n nullval lkn c Ews x gv AS)
       break:
       (∃ rtrn : (enum * Node * val * val * NodeR * val),
           PROP() LOCAL(temp _status (let '(e, pt, pt1, lkt, nrt, rt) := rtrn in enums e))
           SEP(
             (let '(e, pt, pt1, lkt, nrt, rt) := rtrn in
             match e with
             | F => traverse_inv_F γ_I γ_f γ_k γ_m γ_n pn pt pt1 lkt nrt rt c x
             | NF => traverse_inv_NF γ_I γ_f γ_k γ_m γ_n pn pt pt1 lkt nrt rt c x
             | CNT => ⌜pt = nullval /\ x ∉ dom (Cp nrt) /\ (0 ≤ f pt < size)%Z /\
                       is_pointer_or_null pt /\
                       is_pointer_or_null lkt /\
                       (pt = nullval -> rt = nullval) /\ (pt <> nullval -> belongs x nrt) /\
                       in_inset _ _ _ x (Ip nrt) pt /\
                       ¬ in_outsets _ _ _ x (Ip nrt) /\ ✓ (Ip nrt)⌝ ∧ inFP γ_f nullval pt1 lkt ∗
                    nodeFull2 γ_I γ_k γ_m γ_n pt1 nullval nrt c rt ∗
                    ∃ pnN, data_at Ews t_struct_pn (nullval, pnN) pn
             end) ∗
               Q rtrn ∗ mem_mgr gv)).
    + rewrite /traverse_inv.
      Exists n nullval nullval lkn lsh nr1 r.
      entailer !. by iIntros "_".
    + (** go deeply into loop **)
      (*pre-condition*)
      rewrite / traverse_inv.
      Intros pnN pnP ptn1 lock lshN1 nrN rN.
      forward.
      forward.
      forward.
      assert_PROP(field_compatible t_struct_pn [StructField _n] pn). entailer !.
      sep_apply nodeFull_extract.
      Intros.
      (* findNext *)
      rewrite {1} /md_entry_rep.
      Intros.
      forward_call(x, pnN, (field_address t_struct_pn [StructField _n] pn),
                         pnN, (Ip nrN), (Cp nrN), Ews, gv).
      { unfold_data_at (data_at Ews t_struct_pn _ pn).
        set cs' := (@DS_compspecs Σ VSTGS0 N).
        change_compspecs' cs cs'.
        rewrite /cs. entailer !.
      }
      rewrite -> if_false; auto.
      Intros stt.
      destruct stt.1; last first.
      Intros.
      simpl.
      forward.
      forward_if.
      ++ easy. (* contradiction *)
      ++ forward_if. { easy. } (* contradiction *)
         destruct stt as (q & rest).
         set cs' := (@DS_compspecs Σ VSTGS0 N).
         change_compspecs' cs cs'.
         rewrite /cs.
         (* replace *)
         replace (data_at Ews (tptr t_struct_node) rest
                         (field_address t_struct_pn (DOT _n) pn)) with
           (field_at (cs := CompSpecs) Ews t_struct_pn (DOT _n) rest pn).
         2: { rewrite field_at_data_at; try done. }
         simpl.
         (*gather to have md_entry_rep *)
         gather_SEP (node _ _ _) (own γ_I _) (own γ_k _) (own γ_m _).
         (* actually c and r are nonsense here, change if needed*)
         viewshift_SEP 0 (md_entry_rep γ_I γ_k γ_m γ_n pnN nrN c rN).
         { go_lowerx. rewrite bi.sep_emp.
           iIntros "(Hn & HfI & Hfk & Hfm)".
           rewrite /md_entry_rep if_false; auto.
           iFrame; iPureIntro; repeat (split; auto).
         } 
         (* create inFP γ_f rest q1 l *)
         gather_SEP (inFP γ_f pnN ptn1 lock) AS (md_entry_rep γ_I γ_k γ_m γ_n pnN nrN c rN).
         viewshift_SEP 0 (∃ l,
               (inFP γ_f pnN ptn1 lock) ∗ AS ∗
                 md_entry_rep γ_I γ_k γ_m γ_n pnN nrN c rN ∗ inFP γ_f rest nullval l ∧
               ⌜is_pointer_or_null rest /\
                is_pointer_or_null l⌝).
         { go_lowerx. rewrite bi.sep_emp. rewrite @get_inFP_not_null //. }
        Intros l2.
        sep_apply valid_Ip_md.
        Intros.
        assert (pnN <> rest) as Hneq.
        { eapply distinct_node; eauto. clear -H15. set_solver. }
        Intros.
        gather_SEP (md_entry_rep _ _ _ _ _ _ _ _)
          (bi_wand (md_entry_rep _ _ _ _ _ _ _ _) (nodeFull2 _ _ _ _ _ _ _ _ _)).
        sep_apply (bi.wand_elim_r (md_entry_rep γ_I γ_k γ_m γ_n pnN nrN c rN)).
        viewshift_SEP 0
          (∃ nr', ⌜in_inset _ _ _ x (Ip nr') rest⌝ ∧
                    nodeFull2 γ_I γ_k γ_m γ_n nullval rest nr' c rN).
        { go_lowerx. rewrite bi.sep_emp.
          iIntros "H !>".
          iDestruct (nodeFull_switch1 _ _ _ _ _ pnN nrN c rN x nullval rest with "[$H]")
            as "?"; eauto.
        }
        Intros nrNN.
        clear dependent cs'.
        rewrite /traverse_inv.
        forward.
        Exists rest pnN nullval l2 lsh nrNN rN.
        subst.
        unfold_data_at (data_at Ews t_struct_pn _ pn). entailer !. by iIntros "_".
     ++ (* NOTFOUND *)
        forward.
        forward_if.
        { easy. } (* contradiction *)
        forward_if; last first.
        { easy. } (* contradiction *)
        (* NOTFOUND *)
        (*gather to have md_entry_rep *)
        gather_SEP (node _ _ _) (own γ_I _) (own γ_k _) (own γ_m _).
        (* actually c and r are nonsense here, change if needed*)
        viewshift_SEP 0 (md_entry_rep γ_I γ_k γ_m γ_n pnN nrN c rN).
        { go_lowerx. rewrite bi.sep_emp.
          iIntros "(Hn & HfI & Hfk & Hfm)".
          rewrite /md_entry_rep if_false; auto.
          iFrame; iPureIntro; repeat (split; auto).
        }
        Intros.
        (* have valid flow ✓ Ip *)
        sep_apply valid_Ip_md.
        Intros.
        gather_SEP AS (inFP γ_f pnN ptn1 lock).
        (* commit *)
        viewshift_SEP 0 (Q (NF, pnN, ptn1, lock, nrN, rN) ∗ inFP γ_f pnN ptn1 lock).
        { go_lowerx; rewrite bi.sep_emp.
          iIntros "(AU & #HinFP)".
          iMod "AU" as (m) "(Hm & HClose)".
          iDestruct "HClose" as "(_ & HClose)".
          iMod ("HClose" with "[Hm]") as "Hm".
          iFrame "Hm". by iFrame "HinFP ∗".
        }
        gather_SEP (md_entry_rep _ _ _ _ _ _ _ _)
          (bi_wand (md_entry_rep _ _ _ _ _ _ _ _) (nodeFull2 _ _ _ _ _ _ _ _ _)).
        sep_apply (bi.wand_elim_r (md_entry_rep γ_I γ_k γ_m γ_n pnN nrN c rN)).
        forward.
        (* return NOTFOUND; *)
        (* Q (NF, pnN, ptn1, lock, nr1, r) *)
        Exists (NF, pnN, ptn1, lock, nrN, rN).
        rewrite /traverse_inv_NF.
        Exists stt.2.
        subst.
        unfold_data_at (data_at Ews t_struct_pn _ pn).
        set cs' := (@DS_compspecs Σ VSTGS0 N).
        change_compspecs' cs cs'.
        entailer !.
        by iIntros "_".
     ++ (* FOUND *)
        forward.
        forward_if; last first.
        { easy. } (* contradiction *)
        (*gather to have md_entry_rep *)
        gather_SEP (node pnN _ _) (own γ_I _) (own γ_k _) (own γ_m _).
             (* actually c and r are nonsense here, change if needed*)
        viewshift_SEP 0 (md_entry_rep γ_I γ_k γ_m γ_n pnN nrN c rN).
        { go_lowerx. rewrite bi.sep_emp.
          iIntros "(Hn & HfI & Hfk & Hfm)".
          rewrite /md_entry_rep if_false; auto.
          iFrame; iPureIntro; repeat (split; auto).
        }
        Intros.
        (* have valid flow ✓ Ip *)
        sep_apply valid_Ip_md.
        Intros.
        gather_SEP AS (inFP γ_f pnN ptn1 lock).
        (* commit *)
        viewshift_SEP 0 (Q (F, pnN, ptn1, lock, nrN, rN) ∗ inFP γ_f pnN ptn1 lock).
        { go_lowerx; rewrite bi.sep_emp.
          iIntros "(AU & #HinFP)".
          iMod "AU" as (m) "(Hm & HClose)".
          iDestruct "HClose" as "(_ & HClose)".
          iMod ("HClose" with "[Hm]") as "Hm".
          iFrame "Hm". by iFrame "HinFP ∗".
        }
        gather_SEP (md_entry_rep _ _ _ _ _ _ _ _)
          (bi_wand (md_entry_rep _ _ _ _ _ _ _ _) (nodeFull2 _ _ _ _ _ _ _ _ _)).
        sep_apply (bi.wand_elim_r (md_entry_rep γ_I γ_k γ_m γ_n pnN nrN c rN)).
        forward.
        (* return FOUND; *)
        (* Q (F, pnN, ptn1, lock, nr1, r) *)
        Exists (F, pnN, ptn1, lock, nrN, rN).
        rewrite /traverse_inv_F.
        subst.
        unfold_data_at (data_at Ews t_struct_pn _ pn).
        set cs' := (@DS_compspecs Σ VSTGS0 N).
        change_compspecs' cs cs'.
        entailer !. by iIntros "_".
  + Intros rtrn.
    destruct rtrn as ((((stt & ptn1) & lock) & nrN) & rN).
    destruct stt as (stt & pnN).
    destruct stt.
    * forward.
      Exists (F, pnN, ptn1, lock, nrN, rN).
      Exists pnN.
      rewrite /traverse_inv_F.
      set cs' := template_class.CompSpecs.
      change_compspecs' cs cs'.
      entailer !.
    * forward.
      rewrite /traverse_inv_NF.
      Intros pnN'.
      Exists (NF, pnN, ptn1, lock, nrN, rN).
      Exists pnN'.
      set cs' := template_class.CompSpecs.
      change_compspecs' cs cs'.
      entailer !.
    * Intros.
      Intros pnN'.
      forward.
      Exists (CNT, nullval, ptn1, lock, nrN, rN).
      Exists pnN'.
      set cs' := template_class.CompSpecs.
      change_compspecs' cs cs'.
      entailer !.
 Qed.

  (** make_css proof **)

  Lemma body_make_css: semax_body Vprog Gprog f_make_css make_css_spec.
  Proof.
    start_function.
    forward_call (t_struct_css, gv).
    Intros css.
    Intros.
    forward_call (gv).
    Intros lock.
    forward.
    forward.
    simpl.
    forward_call release_nonatomic (lock).
    forward.
    simpl.
    assert (exists ks, dom (ks : nzmap Z nat) = KS) as Hdom.
    { exists (set_fold (fun (k: Z) m => <<[k := 1]>> m) nzmap_empty KS).
      apply (set_fold_ind_L (fun KS acc => dom KS = acc)). set_solver.
      { intros. rewrite -leibniz_equiv_iff nzmap_dom_insert_nonzero; auto. set_solver. }
    }
    destruct Hdom as (ks & Hdom).
    set Ir := flow_int {| infR := {[nullval := ks]}; outR := ∅ |}.
    Exists css.
    entailer !.
    iMod (own_alloc (A := csumR dfracR (agreeR valC)) (Cinl 1%Qp)) as (γ_n) "Hn"; try done.
    rewrite - (Qp.div_2 1) -frac_op Cinl_op.
    iDestruct "Hn" as "(Hn1 & Hn2)".
    rewrite /CSS /CSSi /globalGhost.
    set N1 := ({[nullval := (nullval, lock) ]} : gmap _ _).
    iIntros "(Htm & Hml & Hd)".
    iMod (own_alloc ((● (to_agree <$> N1) : gmap_authR _ _) ⋅
                       (◯ (to_agree <$> N1) : gmap_authR _ _))) as (γ_f) "(Hf● & Hf◯)".
    { apply auth_both_valid_discrete.
      split; auto.
      rewrite / N1.
      iIntros (?).
      rewrite lookup_fmap.
      destruct (N1 !! i) eqn: E; rewrite E; try done.
    }
    iMod (own_alloc ( (● Ir) ⋅ (◯ Ir))) as (γ_I) "(HIr● & HIr◯)".
    { apply auth_both_valid_discrete. split; try done. }
    iMod (own_alloc ((● prod (KS, ∅) : keyset_authR _) ⋅ (◯ prod (KS, ∅): keyset_authR _))) 
      as (γ_k)"(Hks● & Hks◯)".
    { apply auth_both_valid_discrete. split; try done. }
    iMod (own_alloc ((● (Excl <$> ∅) : keymap_authR _ _) ⋅ (◯ (Excl <$> ∅))))
      as (γ_m) "(Hm● & Hm◯)".
    { apply auth_both_valid_discrete. split; try done. }
    iIntros "!>".
    iExists γ_I, γ_f, γ_k, γ_f, γ_m, γ_n.
    iExists (flow_int {| infR := {[ nullval := ks]}; outR := ∅ |}).
    iExists nullval.
    rewrite /dom /flowint_dom /= dom_singleton_L.
    iFrame "Hf● HIr● Hks● Hm● Hn2".
    unfold_data_at (data_at _ _ _ css).
    iDestruct "Hd" as "(Hd & Hl)".
    assert (dom Ir = ({[nullval]} : gset _)) as Dom_Ir.
    { rewrite /Ir /dom /flowint_dom /=. set_solver. }
    set (nr := {| Cp := ∅; Ip := Ir; |}).
    iExists Ews, lock, nr.
    iFrame.
    iSplit; auto.
    { iPureIntro. split; auto. set_solver. }
    iSplit; auto.
    { iPureIntro. split; auto.
      - split; auto.
        rewrite /globalinv.
        repeat (split; auto).
        rewrite /dom /=. set_solver.
        rewrite /dom /flowint_dom /=. set_solver.
        rewrite /closed /outset /out /=; intros k n Hcontra.
        rewrite nzmap_lookup_empty in Hcontra. set_solver.
        intros; rewrite /inset /inf /= lookup_insert Hdom; auto.
      - do 2 (split; auto).
        rewrite /N1 /= /flowint_dom /=. set_solver.
        intros ??? HN1_map.
        rewrite /N1 in HN1_map.
        assert (n = nullval) as H_eq_n_null.
        { destruct (decide (n = nullval)); subst; last first; auto.
          rewrite lookup_singleton_ne in HN1_map; auto. easy.
        }
        by rewrite H_eq_n_null lookup_singleton in HN1_map; inv HN1_map.
    }
    iSplitL.
    iExists false.
    iFrame.
    iExists ({[nullval := nr]}).
    iSplit; auto.
    { iPureIntro.
      rewrite (big_opM_delete _ ({[nullval := nr]}) nullval nr).
      rewrite delete_singleton big_opM_empty.
      repeat (split; auto).
      { rewrite monoid_right_id /nr /=.
        apply intValid_unfold.
        do 2 (split; auto).
        rewrite /Ir /= dom_singleton.
        assert (@dom(@nzmap Node _ _ (@multiset_flows.K_multiset Key _ _) _) _ _ ∅ = ∅). set_solver.
        rewrite H4. set_solver.
      }
      { rewrite monoid_right_id /nr /= /flowint_dom /inf_map /=. set_solver. }
      { rewrite /closed; intros.
        rewrite monoid_right_id /nr /outset /out nzmap_lookup_empty. set_solver.
      }
      { intros; rewrite /inset monoid_right_id /nr /inf lookup_insert /=. set_solver. }
      { set_solver. }
      { rewrite /map_Forall. intros.
        destruct (decide (i = nullval)); subst; last first; auto.
        rewrite lookup_insert_ne in H4.
        rewrite lookup_empty in H4; auto. congruence. auto.
        rewrite lookup_insert in H4. inv H4.
        rewrite /Ir /flowint_dom /inf_map /=. set_solver.
      }
      rewrite lookup_insert; auto. rewrite lookup_insert; auto.
    }
    rewrite (big_opM_delete _ ({[nullval := nr]}) nullval nr).
    rewrite delete_singleton big_opM_empty.
    assert (keyset _ _ _ Ir nullval = KS) as Hkeyset.
    { rewrite /keyset /Ir /outsets big_opS_empty /inf lookup_insert Hdom /=. set_solver. }
    iFrame.
    rewrite Hkeyset dom_empty_L.
    iFrame "Hks◯".
    iSplit; auto.
    iDestruct (imply_node ks Ir with "[%]") as "Hnode".
    { split; auto. }
    iFrame "Hnode". iPureIntro. split; auto.
    rewrite lookup_insert //.
    by rewrite difference_diag_L big_sepS_empty.
  Qed.
    
  (** lookupOp_helper **)
  Lemma lookupOp_helper: semax_body Vprog Gprog f_lookupOp_helper lookupOp_helper_spec.
  Proof.
    start_function.
    rewrite /md_entry_rep_t /= /nodeFull2.
    Intros Nmap.
    rewrite big_opM_delete //.
    set (AS := atomic_shift _ _ _ _ _ ).
    forward_if (PROP ( )
                  LOCAL (let v :=
                           match status with
                           | F =>
                               match (Cp nr) !! x with
                               | Some v' => v'
                               | None => Vlong (Int64.repr (Int.signed (Int.repr 0)))
                               end
                           | _ => Vlong (Int64.repr (Int.signed (Int.repr 0)))
                           end in temp _v v; gvars gv; 
                         temp _c css; temp _p p; temp _x (vint x); temp _status (enums status))
                  SEP (AS; mem_mgr gv; inFP γ_f p p1 l;
                       md_entry_rep γ_I γ_k γ_m γ_n p nr css r ∗
                         ([∗ map] k↦y ∈ delete p Nmap, md_entry_rep γ_I γ_k γ_m γ_n k y css r)) ).
    - destruct status; try discriminate.
      unfold md_entry_rep at 1; Intros.
      + rewrite /map_Forall in H14.
        pose proof H15 as Hmap.
        apply H14 in H15.
        destruct H11 as (Hne_p_null & Hdom).
        forward_call (x, p, (Ip nr), (Cp nr), gv).
        Intros ret.
        rewrite -> if_false; auto.
        assert (x ∈ dom (Cp nr)) as Hdomx.
        { clear -H11. set_solver. }
        assert (Hex : ∃ v, Cp nr !! x = Some v).
        { by rewrite elem_of_dom /is_Some in Hdomx. }
        destruct Hex as [v' Hlookup].
        gather_SEP (node p _ _) (own γ_I _) (own γ_k _) (own γ_m _).
        viewshift_SEP 0 (md_entry_rep γ_I γ_k γ_m γ_n p nr css r).
        { go_lowerx. rewrite /md_entry_rep. rewrite -> if_false; auto.
          iIntros "((? & (? & (? & ?))) & _)". by iFrame.
        }
        forward.
        entailer !.
    - Intros.
      forward.
      destruct status; try entailer !.
    - set Q1:= fun (v : val) => AS.
      destruct status.
      + (* FOUND *)
        destruct H11 as (Hne_p_null & Hdom).
        assert (x ∈ dom (Cp nr)) as Hdomx.
        { clear -Hdom. set_solver. }
        assert (Hex : ∃ v, Cp nr !! x = Some v).
        { apply elem_of_dom in Hdomx.
          rewrite /is_Some in Hdomx. done.
        }
        destruct Hex as [v' Hlookup].
        rewrite Hlookup.
        gather_SEP AS (inFP γ_f _ _ _).
        viewshift_SEP 0 (AS ∗ inFP γ_f p nullval l ∗
             ∃ lsh : share, ⌜readable_share lsh⌝ ∧
             field_at (cs := coarse_lib.CompSpecs) lsh t_struct_css [StructField _lock] l css).
        { go_lowerx. rewrite bi.sep_emp. iApply lock_alloc. }
        Intros lsh.
        forward.
        (* push back lock into invariant *)
        gather_SEP AS (inFP γ_f p nullval l) (field_at (cs := CompSpecs) lsh _ _ _ _).
        viewshift_SEP 0 (AS ∗ (inFP γ_f p nullval l)).
        { go_lowerx. rewrite bi.sep_emp.
          iApply push_lock_back; auto. }
        (* end - push back lock into invariant *)
        forward_call (l, Q v').
        { rewrite /rev_curry /=.
          iIntros "((AU & HinFP) & Hgv & (Hmd & Hbig))".
          iSplitR "Hgv"; last by iStopProof; cancel.
          unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
          iMod "AU" as (m) "(Hm & HClose)".
          iModIntro.
          iExists tt.
          iDestruct "Hm" as (I r1) "HCSSi".
          iAssert ⌜r = r1⌝ as %->.
          { apply elem_of_dom in H13 as (? & ?).
            rewrite (big_opM_delete _ _ nullval); last by rewrite lookup_delete_ne.
            iDestruct "Hbig" as "(Hmd1 & ?)".
            by iApply (unify_root with "[$HCSSi $Hmd1]").
          }
          rewrite /CSSi.
          iDestruct "HCSSi" as (lsh1 lock nr1) "(%Hc & Hglob & Hml & Hf & Hinv & Hown)".
          iDestruct "Hinv" as (b) "(Htm1 & HNF)".
          destruct b; last first.
          {
            iDestruct (nodeFull_extract with "HNF") as "(_ & HN & ?)".
            apply elem_of_dom in H13 as (? & ?).
            rewrite (big_opM_delete _ _ nullval); last by rewrite lookup_delete_ne.
            iDestruct "Hbig" as "(Hmd1 & ?)".
            iDestruct (md_entry_conflict with "[$Hmd1 $HN]") as "[]".
          }
          iDestruct (same_lock with "[$HinFP $Hglob]") as %(_ & <-).
          iFrame "Htm1".
          iSplit.
          iIntros "Htm1".
          simpl.
          iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css) with
            "[$Hglob $Hml $Hf HNF $Hown Htm1]" as "HCSS".
          { iExists nr1. (* whatever*)
            iSplit; auto.
            iExists true.
            iFrame.
          }
          iDestruct "HClose" as "(HClose & _)".
          iFrame.
          iSpecialize ("HClose" with "HCSS").
          iMod ("HClose").
          by iFrame.
          iIntros (_) "Hinv".
          iDestruct "Hinv" as "(Htm1 & _)".
          iDestruct "Hglob" as "(%Hglob & HauthI & Hauthk & Hauthm & Hown_nodes)".
          destruct Hglob as (Hglob & Hr).
          simpl.
          rewrite {1} /md_entry_rep.
          rewrite -> (if_false _ (eq_dec p nullval)); auto.
          iDestruct "HClose" as "(_ & HClose)".
          iApply "HClose".
          iSplit; auto.
          iSplit.
          (* prove m !! x = v' *)
          iDestruct "Hmd" as "(? & ? & ? & ? & Hm & _)".
          iDestruct (own_valid_2 γ_m (●(Excl <$> m) : keymap_authR _ _)
                       (◯ (Excl <$> Cp nr)) with "[$Hauthm] [$Hm]") as %Hownr.
          move: Hownr => /auth_both_valid_discrete [Hsub Hv].
          rewrite lookup_included in Hsub.
          specialize (Hsub x).
          rewrite ! lookup_fmap Hlookup in Hsub.
          destruct (m !! x) eqn: E.
          rewrite E in Hsub.
          iPureIntro.
          rewrite <- leibniz_equiv_iff.
          apply Excl_included; try done.
          rewrite E in Hsub.
          simpl in Hsub.
          rewrite option_included in Hsub.
          destruct Hsub as [Hcontra | (? & ? & ? & Hcontra & ?)]; try easy.
          iClear "HNF".
          iAssert (∃ nr1, nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr1 css r1)
            with "[Hmd Hbig]" as "HNF".
          { iAssert (md_entry_rep γ_I γ_k γ_m γ_n p nr css r1) with "[Hmd]" as "Hmd".
            { iDestruct "Hmd" as "(? & ? & ? & ? & ? & _)".
              iFrame. rewrite -> if_false; auto.
            }
            iApply (join_nodeFull with "[$Hmd $Hbig]"); auto.
          }
          iDestruct "HNF" as (?) "HNF".
          iFrame.
          iExists nr0.
          iSplit; auto.
          iSplit; auto.
          iExists false.
          iFrame.
        }
        simpl.
        forward.
        Exists v'. entailer !.
      + (* NOTFOUND *)
        destruct H11 as (Hne_p_null & Hdom).
        gather_SEP AS (inFP γ_f _ _ _).
        viewshift_SEP 0 (AS ∗ inFP γ_f p nullval l ∗ ∃ lsh : share, ⌜readable_share lsh⌝ ∧
           field_at (cs := coarse_lib.CompSpecs) lsh t_struct_css [StructField _lock] l css).
        { go_lowerx. rewrite bi.sep_emp. iApply lock_alloc. }
        Intros lsh.
        forward.
        (* push back lock into invariant *)
        gather_SEP AS (inFP γ_f p nullval l) (field_at (cs := CompSpecs) lsh _ _ _ _).
        viewshift_SEP 0 (AS ∗ (inFP γ_f p nullval l)).
        { go_lowerx. rewrite bi.sep_emp.
          iApply push_lock_back; auto. }
        (* end - push back lock into invariant *)
        Intros.
        forward_call (l, Q nullval).
        { rewrite /rev_curry /=.
          iIntros "(AU & HinFP & Hgv & (Hmd & Hbig))".
          iSplitR "Hgv"; last by iStopProof; cancel.
          unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
          iMod "AU" as (m) "(Hm & HClose)".
          iModIntro.
          iExists tt.
          iDestruct "Hm" as (I r1) "HCSSi".
          iAssert ⌜r = r1⌝ as %->.
          { apply elem_of_dom in H13 as (? & ?).
            rewrite (big_opM_delete _ _ nullval); last by rewrite lookup_delete_ne.
            iDestruct "Hbig" as "(Hmd1 & ?)".
            by iApply (unify_root with "[$HCSSi $Hmd1]").
          }
          rewrite /CSSi.
          iDestruct "HCSSi" as (lsh1 lock nr1) "(%Hc & Hglob & Hml & Hf & Hinv & Hown)".
          iDestruct "Hinv" as (b) "(Htm1 & HNF)".
          destruct b; last first.
          { iDestruct (nodeFull_extract with "HNF") as "(_ & HN & ?)".
            apply elem_of_dom in H13 as (? & ?).
            rewrite (big_opM_delete _ _ nullval); last by rewrite lookup_delete_ne.
            iDestruct "Hbig" as "(Hmd1 & ?)".
            iDestruct (md_entry_conflict with "[$Hmd1 $HN]") as "[]".
          }
          iDestruct (same_lock with "[$HinFP $Hglob]") as %(_ & <-).
          iFrame "Htm1".
          iSplit.
          iIntros "Htm1".
          simpl.
          iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css) with
            "[$Hglob $Hml $Hf HNF $Hown Htm1]" as "HCSS".
          { iExists nr1. (* whatever *)
            iSplit; auto.
            iExists true.
            iFrame.
          }
          iDestruct "HClose" as "(HClose & _)".
          iFrame.
          iSpecialize ("HClose" with "HCSS").
          iMod ("HClose").
          by iFrame.
          iIntros (_) "Hinv".
          iDestruct "Hinv" as "(Htm1 & _)".
          iDestruct "Hglob" as "(%Hglob & HauthI & Hauthk & Hauthm & Hown_nodes)".
          destruct Hglob as (Hglob & Hr).
          simpl.
          rewrite {1} /md_entry_rep.
          rewrite -> (if_false _ (eq_dec p nullval)); auto.
          iDestruct "HClose" as "(_ & HClose)".
          iApply "HClose".
          iSplit; auto.
          iSplit.
          iDestruct "Hmd" as "(? & ? & ? & Hk & Hm & _)".
          (* prove m !! x = nullval *)
          (* x ∉ dom m *)
          iDestruct (key_new_node_fresh _ _ x with "[$Hauthk $Hk]") as %Hx_notin_dom_m; auto.
          { iPureIntro.
            do 2 (split; auto).
            apply keyset_def; auto.
            intros Hcontra.
            apply outset_in_outsets1 in Hcontra.
            rewrite /in_outsets /in_outset in Hcontra.
            rewrite /in_outsets /in_outset in H5. easy.
          }
          apply not_elem_of_dom_1 in Hx_notin_dom_m.
          rewrite Hx_notin_dom_m; auto.
          iClear "HNF".
          iAssert (∃ nr1, nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr1 css r1)
            with "[Hmd Hbig]" as "HNF".
          { iAssert (md_entry_rep γ_I γ_k γ_m γ_n p nr css r1) with "[Hmd]" as "Hmd".
            { iDestruct "Hmd" as "(? & ? & ? & ? & ? & _)".
              iFrame. rewrite -> if_false; auto.
            }
            iApply (join_nodeFull _ _ _ _ p nr css r1 Nmap with "[$Hmd $Hbig]"); auto.
          }
          iDestruct "HNF" as (?) "HNF".
          iFrame.
          iExists nr0.
          iSplit; auto.
          iSplit; auto.
          iExists false.
          iFrame.
        }
        simpl.
        forward.
        Exists nullval. entailer !.
      + (* CONTINUE *)
        destruct H11 as (Heq_p_null & Hne_dom).
        gather_SEP AS (inFP γ_f _ _ _).
        viewshift_SEP 0 (AS ∗ inFP γ_f p nullval l ∗ ∃ lsh : share, ⌜readable_share lsh⌝ ∧
           field_at (cs := coarse_lib.CompSpecs) lsh t_struct_css [StructField _lock] l css).
        { go_lowerx. rewrite bi.sep_emp. iApply lock_alloc. }
        Intros lsh.
        forward.
        (* push back lock into invariant *)
        gather_SEP AS (inFP γ_f p nullval l) (field_at (cs := CompSpecs) lsh _ _ _ _).
        viewshift_SEP 0 (AS ∗ (inFP γ_f p nullval l)).
        { go_lowerx. rewrite bi.sep_emp.
          iApply push_lock_back; auto. }
        (* end - push back lock into invariant *)
        Intros.
        forward_call (l, Q nullval).
        { rewrite /rev_curry /=.
          iIntros "(AU & HinFP & Hgv & (Hmd & Hbig))".
          iSplitR "Hgv"; last by iStopProof; cancel.
          unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
          iMod "AU" as (m) "(Hm & HClose)".
          iModIntro.
          iExists tt.
          iDestruct "Hm" as (I r1) "HCSSi".
          rewrite /CSSi.
          iDestruct "HCSSi" as (lsh1 lock nr1) "(%Hc & Hglob & Hml & Hf & Hinv & Hown)".
          iDestruct "Hinv" as (b) "(Htm1 & HNF)".
          destruct b; last first.
          { iDestruct (nodeFull_extract with "HNF") as "(_ & HN & ?)"; subst.
            iDestruct (md_entry_conflict with "[$Hmd $HN]") as "[]".
          }
          iDestruct (same_lock with "[$HinFP $Hglob]") as %(_ & <-).
          iFrame "Htm1".
          iSplit.
          iIntros "Htm1".
          simpl.
          iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css) with
            "[$Hglob $Hml $Hf HNF $Hown Htm1]" as "HCSS".
          { iExists nr1. (* whatever *)
            iSplit; auto.
            iExists true.
            iFrame.
          }
          iDestruct "HClose" as "(HClose & _)".
          iFrame.
          iSpecialize ("HClose" with "HCSS").
          iMod ("HClose").
          by iFrame.
          iIntros (_) "Hinv".
          iDestruct "Hinv" as "(Htm1 & _)".
          iDestruct "Hglob" as "(%Hglob & HauthI & Hauthk & Hauthm & Hown_nodes)".
          destruct Hglob as (Hglob & Hr).
          simpl.
          rewrite {1} /md_entry_rep.
          rewrite -> (if_true _ (eq_dec p nullval)); auto.
          iDestruct "HClose" as "(_ & HClose)".
          iApply "HClose".
          iSplit; auto.
          iSplit.
          iDestruct "Hmd" as "(? & ? & ? & Hk & Hm & Hn & Hf_css)".
          (* prove m !! x = nullval *)
          (* x ∉ dom m *)
          iDestruct (key_new_node_fresh _ _ x with "[$Hauthk $Hk]") as %Hx_notin_dom_m; auto.
          { iPureIntro.
            do 2 (split; auto).
            apply keyset_def; auto.
            intros Hcontra.
            apply outset_in_outsets1 in Hcontra.
            rewrite /in_outsets /in_outset in Hcontra.
            rewrite /in_outsets /in_outset in H5. easy.
          }
          apply not_elem_of_dom_1 in Hx_notin_dom_m.
          rewrite Hx_notin_dom_m. auto.
          pose proof Heq_p_null as Heq_p_null1.
          apply H8 in Heq_p_null.
          rewrite -> (if_true _ (eq_dec r nullval)); auto.
          destruct (eq_dec r1 nullval); last first.
          { iDestruct "Hmd" as "(? & ? & ? & ? & ? & ? & Hn & ?)".
            iDestruct "Hown" as "(? & Hown)".
            iDestruct (shot_not_pending with "[$Hn $Hown]") as %[].
          }
          iClear "HNF".
          subst.
          iAssert (∃ nr1, nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr1 css nullval)
            with "[Hmd Hbig]" as "HNF".
          { iAssert (md_entry_rep γ_I γ_k γ_m γ_n nullval nr css nullval) with "[Hmd]" as "Hmd".
            { iDestruct "Hmd" as "(? & ? & ? & ? & ? & ? & ? & ?)".
              iFrame. 
            }
            iApply (@join_nodeFull with "[$Hmd $Hbig]"); auto.
          }
          iDestruct "HNF" as (?) "HNF".
          iFrame.
          iExists nullval, nr0.
          iSplit; auto.
          iSplit; auto.
          iSplitR "Hown"; auto.
          { iExists false. iFrame. }
        }
        simpl.
        forward.
        Exists nullval. entailer !.
   Qed.
  
  Arguments Qp.div : simpl never.
  
  Lemma insertOp_helper: semax_body Vprog Gprog f_insertOp_helper insertOp_helper_spec.
  Proof.
    start_function.
    rewrite /md_entry_rep_t /= /nodeFull2.
    Intros Nmap.
    rewrite big_opM_delete //.
    unfold md_entry_rep at 1; Intros.
    forward_call (x, v, p, (Ip nr), (Cp nr), gv).
    Intros nflwt.
    destruct nflwt as ((((new_node & I_new) & I0) & C_new) & Cp').
    simpl.
    if_tac; subst.
    - set (AS := atomic_shift _ _ _ _ _).
      Intros.
      forward_if.
      + rewrite if_false; auto.
        (* set (nr_p := {| Ig := (Ig nr); Cp := {[x := v]}; Ip := (Ip nr); |}). *)
        gather_SEP AS (node p _ _) (inFP _ _ _ _)
          (own γ_I _) (own γ_k _) (own γ_m _).
        (* md_entry* md = lookup_md(c, p); *)
        set Q1:= fun (v : val) => AS.
        Intros.
        gather_SEP AS (inFP γ_f _ _ _).
        viewshift_SEP 0 (AS ∗ inFP γ_f p nullval l ∗ ∃ lsh : share, ⌜readable_share lsh⌝ ∧
              field_at (cs := coarse_lib.CompSpecs) lsh t_struct_css [StructField _lock] l css).
        { go_lowerx. rewrite bi.sep_emp. iApply lock_alloc. }
        Intros lsh.
        forward.
        (* push back lock into invariant *)
        gather_SEP AS (inFP γ_f p nullval l) (field_at (cs := CompSpecs) lsh _ _ _ _).
        viewshift_SEP 0 (AS ∗ (inFP γ_f p nullval l)).
        { go_lowerx. rewrite bi.sep_emp.
          iApply push_lock_back; auto. }
        (* end - push back lock into invariant *)
        Intros.
        forward_call (l, Q).
        { rewrite /rev_curry /=.
          iIntros "(AU & HinFP & Hnode & HI & Hk & Hm' & Hgv & _ & Hbig)".
          iSplitR "Hgv"; last by iStopProof; cancel.
          unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
          iMod "AU" as (m) "(Hm & HClose)".
          iModIntro.
          iExists tt.
          iDestruct "Hm" as (I r1) "HCSSi".
          iAssert ⌜r = r1⌝ as %->.
          { apply elem_of_dom in H12 as (? & ?).
            rewrite (big_opM_delete _ _ nullval); last by rewrite lookup_delete_ne.
            iDestruct "Hbig" as "(Hmd1 & ?)".
            by iApply (unify_root with "[$HCSSi $Hmd1]"). }
          rewrite /CSSi.
          iDestruct "HCSSi" as (lsh1 lock nr1) "(%Hc & Hglob & Hml & Hf & Hinv & Hown)".
          iDestruct "Hinv" as (b) "(Htm1 & HNF)".
          destruct b.
          2 : { iDestruct (nodeFull_extract with "HNF") as "(_ & HN & ?)".
            apply elem_of_dom in H12 as (? & ?).
            rewrite (big_opM_delete _ _ nullval); last by rewrite lookup_delete_ne.
            iDestruct "Hbig" as "(Hmd1 & ?)".
            iDestruct (md_entry_conflict with "[$Hmd1 $HN]") as "[]".
          }
          iDestruct (same_lock with "[$HinFP $Hglob]") as %(_ & <-).
          iFrame "Htm1".
          iSplit.
          iIntros "Htm1".
          simpl.
          iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css) with
            "[$Hglob $Hml $Hf  Htm1  $Hown]" as "Hcss".
          {
            rewrite /inv_for_lock.
            iExists nr1.
            destruct Hc as (? & ? & ? & ?).
            iSplit; auto.
            iExists true. iFrame.
          }
          iFrame.
          by iApply "HClose".

          iIntros (_) "Hinv".
          iDestruct "Hinv" as "(Htm1 & _)".
          iDestruct "Hglob" as "(%Hglob & HauthI & Hauthk & Hauthm & Hown_nodes)".
          destruct Hglob as (Hglob & Hr).
          iMod (ghost_insert_map_exist _ x v
                 with "[$Hauthm $Hm']") as "(%Hdom_x & Hauthm & Hm')"; auto.
          { rewrite H18. clear. set_solver. }
          set (nr_p := {| Cp := {[x := v]}; Ip := (Ip nr); |}).
          iAssert (md_entry_rep γ_I γ_k γ_m γ_n p nr_p css r1)
            with "[$Hnode $HI Hk Hm']" as "Hmd".
          { rewrite /nr_p /= if_false; auto.
            rewrite ! dom_singleton_L update_singleton H18; auto.
            iFrame "Hk Hm'".
            iPureIntro.
            split; auto.
          }
          iDestruct "HClose" as "(_ & HClose)".
          iApply ("HClose" $! tt).
          simpl.
          rewrite /CSS /CSSi bi.sep_emp.
          destruct (proj1 (elem_of_dom _ _) H12) as (nr0 & ?).
          iExists I, r1, lsh1, lock, nr0.
          iFrame.
          rewrite dom_insert_lookup_L; last by rewrite -elem_of_dom.
          iFrame.
          iSplit; auto.
          iSplit; auto.
          { iPureIntro; split; last done; split; first done.
            intros; destruct Hr as (_ & Hm); first done.
            rewrite Hm in Hdom_x; set_solver. }
          rewrite /inv_for_lock.
          iExists false.
          iFrame "Htm1".
          rewrite /nodeFull2.
          iExists (<[p := nr_p]> Nmap); iSplit.
          + iPureIntro; split3.
            * rewrite -(big_opM_fmap Ip (λ _ n, n)) fmap_insert insert_id.
              rewrite big_opM_fmap //.
              { rewrite lookup_fmap H14 //. }
            * set_solver.
            * split; last by rewrite lookup_insert_ne.
              apply map_Forall_insert_2; auto.
              simpl; by apply (map_Forall_lookup_1 _ _ _ _ H13).
          + rewrite (big_opM_delete _ (<[_:=_]>_)); last by apply lookup_insert.
            rewrite delete_insert_delete; iFrame. }
        simpl.
        forward.
      + done.
    - set (AS := atomic_shift _ _ _ _ _).
      Intros.
      forward_if.
      { easy. }
      (** rename to maintain **)
      rename H8 into Hp_null_r_null. (*p = nullval → r = nullval*)
      rename H9 into Hbelongs. (*p ≠ nullval → belongs x nr*)
      rename H17 into Hmap_choice. (* eq_dec new_node nullval -> ... Cp' = Cp nr \/ ... *)
      rewrite /= in Hmap_choice.
      rename H22 into Hnode_dec_key. (* if eq_dec p nullval -> condition in insertOp *)
      rewrite /= in Hnode_dec_key.
      rename H4 into Hx_inset_Ip. (* in_inset _ _ _ x (Ip nr) p *)
      (** END - rename to maintain **)
      
      forward_if.
      { do 2 sep_apply node_rep_R_valid_pointer. auto with valid_pointer. }
      (** rename to maintain **)
      rename H4 into Heq_p_nullval. (* p = nullval *)
      (** END - rename to maintain **)
      
      pose Heq_p_nullval as Heq_r_nullval.
      apply Hp_null_r_null in Heq_r_nullval.
      rewrite if_true; auto.
      Intros.
      forward.
      rewrite if_false in Hmap_choice; auto.
      gather_SEP AS (inFP _ _ _ _).
      viewshift_SEP 0 (AS ∗ inFP γ_f p nullval l ∗ ∃ lsh : share, ⌜readable_share lsh⌝ ∧
              field_at (cs := coarse_lib.CompSpecs) lsh t_struct_css [StructField _lock] l css).
        { go_lowerx. rewrite bi.sep_emp. iApply lock_alloc. }
      Intros lsh.
      forward.
      destruct Hmap_choice as [Hmap_choice | Hmap_choice].
      + (* Cp' = Cp nr ∧ C_new = {[x := v]} *)
        destruct Hmap_choice as (HCp & HCnew).
        rewrite if_true in Hnode_dec_key; auto.
        destruct Hnode_dec_key as (Hkey_null & Hx_in_ks_new & HdomCp & HSC_null).
        rewrite /SC_null in HSC_null.
        destruct HSC_null as (Hv & HoutIp & HoutI0 & HoutI_new & HdomIp & HdomI0 & HdomI_new &
                        HdomKS & Hks & Hks_disj).
        set (nr_p := {| Cp := Cp' ; Ip := I0; |}).
        set Q1:= fun (v : val) => AS.
        gather_SEP AS.
        rewrite Heq_p_nullval.
        (* push back lock into invariant *)
        rewrite /Q1.
        gather_SEP AS (inFP _ _ _ _) (field_at (cs := CompSpecs) lsh _ _ _ css).
        viewshift_SEP 0 (AS ∗ (inFP γ_f nullval nullval l)).
        { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
        (* end - push back lock into invariant *)
        Intros.
        forward_call (l, Q).
        { rewrite /rev_curry /=.
          iIntros "(AS & HinFP & Hgv & Hml &
                   Hn_new & Hn & HI & Hk & Hm & Hownr & Hf_css & Hbig)".
          iSplitR "Hgv"; last by iStopProof; cancel.
          unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
          iMod "AS" as (m) "[Hcss HClose]".
          rewrite /=.
          iModIntro.
          iExists ().
          iDestruct "Hcss" as (I r1) "HCSSi".
          rewrite /CSSi.
          iDestruct "HCSSi" as (lsh1 lock nr1) "(%Hc & Hglob & Hml1 & Hf & Hinv & Hml2 & Hown)".
          (* new_node ∉ dom I *)
          iDestruct (new_node_fresh with "[$Hml2 Hml $Hn_new]") as %Hnew_notin_domI; try done.
          iAssert ⌜r = r1⌝ as %Hr.
          { apply elem_of_dom in H12 as (? & ?).
            destruct (eq_dec r1 nullval); subst; auto.
            { rewrite -> if_true; auto.
              iDestruct (shot_not_pending with "[$Hown $Hownr]") as %[]. }
          }
          iDestruct "Hinv" as (b) "(Htm1 & HNF)".
          destruct b.
          2: {
            iDestruct (nodeFull_extract with "HNF") as "(_ & HN & ?)".
            iDestruct "HN" as "(? & ? & ? & ? & Hr)".
            rewrite -> (if_true _ (eq_dec nullval _)); auto.
            rewrite -> (if_true _ (eq_dec r1 _)); subst; auto.
            rewrite -> if_true; auto.
            iDestruct "Hr" as "(? & ? & ? & Hr)".
            iDestruct (field_at_conflict Ews t_struct_css (DOT _root) _
                        with "[Hr $Hf_css]") as "[]"; auto; simpl; try lia.
          }
          iDestruct (same_lock with "[$HinFP $Hglob]") as %(_ & <-).
          iFrame "Htm1".
          iSplit.
          iIntros "Htm1".
          iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css) with
            "[$Hglob $Hml1 $Hml2 $Hf Htm1 Hownr]" as "Hcss".
          { rewrite /inv_for_lock.
            iExists nr1.
            destruct Hc as (? & ? & ? & ?).
            iSplit; auto.
            iSplitR "Hownr"; auto; last first.
            rewrite Hr. iFrame.
            iExists true. iFrame.
          }
          iSpecialize ("HClose" with "Hcss").
          iFrame.
          rewrite Hr.
          by iFrame.
          iIntros (_) "Hinv".
          iDestruct "Hinv" as "(Htm1 & _)".
          (*r' = r = nullval *)
          iDestruct "Hglob" as "(%Hglob & HownI & Hownk & Hownm & Hown_nodes)".
          assert (x ∈ keyset Node_EqDecision Node_countable Key (Ip nr) nullval) as Hx_in_keyset.
          { rewrite /keyset /outsets HoutIp big_opS_empty difference_empty_L. by subst. }
          (* x ∉ dom m *)
          iDestruct (key_new_node_fresh _ _ x with "[$Hownk $Hk]") as %Hx_notin_dom_m; auto.
          (* ghost_insert_keyset' *)
          subst.
          iMod (ghost_insert_keyset_add_node _ _ nullval new_node x v m (Cp nr) (Ip nr) I_new I0
                 with "[$Hownk $Hownm $Hk $Hm]")
            as "(Hownk & HkI0 & HkI_new & Hownm & HmI0 & HmI_new)"; try done.
          destruct Hglob as (Hglob & HdomI).
          specialize (HdomI eq_refl).
          destruct HdomI as (HdomI_null & Hmap).
          (* Prove Ip = I *)
          iDestruct (flowEq γ_I I (Ip nr) with "[$HownI $HI]") as %HI.
          { iPureIntro. rewrite HdomI_null HdomIp; try done. }
          iDestruct (md_entries_dom with "[$HownI $Hbig]") as %HNmap.
          { by apply map_Forall_delete. }
          { by destruct Hglob. }
          (* update flow interfaces *)
          iMod (ghost_update_interface_nullval1 _ _ nullval I (Ip nr) I0 I_new new_node lock
                 with "[$HownI $Hown_nodes $HI]") as "Hflow"; try done.
          set (I1 := I0 ⋅ I_new).
          iDestruct "Hflow" as "(%Hctx & HI & HI1 & HI2 & Hown1 & #HinFP_new)".
          destruct Hctx as (Hctx & Hglobinv).
          assert (nullval ∈ dom I1) as Hnull_in_domI1.
          { destruct Hglobinv as (HdomI1 & ?). rewrite HdomI1. clear -HdomI_null. set_solver. }
          iDestruct "HClose" as "(_ & HClose)".
          rewrite -> !if_true; auto.
          iMod (shoot_update _ new_node with "[$Hownr $Hown]") as "Hownr".
          iDestruct (shot_duplicate with "[$Hownr]") as "Hownr".
          iDestruct "Hownr" as "(Hna & Hnf)".
          iAssert (md_entry_rep γ_I γ_k γ_m γ_n nullval nr_p css new_node)
            with "[HmI0 $HI1 HkI0 Hn Hnf Hf_css]" as "Hmd".
          { rewrite /md_entry_rep /nr_p /flowint_dom /= if_false; try done.
            iFrame.
            iSplit; auto.
          }
          set (nr_new := {| Cp := {[x := v]} ; Ip := I_new; |}).
          iAssert (md_entry_rep γ_I γ_k γ_m γ_n new_node nr_new css new_node)
            with "[Hn_new HkI_new HmI_new HI2]" as "Hmd_new".
          { rewrite /md_entry_rep /nr_new dom_singleton_L /=.
            rewrite if_false; try done.
            iFrame. done.
          }
          iApply ("HClose" $! tt).
          iFrame.
          iExists new_node, _.
          iSplit; auto.
          { iPureIntro. by destruct Hc as (? & ? & ? & ?). }
          iSplit; auto.
          iSplitR "Hml2 Hna Hml"; last first.
          { destruct Hglobinv as (HdomI1 & HdomI2).
            rewrite HdomI1.
            setoid_rewrite (big_opS_delete _ _ new_node) at 2.
            assert ((dom I ∪ {[new_node]}) ∖ {[nullval]} ∖ {[new_node]} =
                      dom I ∖ {[nullval]}) as Hdom.
            { clear -H18 HdomI2. set_solver. }
            rewrite Hdom. 
            iFrame.
            rewrite -> if_false; auto. clear -H18 HdomI1. set_solver.
          }
          rewrite /inv_for_lock.
          iExists false. iFrame "Htm1".
          rewrite /nodeFull2.
          assert (Nmap = {[nullval := nr]}) as ->.
          { apply map_eq.
            intros n; destruct (decide (n = nullval)).
            * subst; rewrite lookup_insert //.
            * rewrite HdomI_null dom_delete_L in HNmap.
              rewrite lookup_singleton_ne //.
              apply not_elem_of_dom_1.
              clear -n0 HNmap. set_solver. }
          iExists (<[new_node := nr_new]>({[nullval := nr_p]})); iSplit.
          + iPureIntro; split3.
            * rewrite big_opM_insert; last by apply lookup_singleton_ne.
              rewrite big_opM_insert; last done.
              rewrite big_opM_empty.
              rewrite right_id /= comm //.
            * clear; set_solver.
            * split; last first.
              { rewrite lookup_insert_ne // lookup_singleton //. }
              apply map_Forall_insert_2; auto.
              apply map_Forall_singleton; auto.
          + rewrite big_opM_insert; last by apply lookup_singleton_ne.
            rewrite big_opM_insert; last done.
            iFrame.
            rewrite delete_singleton //. }
        simpl.
        forward.
      + (* contradiction for C <> empty *)
        rewrite Heq_p_nullval.
        gather_SEP (node nullval I0 Cp').
        sep_apply node_nullval_empty; auto. 
        Intros.
        rewrite H8 in Hmap_choice.
        destruct Hmap_choice as (HCp & ?); done.
      + rename H4 into Hp_non_null. (* p ≠ nullval *)
        rewrite if_false in Hmap_choice; auto.
        rewrite if_false in Hnode_dec_key; auto.
        rewrite if_false; auto.
        set Q1:= fun (v : val) => AS.
        destruct Hmap_choice as [HCp | HCp].
        ++ rewrite if_true in Hnode_dec_key; last first.
           { destruct HCp as (HCp & ?). clear - HCp. set_solver. }
           destruct Hnode_dec_key as
             ((Hkey_property1 & Hx_in_ks_new & HdomCp) &
                (HinfI0Ip & HcxtLeq & Hinf & Hk_union & Hk_disj)).
          set (nr_p := {| Cp := Cp'; Ip := I0; |}).
          gather_SEP AS (inFP _ _ _ _).
          viewshift_SEP 0 (AS ∗ inFP γ_f p nullval l ∗
                             ∃ lsh : share, ⌜readable_share lsh⌝ ∧
          field_at (cs := coarse_lib.CompSpecs) lsh t_struct_css [StructField _lock] l css).
          { go_lowerx. rewrite bi.sep_emp. iApply lock_alloc. }
          Intros lsh.
          forward.
          (* push back lock into invariant *)
          rewrite /Q1.
          gather_SEP AS (inFP _ _ _ _) (field_at (cs := CompSpecs) lsh _ _ _ css).
          viewshift_SEP 0 (AS ∗ (inFP γ_f p nullval l)).
          { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
          (* end - push back lock into invariant *)
          Intros.
          forward_call (l, Q).
          { rewrite /rev_curry /=.
            iIntros "(AS & HinFP & Hgv & Hml &
                   Hn_new & Hn & HI & Hk & Hm & _ & Hbig)".
            iSplitR "Hgv"; last by iStopProof; cancel.
            unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
            iMod "AS" as (m) "[Hcss HClose]".
            rewrite /=.
            iModIntro.
            iExists ().
            iDestruct "Hcss" as (I r1) "HCSSi".
            rewrite /CSSi.
            iDestruct "HCSSi" as (lsh1 lock nr1)
                                   "(%Hc & Hglob & Hml1 & Hf & Hinv & Hml2 & Hown)".
            (* new_node ∉ dom I *)
            iDestruct (new_node_fresh with "[$Hml2 Hml $Hn_new]") as %Hnew_notin_domI; try done.
            iDestruct "Hinv" as (b) "(Htm1 & HNF)".
            destruct b.
            2: {
              iDestruct (nodeFull_extract with "HNF") as "(_ & HN & ?)".
              apply elem_of_dom in H12 as (? & ?).
              rewrite (big_opM_delete _ _ nullval); last by rewrite lookup_delete_ne.
              iDestruct "Hbig" as "(Hmd1 & ?)".
              iDestruct (md_entry_conflict with "[$Hmd1 $HN]") as "[]".
            }
            iDestruct (same_lock with "[$HinFP $Hglob]") as %(_ & <-).
            iFrame "Htm1".
            iSplit.
            iIntros "Htm1".
            iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css) with
              "[$Hglob $Hml1 $Hml2 $Hf Htm1 $Hown]" as "Hcss".
            { rewrite /inv_for_lock.
              iExists nr1.
              destruct Hc as (? & ? & ? & ?).
              iSplit; auto.
              iExists true. iFrame.
            }
            iSpecialize ("HClose" with "Hcss").
            by iFrame.
            iIntros (_) "Hinv".
            iDestruct "Hinv" as "(Htm1 & _)".
            iDestruct "Hglob" as "(%Hglob & HownI & Hownk & Hownm & Hown_nodes)".
            assert (x ∈ keyset _ _ _ (Ip nr) p) as Hx_in_keyset.
            { destruct HcxtLeq as (? & ? & ? & ?). rewrite -Hk_union.
              clear -Hx_in_ks_new. set_solver.
            }
            (* x ∉ dom m *)
            iDestruct (key_new_node_fresh _ _ x with "[$Hownk $Hk]") as %Hx_notin_dom_m; auto.
            (* ghost_insert_keyset' *)
            iMod (ghost_insert_keyset_add_node γ_k γ_m p new_node x v m (Cp nr) (Ip nr) I_new I0
                   with "[$Hownk $Hownm $Hk $Hm]")
              as "(Hownk & HkI0 & HkI_new & Hownm & HmI0 & HmI_new)"; try done.
            destruct Hglob as (Hglob & HdomI).
            iDestruct (own_valid_2 γ_I (● I) (◯ (Ip nr)) with "[$] [$]")
              as %Hown%auth_both_valid_discrete.
            destruct Hown as (HownLe & HIvalid).
            iDestruct (md_entries_dom with "[$HownI $Hbig]") as %HNmap.
            { by apply map_Forall_delete. }
            { by destruct Hglob. }
            iMod (ghost_update_interface1 _ _ r1 I (Ip nr) I0 I_new p new_node lock
                   with "[$HownI $Hown_nodes $HI]") as "Hflow"; auto.
            { iPureIntro. repeat (split; auto). }
            hnf in HownLe.
            destruct HownLe as (Iz & HownLe).
            iSpecialize ("Hflow" $! Iz with "[%]"); auto.
            iDestruct "Hflow" as "(%Hctx & HI & HI1 & HI2 & Hown1 & #HinFP_new)".
            destruct Hctx as (_ & Hglobinv).
            iDestruct "HClose" as "(_ & HClose)".
            iAssert (md_entry_rep γ_I γ_k γ_m γ_n p nr_p css r1)
              with "[HmI0 $Hn $HI1 HkI0]" as "Hmd".
            { destruct HCp as (HCp' & HCnew).
              rewrite /md_entry_rep /nr_p HCp' /=.
              rewrite -> if_false; auto.
              by iFrame "∗".
            }
            set (nr_new := {| Cp := C_new; Ip := I_new;|}).
            iAssert (md_entry_rep γ_I γ_k γ_m γ_n new_node nr_new css r1)
              with "[$Hn_new HkI_new HmI_new $HI2]" as "Hmd_new".
            { rewrite if_false; auto.
              destruct HCp as (HCp & HCnew).
              rewrite /nr_new /= HCnew dom_singleton_L /=.
              by iFrame.
            }
            iApply ("HClose" $! tt).
            (* prove md_entry_rep for nullval have root is r1 *)
            pose proof H12 as HNmap_null.
            apply elem_of_dom in H12 as (nr2 & ?).
            rewrite (big_opM_delete _ _ nullval); last by rewrite lookup_delete_ne.
            iDestruct "Hbig" as "(Hmd_null & Hbig)".
            iAssert ⌜r = r1⌝ with "[Hmd_null Hown]" as %->.
            { unfold md_entry_rep at 1.
              rewrite -> if_true; auto.
              iDestruct "Hmd_null" as "(? & ? & ? & ? & ? & ? & Hown1 & ?)".
              destruct (eq_dec r nullval); destruct (eq_dec r1 nullval); subst; auto.
              { iDestruct (shot_not_pending with "[$Hown1 $Hown]") as %[]. }
              { iDestruct (shot_not_pending with "[$Hown1 $Hown]") as %[]. }
              iFrame.
              by iDestruct (shot_agree _ r r1 with "[$Hown1 $Hown]") as %?.
            }
            iFrame.
            iExists nr2.
            iSplit; auto.
            { destruct Hc as (? & ? & ? & ?).
              iPureIntro. repeat (split; auto).
              destruct Hglobinv as (? & ? & ? & ?).
              rewrite H25. clear -H9. set_solver.
            }
            iSplit.
            { destruct Hglobinv as (? & ? & ? & ?).
              iPureIntro.
              do 2  (split; auto).
              intros Hr1.
              specialize (HdomI Hr1).
              destruct HdomI as (HdomI & ?).
              rewrite HdomI in H22.
              apply elem_of_singleton_1 in H22. contradiction.
            }
            iSplitR "Hml Hml2"; last first.
            { destruct Hglobinv as (? & HdomI1 & HdomI2 & ?).
              rewrite HdomI1.
              setoid_rewrite (big_opS_delete _ _ new_node) at 2.
              assert ((dom I ∪ {[new_node]}) ∖ {[nullval]} ∖ {[new_node]} =
                        dom I ∖ {[nullval]}) as Hdom.
              { clear -H18 HdomI2. set_solver. }
              rewrite Hdom. 
              iFrame. clear -H18 HdomI1. set_solver.
            }
            rewrite /inv_for_lock.
            iExists false. iFrame "Htm1".
            rewrite /nodeFull2.
            assert (p ≠ new_node) as Hneq_p_new.
            { intro Hcontra; destruct Hglobinv as (? & ? & ? & HdomIp); subst; contradiction. }
            assert (Nmap !! new_node = None) as HNmap_new.
            {
              assert (new_node ∉ dom Nmap) as Hnew.
              { intros Hcontra.
                assert (new_node ∈ dom (delete p Nmap)).
                { clear -Hcontra Hneq_p_new. set_solver. }
                specialize (elem_of_weaken new_node (dom (delete p Nmap)) (dom I) H9 HNmap).
                easy.
              }
              apply not_elem_of_dom_1; auto.
            }
            iExists (<[new_node := nr_new]>(<[p := nr_p]>Nmap)); iSplit.
            + iPureIntro; split3.
              * rewrite big_opM_insert; last first.
                rewrite lookup_insert_ne; auto.
                rewrite (big_opM_delete _ _ p); last first.
                { rewrite lookup_insert; auto. }
                rewrite delete_insert_delete.
                rewrite /nr_new /nr_p /=.
                apply (global_insert I_new I I0 Nmap p new_node r1 nr nr2); auto.
              * clear -Hneq_p_new HNmap_null H23 Hp_non_null. set_solver. 
              * split; last first.
                {  rewrite ! lookup_insert_ne; eauto. } 
                apply map_Forall_insert_2; auto.
                apply map_Forall_insert_2; auto.
            + rewrite big_opM_insert; last first.
              rewrite lookup_insert_ne; auto.
              setoid_rewrite (big_opM_delete _ _ p) at 2; last first.
              { rewrite lookup_insert; auto. }
              iFrame.
              rewrite delete_insert_delete.
              iClear "HinFP_new HinFP".
              setoid_rewrite (big_opM_delete _ _ nullval) at 2; last first.
              { rewrite lookup_delete_Some.
                repeat (split; auto).
                instantiate (1:= nr2). auto.
              }
              iFrame.
          }
          simpl.
          forward.
       ++ (* Cp' = {[x := v]} ∧ C_new = Cp nr *)
          rewrite if_false in Hnode_dec_key; last first.
          { destruct HCp as (HCp & ?); subst. simpl in *. clear -H19. set_solver. }
          destruct Hnode_dec_key as ((Hkey_property2 & Hx_in_ks_p & HdomCp) &
                                       (HinfI0Ip & HcxtLeq & Hinf & Hk_union & Hk_disj)).
          set (nr_p := {| Cp := Cp'; Ip := I0; |}).
          gather_SEP AS (inFP _ _ _ _).
          viewshift_SEP 0 (AS ∗ inFP γ_f p nullval l ∗
                             ∃ lsh : share, ⌜readable_share lsh⌝ ∧
          field_at (cs := coarse_lib.CompSpecs) lsh t_struct_css [StructField _lock] l css).
          { go_lowerx. rewrite bi.sep_emp. iApply lock_alloc. }
          Intros lsh.
          forward.
          (* push back lock into invariant *)
          rewrite /Q1.
          gather_SEP AS (inFP _ _ _ _) (field_at (cs := CompSpecs) lsh _ _ _ css).
          viewshift_SEP 0 (AS ∗ (inFP γ_f p nullval l)).
          { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
          (* end - push back lock into invariant *)
          Intros.
          forward_call (l, Q).
          { rewrite /rev_curry /=.
            iIntros "(AS & HinFP & Hgv & Hml &
                   Hn_new & Hn & HI & Hk & Hm & _ & Hbig)".
            iSplitR "Hgv"; last by iStopProof; cancel.
            unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
            iMod "AS" as (m) "[Hcss HClose]".
            rewrite /=.
            iModIntro.
            iExists ().
            iDestruct "Hcss" as (I r1) "HCSSi".
            rewrite /CSSi.
            iDestruct "HCSSi" as (lsh1 lock nr1)
                                   "(%Hc & Hglob & Hml1 & Hf & Hinv & Hml2 & Hown)".
            (* new_node ∉ dom I *)
            iDestruct (new_node_fresh with "[$Hml2 Hml $Hn_new]") as %Hnew_notin_domI; try done.
            iDestruct "Hinv" as (b) "(Htm1 & HNF)".
            destruct b.
            2: {
              iDestruct (nodeFull_extract with "HNF") as "(_ & HN & ?)".
              apply elem_of_dom in H12 as (? & ?).
              rewrite (big_opM_delete _ _ nullval); last by rewrite lookup_delete_ne.
              iDestruct "Hbig" as "(Hmd1 & ?)".
              iDestruct (md_entry_conflict with "[$Hmd1 $HN]") as "[]".
            }
            iDestruct (same_lock with "[$HinFP $Hglob]") as %(_ & <-).
            iFrame "Htm1".
            iSplit.
            iIntros "Htm1".
            iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css) with
              "[$Hglob $Hml1 $Hml2 $Hf Htm1 $Hown]" as "Hcss".
            { rewrite /inv_for_lock.
              iExists nr1.
              destruct Hc as (? & ? & ? & ?).
              iSplit; auto.
              iExists true. iFrame.
            }
            iSpecialize ("HClose" with "Hcss").
            by iFrame.
            iIntros (_) "Hinv".
            iDestruct "Hinv" as "(Htm1 & _)".
            iDestruct "Hglob" as "(%Hglob & HownI & Hownk & Hownm & Hown_nodes)".
            assert (x ∈ keyset _ _ _ (Ip nr) p) as Hx_in_keyset.
            { destruct HcxtLeq as (? & ? & ? & ?). rewrite -Hk_union. set_solver. }
            (* x ∉ dom m *)
            iDestruct (key_new_node_fresh _ _ x with "[$Hownk $Hk]") as %Hx_notin_dom_m; auto.
            (* ghost_insert_keyset in between - special case for linked list *)
            iMod (ghost_insert_keyset_add_node_between _ _ p new_node x v m (Cp nr) (Ip nr) I_new I0
                   with "[$Hownk $Hownm $Hk $Hm]")
              as "(Hownk & HkI0 & HkI_new & Hownm & HmI0 & HmI_new)"; auto.
            destruct Hglob as (Hglob & HdomI).
            iDestruct (own_valid_2 γ_I (● I) (◯ (Ip nr)) with "[$] [$]")
              as %Hown%auth_both_valid_discrete.
            destruct Hown as (HownLe & HIvalid).
            iDestruct (md_entries_dom with "[$HownI $Hbig]") as %HNmap.
            { by apply map_Forall_delete. }
            { by destruct Hglob. }
            iMod (ghost_update_interface1 _ _ r1 I (Ip nr) I0 I_new p new_node lock
                   with "[$HownI $Hown_nodes $HI]") as "Hflow"; auto.
            { iPureIntro. repeat (split; auto). }
            hnf in HownLe.
            destruct HownLe as (Iz & HownLe).
            iSpecialize ("Hflow" $! Iz with "[%]"); auto.
            set (I1 := I0 ⋅ I_new ⋅ Iz).
            iDestruct "Hflow" as "(%Hctx & HI & HI1 & HI2 & Hown1 & #HinFP_new)".
            destruct Hctx as (Hctx & Hglobinv).
            iDestruct "HClose" as "(_ & HClose)".
            iAssert (md_entry_rep γ_I γ_k γ_m γ_n p nr_p css r1)
              with "[HmI_new $Hn $HI1 HkI0]" as "Hmd".
            { destruct HCp as (HCp' & HCnew).
              rewrite /md_entry_rep /nr_p HCp' /= dom_singleton_L.
              rewrite -> if_false; auto.
              by iFrame "∗".
            }
            set (nr_new := {| Cp := C_new; Ip := I_new; |}).
            iAssert (md_entry_rep γ_I γ_k γ_m γ_n new_node nr_new css r1)
              with "[$Hn_new HkI_new HmI0 $HI2]" as "Hmd_new".
            { rewrite if_false; auto.
              destruct HCp as (HCp & HCnew).
              rewrite /nr_new /= HCnew.
              by iFrame.
            }
            iApply ("HClose" $! tt).
            (* prove md_entry_rep for nullval have root is r1 *)
            pose proof H12 as HNmap_null.
            apply elem_of_dom in H12 as (nr2 & ?).
            rewrite (big_opM_delete _ _ nullval); last by rewrite lookup_delete_ne.
            iDestruct "Hbig" as "(Hmd_null & Hbig)".
            iAssert ⌜r = r1⌝ with "[Hmd_null Hown]" as %->.
            { unfold md_entry_rep at 1.
              rewrite -> if_true; auto.
              iDestruct "Hmd_null" as "(? & ? & ? & ? & ? & ? & Hown1 & ?)".
              destruct (eq_dec r nullval); destruct (eq_dec r1 nullval); subst; auto.
              { iDestruct (shot_not_pending with "[$Hown1 $Hown]") as %[]. }
              { iDestruct (shot_not_pending with "[$Hown1 $Hown]") as %[]. }
              iFrame.
              by iDestruct (shot_agree _ r r1 with "[$Hown1 $Hown]") as %?.
            }
            iFrame.
            iExists nr2.
            iSplit; auto.
            { destruct Hc as (? & ? & ? & ?).
              iPureIntro. repeat (split; auto).
              destruct Hglobinv as (? & ? & ? & ?).
              rewrite H25. clear -H9. set_solver.
            }
            iSplit.
            { destruct Hglobinv as (? & ? & ? & ?).
              iPureIntro.
              do 2  (split; auto).
              intros Hr1.
              specialize (HdomI Hr1).
              destruct HdomI as (HdomI & ?).
              rewrite HdomI in H22.
              apply elem_of_singleton_1 in H22. contradiction.
            }
            iSplitR "Hml Hml2"; last first.
            { destruct Hglobinv as (? & HdomI1 & HdomI2 & ?).
              rewrite HdomI1.
              setoid_rewrite (big_opS_delete _ _ new_node) at 2.
              assert ((dom I ∪ {[new_node]}) ∖ {[nullval]} ∖ {[new_node]} =
                        dom I ∖ {[nullval]}) as Hdom.
              { clear -H18 HdomI2. set_solver. }
              rewrite Hdom. 
              iFrame. clear -H18 HdomI1. set_solver.
            }
            rewrite /inv_for_lock.
            iExists false. iFrame "Htm1".
            rewrite /nodeFull2.
            assert (p ≠ new_node) as Hneq_p_new.
            { intro Hcontra; destruct Hglobinv as (? & ? & ? & HdomIp); subst; contradiction. }
            assert (Nmap !! new_node = None) as HNmap_new.
            { assert (new_node ∉ dom Nmap) as Hnew.
              { intros Hcontra.
                assert (new_node ∈ dom (delete p Nmap)).
                { clear -Hcontra Hneq_p_new. set_solver. }
                specialize (elem_of_weaken new_node (dom (delete p Nmap)) (dom I) H9 HNmap).
                easy.
              }
              apply not_elem_of_dom_1; auto.
            }
            iExists (<[new_node := nr_new]>(<[p := nr_p]>Nmap)); iSplit.
            + iPureIntro; split3.
              * rewrite big_opM_insert; last first.
                rewrite lookup_insert_ne; auto.
                rewrite (big_opM_delete _ _ p); last first.
                { rewrite lookup_insert; auto. }
                rewrite delete_insert_delete.
                rewrite /nr_new /nr_p /=.
                apply (global_insert I_new I I0 Nmap p new_node r1 nr nr2); auto.
              * clear -Hneq_p_new HNmap_null H23 Hp_non_null. set_solver. 
              * split; last first.
                {  rewrite ! lookup_insert_ne; eauto. } 
                apply map_Forall_insert_2; auto.
                apply map_Forall_insert_2; auto.
            + rewrite big_opM_insert; last first.
              rewrite lookup_insert_ne; auto.
              setoid_rewrite (big_opM_delete _ _ p) at 2; last first.
              { rewrite lookup_insert; auto. }
              iFrame.
              rewrite delete_insert_delete.
              iClear "HinFP_new HinFP".
              setoid_rewrite (big_opM_delete _ _ nullval) at 2; last first.
              { rewrite lookup_delete_Some.
                repeat (split; auto).
                instantiate (1:= nr2). auto.
              }
              iFrame.
          }
          simpl.
          forward.
     Qed.

End verif_coarse_grained_template.
