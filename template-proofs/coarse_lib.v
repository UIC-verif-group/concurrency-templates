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
Require Import tmpl.frac.
Require Import tmpl.keyset_ra_ora.
Require Export tmpl.data_struct.
Require Export tmpl.interface_more.
Require Export tmpl.template_class. (* template class *)
Require Export tmpl.coarse. (* AST of coarse.c *)

Definition one_shotR := csumR fracR (agreeR (leibnizO val)).
Class one_shotG Σ := { #[local] one_shot_inG :: inG Σ one_shotR }.

Definition one_shotΣ : gFunctors := #[GFunctor one_shotR].
Global Instance subG_one_shotΣ {Σ} : subG one_shotΣ Σ → one_shotG Σ.
Proof. solve_inG. Qed.

Section coarse_grained_lock.
  #[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
  Definition Vprog : varspecs. mk_varspecs prog. Defined.

  Context `{NR: NodeRep} `{EqDecision K} `{Countable K}.
  Context `{!cinvG Σ, atom_impl : !atomic_int_impl (Tstruct _atom_int noattr), !flowintG Σ,
        !nodesetG Σ, !nodemapG Σ, !keymapG Σ, !keysetG Σ, !one_shotG Σ}.

  Record NodeR := { Cp : gmap Key KValue; Ip : flowint_T; }.

  Definition belongs (x : Z) (nr : NodeR) : Prop := True.

  Definition is_root (γ_n : gname) (r : val) : mpred :=
    if eq_dec r nullval then emp
    else own (inG0 := one_shot_inG) γ_n (Cinr $ (to_agree r)).

  Definition md_entry_rep γ_I γ_k γ_m γ_n (p : Node) (nr : NodeR) css (r : val): mpred :=
    ⌜is_pointer_or_null p⌝ ∧
      node p (Ip nr) (Cp nr) ∗ own γ_I (◯ (Ip nr)) ∗
        own γ_k (◯ prod (keyset _ _ _ nr.(Ip) p, dom (Cp nr)): keyset_authR Key) ∗
        own γ_m (◯ (Excl <$> (Cp nr)) : keymap_authR _ _) ∗
        (if eq_dec p nullval then
          ⌜is_pointer_or_null r⌝ ∧
            (if eq_dec r nullval then own γ_n (Cinl (1/2)%Qp : csumR _ _)
             else own γ_n (Cinr $ (to_agree r : (agreeR valC)))) ∗
          field_at (cs := CompSpecs) Ews t_struct_css (DOT _root) r css else emp).

  Arguments Qp.div : simpl never.

  Lemma shot_not_pending γ_n a b: own γ_n (Cinl a) ∗ own γ_n (Cinr b) ⊢ False.
  Proof.
    intros.
    iIntros "(Hs & Hp)".
    iDestruct (own_valid_2 with "Hs Hp") as "H".
    iDestruct "H" as %[].
  Qed.

  Lemma shot_agree γ_n r r':
    own γ_n (Cinr (to_agree r)) ∗ own γ_n (Cinr (to_agree r')) ⊢ ⌜r = r'⌝.
  Proof.
    iIntros "(Hs1 & Hs2)".
    iDestruct (own_valid_2 with "Hs1 Hs2") as %Hfoo.
    iPureIntro. apply to_agree_op_inv_L.
    by rewrite -Cinr_op Cinr_valid in Hfoo.
  Qed.

  Definition own_nodes1 γ_f (I : @multiset_flowint_ur Key _ _ ) lock:=
    ∃ N, ⌜dom N = dom I /\
           (forall n m l, N !! n = Some (m, l) ->
                     is_pointer_or_null n /\
                       is_pointer_or_null l /\ m = nullval /\ l = lock)⌝ ∧
           own (inG0 := nodemap_inG) γ_f (● (to_agree <$> N)).

   Lemma node_same_lock γ_f n m l lock (I: @multiset_flowint_ur Key _ _):
    inFP γ_f n m l ∗ own_nodes1 γ_f I lock  ⊢ ⌜m = nullval /\ lock = l⌝.
  Proof.
    intros; iIntros "(#Hfp & Hown)".
    iDestruct "Hfp" as (N1) "[Hown1 %HSome]".
    iDestruct "Hown" as (N0) "(%Hdom & Hown)".
    iDestruct (own_valid_2 γ_f (● (to_agree <$> N0): gmap_authR _ _) (◯ (to_agree <$> N1))
                with "[$] [$]") as "%Hown".
    rewrite auth_both_valid_discrete in Hown.
    destruct Hown as (Hown & _).
    rewrite lookup_included in Hown.
    specialize (Hown n).
    rewrite ! lookup_fmap HSome /= in Hown.
    iPureIntro.
    pose proof Hown as Hown'.
    destruct Hdom as (Hdom & Hznth).
    clear Hdom.
    assert (is_Some (N0 !! n)) as HSome'.
    { apply Some_included_is_Some in Hown.
      destruct (N0 !! n) eqn: E; try done.
      rewrite fmap_is_Some //= in Hown.
    }
    rewrite /is_Some in HSome'.
    destruct HSome' as (? & HSome').
    destruct x as (m' & l').
    rewrite HSome' Some_included_total to_agree_included_L /= in Hown; subst.
    inversion Hown; subst.
    apply Hznth in HSome'.
    destruct HSome' as (? & ? & ? & ?); auto.
  Qed.

  Definition globalGhost γ_I γ_f γ_k γ_m r (C : gmap Key KValue)
    (I: @flowintT _ K_multiset_ccm _ _) lock :=
    ⌜globalinv _ _ _ r I /\ (r = nullval -> dom I = {[nullval]} /\ C = ∅)⌝ ∧
    own γ_I (● I) ∗ own γ_k (● prod (KS, dom C) : keyset_authR Key) ∗
    own γ_m (● (Excl <$> C) : keymap_authR _ _) ∗ own_nodes1 γ_f I lock.

  Definition nodeFull2 (γ_I γ_k γ_m γ_n : gname) (p1 : val) (p : Node) (nr : NodeR) css r : mpred :=
    ∃ (N : gmap Node NodeR),
      let I := [^op map] p↦nr ∈ N, Ip nr in
      ⌜globalinv _ _ _ r I /\ nullval ∈ dom N /\ map_Forall (λ p nr, dom (Ip nr) = {[p]}) N /\ N !! p = Some nr⌝ ∧
       [∗ map] pt↦nr1 ∈ N, md_entry_rep γ_I γ_k γ_m γ_n pt nr1 css r.

  (* this is only useful when not changing the node *)
  Lemma nodeFull_extract : forall γ_I γ_k γ_m γ_n l p nr css r,
    nodeFull2 γ_I γ_k γ_m γ_n l p nr css r ⊢
      ⌜dom (Ip nr) = {[p]}⌝ ∧
      md_entry_rep γ_I γ_k γ_m γ_n p nr css r ∗
      (md_entry_rep γ_I γ_k γ_m γ_n p nr css r -∗ nodeFull2 γ_I γ_k γ_m γ_n l p nr css r).
  Proof.
    intros; unfold nodeFull2.
    iIntros "(%N & (% & % & % & %Hp) & H)".
    iDestruct (big_sepM_lookup_acc with "H") as "H"; first done.
    iDestruct "H" as "($ & H)".
    iSplit; first by auto.
    iIntros "Hp"; iExists N.
    iSplit; first done.
    by iApply "H".
  Qed.

  Lemma big_opM_dom : forall {K V} `{Countable K} (f : V -> flowint_T) (m : gmap K V), ✓ ([^op map] k↦v ∈ m, f v) ->
    dom ([^op map] k↦v ∈ m, f v) = [^union map] k↦v ∈ m, dom (f v).
  Proof.
    intros; induction m using map_first_key_ind.
    - rewrite !big_opM_empty //.
    - rewrite big_opM_insert // in H1 |- *.
      rewrite intComp_dom // IHm.
      apply leibniz_equiv; rewrite big_opM_insert //.
      { by eapply cmra_valid_op_r. }
  Qed.

  Lemma big_unionM_exists : forall {A K V} `{Countable K} `{Countable A} (f : K -> V -> gset A) (m : gmap K V) x,
    x ∈ ([^union map] k↦v ∈ m, f k v) -> exists k v, m !! k = Some v /\ x ∈ f k v.
  Proof.
    intros; induction m using map_first_key_ind.
    - rewrite big_opM_empty // in H2.
    - rewrite big_opM_insert // in H2.
      destruct (decide (x ∈ f i x0)).
      + eexists i, _; rewrite lookup_insert //.
      + apply elem_of_union in H2 as [? | Hx]; first done.
        apply IHm in Hx as (? & ? & ? & ?).
        eexists _, _; rewrite lookup_insert_ne //.
        congruence.
  Qed.

  Lemma big_unionM_exists2 : forall {A K V} `{Countable K} `{Countable A} (f : K -> V -> gset A) (m : gmap K V) x k v,
    m !! k = Some v -> x ∈ f k v -> x ∈ ([^union map] k↦v ∈ m, f k v).
  Proof.
    intros; induction m using map_first_key_ind.
    - done.
    - rewrite big_opM_insert //.
      destruct (decide (i = k)).
      + subst; rewrite lookup_insert in H2; inv H2. set_solver.
      + rewrite lookup_insert_ne // in H2.
        apply IHm in H2; set_solver.
  Qed.

  Lemma node_map_dom : forall N, ✓ ([^op map] p↦nr ∈ N, Ip nr) ->
    map_Forall (λ p nr, dom (Ip nr) = {[p]}) N ->
    dom ([^op map] p↦nr ∈ N, Ip nr) = dom N.
  Proof.
    intros; rewrite big_opM_dom //.
    apply set_eq; split.
    - intros (? & ? & ? & Hdom)%big_unionM_exists.
      eapply map_Forall_lookup_1 in H1; last done.
      rewrite H1 in Hdom; apply elem_of_singleton in Hdom as <-.
      by eapply elem_of_dom_2.
    - intros (? & ?)%elem_of_dom.
      eapply big_unionM_exists2; first done.
      eapply map_Forall_lookup_1 in H1; last done.
      rewrite H1 elem_of_singleton //.
  Qed.

  Lemma nodeFull_switch_null : forall γ_I γ_k γ_m γ_n p1 p nr css r p1',
    nodeFull2 γ_I γ_k γ_m γ_n p1 p nr css r ⊢ ∃ nr', nodeFull2 γ_I γ_k γ_m γ_n p1' nullval nr' css r.
  Proof.
    intros; unfold nodeFull2.
    iIntros "(%N & (%Hglobal & %Hnull & %Hdom & %Hp) & $)".
    destruct (proj1 (elem_of_dom _ _) Hnull); eauto.
  Qed.

  Lemma valid_Ip_md γ_I γ_k γ_m γ_n p nr css r:
    md_entry_rep γ_I γ_k γ_m γ_n p nr css r ⊢ ⌜✓ (Ip nr)⌝.
  Proof.
    iIntros "(? & ? & Hown & ?)".
    iDestruct (own_valid with "Hown") as %Hown.
    iPureIntro.
    apply auth_frag_valid; auto.
  Qed.

  Lemma distinct_node k (Ip: @multiset_flowint_ur Key _ _) p q:
    ✓ Ip -> p ∈ dom Ip -> in_outset _ _ _ k Ip q -> p <> q.
  Proof.
    intros Hv Hdom Hin.
    destruct (decide (p = q)); subst; auto.
    rewrite /in_outset in Hin.
    apply (intValid_in_dom_not_out Ip q) in Hv; auto.
    rewrite Hv in Hin. set_solver.
  Qed.

  Lemma nodeFull_switch1 : forall γ_I γ_k γ_m γ_n p1 p nr css r k p1' p',
    p <> p' ->
    k ∈ outset _ _ _ (Ip nr) p' ->
    nodeFull2 γ_I γ_k γ_m γ_n p1 p nr css r ⊢
      ∃ nr', ⌜in_inset _ _ _ k (Ip nr') p'⌝ ∧ nodeFull2 γ_I γ_k γ_m γ_n p1' p' nr' css r.
  Proof.
    intros; unfold nodeFull2.
    iIntros "(%N & (%Hglobal & % & %Hdom & %Hp) & H)".
    destruct (N !! p') as [nr'|] eqn: Hp'.
    { iExists nr'.
      pose proof Hglobal as Hglobal1.
      destruct Hglobal as (Hvalid & _ & Hclosed & _).
      assert (([^op map] nr ∈ N, Ip nr) = Ip nr ⋅ ([^op map] y ∈ delete p N, Ip y)) as HN.
      { apply insert_delete in Hp; rewrite -{1}Hp big_opM_insert // lookup_delete //. }
      assert (([^op map] y ∈ delete p N, Ip y) =
                Ip nr' ⋅ ([^op map] y ∈ delete p (delete p' N), Ip y)) as HN1.
      { apply insert_delete in Hp'; rewrite -{1} Hp' delete_insert_ne // big_opM_insert //
                                               lookup_delete_ne // lookup_delete // . }
      rewrite HN1 in HN.
      pose proof Hvalid as Hvalid1.
      rewrite HN in Hvalid.
      assert (([^op map] nr ∈ N, Ip nr) =
                (Ip nr) ⋅ (Ip nr') ⋅ ([^op map] y ∈ delete p' (delete p N), Ip y)) as HN2.
      { apply insert_delete in Hp; rewrite -{1}Hp big_opM_insert //.
        erewrite <- lookup_delete_ne in Hp'; eauto.
        apply insert_delete in Hp'; rewrite -{1}Hp' big_opM_insert //.
        rewrite intComp_assoc_valid delete_commute //.
        rewrite lookup_delete //.
        rewrite lookup_delete //.
      }
      assert (✓ (Ip nr ⋅ Ip nr')) as Hvalid2.
      { rewrite HN2 in Hvalid1. eapply intComp_valid_proj1; eauto. }
      assert (in_inset Node_EqDecision Node_countable Key k (Ip nr') p') as Hin_inset.
      { eapply flowint_inset_step; eauto.
        apply Hdom in Hp'. set_solver.
      }
      iSplit; auto.
    }
    exfalso.
    destruct Hglobal as (Hvalid & _ & Hclosed & _).
    assert (([^op map] nr ∈ N, Ip nr) = Ip nr ⋅ ([^op map] y ∈ delete p N, Ip y)) as HN.
    { apply insert_delete in Hp; rewrite -{1}Hp big_opM_insert //.
      apply lookup_delete. }
    eapply flowint_step in Hclosed; try done.
    rewrite big_opM_dom in Hclosed.
    apply big_unionM_exists in Hclosed as (? & ? & Hx & Hin).
    apply lookup_delete_Some in Hx as (? & Hx).
    eapply map_Forall_lookup_1 in Hdom; last done.
    rewrite Hdom in Hin.
    apply elem_of_singleton in Hin; congruence.
    { rewrite HN in Hvalid; by eapply cmra_valid_op_r. }
  Qed.
  
  Definition CSSi (γ_I γ_f γ_k γ_g γ_m γ_n : gname) r C css I: mpred :=
    ∃ lsh lock nr,
      ⌜nullval ∈ dom I /\ readable_share lsh /\ is_pointer_or_null lock /\ is_pointer_or_null r⌝ ∧
      globalGhost γ_I γ_f γ_k γ_m r C I lock ∗ malloc_token Ews t_struct_css css ∗
      field_at lsh t_struct_css [StructField _lock] lock css ∗
      inv_for_lock lock (nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr css r) ∗
      ([∗ set] p ∈ dom I ∖ {[nullval]},
        malloc_token (cs := (@DS_compspecs Σ VSTGS0 NR)) Ews1 t_struct_node p) ∗
           (if eq_dec r nullval then own γ_n (Cinl (1/2)%Qp) else own γ_n (Cinr $ (to_agree r))).
 
  Definition CSS γ_I γ_f γ_k γ_g γ_m γ_n C css : mpred :=
    ∃ I r, CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I.

  Lemma new_node_fresh new_node (I I_new: @multiset_flowint_ur Key _ _) C_new
     (Hsz: (0 < @sizeof (@DS_compspecs Σ VSTGS0 NR) t_struct_node)%Z) (Hnew: new_node <> nullval):
    node new_node I_new C_new ∗
      malloc_token (cs := (@DS_compspecs Σ VSTGS0 NR)) Ews1 t_struct_node new_node ∗
      ([∗ set] p ∈ dom I ∖ {[nullval]},
        malloc_token (cs := (@DS_compspecs Σ VSTGS0 NR)) Ews1 t_struct_node p)
      ⊢ ⌜new_node ∉ dom I⌝.
  Proof.
    iIntros "(Hnew & Hml & Hbig)".
    destruct (decide (new_node ∈ dom I)); subst; auto.
    setoid_rewrite (big_opS_delete _ _ new_node) at 1; auto.
    iDestruct "Hbig" as "(Hml1 & Hbig)".
    iDestruct (@malloc_token_conflict with "[$Hml $Hml1]") as "?"; auto.
    set_solver.
  Qed.

  Lemma nodeFull_switch_root : forall γ_I γ_k γ_m γ_n p1 p nr css r,
      nodeFull2 γ_I γ_k γ_m γ_n p1 p nr css r ⊢
        ∃ nr', nodeFull2 γ_I γ_k γ_m γ_n p r nr' css r.
  Proof.
    intros; unfold nodeFull2.
    iIntros "(%N & (%Hglobal & % & %Hdom & %Hp) & $)".
    assert (r ∈ dom N) as Hr.
    { destruct Hglobal as (? & ? & ?); rewrite <- node_map_dom; auto. }
    apply elem_of_dom in Hr as (? & ?); eauto.
  Qed.

  Lemma valid_pointer_r : forall γ_I γ_k γ_m γ_n p1 p nr css r,
      nodeFull2 γ_I γ_k γ_m γ_n p1 p nr css r ⊢ valid_pointer r.
  Proof.
    intros.
    rewrite nodeFull_switch_root.
    iIntros "(% & H)".
    iDestruct (nodeFull_extract with "H") as "(_ & H & _)".
    iDestruct "H" as "(? & Hn & ?)".
    iApply (node_rep_R_valid_pointer with "Hn").
  Qed.

  Lemma nodeFull_switch_node : forall γ_I γ_k γ_m γ_n p1 nr css r p pn,
      own γ_n (Cinr (to_agree p)) ∗ nodeFull2 γ_I γ_k γ_m γ_n p1 nullval nr css r ⊢
        (own γ_n (Cinr (to_agree p)) ∗ 
        (∃ nr', nodeFull2 γ_I γ_k γ_m γ_n pn p nr' css r)) ∧ valid_pointer p.
  Proof.
    intros; unfold nodeFull2 at 1.
    iIntros "(Hown & (%N & (%Hglobal & % & %Hdom & %Hp) & H))".
    rewrite (big_opM_delete _ _ nullval); eauto.
    iDestruct "H" as "((H1 & H2 & H3 & H4 & H5 & H6 & Hown1 & H7) & Hbig)".
    destruct (eq_dec r nullval); subst; auto.
    - rewrite -> if_true; auto.
      iDestruct (shot_not_pending with "[$Hown $Hown1]") as %[].
    - rewrite -> if_false; auto.
      iDestruct (shot_agree with "[$Hown $Hown1]") as %Hpr.
      iAssert (∃ nr', nodeFull2 γ_I γ_k γ_m γ_n pn r nr' css r)
        with "[H1 H2 H3 H4 H5 H6 Hown1 H7 Hbig]" as "(% & Hbig)".
      { assert (r ∈ dom N) as Hr.
        { destruct Hglobal as (? & ? & ?); by rewrite <- node_map_dom. }
        apply elem_of_dom in Hr as (nr2 & ?).
        iExists nr2, N.
        setoid_rewrite (big_opM_delete _ _ nullval) at 3; eauto.
        iFrame.
        iSplit; auto.
        rewrite -> if_false; auto.
      }
      rewrite Hpr.
      iSplit; try iFrame.
      iApply (valid_pointer_r with "Hbig").
  Qed.

  Lemma nodeFull_conflict γ_I γ_k γ_m γ_n p1 p css a b r1 r2:
    nodeFull2 γ_I γ_k γ_m γ_n p1 p a css r1 ∗
      nodeFull2 γ_I γ_k γ_m γ_n p1 p b css r2 ⊢ False.
  Proof.
    iIntros "(H1 & H2)".
    iDestruct (nodeFull_switch_null _ _ _ _ _ _ _ _ _ p1 with "H1") as "(% & H1)".
    iDestruct (nodeFull_switch_null _ _ _ _ _ _ _ _ _ p1 with "H2") as "(% & H2)".
    iDestruct (nodeFull_extract with "H1") as "(_ & Hmd1 & _)".
    iDestruct (nodeFull_extract with "H2") as "(_ & Hmd2 & _)".
    iDestruct "Hmd1" as "(_ & Hn1 & _ & _ & _ & Hfm1)".
    iDestruct "Hmd2" as "(_ & Hn2 & _ & _ & _ & Hfm2)".
    rewrite -> !(if_true _ (eq_dec nullval nullval)); auto.
    iDestruct "Hfm1" as "(? & ? & Hfm1)".
    iDestruct "Hfm2" as "(? & ? & Hfm2)".
    iDestruct (field_at_conflict (cs := CompSpecs) Ews t_struct_css (DOT _root)
                  with "[$Hfm1 $Hfm2]") as "?"; auto; simpl; lia.
  Qed.

  Lemma md_entry_conflict γ_I γ_k γ_m γ_n (p : Node) nr1 nr2 css r1 r2:
    md_entry_rep γ_I γ_k γ_m γ_n p nr1 css r1 ∗ md_entry_rep γ_I γ_k γ_m γ_n p nr2 css r2 ⊢ False.
  Proof.
    rewrite /md_entry_rep.
    iIntros "((? & Hn1 & ? & ? & ? & Hfn1) & ? & Hn2 & ? & ? & ? & Hfn2)".
    destruct (decide (p = nullval)); subst.
    - rewrite -> ! (if_true _ (eq_dec nullval _)); auto.
      iDestruct "Hfn1" as "(? & ? & Hfn1)".
      iDestruct "Hfn2" as "(? & ? & Hfn2)".
      iDestruct (field_at_conflict (cs := CompSpecs) Ews t_struct_css (DOT _root)
                  with "[$Hfn1 $Hfn2]") as "?"; auto; simpl; lia.
    - iDestruct (node_sep_star with "[$Hn1 $Hn2]") as "?"; auto.
  Qed.

  Lemma nodeFull_exclusive γ_I γ_k γ_m γ_n css nr r:
    exclusive_mpred (nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr css r).
  Proof. rewrite /exclusive_mpred nodeFull_conflict; auto. Qed.

  Lemma inv_lock a b c r1 r2 r3 γ_I γ_k γ_m γ_n (p : Node) p1 lock_in css :
    nodeFull2 γ_I γ_k γ_m γ_n p1 p a css r1 ∗
      inv_for_lock lock_in (nodeFull2 γ_I γ_k γ_m γ_n p1 p b css r2) ⊢
      nodeFull2 γ_I γ_k γ_m γ_n p1 p a css r1 ∗
      inv_for_lock lock_in (nodeFull2 γ_I γ_k γ_m γ_n p1 p c css r3).
  Proof.
    iIntros "(H1 & H2)".
    iDestruct "H2" as (b0) "(H2 & H3)".
    destruct b0.
    - iFrame "H1". iExists _. iFrame.
    - iExFalso. iPoseProof (nodeFull_conflict with "[$H1 $H3]") as "?"; auto.
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
    apply cleave_readable1 in Hr.
    apply cleave_readable2 in Kr.
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

  Lemma same_lock γ_I γ_f γ_k γ_m n m l lock (I: @multiset_flowint_ur Key _ _) C r:
    inFP γ_f n m l ∗ globalGhost γ_I γ_f γ_k γ_m r C I lock  ⊢ ⌜m = nullval /\ lock = l⌝.
  Proof.
    iIntros "(HinFP & Hglob)".
    rewrite /globalGhost.
    iDestruct "Hglob" as "(? & ? & ? & ? & Hown)".
    iDestruct (node_same_lock with "[$HinFP $Hown]") as "?"; auto.
  Qed.

  Lemma in_tree_inv (γ_I γ_f γ_k γ_g γ_m γ_n : gname) p p1 l C css:
    inFP γ_f p p1 l ∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C css ⊢
      (∃ r nr, ⌜is_pointer_or_null r /\ p1 = nullval⌝ ∧ inv_for_lock l (nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr css r) ∗
                 (inv_for_lock l (nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr css r)
                  -∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C css)).
  Proof.
    iIntros "(#HinFP & Hcss)".
    iDestruct "Hcss" as (I r lsh lock nr) "Hcss".
    iDestruct "Hcss" as "(%Hc & Hglob & ? & ? & Hinv & ?)".
    destruct Hc as (? & ? & ? & ?).
    iDestruct (same_lock with "[$HinFP $Hglob]") as %(-> & ->).
    iExists r.
    iFrame "Hinv".
    iSplit; auto.
    iIntros "Hinv".
    iFrame.
    iSplit; auto.
  Qed.

  Lemma md_entries_dom γ_I γ_k γ_m γ_n css r I M :
    map_Forall (λ (p : Node) (nr : NodeR), dom (Ip nr) = {[p]}) M -> ✓ I ->
    own γ_I (● I) ∗ ([∗ map] k↦y ∈ M, md_entry_rep γ_I γ_k γ_m γ_n k y css r) ⊢ ⌜dom M ⊆ dom I⌝.
  Proof.
    intros Hdom ?.
    rewrite elem_of_subseteq.
    iIntros "(●I & M)" (? (? & Hin)%elem_of_dom).
    rewrite map_Forall_lookup in Hdom; specialize (Hdom _ _ Hin).
    iDestruct (big_sepM_lookup_acc with "M") as "(M & _)"; first done.
    iDestruct "M" as "(_ & _ & ◯I & _)".
    iDestruct (own_valid_2 with "●I ◯I") as %((? & [=]) & _)%auth_both_valid_discrete; subst.
    iPureIntro; apply intComp_dom_subseteq_l; first done.
    set_solver.
  Qed.

  Lemma lock_alloc {A} (b: gmap Key KValue → A → iPropI Σ) (Q : A -d> iProp Σ)
    γ_I γ_f γ_k γ_g γ_m γ_n (p: Node) (p1 l css: val) :
    atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗ inFP γ_f p p1 l ⊢
      (|={⊤}=> atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗
                inFP γ_f p nullval l ∗
          (∃ lsh : share, ⌜readable_share lsh⌝ ∧
                            field_at lsh t_struct_css [StructField _lock] l css)).
    Proof.
    iIntros "(AU & #HinFP)".
    iMod "AU" as (m) "[Hm HClose]".
    iDestruct "Hm" as (I r lsh lock nr) "(%Hf & Hglob & Hml & Hf & Hinv)".
    iDestruct (same_lock with "[$HinFP $Hglob]") as %(-> & ->).
    destruct Hf as (Hnull & Hr & Hpt).
    iDestruct (share_divided _ t_struct_css (DOT _lock) with "[$Hf]") as "(Hf1 & Hf2)"; eauto.
    iFrame "Hf2".
    iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css) with "[-HClose]" as "Hl".
    { rewrite /CSS /CSSi.
      iDestruct "Hf1" as (sh) "(% & Hf1)".
      iExists I, r, sh.
      iFrame.
      iPureIntro. subst; split; try done.
    }
    iSpecialize ("HClose" with "Hl").
    iFrame "HinFP ∗".
  Qed.
    
  Lemma push_lock_back {A} (b: gmap Key KValue → A → iPropI Σ) (Q : A -d> iProp Σ)
    γ_I γ_f γ_k γ_g γ_m γ_n (p: Node) (p1 l css: val) lsh
    (Hrs: readable_share lsh):
    atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗ inFP γ_f p p1 l ∗
      field_at lsh t_struct_css [StructField _lock] l css ⊢
      (|={⊤}=> atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗ inFP γ_f p p1 l ).
  Proof.
    iIntros "(AU & #HinFP & Hf)".
    iMod "AU" as (m) "(Hm & HClose)".
    iDestruct "Hm" as (I r lsh1 lock nr) "(%Hf & Hglob & Hml & Hf1 & Hinv)".
    iDestruct (same_lock with "[$HinFP $Hglob]") as %(-> & ->).
    destruct Hf as (Hnull & Hr & Hpt).
    iDestruct (share_join lsh1 lsh t_struct_css (DOT _lock) l css
                with "[$Hf $Hf1]") as (sh) "(% & Hf)"; try iSplit; try done.
    iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css) with "[-HClose]" as "Hl".
    { rewrite /CSS /CSSi.
      iExists I, r, sh.
      iFrame.
      iPureIntro. subst; split; try done.
    }
    iSpecialize ("HClose" with "Hl").
    iFrame "HinFP ∗".
  Qed.

  Lemma ghost_update_interface1 γ_I γ_f r I Ip I0 I_new p new_node new lock
    (Hpt: is_pointer_or_null new /\ is_pointer_or_null lock /\ is_pointer_or_null new_node):
   ⌜new_node ∉ dom I /\ globalinv _ _ _ r I /\ contextualLeq _ Ip (I0 ⋅ I_new) /\
     inf (I0 ⋅ I_new) new_node = 0%CCM /\ dom Ip = {[p]} /\ dom I0 = {[p]} /\
     dom I_new = {[new_node]}⌝ ∧ own γ_I (● I) ∗ own γ_I (◯ (Ip)) ∗ own_nodes1 γ_f I lock
                                 ==∗ ∀ Iz, ⌜I ≡ Ip ⋅ Iz⌝ → let I' := I0 ⋅ I_new ⋅ Iz in
         ⌜contextualLeq _ I I' /\ globalinv _ _ _ r I' /\ dom I' = dom I ∪ {[new_node]} ∧
           dom I' ∖ {[new_node]} = dom I /\
           p ∈ dom I⌝ ∧
               own γ_I (● I') ∗ own γ_I (◯ I0) ∗ own γ_I (◯ I_new) ∗ own_nodes1 γ_f I' lock ∗
                 inFP γ_f new_node nullval lock.
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
                  (● (to_agree <$> <[ new_node := (nullval, lock)]> N1) ⋅
                  ◯ (to_agree <$> <[ new_node := (nullval, lock)]> ∅))
           with "[$Hown]") as "(Hown & Hown')".
    { apply auth_update_alloc.
      rewrite ! fmap_insert.
      apply alloc_local_update; try done.
      rewrite lookup_fmap fmap_None not_elem_of_dom_1; auto.
      rewrite -Hdom in H_neq_new; auto. }
    iModIntro.
    iIntros (Iz1) "%HIz".
    assert (Iz = Iz1) as H_eq_Iz_Iz1.
    { rewrite Ipn_incl_I in HIz.
     apply intComp_cancelable in HIz; try done.
     by rewrite - Ipn_incl_I.
    }
    subst.
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
      destruct (decide (new_node = n)); subst.
      + rewrite lookup_insert in Hnew.
        inversion Hnew; subst.
        destruct Hpt as (? & ? & ?).
        repeat (split; auto).
      + rewrite lookup_insert_ne in Hnew; auto.
  Qed.

  Lemma globalinv_new_root r (I I0 I_new : multiset_flows.multiset_flowint_ur _ _ Key) new_node: ✓ (I0 ⋅ I_new) -> new_node ∈ dom I_new -> out_map I0 = ∅ -> out_map I_new = ∅ ->
    dom (inf I_new new_node) = KS -> globalinv _ _ _ r I ->
    globalinv _ _ _ new_node (I0 ⋅ I_new).
  Proof.
    intros Hvalid Hin HI0 HI_new HKS Hglobal; split3; last split.
    - done.
    - eapply elem_of_weaken; last (by rewrite comm; apply intComp_dom_subseteq_l; rewrite comm); done.
    - rewrite /closed /outset.
      intros ?? Hout.
      assert (n ∉ dom (I0 ⋅ I_new)).
      { intros ?; rewrite intValid_in_dom_not_out // in Hout. }
      rewrite intComp_unfold_out // in Hout.
      rewrite /out HI0 HI_new nzmap_lookup_empty ccm_right_id // in Hout.
    - intros; rewrite /inset intComp_inf_2 //.
      rewrite /out HI0 ccm_pinv_unit HKS //.
  Qed.
  

  (* update interface for the case of p = nullval *)
  Lemma ghost_update_interface_nullval1 γ_I γ_f r I Ip I0 I_new new_node new lock
    (Hpt: is_pointer_or_null new /\ is_pointer_or_null lock /\ is_pointer_or_null new_node):
    ⌜new_node ∉ dom I /\ globalinv _ _ _ r I /\ I ≡ Ip /\ ✓ Ip /\ ✓ (I0 ⋅ I_new) /\
      out_map I0 = ∅ /\ out_map I_new = ∅ /\ dom Ip = {[nullval]} /\ dom I0 = {[nullval]} /\
      dom I_new = {[new_node]} /\ dom (inf I_new new_node) = KS⌝ ∧
      own γ_I (● I) ∗ own γ_I (◯ (Ip)) ∗ own_nodes1 γ_f I lock
      ==∗ let I' := I0 ⋅ I_new in ⌜globalinv _ _ _ new_node I' /\ dom I' = dom I ∪ {[new_node]} ∧
                      dom I' ∖ {[new_node]} = dom I⌝ ∧
                      own γ_I (● I') ∗ own γ_I (◯ (I0)) ∗ own γ_I (◯ (I_new)) ∗
                        own_nodes1 γ_f I' lock ∗ inFP γ_f new_node nullval lock.
  Proof.
    iIntros "(%HH & HI & HIp & Hown)".
    iPoseProof (own_valid_2 with "[$HI] [$HIp]") as "%Hv".
    apply auth_both_valid_discrete in Hv.
    destruct Hv as [[Iz Ipn_incl_I] Valid_I].
    destruct HH as (H_neq_new & Hglob & HIIp & VI & VI0I_new &
                     HoutI0 & HoutI_new & HdomIp & HdomI0 & HdomI_new & HKS).
    rewrite HIIp in Ipn_incl_I.
    set I' := (I0 ⋅ I_new).
    assert (globalinv _ _ _ new_node I') as Hglob_I.
    { eapply globalinv_new_root; eauto. rewrite HdomI_new; set_solver. }
    destruct Hglob as (_ & Hgroot & Hgout & Hgin).
    iMod (own_update_2 γ_I (● I) (◯ Ip) (● (I0 ⋅ I_new) ⋅ ◯ (I0 ⋅ I_new))
           with "[$HI] [$HIp]") as "(Ha & Hf)"; try done.
    { eapply (update_flows_nullval _ _ _ _ new_node); eauto. set_solver. } 
    assert (dom (I0 ⋅ I_new) = dom I0 ∪ {[new_node]}) as domIp_Inew.
    { rewrite intComp_dom; try done. set_solver. }
    iDestruct "Hown" as (N1) "(%Hc & Hown)".
    destruct Hc as (Hdom & Hc).
    iMod (own_update γ_f (● (to_agree <$> N1) : gmap_authR Node _)
           (● (to_agree <$> <[ new_node := (nullval, lock)]> N1) ⋅
            ◯ (to_agree <$> <[ new_node := (nullval, lock)]> ∅)) with "[$Hown]") as "(Hown & Hown')".
     { rewrite ! fmap_insert.
       apply auth_update_alloc, alloc_local_update; try done.
       rewrite -Hdom in H_neq_new; auto.
       rewrite lookup_fmap fmap_None not_elem_of_dom_1; auto.
    }
    iModIntro.
    iSplit.
    { iPureIntro. do 2 (split; auto).
      rewrite /I' domIp_Inew. rewrite HdomI0 HIIp HdomIp. clear. set_solver.
      rewrite /I' domIp_Inew. rewrite HdomI0 HIIp HdomIp.
      clear - H_neq_new HIIp HdomIp. set_solver.
    }
    rewrite auth_frag_op.
    iDestruct "Hf" as "(HI0 & HI_new)".
    iFrame "Ha ∗".
    iSplitL; last first; iPureIntro; try split; auto; try by rewrite lookup_insert.
    split; auto.
    { rewrite /I' domIp_Inew HdomI0 dom_insert_L Hdom HIIp HdomIp; clear; set_solver. }
    intros ? ? ? Hnew.
    destruct Hpt as (? & ? & ?).
    destruct (decide (new_node = n)); subst.
    + rewrite lookup_insert in Hnew.
      inversion Hnew; subst.
      do 2 (split; auto).
    + rewrite lookup_insert_ne in Hnew; auto.
  Qed.

  Lemma int_domm γ_I γ_f γ_k γ_g γ_m γ_n r C css I n In:
    ⌜dom In = {[n]}⌝ ∧ own γ_I (◯ In) ∗ CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I ⊢ ⌜n ∈ dom I⌝.
  Proof.
    iIntros "(%Dom_In & Hi & Hcss)".
    iDestruct "Hcss" as (???) "(_ & (? & HI & ?) & ? & ? & ? & ?)".
    iDestruct (own_valid_2  with "HI Hi") as %Hown%auth_both_valid_discrete.
    destruct Hown as [[Io Io1] I_incl].
    iPureIntro.
    rewrite Io1 intComp_dom; last first; try rewrite <- Io1; auto.
    set_solver.
  Qed.

  Lemma CSS_unfold1 γ_I γ_f γ_k γ_g γ_m γ_n r C I pt p css lock :
    inFP γ_f p pt lock ∗ CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I ∧ ⌜p ∈ dom I⌝ ⊢
    (globalGhost γ_I γ_f γ_k γ_m r C I lock ∗
       (∀ C', globalGhost γ_I γ_f γ_k γ_m r C' I lock -∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C' css)).
  Proof.
    iIntros "(HinFP & Hcss & %)".
    iDestruct "Hcss" as (???) "(? & Hglob & ? & ? & ? & ? & ?)".
    iDestruct (same_lock with "[$HinFP $Hglob]") as %(-> & ->).
    iFrame "Hglob".
    iIntros (C') "Hglob".
    iFrame.
  Qed.

  Lemma ghost_snapshot_fp1 γ_f I q lock:
    own_nodes1 γ_f I lock ∧ ⌜q ∈ dom I⌝ ==∗ own_nodes1 γ_f I lock ∗
      (inFP γ_f q nullval lock ∧ ⌜is_pointer_or_null q /\ is_pointer_or_null lock⌝).
  Proof.
    iIntros "(Hown_nodes & %Hq_dom)".
    iDestruct "Hown_nodes" as (N0) "(%Hc & Hown_nodes)".
    iMod (own_update γ_f (● (to_agree <$> N0): gmap_authR _ _)
            (● (to_agree <$> N0) ⋅ ◯ (to_agree <$> N0)) with "[$Hown_nodes]") as "Hown".
    { apply auth_update_dfrac_alloc. apply _. done. }
    iDestruct "Hown" as "(Haa & Haf)".
    iFrame "Haa".
    iModIntro.
    iSplit; auto.
    destruct Hc as (H1 & Hc).
    assert (q ∈ dom N0) as Hq_dom_N0.
    { by rewrite -H1 in Hq_dom. }
    rewrite elem_of_dom /is_Some in Hq_dom_N0.
    destruct Hq_dom_N0 as ((x1 & x2) & ?).
    specialize (Hc q x1 x2).
    destruct Hc as (? & ? & ? & ?); try done.
    subst.
    iFrame "Haf".
    iPureIntro.
    split; auto.
  Qed.
  
  Lemma ghost_update_step (γ_I γ_f γ_k γ_g γ_m γ_n: gname) pt p (q : Node) lock I C nr css r x
    (Hne_p_null: p <> nullval) (Hdom: dom (Ip nr) = {[p]}):
    inFP γ_f p pt lock ∗ CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I ∗ md_entry_rep γ_I γ_k γ_m γ_n p nr css r ∧
    ⌜in_inset _ _ Key x (Ip nr) p ∧ in_outset _ _ Key x (Ip nr) q⌝
    ==∗ ∃ l, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css ∗ md_entry_rep γ_I γ_k γ_m γ_n p nr css r ∗
        (inFP γ_f q nullval l ∧
          ⌜is_pointer_or_null q /\ is_pointer_or_null l⌝).
  Proof.
    iIntros "(#HinFP & Hcssi & (Hnp & (%Hin & %Hout)))".
    iDestruct "Hnp" as "(%Hc & Hn & HfI & Hfk & Hfm & Hemp)".
    rewrite -> if_false; auto.
    iDestruct (int_domm with "[$HfI $Hcssi]") as %HdomI; auto.
    iDestruct (CSS_unfold1 with "[$Hcssi]") as "(Hglob & Hcss)"; auto.
    iDestruct "Hglob" as "(%Hglob & HaI & Hak & Ham & Hown_nodes)".
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
    iMod (ghost_snapshot_fp1 with "[$Hown_nodes]") as "(Hown_nodes & HinFP')"; auto.
    iDestruct "HinFP'" as "(HinFP' & %Hc1)".
    iModIntro.
    iExists lock.
    iAssert (md_entry_rep γ_I γ_k γ_m γ_n p nr css r)
      with "[$Hn $HfI $Hfk $Hfm]" as "Hmd".
    { rewrite -> if_false; auto. }
    iFrame "HinFP' Hmd".
    iSplit; auto.
    { iApply "Hcss". iFrame. iPureIntro. split; auto. }
    Qed.
  
  Lemma node_exist_inFP1 γ_f n m l lock (I: @multiset_flowint_ur Key _ _):
    inFP γ_f n m l ∗ own_nodes1 γ_f I lock  ⊢ ⌜n ∈ dom I⌝.
  Proof.
    iIntros "(#Hfp & Hown)".
    iDestruct "Hfp" as (N1) "[Hown1 %HSome]".
    iDestruct "Hown" as (N0) "(%Hdom & Hown)".
    iDestruct (own_valid_2 γ_f (● (to_agree <$> N0): gmap_authR _ _) (◯ (to_agree <$> N1))
                with "[$] [$]") as "%Hown".
    rewrite auth_both_valid_discrete in Hown.
    destruct Hown as (Hown & _).
    rewrite lookup_included in Hown.
    specialize (Hown n).
    rewrite ! lookup_fmap HSome // in Hown.
    iPureIntro.
    destruct Hdom as (Hdom & Hznth).
    assert (is_Some (N0 !! n)) as HSome'.
    { apply Some_included_is_Some in Hown.
      destruct (N0 !! n) eqn: E; auto.
      simpl in Hown. by inversion Hown. }
    by rewrite - Hdom elem_of_dom.
  Qed.


  Lemma in_tree_inv' γ_I γ_f γ_k γ_g γ_m γ_n I C p p1 l nr css r:
    inFP γ_f p p1 l ∗ nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr css r ∗
      CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I ⊢
      (nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr css r ∗
         (inv_for_lock l (nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr css r) ∗
            (inv_for_lock l (nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr css r)
             -∗ CSS γ_I γ_f γ_k γ_g γ_m γ_n C css))).
  Proof.
    iIntros "(HinFP & HNF & HCSSi)".
    iDestruct "HCSSi" as (?? nr1) "(% & Hglob & (Hml & (Hf & Hinv & Hml1 & Hn)))".
    iDestruct (same_lock with "[$HinFP $Hglob]") as %(->&->).
    iDestruct (inv_lock _ nr1 nr with "[$HNF $Hinv]") as "(HNF & Hinv)".
    iFrame "HNF Hinv".
    iIntros "Hinv".
    by iFrame.
  Qed.

 Lemma shoot_update γ_n n:
   own (inG0 := one_shot_inG) γ_n (Cinl (1 / 2)%Qp) ∗
     own (inG0 := one_shot_inG) γ_n (Cinl (1 / 2)%Qp)  ⊢ |==>
     own (inG0 := one_shot_inG) γ_n (Cinr $ (to_agree n)).
 Proof.
   rewrite -own_op -Cinl_op frac_op Qp.div_2 own_update; auto.
   by apply cmra_update_exclusive.
 Qed.
  
 Lemma release_lock {A} (b: gmap Key KValue → A → iPropI Σ) (Q : A -d> iProp Σ)
   γ_I γ_f γ_k γ_g γ_m γ_n (p p1 l css : val) nr r:
   inFP γ_f p p1 l ∗ atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗
     nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr css r ⊢
     (atomic_shift (λ _ : (), nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr css r ∗
                  inv_for_lock l (nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr css r))
        (⊤ ∖ ∅) ∅ (λ _ _ : (), inv_for_lock l (nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr css r) ∗ emp)
       (λ _ : (), atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q)).
  Proof.
    iIntros "(#HinFP & AU & Hmd)".
    unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
    iMod "AU" as (m) "(Hm & HClose)".
    iIntros "!>".
    iExists tt.
    iDestruct "Hm" as (I r') "HCSSi".
    iDestruct "HCSSi" as (???) "(% & Hglob & (Hml & (Hf & HNF & Hml1 & Hn)))".
    iDestruct (same_lock with "[$HinFP $Hglob]") as %(->&->).
    iDestruct "Hglob" as "(Hg & (HI & (Hk & Hown_m & Hown_nodes)))".
    iDestruct (nodeFull_extract with "Hmd") as "(% & Hmd & Hmd1)".
    rewrite {1} /md_entry_rep.
    rewrite -> (if_true _ (eq_dec nullval nullval)); auto.
    iDestruct "Hmd" as "(%Hc & Hnode & HfI & Hfk & Hfm & %His & Hfn & Hf_css)".
    destruct (eq_dec r nullval); destruct (eq_dec r' nullval); subst.
    2 : { rewrite -> if_true; auto.
          iDestruct (shot_not_pending with "[$Hn $Hfn]") as %[].
    }
    2 : { rewrite -> if_false; auto.
          iDestruct (shot_not_pending with "[$Hn $Hfn]") as %[].
    } 
    - iAssert (md_entry_rep γ_I γ_k γ_m γ_n nullval nr css nullval)
      with "[$Hnode $HfI $Hfk $Hfn $Hfm $Hf_css]" as "Hmd"; auto.
      iSpecialize ("Hmd1" with "Hmd").
      iDestruct (in_tree_inv' _ _ _ _ _ _ I m p nullval l nr css nullval
                with "[$Hg $HI $Hk $Hown_m
          $Hown_nodes $Hml $Hf $HNF $Hn $Hmd1 $Hml1]") as "(Hmd & Hinv & Hinv1)"; auto.
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
    - rewrite -> if_false; auto.
      iDestruct (shot_agree with "[$Hn $Hfn]") as %->.
      iAssert (md_entry_rep γ_I γ_k γ_m γ_n nullval nr css r)
        with "[$Hnode $HfI $Hfk Hfn $Hfm $Hf_css]" as "Hmd"; auto.
      { rewrite -> if_false; auto. }
      iSpecialize ("Hmd1" with "Hmd").
      iDestruct (in_tree_inv' _ _ _ _ _ _ I m p nullval l nr css r
                  with "[$Hg $HI $Hk $Hown_m
          $Hown_nodes $Hml $Hf $HNF Hn $Hmd1 $Hml1]") as "(Hmd & Hinv & Hinv1)"; auto.
      { iFrame "HinFP". rewrite -> if_false; auto. }
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
   Qed.
  
  Lemma get_inFP_not_null {A} (b: gmap Key KValue → A → mpred)
    (Q : discrete_fun (λ _ : A, mpred))
    γ_I γ_f γ_k γ_g γ_m γ_n pt p lock nr r c x q (Hne_p_null: p <> nullval)
    (Hin_inset: in_inset Node_EqDecision Node_countable Key x (Ip nr) p)
    (Hin_outset: in_outset Node_EqDecision Node_countable Key x (Ip nr) q)
    (Hdom: dom (Ip nr) = {[p]}):
    inFP γ_f p pt lock ∗
      atomic_shift (λ C : gmap Key KValue, CSS γ_I γ_f γ_k γ_g γ_m γ_n C c) ⊤ ∅ b Q ∗
      md_entry_rep γ_I γ_k γ_m γ_n p nr c r
    ⊢ |={⊤}=> ∃ l : val, inFP γ_f p pt lock ∗
      atomic_shift (λ C : gmap Key KValue, CSS γ_I γ_f γ_k γ_g γ_m γ_n C c) ⊤ ∅ b Q ∗
      md_entry_rep γ_I γ_k γ_m γ_n p nr c r ∗ inFP γ_f q nullval l ∧
      ⌜is_pointer_or_null q /\ is_pointer_or_null l⌝.
  Proof.
    iIntros "(#HinFP & AU & Hmd)".
    iMod "AU" as (m) "(Hm & HClose)".
    rewrite {1} /CSS.
    iDestruct "Hm" as (I r1) "HCSSi".
    iDestruct "HCSSi" as (???) "(%Hc & HCSSi)".
    iAssert (md_entry_rep γ_I γ_k γ_m γ_n p nr c r1) with "[Hmd]" as "Hmd".
    { rewrite /md_entry_rep !if_false; auto. }
    iAssert (CSSi γ_I γ_f γ_k γ_g γ_m γ_n r1 m c I)
      with "[$HCSSi]" as "HCSSi"; auto.
    destruct Hc as (? & ?).
    iMod (ghost_update_step with "[$HinFP $HCSSi $Hmd]") as "Hrest"; auto.
    iDestruct "Hrest" as (l) "(HCSS & Hmd & HinFP1 & %Hc)".
    iAssert (md_entry_rep γ_I γ_k γ_m γ_n p nr c r) with "[Hmd]" as "Hmd".
    { rewrite /md_entry_rep !if_false; auto. }
    iExists l.
    iFrame "∗ %".
    iMod ("HClose" with "HCSS") as "HAU".
    by iFrame "HinFP ∗".
  Qed.
  
  Lemma get_inFP_null {A} (b: gmap Key KValue → A → mpred) (Q : discrete_fun (λ _ : A, mpred))
    γ_I γ_f γ_k γ_g γ_m γ_n c:
    atomic_shift (λ C : gmap Key KValue, CSS γ_I γ_f γ_k γ_g γ_m γ_n C c) ⊤ ∅ b Q
    ⊢ |={⊤}=> atomic_shift (λ C : gmap Key KValue, CSS γ_I γ_f γ_k γ_g γ_m γ_n C c) ⊤ ∅ b Q ∗
    ∃ l : val, inFP γ_f nullval nullval l ∧
                    ⌜is_pointer_or_null l⌝.
  Proof.
    iIntros "AU".
    iMod "AU" as (m) "(Hm & HClose)".
    rewrite {1} /CSS /CSSi.
    iDestruct "Hm" as (I r1 lsh lock nr) "(%Hc & Hglob & Hml & Hidx & HNF & Hown)".
    iDestruct "Hglob" as "(%Hglob & HauthI & Hauthk & Hauthm & Hown_nodes)".
    destruct Hc as (Hnull & ?).
    iMod (ghost_snapshot_fp1 γ_f I nullval lock with "[$Hown_nodes]")
      as "(Hown_nodes & HinFP)"; auto.
    iDestruct "HinFP" as "(HinFP & %Hc1)".
    destruct Hc1 as (? & ?).
    iAssert (∃ l : val, inFP γ_f nullval nullval l ∧ ⌜is_pointer_or_null l⌝)
      with "[$HinFP]" as "Hc".
    { iPureIntro. do 2 (split; auto). }
    iFrame.
    iDestruct "HClose" as "(HClose & _)".
    iApply "HClose".
    iFrame.
    iPureIntro.
    repeat (split; auto).
  Qed.

  
  (* root is in footprint *)
  Lemma ghost_update_root γ_I γ_f γ_k γ_g γ_m γ_n r I C css:
    CSSi γ_I γ_f γ_k γ_g γ_m γ_n r C css I
    ==∗ ∃ lkr, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css ∗ inFP γ_f r nullval lkr ∧
                    ⌜is_pointer_or_null r /\
                    is_pointer_or_null lkr(* /\ (0 <= f r < size)%Z*) ⌝.
  Proof.
    iIntros "Hcss".
    iDestruct "Hcss" as (lsh lock nr) "(%Hc & Hglob & Hml & Hidx & HNF & Hn)".
    iDestruct "Hglob" as "(%Hglob & HaI & Hak & Ham & Hown_nodes)".
    destruct Hglob as (Hglob & Hr).
    destruct Hc as (Hnull & ?).
    specialize ((globalinv_root_fp I r) Hglob); intros.
    iMod (ghost_snapshot_fp1 _ _ r with "[$Hown_nodes]") as "(Hown & HinFP)"; auto.
    iDestruct "HinFP" as "(HinFP & %Hc1)".
    destruct Hc1 as (? & ?).
    iModIntro.
    iFrame.
    iPureIntro.
    repeat (split; auto).
  Qed.
  
  Lemma unify_root γ_I γ_f γ_k γ_g γ_m γ_n r1 r pnN nr I C c (Heq_null: pnN = nullval):
    CSSi γ_I γ_f γ_k γ_g γ_m γ_n r1 C c I ∗
      md_entry_rep γ_I γ_k γ_m γ_n pnN nr c r ⊢ ⌜r = r1⌝.
  Proof.
    iIntros "(HCSSi & Hmd)".
    iDestruct "HCSSi" as (lsh lock nr') "(%Hc & ? & ? & ? & ? & ? & Hown)".
    rewrite /md_entry_rep.
    rewrite -> (if_true _ (eq_dec pnN nullval)); auto.
    iDestruct "Hmd" as "(? & ? & ? & ? & ? & ? & Hown1 & ?)".
    destruct (eq_dec r1 nullval); destruct (eq_dec r nullval); subst; auto.
    iDestruct (shot_not_pending with "[$Hown $Hown1]") as %[].
    iDestruct (shot_not_pending with "[$Hown $Hown1]") as %[].
    iDestruct (shot_agree with "[$Hown $Hown1]") as %?; try done.
  Qed.
  
  Lemma in_out_nullval_node {A} (b: gmap Key KValue → A → mpred) (Q : A -d> mpred)
   γ_I γ_f γ_k γ_g γ_m γ_n (p p1 css : val) nr r x
   (HKS: x ∈ KS) (Heq_null: p = nullval) (Heq_r_null: r = nullval) (Hdom_p: dom (Ip nr) = {[p]}):
   atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗
     md_entry_rep γ_I γ_k γ_m γ_n nullval nr css r ⊢
     (|={⊤}=> ⌜x ∉ dom (Cp nr) /\ in_inset _ _ _ x (Ip nr) nullval
             ∧ ¬ in_outsets _ _ _ x (Ip nr) ∧ ✓ Ip nr⌝ ∧
     atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗
       md_entry_rep γ_I γ_k γ_m γ_n nullval nr css r).
 Proof.
   iIntros "(AU & Hmd)".
   iMod "AU" as (m) "(Hm & HClose)".
   iDestruct "Hm" as (I r') "HCSSi".
   iDestruct "HCSSi" as "(%lsh & %lock & % & % & Hglob & ? & ? & ? & ? & Hown)".
   simpl.
   rewrite {1} /md_entry_rep.
   rewrite -> (if_true _ (eq_dec nullval nullval)); auto.
   iDestruct "Hmd" as "(%  & Hn & HfI & Hfk & Hfm & % & Hown1 & Hf)".
   destruct (eq_dec r' nullval); destruct (eq_dec r nullval); subst; auto; try contradiction.
   2 : { iDestruct (shot_not_pending with "[$Hown $Hown1]") as %[]. }
   iDestruct "Hglob" as "(%Hglob & HaI & ? & Hown_m & ?)".
   destruct Hglob as ((Hv & Hr_in_domI & Hclosed & Hkey) & Hrc).
   specialize (Hrc eq_refl).
   destruct Hrc as (HdomI & Hmap).
   iDestruct (own_valid_2 γ_m (●(Excl <$> m) : keymap_authR _ _)
                (◯ (Excl <$> Cp nr)) with "[$Hown_m] [$Hfm]") as %Hownr.
   move: Hownr => /auth_both_valid_discrete [Hsub _].
   rewrite lookup_included in Hsub.
   specialize (Hsub x).
   rewrite ! lookup_fmap Hmap lookup_empty in Hsub.
   assert (x ∉ dom (Cp nr)) as Hnin_x_Cp.
   { destruct (Cp nr !! x) eqn: E; auto.
     rewrite E in Hsub.
     rewrite option_included in Hsub.
     destruct Hsub as [Hcontra | (? & ? & ? & Hcontra & ?)]; try easy.
     apply not_elem_of_dom in E; auto.
   }
   iDestruct (flowEq with "[$HaI $HfI]") as %HflowEq.
   { iPureIntro. repeat (split; auto). subst; set_solver. }
     assert (x ∉ dom (Cp nr) /\ in_inset _ _ _ x (Ip nr) nullval /\
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
     iAssert (md_entry_rep γ_I γ_k γ_m γ_n nullval nr css nullval)
       with "[$Hn $HfI $Hfk $Hfm Hown1 Hf]" as "Hmd".
     { rewrite -> if_true; auto. iFrame "% Hown1 Hf". }
     iFrame "Hmd".
     iFrame "% ∗".
     iApply "HClose".
     iFrame.
     rewrite -> if_true; auto.
 Qed.

 Lemma inset_from_root {A} (b: gmap Key KValue → A → mpred) (Q : A -d> mpred)
    γ_I γ_f γ_k γ_g γ_m γ_n n nr1 r1 css x (Hne: n <> nullval) (xKS: x ∈ KS)
    (HdomIp: dom (Ip nr1) = {[n]}):
    atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗
      md_entry_rep γ_I γ_k γ_m γ_n n nr1 css r1 ∗
      own (inG0 := one_shot_inG) γ_n (Cinr (to_agree n))
      ⊢ |={⊤}=> atomic_shift (λ C, CSS γ_I γ_f γ_k γ_g γ_m γ_n C css) ⊤ ∅ b Q ∗
      md_entry_rep γ_I γ_k γ_m γ_n n nr1 css r1 ∗
      own (inG0 := one_shot_inG) γ_n (Cinr (to_agree n)) ∧ ⌜in_inset _ _ _ x (Ip nr1) n⌝.
  Proof.
    iIntros "(AU & Hmd & Hs)".
    iMod "AU" as (m) "(Hm & HClose)".
    iDestruct "Hm" as (I r') "Hcssi".
    iDestruct "Hcssi" as (???) "(? & (%Hg & ? & ?) & ? & ? & ? & ? & Hn)".
    simpl.
    rewrite {1} /md_entry_rep.
    rewrite -> (if_false _ (eq_dec n nullval)); auto.
    destruct (eq_dec r' nullval); subst.
    { iDestruct (shot_not_pending with "[$Hn $Hs]") as %[]. }
    iDestruct (shot_agree with "[$Hn $Hs]") as %->.
    destruct Hg as (Hglob & Hrest).
    pose proof Hglob as Hglob'.
    rewrite /globalinv in Hglob.
    destruct Hglob as (HIv & HdomI & Hclosed & Hinset).
    specialize (Hinset x xKS).
    rewrite /inset in Hinset |- *.
    iDestruct "Hmd" as "(%Hc & Hnode & HfI & Hfk & Hfm & _)".
    iDestruct (own_valid_2 γ_I (● I) (◯ (Ip nr1)) with "[$] [$]")
      as %Hown%auth_both_valid_discrete.
    destruct Hown as ((Iz & HI) & Hv).
    assert (x ∈ dom (inf (Ip nr1) n)) as Hinset1.
    { apply (inset_monotone I (Ip nr1) Iz x n); auto; clear -HdomIp. set_solver. }
    iAssert (md_entry_rep γ_I γ_k γ_m γ_n n nr1 css r1)
      with "[$Hnode $HfI $Hfk $Hfm]" as "Hmd".
    { rewrite -> if_false; auto. }
    iFrame "Hs Hmd".
    iFrame "%".
    iApply "HClose".
    iFrame.
    rewrite -> if_false; auto.
  Qed.

  Lemma join_nodeFull γ_I γ_k γ_m γ_n p nr css r Nmap (Hnull : nullval ∈ dom Nmap)
    (Hp : Nmap !! p = Some nr)
    (Hglob: globalinv _ _ _ r ([^op map] nr ∈ Nmap, Ip nr))
    (Hforall: map_Forall (λ (p : Node) (nr : NodeR), dom (Ip nr) = {[p]}) Nmap): 
    md_entry_rep γ_I γ_k γ_m γ_n p nr css r ∗
      ([∗ map] k↦y ∈ delete p Nmap, md_entry_rep γ_I γ_k γ_m γ_n k y css r)
      ⊢ ∃ nr1 : NodeR, nodeFull2 γ_I γ_k γ_m γ_n nullval nullval nr1 css r.
  Proof.
    pose proof Hnull as Hnull1.
    rewrite elem_of_dom in Hnull.
    destruct Hnull as (? & Hmap).
    iIntros "(Hmd & Hbig)".
    iExists _, Nmap.
    iSplit; auto.
    setoid_rewrite (big_opM_delete _ _ p nr) at 2; auto. iFrame.
  Qed.

  Lemma global_insert (I_new I I0: @multiset_flowint_ur Key _ _) (Nmap : gmap Node NodeR)
    p new_node r1 nr nr2 (HcxtLeq: contextualLeq multiset_flows.K_multiset (Ip nr) (I0 ⋅ I_new))
    (HForall: map_Forall (λ (p : Node) (nr : NodeR), dom (Ip nr) = {[p]}) Nmap)
    (Hglob: globalinv _ _ _ r1 ([^op map] nr ∈ Nmap, Ip nr)) (Hmap1: Nmap !! p = Some nr)
    (Hmap_null: Nmap !! nullval = Some nr2) (Hp_non_null: p ≠ nullval)
    (Hnew_non_null: new_node ≠ nullval) (Hneq_p_new: p ≠ new_node) (HdomI0: dom I0 = {[p]})
    (HdomInew: dom I_new = {[new_node]}) (HNmap_new: Nmap !! new_node = None)
    (HNmap: dom (delete p Nmap) ⊆ dom I) (Hnew_notin_domI: new_node ∉ dom I)
    (Hinf: inf (I0 ⋅ I_new) new_node = 0%CCM):
    globalinv _ _ _ r1 (I_new ⋅ (I0 ⋅ ([^op map] y ∈ delete p Nmap, Ip y))).
  Proof.
    assert (dom (Ip nr) = {[p]}) as Hp by auto.
    assert (✓ (I0 ⋅ I_new)) as HvI0Inew.
    { by destruct HcxtLeq as (? & ? & _). }
    assert (contextualLeq multiset_flows.K_multiset ([^op map] nr0 ∈ Nmap, Ip nr0)
              (I_new ⋅ (I0 ⋅ ([^op map] y ∈ delete p Nmap, Ip y)))) as ContLeq_I.
    { rewrite (big_opM_delete _ _ p) // assoc (comm _ I_new I0).
      destruct Hglob as (Hv & Hg); rewrite (big_opM_delete _ _ p) // in Hv.
      apply replacement_theorem; try done.
      {
        rewrite big_opM_dom; last by eapply cmra_valid_op_r.
        apply disjoint_intersection_L;
          intros ? Hin1 (n & ? & Hn & Hin2)%big_unionM_exists.
        rewrite intComp_dom in Hin1.
        rewrite HdomInew HdomI0 elem_of_union in Hin1.
        eapply map_Forall_delete in HForall; rewrite map_Forall_lookup in HForall;
          specialize (HForall _ _ Hn); rewrite HForall elem_of_singleton in Hin2.
        destruct Hin1 as [?%elem_of_singleton|?%elem_of_singleton]; subst.
        { rewrite lookup_delete // in Hn. }
        { rewrite lookup_delete_ne // in Hn. rewrite Hn in HNmap_new. easy. }
        { by destruct HcxtLeq as (? & ? & _). }
      }
      destruct Hg as (_ & Hg & _).
      rewrite intComp_dom //.
      rewrite HdomInew HdomI0 Hp.
      rewrite difference_union_distr_l_L difference_diag_L union_empty_l_L difference_disjoint_L.
      intros ? ->%elem_of_singleton.
      destruct (decide (out ([^op map] y ∈ delete p Nmap, Ip y) new_node = 0%CCM)); first auto.
      apply nzmap_empty_lookup in n as (? & ?).
      rewrite (big_opM_delete _ _ p) // in Hg.
        eapply (flowint_step _ _ _ _ new_node) in Hg; [| | by rewrite cmra_comm |].
      rewrite Hp elem_of_singleton // in Hg. done.
      rewrite /outset nzmap_elem_of_dom_total //.
      intros ? ?%elem_of_singleton ?%elem_of_singleton; by subst.
    }
    eapply contextualLeq_impl_globalinv. apply Hglob. auto.
    rewrite /contextualLeq in ContLeq_I.
    destruct ContLeq_I as (Hv1 & Hv2 & HdomS & ? & ?).
    destruct Hglob as (Hv & Hg & Hout & ?).
    pose proof Hv as Hv'.
    rewrite (big_opM_delete _ _ p) // in Hv'.
    intros n Hn.
    assert (n = new_node) as ->.
    { setoid_rewrite (big_opM_delete _ _ p) at 2 in Hn; last first; try done.
      rewrite (intComp_dom (Ip nr)) in Hn; auto.
      rewrite (intComp_dom I_new) in Hn; auto.
      rewrite (intComp_dom I0) in Hn; auto.
      rewrite HdomInew HdomI0 Hp in Hn.
      clear -Hn. set_solver.
      eapply intComp_valid_proj2; eauto.
    }
    set I1 := (I_new ⋅ (I0 ⋅ ([^op map] y ∈ delete p Nmap, Ip y))).
    set Iz1 := ([^op map] y ∈ delete p Nmap, Ip y).
    assert (✓ (I0 ⋅ ([^op map] y ∈ delete p Nmap, Ip y))) as Hv3.
    { eapply intComp_valid_proj2; eauto. }
    assert (new_node ∈ dom I_new) as Hnew_dom.
    { clear -HdomInew. set_solver. }
    assert (new_node ∉ {[p]} ∪ dom ([^op map] y ∈ delete p Nmap, Ip y)) as Hdiff.
    { apply intComp_dom_disjoint in Hv2; rewrite intComp_dom in Hv2; auto.
      rewrite HdomI0 HdomInew in Hv2. clear -Hv2. set_solver.
    }
    assert (out Iz1 new_node = 0%CCM) as out_Iz_zero.
    { apply (intComp_out_zero (Ip nr) Iz1 new_node); auto.
      rewrite (intComp_dom (Ip nr)); auto.
      rewrite Hp /Iz1; auto.
      apply nzmap_eq; intros km.
      pose proof (Hout km new_node) as km_out.
      rewrite /outset nzmap_elem_of_dom_total in km_out.
      apply dec_stable in km_out.
      rewrite big_opM_delete // in km_out.
    }
    rewrite /inset /inf.
    destruct ((inf_map I1 !! new_node)) eqn: E; last first; try by rewrite E.
    rewrite E /default /id.
    assert (inf I1 new_node = inf (I0 ⋅ I_new) new_node)%CCM as Hinf'.
    { rewrite /I1 /Iz1 /=.
      rewrite intComp_inf_1; auto. rewrite intComp_inf_2; auto.
      rewrite intComp_unfold_out; auto.
      rewrite out_Iz_zero; auto.
      by rewrite ccm_right_id.
      rewrite intComp_dom; auto.
      rewrite HdomI0; auto.
    }
    rewrite Hinf /inf E /= in Hinf'; subst. done.
  Qed.
 
End coarse_grained_lock.
Global Hint Resolve nodeFull_exclusive : core.
