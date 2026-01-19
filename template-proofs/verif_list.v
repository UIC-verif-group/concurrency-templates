Set Warnings "-abstract-large-number, -redundant-canonical-projection".
Require Import VST.concurrency.conclib.
From iris.algebra Require Import excl auth gmap agree gset.
Require Import flows.inset_flows.
Require Import flows.multiset_flows.
Require Import flows.flows.
Require Import iris_ora.algebra.gmap.
Require Import iris_ora.logic.own.
Require Import iris_ora.algebra.ext_order.
Require Import iris_ora.algebra.frac_auth.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.atomics.verif_lock_atomic.
Require Import tmpl.list. (*linked list*)
Require Import tmpl.keyset_ra_ora.
Require Import tmpl.data_struct.
Require Import tmpl.flows_ora.
Require Import tmpl.nzmap_more.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Section list_instance.
  Context `{N: NodeRep} `{EqDecision K} `{Countable K}
    `{!cinvG Σ, atom_impl : !atomic_int_impl (Tstruct threads._atom_int noattr),
        !flowintG Σ, !nodesetG Σ, !keysetG Σ, !keymapG Σ, inG Σ (frac_authR (agreeR Node))}.
  Existing Instance nzmap_filter.

#[local] Obligation Tactic := idtac.

Definition flow_int I:=
  @flows.int (@multiset_flows.K_multiset Key Z.eq_dec Z_countable) K_multiset_ccm _ _ I.

#[local] Program Instance specific_node_rep : NodeRep := {
  node := fun (n : Node) (In : @multiset_flowint_ur Key _ _) (C : gmap Key KValue) =>
  if eq_dec n nullval
  then ⌜((∃ ks, dom ks = KS /\ In = flow_int {| infR := {[n := ks]}; outR := ∅ |}) \/
                 (In = flow_int {| infR := {[n := ∅]}; outR := ∅ |})) /\ C = ∅ ⌝ ∧ emp
  else
    ∃ (x : Z) (v : val) (next : Node),
      ⌜(Int.min_signed < x < Int.max_signed)%Z /\ is_pointer_or_null next /\
        (repable_signed x) /\ (tc_val (tptr Tvoid) v) ∧
        C = {[x := v]} ∧
        dom (out_map In) = (if eq_dec next nullval then ∅ else {[next]}) ∧
        dom In = {[n]} /\ x ∈ inset _ _ _ In n /\
        let S := filter (fun (y : Z) => (x < y)%Z) (inset _ _ _ In n) in
        (S = outset _ _ _ In next \/ next = nullval)⌝ ∧
        (if eq_dec next nullval then True else malloc_token Ews2 t_struct_node next) ∗
       data_at Ews t_struct_node (Vint (Int.repr x), (v, next)) n (* ∗
       malloc_token Ews1 t_struct_node n *) }.
Next Obligation.
  intros n In Cn; simpl.
  if_tac; subst; auto.
  Intros x v next. entailer !.
Qed.
Next Obligation.
  intros n In Cn; simpl.
  if_tac; subst; auto.
  Intros x v next. entailer !.
Qed.
Next Obligation.
  intros.
  Intros.
  rewrite -> ! if_false; auto.
  Intros x v next x' v' next'.
  iIntros "((_ & H1) & (_ & H2))".
  iPoseProof (data_at_conflict Ews t_struct_node with "[$H1 $H2]") as "?"; auto; simpl; lia.
Qed.
Next Obligation.
  intros n In Cn.
  Intros.
  subst.
  rewrite -> if_true; auto. entailer !.
Qed.
Next Obligation.
  intros.
  iIntros "%H1".
  rewrite -> if_true; auto.
  iPureIntro.
  do 2 (split; auto).
  left.
  exists ks. done.
Qed.

Lemma malloc_valid_pointer_p sh p:
  malloc_token sh t_struct_node p  ⊢ valid_pointer p.
Proof.
  iIntros "Hml".
  iApply (malloc_token_valid_pointer with "[$Hml]").
Qed.
Local Hint Resolve malloc_valid_pointer_p: valid_pointer.

Lemma get_key: semax_body Vprog Gprog f_get_key get_key_spec.
Proof.
  start_function.
  rewrite /node /specific_node_rep.
  rewrite -> if_false; auto.
  Intros x v next.
  forward.
  forward.
  Exists x.
  rewrite /node /specific_node_rep.
  rewrite -> (if_false _ (eq_dec p nullval)); auto.
  entailer !.
  set_solver.
  Exists x v next.
  entailer !.
Qed.

Lemma get_value: semax_body Vprog Gprog f_get_value get_value_spec.
Proof.
  start_function.
  rewrite /node /specific_node_rep.
  rewrite -> if_false; auto.
  Intros x1 v next.
  forward.
  forward.
  Exists v.
  rewrite /node /specific_node_rep.
  rewrite -> (if_false _ (eq_dec p nullval)); auto.
  assert (x = x1) as Hx.
  { clear -H2. set_solver. }
  entailer !.
  - rewrite lookup_singleton; auto.
  - Exists x1 v next.
    entailer !.
Qed.

Lemma dom_Ip : forall (Ip : flowintT (flowdom := @multiset_flows.K_multiset Key Z.eq_dec Z_countable)) next m x
  (H : dom (out_map Ip) = (if eq_dec next nullval then ∅ else {[next]}))
  (Hx : x ∈ dom (out_map Ip !!! m)),
  m = next ∧ m ≠ nullval.
Proof.
  intros.
  assert (out_map Ip !!! m ≠ 0%CCM) as Hnz.
  { intros Hz; rewrite Hz // in Hx. }
  rewrite -nzmap_elem_of_dom_total H1 in Hnz.
  if_tac in Hnz; subst; set_solver.
Qed.

Lemma findNext: semax_body Vprog Gprog f_findNext findnext_spec.
Proof.
  start_function.
  Intros.
  rewrite /node /specific_node_rep if_false; eauto.
  Intros x0 v0 next.
  forward.
  (* (_x > _y)  *)
  forward_if.
  rewrite /in_inset in H3.
  destruct (decide (filter (λ y : Z, (x0 < y)%Z) (inset _ _ _ Ip p) = ∅)) as [Hyx|Hyx_notemp].
  { apply (filter_empty_not_elem_of_L (C := gset Key) (λ y : Z, (x0 < y)%Z) (inset _ _ _ Ip p) x)
      in Hyx; auto. rewrite /inset //= in Hyx. }
  - do 2 forward.
    simpl.
    forward.
    destruct H12 as [Hfl|Hnext_null].
    destruct (decide (next = nullval)).
    + forward_if; last done. (* next = nullval *)
      forward.
      Exists NF nullval.
      rewrite -> (if_true (nullval = nullval)) by done; entailer !.
      split.
      rewrite dom_singleton_L. apply not_elem_of_singleton_2. lia.
      intros ?.
      rewrite /in_outsets /in_outset /out in H8.
      destruct H8 as (m & H8).
      destruct (dom_Ip _ nullval _ _ H9 H8) as (? & ?); done.
      rewrite /node /specific_node_rep; eauto.
      rewrite -> if_false; auto.
      Exists x0 v0 nullval.
      entailer !.
      rewrite -> if_true; auto.
    + rewrite if_false //. forward_if.
      forward.
      forward.
      Exists CNT next.
      entailer !.
      split.
      rewrite dom_singleton_L. apply not_elem_of_singleton_2. lia.
      * assert (x ∈ filter (λ y : Z, (x0 < y)%Z) (inset _ _ _ Ip p)) as Hx_in_fl.
        { apply elem_of_filter; split; try lia; auto. }
        rewrite Hfl in Hx_in_fl.
        rewrite /outset /out in Hx_in_fl; auto.
      * rewrite /node /specific_node_rep; eauto.
        rewrite (if_false _ (eq_dec p nullval)) //=.
        Exists x0 v0 next.
        rewrite ! (if_false _ (eq_dec next nullval)) //= in H9 |- *.
        entailer !.
    + rewrite -> if_true; auto.
      forward_if.
      forward.
      Exists NF nullval.
      entailer !.
      split.
      rewrite dom_singleton_L. apply not_elem_of_singleton_2. lia.
      intros ?.
      rewrite /in_outsets /in_outset /out in H8.
      destruct H8 as (m & H8).
      destruct (dom_Ip _ nullval _ _ H9 H8) as (? & ?); done.
      rewrite /node /specific_node_rep; eauto.
      rewrite -> if_false; auto.
      Exists x0 v0 nullval.
      entailer !.
      rewrite -> if_true; auto.
      forward.
  - (* if (_x > _y) *)
    forward_if.
    forward.
    destruct H12 as [Hfl|Hnext_null].
    + Exists NF n_pt.
      entailer !.
      rewrite /in_outsets in H10.
      assert (x ∉ outset _ _ _ Ip next) as Hnext.
      { intros Hcontra.
        rewrite - Hfl in Hcontra.
        apply elem_of_filter in Hcontra.
        destruct Hcontra; try lia.
      }
      rewrite /outset /out in Hnext.
      split.
      rewrite dom_singleton_L. apply not_elem_of_singleton_2. lia.
      intros ?.
      rewrite /in_outsets /in_outset /out in H8.
      destruct H8 as (m & Hcontra).
      destruct (dom_Ip _ _ _ _ H9 Hcontra) as (? & ?); subst; done.
      rewrite /node /specific_node_rep.
      rewrite (if_false _ (eq_dec p nullval)) //=.
      Exists x0 v0 next.
      entailer !.
    + Exists NF n_pt.
      entailer !.
      split.
      rewrite dom_singleton_L. apply not_elem_of_singleton_2. lia.
      intros ?.
      rewrite /in_outsets /in_outset /out in H8.
      destruct H8 as (m & Hcontra).
      destruct (dom_Ip _ nullval _ _ H9 Hcontra) as (? & ?); subst; done.
      rewrite /node /specific_node_rep.
      rewrite (if_false _ (eq_dec p nullval)) //=.
      Exists x0 v0 nullval.
      entailer !.
      rewrite -> if_true; auto.
    + (*_x = _y *)
      assert (x = x0) as Heq. lia.
      assert (dom Cp = {[x]}) as HdomCp.
      { rewrite H8 -Heq. clear. set_solver. }
      forward.
      Exists F p.
      entailer !.
      * rewrite /in_outsets /in_outset /out in H8.
        destruct H8 as (m & Hcontra).
        destruct (dom_Ip _ _ _ _ H9 Hcontra) as (? & ?); subst.
        destruct H12 as [Hfl | Hnext_null]; last done.
        assert (x0 ∉ outset _ _ _ Ip next) as Hnext.
        { intros Hx0.
          rewrite -Hfl in Hx0.
          apply elem_of_filter in Hx0; try lia.
        }
        clear - Hcontra Hnext; set_solver.
      * rewrite /node /specific_node_rep.
        rewrite (if_false _ (eq_dec p nullval)) //=.
        Exists x0 v0 next.
        entailer !.
Qed.

Lemma contextualLeq_insert_list_node_null (Ip : flowint_T) (new_node : val) ks:
  let I_new := flow_int {| infR := {[new_node := ks]}; outR := ∅ |} in
  let I0 := flow_int {| infR := {[nullval := ∅]}; outR := ∅ |} in
  dom Ip = {[nullval]} -> ✓ Ip -> ks <> 0%CCM -> inf Ip nullval = ks -> out_map Ip = ∅ -> 
  dom ks = KS -> new_node <> nullval ->
  ✓ (I0 ⋅ I_new) /\ out_map Ip = ∅ /\ out_map I0 = ∅ /\ out_map I_new = ∅ /\
    dom Ip = {[nullval]} /\ dom I0 = {[nullval]} /\ dom I_new = {[new_node]} /\
    dom (inf I_new new_node) = KS /\
    keyset _ _ _ I0 nullval ∪ keyset _ _ _ I_new new_node = keyset _ _ _ Ip nullval /\
    keyset _ _ _ I0 nullval ## keyset _ _ _ I_new new_node.
Proof.
  intros ? ? HdomIp VIp HoutIp Hks HIpks HKS Hneq_new_null.
  assert (✓ I_new) as VInew; auto.
  { rewrite intValid_unfold.
    do 2 (split; auto).
    rewrite /I_new /=. set_solver. }
  assert (✓ I0) as VI0.
  { rewrite intValid_unfold.
    do 2 (split; auto).
    rewrite /I0 /=. set_solver. }
  assert (✓ (I0 ⋅ I_new)) as VI0_new.
  { pose proof VIp as VIp'.
    apply intValid_unfold in VIp.
    destruct VIp as (? & ? & ?).
    apply intValid_composable.
    repeat  (split; auto).
    - rewrite /I0 /I_new /flowint_dom. set_solver.
    - intros i x Hix.
      by rewrite /out /I_new /inf nzmap_lookup_empty ccm_pinv_unit ccm_comm ccm_right_id Hix.
    - intros i x Hix.
      rewrite /I_new /= in Hix.
      by rewrite /out /I_new /I0 /inf nzmap_lookup_empty ccm_pinv_unit ccm_left_id Hix /=.
  }
  assert (out_map I0 = ∅ ∧ out_map I_new = ∅ ∧ dom Ip = {[nullval]} ∧
            dom I0 = {[nullval]} ∧ dom I_new = {[new_node]})
    as (HoutI0 & HoutInew & HdomIp' & HdomI0 & HdomInew).
  { rewrite /I0 /I_new /flowint_dom /=.
    repeat split; auto. clear. set_solver. clear. set_solver. }
  assert (keyset _ _ _ I0 nullval ∪ keyset _ _ _ I_new new_node =
            keyset _ _ _ Ip nullval) as kyS.
  { rewrite /inf in Hks.
    rewrite /keyset /outsets /outset /out /I0 /I_new /inf !
      lookup_insert big_opS_empty HIpks Hks big_opS_empty /=.
    clear -HoutIp. set_solver. }
  assert (keyset _ _ _ I0 nullval ## keyset _ _ _ I_new new_node).
  { rewrite /keyset /outsets /outset /I0 /inf /out /= ! lookup_insert big_opS_empty. set_solver. }
  repeat split; auto.
  by rewrite /I_new /inf /= lookup_insert /=.
Qed.

Lemma contextualLeq_insert_list_node (Ip : flowint_T) (p new_node : val) ks next:
  let I_new := flow_int {| infR := {[new_node := ks]}; outR := out_map Ip |} in
  let I0 := flow_int {| infR := inf_map Ip; outR := <<[ new_node := ks ]>> ∅ |} in
  dom Ip = {[p]} -> new_node <> p -> ✓ Ip -> ks <> 0%CCM ->
  dom Ip ## dom (out_map Ip) -> dom ks ⊆ dom (inf Ip p) ->
  dom (out_map Ip) = (if eq_dec next nullval then ∅ else {[next]}) ->
  new_node <> next ->
  (next <> nullval -> dom (inf Ip p) ∖ dom ks ∪ dom ks ∖ dom (out Ip next)
                      ≡ dom (inf Ip p) ∖ (dom (out Ip next))) -> 
  contextualLeq _ Ip (I0 ⋅ I_new) /\
    inf (I0 ⋅ I_new) new_node = 0%CCM /\
    keyset _ _ _ I0 p ∪ keyset _ _ _ I_new new_node = keyset _ _ _ Ip p /\
    keyset _ _ _ I0 p ## keyset _ _ _ I_new new_node.
Proof.
  intros ? ? HdomIp Hdom_ne_p VIp Hks Hdom_in_out Hsubset Hdom_next Hnew_next_neq Hcond.
  assert (dom I_new = {[new_node]}) as Hnew_in_Inew by set_solver.
  assert (✓ I_new) as VInew; auto.
  { rewrite intValid_unfold.
    do 2 (split; auto); rewrite /I_new /=.
    - rewrite Hdom_next.
      destruct (decide (next = nullval)); subst.
      rewrite -> if_true; auto. set_solver.
      rewrite -> if_false; auto. set_solver.
    - intros. easy. }
  assert (✓ I0) as VI0.
  { pose proof VIp as VIp'.
    apply intValid_unfold in VIp.
    destruct VIp as (? & ? & ?).
    apply intValid_unfold.
    do 2 (split; try done).
    - rewrite /I0 nzmap_dom_insert_nonzero //=. set_solver.
    - intros HinfI0.
      exfalso.
      rewrite /I0 /= in HinfI0.
      rewrite /I0 /=.
      rewrite /dom /flowint_dom HinfI0 in HdomIp. set_solver. }
  assert (✓ (I0 ⋅ I_new)) as VI0_new.
  { pose proof VIp as VIp'.
    apply intValid_unfold in VIp.
    destruct VIp as (? & ? & ?).
    apply intValid_composable.
    repeat (split; try done).
    - rewrite /I0 /I_new /flowint_dom /=. set_solver.
    - intros i x Hix.
      rewrite /out /I_new /inf /=.
      rewrite /I0 /= in Hix.
      assert (out_map Ip !!! i = 0%CCM) as ->.
      { pose proof Hix as Hix'.
        apply flowint_contains in Hix'; auto.
        assert (i = p) as ->. set_solver.
        { rewrite <- nzmap_elem_of_dom_total2. set_solver. }
      }
      by rewrite ccm_pinv_unit ccm_comm ccm_right_id /= Hix.
    - intros i x Hix.
      assert (i = new_node) as ->.
      { rewrite /I_new /= in Hix.
        apply elem_of_dom_2 in Hix.
        clear -Hix. set_solver. }
      rewrite /out /I_new /inf nzmap_lookup_total_insert lookup_insert ccm_pinv_inv ccm_right_id.
      rewrite /I_new /= lookup_insert in Hix. naive_solver.
  }
  assert (keyset _ _ _ I0 p ∪ keyset _ _ _ I_new new_node = keyset _ _ _ Ip p) as kyS.
  { assert (dom <<[ new_node := ks ]>> (out_map Ip) = {[new_node]} ∪ dom (out_map Ip)) as Hun.
    { rewrite -leibniz_equiv_iff nzmap_dom_insert_nonzero; auto. }
    rewrite /keyset /outsets /outset /out /=.
    apply leibniz_equiv.
    replace (dom _) with ({[new_node]} : gset Node).
    2: { apply leibniz_equiv; rewrite nzmap_dom_insert_nonzero; set_solver. }
    rewrite big_opS_singleton nzmap_lookup_total_insert.
    if_tac in Hdom_next; subst.
    - rewrite Hdom_next ! big_opS_empty /I_new /inf lookup_insert /= !difference_empty_L difference_union.
      clear - Hsubset; set_solver.
    - rewrite Hdom_next !big_opS_singleton /I_new /inf lookup_insert /=; auto. }
  assert (keyset _ _ _ I0 p ## keyset _ _ _ I_new new_node).
  { rewrite /keyset /outsets /outset /I0 /inf /out.
    if_tac in Hdom_next; subst.
    - rewrite Hdom_next lookup_insert.
      assert (dom <<[ new_node := ks ]>> ∅ = {[new_node]}) as Hdom_new.
      { rewrite -leibniz_equiv_iff nzmap_dom_insert_nonzero; auto. set_solver. }
      rewrite Hdom_new (big_opS_delete _ _ new_node).
      rewrite nzmap_lookup_total_insert difference_diag_L ! big_opS_empty /= right_id difference_empty.
      clear -Hsubset. set_solver.
      clear. set_solver.
    - rewrite Hdom_next /I_new /inf lookup_insert.
      assert (dom <<[ new_node := ks ]>> ∅ = {[new_node]}) as Hdom_new.
      { rewrite -leibniz_equiv_iff nzmap_dom_insert_nonzero; auto. set_solver. }
      rewrite Hdom_new (big_opS_delete _ _ new_node).
      rewrite nzmap_lookup_total_insert difference_diag_L big_opS_empty (big_opS_delete _ _ next).
      rewrite difference_diag_L big_opS_empty /= !right_id.
      clear; set_solver. clear; set_solver. clear; set_solver.
  }
  repeat (split; auto).
  - rewrite intComp_dom; auto.
    rewrite /I0 /I_new /flowint_dom /=. set_solver.
  - intros n Hn.
    rewrite intComp_inf_1 /= /I0 /I_new /inf /out /=; auto.
    assert (out_map Ip !!! n = 0%CCM) as ->.
    { rewrite <- nzmap_elem_of_dom_total2. set_solver. }
    by rewrite ccm_pinv_unit.
  - intros n Hn.
    pose proof Hn as Hn'.
    rewrite intComp_dom /I0 /I_new /flowint_dom //= in Hn.
    rewrite intComp_unfold_out /I0 /I_new /= /out /=; auto.
    rewrite nzmap_lookup_total_insert_ne //=; auto.
    2: { set_solver. }
    by rewrite nzmap_lookup_empty ccm_comm ccm_right_id.
  - rewrite intComp_inf_2; auto.
    2: { rewrite /I_new. clear.  set_solver. }
    by rewrite /I_new /inf /= lookup_insert /out nzmap_lookup_total_insert ccm_pinv_inv.
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

Definition Gprog : funspecs := ltac:(with_library prog [surely_malloc_spec; insertOp_spec]).

Lemma insertOp: semax_body Vprog Gprog f_insertOp insertOp_spec.
Proof.
  start_function.
  rewrite /node /specific_node_rep.
  destruct (eq_dec p nullval) as [Hp | Hp].
  - forward_if.
    forward_call (t_struct_node, gv).
    vm_compute; try easy.
    Intros new_node.
    repeat forward.
    assert_PROP (new_node <> nullval) as Hnew_null_neq. entailer !.
    Exists new_node.
    destruct H8 as [HIp | HIp].
    * destruct HIp as (ks & Hdom & HIp).
      Exists (flow_int {| infR := {[ new_node := ks]}; outR := ∅ |}). (* I_new *)
      Exists (flow_int {| infR := {[ nullval := ∅ ]}; outR := ∅ |}). (* I0 *)
      Exists ({[x := v]} : gmap _ _).
      Exists (∅ : (@gmap Key _ _ KValue)).
      rewrite -> ! if_false; auto.
      rewrite {2} /node /specific_node_rep.
      rewrite -> if_true; auto.
      rewrite {1} /node /specific_node_rep.
      rewrite -> if_false; auto.
      Exists x v nullval.
      entailer !.
      assert (x ∈ dom ks) as Hxdom. { clear -Hdom H6. set_solver. }
      do 2 (split; auto).
      repeat split.
      all : try (clear; set_solver).
      + split. set_solver.
        rewrite /inset /inf lookup_insert /=; auto.
      + rewrite /key_property_null.
        intros. rewrite /in_inset /inf /= lookup_insert /=. set_solver.
      + split.
        { rewrite /keyset /outsets /outset big_opS_empty /inf lookup_insert /=. set_solver. }
        split.
        { rewrite /keyset /outsets /outset big_opS_empty /inf lookup_insert /=. clear. set_solver. }
        set Ip := flow_int {| infR := {[nullval := ks]}; outR := ∅ |} .
        set I_new := flow_int {| infR := {[new_node := ks]}; outR := ∅ |}.
        set I0 := flow_int {| infR := {[nullval := ∅]}; outR := ∅ |}.
        rewrite /SC_null.
        eapply (contextualLeq_insert_list_node_null Ip new_node ks); try done.
        rewrite /Ip /flowint_dom /=. clear. set_solver. set_solver.
        by rewrite /Ip /inf /= lookup_insert /=.
      + rewrite -> if_true; auto.
        iIntros "H".
        iDestruct (malloc_token_share_join Ews1 Ews2 with "[$H]") as "(H & H1)"; eauto.
        iFrame "H".
    * rewrite /in_inset HIp /inf /= lookup_insert /= in H3. done.
    * contradiction.
  - Intros x0 v0 next.
    forward_if (PROP ( )
      LOCAL (gvars gv; temp _p p; temp _x (vint x); temp _value v)
      SEP (mem_mgr gv; if eq_dec next nullval then True else malloc_token Ews2 t_struct_node next;
           data_at Ews t_struct_node (vint x0, (v0, next)) p)); try done.
    forward.
    entailer !.
    iIntros "?". iFrame.
    forward.
    forward_if.
    do 2 forward.
    Exists nullval Ip Ip.
    Exists (∅ : (@gmap Key _ _ KValue)) (∅ : (@gmap Key _ _ KValue)).
    rewrite -> ! (if_true _ (eq_dec nullval nullval)); auto.
    rewrite /node /specific_node_rep.
    rewrite -> (if_false _ (eq_dec p nullval)); auto.
    Exists x v next.
    entailer !. clear. set_solver.
    iIntros "?". iFrame.
    forward_call (t_struct_node, gv).
    vm_compute; try easy.
    Intros new_node.
    repeat forward.
    assert_PROP(new_node <> nullval) as Hnew_null_neq. entailer !.
    assert_PROP(new_node <> p) as Hnew_p_neq. entailer !.
    forward_if (PROP ()
     LOCAL (temp _t'3 (vint x0); temp _new_node__1 new_node; temp _t'6 (vint x0); 
     gvars gv; temp _p p; temp _x (vint x); temp _value v)
     SEP (mem_mgr gv; malloc_token Ews t_struct_node new_node;
          if (x <? x0)%Z
          then (data_at Ews t_struct_node (vint x0, (v0, next)) new_node ∗
                data_at Ews t_struct_node (vint x, (v, new_node)) p ∗
                (if eq_dec next nullval then True else malloc_token Ews2 t_struct_node next))
          else (data_at Ews t_struct_node (vint x, (v, next)) new_node ∗
                 data_at Ews t_struct_node (vint x0, (v0, new_node)) p) ∗
                 (if eq_dec next nullval then True else malloc_token Ews2 t_struct_node next))).
    + repeat forward.
      assert ((x <? x0)%Z = true) as ->. lia. entailer !.
    + repeat forward.
      assert ((x <? x0)%Z = false) as ->. lia. entailer !.
    + forward.
      destruct ((x <? x0)%Z) eqn: Eq.
      * assert ((x < x0)%Z) as Hlt_xx0 by lia. clear Eq.
        (* side condition *)
        assert (filter (λ '(k, _), (x < k)%Z) (inf Ip p) <> 0%CCM) as Hfl'.
        { intros Hcontra.
          apply nzmap_empty_dom in Hcontra.
          assert (x0 ∈ filter (λ y, (x < y)%Z) (dom (inf Ip p))) as Hx by (apply elem_of_filter; auto).
          rewrite nzmap_filter_dom_L in Hx.
          clear - Hx Hcontra; set_solver. }
        rewrite /node /specific_node_rep.
        set I0 := (flow_int {|
                    infR := inf_map Ip;
                    outR := <<[ new_node := filter (fun '(k, _) => (x < k)%Z)(inf Ip p) ]>> ∅ |}).
        set I_new := (flow_int {|
                    infR := {[ new_node := filter (fun '(k, _) => (x < k)%Z)(inf Ip p) ]};
                    outR := out_map Ip |}).
        Exists new_node.
        Exists I_new I0.
        Exists ({[x0 := v0]} : gmap _ _).
        Exists ({[x := v]} : gmap _ _).
        rewrite -> ! (if_false _ (eq_dec new_node nullval)); auto.
        rewrite -> (if_false _ (eq_dec p nullval)); auto.
        Exists x v new_node.
        Exists x0 v0 next.
        assert_PROP (new_node <> next) as H_new_next_neq.
        { destruct (eq_dec next new_node); subst; auto.
          iIntros "(_ & H1 & _ & _ & H2)".
          rewrite -> if_false; auto.
          iDestruct (malloc_token_share_join with "[$H1]") as "(_ & H1)"; eauto.
          by iDestruct (malloc_token_conflict with "[$H1 $H2]") as "?"; eauto; cbv. }
        entailer !.

        (** Side conditions **)
        (* prove ks *)
        set ks := filter (λ '(k, _), (x < k)%Z) (inf Ip p).
        assert (key_property2 p new_node Ip I_new {[x := v]} {[x0 := v0]} x) as Hkey_prop.
        { exists x0, x.
          split. clear. set_solver.
          split. clear. set_solver.
          split. lia. intros ?? (Hdom & HGe).
          rewrite /in_inset /inf /= lookup_insert /default /id.
          assert (k ∈ filter (λ y, (x < y)%Z) (dom (inf Ip p))) as Hk' by (apply elem_of_filter; split; auto; lia).
          rewrite nzmap_filter_dom_L // in Hk'. }
        assert ({[x]} ⊆ keyset Node_EqDecision Node_countable Key I0 p) as Hx_keyset.
        { rewrite /keyset /inf /outsets /outset /out /=.
          assert (dom <<[ new_node := ks ]>> ∅ = {[new_node]}) as Hn.
          { rewrite -leibniz_equiv_iff nzmap_dom_insert_nonzero; auto. set_solver. }
          rewrite Hn big_opS_singleton nzmap_lookup_total_insert.
          apply singleton_subseteq_l, elem_of_difference.
          assert (x ∉ filter (λ y : Z, (x < y)%Z) (dom (inf Ip p))) as Hx_in_dom.
          { intros (? & ?)%elem_of_filter; lia. }
          rewrite nzmap_filter_dom_L in Hx_in_dom.
          clear - H3 Hx_in_dom. set_solver. }
        assert (x0 ∈ filter (λ k : Z, (x < k)%Z) (dom (inf Ip p))) as Hx_in_dom.
        { apply elem_of_filter; split; try lia; auto. }
        rewrite nzmap_filter_dom_L in Hx_in_dom.
        assert ({[x0]} ⊆ keyset Node_EqDecision Node_countable Key I_new new_node) as Hx0_I_new.
        { rewrite /keyset /inf /outsets /outset /out /= lookup_insert H11.
          apply singleton_subseteq_l, elem_of_difference; split.
          * clear - H13 Hx_in_dom; set_solver.
          * if_tac; first by rewrite big_opS_empty.
            rewrite big_opS_singleton.
            destruct H14 as [Hfl_in | Hnull]; last done.
            rewrite /outset in Hfl_in; rewrite -Hfl_in.
            intros (? & ?)%elem_of_filter; lia. }
        assert (cxtLeq Ip I_new I0 p new_node) as HcxtLeq.
        { rewrite /cxtLeq.
          eapply (contextualLeq_insert_list_node Ip p new_node ks next); eauto.
          + by apply intValid_unfold.
          + apply nzmap_dom_filter_subseteq.
          + intros Hnext.
            destruct H14 as [Hfl_in | Hnull]; last first; try done.
            rewrite /outset /inset in Hfl_in.
            apply (cxt_helper_list Ip p next x x0); auto. }
        assert (dom I0 = {[p]}) as HdomI0.
        { by rewrite /I_new /dom /flowint_dom /=. }
        (** End - Side conditions **)

        rewrite if_false; last first. (* contradiction *)
        rewrite ! dom_singleton_L. intros Hcontra.
        assert (x = x0) as Hxx0. clear - Hcontra. set_solver. lia.
        ** do 2 split; auto.
           split. clear -H15. set_solver.
           rewrite /I_new /dom /flowint_dom /=. clear. set_solver.
           repeat split; auto.
           rewrite /I_new /dom /flowint_dom /=. clear. set_solver.
           { rewrite /inset /inf lookup_insert; auto. }
           { destruct H14 as [Hfl_in | Hnull]; last first; try by right.
             rewrite /inset /inf /outset /out /= lookup_insert.
             if_tac in H11; first auto.
             rewrite /outset /inset /out /inf in Hfl_in.
             left; rewrite - Hfl_in ! nzmap_filter_dom_L.
             f_equal.
             rewrite nzmap_filter_filter.
             apply nzmap_filter_strong_ext.
             intros ??; f_equiv; auto; simpl; lia. }
           repeat (split; auto).
           { rewrite dom_singleton_L; auto. }
           split; auto.
           repeat split; auto.
           { rewrite if_false; auto.
             rewrite -leibniz_equiv_iff nzmap_dom_insert_nonzero; try set_solver. }
           { rewrite /inset /inf /outset /out nzmap_lookup_total_insert nzmap_filter_dom_L.
             by left. }
        ** rewrite <- (malloc_token_share_join Ews1 Ews2 Ews t_struct_node new_node); auto.
           cancel.
           rewrite -> (if_false _ (eq_dec new_node nullval)); auto.
           iIntros "(? & ? & ?)".
           iFrame.
      (* end lemma *)
      * (*_x > _y *)
        assert ((x > x0)%Z) as Hlt_x0x by lia. clear Eq.
        (* side condition *)
        rewrite /node /specific_node_rep.
        set I0 := flow_int {|
                   infR := inf_map Ip;
                   outR := <<[ new_node := filter (fun '(k, _) => (x0 < k)%Z)(inf Ip p) ]>> ∅ |}.
        set I_new := flow_int {|
                   infR := {[ new_node := filter (fun '(k, _) => (x0 < k)%Z)(inf Ip p) ]};
                   outR := out_map Ip |}.
        Exists new_node.
        Exists I_new I0.
        Exists ({[x := v]} : gmap _ _).
        Exists ({[x0 := v0]} : gmap _ _).
        rewrite -> ! (if_false _ (eq_dec new_node nullval)); auto.
        rewrite -> (if_false _ (eq_dec p nullval)); auto.
        Exists x0 v0 new_node.
        Exists x v next.
        assert_PROP (new_node <> next) as H_new_next_neq.
        { destruct (eq_dec next new_node); subst; auto.
          iIntros "(? & H1 & ? & H2)".
          rewrite -> if_false; auto.
          iDestruct (malloc_token_share_join with "[$H1]") as "(_ & H1)"; eauto.
          iDestruct (malloc_token_conflict with "[$H1 $H2]") as "?"; eauto.
          simpl. lia. }
        entailer !.

        (** Side conditions **)
        (* prove ks *)
        set ks := filter (λ '(k, _), (x0 < k)%Z) (inf Ip p).
        assert (key_property1 p new_node Ip I_new {[x0 := v0]} x) as Hkey_prop.
        { exists x0.
          split. clear. set_solver.
          split; first lia; intros ?? (Hk & HGe).
          rewrite /in_inset /inf /= lookup_insert /default /id.
          assert (k ∈ filter (λ y, (x0 < y)%Z) (dom (inf Ip p))) as Hk' by (apply elem_of_filter; split; auto; lia).
          rewrite nzmap_filter_dom_L // in Hk'. }
        assert (x ∈ dom ks) as Hx_in_ks.
        { assert (x ∈ filter (λ y, (x0 < y)%Z) (dom (inf Ip p))) as Hx by (apply elem_of_filter; split; auto; lia).
          rewrite nzmap_filter_dom_L in Hx.
          clear - Hx; set_solver. }
        assert (ks ≠ ∅) by (intros ->; done).
        assert (next = nullval) as Hnext.
        { if_tac in H11; first done.
          destruct H14; last done.
          contradiction H4.
          rewrite outset_in_outsets1 /outsets H11 big_opS_singleton -H14 //.
          apply elem_of_filter; split; auto; lia. }
        assert ({[x]} ⊆ keyset Node_EqDecision Node_countable Key I_new new_node) as Hx_keyset.
        { rewrite /keyset /inf lookup_insert.
          assert (~ in_outsets _ _ _ x I_new) as Hnot_x_I_new.
          { rewrite /in_outsets /in_outset /out /=. done. }
          rewrite /outsets.
          rewrite outset_in_outsets1 in Hnot_x_I_new.
          clear - Hx_in_ks Hnot_x_I_new; set_solver. }
        assert ({[x0]} ⊆ keyset Node_EqDecision Node_countable Key I0 p) as Hx0_I0.
        { rewrite /keyset /inf /outsets /outset /out /=.
          assert (dom <<[ new_node := ks ]>> ∅ = {[new_node]}) as Hdom_new.
          { rewrite -leibniz_equiv_iff nzmap_dom_insert_nonzero; auto. set_solver. }
          rewrite ! Hdom_new big_opS_singleton nzmap_lookup_total_insert.
          assert (x0 ∉ filter (λ y : Z, (x0 < y)%Z) (dom (inf Ip p))) as Hout.
          { intros (? & ?)%elem_of_filter; lia. }
          rewrite nzmap_filter_dom_L in Hout.
          clear - H13 Hout. set_solver. }
        assert (cxtLeq Ip I_new I0 p new_node) as HcxtLeq.
        { rewrite /cxtLeq.
          eapply (contextualLeq_insert_list_node Ip p new_node ks next); auto.
          + by apply intValid_unfold.
          + apply nzmap_dom_filter_subseteq.
          + done. }
        assert (dom I_new = {[new_node]}) as HdomI_new.
        { rewrite /I_new /dom /flowint_dom /=. clear. set_solver. }
        assert (dom I0 = {[p]}) as HdomI0.
        { by rewrite /I_new /dom /flowint_dom /=. }
        (** END - Side conditions **)
        rewrite if_true; try done. (* contradiction *)
        ** do 2 split; auto.
           split; auto.
           clear -H15. set_solver.
           do 2 (split; auto).
           { rewrite /inset /inf lookup_insert //. }
           do 2 (split; auto).
           { rewrite dom_singleton_L; auto. }
           split; auto.
           repeat split; auto.
           { rewrite if_false; auto.
             rewrite -leibniz_equiv_iff nzmap_dom_insert_nonzero; try set_solver. }
           { rewrite /inset /inf /outset /out nzmap_lookup_total_insert nzmap_filter_dom_L.
             by left. }
        ** rewrite <- (malloc_token_share_join Ews1 Ews2 Ews t_struct_node new_node); auto.
           cancel.
           rewrite -> (if_false _ (eq_dec new_node nullval)); auto.
           iIntros "(? & ? & ?)". iFrame.
Qed.

End list_instance.
