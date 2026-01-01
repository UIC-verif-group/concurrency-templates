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
Require Import tmpl.bst. (*binary search tree*)
Require Import tmpl.keyset_ra_ora.
Require Import tmpl.data_struct.
Require Import tmpl.flows_ora.
Require Import tmpl.nzmap_more.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Section bst_instance.
  Context `{N: NodeRep } `{EqDecision K} `{Countable K}.
  Context `{!cinvG Σ, atom_impl : !atomic_int_impl (Tstruct threads._atom_int noattr),
            !flowintG Σ, !nodesetG Σ, !keysetG Σ, !keymapG Σ, inG Σ (frac_authR (agreeR Node))}.

  Existing Instance nzmap_filter.
  
 #[local] Obligation Tactic := idtac.

Definition flow_int I:=
  @flows.int (@multiset_flows.K_multiset Key Z.eq_dec Z_countable) K_multiset_ccm _ _ I.

#[local] Program Instance specific_node_rep : NodeRep := {
  node := fun (n : Node) (In : @multiset_flowint_ur _ _ _) (C: gmap Key KValue) =>
  if eq_dec n nullval
  then ⌜((∃ ks, dom ks = KS /\ In = flow_int {| infR := {[n := ks]}; outR := ∅ |}) \/
           (In = flow_int {| infR := {[n := ∅]}; outR := ∅ |})) /\ C = ∅ ⌝ ∧ emp
  else
  ∃ (x : Z) (v : val) (m1 m2: Node),
  ⌜(Int.min_signed < x < Int.max_signed)%Z /\ is_pointer_or_null m1 /\
    is_pointer_or_null m2 /\ (repable_signed x) /\ (tc_val (tptr Tvoid) v) /\
    C = {[x := v]} ∧
    (dom (out_map In) = (if eq_dec m1 nullval then ∅ else {[m1]}) ∪
                        (if eq_dec m2 nullval then ∅ else {[m2]})) ∧ dom In = {[ n ]} /\
    x ∈ inset _ _ _ In n /\
    (let S1 := filter (fun (y : Z) => (y < x)%Z) (inset _ _ Key In n) in
     let S2 := filter (fun (y : Z) => (y > x)%Z) (inset _ _ Key In n) in
     (S1 = outset _ _ Key In m1 \/ m1 = nullval) ∧
     (S2 = outset _ _ Key In m2 \/ m2 = nullval))⌝ ∧
    (if eq_dec m1 nullval then True else malloc_token Ews2 t_struct_node m1) ∗
      (if eq_dec m2 nullval then True else malloc_token Ews2 t_struct_node m2) ∗
     data_at Ews t_struct_node (Vint (Int.repr x), (v, (m1, m2))) n
    (* ∗ malloc_token Ews1 t_struct_node n *)}.
Next Obligation.
  intros n In Cn; simpl.
  if_tac; subst; auto.
  Intros x v m1 m2. entailer !.
Qed.
Next Obligation.
  intros n In Cn; simpl.
  if_tac; subst; auto.
  Intros x v m1 m2. entailer !.
Qed.
Next Obligation.
  intros.
  Intros.
  rewrite -> ! if_false; auto.
  Intros x v m1 m2 x' v' m1' m2'.
  iIntros "((_ & _ & H1) & (_ & _ & H2))".
  iPoseProof (data_at_conflict Ews t_struct_node with "[$H1 $H2]") as "?"; auto; simpl; lia.
Qed.
Next Obligation.
  intros n In Cn.
  Intros.
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
  Intros x v m1 m2.
  forward.
  forward.
  Exists x.
  rewrite /node /specific_node_rep.
  rewrite -> (if_false _ (eq_dec p nullval)); auto.
  entailer !.
  set_solver.
  Exists x v m1 m2.
  entailer !.
Qed.

Lemma get_value: semax_body Vprog Gprog f_get_value get_value_spec.
Proof.
  start_function.
  rewrite /node /specific_node_rep.
  rewrite -> if_false; auto.
  Intros x1 v m1 m2.
  forward.
  forward.
  Exists v.
  rewrite /node /specific_node_rep.
  rewrite -> (if_false _ (eq_dec p nullval)); auto.
  assert (x = x1) as Hx.
  { clear -H2. set_solver. }
  entailer !.
  - rewrite lookup_singleton; auto.
  - Exists x1 v m1 m2.
    entailer !.
Qed.

Lemma dom_Ip : forall (Ip : flowintT (flowdom := @multiset_flows.K_multiset Key Z.eq_dec Z_countable)) m1 m2 m x
  (H : dom (out_map Ip) = (if eq_dec m1 nullval then ∅ else {[m1]}) ∪ (if eq_dec m2 nullval then ∅ else {[m2]}))
  (Hx : x ∈ dom (out_map Ip !!! m)),
  (m = m1 ∨ m = m2) ∧ m ≠ nullval.
Proof.
  intros.
  assert (out_map Ip !!! m ≠ 0%CCM) as Hnz.
  { intros Hz; rewrite Hz // in Hx. }
  rewrite -nzmap_elem_of_dom_total H1 in Hnz.
  if_tac in Hnz; if_tac in Hnz; subst; set_solver.
Qed.

Lemma findNext: semax_body Vprog Gprog f_findNext findnext_spec.
Proof.
  start_function.
  Intros.
  rewrite /node /specific_node_rep; eauto.
  rewrite -> if_false; auto.
  Intros x0 v0 m1 m2.
  forward.
  (* if (_x < _y) *)
  forward_if.
  - forward. forward.
    rewrite /data_struct.t_struct_node /=.
    forward.
    assert (x ∈ filter (λ y : Z, (y < x0)%Z) (inset _ _ _ Ip p)) as Hx_in_fl.
    { apply elem_of_filter; split; try lia; auto. }
    destruct H12 as [Hfl|Hm1null].
    + rewrite Hfl /outset /out in Hx_in_fl.
      destruct (dom_Ip _ _ _ _ _ H9 Hx_in_fl) as (_ & ?).
      rewrite if_false //.
      forward_if.
      forward. forward.
      Exists CNT m1.
      entailer !.
      rewrite dom_singleton_L in H8.
      apply not_elem_of_singleton_2 in H8. easy. lia.
      rewrite /node /specific_node_rep.
      rewrite -> (if_false _ (eq_dec p nullval)); auto.
      Exists x0 v0 m1 m2.
      rewrite -> !(if_false _ (eq_dec m1 nullval)) in * by auto; by entailer!.
    + forward_if; last done.
      forward.
      Exists NF nullval.
      entailer !.
      split.
      { rewrite dom_singleton_L. apply not_elem_of_singleton_2. lia. }
      intros ?.
      rewrite /in_outsets /in_outset /out in H8.
      destruct H8 as (m & H8).
      destruct (dom_Ip _ nullval _ _ _ H9 H8) as ([|] & ?); try done; subst.
      assert (x ∉ filter (λ y : Z, (y > x0)%Z) (inset _ _ _ Ip p)) as Hx_notin_fl.
      { intros Hcontra%elem_of_filter. lia. }
      destruct H13 as [Hfl|Hm2null]; last done.
      rewrite Hfl /outset /out in Hx_notin_fl.
      clear -H8 Hx_notin_fl. set_solver.
      rewrite /node /specific_node_rep.
      rewrite -> (if_false _ (eq_dec p nullval)); auto.
      Exists x0 v0 nullval m2.
      entailer !.
      rewrite -> (if_true _ (eq_dec nullval nullval)); auto.
   - forward_if. (* if (_x > _y) *)
    (* since x < x0 then filter of (y < x0) inset not empty*)
    assert (x ∈ filter (λ y : Z, (y > x0)%Z) (inset _ _ _ Ip p)) as Hx_in_fl.
    { apply elem_of_filter; split; try lia; auto. }
    forward. forward.
    simpl; forward.
    destruct H13 as [Hfl|Hm2null].
    + rewrite Hfl in Hx_in_fl.
      destruct (dom_Ip _ _ _ _ _ H9 Hx_in_fl) as (_ & ?).
      rewrite -> (if_false _ (eq_dec m2 nullval)); auto.
      forward_if.
      easy.
      forward.
      Exists CNT m2.
      entailer !.
      rewrite dom_singleton_L in H8.
      apply not_elem_of_singleton_2 in H8. easy. lia.
      rewrite /node /specific_node_rep.
      rewrite -> (if_false _ (eq_dec p nullval)); auto.
      Exists x0 v0 m1 m2.
      entailer !.
      rewrite -> if_false; auto.
    + rewrite -> (if_true _ (eq_dec m2 nullval)); auto.
      forward_if; last done.
      forward.
      Exists NF nullval.
      entailer !.
      split.
      { rewrite dom_singleton_L. apply not_elem_of_singleton_2. lia. }
      intros ?.
      rewrite /in_outsets /in_outset /out in H8.
      destruct H8 as (m & H8).
      destruct (dom_Ip _ _ nullval _ _ H9 H8) as ([|] & ?); try done; subst.
      assert (x ∉ filter (λ y : Z, (y < x0)%Z) (inset _ _ _ Ip p)) as Hx_notin_fl.
      { intros Hcontra%elem_of_filter; lia. }
      destruct H12 as [Hfl|Hm1null]; last done.
      rewrite Hfl /outset /out in Hx_notin_fl.
      set_solver.
      rewrite /node /specific_node_rep.
      rewrite -> (if_false _ (eq_dec p nullval)); auto.
      Exists x0 v0 m1 nullval.
      entailer !.
      rewrite -> if_true; auto.
   + (*_x = _y *)
    assert (x = x0) as Heq. lia.
    assert (dom Cp = {[x]}) as HdomCp.
    { rewrite H8 -Heq. clear. set_solver. }
    forward.
    Exists F p.
    entailer !.
    rewrite /in_outsets /in_outset /out in H8.
    destruct H8 as (m & Hcontra).
    destruct (dom_Ip _ _ _ _ _ H9 Hcontra) as ([|] & ?); subst.
    * destruct H12 as [Hfl_m1|?]; last done.
      rewrite /outset /out in Hfl_m1.
      rewrite -Hfl_m1 in Hcontra.
      apply elem_of_filter in Hcontra as (? & ?); lia.
    * destruct H13 as [Hfl_m2|?]; last done.
      rewrite /outset /out in Hfl_m2.
      rewrite -Hfl_m2 in Hcontra.
      apply elem_of_filter in Hcontra as (? & ?); lia.
    * rewrite /node /specific_node_rep.
      rewrite -> (if_false _ (eq_dec p nullval)); auto.
      Exists x0 v0 m1 m2. 
      entailer !.
Qed.

Lemma contextualLeq_insert_BST_node_null (Ip : flowint_T) (new_node : val) ks:
  let I_new := flow_int {| infR := {[new_node := ks]}; outR := ∅ |} in
  let I0 := flow_int {| infR := {[nullval := ∅]}; outR := ∅ |} in
  dom Ip = {[nullval]} -> ✓ Ip -> ks <> 0%CCM -> inf Ip nullval = ks -> out_map Ip = ∅ -> 
  dom ks = KS -> new_node <> nullval -> out_map Ip = ∅ -> 
  ✓ (I0 ⋅ I_new) /\ out_map Ip = ∅ /\ out_map I0 = ∅ /\ out_map I_new = ∅ /\
    dom Ip = {[nullval]} /\ dom I0 = {[nullval]} /\ dom I_new = {[new_node]} /\
    dom (inf I_new new_node) = KS /\
    keyset _ _ _ I0 nullval ∪ keyset _ _ _ I_new new_node = keyset _ _ _ Ip nullval /\
    keyset _ _ _ I0 nullval ## keyset _ _ _ I_new new_node.
Proof.
  intros ? ? HdomIp VIp Hks HIpks HKS Hneq_new_null HoutIp.
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
  { rewrite /inf in HIpks.
    rewrite /keyset /outsets /outset /out /I0 /I_new /inf !
      lookup_insert big_opS_empty HKS big_opS_empty /= HIpks .
    clear -HoutIp. set_solver. }
  assert (keyset _ _ _ I0 nullval ## keyset _ _ _ I_new new_node).
  { rewrite /keyset /outsets /outset /I0 /inf /out /= ! lookup_insert big_opS_empty. set_solver. }
  repeat split; auto.
  by rewrite /I_new /inf /= lookup_insert /=.
Qed.

Lemma contextualLeq_insert_BST_node (Ip : flowint_T) (p new_node : val) ks next:
  let I_new := flow_int {| infR := {[new_node := ks]}; outR := ∅ |} in
  let I0 := flow_int {| infR := inf_map Ip; outR := <<[ new_node := ks ]>>(out_map Ip) |} in
  dom Ip = {[p]} -> new_node <> p -> ✓ Ip -> ks <> 0%CCM ->
  dom Ip ## dom (out_map Ip) -> dom ks ⊆ dom (inf Ip p) ->
  dom (out_map Ip) = (if eq_dec next nullval then ∅ else {[next]}) ->
  new_node <> next ->
  (next <> nullval -> dom (inf Ip p) ∖ dom (out Ip next) ∪ dom ks ≡ dom (inf Ip p) ∖ dom (out Ip next)) ->
  contextualLeq _ Ip (I0 ⋅ I_new) /\
  inf (I0 ⋅ I_new) new_node = 0%CCM /\
  keyset _ _ _ I0 p ∪ keyset _ _ _ I_new new_node = keyset _ _ _ Ip p /\
  keyset _ _ _ I0 p ## keyset _ _ _ I_new new_node.
Proof.
  intros ? ? HdomIp Hdom_ne_p VIp Hks Hdom_in_out Hsubset Hdom_next Hnew_next_neq Hcond.
  assert (dom I_new = {[new_node]}) as Hnew_in_Inew by set_solver.
  assert (✓ I_new) as VInew; auto.
  { rewrite intValid_unfold.
    do 2 (split; auto).
    rewrite /I_new /=. set_solver. }
  assert (✓ I0) as VI0.
  { pose proof VIp as VIp'.
    apply intValid_unfold in VIp.
    destruct VIp as (? & ? & ?).
    apply intValid_unfold.
    do 2 (split; try done).
    - rewrite /I0 nzmap_dom_insert_nonzero; auto. set_solver.
    - rewrite /I0.
      intros HinfI0.
      rewrite /I0 /= in HinfI0.
      exfalso.
      rewrite /dom / flowint_dom HinfI0 in HdomIp. set_solver. }
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
      assert (i = new_node) as ->.
      { rewrite /I_new in Hix.
        apply elem_of_dom_2 in Hix.
        clear -Hix. set_solver. }
      rewrite /out /I_new /inf nzmap_lookup_total_insert lookup_insert ccm_pinv_inv ccm_right_id.
      rewrite /I_new lookup_insert in Hix. naive_solver. }
  assert (keyset _ _ _ I0 p ∪ keyset _ _ _ I_new new_node = keyset _ _ _ Ip p) as kyS.
  { assert (dom <<[ new_node := ks ]>> (out_map Ip) = {[new_node]} ∪ dom (out_map Ip)) as Hun.
    { rewrite -leibniz_equiv_iff nzmap_dom_insert_nonzero; auto. }
    rewrite /keyset /outsets /outset /out /=.
    if_tac in Hdom_next; subst.
    - rewrite Hdom_next ! big_opS_empty /I_new /inf lookup_insert Hun -leibniz_equiv_iff.
      rewrite (big_opS_delete _ _ new_node).
      rewrite Hdom_next union_empty_r_L difference_diag_L big_opS_empty nzmap_lookup_total_insert.
      rewrite right_id !difference_empty difference_union. clear -Hsubset. set_solver. clear. set_solver.
    - rewrite Hdom_next ! big_opS_empty /I_new /inf lookup_insert - leibniz_equiv_iff Hun.
      rewrite (big_opS_delete _ _ new_node) Hdom_next.
      rewrite (big_opS_delete _ _ next).
      assert ({[new_node; next]} ∖ {[new_node]} ∖ {[next]} = (∅ : gset _)) as Hn'.
      clear -Hnew_next_neq. set_solver.
      rewrite Hn' big_opS_empty nzmap_lookup_total_insert nzmap_lookup_total_insert_ne //=.
      rewrite big_opS_singleton difference_empty_L union_empty_r.
      rewrite (union_comm (dom ks)).
      apply Hcond in H1.
      by rewrite -difference_difference_l difference_union.
      clear -Hnew_next_neq. set_solver.
      clear. set_solver.
  }
  assert (keyset _ _ _ I0 p ## keyset _ _ _ I_new new_node).
  { rewrite /keyset /outsets /outset /I0 /inf /out /=.
    if_tac in Hdom_next; subst.
    - assert (dom <<[ new_node := ks ]>> (out_map Ip) = dom (<<[ new_node := ks ]>> ∅)) as Hn.
      { rewrite -leibniz_equiv_iff ! nzmap_dom_insert_nonzero; auto.
        rewrite Hdom_next //. }
      rewrite big_opS_empty.
      rewrite (big_opS_delete _ _ new_node).
      rewrite nzmap_lookup_total_insert lookup_insert.
      assert (dom <<[ new_node := ks ]>> ∅ ∖ {[new_node]} = ∅) as Hn1. 
      { rewrite -leibniz_equiv_iff nzmap_dom_insert_nonzero; auto. clear. set_solver. }
      rewrite Hn Hn1.
      rewrite big_opS_empty. clear. set_solver.
      rewrite nzmap_dom_insert_nonzero; auto. clear. set_solver.
    - rewrite lookup_insert big_opS_empty /=.
      assert (dom <<[ new_node := ks ]>> (out_map Ip) = {[new_node]} ∪ dom (out_map Ip)) as Hn.
      { rewrite -leibniz_equiv_iff nzmap_dom_insert_nonzero; auto. }
      rewrite (big_opS_delete _ _ new_node).
      rewrite nzmap_lookup_total_insert Hn Hdom_next.
      rewrite (big_opS_delete _ _ next).
      rewrite nzmap_lookup_total_insert_ne; auto.
      clear. set_solver. clear -Hnew_next_neq. set_solver. set_solver.
  }
  repeat (split; try done).
  - rewrite intComp_dom; auto.
    rewrite /I0 /I_new /flowint_dom /=. set_solver.
  - intros n Hn.
    by rewrite intComp_inf_1 //= /I0 /inf /I_new /out nzmap_lookup_empty ccm_pinv_unit.
  - intros n Hn.
    rewrite intComp_unfold_out //= /I0 /I_new /out nzmap_lookup_empty
      ccm_right_id nzmap_lookup_total_insert_ne; auto.
    rewrite intComp_dom /I0 /I_new /flowint_dom //= in Hn.
    clear -Hn. set_solver.
  - rewrite intComp_inf_2; auto.
    2: { rewrite /I_new. set_solver. }
    by rewrite /I_new /inf /= lookup_insert /out nzmap_lookup_total_insert ccm_pinv_inv.
Qed.

Definition Gprog : funspecs := ltac:(with_library prog [surely_malloc_spec; insertOp_spec]).

(* Proving insertOp satisfies spec *)
Lemma insertOp: semax_body Vprog Gprog f_insertOp insertOp_spec.
Proof.
  start_function.
  rewrite /node /specific_node_rep.
  destruct (eq_dec p nullval) as [Hp | Hp].
  - Intros.
    forward_if.
    forward_call (t_struct_node, gv).
    simpl. vm_compute; split; try easy.
    Intros new_node.
    repeat forward.
    assert_PROP(new_node <> nullval) as Hnew_null_neq. entailer !.
    Exists new_node.
    destruct H7 as [HIp | HIp].
    * destruct HIp as (ks & Hdom & HIp).
      set I_new := flow_int {| infR := {[new_node := ks]}; outR := ∅ |}.
      set I0 := flow_int {| infR := {[ nullval := ∅ ]}; outR := ∅ |}.
      Exists I_new I0 ({[x := v]} : gmap _ _) (∅ : (@gmap Key _ _ KValue)).
      rewrite -> ! (if_false _ (eq_dec new_node nullval)); auto.
      rewrite {2} /node /specific_node_rep.
      rewrite -> if_true; auto.
      rewrite {1} /node /specific_node_rep.
      rewrite -> if_false; auto.
      Exists x v nullval nullval.
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
        { rewrite /keyset /outsets /outset big_opS_empty /inf lookup_insert /=.
          set_solver. }
        split.
        { rewrite /keyset /outsets /outset big_opS_empty /inf lookup_insert /=.
          clear. set_solver. }
        set Ip := flow_int {| infR := {[nullval := ks]}; outR := ∅ |} .
        assert (out_map Ip = ∅) as HoutIp.
        { by rewrite /Ip /out_map /=. }
        rewrite /SC_null.
        eapply (contextualLeq_insert_BST_node_null Ip new_node ks); try done.
        rewrite /Ip /flowint_dom /=. clear. set_solver. set_solver.
        by rewrite /Ip /inf /= lookup_insert /=.
      + rewrite -> if_true; auto.
        iIntros "H".
        iDestruct (malloc_token_share_join Ews1 Ews2 with "[$H]") as "(H & H1)"; eauto.
        iFrame "H". done.
    * rewrite /in_inset HIp /inf /= lookup_insert /= in H3. done.
    * contradiction.
  - Intros x0 v0 m1 m2.
    forward_if (PROP ( )
     LOCAL (gvars gv; temp _p p; temp _x (vint x); temp _value v)
     SEP (mem_mgr gv;
          if eq_dec m1 nullval then True else malloc_token Ews2 t_struct_node m1;
          if eq_dec m2 nullval then True else malloc_token Ews2 t_struct_node m2;
          data_at Ews t_struct_node (vint x0, (v0, (m1, m2))) p)).
    contradiction.
    forward.
    entailer !.
    iIntros "(? & ?)". iFrame.
    forward.
    forward_if.
    do 2 forward.
    Exists nullval Ip Ip.
    Exists (∅ : (@gmap Key _ _  KValue)) (∅ : (@gmap Key _ _ KValue)).
    entailer !.
    rewrite -> ! (if_true _ (eq_dec nullval nullval)); auto.
    rewrite /node /specific_node_rep.
    rewrite -> (if_false _ (eq_dec p nullval)); auto.
    Exists x v m1 m2.
    entailer !.
    set_solver.
    iIntros "(? & ?)". iFrame.
    forward_call (t_struct_node, gv).
    vm_compute; split; try easy.
    Intros new_node.
    repeat forward.
    assert_PROP(new_node <> nullval) as Hnew_null_neq. entailer !.
    assert_PROP(new_node <> p) as Hnew_p_neq. entailer !.
    forward_if (PROP ()
                LOCAL (temp _t'4 (vint x0); temp _new_node__1 new_node; temp _t'5 (vint x0); 
     gvars gv; temp _p p; temp _x (vint x); temp _value v)
     SEP (mem_mgr gv; malloc_token Ews t_struct_node new_node;
     data_at Ews t_struct_node (vint x, (v, (nullval, nullval))) new_node;
        if (x <? x0)%Z 
        then (data_at Ews t_struct_node (vint x0, (v0, (new_node, m2))) p ∗
                (if eq_dec m1 nullval then True else malloc_token Ews2 t_struct_node m1) ∗
                (if eq_dec m2 nullval then True else malloc_token Ews2 t_struct_node m2))
        else  (data_at Ews t_struct_node (vint x0, (v0, (m1, new_node))) p) ∗
                (if eq_dec m1 nullval then True else malloc_token Ews2 t_struct_node m1) ∗
                (if eq_dec m2 nullval then True else malloc_token Ews2 t_struct_node m2))).
    + forward.
      assert ((x <? x0)%Z = true) as ->. lia. entailer !.
    + forward.
      assert ((x <? x0)%Z = false) as ->. lia. entailer !.
    + forward.
      destruct (x <? x0)%Z eqn: Eq.
      * assert (x < x0)%Z as Hlt_xx0 by lia. clear Eq.
        (*prove side condition*)
        assert (filter (λ '(k, _), (k < x0)%Z) (inf Ip p) ≠ 0%CCM) as Hfl'.
        { intros Hcontra.
          apply nzmap_empty_dom in Hcontra.
          assert (x ∈ filter (λ y, (y < x0)%Z) (dom (inf Ip p))) as Hx by (apply elem_of_filter; auto).
          rewrite nzmap_filter_dom_L in Hx.
          clear - Hx Hcontra; set_solver. }
        (* m1 is always nullval *)
        destruct H14 as [Hfl_in | Hm1_eq_null].
        { exfalso.
          apply H4.
          assert (x ∈ filter (λ y : Z, (y < x0)%Z) (dom (inf Ip p))) as Hx_in_dom.
          { apply elem_of_filter; split; try lia; auto. }
          rewrite Hfl_in in Hx_in_dom.
          eexists; eauto. }
        rewrite /node /specific_node_rep.
        Exists new_node.
        set I_new := flow_int {|
                      infR := {[ new_node := filter (fun '(k, _) => (k < x0)%Z)(inf Ip p) ]};
                      outR := ∅ |}.
        set I0 := flow_int {|
                   infR := inf_map Ip;
                   outR := <<[ new_node := filter (fun '(k, _) => (k < x0)%Z)(inf Ip p) ]>>
                                       (out_map Ip) |}.
        Exists I_new I0.
        Exists ({[x := v]} : gmap _ _).
        Exists ({[x0 := v0]} : gmap _ _).
        rewrite -> ! (if_false _ (eq_dec new_node nullval)); auto.
        rewrite -> (if_false _ (eq_dec p nullval)); auto.
        Exists x0 v0 new_node m2.
        Exists x v nullval nullval.
        assert_PROP (new_node <> m2).
        { destruct (eq_dec m2 new_node); subst; auto.
          iIntros "(_ & H1 & _ & _ & _ & H2)".
          rewrite (if_false _ (eq_dec new_node _)) //=.
          iDestruct (malloc_token_share_join with "[$H1]") as "(_ & H1)"; auto.
          iDestruct (malloc_token_conflict with "[$H1 $H2]") as "?"; auto.
          done. }
        entailer !.
        (* decide (dom {[x0 := v0]} = dom {[x0 := v0]}) *)
        rewrite -> if_true; auto.
        
        (** Side conditions **)
        (* prove ks *)
        set ks := filter (λ '(k, _), (k < x0)%Z) (inf Ip p).
        assert (key_property1 p new_node Ip I_new {[x0 := v0]} x) as Hkey_prop.
        { exists x0.
          split. clear. set_solver.
          split; intros ?? (Hk & HGe); try lia.
          rewrite /in_inset /inf /= lookup_insert /default /id.
          assert (k ∈ filter (λ y, (y < x0)%Z) (dom (inf Ip p))) as Hk' by (apply elem_of_filter; auto).
          rewrite nzmap_filter_dom_L // in Hk'. }
        (* Generate union and disjoint *)
        pose proof (union_filter_dom x0 (inf Ip p)) as H_union.
        pose proof (disjoin_filter1 x0 (inf Ip p)) as (Hdisj1 & Hdisj2 & Hdisj3).
        assert (dom (filter (λ kv : Z * nat, (kv.1 < x0)%Z) (inf Ip p)) = dom ks)
          as Hdom_ks by auto.
        (* end *)
        assert ({[x]} ⊆ keyset Node_EqDecision Node_countable Key I_new new_node) as Hx_keyset.
        { rewrite /keyset /inf lookup_insert /outsets big_opS_empty.
          assert (x ∈ filter (λ y : Z, (y < x0)%Z) (dom (inf Ip p))) as Hx_in_dom.
          { apply elem_of_filter; split; try lia; auto. }
          rewrite nzmap_filter_dom_L in Hx_in_dom.
          clear -Hx_in_dom. set_solver. }
        assert ({[x0]} ⊆ keyset Node_EqDecision Node_countable Key I0 p) as Hx0_I0.
        { rewrite /keyset /inf /outsets /outset /out /=.
          apply singleton_subseteq_l, elem_of_difference; split; first done.
          rewrite (big_opS_delete _ _ new_node).
          rewrite ! nzmap_lookup_total_insert.
          assert (dom <<[ new_node := ks ]>> (out_map Ip) =
                       {[new_node]} ∪ dom (out_map Ip)) as Hn.
          { rewrite -leibniz_equiv_iff nzmap_dom_insert_nonzero; auto. }
          rewrite Hn.
          2 : { rewrite nzmap_dom_insert_nonzero. clear. set_solver. auto. }
          rewrite H11.
          rewrite -> if_true; auto.
          rewrite elem_of_union; intros [Hx0 | Hx0].
          { clear -Hx0. assert (x0 ∉ filter (λ y : Z, (y < x0)%Z) (dom (inf Ip p))) as Hout.
            { intros (? & ?)%elem_of_filter; lia. }
            rewrite nzmap_filter_dom_L in Hout; set_solver. }
          rewrite difference_union_distr_l_L difference_diag_L !union_empty_l_L in Hx0; if_tac in Hx0.
          { replace (∅ ∖ {[new_node]}) with (∅ : gset val) in Hx0 by (clear; set_solver).
            rewrite big_opS_empty // in Hx0. }
          rewrite difference_disjoint_L in Hx0; last by clear - H10; set_solver.
          rewrite big_opS_singleton nzmap_lookup_total_insert_ne // in Hx0.
          destruct H15 as [Hout | ?]; last done.
          rewrite /outset in Hout; rewrite -Hout in Hx0.
          apply elem_of_filter in Hx0 as (? & ?); lia. }
        (* end {[x0]} ⊆ keyset Node_EqDecision Node_countable Key I0 p *)
        assert (cxtLeq Ip I_new I0 p new_node) as HctxLeq.
        { rewrite /cxtLeq.
          eapply (contextualLeq_insert_BST_node Ip p new_node ks m2); try easy.
          * by apply intValid_unfold.
          * apply nzmap_dom_filter_subseteq.
          * rewrite -> if_true in H11; auto.
            rewrite union_empty_l_L in H11; auto.
          * intros; destruct H15 as [Hfl_out | Hnull]; last done.
            rewrite /outset /inset in Hfl_out.
            assert (dom ks ## dom (out Ip m2)) as Hdisj6.
            { rewrite ! nzmap_filter_dom_L in Hdisj1.
              by rewrite -Hfl_out nzmap_filter_dom_L. }
            clear -Hdisj6 H_union. set_solver. }
        (* end: cxtLeq *)
        assert (dom I_new = {[new_node]}) as HdomI_new.
        { rewrite /I_new /dom /flowint_dom /=. clear. set_solver. }
        assert (dom I0 = {[p]}) as HdomI0.
        { by rewrite /I_new /dom /flowint_dom /=. }
        assert (x ∈ inset _ _ _ I_new new_node) as Hx_in_I_new.
        { rewrite /keyset in Hx_keyset.
          clear -Hx_keyset; set_solver. }
       (** END - Side conditions **)
       
       ** repeat (split; auto).
          clear -H16. set_solver.
          { rewrite dom_singleton_L; auto. }
          { rewrite if_false //= - leibniz_equiv_iff nzmap_dom_insert_nonzero //= H11.
            clear. set_solver.
          }
          { (* filter \/ node_node = nullval *)
            left.
            rewrite /inset /inf /outset /out nzmap_lookup_total_insert; auto.
            rewrite ! nzmap_filter_dom_L /inf. set_solver. }
          { (* filter \/ m2 = nullval *)
            rewrite /outset in H11.
            rewrite /inset /inf /outset /out /=.
            destruct (decide (m2 = nullval)) as [|Hm2_null_neq]; auto.
            destruct H15 as [Hfl_yx |Hm2_null]; auto.
            assert (x ∉ outset _ _ _ Ip m2) as Hm2.
            { intros Hcontra.
              assert (x ∈ filter (λ y : Z, (y > x0)%Z) (inset _ _ _ Ip p)) as Hflx.
              { clear -Hfl_yx Hcontra. set_solver. }
              apply elem_of_filter in Hflx. lia. }
            rewrite -> if_true, -> if_false in H11; auto.
            rewrite /outset /out in Hm2.
            rewrite /inset /in_inset /inf in H3. 
            rewrite nzmap_lookup_total_insert_ne; auto. }
       ** (* malloc *)
          rewrite -> !(if_true _ (eq_dec nullval nullval)); auto.
          rewrite -> (if_false _ (eq_dec new_node _)); auto.
          rewrite <- (malloc_token_share_join Ews1 Ews2 _ t_struct_node new_node); auto.
          simpl; cancel.
          iIntros "(_ & ?)". iFrame.
     * (* right child*)
       assert ((x > x0)%Z) as Hlt_x0x by lia. clear Eq.
       assert (filter (λ y : Z, (y > x0)%Z) (inset _ _ _ Ip p) <> ∅) as Hfl.
       {
         destruct (decide (filter (λ y : Z, (y > x0)%Z) (inset _ _ _ Ip p) = ∅)); auto.
         { apply (filter_empty_not_elem_of_L (C := gset Key) (λ y : Z, (y > x0)%Z)
                 (inset _ _ _ Ip p) x) in e; auto.
         }
       }
       (*prove side condition*)
       assert (filter (λ '(k, _), (k > x0)%Z) (inf Ip p) ≠ 0%CCM) as Hfl'.
       { intros Hcontra.
         apply nzmap_empty_dom in Hcontra.
         assert (x ∈ filter (λ y, (y > x0)%Z) (dom (inf Ip p))) as Hx by (apply elem_of_filter; auto).
         rewrite nzmap_filter_dom_L in Hx.
         clear - Hx Hcontra; set_solver. }
       (* m2 is always nullval *)
       assert (m2 = nullval) as Hm2_eq_null.
       { destruct H15 as [Hfl_in | Hnext_null_eq]; auto.
         exfalso.
         apply H4.
         assert (x ∈ filter (λ y : Z, (y > x0)%Z) (dom (inf Ip p))) as Hx_in_dom.
         { apply elem_of_filter; split; try lia; auto. }
         rewrite Hfl_in in Hx_in_dom.
         eexists; eauto. }
       rewrite /node /specific_node_rep.
       set I_new := flow_int {|
                     infR := {[ new_node := filter (fun '(k, _) => (k > x0)%Z)(inf Ip p) ]};
                     outR := ∅ |}.
       set I0 := flow_int {|
                     infR := inf_map Ip;
                     outR := <<[ new_node := filter (fun '(k, _) => (k > x0)%Z)(inf Ip p) ]>>
                                      (out_map Ip) |}.
       Exists new_node.
       Exists I_new I0.
       Exists ({[x := v]} : gmap _ _).
       Exists ({[x0 := v0]} : gmap _ _).
       rewrite -> ! (if_false _ (eq_dec new_node nullval)); auto.
       rewrite -> (if_false _ (eq_dec p nullval)); auto.
       Exists x0 v0 m1 new_node.
       Exists x v nullval nullval.
       assert_PROP (new_node <> m1).
       { destruct (eq_dec m1 new_node); subst; auto.
         iIntros "(_ & H1 & _ & _ & H2 & _)".
         rewrite -> if_false; auto.
         iDestruct (malloc_token_share_join _ _ with "[$H1]") as "(_ & H1)"; eauto.
         iDestruct (malloc_token_conflict _ _ _ with "[$]") as "?"; eauto.
         simpl. lia.
       }
       entailer !.
       (* decide (dom {[x0 := v0]} = dom {[x0 := v0]}) *)
       rewrite -> if_true; auto.
       (** Side conditions **)
       (* prove ks *)
       set ks := filter (λ '(k, _), (k > x0)%Z) (inf Ip p).
       assert (key_property1 p new_node Ip I_new {[x0 := v0]} x) as Hkey_prop.
       { exists x0.
         split. clear. set_solver.
         split; intros ?? (Hk & HGe); try lia.
         rewrite /in_inset /inf /= lookup_insert /default /id.
         assert (k ∈ filter (λ y, (y > x0)%Z) (dom (inf Ip p))) as Hk' by (apply elem_of_filter; auto).
         rewrite nzmap_filter_dom_L // in Hk'. }
       (* Generate union and disjoint *)
       pose proof (union_filter_dom x0 (inf Ip p)) as H_union.
       pose proof (disjoin_filter1 x0 (inf Ip p)) as (Hdisj1 & Hdisj2 & Hdisj3).
       assert (dom (filter (λ kv : Z * nat, (kv.1 > x0)%Z) (inf Ip p)) = dom ks)
         as Hdom_ks by auto.
       (* end *)
       assert ({[x]} ⊆ keyset Node_EqDecision Node_countable Key I_new new_node) as Hx_keyset.
       {  rewrite /keyset /inf lookup_insert /outsets big_opS_empty.
          assert (x ∈ filter (λ y : Z, (y > x0)%Z) (dom (inf Ip p))) as Hx_in_dom.
          { apply elem_of_filter; split; try lia; auto. }
          rewrite /default /id.
          rewrite nzmap_filter_dom_L in Hx_in_dom.
          clear -Hx_in_dom. set_solver. }
       assert ({[x0]} ⊆ keyset Node_EqDecision Node_countable Key I0 p) as Hx0_I0.
       { rewrite /keyset /inf /outsets /outset /out /=.
          apply singleton_subseteq_l, elem_of_difference; split; first done.
          rewrite (big_opS_delete _ _ new_node).
          rewrite ! nzmap_lookup_total_insert.
          assert (dom <<[ new_node := ks ]>> (out_map Ip) =
                       {[new_node]} ∪ dom (out_map Ip)) as Hn.
          { rewrite -leibniz_equiv_iff nzmap_dom_insert_nonzero; auto. }
          rewrite Hn.
          2 : { rewrite nzmap_dom_insert_nonzero. clear. set_solver. auto. }
          rewrite H11.
          rewrite -> (if_true (nullval = nullval)); auto.
          rewrite elem_of_union; intros [Hx0 | Hx0].
          { clear -Hx0. assert (x0 ∉ filter (λ y : Z, (y > x0)%Z) (dom (inf Ip p))) as Hout.
            { intros (? & ?)%elem_of_filter; lia. }
            rewrite nzmap_filter_dom_L in Hout; set_solver. }
          rewrite difference_union_distr_l_L difference_diag_L !union_empty_l_L union_empty_r_L in Hx0; if_tac in Hx0.
          { replace (∅ ∖ {[new_node]}) with (∅ : gset val) in Hx0 by (clear; set_solver).
            rewrite big_opS_empty // in Hx0. }
          rewrite difference_disjoint_L in Hx0; last by clear - H10; set_solver.
          rewrite big_opS_singleton nzmap_lookup_total_insert_ne // in Hx0.
          destruct H14 as [Hout | ?]; last done.
          rewrite /outset in Hout; rewrite -Hout in Hx0.
          apply elem_of_filter in Hx0 as (? & ?); lia. }
        (* end {[x0]} ⊆ keyset Node_EqDecision Node_countable Key I0 p *)
        assert (cxtLeq Ip I_new I0 p new_node) as HctxLeq.
        { rewrite /cxtLeq.
          eapply (contextualLeq_insert_BST_node Ip p new_node ks m1); auto.
          * by apply intValid_unfold.
          * apply nzmap_dom_filter_subseteq.
          * rewrite -> (if_true (nullval = nullval)) in H11; auto.
            rewrite union_empty_r_L in H11; auto.
          * intros; destruct H14 as [Hfl_out | Hnull]; last done.
            rewrite /outset /inset in Hfl_out.
            assert (dom ks ## dom (out Ip m1)) as Hdisj6.
            { rewrite ! nzmap_filter_dom_L in Hdisj1.
              by rewrite -Hfl_out nzmap_filter_dom_L. }
            clear -Hdisj6 H_union. set_solver. }
        assert (dom I_new = {[new_node]}) as HdomI_new.
        { rewrite /I_new /dom /flowint_dom /=. clear. set_solver. }
        assert (dom I0 = {[p]}) as HdomI0.
        { by rewrite /I_new /dom /flowint_dom /=. }
        assert (x ∈ inset _ _ _ I_new new_node) as Hx_in_I_new.
        { rewrite /keyset in Hx_keyset.
          clear -Hx_keyset; set_solver. }
       (** END - Side conditions **)
       ** repeat (split; auto).
          clear -H16. set_solver.
          { rewrite dom_singleton_L; auto. }
          { rewrite -> (if_false _ (eq_dec new_node nullval)); auto.
            rewrite - leibniz_equiv_iff nzmap_dom_insert_nonzero //= H11.
            clear. set_solver. 
          }
          { rewrite /inset /inf /outset /out nzmap_lookup_total_insert_ne; auto. }
          { rewrite /outset in H13.
            rewrite /inset /inf /outset /out /=.
            left; rewrite nzmap_lookup_total_insert nzmap_filter_dom_L //. }
       ** rewrite -> !(if_true _ (eq_dec nullval nullval)); auto.
          rewrite -> (if_false _ (eq_dec new_node _)); auto.
          rewrite <- (malloc_token_share_join Ews1 Ews2 Ews t_struct_node new_node); auto.
          simpl; cancel.
          iIntros "(? & _)".
          iFrame.
Qed.

End bst_instance.
