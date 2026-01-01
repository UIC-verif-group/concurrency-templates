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
Require Import tmpl.flows_ora.
Require Import tmpl.keyset_ra_ora.
Require Export tmpl.common.
Import Clightdefs.ClightNotations.
Local Open Scope clight_scope.

Definition _findNext : ident := ($ "findNext").
Definition _node : ident := ($ "node").
Definition _get_key : ident := ($ "get_key").
Definition _get_value : ident := ($ "get_value").
Definition _insertOp : ident := ($ "insertOp").

Definition Key := Z.
Definition KValue := val.
Definition flowint_T := @flowintT (@multiset_flows.K_multiset Key Z.eq_dec Z_countable) _ _ _.

Definition cxtLeq (Ip I_new I0: flowint_T) p new_node : Prop :=
  contextualLeq _ Ip (I0 ⋅ I_new) ∧ inf (I0 ⋅ I_new) new_node = 0%CCM ∧
    keyset _ _ _ I0 p ∪ keyset _ _ _ I_new new_node = keyset _ _ _ Ip p ∧
    keyset _ _ _ I0 p ## keyset _ _ _ I_new new_node.

Definition SC_null (Ip I0 I_new : flowint_T) new_node : Prop := 
  ✓ (I0 ⋅ I_new) /\ out_map Ip = ∅ /\ out_map I0 = ∅ /\ out_map I_new = ∅ /\
    dom Ip = {[nullval]} /\ dom I0 = {[nullval]} /\ dom I_new = {[new_node]} /\
    dom (inf I_new new_node) = KS /\
    keyset _ _ _ I0 nullval ∪ keyset _ _ _ I_new new_node = keyset _ _ _ Ip nullval /\
    keyset _ _ _ I0 nullval ## keyset _ _ _ I_new new_node.

Definition key_property_null new_node (Ip I_new : flowint_T) :=
  (forall k, k ∈ KS -> in_inset _ _ _ k I_new new_node).

Definition key_property1 p new_node (Ip I_new : flowint_T) (Cp : gmap Z val) x :=
  exists (key : Z),
    dom Cp = {[key]} /\
      ((x < key)%Z -> forall k, k ∈ dom (inf Ip p) /\ (k < key)%Z -> in_inset _ _ _ k I_new new_node) /\
      ((x > key)%Z -> forall k, k ∈ dom (inf Ip p) /\ (k > key)%Z -> in_inset _ _ _ k I_new new_node).

Definition key_property2 p new_node (Ip I_new : flowint_T) (Cp' Cp : gmap Z val) x :=
  exists (key key': Z),
    dom Cp' = {[key']} /\ dom Cp = {[key]} /\ (key > key')%Z /\
      ((x = key')%Z -> forall k, k ∈ dom (inf Ip p) /\ (k > key')%Z ->
                                 in_inset _ _ _ k I_new new_node).

Definition Ews1 := fst (slice.cleave Ews).
Definition Ews2 := snd (slice.cleave Ews).
Lemma readable_Ews1 : readable_share Ews1.
Proof. apply slice.cleave_readable1; auto. Qed.
Lemma readable_Ews2 : readable_share Ews2.
Proof. apply slice.cleave_readable2; auto. Qed.
Lemma Ews1_Ews2_join : sepalg.join Ews1 Ews2 Ews.
Proof. apply slice.cleave_join. Qed.
Global Hint Resolve readable_Ews1 readable_Ews2 Ews1_Ews2_join : core.

(* Axiom *)
Axiom signed_bounds_axiom_KS: forall (k : Z), (Int.min_signed < k < Int.max_signed)%Z -> k ∈ KS.

Section Flows_Cameras.
  Lemma flwint n (x y : @multiset_flowint_ur Key _ _): ✓{n} y → x ≼ₒ{n} y → x ≼{n} y.
  Proof. intros Hv Hxy; destruct y; destruct Hxy; subst; try done. Qed.
  
  Canonical Structure flow_authR := @authR _ flwint.
  
  (* RA for authoritative flow interfaces over multisets of keys *)
  Class flowintG Σ := FlowintG { flowint_inG :> inG Σ (flow_authR) }.
  Definition flowintΣ : gFunctors := #[GFunctor (flow_authR)].
  
  Instance subG_flowintΣ {Σ} : subG flowintΣ Σ → flowintG Σ.
  Proof. solve_inG. Qed.

  (* RA for authoritative sets of nodes *)
  Canonical Structure gmap_authR K A `{Countable K} :=
    inclR(iris.algebra.auth.authR(iris.algebra.gmap.gmapR K A)).

  Class nodemapG Σ :=
    NodemapG { nodemap_inG :> inG Σ (gmap_authR Node (iris.algebra.agree.agree (prodO val val))) }.
  Definition nodemapΣ : gFunctors :=
    #[GFunctor (gmap_authR Node (iris.algebra.agree.agree (prodO val val)))].

  Instance subG_nodemapΣ {Σ} : subG nodemapΣ Σ → nodemapG Σ.
  Proof. solve_inG. Qed.

  Canonical Structure gset_authR A `{Countable A} := inclR(iris.algebra.auth.authR(gsetR A)).
  
  Class nodesetG Σ := NodesetG { nodeset_inG :> inG Σ (gset_authR Node ) }.
  Definition nodesetΣ : gFunctors := #[GFunctor (gset_authR Node )].

  Instance subG_nodesetΣ {Σ} : subG nodesetΣ Σ → nodesetG Σ.
  Proof. solve_inG. Qed.

  (* keymap *)
  Canonical Structure keymap_authR K A `{Countable K} :=
    inclR(iris.algebra.auth.authR(iris.algebra.gmap.gmapR K A)).

  Class keymapG Σ :=
    KeymapG { keymap_inG :> inG Σ (keymap_authR Key (iris.algebra.excl.excl val))}.
  Definition keymapΣ : gFunctors :=
    #[GFunctor (keymap_authR Key (iris.algebra.excl.excl val))].

  Instance subG_keymapΣ {Σ} : subG (@keymapΣ) Σ → (@keymapG) Σ.
  Proof. solve_inG. Qed.

  (* keyset *)
  Lemma ks A `{Countable A} n (x y : keysetUR A): ✓{n} y → x ≼ₒ{n} y → x ≼{n} y.
  Proof. intros Hv Hxy; destruct y; destruct Hxy; subst; try done. Qed.
  Canonical Structure keyset_authR A `{Countable A} := @authR _ (ks A).

  Class keysetG Σ := KeysetG { keyset_inG :> inG Σ (keyset_authR Key) }.
  Definition keysetΣ : gFunctors := #[GFunctor (keyset_authR Key)].

  Instance subG_keysetΣ {Σ} : subG (@keysetΣ) Σ → (@keysetG) Σ.
  Proof. solve_inG. Qed.
End Flows_Cameras.

Section NodeRep.
  Context `{!VSTGS unit Σ, !flowintG Σ, !nodesetG Σ, !nodemapG Σ, !keymapG Σ }.
  
  Class NodeRep : Type := {
    DS_compspecs :: compspecs;
    node : Node → @multiset_flowint_ur Key _ _ → gmap Key KValue -> mpred;
    node_rep_R_valid_pointer: forall n I_n C, node n I_n C ⊢ valid_pointer n;
    node_rep_R_pointer_null: forall n I_n C, node n I_n C ⊢ ⌜is_pointer_or_null n⌝;
    node_sep_star: forall n I_n I_n' C C', ⌜n <> nullval⌝ ∧ node n I_n C ∗ node n I_n' C' ⊢ False;
    node_nullval_empty: forall n I_n C, ⌜n = nullval⌝ ∧ node n I_n C ⊢ ⌜C = ∅ ⌝;
    imply_node : forall ks Ir,
        <affine> ⌜dom ks = KS /\
          Ir = @flows.int (@multiset_flows.K_multiset _ _ _) K_multiset_ccm _ _
             {| infR := {[nullval := ks]}; outR := ∅ |}⌝ ⊢ node nullval Ir ∅;

    (* t_struct_node *)
    t_struct_node := Tstruct _node noattr; 

    (* findNext *)
    findnext_spec :=
        DECLARE _findNext
    WITH x : Z, p : Node, n : val, n_pt : val, Ip : flowintT,
       Cp : gmap Key KValue, sh : share, gv : globals
    PRE [ tptr t_struct_node, tptr (tptr t_struct_node), tint ]
    PROP (writable_share sh; is_pointer_or_null n_pt; (Int.min_signed < x < Int.max_signed)%Z)
    PARAMS (p; n; Vint (Int.repr x)) GLOBALS (gv)
    SEP (node p Ip Cp ∗ ⌜in_inset _ _ _ x Ip p /\ p <> nullval⌝ ∧
           data_at sh (tptr t_struct_node) n_pt n)
    POST [ tint ]
    ∃ (stt: enum), ∃ (next : Node),
    PROP (is_pointer_or_null next)
    LOCAL (temp ret_temp (enums stt))
    SEP (node p Ip Cp;
         match stt with
         | F  => ⌜(dom Cp = {[x]}) /\ ¬in_outsets _ _ Key x Ip⌝ ∧
                  data_at sh (tptr t_struct_node) n_pt n
         | NF => ⌜(x ∉ dom Cp) /\ ¬in_outsets _ _ Key x Ip⌝ ∧
                  data_at sh (tptr t_struct_node) next n            
         | CNT => ⌜(x ∉ dom Cp) /\ (next <> nullval /\ in_outset _ _ _ x Ip next)⌝ ∧
                    data_at sh (tptr t_struct_node) next n
         end);

    (* get_key_spec *)
    get_key_spec :=
        DECLARE _get_key
    WITH p : Node, Ip : flowintT, Cp : gmap Key KValue, gv : globals
    PRE [ tptr t_struct_node]
    PROP (p <> nullval)
    PARAMS (p) GLOBALS (gv)
    SEP (node p Ip Cp)
    POST [ tint ]
    ∃ (key: Z),
    PROP (dom Cp = {[key]} /\ key ∈ inset _ _ _ Ip p /\
            (Int.min_signed < key < Int.max_signed)%Z)
    RETURN (vint key)
    SEP (node p Ip Cp);

    (* get_value_spec *)
    get_value_spec :=
        DECLARE _get_value
    WITH x:Z, p : Node, Ip : flowintT, Cp : gmap Key KValue, gv : globals
    PRE [ tptr t_struct_node]
    PROP (p <> nullval; dom Cp = {[x]})
    PARAMS (p) GLOBALS (gv)
    SEP (node p Ip Cp)
    POST [ tptr tvoid ]
    ∃ (ret: val),
    PROP ({[x]} = dom Cp /\ ret = match Cp !! x with
                                 | Some v => v
                                 | None => nullval
                                 end)
    RETURN (ret)
    SEP (node p Ip Cp);

    (* insertOp_spec *)
    insertOp_spec :=
        DECLARE _insertOp
    WITH x : Z, v : val, p : Node, Ip : flowintT, Cp : gmap Key KValue, gv : globals
    PRE [tptr t_struct_node, tint, tptr tvoid]
    PROP ((Int.min_signed < x < Int.max_signed)%Z; is_pointer_or_null v;
        in_inset _ _ Key x Ip p; ¬ in_outsets _ _ Key x Ip; ✓ Ip; x ∈ KS)
    PARAMS (p; Vint (Int.repr x); v)
    GLOBALS (gv)
    SEP (mem_mgr gv; node p Ip Cp)
    POST[ tptr t_struct_node ]
    ∃ (new_node: Node) (I_new I0: flowint_T) (C_new Cp' : gmap Key KValue),
    PROP (is_pointer_or_null new_node; (0 < sizeof (t_struct_node))%Z;
          if eq_dec new_node nullval then True else
          (Cp' = Cp ∧ C_new = {[x := v]}) \/ (Cp' = {[x := v]} ∧ C_new = Cp))
    RETURN (new_node)
    SEP (mem_mgr gv; 
       if eq_dec new_node nullval then ⌜dom Cp = {[x]} /\ p <> nullval⌝ ∧ node p Ip {[x := v]}
       else ⌜x ∉ dom Cp /\ dom I_new = {[new_node]} /\ dom I0 = {[p]}⌝ ∧
              malloc_token Ews1 t_struct_node new_node ∗
                node new_node I_new C_new ∗ node p I0 Cp' ∧
              ⌜(if eq_dec p nullval
                then (key_property_null new_node Ip I_new) /\
                       {[x]} ⊆ keyset _ _ _ I_new new_node /\
                       dom Cp ⊆ keyset _ _ _ I0 p /\ SC_null Ip I0 I_new new_node 
               else ((if decide (dom Cp' = dom Cp) then
                        ((key_property1 p new_node Ip I_new Cp x) /\
                           {[x]} ⊆ keyset _ _ _ I_new new_node /\ dom Cp ⊆ keyset _ _ _ I0 p)
                      else
                        ((key_property2 p new_node Ip I_new Cp' Cp x) /\ 
                          {[x]} ⊆ keyset _ _ _ I0 p /\ dom Cp ⊆ keyset _ _ _ I_new new_node)) /\
                       inf_map I0 = inf_map Ip /\
                       cxtLeq Ip I_new I0 p new_node))⌝);
  }.

  (* inFP γ_f Node pointer lock *)
  Definition inFP (γ_f : gname) (n : Node) (m : val) (lock : val) : mpred :=
    ∃ (N: gmap Node (val * val)),
      own (inG0 := nodemap_inG) γ_f (◯ (to_agree <$> N) : gmap_authR Node _) ∧
        ⌜N !! n = Some (m, lock)⌝.

  Definition own_nodes γ_f (I : @multiset_flowint_ur Key _ _ ) md :=
    ∃ N, ⌜dom N = dom I /\
           (forall n m l, N !! n = Some (m, l) -> is_pointer_or_null n /\ is_pointer_or_null m /\
                  is_pointer_or_null l /\ Znth (f n) md = m /\ (0 <= f n < Zlength md)%Z)⌝ ∧
         own (inG0 := nodemap_inG) γ_f (● (to_agree <$> N)).

  Global Instance inFP_persistent γ_f n m l : Persistent (inFP γ_f n m l).
  Proof.
    apply bi.exist_persistent.
    intros x.
    apply bi.and_persistent.
    apply own_core_persistent, (iris.algebra.auth.auth_frag_core_id _ ).
    apply _. apply _.
  Qed.

  Lemma inFP_duplicate γ_f n m l:
    inFP γ_f n m l ⊢ inFP γ_f n m l ∗ inFP γ_f n m l.
  Proof. by rewrite - bi.persistent_sep_dup; iIntros "?". Qed.

  Lemma in_FP_equiv γ_f p p1 p2 l1 l2:
    inFP γ_f p p1 l1 ∗ inFP γ_f p p2 l2 ⊢ ⌜p1 = p2 /\ l1 = l2⌝ .
  Proof.
    rewrite /inFP.
    iIntros "(HinFP1 & HinFP2)".
    iDestruct "HinFP1" as (N1) "(HinFP1 & %HN1)".
    iDestruct "HinFP2" as (N2) "(HinFP2 & %HN2)".
    iDestruct (own_valid_2 γ_f (◯ (to_agree <$> N1): gmap_authR _ _)
                 (◯ (to_agree <$> N2)) with "[$] [$]") as %Hown.
    rewrite auth_frag_op_valid in Hown.
    eapply lookup_valid_Some in Hown; last first.
    rewrite lookup_op ! lookup_fmap.
    erewrite HN1.
    by rewrite HN2 -Some_op.
    apply to_agree_op_inv_L in Hown.
    by inversion Hown.
  Qed.

  Lemma node_exist_inFP γ_f n m l md (I: @multiset_flowint_ur Key _ _):
    inFP γ_f n m l ∗ own_nodes γ_f I md  ⊢ ⌜n ∈ dom I⌝.
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

  Lemma node_exist_md γ_f n m l md (I: @multiset_flowint_ur Key _ _):
    inFP γ_f n m l ∗ own_nodes γ_f I md  ⊢ ⌜Znth (f n) md = m⌝.
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
    assert (is_Some (N0 !! n)) as HSome'.
    { apply Some_included_is_Some in Hown.
      destruct (N0 !! n) eqn: E; try done.
      rewrite fmap_is_Some //= in Hown. }
    rewrite /is_Some in HSome'.
    destruct HSome' as (? & HSome').
    destruct x as (m' & l').
    rewrite HSome' Some_included_total to_agree_included_L /= in Hown; subst.
    inversion Hown; subst.
    by eapply Hznth.
  Qed.

  Lemma ghost_snapshot_fp γ_f I md q:
    own_nodes γ_f I md ∧ ⌜q ∈ dom I⌝ ==∗ own_nodes γ_f I md ∗
    (∃ q1 l, inFP γ_f q q1 l ∧
         ⌜is_pointer_or_null q /\ is_pointer_or_null q1 /\ is_pointer_or_null l /\
                   Znth (f q) md = q1 /\ (0 <= f q < Zlength md)%Z⌝).
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
    destruct Hc as (? & Hc).
    assert (q ∈ dom N0) as Hq_dom_N0.
    { by rewrite -H in Hq_dom. }
    rewrite elem_of_dom /is_Some in Hq_dom_N0.
    destruct Hq_dom_N0 as ((x1 & x2) & ?).
    specialize (Hc q x1 x2).
    destruct Hc as (? & ? & ? & ?); try done.
    iExists x1, x2. by iFrame "Haf".
  Qed.

End NodeRep.
