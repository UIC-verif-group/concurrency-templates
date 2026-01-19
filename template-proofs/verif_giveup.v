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
Require Import VST.floyd.library.
Require Import VST.atomics.verif_lock_atomic.
Require Import tmpl.flows_ora.
Require Import tmpl.keyset_ra_ora.
Require Export tmpl.data_struct.
Require Export tmpl.template_class.
Require Export tmpl.giveup_lib.
Require Export tmpl.giveup. (* AST of giveup.c *)

Section verif_giveup_template.
  Existing Instance giveup_lib.CompSpecs.
  Definition Vprog : varspecs. mk_varspecs prog. Defined. 
  
  Context `{NR: NodeRep } `{EqDecision K} `{Countable K}.
  Context `{!cinvG Σ, atom_impl : !atomic_int_impl (Tstruct _atom_int noattr), !flowintG Σ,
        !nodesetG Σ, !nodemapG Σ, !keymapG Σ, !keysetG Σ, !inG Σ (excl_authR (leibnizO val))}.

  #[local] Program Instance specific_template : Template := {
      NodeRt := NodeR;
      CSSt := CSS;
      md_entry_rep_t := md_entry_rep;
      belongs_t := belongs;
      is_root_t := is_root;
      Ip_of := Ip;
      Cp_of := Cp;
    }.
  
  Definition lookup_md_spec :=
    DECLARE _lookup_md
      ATOMIC TYPE (ConstType (val * Node * val * val *
                                gname * gname * gname * gname * gname * gname * globals))
    OBJ C INVS empty
    WITH c, p, p1, l, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, gv
    PRE [ tptr t_struct_css, tptr t_struct_node ]
    PROP (is_pointer_or_null p)
    PARAMS (c; p)
    GLOBALS (gv)
    SEP (inFP γ_f p p1 l) | (CSS γ_I γ_f γ_k γ_g γ_m γ_n C c)
    POST[ tptr t_md_entry ]
    ∃ p1' : val,
      PROP ()
        LOCAL (temp ret_temp p1')
        SEP (⌜p1' = p1 /\ (0 ≤ f p < size)%Z⌝ ∧ inFP γ_f p p1 l;
             ∃ (lsh : share),
               ⌜readable_share lsh⌝ ∧
                 field_at (cs := giveup_lib.CompSpecs) lsh t_md_entry [StructField _lock] l p1) |
      (CSS γ_I γ_f γ_k γ_g γ_m γ_n C c).

  Definition inRange_spec :=
    DECLARE _inRange
      WITH x: Z, m: val, min: Z, max : Z, sh: share, gv: globals
    PRE [ tptr t_md_entry, tint]
    PROP (writable_share sh; repable_signed min; repable_signed max; repable_signed x)
    PARAMS (m; Vint (Int.repr x))
    GLOBALS (gv)
    SEP (field_at sh t_md_entry [StructField _min] (Vint (Int.repr min)) m;
         field_at sh t_md_entry [StructField _max] (Vint (Int.repr max)) m)
    POST [ tint ]
    ∃ (succ: bool),
    PROP (match succ with
          | true => (min < x < max)%Z
          | false => ((x <= min)%Z ∨ (max <= x)%Z)
         end)
    LOCAL (temp ret_temp (Vint (if succ then Int.one else Int.zero)))
    SEP (field_at sh t_md_entry [StructField _min] (Vint (Int.repr min)) m;
         field_at sh t_md_entry [StructField _max] (Vint (Int.repr max)) m).

  (** inRange proof **)
  Lemma inRange_giveup: semax_body Vprog Gprog f_inRange inRange_spec.
  Proof.
    start_function.
    forward.
    forward_if (PROP ()
                  LOCAL (temp _t'1 (if andb (Z.ltb min x) (Z.ltb x max)
                                    then Val.of_bool true
                                    else Val.of_bool false);
                         temp _t'2 (vint min); gvars gv; temp _m m; temp _x (vint x))
                  SEP (field_at sh t_md_entry (DOT _min) (vint min) m;
                       field_at sh t_md_entry (DOT _max) (vint max) m)).
    - repeat forward. entailer !.
      destruct (Z.ltb_spec min x), (Z.ltb_spec x max); try rep_lia.
      + rewrite / Val.of_bool /Int.lt.
        autorewrite with norm; auto.
      + rewrite /Val.of_bool /Int.lt.
        apply Z.le_ge in H9.
        destruct (zlt x max); [try easy | auto].
    - forward.
      destruct (Z.ltb_spec min x); try rep_lia.
      entailer !.
    - forward_if. forward.
      + assert (((Z.ltb min x) && (Z.ltb x max))%bool = true) as Hx.
        { destruct((Z.ltb min x) && (Z.ltb x max))%bool; easy. }
        Exists true. entailer !.
      + assert (((Z.ltb min x) && (Z.ltb x max))%bool = false) as Hy.
        { destruct ((Z.ltb min x) && (Z.ltb x max))%bool; easy. }
        forward.
        Exists false.
        entailer !.
  Qed.
  
  Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec; surely_malloc_spec;
                             hash_spec; insertOp_spec; findnext_spec;
                             inRange_spec; get_key_spec; lookup_md_spec; get_value_spec]).

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

  Ltac change_compspecs_warning A cs cs' ::= idtac.
  
  Instance cce : change_composite_env template_class.CompSpecs giveup_lib.CompSpecs.
  Proof.
    make_cs_preserve template_class.CompSpecs giveup_lib.CompSpecs.
  Defined.

  Instance cce1 : change_composite_env (@DS_compspecs Σ VSTGS0 NR) giveup_lib.CompSpecs.
  Proof.
    make_cs_preserve (@DS_compspecs Σ VSTGS0 NR) giveup_lib.CompSpecs.
  Defined.

  Definition traverse_inv (γ_f : gname) (pn p p1 l c : val) (sh: share) (x : Z) gv
    AS : environ -> mpred :=
    ∃ (pnN pnP: Node) (pn1 l1 : val),
      PROP (is_pointer_or_null pnN; is_pointer_or_null l1)
        LOCAL (temp _p p; temp _status (vint 2); temp _pn__2 pn; temp _c c; temp _x (vint x);
               gvars gv)
        SEP (⌜pnN <> nullval /\ (0 ≤ f pnN < size)%Z⌝ ∧ inFP γ_f pnN pn1 l1;
             data_at sh (t_struct_pn) (pnP, pnN) pn; inFP γ_f p p1 l; AS; mem_mgr gv).

  Definition traverse_inv_NF
    (γ_I γ_f γ_k γ_m γ_n : gname) pn pnN ptn1 lock (nr1 : NodeR) r c x :=
    ∃ pnN', ⌜(min nr1 < x < max nr1)%Z /\ pnN ≠ nullval /\ x ∉ dom (Cp nr1) /\
              is_pointer_or_null pnN /\ is_pointer_or_null lock /\ in_inset _ _ _ x (Ip nr1) pnN /\
              ¬ in_outsets _ _ _  x (Ip nr1) /\ (pnN ≠ nullval -> belongs x nr1) /\ ✓ (Ip nr1) /\
              (pnN = nullval -> r = nullval)⌝ ∧
    inFP γ_f pnN ptn1 lock ∗ data_at Ews (t_struct_pn) (pnN, pnN') pn ∗ 
    md_entry_rep γ_I γ_k γ_m γ_n ptn1 pnN nr1 c r.

  Definition traverse_inv_F
    (γ_I γ_f γ_k γ_m γ_n : gname) pn pnN ptn1 lock (nr1 : NodeR) r c x :=
    ⌜(min nr1 < x < max nr1)%Z /\ pnN ≠ nullval /\ (dom (Cp nr1) = {[x]}) /\ 
      is_pointer_or_null pnN /\ is_pointer_or_null lock /\
      in_inset _ _ _ x (Ip nr1) pnN /\ 
      ¬ in_outsets _ _ _  x (Ip nr1) /\ (pnN ≠ nullval -> belongs x nr1) /\ ✓ (Ip nr1) /\
      (pnN = nullval -> r = nullval)⌝ ∧
      inFP γ_f pnN ptn1 lock ∗ data_at Ews (t_struct_pn) (pnN, pnN) pn ∗ 
      md_entry_rep γ_I γ_k γ_m γ_n ptn1 pnN nr1 c r. 

  Lemma data_at_valid_pointer_p γ_I γ_k γ_m γ_n p p1 l c r:
      md_entry_rep γ_I γ_k γ_m γ_n p1 p l c r  ⊢ valid_pointer p.
  Proof.
    iIntros "(? & ? & ? & ? & Hn & ?)".
    iApply (node_rep_R_valid_pointer with "[$Hn]").
  Qed.
  Local Hint Resolve data_at_valid_pointer_p: valid_pointer.

  (** traverse proof **)
  Lemma traverse_giveup: semax_body Vprog Gprog f_traverse traverse_spec.
  Proof.
    start_function.
    rewrite /is_root_t /=.
    set cs := giveup_lib.CompSpecs.
    set cs' := template_class.CompSpecs.
    change_compspecs' cs cs'.
    set (AS := atomic_shift _ _ _ _ _ ).
    set Q1:= fun (v : val ) => AS.
    forward. forward.
    simpl.
    clear dependent cs'.
    rewrite /cs.
    (* md_entry* md = lookup_md(c, pn->n); *)
    forward_call (c, pnN, p1, l, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, gv, Q1).
    { rewrite /rev_curry /=. apply bi.sep_mono; [|cancel]. by iApply AS_to_AS. }
    split; auto.
    Intros p lsh.
    rewrite H6 /Q1.
    do 2 forward.
    forward_call acquire_inv_atomic (l, ∃ (r : val) (nr: NodeR), ⌜is_pointer_or_null r⌝ ∧
       inFP γ_f pnN p1 l ∗ AS ∗ md_entry_rep γ_I γ_k γ_m γ_n p1 pnN nr c r).
    { iIntros "(AU & HinFP & Hf & Hd & Hgv)".
      iCombine "HinFP AU" as "HAU".
      iCombine "Hgv Hf Hd" as "Hrst".
      iStopProof.
      apply bi.sep_mono; [|cancel]. iApply (acquire_lock None).
    }
    simpl.
    Intros nrv.
    destruct nrv as (r & nr).
    forward.
    assert_PROP (is_pointer_or_null r). entailer !.
    (* if(!pn->n) *)
    forward_if (PROP ( )
      LOCAL (temp _status (vint 2); gvars gv; temp _c c; temp _pn__2 pn; temp _x (vint x))
      SEP (AS; mem_mgr gv; ∃ (n : Node) (p1 l: val), ⌜n <> nullval /\ is_pointer_or_null n /\
        is_pointer_or_null p1 /\ is_pointer_or_null l /\ (0 ≤ f n < size)%Z⌝ ∧
            inFP γ_f n p1 l ∗ data_at Ews t_struct_pn (nullval, n) pn)).
    - rewrite /md_entry_rep if_true; auto.
      forward.
      (* hash (r) *)
      forward_call (r).
      forward.
      forward_call (pnN).
      forward_if.
      + (* CONTINUE *)
        subst pnN. (* pnN = nullval *)
        (* obtain r = nullval *)
        destruct H20 as (Hfrange & Hrep).
        apply repr_inj_signed, f_injective in H19; auto.
        (* push back lock into invariant *)
        gather_SEP AS (inFP γ_f nullval p1 l)
          (field_at (cs := CompSpecs) _ _ [StructField _lock] _ _).
        viewshift_SEP 0 (AS ∗ (inFP γ_f nullval p1 l)).
        { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
        (* end - push back lock into invariant *)
        Intros.
        gather_SEP (node _ _ _) (malloc_token _ _ _) (field_at _ _ _ _ _)
          (field_at _ _ _ _ _) (own _ _) (own _ _) (own _ _) (own _ _) (field_at _ _ _ _ _).
        viewshift_SEP 0 (md_entry_rep γ_I γ_k γ_m γ_n p1 nullval nr c r).
        { go_lowerx. rewrite bi.sep_emp.
          iIntros "(Hn & Hml & Hmin & Hmax & HfI & Hfk & Hfm & Hfn & Hf_css)".
          iFrame. iPureIntro; repeat (split; auto).
        }
        gather_SEP AS (inFP γ_f nullval p1 l).
        Intros.
        gather_SEP AS (md_entry_rep γ_I γ_k γ_m γ_n p1 nullval nr c r).
        viewshift_SEP 0 (⌜x ∉ dom (Cp nr) /\ in_inset _ _ _ x (Ip nr) nullval ∧
                           ¬ in_outsets _ _ _ x (Ip nr) ∧ ✓ Ip nr⌝ ∧
                           AS ∗ (md_entry_rep γ_I γ_k γ_m γ_n p1 nullval nr c r)).
        { go_lowerx; rewrite bi.sep_emp -in_out_nullval_node; auto. }
        Intros.
        gather_SEP AS (inFP γ_f nullval p1 l).
        viewshift_SEP 0 (Q (CNT, nullval, p1, l, nr, r) ∗ inFP γ_f nullval p1 l).
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
        Exists (CNT, nullval, p1, l, nr, nullval).
        Exists nullval.
        set cs' := template_class.CompSpecs.
        change_compspecs' cs cs'.
        entailer !.
      + (*obtain r <> nullval *)
        forward.
        destruct H20 as (Hfrange & Hrep).
        apply repr_neq_e in H19; auto.
        assert (r <> nullval) as Hne_r_null.
        { intros Hcontra. subst r pnN. easy. }
        forward.
        (* release (mdr->lock); *)
        (* push back lock into invariant *)
        gather_SEP AS (inFP γ_f pnN _ _)
          (field_at (cs := CompSpecs) _ _ [StructField _lock] _ _).
        viewshift_SEP 0 (AS ∗ (inFP γ_f pnN p1 l)).
        { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
        (* end - push back lock into invariant *)
        Intros.
        gather_SEP (node _ _ _) (malloc_token _ _ _) (field_at _ _ _ _ _)
          (field_at _ _ _ _ _) (own _ _) (own _ _) (own _ _) (own _ _) (field_at _ _ _ _ _).
        viewshift_SEP 0 (md_entry_rep γ_I γ_k γ_m γ_n p1 pnN nr c r).
        { go_lowerx. rewrite bi.sep_emp.
          iIntros "(Hn & Hml & Hmin & Hmax & HfI & Hfk & Hfm & Hfn & Hf_css)".
          iFrame.
          rewrite -> if_true; auto.
          iFrame "Hfn Hf_css".
          iPureIntro; repeat (split; auto).
        }
        (* gain inFP γ_f r pr lr *)
        gather_SEP AS (md_entry_rep γ_I γ_k γ_m γ_n p1 pnN nr c r).
        viewshift_SEP 0 (∃ pr lr, AS ∗ (md_entry_rep γ_I γ_k γ_m γ_n p1 pnN nr c r) ∗
                           inFP γ_f r pr lr ∧
                                        ⌜is_pointer_or_null pr /\ is_pointer_or_null lr /\
                                         (0 <= f r < size)%Z⌝).
        { go_lowerx. rewrite bi.sep_emp.
          iIntros "(HAU & Hmd)".
          iMod "HAU" as (m) "(Hm & HClose)".
          rewrite /CSSt /=.
          rewrite {1} /CSS.
          iDestruct "Hm" as (I md r1) "HCSSi".
          iDestruct (unify_root with "[$HCSSi $Hmd]") as %<-; auto.
          iMod (ghost_update_root with "[$HCSSi]") as "inFP".
          iDestruct "inFP" as (pr lr) "(HCSS & inFP & %Hc)".
          iAssert (⌜is_pointer_or_null pr ∧ is_pointer_or_null lr ∧ (0 ≤ f r < size)%Z⌝) as "Hc".
          { destruct Hc as (? & ? & ? & ? & ?).
            iPureIntro. split; auto.
          }
          iExists pr, lr.
          iFrame "Hc ∗".
          by iApply "HClose".
        }
        Intros pr lr.
        forward_call release_inv (l, md_entry_rep γ_I γ_k γ_m γ_n p1 pnN nr c r, AS).
        { rewrite /rev_curry /=. lock_props.
          iIntros "(HAU & Hmd & HinFP1 & HinFP & Hdata & Hgv)".
          iCombine "HAU HinFP Hmd" as "?".
          iCombine "HinFP1 Hdata Hgv" as "?".
          iStopProof.
          apply bi.sep_mono; [|cancel].
          rewrite /AS -release_lock.
          rewrite /CSSt /=.
          entailer !. 
        }
        simpl.
        Exists r pr lr. entailer !.
   - (* release(md->lock);  *)
     forward.
     simpl.
     (* push back lock into invariant *)
     gather_SEP AS (inFP γ_f _ _ _) (field_at _ _ _ _ _).
     viewshift_SEP 0 (AS ∗ (inFP γ_f pnN p1 l)).
     { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
     sep_apply inFP_duplicate.
     forward_call release_inv (l, md_entry_rep γ_I γ_k γ_m γ_n p1 pnN nr c r, AS).
     { rewrite /rev_curry /=. lock_props.
       iIntros "((HinFP & HinFP1) & HAU & Hmd & Hgv & Hdata)".
       iCombine "HAU HinFP Hmd" as "?".
       iCombine "HinFP1 Hdata Hgv" as "?".
       iStopProof.
       apply bi.sep_mono; [|cancel].
       rewrite /AS -release_lock /md_entry_rep if_false; auto.
       rewrite /CSSt /=. entailer !.
     }
     simpl.
     entailer !.
     Exists pnN p1 l. entailer !.
   - (** main program **)
     clear dependent pnN.
     Intros n ptn lkn.
     rewrite /cs.
     forward.
     sep_apply inFP_duplicate.
     forward_loop (traverse_inv γ_f pn n ptn lkn c Ews x gv AS)
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
                    md_entry_rep γ_I γ_k γ_m γ_n pt1 nullval nrt c rt ∗
                    ∃ pnN, data_at Ews t_struct_pn (nullval, pnN) pn
             end) ∗
               Q rtrn ∗ mem_mgr gv)).
    + rewrite /traverse_inv.
      Exists n nullval ptn lkn.
      entailer !.
    + (** go deeply into loop **)
      (*pre-condition*)
      rewrite /cs /traverse_inv.
      Intros pnN pnP ptn1 lock.
      forward.
      gather_SEP AS.
      (* md_entry* md = lookup_md(c, pn->n); *)
      forward_call (c, pnN, ptn1, lock, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, gv, Q1).
      { rewrite /rev_curry /=. apply bi.sep_mono; [|cancel]. by iApply AS_to_AS. }
      simpl.
      split; auto.
      Intros pt1 lsh1.
      rewrite H13.
      forward. forward.
      (* acquire(md->lock); *)
      forward_call acquire_inv_atomic (lock, ∃ (r : val) (nr: NodeR),
            ⌜is_pointer_or_null r⌝ ∧ inFP γ_f pnN ptn1 lock ∗ AS ∗
                                       md_entry_rep γ_I γ_k γ_m γ_n ptn1 pnN nr c r).
      { iIntros "(AU & HinFP & Hf & Hd & Hgv)".
        iCombine "HinFP AU" as "HAU".
        iCombine "Hgv Hf Hd" as "Hrst".
        iStopProof.
        apply bi.sep_mono; [|cancel]. iApply (acquire_lock None).
      }
      Intros nrv.
      destruct nrv as (r1 & nr1).
      forward.
      forward.
      simpl.
      (* inrange function *)
      rewrite /md_entry_rep.
      Intros.
      forward_call(x, ptn1, (min nr1), (max nr1), Ews, gv).
      Intros succ.
      destruct succ.
      ** forward_if.
         rewrite /cs.
         forward.
         rewrite -> if_false; auto.
         assert_PROP(field_compatible t_struct_pn [StructField _n] pn). entailer !.
           (* findNext *)
         forward_call(x, pnN, (field_address t_struct_pn [StructField _n] pn),
                         pnN, (Ip nr1), (Cp nr1), Ews, gv).
         { unfold_data_at (data_at Ews t_struct_pn _ pn).
           set cs' := (@DS_compspecs Σ VSTGS0 NR).
           change_compspecs' cs cs'.
           rewrite /cs. entailer !.
         }
         Intros stt.
         destruct stt.1; last first.
         Intros.
         forward.
         forward_if.
         ++ easy. (* contradiction *)
         ++ forward_if.
            { easy. } (* contradiction *)
            destruct stt as (q & rest).
            simpl in H25, H26.
            set cs' := (@DS_compspecs Σ VSTGS0 NR).
            change_compspecs' cs cs'.
            rewrite /cs.
              (* replace *)
            replace (data_at Ews (tptr t_struct_node) rest
                         (field_address t_struct_pn (DOT _n) pn)) with
                (field_at (cs := CompSpecs) Ews t_struct_pn (DOT _n) rest pn).
            2: {
              rewrite /cs.
              rewrite field_at_data_at; try done.
            }
            clear dependent cs'.
            simpl.
            rewrite H13. (* pt1 = ptn1 *)
            forward.
            (* release(md->lock); *)
            (* push back lock into invariant *)
            gather_SEP AS (inFP γ_f pnN ptn1 lock)
                (field_at (cs := CompSpecs) lsh1 t_md_entry (DOT _lock) lock ptn1).
            viewshift_SEP 0 (AS ∗ (inFP γ_f pnN ptn1 lock)).
            { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
            (* gather to have md_entry_rep *)
            gather_SEP (node pnN _ _) (malloc_token _ _ _) (field_at _ t_md_entry  _ _ _)
                (field_at _ t_md_entry  _ _ _) (own γ_I _) (own γ_k _) (own γ_m _).
            (* actually c and r are nonsense here, change if needed*)
            viewshift_SEP 0 (md_entry_rep γ_I γ_k γ_m γ_n ptn1 pnN nr1 c r).
            { go_lowerx. rewrite bi.sep_emp.
              iIntros "(Hn & Hml & Hmin & Hmax & HfI & Hfk & Hfm)".
              rewrite /md_entry_rep if_false; auto.
              iFrame; iPureIntro; repeat (split; auto).
            }
            Intros.
            gather_SEP AS (md_entry_rep γ_I γ_k γ_m γ_n ptn1 pnN nr1 c r).
            viewshift_SEP 0 (∃ q1 l,
               AS ∗ md_entry_rep γ_I γ_k γ_m γ_n ptn1 pnN nr1 c r ∗ inFP γ_f rest q1 l ∧
               ⌜is_pointer_or_null rest /\ is_pointer_or_null q1 /\
                is_pointer_or_null l /\ (0 <= f rest < size)%Z⌝).
            { go_lowerx. rewrite bi.sep_emp - get_inFP_not_null; eauto. }
            Intros p2 l2.
            forward_call release_inv (lock, md_entry_rep γ_I γ_k γ_m γ_n ptn1 pnN nr1 c r, AS).
            { rewrite /rev_curry /=. lock_props.
              iIntros "(HAU & Hmd & HinFP0 & HinFP & Hrest)".
              iCombine "HAU HinFP Hmd" as "?".
              iCombine " HinFP0 Hrest" as "?".
              iStopProof.
              apply bi.sep_mono; [|cancel].
              rewrite /AS -release_lock /md_entry_rep if_false; auto.
              rewrite /CSSt /=. entailer !.
            }
            simpl.
            rewrite /traverse_inv.
            Exists rest pnN p2 l2.
            subst.
            unfold_data_at (data_at Ews t_struct_pn _ pn). entailer !.
         ++ forward.
            forward_if.
            { easy. } (* contradiction *)
            forward_if; last first.
            { easy. } (* contradiction *)
            rewrite H13. (* pt1 = ptn1 *)
            (* NOTFOUND *)
            (* push back lock into invariant *)
            Intros.
            gather_SEP AS (inFP γ_f pnN ptn1 lock)
               (field_at (cs := CompSpecs) lsh1 t_md_entry (DOT _lock) lock ptn1).
            viewshift_SEP 0 (AS ∗ (inFP γ_f pnN ptn1 lock)).
            { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
             (*gather to have md_entry_rep *)
            gather_SEP (node pnN _ _) (malloc_token _ _ _) (field_at _ t_md_entry _ _ _)
               (field_at _ t_md_entry  _ _ _) (own γ_I _) (own γ_k _) (own γ_m _).
             (* actually c and r are nonsense here, change if needed*)
            viewshift_SEP 0 (md_entry_rep γ_I γ_k γ_m γ_n ptn1 pnN nr1 c r).
            { go_lowerx. rewrite bi.sep_emp.
              iIntros "(Hn & Hml & Hmin & Hmax & HfI & Hfk & Hfm)".
              rewrite /md_entry_rep if_false; auto.
              iFrame; iPureIntro; repeat (split; auto).
            }
            Intros.
            (* have valid flow ✓ Ip *)
            gather_SEP AS (md_entry_rep _ _ _ _ _ _ _ _ _ ).
            viewshift_SEP 0 (⌜✓ (Ip nr1)⌝ ∧ AS ∗ md_entry_rep γ_I γ_k γ_m γ_n ptn1 pnN nr1 c r).
            { go_lowerx. rewrite bi.sep_emp. iApply valid_flow. }
            Intros.
            gather_SEP AS (inFP γ_f pnN ptn1 lock).
            (* commit *)
            viewshift_SEP 0 (Q (NF, pnN, ptn1, lock, nr1, r) ∗ inFP γ_f pnN ptn1 lock).
            { go_lowerx; rewrite bi.sep_emp.
              iIntros "(AU & #HinFP)".
              iMod "AU" as (m) "(Hm & HClose)".
              iDestruct "HClose" as "(_ & HClose)".
              iMod ("HClose" with "[Hm]") as "Hm".
              iFrame "Hm". by iFrame "HinFP ∗".
            }
            forward.
            (* return NOTFOUND; *)
            (* Q (NF, pnN, ptn1, lock, nr1, r) *)
            Exists (NF, pnN, ptn1, lock, nr1, r).
            rewrite /traverse_inv_NF.
            Exists stt.2.
            subst.
            unfold_data_at (data_at Ews t_struct_pn _ pn).
            set cs' := (@DS_compspecs Σ VSTGS0 NR).
            change_compspecs' cs cs'.
            entailer !.
            iIntros "_"; done.
         ++ forward.
            forward_if; last first.
            { easy. } (* contradiction *)
            (* FOUND *)
            (* push back lock into invariant *)
            Intros.
            rewrite H13. (* pt1 = ptn1 *)
            gather_SEP AS (inFP γ_f pnN ptn1 lock)
               (field_at (cs := CompSpecs) lsh1 t_md_entry (DOT _lock) _ _).
            viewshift_SEP 0 (AS ∗ (inFP γ_f pnN ptn1 lock)).
            { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
             (*gather to have md_entry_rep *)
            gather_SEP (node pnN _ _) (malloc_token _ _ _) (field_at _ t_md_entry  _ _ _)
               (field_at _ t_md_entry  _ _ _) (own γ_I _) (own γ_k _) (own γ_m _).
            (* actually c and r are nonsense here, change if needed*)
            viewshift_SEP 0 (md_entry_rep γ_I γ_k γ_m γ_n ptn1 pnN nr1 c r).
            { go_lowerx. rewrite bi.sep_emp.
              iIntros "(Hn & Hml & Hmin & Hmax & HfI & Hfk & Hfm)".
              rewrite /md_entry_rep if_false; auto.
              iFrame; iPureIntro; repeat (split; auto).
            }
            Intros.
            (* have valid flow ✓ Ip *)
            gather_SEP AS (md_entry_rep _ _ _ _ _ _ _ _ _ ).
            viewshift_SEP 0 (⌜✓ (Ip nr1)⌝ ∧ AS ∗ md_entry_rep γ_I γ_k γ_m γ_n ptn1 pnN nr1 c r).
            { go_lowerx. rewrite bi.sep_emp. iApply valid_flow. }
            Intros.
            gather_SEP AS (inFP γ_f pnN ptn1 lock).
            (* commit *)
            viewshift_SEP 0 (Q (F, pnN, ptn1, lock, nr1, r) ∗ inFP γ_f pnN ptn1 lock).
            { go_lowerx; rewrite bi.sep_emp.
              iIntros "(AU & #HinFP)".
              iMod "AU" as (m) "(Hm & HClose)".
              iDestruct "HClose" as "(_ & HClose)".
              iMod ("HClose" with "[Hm]") as "Hm".
              iFrame "Hm". by iFrame "HinFP ∗".
            }
            forward.
            (* return FOUND; *)
            (* Q (F, pnN, ptn1, lock, nr1, r) *)
            Exists (F, pnN, ptn1, lock, nr1, r).
            rewrite /traverse_inv_F.
            subst.
            unfold_data_at (data_at Ews t_struct_pn _ pn).
            set cs' := (@DS_compspecs Σ VSTGS0 NR).
            change_compspecs' cs cs'.
            entailer !. by iIntros "_".
         ++ easy. (* contradiction *)
      ** forward_if.
         { easy. } (* contradiction *)
         rewrite -> if_false; auto.
         rewrite /cs.
         forward.
         (* release(md->lock); *)
         (* push back lock into invariant *)
         gather_SEP AS (inFP γ_f pnN ptn1 lock)
           (field_at (cs := CompSpecs) lsh1 t_md_entry (DOT _lock) lock ptn1).
         viewshift_SEP 0 (AS ∗ (inFP γ_f pnN ptn1 lock)).
         { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
         (*gather to have md_entry_rep *)
         gather_SEP (node _ _ _) (malloc_token _ _ _) (field_at _ t_md_entry _ _ _)
           (field_at _ t_md_entry _ _ _) (own γ_I _) (own γ_k _) (own γ_m _).
         (* actually c and r are nonsense here, change if needed*)
         viewshift_SEP 0 (md_entry_rep γ_I γ_k γ_m γ_n ptn1 pnN nr1 c r).
         { go_lowerx. rewrite bi.sep_emp.
           iIntros "(Hn & Hml & Hmin & Hmax & HfI & Hfk & Hfm)".
           rewrite /md_entry_rep if_false; auto.
           iFrame; iPureIntro; repeat (split; auto).
         }
         Intros.
         gather_SEP AS (inFP γ_f pnN ptn1 lock) (md_entry_rep _ _ _ _ _ _ _ _ _).
         forward_call release_inv (lock,
             md_entry_rep γ_I γ_k γ_m γ_n ptn1 pnN nr1 c r, AS).
         { rewrite /rev_curry /=. lock_props.
           iIntros "((HAU & HinFP & Hmd) & Hrest)".
           iCombine "HAU HinFP Hmd" as "?".
           iCombine "Hrest" as "?".
           iStopProof.
           apply bi.sep_mono; [|cancel].
           rewrite /AS -release_lock /md_entry_rep if_false; auto.
           rewrite /CSSt /=. entailer !.
         }
         simpl.
         forward.
         rewrite /traverse_inv.
         Exists n pnN ptn lkn.
         sep_apply inFP_duplicate. entailer !.
    + Intros rtrn.
      destruct rtrn as ((((stt & ptn1) & lock) & nr1) & r1).
      destruct stt as (stt & pnN).
      destruct stt.
      * forward.
        Exists (F, pnN, ptn1, lock, nr1, r1).
        Exists pnN.
        rewrite /traverse_inv_F.
        set cs' := template_class.CompSpecs.
        change_compspecs' cs cs'.
        entailer !.
      * forward.
        rewrite /traverse_inv_NF.
        Intros pnN'.
        Exists (NF, pnN, ptn1, lock, nr1, r1).
        Exists pnN'.
        set cs' := template_class.CompSpecs.
        change_compspecs' cs cs'.
        entailer !.
      * Intros.
        Intros pnN'.
        forward.
        Exists (CNT, nullval, ptn1, lock, nr1, r1).
        Exists pnN'.
        set cs' := template_class.CompSpecs.
        change_compspecs' cs cs'.
        entailer !.
  Qed.

  (** get_root proof **)
  Lemma get_root: semax_body Vprog Gprog f_get_root get_root_spec.
  Proof.
    start_function.
    rewrite /CSSt /=.
    set (AS := atomic_shift _ _ _ _ _ ).
    set Q1:= fun (v : val) => AS.
    gather_SEP AS.
    (* gain inFP γ_f nullval q1 l, before calling lookup_md *)
    viewshift_SEP 0 (AS ∗ ∃ q1 l, inFP γ_f nullval q1 l ∧
        ⌜is_pointer_or_null q1 /\ is_pointer_or_null l /\ (0 <= f nullval < size)%Z⌝).
    { go_lowerx. by rewrite bi.sep_emp - get_inFP_null. }
    Intros p1 l.
    (* call lookup_md *)
    forward_call (c, nullval, p1, l, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, gv, Q1).
    { rewrite /rev_curry /=. apply bi.sep_mono; [|cancel]. by iApply AS_to_AS. }
    repeat (split; auto).
    Intros q lsh.
    rewrite H2.
    forward.
    (* acquire *)
    forward_call acquire_inv_atomic (l,
        ∃ (r : val) (nr: NodeR), ⌜is_pointer_or_null r⌝ ∧ inFP γ_f nullval p1 l ∗ AS ∗
             md_entry_rep γ_I γ_k γ_m γ_n p1 nullval nr c r); rewrite /=.
    { rewrite /rev_curry /Q1 /=.
      iIntros "(HinFP & (AU & Hfl & Hgv))".
      iCombine "AU HinFP" as "HAU".
      iCombine "Hfl Hgv" as "Hrst".
      iStopProof.
      apply bi.sep_mono; [|cancel].
      iApply (acquire_lock None).
    }
    Intros ab.
    destruct ab as (r & nr).
    rewrite /md_entry_rep.
    rewrite -> if_true; auto.
    Intros.
    simpl.
    forward.
    gather_SEP AS (own γ_n _).
    (* gain inFP γ_f r p1 l1 for post condition *)
    viewshift_SEP 0 (∃ p1 l1,
          ⌜is_pointer_or_null r ∧ is_pointer_or_null p1 ∧
            is_pointer_or_null l1 /\ (0 ≤ f r < size)%Z⌝ ∧
            AS ∗ own γ_n (◯E r : excl_authR (leibnizO val)) ∗ inFP γ_f r p1 l1).
    { go_lowerx. rewrite bi.sep_emp.
      iIntros "(AU & Hown1)".
      iMod "AU" as (m) "(Hm & HClose)".
      simpl.
      rewrite {1} /CSS /CSSi.
      iDestruct "Hm" as (I md r1) "(%Hc & Hglob & Hml & Hidx & HNF & Hown)".
      iDestruct (own_valid_2 γ_n (●E r1 : excl_authR (leibnizO val)) (◯E r)
                  with "[$Hown] [$Hown1]") as %Hownr%@excl_auth_agree_L.
      iMod (ghost_update_root with "[$Hglob $Hml $Hidx $HNF $Hown]") as "HCSSi"; auto.
      iDestruct "HCSSi" as (pr lr) "(HCSSi & HinFP & %Hc1)".
      subst.
      iFrame.
      iDestruct "HClose" as "(HClose & _)".
      iSpecialize ("HClose" with "HCSSi").
      iMod ("HClose").
      iFrame "HClose".
      iPureIntro.
      destruct Hc1 as (? & ? & ? & ? & ?).
      repeat (split; auto).
    }
    Intros q1 l1.
    forward.
    (* push back lock into invariant *)
    gather_SEP AS (inFP γ_f nullval p1 l) (field_at (cs := CompSpecs) lsh _ _ _ p1).
    viewshift_SEP 0 (AS ∗ (inFP γ_f nullval p1 l)).
    { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
    (* end - push back lock into invariant *)
    (* release *)
    forward_call release_inv (l, md_entry_rep γ_I γ_k γ_m γ_n p1 nullval nr c r, AS).
    { rewrite /rev_curry /=. lock_props.
      iIntros "((HAU & HinFP) & Hfn & HinFP1 & Hml & Hmin & Hmax &
                  Hn & HfI & Hfk & Hfm & Hf_css & Hgv)".
      iCombine "HAU Hfn HinFP Hml Hmin Hmax Hn HfI Hfk Hfm Hf_css" as "?".
      iCombine "HinFP1 Hgv" as "?".
      iStopProof.
      apply bi.sep_mono; [|cancel].
      rewrite /AS -release_lock /md_entry_rep.
      rewrite -> if_true; auto.
      entailer !.
    }
    simpl.
    gather_SEP AS (inFP γ_f r q1 l1).
    viewshift_SEP 0 (∃ q1 l, ⌜is_pointer_or_null q1 /\ is_pointer_or_null l /\ (0 ≤ f r < size)%Z⌝ ∧
                               Q (r, q1, l) ∗ inFP γ_f r q1 l).
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
    rewrite /is_root_t /=.
    Exists (r, q2, l2).
    entailer !.
  Qed.

  (** make_css proof **)
  Lemma body_make_css: semax_body Vprog Gprog f_make_css make_css_spec.
  Proof.
    start_function.
    forward_call (t_struct_css, gv).
    Intros css.
    assert_PROP (isptr (field_address t_struct_css (DOT _metadata) css)).
    { entailer!. }
    forward_call (nullval).
    Intros.
    forward_call (t_md_entry, gv).
    Intros new.
    assert (size = 16384%Z) as Hsz by (setoid_rewrite (proj2_sig has_size); auto).
    rewrite /= in Hsz.
    assert ((0 ≤ f nullval < Zlength (Zrepeat Vundef 16384))%Z) as Hlen.
    { rewrite Zlength_Zrepeat -Hsz. auto. lia. }
    forward.
    simpl.
    forward_call (gv).
    Intros lock.
    forward.
    forward.
    simpl.
    rewrite upd_Znth_same; try auto.
    entailer !.
    rewrite upd_Znth_same; try done.
    forward.
    simpl.
    forward.
    simpl.
    rewrite upd_Znth_same; try done.
    entailer !.
    rewrite upd_Znth_same; try done.
    forward.
    forward.
    simpl.
    rewrite upd_Znth_same; try done.
    entailer !.
    rewrite upd_Znth_same; try done.
    forward.
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
    assert_PROP (isptr (field_address t_struct_css (DOT _metadata) css)).
    { entailer!. }
    rewrite /CSS /CSSi /globalGhost.
    set N1 := ({[nullval := (new, lock) ]} : gmap _ _).
    iIntros "(Htm & Hml & Hd & Hml1 & Hd1)".
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
    iMod (own_alloc ((●E nullval : excl_authR _) ⋅ (◯E nullval))) as (γ_n) "(Hn● & Hn◯)".
    { rewrite auth_both_valid_discrete. split; auto; try done. }
    
    iMod (own_alloc ((● (Excl <$> ∅) : keymap_authR _ _) ⋅ (◯ (Excl <$> ∅))))
      as (γ_m) "(Hm● & Hm◯)".
    { apply auth_both_valid_discrete. split; try done. }
    rewrite /CSS /CSSi.
    iIntros "!>".
    iExists γ_I, γ_f, γ_k, γ_f, γ_m, γ_n.
    iExists (flow_int {| infR := {[ nullval := ks]}; outR := ∅ |}).
    iExists (upd_Znth (f nullval) (Zrepeat Vundef 16384) new).
    iExists nullval.
    rewrite /nodeFull /dom /flowint_dom /= dom_singleton_L.
    rewrite (big_opS_delete _ _ nullval); auto.
    2: { set_solver. }
    rewrite difference_diag_L big_opS_empty.
    iFrame "Hf● HIr● Hks● Hn● Hm●".
    unfold_data_at (data_at _ _ _ css).
    assert (dom Ir = ({[nullval]} : gset _)) as Dom_Ir.
    { rewrite /Ir /dom /flowint_dom /=. set_solver. }
    rewrite /ltree.
    iDestruct "Hd1" as "(Hf & Hf1)".
    iSplit; auto.
    { iPureIntro. split; auto.
      rewrite Zlength_upd_Znth Zlength_Zrepeat. done. lia.
      clear. set_solver.
    }
    iSplitR.
    iSplit.
    { iPureIntro.
      split; auto.
      rewrite /globalinv.
      repeat (split; auto).
      rewrite /dom /=. set_solver.
      rewrite /dom /flowint_dom /=. set_solver.
      rewrite /closed /outset /out /=.
      intros k n Hcontra.
      rewrite nzmap_lookup_empty in Hcontra.
      set_solver.
      intros.
      rewrite /inset /inf /= lookup_insert Hdom; auto.
    }
    iSplit; auto.
    { iPureIntro.
      do 1 (split; auto).
      rewrite /N1 /flowint_dom /dom_singleton_L /inf_map /=.
      set_solver.
      intros ??? HN1_map.
      rewrite /N1 in HN1_map.
      assert (n = nullval) as H_eq_n_null.
      { destruct (decide (n = nullval)); subst; last first; auto.
        rewrite lookup_singleton_ne in HN1_map; auto. easy.
      }
      rewrite H_eq_n_null lookup_singleton in HN1_map.
      inversion HN1_map; subst.
      repeat (split; auto).
      rewrite upd_Znth_same; auto. lia.
      rewrite Zlength_upd_Znth Zlength_Zrepeat. lia. lia.
    }
    iFrame "Hml1".
    rewrite ! Zlength_upd_Znth ! upd_Znth_same; auto.
    iAssert (([∗ set] i ∈ upto_gset size ∖ {[0%Z]}, md_slot i css) ∗
               field_at (cs := CompSpecs)
               Ews t_struct_css [ArraySubsc (f nullval); StructField _metadata] new css )
              with "[Hf1]"as "(Hidxs & Harr)".
    {
      rewrite field_at_data_at.
      iDestruct (data_at_array_elems _ (tptr (Tstruct _md_entry noattr)) with "[$Hf1]") as "Hf1".
      change (upto _) with (0%Z :: map Z.succ (upto (Z.to_nat 16383))).
      rewrite big_sepL_cons.
      iDestruct "Hf1" as "(Hf & Hf1)".
      iSplitR "Hf"; last first.
      rewrite css_array_to_nested_field. iFrame "Hf"; auto. auto. lia.
      rewrite /upto_gset /Zseq Z2Nat.inj_0 list_to_set_map_seq0_remove_zero
        big_sepS_list_to_set /Zseq.
      rewrite succ_upto_size Hsz.
      iApply (big_sepL_mono with "Hf1").
      intros.
      iIntros "H".
      iLeft.
      unfold field_at_.
      rewrite (field_at_app _ _ [ArraySubsc y] [_]); last done.
      iStopProof.
      cancel.
      apply NoDup_Z_of_nat_seq.
    }
    iFrame "Hidxs Harr".
    iExists new.
    iSplit; auto.
    { iPureIntro. split; auto. }
    set (nr := {| min := Int.min_signed; max := Int.max_signed; Cp := ∅; Ip := Ir; |}).
    iExists Ews, lock, nr.
    unfold_data_at (data_at _ _ _ new).
    iDestruct "Hd" as "(Hlock & Hmin & Hmax)".
    iFrame "Hlock".
    iSplit.
    { iPureIntro. split; auto. }
    iSplitL "Hf◯".
    { rewrite /inFP.
      iExists N1.
      iSplit; try done.
      rewrite /N1 lookup_insert; try done.
    }
    rewrite /inv_for_lock.
    iExists false.
    iFrame "Htm".
    rewrite /md_entry_rep.
    rewrite -> if_true; auto.
    rewrite /nr /=.
    iFrame "Hf Hmin Hmax Hml HIr◯ Hm◯".
    assert (keyset _ _ _ Ir nullval = KS) as Hkeyset.
    { rewrite /keyset /Ir /outsets big_opS_empty /inf lookup_insert Hdom /=. set_solver. }
    rewrite Hkeyset dom_empty_L.
    iFrame "Hn◯ Hks◯".
    iSplit; auto.
    { iDestruct (imply_node ks Ir with "[%]") as "Hnode".
      { split; auto. }
      iFrame "Hnode".
      iPureIntro. split; auto.
    }
  Qed.
  
  (** lookup_md proof **)
  Lemma lookup_md: semax_body Vprog Gprog f_lookup_md lookup_md_spec.
  Proof.
    start_function.
    set (AS := atomic_shift _ _ _ _ _ ).
    assert (size = 16384%Z) as Hsz by (setoid_rewrite (proj2_sig has_size); auto).
    simpl in Hsz.
    forward_call (p).
    gather_SEP AS (inFP γ_f p p1 l).
    viewshift_SEP 0 (AS ∗ inFP γ_f p p1 l ∗
                   (∃ (lsh : share) (md : list val),
                     ⌜readable_share lsh /\ Znth (f p) md = p1 /\
                       is_pointer_or_null (Znth (f p) md)⌝ ∧
                       field_at lsh t_struct_css [ArraySubsc (f p); StructField _metadata]
                         (Znth (f p) md) c) ∗
                  (∃ (lsh : share), ⌜readable_share lsh⌝ ∧
                                      field_at lsh t_md_entry [StructField _lock] l p1)).
    { go_lowerx. by rewrite bi.sep_emp md_lock_alloc. }
    Intros lsh1 md lsh2.
    forward.
    gather_SEP AS (inFP γ_f _ _ _) (field_at _ _ _ _ c).
    viewshift_SEP 0 (AS ∗ inFP γ_f p p1 l).
    { go_lowerx; rewrite bi.sep_emp. by apply md_push_back. }
    viewshift_SEP 0 (Q p1 ∗ inFP γ_f p p1 l).
    { go_lowerx; rewrite bi.sep_emp.
      iIntros "(AU & #HinFP)".
      iMod "AU" as (m) "(Hm & HClose)".
      iDestruct "HClose" as "(_ & HClose)".
      iMod ("HClose" with "[Hm]") as "Hm".
      iFrame "Hm".
      by iFrame "HinFP ∗".
    }
    forward.
    Exists (Znth (f p) md).
    entailer !. 
    iIntros "Hf".
    iExists lsh2; auto.
  Qed.

  (** insertOp_helper **)
  Lemma data_at_field_compatible : forall new,
      data_at_ Ews t_md_entry new ⊢ ⌜field_compatible t_md_entry [] new⌝.
  Proof.
    intros.
    iIntros "H".
    iApply (data_at__local_facts with "[$H]").
  Qed.
  Local Hint Resolve data_at_field_compatible: valid_pointer.

  (** insertOp_helper proof **)
  Lemma insertOp_helper: semax_body Vprog Gprog f_insertOp_helper insertOp_helper_spec.
  Proof.
    start_function.
    rewrite /md_entry_rep_t /= /md_entry_rep.
    Intros.
    forward_call (x, v, p, (Ip nr), (Cp nr), gv).
    Intros nflwt.
    destruct nflwt as ((((new_node & I_new) & I0) & C_new) & Cp').
    destruct (decide (new_node = nullval)); subst.
    - (* clear H17. *)
      rewrite -> if_true; auto.
      set (AS := atomic_shift _ _ _ _ _).
      Intros.
      forward_if.
      + rewrite if_false; auto.
        set (nr_p := {| min := (min nr); max := (max nr); Cp := {[x := v]}; Ip := (Ip nr); |}).
        gather_SEP AS (node p _ _) (inFP _ _ _ _) (malloc_token _ _ _)
          (field_at (cs := CompSpecs) _ t_md_entry [StructField _min] _ _)
          (field_at (cs := CompSpecs) _ t_md_entry [StructField _max] _ _)
          (own γ_I _) (own γ_k _) (own γ_m _).
        (* md_entry* md = lookup_md(c, p); *)
        set Q1:= fun (v : val ) => AS.
        Intros.
        forward_call (css, p, p1, l, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, gv, Q1).
        { rewrite /rev_curry /=. apply bi.sep_mono; [|cancel]. by iApply AS_to_AS. }
        simpl.
        subst; try done.
        Intros lk lsh.
        rewrite H22.
        forward.
        (* push back lock into invariant *)
        rewrite /Q1.
        gather_SEP AS (inFP γ_f p p1 l) (field_at (cs := CompSpecs) lsh _ _ _ p1).
        viewshift_SEP 0 (AS ∗ (inFP γ_f p p1 l)).
        { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
        (* end - push back lock into invariant *)
        Intros.
        forward_call (l, Q).
        { rewrite /rev_curry /Q1 /=.
          iIntros "(AU & HinFP & Hnode & Hml_p & Hmin & Hmax & HI & Hk & Hm' & Hgv)".
          iCombine "AU HinFP Hnode Hml_p Hmin Hmax HI Hk Hm'" as "Hmd".
          iCombine "Hgv" as "Hframe".
          iStopProof.
          apply bi.sep_mono; [|cancel].
          iIntros "(AU & #HinFP & Hnode & Hml_p & Hmin & Hmax & HI & Hk & Hm')".
          unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
          iMod "AU" as (m) "(Hm & HClose)".
          iDestruct "Hm" as (I md r1) "(%Hc & Hglob & Hml & Hidx & HNF & Hown)".
          iModIntro.
          iExists tt.
          iAssert (⌜p ∈ dom I⌝) with "[Hglob HI]" as "%HpInDom".
          { iDestruct "Hglob" as "(%Hglob & HauthI & Hauthk & Hauthm & Hown_nodes)".
            destruct Hglob as (Hglob & Hr).
            iDestruct (own_valid_2 with "[$HauthI] [$HI]") as "%HvIp".
            apply auth_both_valid_discrete in HvIp.
            destruct HvIp as (Hle & Valid_I).
            destruct Hle as [Io I_incl].
            iPureIntro.
            rewrite I_incl in Valid_I.
            rewrite I_incl.
            rewrite intComp_dom; auto.
            set_solver.
          }
          setoid_rewrite (big_opS_delete _ _ p) at 1; auto.
          iDestruct "HNF" as "(HNF & Hrest)".
          iDestruct "HNF" as (q qsh) "(% & Hf & Hlt)".
          rewrite {1} /ltree.
          iDestruct "Hlt" as (lsh1 lk1 nr1') "(% & Hf1 & HinFP1 & Hinv)".
          iAssert (⌜q = p1 /\ lk1 = l⌝) with "[HinFP HinFP1]" as "%Hpk".
          { iDestruct (in_FP_equiv _ p q p1 lk1 l with "[$HinFP $HinFP1]") as "?"; auto. }
          destruct Hpk as (Hpt & Hlk).
          rewrite Hpt Hlk.
          iDestruct "Hinv" as (b) "(Htm1 & Hmd1)".
          destruct b.
          2 :{ 
            iDestruct "Hmd1" as "(? & Hml1 & ?)".
            iPoseProof (malloc_token_conflict with "[$Hml1 $Hml_p]") as "HF";
              simpl; eauto. lia.
          }
          iFrame "Htm1".
          iSplit.
          iIntros "Htm1".
          simpl.
          iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css) with
                "[$Hglob $Hml $Hidx Hf Hf1 HinFP1 Htm1 Hmd1 Hrest $Hown]" as "Hcss".
          { destruct H25 as (? & ? & ? & ?).
            destruct H26 as (? & ? & ?).
            iSplit; auto.
            setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
            iFrame.
            iSplit; auto.
            iPureIntro.
            subst. repeat (split; auto). 
            iExists _.
            iSplit; auto.
            iPureIntro.
            subst. repeat (split; auto).
            iExists true. iFrame.
          }
          iFrame.
          iApply "HClose".
          iFrame "Hcss".
          iIntros (_) "Hinv".
          iDestruct "Hinv" as "(Htm1 & _)".
          iDestruct "Hglob" as "(%Hglob & HauthI & Hauthk & Hauthm & Hown_nodes)".
          destruct Hglob as (Hglob & Hr).
          iMod (ghost_insert_map_exist _ x v
                 with "[$Hauthm $Hm']") as "(%Hdom_x & Hauthm & Hm')"; auto.
          { rewrite H19. clear. set_solver. }
          iAssert (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr_p css r)
            with "[$Hnode $Hml_p $Hmin $Hmax $HI Hk Hm']" as "Hmd".
          { rewrite /nr_p /= if_false; auto.
            rewrite ! dom_singleton_L update_singleton H19.
            iFrame "Hk Hm'".
            iPureIntro.
            do 7 (split; auto).
            intros; apply H15; rewrite H19 //. auto.
          }
          destruct H25 as (? & ? & ? & ?).
          destruct H26 as (? & ? & ?).
          simpl.
          iDestruct "HClose" as "(_ & HClose)".
          iApply ("HClose" $! tt).
          rewrite /CSS /CSSi bi.sep_emp.
          iExists I, md, r1.
          iFrame "HauthI Hown_nodes Hown Hidx Hml".
          iSplit; auto.
          iFrame.
          iSplitL "Hauthk".
          iSplit.
          { iPureIntro.
            split; auto; intros Hr1; specialize (Hr Hr1); destruct Hr; split; auto. set_solver.
          }
          assert (dom (<[x:=v]> m) = dom m) as Hdom.
          { rewrite dom_insert_L. clear -Hdom_x. set_solver. }
          rewrite Hdom.
          iFrame "Hauthk".
          setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
          iFrame "Hf Hf1 HinFP1 Hrest".
          iSplit; auto.
          iPureIntro.
          subst. repeat (split; auto).
          iExists nr_p.
          iSplit; auto.
          subst. iPureIntro. repeat (split; auto).
          iExists false.
          rewrite /nr_p /md_entry_rep /= !if_false; auto.
          iFrame.
        }
        forward.
      + try done.
    - rewrite -> (if_false _ (eq_dec new_node nullval)); auto.
      set (AS := atomic_shift _ _ _ _ _).
      Intros.
      forward_if.
      easy.
      assert (size = 16384%Z) as Hsz by (setoid_rewrite (proj2_sig has_size); auto).
      rewrite /= in Hsz.
      forward_call (new_node).
      forward_call (t_md_entry, gv).
      Intros new.
      assert_PROP(is_pointer_or_null new). entailer !.
      rewrite Hsz /= in H24.
      simpl.
      gather_SEP AS (inFP γ_f p p1 l) (malloc_token Ews1 _ new_node).
      assert (f new_node <> 0%Z) as Hne_f_new.
      { intro Hcontra; pose proof f_0 as Hf0; rewrite <- Hf0 in Hcontra;
          apply f_injective in Hcontra; easy.
      }
      (* c->metadata[idx] = surely_malloc(sizeof(md_entry)); *)
      viewshift_SEP 0 (AS ∗ (inFP γ_f p p1 l) ∗
          field_at_ Ews t_struct_css [ArraySubsc (f new_node); StructField _metadata] css).
      { go_lowerx.
        rewrite bi.sep_emp -AS_to_css_metadata_update; auto.
        rewrite Hsz; auto.
      }
      Intros.
      sep_apply data_at_field_compatible.
      Intros.
      forward.
      forward_call (gv).
      Intros lock.
      assert_PROP(is_pointer_or_null lock). entailer !.
      do 2 forward.
      (* Using axiom to obtain it *)
      assert (f nullval ≠ f new_node) as Hne_null_new.
      { intros Hcontra; apply f_injective in Hcontra; auto. }
      (** rename to maintain **)
      rename H8 into Hp_null_r_null. (*p = nullval → r = nullval*)
      rename H9 into Hbelongs. (*p ≠ nullval → belongs x nr*)
      rename H13 into Hnonnull_inset_range. (*p ≠ nullval → ... → in_inset *)
      rename H15 into HCp_dom_keys_range. (*∀ k : Z, k ∈ dom (Cp nr) → (min nr < k < max nr)%Z *)
      rename H18 into Hmap_choice. (* eq_dec new_node nullval -> ... Cp' = Cp nr \/ ... *)
      rewrite /= in Hmap_choice.
      rename H22 into Hnode_dec_key. (* if eq_dec p nullval -> condition in insertOp *)
      rewrite /= in Hnode_dec_key.
      rename H24 into Hnew_bound. (* (0 ≤ f new_node < 16384)%Z *)
      rename H4 into Hx_inset_Ip. (* in_inset _ _ _ x (Ip nr) p *)
      (** END - rename to maintain **)
      
      forward_if.
      do 2 sep_apply node_rep_R_valid_pointer.
      auto with valid_pointer.
      (* clear H17. *)
      (** rename to maintain **)
      rename H4 into Heq_p_nullval. (* p = nullval *)
      (** END - rename to maintain **)
      
      pose Heq_p_nullval as Heq_r_nullval.
      apply Hp_null_r_null in Heq_r_nullval.
      rewrite if_true; auto.
      Intros.
      repeat forward.
      rewrite if_false in Hmap_choice; auto.
      destruct Hmap_choice as [Hmap_choice | Hmap_choice].
      + (* Cp' = Cp nr ∧ C_new = {[x := v]} *)
        destruct Hmap_choice as (HCp & HCnew).
        rewrite if_true in Hnode_dec_key; auto.
        destruct Hnode_dec_key as (Hkey_null & Hx_in_ks_new & HdomCp & HSC_null).
        rewrite /SC_null in HSC_null.
        destruct HSC_null as (Hv & HoutIp & HoutI0 & HoutI_new & HdomIp & HdomI0 & HdomI_new &
                        HdomKS & Hks & Hks_disj).
        unfold_data_at (data_at _ _ _ new).
        set (nr_p := {| min := (min nr); max := (max nr); Cp := Cp'; Ip := I0; |}).
        set (nr1 := {| min := (min nr); max := (max nr); Cp := (Cp nr); Ip := I0; |}).
        set Q1 := fun (v : val ) => AS.
        gather_SEP AS.
        rewrite Heq_p_nullval.
        forward_call (css, nullval, p1, l, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, gv, Q1).
        { rewrite /rev_curry /=. apply bi.sep_mono; [|cancel]. by iApply AS_to_AS. }
        subst; try done.
        Intros lk lsh.
        rewrite H4 -Heq_p_nullval.
        forward.
        (* push back lock into invariant *)
        rewrite /Q1.
        gather_SEP AS (inFP γ_f p p1 l) (field_at (cs := CompSpecs) lsh _ _ _ p1).
        viewshift_SEP 0 (AS ∗ (inFP γ_f p p1 l)).
        { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
        (* end - push back lock into invariant *)
        Intros.
        forward_call (lock, inFP γ_f p p1 l ∗
         atomic_shift (λ _ : (), atomic_int_at Ews (vint 1) l) (⊤ ∖ ∅) ∅
            (λ _ _ : (), atomic_int_at Ews (vint 0) l ∗ emp) (λ _ : (), Q)).
        { rewrite /rev_curry /Q1 /=.
          iIntros "(AS & #HinFP & Hgv & Htm & Hf_new & Hmin_new & Hmax_new & Hf1 & Hml &
                   Hn_new & Hn & Hml_p & Hmin & Hmax & HI & Hk & Hm & Hownr & Hf_css)".
          iCombine "Hn_new Hmin_new Hmax_new Hf_css Hownr Hml" as "Hmd_new".
          iCombine "AS Htm Hf_new HinFP Hmin Hmax Hn HI Hk Hm Hf1 Hml_p" as "Hmd_p".
          iCombine "Hgv" as "Hframe".
          iStopProof.
          do 2 (rewrite assoc); apply bi.sep_mono; [|cancel].
          iIntros "(Hmd_new & Hmd_p)".
          unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
          iDestruct "Hmd_p" as "(HAS & Htm & Hl_new & #HinFP & Hmin &
                   Hmax & Hn_p & HI & Hk & Hm & Hf_css & Hml_p)".
          iDestruct "Hmd_new" as "(_ & Hn_new & Hmin_new &
                             Hmax_new & Hf_css_new & Hownr & Hml_new)".
          iMod "HAS" as (m) "[Hcss HClose]".
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
          iIntros (tt) "(Htm & _)".
          iDestruct "HClose" as "(HClose & _)".
          iSpecialize ("HClose" with "Hcss").
          iMod ("HClose").
          rewrite Heq_p_nullval.
          iFrame "HinFP".
          rewrite <- Heq_p_nullval.
          iModIntro.
          unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
          clear dependent m.
          iMod "HClose" as (m) "[Hcss HClose]".
          iExists ().
          iModIntro.
          (*prove atomic_int_at *)
          iDestruct "Hcss" as (I md r') "Hcssi".
          iDestruct "Hcssi" as "(%Hznth & Hglob & Hml & Hidx & HNF & Hownr')".
          destruct Hznth as (Hznth & Hnull_in_domI).
          assert ((0 ≤ f nullval < Zlength md)%Z) as Hfnull.
          { rewrite Heq_p_nullval in H3. by rewrite Hznth. }
          assert ((0 ≤ f new_node < Zlength md)%Z) as Hfnew_bound_md.
          { rewrite -Hsz in Hnew_bound. by rewrite Hznth. }
          (* new_node ∉ dom I *)
          iDestruct (new_node_fresh with "[$Htm $Hl_new $Hf_css $HNF]")
            as %Hnew_notin_domI; auto.
          setoid_rewrite (big_opS_delete _ _ nullval) at 1; auto.
          iDestruct "HNF" as "(HNF & Hrest)".
          iDestruct "HNF" as (q qsh) "(% & Hf & Hlt)".
          rewrite {1} /ltree.
          iDestruct "Hlt" as (lsh1 lk1 nr1') "(% & Hf1 & HinFP1 & Hinv)".
          iAssert (⌜q = p1 /\ lk1 = l⌝) with "[HinFP HinFP1]" as "%Hpk".
          { subst. iDestruct (in_FP_equiv _ nullval q p1 with "[$HinFP $HinFP1]") as "?"; auto. }
          destruct Hpk as (Hpt & Hlk).
          rewrite Hpt Hlk.
          iDestruct "Hinv" as (b) "(Htm1 & Hmd1)".
          destruct b.
          2 : {
            iDestruct "Hmd1" as "(? & Hml1 & ?)".
            iPoseProof (malloc_token_conflict with "[$Hml1 $Hml_p]") as "HF"; simpl; eauto. lia.
          }
          iFrame "Htm1".
          iSplit.
          iIntros "Htm1".
          iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css) with
            "[$Hglob $Hml $Hidx $Hownr' Hf Hf1 HinFP1 Htm1 Hmd1 Hrest]" as "Hcss".
          { iSplit; auto.
            setoid_rewrite (big_opS_delete _ _ nullval) at 2; auto.
            iFrame.
            iSplit; auto.
            iPureIntro.
            subst; auto.
            iExists nr.
            iSplit; auto. subst. auto.
            iExists true. iFrame.
          }
          iSpecialize ("HClose" with "Hcss").
          by iFrame.
          iIntros (_) "Hinv".
          iDestruct "Hinv" as "(Htm1 & _)".
          iDestruct (own_valid_2 γ_n (●E r' : excl_authR (leibnizO val)) (◯E r)
                      with "[$Hownr'] [$Hownr]") as %Hownr%@excl_auth_agree_L.
          rewrite Heq_r_nullval in Hownr; rewrite Hownr.
          iDestruct "Hglob" as "(%Hglob & HownI & Hownk & Hownm & Hown_nodes)".
          assert (x ∈ keyset Node_EqDecision Node_countable Key (Ip nr) p) as Hx_in_keyset.
          { rewrite /keyset /outsets HoutIp big_opS_empty difference_empty_L; done. }
          (* x ∉ dom m *)
          iDestruct (key_new_node_fresh _ _ x with "[$Hownk $Hk]") as %Hx_notin_dom_m; auto.
          (* ghost_insert_keyset' *)
          iMod (ghost_insert_keyset_add_node _ _ p new_node x v m (Cp nr) (Ip nr) I_new I0
            with "[$Hownk $Hownm $Hk $Hm]")
            as "(Hownk & HkI0 & HkI_new & Hownm & HmI0 & HmI_new)"; try done.
          { iPureIntro. repeat split; try done; rewrite Heq_p_nullval; done. }
          destruct Hglob as (Hglob & HdomI).
          specialize (HdomI eq_refl).
          destruct HdomI as (HdomI_null & Hmap).
          (* Prove Ip = I *)
          iDestruct (flowEq γ_I I (Ip nr) with "[$HownI $HI]") as %HI.
          { iPureIntro. rewrite HdomI_null HdomIp; try done. }
          (* update flow interfaces *)
          iMod (ghost_update_interface_nullval _ _ r' I (Ip nr) I0 I_new new_node new lock
                 with "[$HownI $Hown_nodes $HI]") as "Hflow"; try done.
          { iPureIntro. subst p r'. repeat (split; auto). }
          iDestruct "Hflow" as (I1 md1) "(%Hctx & HI & HI1 & HI2 & Hown1 & #HinFP_new)".
          destruct Hctx as (Hctx & Hglobinv).
          assert (nullval ∈ dom I1) as Hnull_in_domI1.
          { destruct Hglobinv as (HdomI1 & ?). rewrite HdomI1. clear -HdomI_null. set_solver. }
          iDestruct "HClose" as "(_ & HClose)".
          rewrite Heq_r_nullval.
          iMod (own_update_2 γ_n (●E nullval : excl_authR (leibnizO val)) (◯E nullval)
                  ((●E new_node) ⋅ (◯E new_node)) with "[$Hownr'] [$Hownr]") as "Hownr".
          { apply (excl_auth_update nullval). }
          rewrite own_op.
          iDestruct "Hownr" as "(Hna & Hnf)".
          iAssert (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr_p css new_node)
            with "[$Hmin $Hmax HmI0 $Hn_p $HI1 HkI0 Hf_css_new Hnf $Hml_p]" as "Hmd".
          { rewrite /md_entry_rep /nr_p /flowint_dom /= HCp if_true; try done.
            iFrame.
            repeat (split; intuition; [auto | ]); intros; subst p; try done.
          }
          iAssert (nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css new_node) with
            "[Hrest Hmd Htm1 Hf HinFP1 Hf1]" as "HNF".
          { setoid_rewrite (big_opS_delete _ _ nullval) at 2; auto.
            rewrite {2} /ltree.
            iFrame.
            iSplitL "Htm1 Hmd".
            iSplit; auto.
            iPureIntro. subst; auto.
            iExists nr_p.
            iSplit. subst; auto.
            iExists false. subst.
            iFrame "Htm1 Hmd".
            iApply (big_sepS_mono with "[$Hrest]").
            intros.
            iIntros "H".
            iDestruct "H" as (? ?) "(%Hc & H1 & H2)".
            iFrame "H1".
            iExists p0.
            assert (x0 <> nullval).
            { clear -H18. set_solver. }
            iDestruct (ltree_imply with "[$H2]") as "?"; auto.
          } 
          iApply ("HClose" $! tt).
          rewrite bi.sep_emp.
          iExists I1, md1, new_node.
          iFrame.
          rewrite /nodeFull.
          setoid_rewrite (big_opS_delete _ _ new_node) at 2.
          destruct Hglobinv as (HdomI1 & HdomI1' & Hmd1).
          rewrite HdomI1' Hmd1 !upd_Znth_same; auto.
          repeat iSplit; try done. { by rewrite Zlength_upd_Znth. }
          iAssert (ltree γ_I γ_k γ_f γ_m γ_n new new_node css new_node)
            with "[Hl_new Htm Hmin_new Hmax_new Hn_new HI2 HmI_new Hml_new HkI_new]"
            as "Hltree"; try done.
          { set (nr_new := {| min := Int.min_signed; max := Int.max_signed;
                              Cp := C_new; Ip := I_new; |}).
            rewrite /ltree.
            iExists _, _, nr_new.
            iFrame "Hl_new HinFP_new".
            iSplit; auto.
            iExists false.
            iFrame "Htm ∗".
            rewrite /md_entry_rep /nr_new HCnew dom_singleton_L /=.
            assert (Vint (Int.sub (Int.neg (Int.repr 2147483647)) (Int.repr 1)) =
                      vint Int.min_signed) as ->; auto; try by autorewrite with norm.
            iFrame "∗".
            rewrite if_false; auto.
            iSplit; try done.
            { iPureIntro.
              do 5 (split; auto).
              intros ? k ?.
              rewrite /key_property_null in Hkey_null.
              apply Hkey_null, signed_bounds_axiom_KS; auto.
              split; auto.
              intros k ?%elem_of_singleton_1; subst. done.
            }
          }
          iSplitL "Hltree Hf_css".
          { iFrame; iPureIntro; rewrite Zlength_upd_Znth; split; auto. }
          rewrite HdomI_null ! big_opS_singleton.
          iDestruct "HNF" as (q1 lsh2) "(%Hc & Hf & Hlt)".
          iFrame "Hlt ∗".
          iExists lsh2.
          iSplit; try done.
          { iPureIntro.
            destruct Hc as (? & ? & ? & ?).
            rewrite Heq_p_nullval in H3.
            rewrite Zlength_upd_Znth upd_Znth_diff; auto.
          }
          rewrite upd_Znth_diff; auto.
          destruct Hglobinv as (HdomI1 & ? & ?).
          rewrite HdomI1. clear. set_solver.
       }
       simpl.
       Intros.
       (*release (md->lock);*)
       forward_call (l, Q).
       { rewrite /rev_curry /= /Q1.
         iIntros "(HAU & HinFP & Hgv)".
         iCombine "HAU HinFP" as "?".
         iCombine "Hgv" as "?".
         iStopProof.
         apply bi.sep_mono; [|cancel].
         iIntros "(AU & HinFP)".
         iFrame.
       }
       forward.
      + (* contradiction for C <> empty *)
        rewrite Heq_p_nullval.
        gather_SEP (node nullval I0 Cp').
        sep_apply node_nullval_empty; auto. 
        Intros.
        rewrite H4 in Hmap_choice.
        destruct Hmap_choice as (HCp & ?); try done.
      + (* clear H17. *)
        rename H4 into Hp_non_null. (* p ≠ nullval *)
        rewrite if_false in Hmap_choice; auto.
        rewrite if_false in Hnode_dec_key; auto.
        rewrite if_false; auto.
        set Q1:= fun (v : val ) => AS.
        destruct Hmap_choice as [HCp | HCp].
        ++ rewrite if_true in Hnode_dec_key; last first.
           { destruct HCp as (HCp & ?). clear -HCp. set_solver. }
           destruct Hnode_dec_key as
             ((Hkey_property1 & Hx_in_ks_new & HdomCp) &
                (HinfI0Ip & HcxtLeq & Hinf & Hk_union & Hk_disj)).
          forward_call (css, p, p1, l, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, gv, Q1).
          { rewrite /rev_curry bi.sep_emp /Q1 /=.
            iIntros "(Hgv & Htm & Hnew & AS & Hf1 & Hml & Hn_new & Hn &
                          Hmin & Hmax & HI & Hk & Hm)".
            iCombine "AS Hgv Htm Hnew Hf1 Hml Hn_new Hn Hmin Hmax HI Hk Hm" as "Hmd".
            iStopProof.
            apply bi.sep_mono; [|cancel]; by iApply AS_to_AS.
          }
          split; auto.
          Intros q1 lsh.
          subst q1.
          (*lock_t lockp = md->lock;*)
          forward.
          (* push back lock into invariant *)
          rewrite /Q1.
          gather_SEP AS (inFP γ_f p p1 l) (field_at (cs := CompSpecs) lsh _ _ _ p1).
          viewshift_SEP 0 (AS ∗ (inFP γ_f p p1 l)).
          { go_lowerx. by rewrite bi.sep_emp push_lock_back. }
          (* end *)
          (* int key = get_key(p); *)
          forward_call (p, I0, Cp', gv).
          Intros key.
          forward_if.
        * repeat forward.
          set (nr_p := {| min := (min nr); max := (max nr); Cp := Cp'; Ip := I0; |}).
          unfold_data_at (data_at _ _ _ new).
          rename H18 into Hlt_x_key. (* (x < key)%Z *)
          rename H4 into HdomCp'_key. (* dom Cp' = {[key]} *)
          forward_call (lock, inFP γ_f p p1 l ∗
               atomic_shift (λ _ : (), atomic_int_at Ews (vint 1) l) (⊤ ∖ ∅) ∅
                     (λ _ _ : (), atomic_int_at Ews (vint 0) l ∗ emp) (λ _ : (), Q)).
            { rewrite /rev_curry /=.
              iIntros "(Hn & AS & #HinFP & Hgv & Htm & Hf_new & Hmin_new & Hmax_new &
                 Hf_css & Hml_new & Hn_new & Hml_p & Hmin & Hmax & HI & Hk & Hm)".
              iCombine "Hn_new Hmin_new Hmax_new Hf_css Hml_new" as "Hmd_new".
              iCombine "AS Htm Hf_new HinFP Hmin Hmax Hn HI Hk Hm Hml_p" as "Hmd_p".
              iCombine "Hgv" as "Hframe".
              iStopProof.
              do 2 (rewrite assoc); apply bi.sep_mono; [|cancel].
              (* reduce proof using insertOp_helper_gain_md_entry_rep *)
              eapply insertOp_helper_gain_md_entry_rep; eauto.
              rewrite /cxtLeq; eauto.
            }
            simpl.
            Intros.
            (*release (md->lock);*)
            forward_call (l, Q).
            { rewrite /rev_curry /= /Q1.
              iIntros "(HAU & HinFP & Hgv)".
              iCombine "HAU HinFP" as "?".
              iCombine "Hgv" as "?".
              iStopProof.
              apply bi.sep_mono; [|cancel].
              iIntros "(AU & HinFP)".
              iFrame.
            }
            go_lowerx; auto.
        * rename H15 into Hge_x_key. (* (x >= key)%Z *)
          rename H4 into HdomCp'_key. (* dom Cp' = {[key]} *)
          assert (x <> key) as Hneq by (intros Heq; destruct HCp as (HCp' & ?);
            subst; rewrite HdomCp'_key in H19; apply not_elem_of_singleton in H19; done).
          assert ((x > key)%Z) as Hgt_x_key by lia.
          (* similar to x < key *)
          repeat forward.
          set (nr_p := {| min := (min nr); max := (max nr); Cp := Cp'; Ip := I0; |}).
          unfold_data_at (data_at _ _ _ new).
          forward_call (lock, inFP γ_f p p1 l ∗
                                atomic_shift (λ _ : (), atomic_int_at Ews (vint 1) l) (⊤ ∖ ∅) ∅
                                (λ _ _ : (), atomic_int_at Ews (vint 0) l ∗ emp) (λ _ : (), Q)).
          { rewrite /rev_curry /Q1 /=.
            iIntros "(Hn & AS & #HinFP & Hgv & Htm & Hf_new & Hmin_new & Hmax_new &
                 Hf_css & Hml_new & Hn_new & Hml_p & Hmin & Hmax & HI & Hk & Hm)".
            iCombine "Hn_new Hmin_new Hmax_new Hf_css Hml_new" as "Hmd_new".
            iCombine "AS Htm Hf_new HinFP Hmin Hmax Hn HI Hk Hm Hml_p" as "Hmd_p".
            iCombine "Hgv" as "Hframe".
            iStopProof.
            do 2 (rewrite assoc); apply bi.sep_mono; [|cancel].
            (* reduce proof 200 line code using insertOp_helper_gain_md_entry_rep *)
            eapply insertOp_helper_gain_md_entry_rep; eauto.
            rewrite /cxtLeq; eauto.
          }
          simpl.
          Intros.
          (*release (md->lock);*)
          forward_call (l, Q).
          { rewrite /rev_curry /= /Q1.
            iIntros "(HAU & HinFP & Hgv)".
            iCombine "HAU HinFP" as "?".
            iCombine "Hgv" as "?".
            iStopProof.
            apply bi.sep_mono; [|cancel].
            iIntros "(AU & HinFP)".
            iFrame.
          }
          go_lowerx; auto.
       ++ (* Cp' = {[x := v]} ∧ C_new = Cp nr *)
          rewrite if_false in Hnode_dec_key; last first.
          { destruct HCp as (HCp & ?); subst. clear - H19. set_solver. }
          destruct Hnode_dec_key as ((Hkey_property2 & Hx_in_ks_p & HdomCp) &
                                         (HinfI0Ip & HcxtLeq & Hinf & Hk_union & Hk_disj)).
          forward_call (css, p, p1, l, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, gv, Q1).
          { rewrite /rev_curry bi.sep_emp /Q1 /=.
            iIntros "(Hgv & Htm & Hnew & AS & Hf1 & Hml & Hn_new & Hn &
                          Hmin & Hmax & HI & Hk & Hm)".
            iCombine "AS Hgv Htm Hnew Hf1 Hml Hn_new Hn Hmin Hmax HI Hk Hm" as "Hmd".
            iStopProof. apply bi.sep_mono; [|cancel]. by iApply AS_to_AS.
          }
          simpl.
          split; auto.
          Intros q1 lsh. subst q1.
          forward.
          (* push back lock into invariant *)
          rewrite /Q1.
          gather_SEP AS (inFP γ_f p p1 l) (field_at (cs := CompSpecs) lsh _ _ _ p1).
          viewshift_SEP 0 (AS ∗ (inFP γ_f p p1 l)).
          { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
          (* end - push back lock into invariant *)
          forward_call (p, I0, Cp', gv).
          Intros key.
          rename H4 into HdomCp'_key. (* dom Cp' = {[key]} *)
          forward_if.
          rename H4 into Hlt_x_key. (* (x < key)%Z *)
          * (* x < key, prove using contradiction *)
            exfalso.
            destruct HCp as (HCp' & HCnew); subst.
            rewrite dom_singleton_L in HdomCp'_key.
            assert (x = key) as Hkey; try lia.
            { clear -HdomCp'_key. set_solver. }
          * (* prove only x = key works in this case *)
            assert ((x = key)%Z) as Heq_x_key.
            { destruct HCp as (HCp' & HC_new); subst.
              rewrite dom_singleton_L in HdomCp'_key.
              clear - HdomCp'_key. set_solver.
            }
            (* key = x *)
            repeat forward.
            set (nr_p := {| min := (min nr); max := (max nr); Cp := Cp'; Ip := I0;|}).
            unfold_data_at (data_at _ _ _ new).
            rewrite /Q1.
            forward_call (lock, inFP γ_f p p1 l ∗
               atomic_shift (λ _ : (), atomic_int_at Ews (vint 1) l) (⊤ ∖ ∅) ∅
                     (λ _ _ : (), atomic_int_at Ews (vint 0) l ∗ emp) (λ _ : (), Q)).
            { rewrite /rev_curry /Q1 /=.
              iIntros "(Hn & AS & #HinFP & Hgv & Htm & Hf_new & Hmin_new & Hmax_new &
                 Hf_css & Hml_new & Hn_new & Hml_p & Hmin & Hmax & HI & Hk & Hm)".
              iCombine "Hn_new Hmin_new Hmax_new Hf_css Hml_new" as "Hmd_new".
              iCombine "AS Htm Hf_new HinFP Hmin Hmax Hn HI Hk Hm Hml_p" as "Hmd_p".
              iCombine "Hgv" as "Hframe".
              iStopProof.
              do 2 (rewrite assoc); apply bi.sep_mono; [|cancel].
              iIntros "(Hmd_new & Hmd_p)".
              unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
              iDestruct "Hmd_p" as "(HAS & Htm & Hl_new & #HinFP & Hmin &
                   Hmax & Hn_p & HI & Hk & Hm & Hml_p)".
              iDestruct "Hmd_new" as "(_ & Hn_new & Hmin_new & Hmax_new & Hf_css_new & Hml_new)".
              iMod "HAS" as (m) "[Hcss HClose]".
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
              iIntros (tt) "(Htm & _)".
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
                { clear -H14. set_solver. }
                iPureIntro.
                rewrite I_incl in Valid_I.
                rewrite I_incl.
                rewrite intComp_dom; auto.
                clear -Hdomp. set_solver.
              }
              destruct Hznth as (Hznth & Hnull_in_domI).
              assert ((0 ≤ f new_node < Zlength md)%Z) as Hfnew_bound_md.
              { rewrite -Hsz in Hnew_bound. by rewrite Hznth. }
              (* new_node ∉ dom I *)
              iDestruct (new_node_fresh with "[$Htm $Hl_new $Hf_css_new $HNF]")
                as %Hnew_notin_domI; auto.
              setoid_rewrite (big_opS_delete _ _ p) at 1; auto.
              iDestruct "HNF" as "(HNF & Hrest)".
              iDestruct "HNF" as (q qsh) "(% & Hf & Hlt)".
              rewrite {1} /ltree.
              iDestruct "Hlt" as (lsh1 lk1 nr1') "(% & Hf1 & HinFP1 & Hinv)".
              iAssert (⌜q = p1 /\ lk1 = l⌝) with "[HinFP HinFP1]" as "%Hpk".
              { subst; by iDestruct (in_FP_equiv _ p q p1 lk1 l with "[$HinFP $HinFP1]") as "?". }
              destruct Hpk as (Hpt & Hlk).
              rewrite Hpt Hlk.
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
                iExists true. iFrame.
              }
              iSpecialize ("HClose" with "Hcss").
              by iFrame.
              iIntros (_) "Hinv".
              iDestruct "Hinv" as "(Htm1 & _)".
              iDestruct "Hglob" as "(%Hglob & HownI & Hownk & Hownm & Hown_nodes)".
              assert (x ∈ keyset Node_EqDecision Node_countable Key (Ip nr) p) as Hx_in_keyset.
              { destruct HcxtLeq as (? & ? & ? & ?). rewrite -Hk_union. set_solver. }
              (* x ∉ dom m *)
              iDestruct (key_new_node_fresh _ _ x with "[$Hownk $Hk]") as %Hx_notin_dom_m; auto.
              (* ghost_insert_keyset in between - special case for linked list *)
              iMod (ghost_insert_keyset_add_node_between _ _
                      p new_node x v m (Cp nr) (Ip nr) I_new I0
                     with "[$Hownk $Hownm $Hk $Hm]")
                as "(Hownk & HkI0 & HkI_new & Hownm & HmI0 & HmI_new)"; auto.
              Unshelve. 2 : { done. }
              destruct Hglob as (Hglob & HdomI).
              iMod (ghost_update_interface _ _ r' I (Ip nr) I0 I_new p new_node new lock
                     with "[$HownI $Hown_nodes $HI]") as "Hflow"; auto.
              { (split; auto). rewrite Hznth; auto. }
              iDestruct "Hflow" as (I1 md1) "(%Hctx & HI & HI1 & HI2 & Hown1 & #HinFP_new)".
              destruct Hctx as (Hctx & Hglobinv).
              assert (nullval ∈ dom I1) as Hnull_in_domI1.
              { destruct Hglobinv as (? & HdomI1 & ?).
                rewrite HdomI1. clear -Hnull_in_domI. set_solver.
              }
              rewrite / key_property2 in Hkey_property2.
              destruct Hkey_property2 as (? & ? & Hdom & Hdom' & Heq).
              iDestruct "HClose" as "(_ & HClose)".
              iAssert (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr_p css r)
                with "[$Hmin $Hmax HmI_new $Hn_p $HI1 HkI0 $Hml_p]" as "Hmd".
              { destruct HCp as (HCp' & HCnew).
                rewrite /md_entry_rep /nr_p HCp' /=.
                rewrite -> if_false; auto.
                rewrite dom_singleton_L.
                iFrame "∗".
                specialize (Hbelongs Hp_non_null); rewrite /belongs_t /= /belongs in Hbelongs.
                iPureIntro.
                repeat (split; auto).
                by rewrite /in_inset /inf HinfI0Ip.
                apply elem_of_singleton_1 in H24; subst k; try lia.
                apply elem_of_singleton_1 in H24; subst k; try lia.
              }
              iAssert (nodeFull γ_I γ_k γ_f γ_m γ_n (dom I) md css r')
                with "[Hrest Hmd Hf HinFP1 Hf1 Htm1]" as "HNF".
              { setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
                rewrite {2} /ltree.
                iFrame.
                iSplit; auto.
                iPureIntro. subst. auto.
                iExists nr_p.
                iSplit. subst. auto.
                iExists false. subst.
                iFrame "Htm1".
                rewrite /md_entry_rep !if_false; auto.
              }
              iApply ("HClose" $! tt).
              rewrite bi.sep_emp /CSS.
              iExists I1 , md1, r'.
              iFrame.
              setoid_rewrite (big_opS_delete _ _ new_node) at 2.
              destruct Hglobinv as (Hglob1 & HdomI1 & HdomI1' & Hmd1 & Hdomp).
              rewrite HdomI1' Hmd1 /nodeFull !upd_Znth_same.
              iSplit; auto.
              { by rewrite Zlength_upd_Znth. }
              iSplit; auto.
              iPureIntro.
              { do 2 split; auto.
                intros Hr'.
                specialize (HdomI Hr').
                destruct HdomI as (HdomI & ?).
                rewrite HdomI in Hdomp.
                apply elem_of_singleton_1 in Hdomp. try done.
              }
              iAssert (ltree γ_I γ_k γ_f γ_m γ_n new new_node css r')
               with "[Hl_new Htm Hmin_new Hmax_new Hn_new HI2 HkI_new Hml_new HmI0]" as "Hltree".
              { rewrite /ltree.
                set (nr_new := {| min := Int.signed (Int.repr key) ;
                                    max := (max nr) ; Cp := C_new; Ip := I_new;|}).
                iExists _, _, nr_new.
                iFrame "Hl_new HinFP_new".
                iSplit; auto.
                iExists false. iFrame "Htm".
                rewrite /md_entry_rep /nr_new /=.
                destruct HCp as (HCp' & HCnew).
                rewrite HCnew.
                assert (vint (Int.signed (Int.repr key)) = vint key) as ->; auto.
                { rewrite Int.signed_repr; auto. lia. }
                assert (Int.signed (Int.repr key) = key) as Hkey_int.
                { rewrite Int.signed_repr; auto. lia. }
                iFrame.
                rewrite if_false; auto.
                destruct Heq as (Hx0x1_ge & Heq).
                specialize (Hbelongs Hp_non_null).
                rewrite /belongs_t /= /belongs in Hbelongs.
                subst.
                assert (x1 = key) as Hx1_key_eq.
                { rewrite dom_singleton_L in Hdom. clear -Hdom. set_solver. }
                iPureIntro.
                repeat (split; auto; try lia).
                intros _ ? Hk1.
                subst.
                assert ((k > key)%Z) as Hk_key_lt. lia.
                apply Heq; auto.
                split; try apply Hnonnull_inset_range; try lia; try done.
                assert (k = x0) as Hkx0_eq.
                { rewrite Hdom' in H24. clear -H24. set_solver. }
                subst. lia.
                specialize (HCp_dom_keys_range k).
                apply HCp_dom_keys_range in H24. lia.
              }
              iSplitL "Hltree Hf_css_new".
              { iFrame "Hltree Hf_css_new".
                iPureIntro. rewrite Zlength_upd_Znth; try do 2 (split; auto).
              }
              iApply (big_sepS_mono with "[$HNF]").
              intros.
              iIntros "H".
              iDestruct "H" as (? ?) "(%Hc & H1 & H2)".
              iFrame "H2".
              rewrite Zlength_upd_Znth upd_Znth_diff; auto; try by destruct Hc.
              intros Hcontra.
              apply f_injective in Hcontra. set_solver. auto.
              destruct Hglobinv as (? & HdomI1 & ? & ?).
              rewrite HdomI1; clear. set_solver.
           }
           simpl.
           (*release (md->lock);*)
           forward_call (l, Q).
           { rewrite /rev_curry /=.
             iIntros "(HAU & HinFP)".
             iStopProof.
             apply bi.sep_mono; [|cancel].
             iIntros "(AU & HinFP)".
             iFrame.
           }
           go_lowerx; auto.
  Qed.

  (* lookupOp_helper proof *)
  Lemma lookupOp_helper: semax_body Vprog Gprog f_lookupOp_helper lookupOp_helper_spec.
  Proof.
    start_function.
    forward.
    rewrite /md_entry_rep_t /=.
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
              SEP (AS; mem_mgr gv; inFP γ_f p p1 l; md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r)).
    - destruct status; try discriminate.
      rewrite /md_entry_rep.
      Intros.
      + destruct H11 as (Hne_p_null & Hdom).
        forward_call (x, p, (Ip nr), (Cp nr), gv).
        Intros ret.
        rewrite -> if_false; auto.
        assert (x ∈ dom (Cp nr)) as Hdomx.
        { clear -H11. set_solver. }
        assert (Hex : ∃ v, Cp nr !! x = Some v).
        { by rewrite elem_of_dom /is_Some in Hdomx. }
        destruct Hex as [v' Hlookup].
        forward.
        entailer !.
        rewrite /md_entry_rep if_false; auto.
        entailer !.
    - forward. destruct status; try entailer !.
    - set Q1:= fun (v : val ) => AS.
      destruct status.
      + (* FOUND *)
        destruct H11 as (Hne_p_null & Hdom).
        assert (x ∈ dom (Cp nr)) as Hdomx.
        { clear -Hdom. set_solver. }
        assert (Hex : ∃ v, Cp nr !! x = Some v).
        { apply elem_of_dom in Hdomx. rewrite /is_Some in Hdomx. done. }
        destruct Hex as [v' Hlookup].
        rewrite Hlookup.
        Intros.
        forward_call (css, p, p1, l, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, gv, Q1).
        { rewrite /rev_curry /=. apply bi.sep_mono; [|cancel]. by iApply AS_to_AS. }
        simpl.
        subst; try done.
        Intros lk lsh.
        rewrite H11 /Q1.
        forward.
        (* push back lock into invariant *)
        gather_SEP AS (inFP γ_f p p1 l) (field_at (cs := CompSpecs) lsh _ _ _ p1).
        viewshift_SEP 0 (AS ∗ (inFP γ_f p p1 l)).
        { go_lowerx. by rewrite bi.sep_emp push_lock_back. }
        (* end - push back lock into invariant *)
        Intros.
        forward_call (l, Q v').
        { rewrite /rev_curry /=.
          iIntros "(AU & HinFP & Hgv & Hmd)".
          iCombine "AU HinFP Hmd" as "Hmd".
          iCombine "Hgv" as "Hframe".
          iStopProof.
          apply bi.sep_mono; [|cancel].
          iIntros "(AU & #HinFP & Hmd)".
          unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
          iMod "AU" as (m) "(Hm & HClose)".
          iDestruct "Hm" as (I md r1) "(%Hc & Hglob & Hml & Hidx & HNF & Hown)".
          rewrite {1} /md_entry_rep.
          iDestruct "Hmd" as "(%Hc1 & Hl & Hmin & Hmax & 
                    Hn_p & HI & Hk & Hm & Hrst)".
          destruct Hc1 as (? & ? & ? & ? & HdomIp).
          simpl.
          iModIntro.
          iExists tt.
          iAssert (⌜p ∈ dom I⌝) with "[Hglob HI]" as "%HpInDom".
          { iDestruct "Hglob" as "(%Hglob & HauthI & Hauthk & Hauthm & Hown_nodes)".
            destruct Hglob as (Hglob & Hr).
            iDestruct (own_valid_2 with "[$HauthI] [$HI]") as "%HvIp".
            apply auth_both_valid_discrete in HvIp.
            destruct HvIp as ([Io I_incl] & Valid_I).
            assert (p ∈ dom (Ip nr)) as Hdomp.
            { clear -HdomIp. set_solver. }
            iPureIntro.
            rewrite I_incl in Valid_I.
            rewrite I_incl intComp_dom; auto.
            clear -Hdomp. set_solver.
          }
          setoid_rewrite (big_opS_delete _ _ p) at 1; auto.
          iDestruct "HNF" as "(HNF & Hrest)".
          iDestruct "HNF" as (q qsh) "(% & Hf & Hlt)".
          rewrite {1} /ltree.
          iDestruct "Hlt" as (lsh1 lk1 nr1') "(% & Hf1 & HinFP1 & Hinv)".
          iAssert (⌜q = p1 /\ lk1 = l⌝) with "[HinFP HinFP1]" as "%Hpk".
          { by iDestruct (in_FP_equiv _ p q p1 lk1 l with "[$HinFP $HinFP1]") as "?". }
          destruct Hpk as (Hpt & Hlk).
          rewrite Hpt Hlk.
          iDestruct "Hinv" as (b) "(Htm1 & Hmd1)".
          destruct b.
          2 :{ 
            iDestruct "Hmd1" as "(? & Hml1 & ?)".
            iPoseProof (malloc_token_conflict with "[$Hml1 $Hl]") as "HF"; simpl; eauto. lia.
          }
          iFrame "Htm1".
          iSplit.
          iIntros "Htm1".
          iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css) with
            "[$Hglob $Hml $Hidx Hf Hf1 HinFP1 Htm1 Hrest Hown ]" as "Hcss".
          { iSplit; auto.
            setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
            iFrame.
            iSplit; subst; auto.
            iExists nr.
            iSplit; subst; auto.
            iExists true. iFrame.
          }
          iDestruct "HClose" as "(HClose & _)".
          iFrame.
          iSpecialize ("HClose" with "Hcss").
          iMod ("HClose").
          iFrame.
          iPureIntro.
          subst. repeat (split; auto).
          iIntros (_) "Hinv".
          iDestruct "Hinv" as "(Htm1 & _)".
          iDestruct "Hglob" as "(%Hglob & HauthI & Hauthk & Hauthm & Hown_nodes)".
          destruct Hglob as (Hglob & Hr).
          rewrite -> (if_false _ (eq_dec p nullval)); auto.
          iDestruct "HClose" as "(_ & HClose)".
          iApply "HClose".
          iSplit; auto.
          iSplit.
          (* prove m !! x = v' *)
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
          rewrite option_included in Hsub.
          destruct Hsub as [Hcontra | (? & ? & ? & Hcontra & ?)]; try easy.
          iFrame.
          setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
          iFrame.
          do 3 (iSplit; subst; auto).
          iExists nr.
          iSplit; auto.
          iExists false.
          iFrame.
          rewrite -> if_false; auto.
        }
        simpl.
        forward.
        Exists v'. auto.
      + (* NOTFOUND *)
        destruct H11 as (Hne_p_null & Hne_dom).
        Intros.
        forward_call (css, p, p1, l, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, gv, Q1).
        { rewrite /rev_curry /=. apply bi.sep_mono; [|cancel]. by iApply AS_to_AS. }
        simpl.
        subst; try done.
        Intros lk lsh.
        rewrite H11.
        forward.
        (* push back lock into invariant *)
        rewrite /Q1.
        gather_SEP AS (inFP γ_f p p1 l) (field_at (cs := CompSpecs) lsh _ _ _ p1).
        viewshift_SEP 0 (AS ∗ (inFP γ_f p p1 l)).
        { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
        (* end - push back lock into invariant *)
        Intros.
        forward_call (l, Q nullval).
        { rewrite /rev_curry /=.
          iIntros "(AU & HinFP & Hgv & Hmd)".
          iCombine "AU HinFP Hmd" as "Hmd".
          iCombine "Hgv" as "Hframe".
          iStopProof.
          apply bi.sep_mono; [|cancel].
          iIntros "(AU & #HinFP & Hmd)".
          unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
          iMod "AU" as (m) "(Hm & HClose)".
          iDestruct "Hm" as (I md r1) "(%Hc & Hglob & Hml & Hidx & HNF & Hown)".
          rewrite {1} /md_entry_rep.
          iDestruct "Hmd" as "(%Hc1 & Hl & Hmin & Hmax &
                    Hn_p & HI & Hk & Hm & Hrst)".
          destruct Hc1 as (? & ? & ? & ? & HdomIp).
          simpl.
          iModIntro.
          iExists tt.
          iAssert (⌜p ∈ dom I⌝) with "[Hglob HI]" as "%HpInDom".
          { iDestruct "Hglob" as "(%Hglob & HauthI & Hauthk & Hauthm & Hown_nodes)".
            destruct Hglob as (Hglob & Hr).
            iDestruct (own_valid_2 with "[$HauthI] [$HI]") as "%HvIp".
            apply auth_both_valid_discrete in HvIp.
            destruct HvIp as ([Io I_incl] & Valid_I).
            assert (p ∈ dom (Ip nr)) as Hdomp.
            { clear -HdomIp. set_solver. }
            iPureIntro.
            rewrite I_incl in Valid_I.
            rewrite I_incl intComp_dom; auto.
            clear -Hdomp. set_solver.
          }
          setoid_rewrite (big_opS_delete _ _ p) at 1; auto.
          iDestruct "HNF" as "(HNF & Hrest)".
          iDestruct "HNF" as (q qsh) "(% & Hf & Hlt)".
          rewrite {1} /ltree.
          iDestruct "Hlt" as (lsh1 lk1 nr1') "(% & Hf1 & HinFP1 & Hinv)".
          iAssert (⌜q = p1 /\ lk1 = l⌝) with "[HinFP HinFP1]" as "%Hpk".
          { iDestruct (in_FP_equiv _ p q p1 lk1 l with "[$HinFP $HinFP1]") as "?"; auto. }
          destruct Hpk as (Hpt & Hlk).
          rewrite Hpt Hlk.
          iDestruct "Hinv" as (b) "(Htm1 & Hmd1)".
          destruct b.
          2 : { iDestruct "Hmd1" as "(? & Hml1 & ?)".
              iPoseProof (malloc_token_conflict with "[$Hml1 $Hl]") as "HF"; simpl; eauto. lia.
          }
          iFrame "Htm1".
          iSplit.
          iIntros "Htm1".
          iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css) with
            "[$Hglob $Hml $Hidx Hf Hf1 HinFP1 Htm1 Hrest Hown ]" as "Hcss".
          { iSplit; auto.
            setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
            iFrame.
            iSplit; subst; auto.
            iExists nr.
            iSplit; subst; auto.
            iExists true. iFrame.
          }
          iDestruct "HClose" as "(HClose & _)".
          iFrame.
          iSpecialize ("HClose" with "Hcss").
          iMod ("HClose").
          iFrame.
          iPureIntro.
          subst. repeat (split; auto).
          iIntros (_) "Hinv".
          iDestruct "Hinv" as "(Htm1 & _)".
          iDestruct "Hglob" as "(%Hglob & HauthI & Hauthk & Hauthm & Hown_nodes)".
          destruct Hglob as (Hglob & Hr).
          rewrite -> (if_false _ (eq_dec p nullval)); auto.
          iDestruct "HClose" as "(_ & HClose)".
          iApply "HClose".
          iSplit; auto.
          iSplit.
          (* prove m !! x = nullval *)
          (* x ∉ dom m *)
          iDestruct (key_new_node_fresh _ _ x with "[$Hauthk $Hk]") as %Hx_notin_dom_m; auto.
          { iPureIntro.
            do 2 (split; auto).
            apply keyset_def.
            apply H4.
            intros Hcontra.
            apply outset_in_outsets1 in Hcontra.
            rewrite /in_outsets /in_outset in Hcontra.
            rewrite /in_outsets /in_outset in H6. easy.
          }
          apply not_elem_of_dom_1 in Hx_notin_dom_m.
          rewrite Hx_notin_dom_m; auto.
          iFrame.
          setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
          iFrame.
          do 3 (iSplit; subst; auto).
          iExists nr.
          iSplit; auto.
          iExists false.
          iFrame.
          rewrite -> if_false; auto.
        }
        simpl.
        forward.
        Exists nullval. auto.
      + (* CONTINUE *)
        destruct H11 as (Heq_p_null & Hne_dom).
        Intros.
        forward_call (css, p, p1, l, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, gv, Q1).
        { rewrite /rev_curry /=. apply bi.sep_mono; [|cancel]. by iApply AS_to_AS. }
        simpl.
        subst; try done.
        Intros lk lsh.
        rewrite H11.
        forward.
        (* push back lock into invariant *)
        rewrite /Q1.
        gather_SEP AS (inFP γ_f p p1 l) (field_at (cs := CompSpecs) lsh _ _ _ p1).
        viewshift_SEP 0 (AS ∗ (inFP γ_f p p1 l)).
        { go_lowerx. rewrite bi.sep_emp push_lock_back; auto. }
        (* end - push back lock into invariant *)
        Intros.
        forward_call (l, Q nullval).
        { rewrite /rev_curry /=.
          iIntros "(AU & HinFP & Hgv & Hmd)".
          iCombine "AU HinFP Hmd" as "Hmd".
          iCombine "Hgv" as "Hframe".
          iStopProof.
          apply bi.sep_mono; [|cancel].
          iIntros "(AU & #HinFP & Hmd)".
          unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
          iMod "AU" as (m) "(Hm & HClose)".
          iDestruct "Hm" as (I md r1) "(%Hc & Hglob & Hml & Hidx & HNF & Hown)".
          rewrite {1} /md_entry_rep.
          iDestruct "Hmd" as "(%Hc1 & Hl & Hmin & Hmax &
                    Hn_p & HI & Hk & Hm & Hrst)".
          destruct Hc1 as (? & ? & ? & ? & HdomIp).
          iModIntro.
          iExists tt.
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
            rewrite I_incl intComp_dom; auto.
            clear -Hdomp. set_solver.
          }
          setoid_rewrite (big_opS_delete _ _ p) at 1; auto.
          iDestruct "HNF" as "(HNF & Hrest)".
          iDestruct "HNF" as (q qsh) "(% & Hf & Hlt)".
          rewrite {1} /ltree.
          iDestruct "Hlt" as (lsh1 lk1 nr1') "(% & Hf1 & HinFP1 & Hinv)".
          iAssert (⌜q = p1 /\ lk1 = l⌝) with "[HinFP HinFP1]" as "%Hpk".
          { iDestruct (in_FP_equiv _ p q p1 lk1 l with "[$HinFP $HinFP1]") as "?"; auto. }
          destruct Hpk as (Hpt & Hlk).
          rewrite Hpt Hlk.
          iDestruct "Hinv" as (b) "(Htm1 & Hmd1)".
          destruct b.
          2 : { iDestruct "Hmd1" as "(? & Hml1 & ?)".
              iPoseProof (malloc_token_conflict with "[$Hml1 $Hl]") as "HF"; simpl; eauto. lia.
          }
          iFrame "Htm1".
          iSplit.
          iIntros "Htm1".
          iAssert (CSS γ_I γ_f γ_k γ_g γ_m γ_n m css) with
            "[$Hglob $Hml $Hidx Hf Hf1 HinFP1 Htm1 Hrest Hown ]" as "Hcss".
          { iSplit; auto.
            setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
            iFrame.
            iSplit; subst; auto.
            iExists nr.
            iSplit; subst; auto.
            iExists true. auto. 
          }
          iDestruct "HClose" as "(HClose & _)".
          iFrame.
          iSpecialize ("HClose" with "Hcss").
          iMod ("HClose").
          iFrame.
          iPureIntro.
          subst. repeat (split; auto).
          iIntros (_) "Hinv".
          iDestruct "Hinv" as "(Htm1 & _)".
          iDestruct "Hglob" as "(%Hglob & HauthI & Hauthk & Hauthm & Hown_nodes)".
          destruct Hglob as (Hglob & Hr).
          rewrite -> (if_true _ (eq_dec p nullval)); auto.
          iDestruct "HClose" as "(_ & HClose)".
          iApply "HClose".
          iSplit; auto.
          iSplit.
          (* prove m !! x = nullval *)
          (* x ∉ dom m *)
          iDestruct (key_new_node_fresh _ _ x with "[$Hauthk $Hk]") as %Hx_notin_dom_m; auto.
          { iPureIntro.
            do 2 (split; auto).
            apply keyset_def.
            apply H4.
            intros Hcontra.
            apply outset_in_outsets1 in Hcontra.
            rewrite /in_outsets /in_outset in Hcontra.
            rewrite /in_outsets /in_outset in H6. easy.
          }
          apply not_elem_of_dom_1 in Hx_notin_dom_m.
          rewrite Hx_notin_dom_m. auto.
          pose proof Heq_p_null as Heq_p_null1.
          iDestruct "Hrst" as "(%Hc1 & Hn & ?)".
          iDestruct (own_valid_2 γ_n (●E r1 : excl_authR (leibnizO val)) (◯E r)
                      with "[$Hown] [$Hn]") as %Hownr%@excl_auth_agree_L.
          iFrame.
          setoid_rewrite (big_opS_delete _ _ p) at 2; auto.
          iFrame.
          subst.
          do 2 (iSplit; subst; auto).
          iSplit; auto.
          iExists nr.
          iSplit; auto.
          iExists false. iFrame.
          iPureIntro.
          repeat (split; auto).
    }
    simpl.
    forward.
    Exists nullval. auto.
 Qed.
  
End verif_giveup_template.
