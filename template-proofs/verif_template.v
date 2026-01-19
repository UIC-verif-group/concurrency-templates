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
Require Import tmpl.flows_ora.
Require Import VST.atomics.general_atomics.
Require Import tmpl.keyset_ra_ora.
Require Export tmpl.template_class.
Require Export tmpl.template. (* AST of template.c *)
Require Import VST.floyd.library.

Section Template.
  #[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
  Definition Vprog : varspecs. mk_varspecs prog. Defined.

  Context `{!VSTGS unit Σ, !cinvG Σ, atom_impl : !atomic_int_impl (Tstruct _atom_int noattr),
        !flowintG Σ, !nodesetG Σ, !nodemapG Σ, !keymapG Σ, !keysetG Σ,
        !inG Σ (excl_authR (leibnizO val)), !NodeRep, ! Template }.
  
   
  Definition insert_spec :=
    DECLARE _insert
      ATOMIC TYPE (ConstType (Z * val * val * NodeRt * gname * gname *
                        gname * gname * gname * gname * share * globals))
      OBJ C INVS empty
      WITH x, v, css, nr, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, sh, gv
    PRE [ tptr t_struct_css, tint, tptr tvoid ]
    PROP (repable_signed x; is_pointer_or_null v;
          (Int.min_signed < x < Int.max_signed)%Z;
           x ∈ KS)
    PARAMS (css; Vint (Int.repr x); v)
    GLOBALS (gv)
    SEP (mem_mgr gv) | (CSSt γ_I γ_f γ_k γ_g γ_m γ_n C css)
    POST[ tvoid ]
      PROP ()
      LOCAL ()
      SEP (mem_mgr gv) |
      (CSSt γ_I γ_f γ_k γ_g γ_m γ_n (<[x:=v]>C) css).

  Definition lookup_spec :=
    DECLARE _insert
      ATOMIC TYPE (ConstType (Z * val * val * NodeRt * gname * gname *
                                gname * gname * gname * gname * share * globals))
      OBJ C INVS empty
      WITH x, v, css, nr, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, sh, gv
    PRE [ tptr t_struct_css, tint]
    PROP (repable_signed x; is_pointer_or_null v;
          (Int.min_signed < x < Int.max_signed)%Z;
          x ∈ KS)
          PARAMS (css; Vint (Int.repr x))
    GLOBALS (gv)
    SEP (mem_mgr gv) | (CSSt γ_I γ_f γ_k γ_g γ_m γ_n C css)
    POST[ tptr tvoid ]
     ∃ ret : val,
       PROP ()
       LOCAL ()
       SEP (mem_mgr gv) | (⌜(ret = match C !! x with
                                   | Some v => v
                                   | None => nullval end)⌝ ∧
         CSSt γ_I γ_f γ_k γ_g γ_m γ_n C css).

  Definition Gprog : funspecs :=
     ltac:(with_library prog [surely_malloc_spec; get_root_spec; traverse_spec;
                              insertOp_helper_spec; lookupOp_helper_spec]).
 
   Lemma insert: semax_body Vprog Gprog f_insert insert_spec.
   Proof.
     start_function.
     forward_call(t_struct_pn, gv).
     Intros pn.
     forward.
     set (AS := atomic_shift _ _ _ _ _ ).
     set Q1:= fun (v : val * val * val) => AS.
     forward_call (css, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, gv, Q1).
     { rewrite /rev_curry /Q1 /=.
       iIntros "(Hml & Hdata & HAU)".
       iCombine "HAU" as "HAU".
       iCombine "Hml Hdata" as "Hrst".
       iStopProof.
       apply bi.sep_mono; [| cancel].
       iIntros "HAU".
       unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
       iMod "HAU" as (m) "(Hm & HClose)".
       iDestruct "HClose" as "(HClose & _)".
       simpl.
       iModIntro.
       iExists m.
       iFrame.
       iSplit.
       iIntros "Hm".
       by iSpecialize ("HClose" with "Hm").
       iIntros (?) "Hm".
       iApply "HClose".
       iDestruct "Hm" as "(Hm & _)".
       iFrame.
     }
     done.
     Intros root.
     destruct root as ((r & r1) & l).
     simpl.
     forward.
     set Q2 := fun (v : enum * Node * val * val * NodeRt * val) => AS.
     rewrite /Q1.
     forward_call (x, v, pn, css, r1, r, l, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, sh, gv, Q2).
     { rewrite /rev_curry /Q2 /=. apply bi.sep_mono; [| cancel].
       iIntros "HAU".
       unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
       iMod "HAU" as (m) "(Hm & HClose)".
       iDestruct "HClose" as "(HClose & _)".
       iModIntro.
       iExists m.
       iFrame.
       iSplit.
       iIntros "Hm".
       iSpecialize ("HClose" with "Hm"); try done.
       iIntros (?) "Hm".
       iApply "HClose".
       iDestruct "Hm" as "(Hm & _)".
       iFrame.
     }
     simpl.
     repeat (split; auto).
     Intros rtrn.
     Intros pnN.
     rewrite /Q2.
     destruct rtrn as ((((stt & ptn1) & lock) & nr1) & rt).
     destruct stt as (stt & pnP).
     destruct stt.
     - Intros.
       forward.
       forward_call (x, v, css, rt, ptn1, pnP, lock, nr1,
                      γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, sh, gv, Q).
       { rewrite /rev_curry /Q2 /=.
         apply bi.sep_mono; [| cancel].
         iIntros "HAU".
         unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
         iMod "HAU" as (m) "(Hm & HClose)".
         simpl.
         iModIntro.
         iExists m.
         iFrame.
       }
       simpl.
       repeat (split; auto).
       simpl.
       (* free *)
       forward_call (t_struct_pn, pn, gv).
       { assert_PROP (pn <> nullval) by entailer !. rewrite if_false; auto. cancel. }
       entailer !.
     - Intros.
       forward.
       forward_call (x, v, css, rt, ptn1, pnP, lock, nr1,
                      γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, sh, gv, Q).
       { rewrite /rev_curry /Q2 /=.
         apply bi.sep_mono; [| cancel].
         iIntros "HAU".
         unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
         iMod "HAU" as (m) "(Hm & HClose)".
         simpl.
         iModIntro.
         iExists m.
         iFrame.
       }
       simpl.
       repeat (split; auto).
       simpl.
       (* free *)
       forward_call (t_struct_pn, pn, gv).
       { assert_PROP (pn <> nullval) by entailer !. rewrite if_false; auto. cancel. }
       entailer !.
     - Intros.
       forward.
       forward_call (x, v, css, rt, ptn1, pnP, lock, nr1,
                      γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, sh, gv, Q).
       { rewrite /rev_curry /Q2 /=.
         apply bi.sep_mono; [| cancel].
         iIntros "HAU".
         unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
         iMod "HAU" as (m) "(Hm & HClose)".
         simpl.
         iModIntro.
         iExists m.
         iFrame.
       }
       simpl.
       repeat (split; auto).
       simpl.
       (* free *)
       forward_call (t_struct_pn, pn, gv).
       { assert_PROP (pn <> nullval) by entailer !. rewrite if_false; auto. cancel. }
       entailer !.
   Qed.

   Lemma lookup: semax_body Vprog Gprog f_lookup lookup_spec.
   Proof.
     start_function.
     forward_call(t_struct_pn, gv).
     Intros pn.
     forward.
     set (AS := atomic_shift _ _ _ _ _ ).
     set Q1:= fun (v : val * val * val  ) => AS.
     forward_call (css, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, gv, Q1).
     { rewrite /rev_curry /Q1 /=.
       iIntros "(Hml & Hdata & HAU)".
       iCombine "HAU" as "HAU".
       iCombine "Hml Hdata" as "Hrst".
       iStopProof.
       apply bi.sep_mono; [| cancel].
       iIntros "HAU".
       unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
       iMod "HAU" as (m) "(Hm & HClose)".
       iDestruct "HClose" as "(HClose & _)".
       simpl.
       iModIntro.
       iExists m.
       iFrame.
       iSplit.
       iIntros "Hm".
       by iSpecialize ("HClose" with "Hm").
       iIntros (?) "Hm".
       iApply "HClose".
       iDestruct "Hm" as "(Hm & _)".
       iFrame.
     }
     done.
     Intros root.
     destruct root as ((r & r1) & l).
     simpl.
     forward.
     set Q2 := fun (v : enum * Node * val * val * NodeRt * val) => AS.
     rewrite /Q1.
     forward_call (x, v, pn, css, r1, r, l, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, sh, gv, Q2).
     { rewrite /rev_curry /Q2 /=. apply bi.sep_mono; [| cancel].
       iIntros "HAU".
       unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
       iMod "HAU" as (m) "(Hm & HClose)".
       iDestruct "HClose" as "(HClose & _)".
       iModIntro.
       iExists m.
       iFrame.
       iSplit.
       iIntros "Hm".
       iSpecialize ("HClose" with "Hm"); try done.
       iIntros (?) "Hm".
       iApply "HClose".
       iDestruct "Hm" as "(Hm & _)".
       iFrame.
     }
     simpl.
     repeat (split; auto).
     Intros rtrn.
     Intros pnN.
     rewrite /Q2.
     destruct rtrn as ((((stt & ptn1) & lock) & nr1) & rt).
     destruct stt as (stt & pnP).
     destruct stt.
     - (* FOUND *)
       Intros.
       forward.
       clear dependent Q2.
       set Q2 := fun (v : val) => Q v.
       forward_call (F, x, v, css, rt, ptn1, pnP, lock, nr1,
                      γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, sh, gv, Q2).
       { rewrite /rev_curry /Q2 /=.
         apply bi.sep_mono; [| cancel].
         iIntros "HAU".
         unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
         iMod "HAU" as (m) "(Hm & HClose)".
         simpl.
         iModIntro.
         iExists m.
         iFrame.
       }
       simpl.
       repeat (split; auto).
       simpl.
       Intros v1.
       rewrite /Q2.
       forward.
       (* free *)
       forward_call (t_struct_pn, pn, gv).
       { assert_PROP (pn <> nullval) by entailer !. rewrite if_false; auto. cancel. }
       forward.
       Exists v1. entailer !.
     - (* NOTFOUND *)
       Intros.
       forward.
       clear dependent Q2.
       set Q2 := fun (v : val) => Q v.
       forward_call (NF, x, v, css, rt, ptn1, pnP, lock, nr1,
                      γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, sh, gv, Q2).
       { rewrite /rev_curry /Q2 /=.
         apply bi.sep_mono; [| cancel].
         iIntros "HAU".
         unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
         iMod "HAU" as (m) "(Hm & HClose)".
         simpl.
         iModIntro.
         iExists m.
         iFrame.
       }
       simpl.
       repeat (split; auto).
       simpl.
       Intros v1.
       rewrite /Q2.
       forward.
       (* free *)
       forward_call (t_struct_pn, pn, gv).
       { assert_PROP (pn <> nullval) by entailer !. rewrite if_false; auto. cancel. }
       forward.
       Exists v1. entailer !.
    - (* CONTINUE *)
      Intros.
      forward.
      clear dependent Q2.
      set Q2 := fun (v : val) => Q v.
      forward_call (CNT, x, v, css, rt, ptn1, pnP, lock, nr1,
                     γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, sh, gv, Q2).
      { rewrite /rev_curry /Q2 /=.
        apply bi.sep_mono; [| cancel].
        iIntros "HAU".
        unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
        iMod "HAU" as (m) "(Hm & HClose)".
        simpl.
        iModIntro.
        iExists m.
        iFrame.
      }
      simpl.
      repeat (split; auto).
      simpl.
      Intros v1.
      rewrite /Q2.
      forward.
      (* free *)
      forward_call (t_struct_pn, pn, gv).
      { assert_PROP (pn <> nullval) by entailer !. rewrite if_false; auto. cancel. }
      forward.
      Exists v1. entailer !.
  Qed.
   
End Template.
