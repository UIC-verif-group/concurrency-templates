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
Require Export tmpl.template. (* AST of template.c *)
Import Clightdefs.ClightNotations.
Local Open Scope clight_scope.

Definition t_struct_css := Tstruct _css noattr.
Definition t_struct_pn := Tstruct _pn noattr.
Definition _make_css : ident := ($ "make_css").

Section template_class.
  #[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
  Definition Vprog : varspecs. mk_varspecs prog. Defined.

  Context `{NR: NodeRep} `{EqDecision K} `{Countable K} `{nodemapG Σ}.
  
  (* Classtype for template *)
  Class Template  := {
      NodeRt : Type;
      CSSt: gname -> gname -> gname -> gname -> gname -> gname -> gmap Key KValue -> val -> mpred;
      md_entry_rep_t: gname -> gname -> gname -> gname -> val -> Node -> NodeRt -> val -> val -> mpred;
      belongs_t: Z -> NodeRt -> Prop;
      is_root_t: gname -> val -> mpred;
      Ip_of : NodeRt -> flowint_T;
      Cp_of : NodeRt -> gmap Key KValue;
      
      (** insertOp_helper spec **)
      insertOp_helper_spec :=
        DECLARE _insertOp_helper
      ATOMIC TYPE (ConstType (Z * val * val * val * val * Node * val * NodeRt * gname * gname *
                        gname * gname * gname * gname * share * globals))
      OBJ C INVS empty
      WITH x, v, css, r, p1, p, l, nr, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, sh, gv
      PRE [ tptr t_struct_css, tptr t_struct_node, tint, tptr tvoid ]
      PROP (repable_signed x; is_pointer_or_null v; (Int.min_signed < x < Int.max_signed)%Z;
            is_pointer_or_null p; in_inset _ _ Key x (Ip_of nr) p;  
            ¬ in_outsets _ _ Key x (Ip_of nr); ✓ (Ip_of nr); x ∈ KS; p = nullval -> r = nullval; 
            p <> nullval -> belongs_t x nr; is_pointer_or_null l)
      PARAMS (css; p; Vint (Int.repr x); v)
      GLOBALS (gv)
      SEP (mem_mgr gv; inFP γ_f p p1 l;
           md_entry_rep_t γ_I γ_k γ_m γ_n p1 p nr css r) | (CSSt γ_I γ_f γ_k γ_g γ_m γ_n C css)
      POST[ tvoid ]
      PROP ()
      LOCAL ()
      SEP (mem_mgr gv) | (CSSt γ_I γ_f γ_k γ_g γ_m γ_n (<[x:=v]>C) css);

      (** lookupOp_helper spec **)
      lookupOp_helper_spec :=
        DECLARE _lookupOp_helper
      ATOMIC TYPE (ConstType (enum * Z * val * val * val * val * Node * val * NodeRt *
                        gname * gname * gname * gname * gname * gname * share * globals))
      OBJ C INVS empty
      WITH status, x, v, css, r, p1, p, l, nr, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, sh, gv
      PRE [ tptr t_struct_css, tptr t_struct_node, tint, tint ]
      PROP (repable_signed x; is_pointer_or_null v; (Int.min_signed < x < Int.max_signed)%Z; 
            is_pointer_or_null p; in_inset _ _ Key x (Ip_of nr) p;
            ¬ in_outsets _ _ Key x (Ip_of nr); ✓ (Ip_of nr); x ∈ KS; p = nullval -> r = nullval;
            p <> nullval -> belongs_t x nr; is_pointer_or_null l;
          (match status with
           | F =>  (p <> nullval /\ dom (Cp_of nr) = {[x]})
           | NF => (p <> nullval /\ x ∉ dom (Cp_of nr))
           | CNT => (p = nullval /\ x ∉ dom (Cp_of nr))
           end))
      PARAMS (css; p; Vint (Int.repr x); enums status)
      GLOBALS (gv)
      SEP (mem_mgr gv; inFP γ_f p p1 l; md_entry_rep_t γ_I γ_k γ_m γ_n p1 p nr css r) |
        (CSSt γ_I γ_f γ_k γ_g γ_m γ_n C css)
      POST[ tptr tvoid ]
      ∃ ret : val,
      PROP ()
      LOCAL (temp ret_temp ret)
      SEP (mem_mgr gv) |
        (⌜(ret = match C !! x with
                 | Some v => v
                 | None => nullval end)⌝ ∧
           CSSt γ_I γ_f γ_k γ_g γ_m γ_n C css);

      (** traverse spec **)
      traverse_spec := DECLARE _traverse
      ATOMIC TYPE (ConstType (Z * val * val * val * val * Node * val *
                        gname * gname * gname * gname * gname * gname * share * globals))
      OBJ C INVS empty
      WITH x, v, pn, c, p1, pnN, l, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, sh, gv
      PRE [ tptr t_struct_css, tptr t_struct_pn, tint ]
      PROP (repable_signed x; is_pointer_or_null v; (Int.min_signed < x < Int.max_signed)%Z; 
            is_pointer_or_null pnN; is_pointer_or_null l; x ∈ KS)
      PARAMS (c; pn; Vint (Int.repr x))
      GLOBALS (gv)
      SEP (mem_mgr gv;
           is_root_t γ_n pnN;
           data_at Ews t_struct_pn (nullval, pnN) pn;
           inFP γ_f pnN p1 l) | (CSSt γ_I γ_f γ_k γ_g γ_m γ_n C c)
      POST[tint]
      (* rtrn : (status, node, pointer, lock, nodeR, root *)
      ∃ rtrn : (enum * Node * val * val * NodeRt * val),
      PROP ()
      LOCAL (temp ret_temp (let '(e, pt, pt1, lkt, nrt, rt) := rtrn in enums e))
      SEP (∃ (pnN : val), let '(e, pt, pt1, lkt, nrt, rt) := rtrn in
          ⌜is_pointer_or_null pt /\ is_pointer_or_null lkt /\
            (pt = nullval -> rt = nullval) /\ (pt <> nullval -> belongs_t x nrt) /\
            in_inset _ _ _ x (Ip_of nrt) pt /\ ¬ in_outsets _ _ _ x (Ip_of nrt) /\  ✓ (Ip_of nrt)⌝ ∧
           match e with
           | F => ⌜pt <> nullval /\ dom (Cp_of nrt) = {[x]}⌝ ∧
                   inFP γ_f pt pt1 lkt ∗
                   data_at Ews (t_struct_pn) (pt, pnN) pn ∗
                   md_entry_rep_t γ_I γ_k γ_m γ_n pt1 pt nrt c rt
           | NF => ⌜pt <> nullval /\ x ∉ dom (Cp_of nrt)⌝ ∧ inFP γ_f pt pt1 lkt ∗
                    data_at Ews (t_struct_pn) (pt, pnN) pn ∗
                    md_entry_rep_t γ_I γ_k γ_m γ_n pt1 pt nrt c rt
           | CNT => ⌜pt = nullval /\ x ∉ dom (Cp_of nrt)⌝ ∧
                  inFP γ_f pt pt1 lkt ∗
                  data_at Ews (t_struct_pn) (pt, pnN) pn ∗
                  md_entry_rep_t γ_I γ_k γ_m γ_n pt1 pt nrt c rt
             end; mem_mgr gv)
      | (CSSt γ_I γ_f γ_k γ_g γ_m γ_n C c);

      (** get_root spec **)
      get_root_spec := DECLARE _get_root
      ATOMIC TYPE (ConstType (val * gname * gname * gname * gname * gname * gname * globals))
      OBJ C INVS empty
      WITH c, γ_I, γ_f, γ_k, γ_g, γ_m, γ_n, gv
      PRE [ tptr t_struct_css ]
      PROP (True)
      PARAMS (c)
      GLOBALS (gv)
      SEP (mem_mgr gv) | (CSSt γ_I γ_f γ_k γ_g γ_m γ_n C c)
      POST[ tptr t_struct_node ]
      ∃ p : (val * val * val),
      PROP ()
      LOCAL (temp ret_temp p.1.1)
      SEP (let '(r, p1, l1) := p in
          ⌜is_pointer_or_null r /\ is_pointer_or_null p1 /\
            is_pointer_or_null l1⌝  ∧
            is_root_t γ_n r ∗
            inFP γ_f r p1 l1; mem_mgr gv ) | (CSSt γ_I γ_f γ_k γ_g γ_m γ_n C c);
      
      (** make_css spec **)
      make_css_spec :=
        DECLARE _make_css
          WITH gv: globals
      PRE [ ]
      PROP ()
      PARAMS () GLOBALS (gv)
      SEP (mem_mgr gv)
      POST [tptr  t_struct_css ]
      ∃ (css : val),
      PROP ()
      RETURN (css)
      SEP (mem_mgr gv;
           |={⊤}=> ∃ (γ_I γ_f γ_k γ_g γ_m γ_n : gname), CSSt γ_I γ_f γ_k γ_g γ_m γ_n ∅ css);
      
    }.

End template_class.
