Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Import Clightdefs.ClightNotations.
Local Open Scope clight_scope.

Definition _surely_malloc : ident := ($ "surely_malloc").
Definition _hash : ident := ($ "hash").

Section common_spec.
  Context `{!VSTGS unit Σ}.

  (* FOUND = F, NOTFOUND = NF, CONTINUE = CNT *)
  Inductive enum : Type := F | NF | CNT.

  Definition enums x : val :=
    match x with
    | F => Vint Int.zero
    | NF => Vint Int.one
    | CNT => Vint (Int.repr 2%Z)
    end.

  #[global] Instance enum_inhabited : Inhabitant enum.
  Proof. rewrite /Inhabitant; apply F. Defined.

  Definition surely_malloc_spec {cs: compspecs} :=
  DECLARE _surely_malloc
    WITH t: type, gv: globals
                        PRE [ size_t ]
                        PROP (and (Z.le 0 (sizeof t)) (Z.lt (sizeof t) Int.max_unsigned);
                              complete_legal_cosu_type t = true;
                              natural_aligned natural_alignment t = true)
                        PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
                        SEP (mem_mgr gv)
                        POST [ tptr tvoid ]
                        ∃ p: _,
                          PROP ()
                            RETURN (p)
                            SEP (mem_mgr gv; malloc_token Ews t p ∗ data_at_ Ews t p).

(** Spec of hash function **)
  Definition has_size : {x : Z | x = 16384}.
  Proof. eexists; eauto. Qed.

  Definition size := proj1_sig has_size.
  Lemma size_signed : (size <= Int.max_signed)%Z.
  Proof. rewrite /size (proj2_sig has_size) /=. rep_lia. Qed.

  Arguments size : simpl never.
  Parameter f : val -> Z. (* for hash *)

  Axiom f_injective : forall (new p : val), f new = f p -> new = p.
  Axiom f_0 : f nullval = 0%Z.
  
  Definition hash_spec {cs: compspecs} :=
  DECLARE _hash
    WITH p : val
               PRE [ tptr tvoid ]
               PROP (is_pointer_or_null p)
               PARAMS (p)
               GLOBALS ()
               SEP ()
               POST [ tint ]
               PROP ((0 ≤ f p < size)%Z /\ repable_signed (f p))
               RETURN (vint (f p)) SEP ().
End common_spec.
