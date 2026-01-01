From iris.algebra Require Import proofmode_classes.
From iris.proofmode Require Import classes.
From iris_ora.logic Require Export derived.
From iris.prelude Require Import options.
Import oupred.ouPred.

(* Setup of the proof mode *)
Section class_instances.
  Context {M : uora}.
  Implicit Types P Q R : ouPred M.

  Global Instance into_pure_ora_valid `{!OraDiscrete A} (a : A) :
    @IntoPure (ouPredI M) (✓ a) (✓ a).
  Proof. by rewrite /IntoPure discrete_valid. Qed.

  Global Instance from_pure_cmra_valid {A : ora} (a : A) :
    @FromPure (ouPredI M) true (✓ a) (✓ a).
  Proof.
    rewrite /FromPure /= /bi_affinely.
    eapply bi.pure_elim; first apply bi.and_elim_r.
    intros; rewrite -ouPred.ora_valid_intro //.
    apply bi.and_elim_l.
  Qed.

  Global Instance from_sep_ownM (a b1 b2 : M) :
    IsOp(A := ora_cmraR M) a b1 b2 →
    FromSep (ouPred_ownM a) (ouPred_ownM b1) (ouPred_ownM b2).
  Proof. intros. by rewrite /FromSep -ownM_op -(is_op(A := ora_cmraR M)). Qed.
(*  (* TODO: Improve this instance with generic own simplification machinery
  once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  Global Instance combine_sep_as_ownM (a b1 b2 : M) :
    IsOp a b1 b2 →
    CombineSepAs (uPred_ownM b1) (uPred_ownM b2) (uPred_ownM a).
  Proof. intros. by rewrite /CombineSepAs -ownM_op -is_op. Qed.
  (* TODO: Improve this instance with generic own validity simplification
  machinery once https://gitlab.mpi-sws.org/iris/iris/-/issues/460 is fixed *)
  Global Instance combine_sep_gives_ownM (b1 b2 : M) :
    CombineSepGives (uPred_ownM b1) (uPred_ownM b2) (✓ (b1 ⋅ b2)).
  Proof.
    intros. rewrite /CombineSepGives -ownM_op ownM_valid.
    by apply: bi.persistently_intro.
  Qed.*)
  Global Instance from_sep_ownM_core_id (a b1 b2 : M) :
    IsOp(A := ora_cmraR M) a b1 b2 → TCOr (OraCoreId b1) (OraCoreId b2) →
    FromAnd (ouPred_ownM a) (ouPred_ownM b1) (ouPred_ownM b2).
  Proof.
    intros ? H. rewrite /FromAnd (is_op(A := ora_cmraR M) a) ownM_op.
    destruct H; by rewrite bi.persistent_and_sep_1.
  Qed.

(*  Global Instance into_and_ownM p (a b1 b2 : M) :
    IsOp(A := ora_cmraR M) a b1 b2 → IntoAnd p (ouPred_ownM a) (ouPred_ownM b1) (ouPred_ownM b2).
  Proof.
    intros. apply bi.intuitionistically_if_mono. by rewrite (is_op(A := ora_cmraR M) a) ownM_op bi.sep_and.
  Qed. *)

  Global Instance into_sep_ownM (a b1 b2 : M) :
    IsOp(A := ora_cmraR M) a b1 b2 → IntoSep (ouPred_ownM a) (ouPred_ownM b1) (ouPred_ownM b2).
  Proof. intros. by rewrite /IntoSep (is_op(A := ora_cmraR M) a) ownM_op. Qed.
End class_instances.
