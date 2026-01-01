From iris.algebra Require Export ofe monoid cmra numbers.
From stdpp Require Import finite.
Set Default Proof Using "Type".

(* The order of an ordered RA quantifies over [A], not [option A].  This means
   we do not get reflexivity.  However, if we used [option A], the following
   would no longer hold:
     x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2
*)
Class OraOrder A := Oraorder : A → A → Prop.
Infix "≼ₒ" := Oraorder (at level 70) : stdpp_scope.
Notation "(≼ₒ)" := Oraorder (only parsing) : stdpp_scope.
#[export] Hint Extern 0 (_ ≼ₒ _) => reflexivity : core.
#[export] Instance: Params (@Oraorder) 2 := {}.

Class OraOrderN A := OraorderN : nat → A → A → Prop.
Notation "x ≼ₒ{ n } y" := (OraorderN n x y)
  (at level 70, n at next level, format "x  ≼ₒ{ n }  y") : stdpp_scope.
(*Notation "(≼ₒ{ n })" := (OraorderN n) (only parsing) : stdpp_scope.*)
#[export] Instance: Params (@OraorderN) 3 := {}.
#[export] Hint Extern 0 (_ ≼ₒ{_} _) => reflexivity : core.

Class Increasing `{Op A, OraOrder A} (x : A) := increasing : ∀ y, y ≼ₒ x ⋅ y.
Arguments increasing {_ _ _} _ {_}.

(*Class IncreasingN `{Op A, OraOrderN A} n (x : A) := increasingN : ∀ y, y ≼ₒ{n} x ⋅ y.
Arguments increasingN {_ _ _} _ _ {_}.*)

Section mixin.
  Context (A : Type).

  Implicit Types (x : A).
  Local Set Primitive Projections.

  Record OraMixin `{Dist A, Equiv A, PCore A, Op A, Valid A, ValidN A,
                      OraOrder A, OraOrderN A} := {
    (* setoids *)
    mixin_ora_pcore_increasing x cx : pcore x = Some cx → Increasing cx;
    mixin_ora_increasing_closed n x y : Increasing x → x ≼ₒ{n} y → Increasing y;
    (* monoid *)
    mixin_ora_pcore_monoN n x y cx :
      x ≼ₒ{n} y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ₒ{n} cy;
    (* This follows from ora_extend + cmra_extend. *)
    mixin_ora_op_extend n x y1 y2 :
      ✓{n} x → y1 ⋅ y2 ≼ₒ{n} x →
      ∃ z1 z2, z1 ⋅ z2 ≼ₒ{S n} x ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2;
    mixin_ora_extend n x y :
      ✓{n} x → y ≼ₒ{n} x → ∃ z, z ≼ₒ{S n} x ∧ z ≡{n}≡ y;
    (* OraOrder *)
    mixin_ora_dist_orderN n x y : x ≡{n}≡ y → x ≼ₒ{n} y;
    mixin_ora_orderN_S n x y : x ≼ₒ{S n} y → x ≼ₒ{n} y;
    mixin_ora_orderN_trans n : Transitive (OraorderN n);
    mixin_ora_orderN_op n x x' y : x ≼ₒ{n} x' → x ⋅ y ≼ₒ{n} x' ⋅ y;
    mixin_ora_validN_orderN n x y : ✓{n} x → y ≼ₒ{n} x → ✓{n} y;
    mixin_ora_order_orderN x y : x ≼ₒ y ↔ (∀ n, x ≼ₒ{n} y);
    mixin_ora_pcore_order_op x cx y :
      pcore x ≡ Some cx → ∃ cxy, pcore (x ⋅ y) ≡ Some cxy ∧ cx ≼ₒ cxy
  }.
End mixin.

(** Bundled version *)
Structure ora := Ora' {
  ora_car :> Type;
  ora_equiv : Equiv ora_car;
  ora_dist : Dist ora_car;
  ora_pcore : PCore ora_car;
  ora_op : Op ora_car;
  ora_valid : Valid ora_car;
  ora_validN : ValidN ora_car;
  ora_order : OraOrder ora_car;
  ora_orderN : OraOrderN ora_car;
  ora_ofe_mixin : OfeMixin ora_car;
  ora_cmra_mixin : CmraMixin ora_car;
  ora_mixin : OraMixin ora_car;
}.
Arguments Ora' _ {_ _ _ _ _ _ _ _} _ _ _.
(* Given [m : OraMixin A], the notation [Ora A m] provides a smart
constructor, which uses [ofe_mixin_of A] to infer the canonical OFE mixin of
the type [A], so that it does not have to be given manually. *)
Notation Ora A m := (Ora' A (ofe_mixin_of A%type) (cmra_mixin_of A%type) m) (only parsing).

Arguments ora_car : simpl never.
Arguments ora_equiv : simpl never.
Arguments ora_dist : simpl never.
Arguments ora_pcore : simpl never.
Arguments ora_op : simpl never.
Arguments ora_valid : simpl never.
Arguments ora_validN : simpl never.
Arguments ora_order : simpl never.
Arguments ora_orderN : simpl never.
Arguments ora_ofe_mixin : simpl never.
Arguments ora_cmra_mixin : simpl never.
Arguments ora_mixin : simpl never.
Add Printing Constructor ora.
#[export] Hint Extern 0 (PCore _) => eapply (@ora_pcore _) : typeclass_instances.
#[export] Hint Extern 0 (Op _) => eapply (@ora_op _) : typeclass_instances.
#[export] Hint Extern 0 (Valid _) => eapply (@ora_valid _) : typeclass_instances.
#[export] Hint Extern 0 (ValidN _) => eapply (@ora_validN _) : typeclass_instances.
#[export] Hint Extern 0 (OraOrder _) => eapply (@ora_order _) : typeclass_instances.
#[export] Hint Extern 0 (OraOrderN _) => eapply (@ora_orderN _) : typeclass_instances.
Coercion ora_ofeO (A : ora) : ofe := Ofe A (ora_ofe_mixin A).
Canonical Structure ora_ofeO.
Coercion ora_cmraR (A : ora) : cmra := Cmra A (ora_cmra_mixin A).
Canonical Structure ora_cmraR.

Definition ora_mixin_of' A {Ac : ora} (f : Ac → A) : OraMixin Ac := ora_mixin Ac.
Notation ora_mixin_of A :=
  ltac:(let H := eval hnf in (ora_mixin_of' A id) in exact H) (only parsing).

(** Lifting properties from the mixin *)
Section ora_mixin.
  Context {A : ora}.
  Implicit Types x y : A.
  Global Instance ora_assoc : Assoc (≡@{A} ) (⋅) := cmra_assoc.
  Global Instance ora_comm : Comm (≡@{A} ) (⋅) := cmra_comm.
  Global Instance ora_pcore_increasing x cx : pcore x = Some cx → Increasing cx.
  Proof. apply (mixin_ora_pcore_increasing _ (ora_mixin A)). Qed.
  Lemma ora_increasing_closed n x y : Increasing x → x ≼ₒ{n} y → Increasing y.
  Proof. apply (mixin_ora_increasing_closed _ (ora_mixin A)). Qed.
  Lemma ora_pcore_monoN n x y cx :
    x ≼ₒ{n} y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ₒ{n} cy.
  Proof. apply (mixin_ora_pcore_monoN _ (ora_mixin A)). Qed.
  Lemma ora_op_extend n x y1 y2 :
    ✓{n} x → y1 ⋅ y2 ≼ₒ{n} x →
    ∃ z1 z2, z1 ⋅ z2 ≼ₒ{S n} x ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2.
  Proof. apply (mixin_ora_op_extend _ (ora_mixin A)). Qed.
  Lemma ora_extend n x y :
      ✓{n} x → y ≼ₒ{n} x → ∃ z, z ≼ₒ{S n} x ∧ z ≡{n}≡ y.
  Proof. apply (mixin_ora_extend _ (ora_mixin A)). Qed.
  Lemma ora_dist_orderN n x y : x ≡{n}≡ y → x ≼ₒ{n} y.
  Proof. apply (mixin_ora_dist_orderN _ (ora_mixin A)). Qed.
  Lemma ora_orderN_S n x y : x ≼ₒ{S n} y → x ≼ₒ{n} y.
  Proof. apply (mixin_ora_orderN_S _ (ora_mixin A)). Qed.
  Global Instance ora_orderN_trans n : Transitive (@OraorderN A _ n).
  Proof. apply (mixin_ora_orderN_trans _ (ora_mixin A)). Qed.
  Lemma ora_orderN_op n x x' y : x ≼ₒ{n} x' → x ⋅ y ≼ₒ{n} x' ⋅ y.
  Proof. apply (mixin_ora_orderN_op _ (ora_mixin A)). Qed.
  Lemma ora_validN_orderN n x y : ✓{n} x → y ≼ₒ{n} x → ✓{n} y.
  Proof. apply (mixin_ora_validN_orderN _ (ora_mixin A)). Qed.
  Lemma ora_order_orderN x y : x ≼ₒ y ↔ (∀ n, x ≼ₒ{n} y).
  Proof. apply (mixin_ora_order_orderN _ (ora_mixin A)). Qed.
  Lemma ora_pcore_order_op x cx y :
    pcore x ≡ Some cx → ∃ cxy, pcore (x ⋅ y) ≡ Some cxy ∧ cx ≼ₒ cxy.
  Proof. apply (mixin_ora_pcore_order_op _ (ora_mixin A)). Qed.
End ora_mixin.


Definition OraopM {A : ora} (x : A) (my : option A) :=
  match my with Some y => x ⋅ y | None => x end.
Infix "⋅?" := OraopM (at level 50, left associativity) : stdpp_scope.

(** * CoreId elements *)
Class OraCoreId {A : ora} (x : A) := oracore_id : pcore x ≡ Some x.
Arguments oracore_id {_} _ {_}.
#[export] Hint Mode OraCoreId + ! : typeclass_instances.
#[export] Instance: Params (@OraCoreId) 1 := {}.

(** * Exclusive elements (i.e., elements that cannot have a frame). *)
Class OraExclusive {A : ora} (x : A) := oraexclusive0_l y : ✓{0} (x ⋅ y) → False.
Arguments oraexclusive0_l {_} _ {_} _ _.
#[export] Hint Mode OraExclusive + ! : typeclass_instances.
#[export] Instance: Params (@OraExclusive) 1 := {}.

(** * Cancelable elements. *)
Class OraCancelable {A : ora} (x : A) :=
  oracancelableN n y z : ✓{n}(x ⋅ y) → x ⋅ y ≡{n}≡ x ⋅ z → y ≡{n}≡ z.
Arguments oracancelableN {_} _ {_} _ _ _ _.
#[export] Hint Mode OraCancelable + ! : typeclass_instances.
#[export] Instance: Params (@OraCancelable) 1 := {}.

(** * Identity-free elements. *)
Class OraIdFree {A : ora} (x : A) :=
  oraid_free0_r y : ✓{0}x → x ⋅ y ≡{0}≡ x → False.
Arguments oraid_free0_r {_} _ {_} _ _.
#[export] Hint Mode OraIdFree + ! : typeclass_instances.
#[export] Instance: Params (@OraIdFree) 1 := {}.

(** * CMRAs whose core is total *)
(** The function [core] may return a dummy when used on CMRAs without total
core. *)
Class OraTotal (A : ora) := ora_total (x : A) : is_Some (pcore x).
#[export] Hint Mode OraTotal ! : typeclass_instances.

Structure uora := Uora' {
  uora_car :> Type;
  uora_equiv : Equiv uora_car;
  uora_dist : Dist uora_car;
  uora_pcore : PCore uora_car;
  uora_op : Op uora_car;
  uora_valid : Valid uora_car;
  uora_validN : ValidN uora_car;
  uora_order : OraOrder uora_car;
  uora_orderN : OraOrderN uora_car;
  uora_unit : Unit uora_car;
  uora_ofe_mixin : OfeMixin uora_car;
  uora_cmra_mixin : CmraMixin uora_car;
  uora_ora_mixin : OraMixin uora_car;
  uora_ucmra_mixin : UcmraMixin uora_car;
}.
Arguments Uora' _ {_ _ _ _ _ _ _ _ _} _ _ _.
Notation Uora A m :=
  (Uora' A (ofe_mixin_of A%type) (cmra_mixin_of A%type) (ora_mixin_of A%type) m) (only parsing).
Arguments uora_car : simpl never.
Arguments uora_equiv : simpl never.
Arguments uora_dist : simpl never.
Arguments uora_pcore : simpl never.
Arguments uora_op : simpl never.
Arguments uora_valid : simpl never.
Arguments uora_validN : simpl never.
Arguments uora_order : simpl never.
Arguments uora_orderN : simpl never.
Arguments uora_ofe_mixin : simpl never.
Arguments uora_cmra_mixin : simpl never.
Arguments uora_ora_mixin : simpl never.
Arguments uora_ucmra_mixin : simpl never.
Add Printing Constructor uora.
#[export] Hint Extern 0 (Unit _) => eapply (@uora_unit _) : typeclass_instances.
Coercion uora_ofeO (A : uora) : ofe := Ofe A (uora_ofe_mixin A).
Canonical Structure uora_ofeO.
Coercion uora_oraR (A : uora) : ora :=
  Ora' A (uora_ofe_mixin A) (uora_cmra_mixin A) (uora_ora_mixin A).
Canonical Structure uora_oraR.
Coercion uora_ucmraR (A : uora) : ucmra :=
  Ucmra' A (uora_ofe_mixin A) (uora_cmra_mixin A) (uora_ucmra_mixin A).
Canonical Structure uora_ucmraR.

(** Lifting properties from the mixin *)
Section uora_mixin.
  Context {A : uora}.
  Implicit Types x y : A.
  Global Instance uora_unit_left_id : LeftId (≡) ε (@op A _).
  Proof. apply (mixin_ucmra_unit_left_id _ (ucmra_mixin A)). Qed.
End uora_mixin.

(** * Discrete CMRAs *)
Class OraDiscrete (A : ora) := {
  ora_discrete_ofe_discrete :: OfeDiscrete A;
  ora_discrete_valid (x : A) : ✓{0} x → ✓ x;
  ora_discrete_order (x y: A) : x ≼ₒ{0} y → x ≼ₒ y
}.
#[export] Hint Mode OraDiscrete ! : typeclass_instances.

(** * Morphisms *)
Class OraMorphism {A B : ora} (f : A → B) := {
  ora_cmra_morphism :: CmraMorphism f;
  ora_morphism_orderN n x y : x ≼ₒ{n} y  → f x ≼ₒ{n} f y;
  ora_morphism_increasing x : Increasing x → Increasing (f x);
}.
Arguments ora_cmra_morphism {_ _} _ {_}.
Arguments ora_morphism_orderN {_ _} _ {_} _ _ _.
Arguments ora_morphism_increasing {_ _} _ _ _.

(** * Properties **)
Section ora.
Context {A : ora}.
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

(** ** Setoids *)
Global Instance ora_order_trans: Transitive (@Oraorder A _).
Proof.
  intros x y z Hxy Hyz; apply ora_order_orderN => n;
    eapply (@ora_orderN_trans _ _ _ y); by eapply ora_order_orderN.
Qed.
Global Instance ora_pcore_ne' : NonExpansive (@pcore A _) := cmra_pcore_ne'.
Lemma ora_pcore_proper x y cx :
  x ≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡ cy.
Proof.
  apply @cmra_pcore_proper.
Qed.
Global Instance ora_pcore_proper' : Proper ((≡) ==> (≡)) (@pcore A _).
Proof. apply (ne_proper _). Qed.
Global Instance ora_op_ne' : NonExpansive2 (@op A _).
Proof. intros n x1 x2 Hx y1 y2 Hy. by rewrite Hy (comm _ x1) Hx (comm _ y2). Qed.
Global Instance ora_op_proper' : Proper ((≡) ==> (≡) ==> (≡)) (@op A _).
Proof. apply (ne_proper_2 _). Qed.
Global Instance ora_validN_ne' n : Proper (dist n ==> iff) (@validN A _ n) | 1 := cmra_validN_ne' n.
Global Instance ora_validN_proper n : Proper ((≡) ==> iff) (@validN A _ n) | 1 := cmra_validN_proper n.

Lemma ora_order_op x x' y : x ≼ₒ x' → x ⋅ y ≼ₒ x' ⋅ y.
Proof.
  intros. apply ora_order_orderN =>?.
  by eapply ora_orderN_op, ora_order_orderN.
Qed.

Global Instance ora_valid_proper : Proper ((≡) ==> iff) (@valid A _) := cmra_valid_proper.
Global Instance ora_orderN_ne n :
  Proper (dist n ==> dist n ==> iff) (@OraorderN A _ n) | 1.
Proof.
  intros x x' Hx y y' Hy. split.
  - intros Hxy. etrans; first apply ora_dist_orderN; first by rewrite -Hx.
    etrans; first done. by apply ora_dist_orderN.
  - intros Hxy'. etrans; first apply ora_dist_orderN; first done.
    etrans; first done. by apply ora_dist_orderN.
Qed.
Global Instance ora_orderN_proper n :
  Proper ((≡) ==> (≡) ==> iff) (@OraorderN A _ n) | 1.
Proof.
  intros x x' Hx y y' Hy; revert Hx Hy; rewrite !equiv_dist=> Hx Hy.
  by rewrite (Hx n) (Hy n).
Qed.
Global Instance ora_order_proper :
  Proper ((≡) ==> (≡) ==> iff) (@Oraorder A _) | 1.
Proof.
  intros x x' Hx y y' Hy.
  split; intros Hxy; apply ora_order_orderN => n;
    eapply (ora_order_orderN) in Hxy.
  - eapply ora_orderN_proper; [symmetry| symmetry|]; eauto.
  - eapply ora_orderN_proper; eauto.
Qed.
Global Instance ora_orderN_properN n :
  Proper (flip (OraorderN n) ==> (OraorderN n) ==> impl) (@OraorderN A _ n) | 1.
Proof.
  intros x x' Hx y y' Hy Hz.
  etrans; first apply Hx. etrans; eauto.
Qed.
Global Instance ora_order_properN :
  Proper (flip (≼ₒ) ==> (≼ₒ) ==> impl) (@Oraorder A _) | 1.
Proof.
  intros x x' Hx y y' Hy Hz.
  etrans; first apply Hx. etrans; eauto.
Qed.
Global Instance ora_opM_ne : NonExpansive2 (@OraopM A).
Proof. destruct 2; by ofe_subst. Qed.
Global Instance ora_opM_proper : Proper ((≡) ==> (≡) ==> (≡)) (@OraopM A).
Proof. destruct 2; by setoid_subst. Qed.

Global Instance CoreId_proper : Proper ((≡) ==> iff) (@OraCoreId A).
Proof. solve_proper. Qed.
Global Instance Exclusive_proper : Proper ((≡) ==> iff) (@OraExclusive A).
Proof. intros x y Hxy. rewrite /OraExclusive. by setoid_rewrite Hxy. Qed.
Global Instance Cancelable_proper : Proper ((≡) ==> iff) (@OraCancelable A).
Proof. intros x y Hxy. rewrite /OraCancelable. by setoid_rewrite Hxy. Qed.
Global Instance IdFree_proper : Proper ((≡) ==> iff) (@OraIdFree A).
Proof. intros x y Hxy. rewrite /OraIdFree. by setoid_rewrite Hxy. Qed.

(** ** Op *)
Lemma ora_opM_assoc x y mz : (x ⋅ y) ⋅? mz ≡ x ⋅ (y ⋅? mz).
Proof. destruct mz; by rewrite /= -?assoc. Qed.

(*(** ** Validity *)
Lemma ora_validN_le n n' x : ✓{n} x → n' ≤ n → ✓{n'} x.
Proof. induction 2; eauto using ora_validN_S. Qed.
Lemma ora_valid_op_l x y : ✓ (x ⋅ y) → ✓ x.
Proof. rewrite !ora_valid_validN; eauto using ora_validN_op_l. Qed.
Lemma ora_validN_op_r n x y : ✓{n} (x ⋅ y) → ✓{n} y.
Proof. rewrite (comm _ x); apply ora_validN_op_l. Qed.
Lemma ora_valid_op_r x y : ✓ (x ⋅ y) → ✓ y.
Proof. rewrite !ora_valid_validN; eauto using ora_validN_op_r. Qed.

(** ** Core *)
Lemma ora_pcore_l' x cx : pcore x ≡ Some cx → cx ⋅ x ≡ x.
Proof. inversion 1 as [?? Ha|]; subst. by rewrite -Ha; apply ora_pcore_l. Qed.
Lemma ora_pcore_r x cx : pcore x = Some cx → x ⋅ cx ≡ x.
Proof. intros. rewrite comm. by apply ora_pcore_l. Qed.
Lemma ora_pcore_r' x cx : pcore x ≡ Some cx → x ⋅ cx ≡ x.
Proof. inversion 1 as [?? Ha|]; subst. by rewrite -Ha; apply ora_pcore_r. Qed.
Lemma ora_pcore_idemp' x cx : pcore x ≡ Some cx → pcore cx ≡ Some cx.
Proof. inversion 1 as [?? Ha|]; subst. rewrite -Ha; eauto using ora_pcore_idemp. Qed.
Lemma ora_pcore_dup x cx : pcore x = Some cx → cx ≡ cx ⋅ cx.
Proof. intros; symmetry; eauto using ora_pcore_r', ora_pcore_idemp. Qed.
Lemma ora_pcore_dup' x cx : pcore x ≡ Some cx → cx ≡ cx ⋅ cx.
Proof. intros; symmetry; eauto using ora_pcore_r', ora_pcore_idemp'. Qed.
Lemma ora_pcore_validN n x cx : ✓{n} x → pcore x = Some cx → ✓{n} cx.
Proof.
  intros Hvx Hx%ora_pcore_l. move: Hvx; rewrite -Hx. apply ora_validN_op_l.
Qed.
Lemma ora_pcore_valid x cx : ✓ x → pcore x = Some cx → ✓ cx.
Proof.
  intros Hv Hx%ora_pcore_l. move: Hv; rewrite -Hx. apply ora_valid_op_l.
Qed.*)

(** ** CoreId elements *)
Lemma oracore_id_dup x `{!OraCoreId x} : x ≡ x ⋅ x.
Proof. by apply @cmra_pcore_dup' with x. Qed.
Global Instance ora_coreid_increasing x `{!OraCoreId x} : Increasing x.
Proof.
  inversion OraCoreId0 as [?? Heq|].
  intros ?.
  rewrite -Heq; eapply ora_pcore_increasing; eauto.
Qed.

(** ** Exclusive elements *)
Lemma OraexclusiveN_l n x `{!OraExclusive x} y : ✓{n} (x ⋅ y) → False.
Proof. intros. eapply (oraexclusive0_l x y), cmra_validN_le; eauto with lia. Qed.
Lemma OraexclusiveN_r n x `{!OraExclusive x} y : ✓{n} (y ⋅ x) → False.
Proof. rewrite comm. by apply OraexclusiveN_l. Qed.
Lemma Oraexclusive_l x `{!OraExclusive x} y : ✓ (x ⋅ y) → False.
Proof. by move /cmra_valid_validN /(_ 0) /oraexclusive0_l. Qed.
Lemma Oraexclusive_r x `{!OraExclusive x} y : ✓ (y ⋅ x) → False.
Proof. rewrite comm. by apply Oraexclusive_l. Qed.
Lemma OraexclusiveN_opM n x `{!OraExclusive x} my : ✓{n} (x ⋅? my) → my = None.
Proof. destruct my as [y|]. move=> /(OraexclusiveN_l _ x) []. done. Qed.
Lemma Oraexclusive_includedN n x `{!OraExclusive x} y : x ≼{n} y → ✓{n} y → False.
Proof. intros [? ->]. by apply OraexclusiveN_l. Qed.
Lemma Oraexclusive_included x `{!OraExclusive x} y : x ≼ y → ✓ y → False.
Proof. intros [? ->]. by apply Oraexclusive_l. Qed.

(** ** Order *)
(*Lemma ora_valid_order x y : ✓ y → x ≼ y → ✓ x.
Proof. intros Hyv [z ?]; setoid_subst; eauto using ora_valid_op_l. Qed.
Lemma ora_validN_order n x y : ✓{n} y → x ≼ y → ✓{n} x.
Proof. intros Hyv [z ?]; setoid_subst; eauto using ora_validN_op_l. Qed.*)

Lemma ora_orderN_le n n' x y : x ≼ₒ{n} y → n' ≤ n → x ≼ₒ{n'} y.
Proof. induction 2; auto using ora_orderN_S. Qed.

(* Lemma ora_pcore_order_op' x cx y : *)
(*   pcore x ≡ Some cx → ∃ cxy, pcore (x ⋅ y) = Some cxy ∧ cx ≼ₒ cxy. *)
(* Proof. *)
(*   intros (cx'&?&Hcx)%equiv_Some_inv_r'. *)
(*   destruct (ora_pcore_order_op x cx' y) as (cy&->&?); auto. *)
(*   exists cy; by rewrite Hcx. *)
(*  Qed. *)

Global Instance ora_orderN_refl n: Reflexive ((OraorderN n) : A → A → Prop).
Proof. intros ?; by apply ora_dist_orderN. Qed.

Lemma ora_order_refl : Reflexive ((≼ₒ) : A → A → Prop).
Proof. intros x. by eapply ora_order_orderN. Qed.

Lemma ora_pcore_monoN' n x y cx :
  x ≼ₒ{n} y → pcore x ≡ Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ₒ{n} cy.
Proof.
  intros ?.
  inversion 1 as [cx' ? Hcx|]; subst.
  destruct (ora_pcore_monoN n x y cx') as (cy&->&?); auto.
  exists cy; by rewrite -Hcx.
Qed.
(* Lemma cmra_pcore_monoN' n x y cx : *)
(*   x ≼{n} y → pcore x ≡{n}≡ Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼{n} cy. *)
(* Proof. *)
(*   intros [z Hy] (cx'&?&Hcx)%dist_Some_inv_r'. *)
(*   destruct (cmra_pcore_mono x (x ⋅ z) cx') *)
(*     as (cy&Hxy&?); auto using cmra_included_l. *)
(*   assert (pcore y ≡{n}≡ Some cy) as (cy'&?&Hcy')%dist_Some_inv_r'. *)
(*   { by rewrite Hy Hxy. } *)
(*   exists cy'; split; first done. *)
(*   rewrite Hcx -Hcy'; auto using cmra_included_includedN. *)
(* Qed. *)
(* Lemma ora_order_pcore x cx : pcore x = Some cx → cx ≼ₒ x. *)
(* Proof. exists x. by rewrite ora_pcore_l. Qed. *)

Lemma ora_monoN_l n x y z : x ≼ₒ{n} y → z ⋅ x ≼ₒ{n} z ⋅ y.
Proof. rewrite !(comm _ z) => ?. by apply ora_orderN_op. Qed.
Lemma ora_mono_l x y z : x ≼ₒ y → z ⋅ x ≼ₒ z ⋅ y.
Proof.
  rewrite !(comm _ z) => ?.
  apply ora_order_orderN =>?; apply ora_orderN_op.
  by apply ora_order_orderN.
Qed.
Lemma ora_monoN_r n x y z : x ≼ₒ{n} y → x ⋅ z ≼ₒ{n} y ⋅ z.
Proof. by intros; rewrite -!(comm _ z); apply ora_monoN_l. Qed.
Lemma ora_mono_r x y z : x ≼ₒ y → x ⋅ z ≼ₒ y ⋅ z.
Proof. by intros; rewrite -!(comm _ z); apply ora_mono_l. Qed.
Lemma ora_monoN n x1 x2 y1 y2 : x1 ≼ₒ{n} y1 → x2 ≼ₒ{n} y2 → x1 ⋅ x2 ≼ₒ{n} y1 ⋅ y2.
Proof.
  intros; etrans; first apply ora_monoN_l; eauto.
  eauto using ora_monoN_r.
Qed.
Lemma ora_mono x1 x2 y1 y2 : x1 ≼ₒ y1 → x2 ≼ₒ y2 → x1 ⋅ x2 ≼ₒ y1 ⋅ y2.
Proof. intros; etrans; eauto using ora_mono_l, ora_mono_r. Qed.

Global Instance ora_monoN' n :
  Proper (OraorderN n ==> OraorderN n ==> OraorderN n) (@op A _).
Proof. intros x1 x2 Hx y1 y2 Hy. by apply ora_monoN. Qed.
Global Instance ora_mono' :
  Proper (Oraorder ==> Oraorder ==> Oraorder) (@op A _).
Proof. intros x1 x2 Hx y1 y2 Hy. by apply ora_mono. Qed.

(*Global Instance Increasing_IncreasingN (x : A) n {H : Increasing x} : IncreasingN n x.
Proof. by intros ?; apply ora_order_orderN. Qed.*)

(* Lemma ora_order_dist_l n x1 x2 x1' : *)
(*   x1 ≼ₒ x2 → x1' ≡{n}≡ x1 → ∃ x2', x1' ≼ₒ x2' ∧ x2' ≡{n}≡ x2. *)
(* Proof. *)
(*   intros [z Hx2] Hx1; exists (x1' ⋅ z); split; auto using cmra_included_l. *)
(*   by rewrite Hx1 Hx2. *)
(* Qed. *)

(** ** Total core *)
Section total_core.
  Local Set Default Proof Using "Type*".
  Context `{OraTotal A}.

  Lemma ora_core_l x : core x ⋅ x ≡ x.
  Proof.
    destruct (ora_total x) as [cx Hcx]. by rewrite /core /= Hcx cmra_pcore_l.
  Qed.
  Lemma ora_core_idemp x : core (core x) ≡ core x.
  Proof.
    destruct (ora_total x) as [cx Hcx]. by rewrite /core /= Hcx cmra_pcore_idemp.
  Qed.
  Lemma ora_core_mono x y : x ≼ₒ y → core x ≼ₒ core y.
  Proof.
    intros; destruct (ora_total x) as [cx Hcx].
    apply ora_order_orderN => n.
    destruct (ora_pcore_monoN n x y cx) as (cy&Hcy&?); auto;
      first by apply ora_order_orderN.
    by rewrite /core /= Hcx Hcy.
  Qed.

  Global Instance ora_core_ne : NonExpansive (@core A _).
  Proof.
    intros n x y Hxy. destruct (ora_total x) as [cx Hcx].
    by rewrite /core /= -Hxy Hcx.
  Qed.
  Global Instance ora_core_proper : Proper ((≡) ==> (≡)) (@core A _).
  Proof. apply (ne_proper _). Qed.

  Lemma ora_core_r x : x ⋅ core x ≡ x.
  Proof. by rewrite (comm _ x) ora_core_l. Qed.
  Lemma ora_core_dup x : core x ≡ core x ⋅ core x.
  Proof. by rewrite -{3}(ora_core_idemp x) ora_core_r. Qed.
  Lemma ora_core_validN n x : ✓{n} x → ✓{n} core x.
  Proof. rewrite -{1}(ora_core_l x); apply cmra_validN_op_l. Qed.
  Lemma ora_core_valid x : ✓ x → ✓ core x.
  Proof. rewrite -{1}(ora_core_l x); apply cmra_valid_op_l. Qed.

  Lemma oracore_id_total x : OraCoreId x ↔ core x ≡ x.
  Proof.
    split; [intros; by rewrite /core /= (oracore_id x)|].
    rewrite /OraCoreId /core /=.
    destruct (ora_total x) as [? ->]. by constructor.
  Qed.
  Lemma oracore_id_core x `{!OraCoreId x} : core x ≡ x.
  Proof. by apply oracore_id_total. Qed.

  Global Instance ora_core_core_id x : OraCoreId (core x).
  Proof.
    destruct (ora_total x) as [cx Hcx].
    rewrite /OraCoreId /core /= Hcx /=. eapply @cmra_pcore_idemp; eauto.
  Qed.

  Lemma ora_core_increasing x : Increasing (core x).
  Proof.
    intros z. rewrite /core.
    destruct (ora_total x) as [cx Hcx]; rewrite Hcx /=.
    eapply ora_pcore_increasing; eauto.
  Qed.

  Lemma ora_included_core x : core x ≼ x.
  Proof. by exists x; rewrite ora_core_l. Qed.
  Global Instance ora_orderN_preorder n : PreOrder (@OraorderN A _ n).
  Proof.
    split; [|apply _]; auto.
  Qed.
  Global Instance ora_order_preorder : PreOrder (@Oraorder A _).
  Proof.
    split; [|apply _]. intros x; by apply ora_order_orderN.
  Qed.
  Lemma ora_core_monoN n x y : x ≼ₒ{n} y → core x ≼ₒ{n} core y.
  Proof.
    intros Hxy.
    intros; destruct (ora_total x) as [cx Hcx].
    destruct (ora_pcore_monoN n x y cx) as (cy&Hcy&?); trivial.
    by rewrite /core /= Hcx Hcy.
  Qed.
End total_core.

(** ** Discrete *)
(* Lemma cmra_discrete_included_l x y : Discrete x → ✓{0} y → x ≼ₒ{0} y → x ≼ₒ y. *)
(* Proof. *)
(*   intros ?? [x' ?]. *)
(*   destruct (cmra_extend 0 y x x') as (z&z'&Hy&Hz&Hz'); auto; simpl in *. *)
(*   by exists z'; rewrite Hy (discrete x z). *)
(* Qed. *)
(* Lemma cmra_discrete_included_r x y : Discrete y → x ≼{0} y → x ≼ y. *)
(* Proof. intros ? [x' ?]. exists x'. by apply (discrete y). Qed. *)
(* Lemma cmra_op_discrete x1 x2 : *)
(*   ✓ (x1 ⋅ x2) → Discrete x1 → Discrete x2 → Discrete (x1 ⋅ x2). *)
(* Proof. *)
(*   intros ??? z Hz. *)
(*   destruct (cmra_extend 0 z x1 x2) as (y1&y2&Hz'&?&?); auto; simpl in *. *)
(*   { rewrite -?Hz. by apply cmra_valid_validN. } *)
(*   by rewrite Hz' (discrete x1 y1) // (discrete x2 y2). *)
(* Qed. *)

(** ** Discrete *)
Instance ora_cmra_discrete `{OraDiscrete A} : CmraDiscrete A.
Proof.
  destruct H; split; auto.
Qed.

Lemma ora_discrete_valid_iff `{OraDiscrete A} n x : ✓ x ↔ ✓{n} x.
Proof.
  split; first by rewrite cmra_valid_validN.
  eauto using ora_discrete_valid, cmra_validN_le with lia.
Qed.
Lemma ora_discrete_valid_iff_0 `{OraDiscrete A} n x : ✓{0} x ↔ ✓{n} x.
Proof. apply cmra_discrete_valid_iff_0. Qed.
Lemma ora_discrete_included_iff `{OraDiscrete A} n x y : x ≼ₒ y ↔ x ≼ₒ{n} y.
Proof.
  split => ?; first by apply ora_order_orderN.
  apply ora_discrete_order; eapply ora_orderN_le; first eauto; lia.
Qed.
Lemma cmra_discrete_included_iff_0 `{OraDiscrete A} n x y : x ≼ₒ{0} y ↔ x ≼ₒ{n} y.
Proof. by rewrite -!ora_discrete_included_iff. Qed.

(* (** Cancelable elements  *) *)
(* Global Instance cancelable_proper : Proper (equiv ==> iff) (@Cancelable A). *)
(* Proof. unfold Cancelable. intros x x' EQ. by setoid_rewrite EQ. Qed. *)
(* Lemma cancelable x `{!Cancelable x} y z : ✓(x ⋅ y) → x ⋅ y ≡ x ⋅ z → y ≡ z. *)
(* Proof. rewrite !equiv_dist cmra_valid_validN. intros. by apply (cancelableN x). Qed. *)
(* Lemma discrete_cancelable x `{CmraDiscrete A}: *)
(*   (∀ y z, ✓(x ⋅ y) → x ⋅ y ≡ x ⋅ z → y ≡ z) → Cancelable x. *)
(* Proof. intros ????. rewrite -!discrete_iff -cmra_discrete_valid_iff. auto. Qed. *)
(* Global Instance cancelable_op x y : *)
(*   Cancelable x → Cancelable y → Cancelable (x ⋅ y). *)
(* Proof. *)
(*   intros ?? n z z' ??. apply (cancelableN y), (cancelableN x). *)
(*   - eapply cmra_validN_op_r. by rewrite assoc. *)
(*   - by rewrite assoc. *)
(*   - by rewrite !assoc. *)
(* Qed. *)
(* Global Instance exclusive_cancelable (x : A) : Exclusive x → Cancelable x. *)
(* Proof. intros ? n z z' []%(exclusiveN_l _ x). Qed. *)

(* (** Id-free elements  *) *)
(* Global Instance id_free_ne n : Proper (dist n ==> iff) (@IdFree A). *)
(* Proof. *)
(*   intros x x' EQ%(dist_le _ 0); last lia. rewrite /IdFree. *)
(*   split=> y ?; (rewrite -EQ || rewrite EQ); eauto. *)
(* Qed. *)
(* Global Instance id_free_proper : Proper (equiv ==> iff) (@IdFree A). *)
(* Proof. by move=> P Q /equiv_dist /(_ 0)=> ->. Qed. *)
(* Lemma id_freeN_r n n' x `{!IdFree x} y : ✓{n}x → x ⋅ y ≡{n'}≡ x → False. *)
(* Proof. eauto using cmra_validN_le, dist_le with lia. Qed. *)
(* Lemma id_freeN_l n n' x `{!IdFree x} y : ✓{n}x → y ⋅ x ≡{n'}≡ x → False. *)
(* Proof. rewrite comm. eauto using id_freeN_r. Qed. *)
(* Lemma id_free_r x `{!IdFree x} y : ✓x → x ⋅ y ≡ x → False. *)
(* Proof. move=> /cmra_valid_validN ? /equiv_dist. eauto. Qed. *)
(* Lemma id_free_l x `{!IdFree x} y : ✓x → y ⋅ x ≡ x → False. *)
(* Proof. rewrite comm. eauto using id_free_r. Qed. *)
(* Lemma discrete_id_free x `{CmraDiscrete A}: *)
(*   (∀ y, ✓ x → x ⋅ y ≡ x → False) → IdFree x. *)
(* Proof. *)
(*   intros Hx y ??. apply (Hx y), (discrete _); eauto using cmra_discrete_valid. *)
(* Qed. *)
(* Global Instance id_free_op_r x y : IdFree y → Cancelable x → IdFree (x ⋅ y). *)
(* Proof. *)
(*   intros ?? z ? Hid%symmetry. revert Hid. rewrite -assoc=>/(cancelableN x) ?. *)
(*   eapply (id_free0_r _); [by eapply cmra_validN_op_r |symmetry; eauto]. *)
(* Qed. *)
(* Global Instance id_free_op_l x y : IdFree x → Cancelable y → IdFree (x ⋅ y). *)
(* Proof. intros. rewrite comm. apply _. Qed. *)
(* Global Instance exclusive_id_free x : Exclusive x → IdFree x. *)
(* Proof. intros ? z ? Hid. apply (exclusiveN_l 0 x z). by rewrite Hid. Qed. *)
End ora.

(** * Properties about CMRAs with a unit element **)
Section uora.
  Context {A : uora}.
  Implicit Types x y z : A.

  Lemma uora_unit_validN n : ✓{n} (ε:A).
  Proof. apply (@cmra_valid_validN (ora_cmraR _)), ucmra_unit_valid. Qed.
  Global Instance uora_unit_right_id : RightId (≡) ε (@op A _).
  Proof. apply ucmra_unit_right_id. Qed.
  Global Instance uora_unit_core_id : OraCoreId (ε:A).
  Proof. apply ucmra_pcore_unit. Qed.

  Lemma uora_unit_order_increasing x `{!Increasing x} : ε ≼ₒ x.
  Proof.
    setoid_replace x with (x ⋅ ε) by by rewrite right_id.
    apply (increasing _).
  Qed.

  Global Instance uora_increasing_order_unit x : ε ≼ₒ x → Increasing x.
  Proof.
    intros Hx y.
    setoid_replace y with (ε ⋅ y) at 1 by by rewrite left_id.
    apply ora_order_op; auto.
  Qed.

  Lemma uora_unit_order_pcore x y : pcore x = Some y → ε ≼ₒ y.
  Proof.
    intros; apply uora_unit_order_increasing.
    by eapply ora_pcore_increasing.
  Qed.

  Global Instance uora_unit_ora_total : OraTotal A.
  Proof.
    intros x.
    destruct (ora_pcore_order_op ε ε x) as (?&Hc&_).
    apply ucmra_pcore_unit.
    rewrite -(left_id _ _ x) Hc; eauto.
  Qed.

  Lemma uora_unit_order_core x : ε ≼ₒ core x.
  Proof.
    destruct (ora_total x) as [z Heq]; rewrite /core Heq /=.
    apply uora_unit_order_increasing.
    by eapply ora_pcore_increasing.
  Qed.

  Lemma uora_core_order_op x y : core x ≼ₒ core (x ⋅ y).
  Proof.
    destruct (ora_total x) as [z Heq]; rewrite /core Heq /=.
    destruct (ora_pcore_order_op x z y) as (cxy&Hcxy&?); first by rewrite Heq.
    by rewrite Hcxy /=.
  Qed.

  Global Instance empty_oracancelable : OraCancelable (ε:A).
  Proof. intros ???. by rewrite !left_id. Qed.

  (* For big ops *)
  Global Instance ora_monoid : Monoid (@op A _) := cmra_monoid.
End uora.

#[export] Hint Immediate uora_unit_ora_total : core.

(*(** * Properties about CMRAs with Leibniz equality *)
Section ora_leibniz.
  Local Set Default Proof Using "Type*".
  Context {A : ora} `{!LeibnizEquiv A}.
  Implicit Types x y : A.

  Global Instance ora_assoc_L : Assoc (=) (@op A _).
  Proof. intros x y z. unfold_leibniz. by rewrite assoc. Qed.
  Global Instance ora_comm_L : Comm (=) (@op A _).
  Proof. intros x y. unfold_leibniz. by rewrite comm. Qed.

  Lemma ora_pcore_l_L x cx : pcore x = Some cx → cx ⋅ x = x.
  Proof. apply cmra_pcore_l_L. Qed.
  Lemma ora_pcore_idemp_L x cx : pcore x = Some cx → pcore cx = Some cx.
  Proof. apply cmra_pcore_idemp_L. Qed.

  Lemma ora_opM_assoc_L x y mz : (x ⋅ y) ⋅? mz = x ⋅ (y ⋅? mz).
  Proof. unfold_leibniz. apply ora_opM_assoc. Qed.

  (** ** Core *)
  Lemma ora_pcore_r_L x cx : pcore x = Some cx → x ⋅ cx = x.
  Proof. apply cmra_pcore_r_L. Qed.
  Lemma ora_pcore_dup_L x cx : pcore x = Some cx → cx = cx ⋅ cx.
  Proof. apply cmra_pcore_dup_L. Qed.

  (** ** CoreId elements *)
  Lemma oracore_id_dup_L x `{!OraCoreId x} : x = x ⋅ x.
  Proof. unfold_leibniz. by apply oracore_id_dup. Qed.

  (** ** Total core *)
  Section total_core.
    Context `{OraTotal A}.

    Lemma ora_core_r_L x : x ⋅ core x = x.
    Proof. unfold_leibniz. apply ora_core_r. Qed.
    Lemma ora_core_l_L x : core x ⋅ x = x.
    Proof. unfold_leibniz. apply ora_core_l. Qed.
    Lemma ora_core_idemp_L x : core (core x) = core x.
    Proof. unfold_leibniz. apply ora_core_idemp. Qed.
    Lemma ora_core_dup_L x : core x = core x ⋅ core x.
    Proof. unfold_leibniz. apply ora_core_dup. Qed.
    Lemma oracore_id_total_L x : OraCoreId x ↔ core x = x.
    Proof. unfold_leibniz. apply oracore_id_total. Qed.
    Lemma oracore_id_core_L x `{!OraCoreId x} : core x = x.
    Proof. by apply oracore_id_total_L. Qed.
  End total_core.
End ora_leibniz.

Section uora_leibniz.
  Local Set Default Proof Using "Type*".
  Context {A : uora} `{!LeibnizEquiv A}.
  Implicit Types x y z : A.

  Global Instance uora_unit_left_id_L : LeftId (=) ε (@op A _).
  Proof. intros x. unfold_leibniz. by rewrite left_id. Qed.
  Global Instance uora_unit_right_id_L : RightId (=) ε (@op A _).
  Proof. intros x. unfold_leibniz. by rewrite right_id. Qed.
End uora_leibniz.*)

(** * Constructing an ORA with total core *)
Section ora_total.
  Context A `{!Dist A, !Equiv A, !PCore A, !Op A, !Valid A, !ValidN A, OraOrder A, OraOrderN A}.
  Context (total : ∀ x : A, is_Some (pcore x)).
  Context (core_increasing : ∀ x, Increasing (core x)).
  Context (increasing_closed : ∀ n x y, Increasing x → x ≼ₒ{n} y → Increasing y).
  Context (core_monoN : ∀ n x y, x ≼ₒ{n} y → core x ≼ₒ{n} core y).
  Context (op_extend : ∀ (n : nat) (x y1 y2 : A),
              ✓{n} x → y1 ⋅ y2 ≼ₒ{n} x →
              ∃ z1 z2, z1 ⋅ z2 ≼ₒ{S n} x ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2).
  Context (extend_order : ∀ (n : nat) (x y : A),
              ✓{n} x → y ≼ₒ{n} x → ∃ z, z ≼ₒ{S n} x ∧ z ≡{n}≡ y).
  Context (dist_orderN : ∀ (n : nat) (x y : A), x ≡{n}≡ y → x ≼ₒ{n} y).
  Context (orderN_S : ∀ (n : nat) (x y : A), x ≼ₒ{S n} y → x ≼ₒ{n} y).
  Context (OrderN_trans : ∀ n : nat, Transitive (OraorderN n)).
  Context (orderN_op : ∀ (n : nat) (x x' y : A), x ≼ₒ{n} x' → x ⋅ y ≼ₒ{n} x' ⋅ y).
  Context (validN_orderN : ∀ (n : nat) (x y : A), ✓{n} x → y ≼ₒ{n} x → ✓{n} y).
  Context (order_orderN : ∀ x y : A, x ≼ₒ y ↔ (∀ n : nat, x ≼ₒ{n} y)).
  Context (pcore_order_op : ∀ x cx y : A,
              pcore x ≡ Some cx →
              ∃ cxy : A, pcore (x ⋅ y) ≡ Some cxy ∧ cx ≼ₒ cxy).
  Lemma ora_total_mixin : OraMixin A.
  Proof using Type*.
    split; auto.
    - intros x cx Hcx. pose proof (core_increasing x) as Hcx'.
      by rewrite /core Hcx /= in Hcx'.
    - intros n x y cx Hxy%(core_monoN n) Hx. move: Hxy.
      rewrite /core /= Hx /=. case (total y)=> [cy ->]; eauto.
  Qed.
End ora_total.

(** * Properties about morphisms *)
#[export] Instance ora_morphism_id {A : ora} : OraMorphism (@id A).
Proof. split=>//=. apply cmra_morphism_id. Qed.
#[export] Instance ora_morphism_proper {A B : ora} (f : A → B) `{!OraMorphism f} :
  Proper ((≡) ==> (≡)) f := ne_proper _.
#[export] Instance ora_morphism_compose {A B C : ora} (f : A → B) (g : B → C) :
  OraMorphism f → OraMorphism g → OraMorphism (g ∘ f).
Proof.
  split.
  - apply cmra_morphism_compose; apply _.
  - move=> n x Hx Hle /=. by apply ora_morphism_orderN, ora_morphism_orderN.
  - move=> x Hx /=.
    apply ora_morphism_increasing; eauto.
    apply ora_morphism_increasing; eauto.
Qed.

Section ora_morphism.
  Local Set Default Proof Using "Type*".
  Context {A B : ora} (f : A → B) `{!OraMorphism f}.

  Lemma ora_morphism_validN n (x : A) : ✓{n} x → ✓{n} f x.
  Proof. apply cmra_morphism_validN, _. Qed.
  Lemma ora_morphism_pcore (x : A) : f <$> pcore x ≡ pcore (f x).
  Proof. rewrite -cmra_morphism_pcore //. Qed.
  Lemma ora_morphism_op (x y : A) : f (x ⋅ y) ≡ f x ⋅ f y.
  Proof. apply @cmra_morphism_op, _. Qed.

  Lemma ora_morphism_core x : core (f x) ≡ f (core x).
  Proof. unfold core. rewrite -ora_morphism_pcore. by destruct (pcore x). Qed.
  Lemma ora_morphism_monotone x y : x ≼ₒ y → f x ≼ₒ f y.
  Proof.
    intros Hle. apply ora_order_orderN => n. apply ora_morphism_orderN; eauto.
    by eapply ora_order_orderN in Hle.
  Qed.
  Lemma ora_morphism_monotoneN n x y : x ≼ₒ{n} y → f x ≼ₒ{n} f y.
  Proof. by apply ora_morphism_orderN. Qed.
  Lemma ora_monotone_valid x : ✓ x → ✓ f x.
  Proof. rewrite !cmra_valid_validN; intros; apply ora_morphism_validN; auto. Qed.
End ora_morphism.

(** Functors *)
Record OrarFunctor := OraRFunctor {
  orarFunctor_car : ∀ A `{!Cofe A} B `{!Cofe B}, ora;
  orarFunctor_map `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} :
    ((A2 -n> A1) * (B1 -n> B2)) → orarFunctor_car A1 B1 -n> orarFunctor_car A2 B2;
  orarFunctor_map_ne `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} :
    NonExpansive (@orarFunctor_map A1 _ A2 _ B1 _ B2 _);
  orarFunctor_map_id `{!Cofe A, !Cofe B} (x : orarFunctor_car A B) :
    orarFunctor_map (cid,cid) x ≡ x;
  orarFunctor_map_compose `{!Cofe A1, !Cofe A2, !Cofe A3, !Cofe B1, !Cofe B2, !Cofe B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    orarFunctor_map (f◎g, g'◎f') x ≡ orarFunctor_map (g,g') (orarFunctor_map (f,f') x);
  orarFunctor_mor `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2}
      (fg : (A2 -n> A1) * (B1 -n> B2)) :
    OraMorphism (orarFunctor_map fg)
}.
#[export] Existing Instances orarFunctor_map_ne orarFunctor_mor.
#[export] Instance: Params (@orarFunctor_map) 5 := {}.

Declare Scope orarFunctor_scope.
Delimit Scope orarFunctor_scope with RF.
Bind Scope orarFunctor_scope with rFunctor.

Class OrarFunctorContractive (F : OrarFunctor) :=
  orarFunctor_map_contractive `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} ::
    Contractive (@orarFunctor_map F A1 _ A2 _ B1 _ B2 _).

Definition OrarFunctor_apply (F: OrarFunctor) (A: ofe) `{!Cofe A} : ora := orarFunctor_car F A A.
Coercion OrarFunctor_apply : OrarFunctor >-> Funclass.

Program Definition OraconstRF (B : ora) : OrarFunctor :=
  {| orarFunctor_car A1 _ A2 _ := B; orarFunctor_map A1 _ A2 _ B1 _ B2 _ f := cid |}.
Solve Obligations with done.
Coercion OraconstRF : ora >-> OrarFunctor.

#[export] Instance OraconstRF_contractive B : OrarFunctorContractive (OraconstRF B).
Proof. rewrite /OrarFunctorContractive; apply _. Qed.

Record uorarFunctor := UOraRFunctor {
  uorarFunctor_car : ∀ A `{!Cofe A} B `{!Cofe B}, uora;
  uorarFunctor_map `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} :
    ((A2 -n> A1) * (B1 -n> B2)) → uorarFunctor_car A1 B1 -n> uorarFunctor_car A2 B2;
  uorarFunctor_map_ne `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} :
    NonExpansive (@uorarFunctor_map A1 _ A2 _ B1 _ B2 _);
  uorarFunctor_map_id `{!Cofe A, !Cofe B} (x : uorarFunctor_car A B) :
    uorarFunctor_map (cid,cid) x ≡ x;
  uorarFunctor_map_compose `{!Cofe A1, !Cofe A2, !Cofe A3, !Cofe B1, !Cofe B2, !Cofe B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    uorarFunctor_map (f◎g, g'◎f') x ≡ uorarFunctor_map (g,g') (uorarFunctor_map (f,f') x);
  uorarFunctor_mor `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2}
      (fg : (A2 -n> A1) * (B1 -n> B2)) :
    OraMorphism (uorarFunctor_map fg)
}.
#[export] Existing Instances uorarFunctor_map_ne uorarFunctor_mor.
#[export] Instance: Params (@uorarFunctor_map) 5 := {}.

Declare Scope uorarFunctor_scope.
Delimit Scope uorarFunctor_scope with URF.
Bind Scope uorarFunctor_scope with uorarFunctor.

Class uorarFunctorContractive (F : uorarFunctor) :=
  uorarFunctor_map_contractive `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} ::
    Contractive (@uorarFunctor_map F A1 _ A2 _ B1 _ B2 _).

Definition uorarFunctor_apply (F: uorarFunctor) (A: ofe) `{!Cofe A} : uora :=
  uorarFunctor_car F A A.

Program Definition OraconstURF (B : uora) : uorarFunctor :=
  {| uorarFunctor_car A1 _ A2 _ := B; uorarFunctor_map A1 _ A2 _ B1 _ B2 _ f := cid |}.
Solve Obligations with done.
Coercion OraconstURF : uora >-> uorarFunctor.

#[export] Instance OraconstURF_contractive B : uorarFunctorContractive (OraconstURF B).
Proof. rewrite /uorarFunctorContractive; apply _. Qed.

(** * Transporting a CMRA equality *)
Definition ora_transport {A B : ora} (H : A = B) (x : A) : B :=
  eq_rect A id x _ H.

Lemma ora_transport_trans {A B C : ora} (H1 : A = B) (H2 : B = C) x :
  ora_transport H2 (ora_transport H1 x) = ora_transport (eq_trans H1 H2) x.
Proof. by destruct H2. Qed.

Section ora_transport.
  Context {A B : ora} (H : A = B).
  Notation T := (ora_transport H).
  Global Instance ora_transport_ne : NonExpansive T.
  Proof. by intros ???; destruct H. Qed.
  Global Instance ora_transport_proper : Proper ((≡) ==> (≡)) T.
  Proof. by intros ???; destruct H. Qed.
  Lemma ora_transport_op x y : T (x ⋅ y) = T x ⋅ T y.
  Proof. by destruct H. Qed.
  Lemma ora_transport_core x : T (core x) = core (T x).
  Proof. by destruct H. Qed.
  Lemma ora_transport_validN n x : ✓{n} T x ↔ ✓{n} x.
  Proof. by destruct H. Qed.
  Lemma ora_transport_valid x : ✓ T x ↔ ✓ x.
  Proof. by destruct H. Qed.
  Global Instance ora_transport_discrete x : Discrete x → Discrete (T x).
  Proof. by destruct H. Qed.
  Global Instance ora_transport_core_id x : OraCoreId x → OraCoreId (T x).
  Proof. by destruct H. Qed.
End ora_transport.

(** * Instances *)
(** ** Discrete ORA *)
Section mixin.
  Context (A : Type).

  Implicit Types (x : A).
  Local Set Primitive Projections.

  Record DORAMixin `{Equiv A, OraOrder A, PCore A, Op A, Valid A} := {
    (* setoids *)
    dora_core_increasing x cx : pcore x = Some cx → Increasing cx;
    dora_dist_order x y : x ≡ y → x ≼ₒ y;
    (* monoid *)
    dora_pcore_mono x y cx :
      x ≼ₒ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ₒ cy;
    (* order *)
    dora_order_trans : Transitive Oraorder;
    dora_order_op x x' y : x ≼ₒ x' → x ⋅ y ≼ₒ x' ⋅ y;
    dora_valid_orderN x y : ✓ x → y ≼ₒ x → ✓ y;
    dora_pcore_order_op x cx y :
      pcore x ≡ Some cx → ∃ cxy : A, pcore (x ⋅ y) ≡ Some cxy ∧ cx ≼ₒ cxy
  }.
End mixin.

Section discrete.
  Local Set Default Proof Using "Type*".
  Context `{Equiv A, OraOrder A, PCore A, Op A, Valid A} (Heq : @Equivalence A (≡)).
  Context (dora_mix : DORAMixin A).
  Existing Instances discrete_dist.
  Global Instance discrete_orderN : OraOrderN A := λ _ x y, x ≼ₒ y.

  Instance discrete_validN : ValidN A := λ n x, ✓ x.
  Definition discrete_ora_mixin : OraMixin A.
  Proof.
    destruct dora_mix; split; eauto; try done.
    - intros n x y Hx Hxy z. etrans; first apply Hx.
      eapply dora_order_op; eauto.
    - intros x; split; first done. by move=> /(_ 0).
  Qed.

  Context (ra_mix : RAMixin A).

  Instance discrete_ora_discrete :
    OraDiscrete (Ora' A (discrete_ofe_mixin Heq) (discrete_cmra_mixin Heq ra_mix) discrete_ora_mixin).
  Proof. split; try done. apply _. Qed.
End discrete.

(** A smart constructor for the discrete RA over a carrier [A]. It uses *)
(* [ofe_discrete_equivalence_of A] to make sure the same [Equivalence] proof is *)
(* used as when constructing the OFE. *)
Notation discreteOra A ra_mix :=
  (Ora A (discrete_ora_mixin (discrete_ofe_equivalence_of A%type) ra_mix))
  (only parsing).

Section dora_total.
  Local Set Default Proof Using "Type*".
  Context A `{Equiv A, PCore A, Op A, Valid A, OraOrder A}.
  Context (total : ∀ x : A, is_Some (pcore x)).
  Context (core_increasing : ∀ x cx, pcore x = Some cx → Increasing cx).
  Context (dora_dist_order : ∀ x y, x ≡ y → x ≼ₒ y).
  Context (core_mono_order : ∀ x y : A, x ≼ₒ y → core x ≼ₒ core y).
  Context (order_trans : Transitive Oraorder).
  Context (orderN_op : ∀ x x' y, x ≼ₒ x' → x ⋅ y ≼ₒ x' ⋅ y).
  Context (validN_orderN : ∀ x y, ✓ x → y ≼ₒ x → ✓ y).
  Context (pcore_order_op : ∀ x cx y,
              pcore x ≡ Some cx →
              ∃ cxy : A, pcore (x ⋅ y) ≡ Some cxy ∧ cx ≼ₒ cxy).

  Lemma dora_total_mixin : DORAMixin A.
  Proof.
    split; auto.
    - intros x y cx Hxy%core_mono_order Hx. move: Hxy.
      rewrite /core /= Hx /=. case (total y)=> [cy ->]; eauto.
  Qed.
End dora_total.

(** ** CMRA for the unit type *)
Section unit.
  Instance unit_valid : Valid () := λ x, True.
  Instance unit_validN : ValidN () := λ n x, True.
  Instance unit_pcore : PCore () := λ x, Some x.
  Instance unit_op : Op () := λ x y, ().
  Instance unit_order : OraOrder () := λ _ _, True.
  Lemma unit_ora_mixin : OraMixin ().
  Proof.
    apply discrete_ora_mixin, dora_total_mixin; try by eauto.
    intros [] [] []; eauto.
  Qed.
  Canonical Structure unitR : ora := Ora unit unit_ora_mixin.

  Instance unit_unit : Unit () := ().
  Lemma unit_uora_mixin : UcmraMixin ().
  Proof. done. Qed.
  Canonical Structure unitUR : uora := Uora unit unit_uora_mixin.

  Global Instance unit_cmra_discrete : OraDiscrete unitR.
  Proof. done. Qed.
  Global Instance unit_core_id (x : ()) : OraCoreId x.
  Proof. by constructor. Qed.
  Global Instance unit_cancelable (x : ()) : OraCancelable x.
  Proof. by constructor. Qed.
End unit.

(** ** Natural numbers *)
Section nat.
  Instance nat_valid : Valid nat := λ x, True.
  Instance nat_validN : ValidN nat := λ n x, True.
  Instance nat_pcore : PCore nat := λ x, Some 0.
  Instance nat_op : Op nat := plus.
  Instance nat_order : OraOrder nat := le.
  Definition nat_op_plus x y : x ⋅ y = x + y := eq_refl.
  Lemma nat_order_le (x y : nat) : x ≼ₒ y ↔ x ≤ y.
  Proof. trivial. Qed.
  Lemma nat_dora_mixin : DORAMixin nat.
  Proof.
    apply dora_total_mixin; try apply _; rewrite /op /nat_op /Oraorder /nat_order;
      try by eauto with lia.
    - intros ? ? Hc. inversion Hc; subst. by cbv.
    - intros x y z. erewrite leibniz_equiv; eauto.
  Qed.
  Canonical Structure natR : ora := discreteOra nat nat_dora_mixin.

  Global Instance nat_ora_discrete : OraDiscrete natR.
  Proof. apply discrete_ora_discrete. Qed.

  Instance nat_unit : Unit nat := 0.
  Lemma nat_uora_mixin : UcmraMixin nat.
  Proof. split; apply _ || done. Qed.
  Canonical Structure natUR : uora := Uora nat nat_ucmra_mixin.

  Global Instance nat_cancelable (x : nat) : OraCancelable x.
  Proof. by intros ???? ?%Nat.add_cancel_l. Qed.

  Lemma nat_local_update (x y x' y' : nat) :
    x + y' = x' + y → (x,y) ~l~> (x',y').
  Proof.
    intros ??; apply local_update_unital_discrete=> z _.
    compute -[minus plus]; lia.
  Qed.

  (* This one has a higher precendence than [is_op_op] so we get a [+] instead
     of an [⋅]. *)
  Global Instance nat_is_op (n1 n2 : nat) : IsOp (n1 + n2) n1 n2.
  Proof. done. Qed.

End nat.

Definition mnat := nat.

Section mnat.
  Instance mnat_unit : Unit mnat := 0.
  Instance mnat_valid : Valid mnat := λ x, True.
  Instance mnat_validN : ValidN mnat := λ n x, True.
  Instance mnat_pcore : PCore mnat := Some.
  Instance mnat_op : Op mnat := Nat.max.
  Instance mnat_order : OraOrder mnat := le.
  Definition mnat_op_max x y : x ⋅ y = x `max` y := eq_refl.
  Lemma mnat_order_le (x y : mnat) : x ≼ₒ y ↔ x ≤ y.
  Proof. done. Qed.

  Lemma mnat_ra_mixin : RAMixin mnat.
  Proof.
    apply ra_total_mixin; try apply _; rewrite /op /mnat_op /Oraorder /mnat_order;
      try by eauto with lia.
    - intros x y z. apply Nat.max_assoc.
    - intros x y. apply Nat.max_comm.
    - intros x. apply Nat.max_id.
  Qed.

  Lemma mnat_dora_mixin : DORAMixin mnat.
  Proof.
    apply dora_total_mixin; try apply _; rewrite /op /mnat_op /Oraorder /mnat_order;
      try by eauto with lia.
    - intros ? ? Hc z. inversion Hc; subst.
      apply PeanoNat.Nat.le_max_r.
    - intros x y z. erewrite leibniz_equiv; eauto.
    - rewrite /pcore /mnat_pcore; inversion 1; subst.
      setoid_subst. eauto with lia.
  Qed.
  Canonical Structure mnatR : ora :=
    Ora' mnat (discrete_ofe_mixin _) (discrete_cmra_mixin _ mnat_ra_mixin) (discrete_ora_mixin _ mnat_dora_mixin).

  Global Instance mnat_ora_discrete : OraDiscrete mnatR.
  Proof. apply discrete_ora_discrete. Qed.

  Lemma mnat_ucmra_mixin : UcmraMixin mnat.
  Proof. split; apply _ || done. Qed.
  Canonical Structure mnatUR : uora :=
    Uora' mnat (discrete_ofe_mixin _) (discrete_cmra_mixin _ mnat_ra_mixin) (discrete_ora_mixin _ mnat_dora_mixin) mnat_ucmra_mixin.

  Global Instance mnat_core_id (x : mnat) : OraCoreId x.
  Proof. by constructor. Qed.
End mnat.

(** ** Positive integers. *)
Section positive.
  Instance pos_valid : Valid positive := λ x, True.
  Instance pos_validN : ValidN positive := λ n x, True.
  Instance pos_pcore : PCore positive := λ x, None.
  Instance pos_op : Op positive := Pos.add.
  Instance pos_order : OraOrder positive := Pos.le.
  Definition pos_op_plus x y : x ⋅ y = (x + y)%positive := eq_refl.
  (* Note this is weaker than cmra version of positive whose order is <. *)
  Lemma pos_order_le (x y : positive) : x ≼ₒ y ↔ (x ≤ y)%positive.
  Proof. done. Qed.
  Lemma pos_dora_mixin : DORAMixin positive.
  Proof.
    split; try by eauto; try apply _.
    - intros x y. inversion 1; subst. unfold Oraorder, pos_order.
      lia.
    - intros ? ? ?. unfold Oraorder, pos_order.
      apply Pos.add_le_mono_r.
  Qed.
  Canonical Structure positiveR : ora := discreteOra positive pos_dora_mixin.

  Global Instance pos_cmra_discrete : OraDiscrete positiveR.
  Proof. apply discrete_ora_discrete. Qed.

  Global Instance pos_cancelable (x : positive) : OraCancelable x.
  Proof. intros n y z ??. by eapply Pos.add_reg_l, leibniz_equiv. Qed.
  Global Instance pos_id_free (x : positive) : OraIdFree x.
  Proof.
    intros y ??. apply (Pos.add_no_neutral x y). rewrite Pos.add_comm.
    by apply leibniz_equiv.
  Qed.
End positive.

(** Product *)
Section prod.
  Context {A B : ora}.
  Local Arguments pcore _ _ !_ /.
  Local Arguments prod_pcore_instance _ _ !_/.
  Local Arguments cmra_car _ /.
  Local Arguments cmra_pcore _ / _.
  Local Arguments ora_pcore _ !_/.

  Lemma prod_pcore_Some (x cx : A * B) :
    pcore x = Some cx ↔ pcore (x.1) = Some (cx.1) ∧ pcore (x.2) = Some (cx.2).
  Proof. apply prod_pcore_Some. Qed.
  Lemma prod_pcore_Some' (x cx : A * B) :
    pcore x ≡ Some cx ↔ pcore (x.1) ≡ Some (cx.1) ∧ pcore (x.2) ≡ Some (cx.2).
  Proof. apply @prod_pcore_Some'. Qed.

  Instance prod_order : OraOrder (A * B) := λ x y, x.1 ≼ₒ y.1 ∧ x.2 ≼ₒ y.2.
  Instance prod_orderN : OraOrderN (A * B) := λ n x y, x.1 ≼ₒ{n} y.1 ∧ x.2 ≼ₒ{n} y.2.

  Definition prod_ora_mixin : OraMixin (A * B).
  Proof.
    split; try apply _.
    - intros [x1 x2] [cx1 cx2] Hcx [z1 z2]; simpl.
      apply prod_pcore_Some in Hcx; destruct Hcx as [Hcx1 Hcx2]; simpl in *.
      split; simpl; eapply ora_pcore_increasing; eauto.
    - intros n [x1 x2] [y1 y2] Hx [Hxy1 Hxy2]; simpl in *.
      assert (Increasing x1) as Hx1i.
      { intros z. by destruct (Hx (z, y2)) as [Hz _]. }
      assert (Increasing x2) as Hx2i.
      { intros z. by destruct (Hx (y1, z)) as [_ Hz]. }
      intros [z1 z2]; split; simpl.
      + eapply ora_increasing_closed; eauto.
      + eapply ora_increasing_closed; eauto.
    - intros n [x1 x2] [??] cx [??] Hcx; simpl in *.
      destruct (pcore x1) as [|] eqn:Heqx1; last done.
      destruct (pcore x2) as [|] eqn:Heqx2; last done.
      simpl in *; simplify_eq.
      edestruct (ora_pcore_monoN n x1) as [cy1 [Hcy1 ?]]; eauto.
      edestruct (ora_pcore_monoN n x2) as [cy2 [Hcy2 ?]]; eauto.
      eexists (cy1, cy2). rewrite Hcy1 Hcy2 /=; repeat split; auto.
    - intros n [x1 x2] [y11 y12] [y21 y22] [? ?] [? ?]; simpl in *.
      destruct (ora_op_extend n x1 y11 y21) as (z11&z12&Hz1eq&?&?); auto.
      destruct (ora_op_extend n x2 y12 y22) as (z21&z22&Hz2eq&?&?); auto.
      exists (z11, z21), (z12, z22); repeat split; simpl; auto.
    - intros n [x1 x2] [y1 y2] [??] [??]; simpl in *.
      destruct (ora_extend n x1 y1) as [z1 [? ?]]; auto.
      destruct (ora_extend n x2 y2) as [z2 [? ?]]; auto.
      exists (z1, z2); done.
    - intros ??? [??]; split; by apply ora_dist_orderN.
    - intros ??? [??]; split; by apply ora_orderN_S.
    - intros ???? [??]; split; by apply ora_orderN_op.
    - intros ??? [??] [??]; split; by eapply ora_validN_orderN.
    - intros ? ?; split.
      + intros [??] ?; split; by apply ora_order_orderN.
      + intros Hxy; split; apply ora_order_orderN => m; by destruct (Hxy m).
    - intros [x1 x2] [cx1 cx2] [y1 y2]; simpl.
      destruct (pcore x1) as [|] eqn:Heqx1; last by inversion 1.
      destruct (pcore x2) as [|] eqn:Heqx2; last by inversion 1.
      inversion 1 as [? ? Heq|]; simplify_eq.
      inversion Heq; simpl in *.
      destruct (ora_pcore_order_op x1 cx1 y1) as [cxy1 [Hcxy1 ?]];
        first by setoid_subst; rewrite Heqx1.
      destruct (ora_pcore_order_op x2 cx2 y2) as [cxy2 [Hcxy2 ?]];
        first by setoid_subst; rewrite Heqx2.
      exists (cxy1, cxy2); simpl.
      destruct (pcore (x1 ⋅ y1)); last by inversion Hcxy1.
      destruct (pcore (x2 ⋅ y2)); last by inversion Hcxy2.
      simpl; repeat split; eauto.
      apply Some_proper; split; simpl; apply Some_equiv_inj; eauto.
  Qed.
  Canonical Structure prodR := Ora (prod A B) prod_ora_mixin.

  Lemma pair_op (a a' : A) (b b' : B) : (a, b) ⋅ (a', b') = (a ⋅ a', b ⋅ b').
  Proof. done. Qed.

  Global Instance prod_ora_total : OraTotal A → OraTotal B → OraTotal prodR.
  Proof.
    intros H1 H2 [a b]. destruct (H1 a) as [ca ?], (H2 b) as [cb ?].
    exists (ca,cb). by simplify_option_eq.
  Qed.

  Global Instance prod_ora_discrete :
    OraDiscrete A → OraDiscrete B → OraDiscrete prodR.
  Proof.
    split. apply _.
    by intros ? []; split; apply ora_discrete_valid.
    by intros ? ? []; split; apply ora_discrete_order.
  Qed.

  Global Instance pair_increasing x y :
    Increasing x → Increasing y → Increasing (x,y).
  Proof. split; auto. Qed.

  Global Instance pair_core_id x y :
    OraCoreId x → OraCoreId y → OraCoreId (x,y).
  Proof. by rewrite /OraCoreId prod_pcore_Some'. Qed.

  Global Instance pair_exclusive_l x y : OraExclusive x → OraExclusive (x,y).
  Proof. by intros ?[][?%oraexclusive0_l]. Qed.
  Global Instance pair_exclusive_r x y : OraExclusive y → OraExclusive (x,y).
  Proof. by intros ?[][??%oraexclusive0_l]. Qed.

  Global Instance pair_cancelable x y :
    OraCancelable x → OraCancelable y → OraCancelable (x,y).
  Proof.
    intros ???[][][][]. constructor; simpl in *; by eapply oracancelableN.
  Qed.

  Global Instance pair_id_free_l x y : OraIdFree x → OraIdFree (x,y).
  Proof. move=>? [??] [? _] [/=? _]. eauto. Qed.
  Global Instance pair_id_free_r x y : OraIdFree y → OraIdFree (x,y).
  Proof. move=>? [??] [_ ?] [_ /=?]. eauto. Qed.
End prod.

Arguments prodR : clear implicits.

Section prod_unit.
  Context {A B : uora}.

  Instance prod_unit `{Unit A, Unit B} : Unit (A * B) := (ε, ε).
  Lemma prod_ucmra_mixin : UcmraMixin (A * B).
  Proof.
    split.
    - split; apply ucmra_unit_valid.
    - by split; rewrite /=left_id.
    - rewrite prod_pcore_Some'; split; apply (oracore_id _).
  Qed.
  Canonical Structure prodUR := Uora' (prod A B) (ofe_mixin_of (A * B)) (@prod_cmra_mixin A B) prod_ora_mixin prod_ucmra_mixin.

  Lemma pair_split (x : A) (y : B) : (x, y) ≡ (x, ε) ⋅ (ε, y).
  Proof. by rewrite pair_op left_id right_id. Qed.

  Lemma pair_split_L `{!LeibnizEquiv A, !LeibnizEquiv B} (x : A) (y : B) :
    (x, y) = (x, ε) ⋅ (ε, y).
  Proof. unfold_leibniz. apply pair_split. Qed.
End prod_unit.

Arguments prodUR : clear implicits.

#[export] Instance prod_map_cmra_morphism {A A' B B' : ora} (f : A → A') (g : B → B') :
  OraMorphism f → OraMorphism g → OraMorphism (prod_map f g).
Proof.
  split; first apply _.
  - intros n x y [??]; split; simpl; apply ora_morphism_orderN; auto.
  - intros x Hx [z1 z2]; split; simpl.
    + eapply ora_morphism_increasing; eauto.
      { intros z. destruct (Hx (z, x.2)); simpl in *; auto. }
    + eapply ora_morphism_increasing; eauto.
      { intros z. destruct (Hx (x.1, z)); simpl in *; auto. }
Qed.

Program Definition prodRF (F1 F2 : OrarFunctor) : OrarFunctor := {|
  orarFunctor_car A _ B _ := prodR (orarFunctor_car F1 A B) (orarFunctor_car F2 A B);
  orarFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    prodO_map (orarFunctor_map F1 fg) (orarFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 A1 ? A2 ? B1 ? B2 ? n ???. by apply prodO_map_ne; apply orarFunctor_map_ne.
Qed.
Next Obligation. by intros F1 F2 A ? B ? [??]; rewrite /= !orarFunctor_map_id. Qed.
Next Obligation.
  intros F1 F2 A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' [??]; simpl.
  by rewrite !orarFunctor_map_compose.
Qed.
Notation "F1 * F2" := (prodRF F1%RF F2%RF) : rFunctor_scope.

#[export] Instance prodRF_contractive F1 F2 :
  OrarFunctorContractive F1 → OrarFunctorContractive F2 →
  OrarFunctorContractive (prodRF F1 F2). 
Proof.
  intros ?? A1 ? A2 ? B1 ? B2 ? n ???;
    by apply prodO_map_ne; apply orarFunctor_map_contractive.
Qed.

Program Definition prodURF (F1 F2 : uorarFunctor) : uorarFunctor := {|
  uorarFunctor_car A _ B _ := prodUR (uorarFunctor_car F1 A B) (uorarFunctor_car F2 A B);
  uorarFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    prodO_map (uorarFunctor_map F1 fg) (uorarFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 A1 ? A2 ? B1 ? B2 ? n ???. by apply prodO_map_ne; apply uorarFunctor_map_ne.
Qed.
Next Obligation. by intros F1 F2 A ? B ? [??]; rewrite /= !uorarFunctor_map_id. Qed.
Next Obligation.
  intros F1 F2 A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' [??]; simpl.
  by rewrite !uorarFunctor_map_compose.
Qed.
Notation "F1 * F2" := (prodURF F1%URF F2%URF) : urFunctor_scope.

#[export] Instance prodURF_contractive F1 F2 :
  uorarFunctorContractive F1 → uorarFunctorContractive F2 →
  uorarFunctorContractive (prodURF F1 F2).
Proof.
  intros ?? A1 ? A2 ? B1 ? B2 ? n ???;
    by apply prodO_map_ne; apply uorarFunctor_map_contractive.
Qed.

(** ** CMRA for the option type *)
Section option.
  Context {A : ora}.
  Implicit Types a b : A.
  Implicit Types ma mb : option A.
  Local Arguments core _ _ !_ /.
  Local Arguments option_pcore_instance _ !_/.
  Local Arguments cmra_car _ /.
  Local Arguments cmra_pcore _ / _.
  Local Arguments pcore _ _ !_ /.

  Instance option_valid : Valid (option A) := λ ma,
    match ma with Some a => ✓ a | None => True end.
  Instance option_validN : ValidN (option A) := λ n ma,
    match ma with Some a => ✓{n} a | None => True end.
  Instance option_pcore : PCore (option A) := λ ma, Some (ma ≫= pcore).
  Arguments option_pcore !_ /.
  Instance option_op : Op (option A) := union_with (λ a b, Some (a ⋅ b)).
  Instance option_order : OraOrder (option A) :=
    λ x y,
    match x with
    | None =>
      match y with
      | None => True
      | Some y' => Increasing y'
      end
    | Some x' =>
      match y with
      | None => False
      | Some y' => x' ≼ₒ y'
      end
    end.
  Instance option_orderN : OraOrderN (option A) :=
    λ n x y,
    match x with
    | None =>
      match y with
      | None => True
      | Some y' => Increasing y'
      end
    | Some x' =>
      match y with
      | None => False
      | Some y' => x' ≼ₒ{n} y'
      end
    end.

  Definition Some_valid a : ✓ Some a ↔ ✓ a := reflexivity _.
  Definition Some_validN a n : ✓{n} Some a ↔ ✓{n} a := reflexivity _.
  Definition Some_op a b : Some (a ⋅ b) = Some a ⋅ Some b := eq_refl.
  Lemma Some_core `{OraTotal A} a : Some (core a) = core (Some a).
  Proof. rewrite /core /=. by destruct (ora_total a) as [? ->]. Qed.
  Lemma Some_op_opM a ma : Some a ⋅ ma = Some (a ⋅? ma).
  Proof. by destruct ma. Qed.

 Lemma option_included ma mb :
    ma ≼ mb ↔ ma = None ∨ ∃ a b, ma = Some a ∧ mb = Some b ∧ (a ≡ b ∨ a ≼ b).
  Proof.
    split.
    - intros [mc Hmc].
      destruct ma as [a|]; [right|by left].
      destruct mb as [b|]; [exists a, b|destruct mc; inversion_clear Hmc].
      destruct mc as [c|]; inversion_clear Hmc; split_and?; auto.
      right; eexists; eauto.
    - intros [->|(a&b&->&->&[Hc|[c Hc]])].
      + exists mb. by destruct mb.
      + exists None; by constructor.
      + exists (Some c); by constructor.
  Qed.

  Lemma option_includedN n ma mb :
    ma ≼{n} mb ↔ ma = None ∨ ∃ x y, ma = Some x ∧ mb = Some y ∧ (x ≡{n}≡ y ∨ x ≼{n} y).
  Proof.
    split.
    - intros [mc Hmc].
      destruct ma as [a|]; [right|by left].
      destruct mb as [b|]; [exists a, b|destruct mc; inversion_clear Hmc].
      destruct mc as [c|]; inversion_clear Hmc; split_and?; auto.
      right; eexists; eauto.
    - intros [->|(a&y&->&->&[Hc|[c Hc]])].
      + exists mb. by destruct mb.
      + exists None; by constructor.
      + exists (Some c); by constructor.
  Qed.

  Lemma option_order' ma mb :
    ma ≼ₒ mb ↔ (ma = None ∧ (mb = None ∨ ∃ b, mb = Some b ∧ Increasing b)) ∨
    ∃ a b, ma = Some a ∧ mb = Some b ∧ a ≼ₒ b.
  Proof.
    split.
    - destruct ma as [ma|]; destruct mb as [mb|]; try done; auto.
      + right; eexists _, _; eauto.
      + left; split; eauto.
    - intros [[-> [->|[?[->?]]]]|[?[?[?[??]]]]]; subst; auto.
  Qed.

  Lemma option_orderN' n ma mb :
    ma ≼ₒ{n} mb ↔ (ma = None ∧ (mb = None ∨ ∃ b, mb = Some b ∧ Increasing b)) ∨
    ∃ a b, ma = Some a ∧ mb = Some b ∧ a ≼ₒ{n} b.
  Proof.
    split.
    - destruct ma as [ma|]; destruct mb as [mb|]; try done; auto.
      + right; eexists _, _; eauto.
      + left; split; eauto.
    - intros [[-> [->|[?[->?]]]]|[?[?[?[??]]]]]; subst; auto.
  Qed.

  Lemma Some_increasing a : Increasing a ↔ Increasing (Some a).
  Proof.
    split; intros Ha.
    - intros [z|]; last by auto. apply Ha.
    - intros z. by specialize (Ha (Some z)).
  Qed.

  Lemma None_increasing : Increasing None.
  Proof.
    intros [a|]; last done. apply ora_order_refl.
  Qed.

(*  Lemma Some_increasingN n a : Increasing a ↔ IncreasingN n (Some a).
  Proof.
    split; intros Ha.
    - intros [z|]; last by auto. apply ora_order_orderN, Ha.
    - intros z. hnf in Ha. by specialize (Ha (Some z)).
  Qed. *)

  Lemma option_ora_mixin : OraMixin (option A).
  Proof.
    apply ora_total_mixin; try apply optionR; try apply _; auto.
    - intros [x|] [z|]; simpl; auto.
      + destruct (pcore x) as [cx|] eqn:Heq;
          first by eapply ora_pcore_increasing.
        apply ora_order_refl.
      + destruct (pcore x) as [cx|] eqn:Heq; last done;
          by eapply ora_pcore_increasing.
      + apply ora_order_refl.
    - intros n [x|] [y|] Hx Hxy; try done.
      + apply Some_increasing in Hx. apply Some_increasing.
        eapply ora_increasing_closed; eauto.
      + apply Some_increasing. apply Hxy.
    - intros n ma mb; setoid_rewrite option_orderN'.
      intros [[-> [->|[? [Heq ?]]]]|[a [b [Ha [Hb Ho]]]]]; subst; simpl; eauto.
      + left; split; trivial.
        destruct (pcore x) as [cx|] eqn:Heqn; auto.
        right; eexists cx; split; eauto using ora_pcore_increasing.
      + destruct (pcore a) as [ca|] eqn:Heqa.
        * right. destruct (ora_pcore_monoN n a b ca); eauto.
        * left; split; auto.
          destruct (pcore b) as [cb|] eqn:Heqb; auto.
          right; eexists; split; eauto using ora_pcore_increasing.
    - intros n [x|] [y1|] [y2|] Hx; rewrite /op /OraorderN /= => Hysx; try tauto.
      * destruct (ora_op_extend n x y1 y2) as (z1&z2&?&?&?); auto.
        exists (Some z1), (Some z2); simpl; repeat split; by try apply Some_ne.
      * destruct (ora_extend n x y1) as [z1 [Hz1 Hz1']]; auto.
        exists (Some z1), None; simpl; repeat split; auto.
        by apply Some_ne.
      * destruct (ora_extend n x y2) as [z2 [Hz2 Hz2']]; auto.
        exists None, (Some z2); simpl; repeat split; auto.
        by apply Some_ne.
      * exists None, None; repeat split; auto.
      * exists None, None; repeat split; auto.
    - intros n [x|] [y|] Hx; rewrite /OraorderN /= => Hysx; try tauto.
      * destruct (ora_extend n x y) as [z [Hz Hz']]; auto.
        exists (Some z); simpl; repeat split; auto.
        by apply Some_ne.
      * exists None; auto.
      * exists None; auto.
    - intros n [x|] [y|]; try (by inversion 1).
      intros Hxy. apply ora_dist_orderN.
      by apply Some_dist_inj.
    - intros n [x|] [y|]; intros Hxy; try done.
        by apply ora_orderN_S.
    - intros n [x|] [y|] [z|]; intros Hxy Hyz; try done.
      * eapply ora_orderN_trans; eauto.
      * eapply ora_increasing_closed; eauto.
    - intros n [x|] [x'|] [y|]; intros Hxx'; try done.
      * by apply ora_orderN_op.
      * apply ora_order_orderN; auto.
      * apply ora_orderN_refl.
    - intros n [x|] [y|]; try done.
      intros; eapply ora_validN_orderN; eauto.
    - intros [x|] [y|]; try done.
      * apply ora_order_orderN.
      * split; auto. intros Hx; apply (Hx 0).
      * split; auto. intros Hx; apply (Hx 0).
    - intros [x|] [cx|] [y|] Hcx; try done; simpl in *; simplify_eq.
      + inversion Hcx; subst.
        destruct (ora_pcore_order_op x cx y) as [z [Hz Hz']]; auto.
        exists (Some z). rewrite Hz. split; eauto.
      + eexists (Some cx); split; eauto.
        rewrite /Oraorder /=; apply ora_order_refl.
      + destruct (pcore (x ⋅ y)) as [z|] eqn:Heq.
        * exists (Some z); split; eauto. eapply ora_pcore_increasing; eauto.
        * exists None; split; auto.
      + exists None; rewrite Hcx; auto.
      + inversion Hcx as [? ? Heq'|]; inversion Heq'.
      + inversion Hcx as [? ? Heq'|]; inversion Heq'.
      + destruct (pcore y) as [cy|] eqn:Heq.
        * exists (Some cy); split; auto. eapply ora_pcore_increasing; eauto.
        * exists None; auto.
      + exists None; auto.
  Qed.

  Canonical Structure optionR := Ora (option A) option_ora_mixin.

  Global Instance option_cmra_discrete : OraDiscrete A → OraDiscrete optionR.
  Proof.
    split; [apply _| |].
    by intros [a|]; [apply (ora_discrete_valid a)|].
    by intros [a|] [b|]; [apply (ora_discrete_order a)| | |].
 Qed.

  Instance option_unit : Unit (option A) := None.
  Lemma option_uora_mixin : UcmraMixin optionR.
  Proof. split. done. by intros []. done. Qed.
  Canonical Structure optionUR := Uora (option A) option_uora_mixin.

  (** Misc *)
  Lemma op_None ma mb : ma ⋅ mb = None ↔ ma = None ∧ mb = None.
  Proof. destruct ma, mb; naive_solver. Qed.
  Lemma op_is_Some ma mb : is_Some (ma ⋅ mb) ↔ is_Some ma ∨ is_Some mb.
  Proof. rewrite -!not_eq_None_Some op_None. destruct ma, mb; naive_solver. Qed.

  Lemma cmra_opM_assoc' a mb mc : a ⋅? mb ⋅? mc ≡ a ⋅? (mb ⋅ mc).
  Proof. destruct mb, mc; by rewrite /= -?assoc. Qed.

  Global Instance Some_core_id a : OraCoreId a → OraCoreId (Some a).
  Proof. by constructor. Qed.
  Global Instance option_core_id ma : (∀ x : A, OraCoreId x) → OraCoreId ma.
  Proof. intros. destruct ma; apply _. Qed.

  Lemma OraexclusiveN_Some_l n a `{!OraExclusive a} mb :
    ✓{n} (Some a ⋅ mb) → mb = None.
  Proof. destruct mb. move=> /(OraexclusiveN_l _ a) []. done. Qed.
  Lemma OraexclusiveN_Some_r n a `{!OraExclusive a} mb :
    ✓{n} (mb ⋅ Some a) → mb = None.
  Proof. rewrite comm. by apply OraexclusiveN_Some_l. Qed.

  Lemma Oraexclusive_Some_l a `{!OraExclusive a} mb : ✓ (Some a ⋅ mb) → mb = None.
  Proof. destruct mb. move=> /(Oraexclusive_l a) []. done. Qed.
  Lemma Oraexclusive_Some_r a `{!OraExclusive a} mb : ✓ (mb ⋅ Some a) → mb = None.
  Proof. rewrite comm. by apply Oraexclusive_Some_l. Qed.

  Lemma Some_includedN n a b : Some a ≼{n} Some b ↔ a ≡{n}≡ b ∨ a ≼{n} b.
  Proof. rewrite option_includedN; naive_solver. Qed.
  Lemma Some_included a b : Some a ≼ Some b ↔ a ≡ b ∨ a ≼ b.
  Proof. rewrite option_included; naive_solver. Qed.
  Lemma Some_included_2 a b : a ≼ b → Some a ≼ Some b.
  Proof. rewrite Some_included; eauto. Qed.


  Lemma Some_orderN n a b : Some a ≼ₒ{n} Some b ↔ a ≼ₒ{n} b.
  Proof. rewrite option_orderN'; naive_solver. Qed.
  Lemma Some_order a b : Some a ≼ₒ Some b ↔ a ≼ₒ b.
  Proof. rewrite option_order'; naive_solver. Qed.
  Lemma Some_order_2 a b : a ≼ₒ b → Some a ≼ₒ Some b.
  Proof. rewrite Some_order; eauto. Qed.

  Lemma Some_orderN_total `{OraTotal A} n a b : Some a ≼ₒ{n} Some b ↔ a ≼ₒ{n} b.
  Proof. by rewrite Some_orderN. Qed.
  Lemma Some_order_total `{OraTotal A} a b : Some a ≼ₒ Some b ↔ a ≼ₒ b.
  Proof. by rewrite Some_order. Qed.

  Lemma Some_includedN_exclusive n a `{!OraExclusive a} b :
    Some a ≼{n} Some b → ✓{n} b → a ≡{n}≡ b.
  Proof. move=> /Some_includedN [//|/Oraexclusive_includedN]; tauto. Qed.
  Lemma Some_included_exclusive a `{!OraExclusive a} b :
    Some a ≼ Some b → ✓ b → a ≡ b.
  Proof. move=> /Some_included [//|/Oraexclusive_included]; tauto. Qed.

  Lemma is_Some_includedN n ma mb : ma ≼{n} mb → is_Some ma → is_Some mb.
  Proof. rewrite -!not_eq_None_Some option_includedN. naive_solver. Qed.
  Lemma is_Some_included ma mb : ma ≼ mb → is_Some ma → is_Some mb.
  Proof. rewrite -!not_eq_None_Some option_included. naive_solver. Qed.

  Lemma is_Some_orderN n ma mb : ma ≼ₒ{n} mb → is_Some ma → is_Some mb.
  Proof. rewrite -!not_eq_None_Some option_orderN'. naive_solver. Qed.
  Lemma is_Some_includedorder ma mb : ma ≼ₒ mb → is_Some ma → is_Some mb.
  Proof. rewrite -!not_eq_None_Some option_order'. naive_solver. Qed.

  Global Instance cancelable_Some a :
    OraIdFree a → OraCancelable a → OraCancelable (Some a).
  Proof.
    intros Hirr ?? [b|] [c|] ? EQ; inversion_clear EQ.
    - constructor. by apply (oracancelableN a).
    - destruct (Hirr b); [|eauto using dist_le with lia].
      by eapply (cmra_validN_op_l 0 a b), (cmra_validN_le n); last lia.
    - destruct (Hirr c); [|symmetry; eauto using dist_le with lia].
      by eapply (cmra_validN_le n); last lia.
    - done.
  Qed.
End option.

Arguments optionR : clear implicits.
Arguments optionUR : clear implicits.

(* Section option_prod. *)
(*   Context {A B : ora}. *)
(*   Implicit Types a : A. *)
(*   Implicit Types b : B. *)

(*   Lemma Some_pair_includedN n a1 a2 b1 b2 : *)
(*     Some (a1,b1) ≼{n} Some (a2,b2) → Some a1 ≼{n} Some a2 ∧ Some b1 ≼{n} Some b2. *)
(*   Proof. rewrite !Some_includedN. intros [[??]|[??]%prod_includedN]; eauto. Qed. *)
(*   Lemma Some_pair_includedN_total_1 `{OraTotal A} n a1 a2 b1 b2 : *)
(*     Some (a1,b1) ≼{n} Some (a2,b2) → a1 ≼{n} a2 ∧ Some b1 ≼{n} Some b2. *)
(*   Proof. intros ?%Some_pair_includedN. by rewrite -(Some_includedN_total _ a1). Qed. *)
(*   Lemma Some_pair_includedN_total_2 `{CmraTotal B} n a1 a2 b1 b2 : *)
(*     Some (a1,b1) ≼{n} Some (a2,b2) → Some a1 ≼{n} Some a2 ∧ b1 ≼{n} b2. *)
(*   Proof. intros ?%Some_pair_includedN. by rewrite -(Some_includedN_total _ b1). Qed. *)

(*   Lemma Some_pair_included a1 a2 b1 b2 : *)
(*     Some (a1,b1) ≼ Some (a2,b2) → Some a1 ≼ Some a2 ∧ Some b1 ≼ Some b2. *)
(*   Proof. rewrite !Some_included. intros [[??]|[??]%prod_included]; eauto. Qed. *)
(*   Lemma Some_pair_included_total_1 `{CmraTotal A} a1 a2 b1 b2 : *)
(*     Some (a1,b1) ≼ Some (a2,b2) → a1 ≼ a2 ∧ Some b1 ≼ Some b2. *)
(*   Proof. intros ?%Some_pair_included. by rewrite -(Some_included_total a1). Qed. *)
(*   Lemma Some_pair_included_total_2 `{CmraTotal B} a1 a2 b1 b2 : *)
(*     Some (a1,b1) ≼ Some (a2,b2) → Some a1 ≼ Some a2 ∧ b1 ≼ b2. *)
(*   Proof. intros ?%Some_pair_included. by rewrite -(Some_included_total b1). Qed. *)
(* End option_prod. *)

#[export] Instance option_fmap_ora_morphism {A B : ora} (f: A → B) `{!OraMorphism f} :
  OraMorphism (fmap f : option A → option B).
Proof.
  split; first apply _.
  - intros n [x|] [y|] ?; try done.
    + simpl. apply Some_orderN.
        by apply ora_morphism_orderN.
    + simpl. apply ora_morphism_increasing; eauto.
  - intros [a|]; simpl; eauto.
    + intros Ha%Some_increasing. apply (Some_increasing (f a)).
      by apply ora_morphism_increasing.
    + intros ?; apply None_increasing.
Qed.

Program Definition optionRF (F : OrarFunctor) : OrarFunctor := {|
  orarFunctor_car A _ B _ := optionR (orarFunctor_car F A B);
  orarFunctor_map A1 _ A2 _ B1 _ B2 _ fg := optionO_map (orarFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply optionO_map_ne, orarFunctor_map_ne.
Qed.
Next Obligation.
  intros F A ? B ? x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_equiv_ext=>y; apply orarFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -option_fmap_compose.
  apply option_fmap_equiv_ext=>y; apply orarFunctor_map_compose.
Qed.

#[export] Instance optionRF_contractive F :
  OrarFunctorContractive F → OrarFunctorContractive (optionRF F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply optionO_map_ne, orarFunctor_map_contractive.
Qed.

Program Definition optionURF (F : OrarFunctor) : uorarFunctor := {|
  uorarFunctor_car A _ B _ := optionUR (orarFunctor_car F A B);
  uorarFunctor_map A1 _ A2 _ B1 _ B2 _ fg := optionO_map (orarFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply optionO_map_ne, orarFunctor_map_ne.
Qed.
Next Obligation.
  intros F A ? B ? x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_equiv_ext=>y; apply orarFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -option_fmap_compose.
  apply option_fmap_equiv_ext=>y; apply orarFunctor_map_compose.
Qed.

#[export] Instance optionURF_contractive F :
  OrarFunctorContractive F → uorarFunctorContractive (optionURF F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply optionO_map_ne, orarFunctor_map_contractive.
Qed.

(* Dependently-typed functions over a discrete domain *)
Section discrete_fun_ora.
  Context {A : Type} `{Hfin : Finite A} {B : A → uora}.
  Implicit Types f g : discrete_fun B.

  Instance discrete_fun_op : Op (discrete_fun B) := λ f g x, f x ⋅ g x.
  Instance discrete_fun_pcore : PCore (discrete_fun B) := λ f, Some (λ x, core (f x)).
  Instance discrete_fun_valid : Valid (discrete_fun B) := λ f, ∀ x, ✓ f x.
  Instance discrete_fun_validN : ValidN (discrete_fun B) := λ n f, ∀ x, ✓{n} f x.
  Instance discrete_fun_orderN : OraOrderN (discrete_fun B) :=
    λ n f g, ∀ x, f x ≼ₒ{n} g x.
  Instance discrete_fun_order : OraOrder (discrete_fun B) := λ f g, ∀ x, f x ≼ₒ g x.

  Definition discrete_fun_lookup_op f g x : (f ⋅ g) x = f x ⋅ g x := eq_refl.
  Definition discrete_fun_lookup_core f x : (core f) x = core (f x) := eq_refl.

  Lemma discrete_fun_included_spec_1 (f g : discrete_fun B) x : f ≼ g → f x ≼ g x.
  Proof.
    by intros [h Hh]; exists (h x); rewrite /op /discrete_fun_op_instance (Hh x).
  Qed.

  Lemma discrete_fun_included_spec (f g : discrete_fun B) : f ≼ g ↔ ∀ x, f x ≼ g x.
  Proof using Hfin.
    split; [by intros [h Hh] x; exists (h x); rewrite /op /discrete_fun_op (Hh x)|].
    intros [h ?]%finite_choice. by exists h.
  Qed.

  Lemma discrete_fun_increasing f : Increasing f ↔ ∀ x, Increasing (f x).
  Proof using Type*.
    split.
    - intros Hf x z.
      pose proof (Hf (λ u, match decide (x = u) with
                             | left eq =>
                               match eq in _ = r return B r with eq_refl => z end
                             | right _ => (f u)
                           end) x) as Hf'; simpl in *.
      rewrite /op /discrete_fun_op /= in Hf'.
      by destruct decide as [[]|]; last done; simpl in *.
    - intros Hf z w. apply Hf.
  Qed.

  Lemma discrete_fun_ora_mixin : OraMixin (discrete_fun B).
  Proof using Hfin.
    apply ora_total_mixin.
    - eauto.
    - intros f g x. rewrite /op /discrete_fun_op /core /=.
      apply ora_core_increasing.
    - intros n f g Hf Hfg. apply discrete_fun_increasing => x w.
      eapply ora_increasing_closed; eauto.
      by apply discrete_fun_increasing.
    - intros n f g Hfg x. rewrite /core /=. apply ora_core_monoN, Hfg.
    - intros n f f1 f2 Hf Hf12.
(*      assert (FUN := λ x, ora_op_extend n (f x) (f1 x) (f2 x) (Hf x) (Hf12 x)). *)
      destruct (finite_choice (λ x (yy : B x * B x),
        yy.1 ⋅ yy.2 ≼ₒ{S n} f x ∧ yy.1 ≡{n}≡ f1 x ∧ yy.2 ≡{n}≡ f2 x)) as [gg Hgg].
      { intros x; simpl.
        destruct (ora_op_extend n (f x) (f1 x) (f2 x)) as (z1&z2&Hz);
          first (by apply Hf); first by apply Hf12.
        exists (z1, z2); eauto. }
      exists (λ x, (gg x).1), (λ x, (gg x).2); naive_solver.
    - intros n f g Hf Hfg.
(*      assert (FUN := λ x, ora_extend n (f x) (g x) (Hf x) (Hfg x)). *)
      destruct (finite_choice (λ x (y : B x), y ≼ₒ{S n} f x ∧ y ≡{n}≡ g x))
        as [g' Hg'].
      { intros x; simpl.
        destruct (ora_extend n (f x) (g x)) as (z&Hz);
          first (by apply Hf); first by apply Hfg. exists z; eauto. }
      exists g'; naive_solver.
    - intros n f g Hfg x. apply ora_dist_orderN; apply Hfg.
    - intros n f g Hfg x. apply ora_orderN_S; apply Hfg.
    - intros n f g h Hfg Hgh x.
      eapply ora_orderN_trans; first eapply Hfg; apply Hgh.
    - intros n f g h Hfg x. rewrite /op /discrete_fun_op /=.
      apply ora_orderN_op; apply Hfg.
    - intros n f g Hf Hgf x. eapply ora_validN_orderN; eauto.
    - intros f g; split.
      + intros Hfg n x; apply ora_order_orderN; eauto.
      + intros Hfg x. apply ora_order_orderN => n; apply Hfg.
    - intros f cf g Hf.
      exists (core (f ⋅ g)); split; [reflexivity|].
      intros i.
      inversion Hf as [?? Heq|]; subst.
      rewrite -(Heq i).
      rewrite {2}/core /=.
      apply uora_core_order_op.
  Qed.
  Canonical Structure discrete_funR := Ora (discrete_fun B) discrete_fun_ora_mixin.

  Instance discrete_fun_unit : Unit (discrete_fun B) := λ x, ε.
  Definition discrete_fun_lookup_empty x : ε x = ε := eq_refl.

  Lemma discrete_fun_ucmra_mixin : UcmraMixin (discrete_fun B).
  Proof.
    split.
    - intros x; apply ucmra_unit_valid.
    - by intros f x; rewrite discrete_fun_lookup_op left_id.
    - constructor=> x. apply oracore_id_core, _.
  Qed.
  Canonical Structure discrete_funUR := Uora (discrete_fun B) discrete_fun_ucmra_mixin.

  Global Instance discrete_fun_unit_discrete :
    (∀ i, Discrete (ε : B i)) → Discrete (ε : discrete_fun B).
  Proof. intros ? f Hf x. by apply: discrete. Qed.
End discrete_fun_ora.

Arguments discrete_funR {_ _ _} _.
Arguments discrete_funUR {_ _ _} _.

Global Instance discrete_fun_map_ora_morphism
    `{Finite A} {B1 B2 : A → uora} (f : ∀ x, B1 x → B2 x) :
  (∀ x, OraMorphism (f x)) → OraMorphism (discrete_fun_map f).
Proof.
  intros Ho; split.
  - apply (discrete_fun_map_cmra_morphism f).
    intros x; apply Ho.
  - intros n g1 g2 Hg x. rewrite /discrete_fun_map. eapply ora_morphism_orderN; eauto.
  - intros g Hg. apply discrete_fun_increasing => x z.
    apply (ora_morphism_increasing (f x)); eauto.
    by apply discrete_fun_increasing.
Qed.

Program Definition discrete_funURF `{Finite C} (F : C → uorarFunctor) : uorarFunctor := {|
  uorarFunctor_car A _ B _ := discrete_funUR (λ c, uorarFunctor_car (F c) A B);
  uorarFunctor_map A1 _ A2 _ B1 _ B2 _ fg := discrete_funO_map (λ c, uorarFunctor_map (F c) fg)
|}.
Next Obligation.
  intros C ?? F A1 ? A2 ? B1 ? B2 ? n ?? g.
  by apply discrete_funO_map_ne=>?; apply uorarFunctor_map_ne.
Qed.
Next Obligation.
  intros C ?? F A ? B ? g; simpl. rewrite -{2}(discrete_fun_map_id g).
  apply discrete_fun_map_ext=> y; apply uorarFunctor_map_id.
Qed.
Next Obligation.
  intros C ?? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f1 f2 f1' f2' g. rewrite /=-discrete_fun_map_compose.
  apply discrete_fun_map_ext=>y; apply uorarFunctor_map_compose.
Qed.
Global Instance discrete_funURF_contractive `{Finite C} (F : C → uorarFunctor) :
  (∀ c, uorarFunctorContractive (F c)) → uorarFunctorContractive (discrete_funURF F).
Proof.
  intros ?? A1 ? A2 ? B1 ? B2 ? n ?? g.
  by apply discrete_funO_map_ne=>c; apply uorarFunctor_map_contractive.
Qed.
