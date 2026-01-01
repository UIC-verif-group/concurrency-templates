From iris.algebra Require Export updates.
From iris_ora.algebra Require Export ora.
From iris.bi Require Export derived_connectives plainly internal_eq bi.
From stdpp Require Import finite.
Set Default Proof Using "Type".
Local Hint Extern 1 (_ ≼ₒ _) => etrans; [eassumption|] : core.
Local Hint Extern 1 (_ ≼ₒ _) => etrans; [|eassumption] : core.
Local Hint Extern 10 (_ ≤ _) => lia : core.


(* TODO: change following text. *)

(** The basic definition of the ouPred type, its metric and functor laws.
    You probably do not want to import this file. Instead, import
    base_logic.base_logic; that will also give you all the primitive
    and many derived laws for the logic. *)

(* A good way of understanding this definition of the uPred OFE is to
   consider the OFE uPred0 of monotonous SProp predicates. That is,
   uPred0 is the OFE of non-expansive functions from M to SProp that
   are monotonous with respect to CMRA inclusion. This notion of
   monotonicity has to be stated in the SProp logic. Together with the
   usual closedness property of SProp, this gives exactly uPred_mono.

   Then, we quotient uPred0 *in the sProp logic* with respect to
   equivalence on valid elements of M. That is, we quotient with
   respect to the following *sProp* equivalence relation:
     P1 ≡ P2 := ∀ x, ✓ x → (P1(x) ↔ P2(x))       (1)
   When seen from the ambiant logic, obtaining this quotient requires
   definig both a custom Equiv and Dist.


   It is worth noting that this equivalence relation admits canonical
   representatives. More precisely, one can show that every
   equivalence class contains exactly one element P0 such that:
     ∀ x, (✓ x → P0(x)) → P0(x)                 (2)
   (Again, this assertion has to be understood in sProp). Intuitively,
   this says that P0 trivially holds whenever the resource is invalid.
   Starting from any element P, one can find this canonical
   representative by choosing:
     P0(x) := ✓ x → P(x)                        (3)

   Hence, as an alternative definition of uPred, we could use the set
   of canonical representatives (i.e., the subtype of monotonous
   sProp predicates that verify (2)). This alternative definition would
   save us from using a quotient. However, the definitions of the various
   connectives would get more complicated, because we have to make sure
   they all verify (2), which sometimes requires some adjustments. We
   would moreover need to prove one more property for every logical
   connective.
 *)

Record ouPred (M : uora) : Type := IProp {
  ouPred_holds :> nat → M → Prop;

  ouPred_mono n1 n2 x1 x2 :
    ouPred_holds n1 x1 → x1 ≼ₒ{n1} x2 → n2 ≤ n1 → ouPred_holds n2 x2
}.
Arguments ouPred_holds {_} _ _ _ : simpl never.
Add Printing Constructor ouPred.
#[export] Instance: Params (@ouPred_holds) 3 := {}.

Bind Scope bi_scope with ouPred.
Arguments ouPred_holds {_} _%I _ _.

Section cofe.
  Context {M : uora}.

  Inductive ouPred_equiv' (P Q : ouPred M) : Prop :=
    { ouPred_in_equiv : ∀ n x, ✓{n} x → P n x ↔ Q n x }.
  Instance ouPred_equiv : Equiv (ouPred M) := ouPred_equiv'.
  Inductive ouPred_dist' (n : nat) (P Q : ouPred M) : Prop :=
    { ouPred_in_dist : ∀ n' x, n' ≤ n → ✓{n'} x → P n' x ↔ Q n' x }.
  Instance ouPred_dist : Dist (ouPred M) := ouPred_dist'.
  Definition ouPred_ofe_mixin : OfeMixin (ouPred M).
  Proof.
    split.
    - intros P Q; split.
      + by intros HPQ n; split=> i x ??; apply HPQ.
      + intros HPQ; split=> n x ?; apply HPQ with n; auto.
    - intros n; split.
      + by intros P; split=> x i.
      + by intros P Q HPQ; split=> x i ??; symmetry; apply HPQ.
      + intros P Q Q' HP HQ; split=> i x ??.
        by trans (Q i x);[apply HP|apply HQ].
    - intros n m P Q HPQ; split=> i x ??; apply HPQ; auto.
  Qed.
  Canonical Structure ouPredO : ofe := Ofe (ouPred M) ouPred_ofe_mixin.

  Program Definition ouPred_compl : Compl ouPredO := λ c,
    {| ouPred_holds n x := ∀ n', n' ≤ n → ✓{n'}x → c n' n' x |}.
  Next Obligation.
    move=> /= c n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23 Hv. eapply ouPred_mono.
    eapply HP, ora_validN_orderN, ora_orderN_le=>//; lia.
    eapply ora_orderN_le=>//; lia. done.
  Qed.
  Global Program Instance ouPred_cofe : Cofe ouPredO := {| compl := ouPred_compl |}.
  Next Obligation.
    intros n c; split=>i x Hin Hv.
    etrans; [|by symmetry; apply (chain_cauchy c i n)]. split=>H; [by apply H|].
    repeat intro. apply (chain_cauchy c n' i)=>//. by eapply ouPred_mono.
  Qed.
End cofe.
Arguments ouPredO : clear implicits.

#[export] Instance ouPred_ne {M} (P : ouPred M) n : Proper (dist n ==> iff) (P n).
Proof.
  intros x1 x2 Hx; split=> ?; eapply ouPred_mono; eauto; by rewrite Hx.
Qed.
#[export] Instance ouPred_proper {M} (P : ouPred M) n : Proper ((≡) ==> iff) (P n).
Proof. by intros x1 x2 Hx; apply ouPred_ne, equiv_dist. Qed.

Lemma ouPred_holds_ne {M} (P Q : ouPred M) n1 n2 x :
  P ≡{n2}≡ Q → n2 ≤ n1 → ✓{n2} x → Q n1 x → P n2 x.
Proof.
  intros [Hne] ???. eapply Hne; try done. eauto using ouPred_mono, cmra_validN_le.
Qed.

(* TODO: remove!? *)
(* Equivalence to the definition of uPred in the appendix. *)
Lemma ouPred_alt {M : uora} (P: nat → M → Prop) :
  (∀ n1 n2 x1 x2, P n1 x1 → x1 ≼ₒ{n1} x2 → n2 ≤ n1 → P n2 x2) ↔
  ( (∀ x n1 n2, n2 ≤ n1 → P n1 x → P n2 x) (* Pointwise down-closed *)
  ∧ (∀ n x1 x2, x1 ≡{n}≡ x2 → ∀ m, m ≤ n → P m x1 ↔ P m x2) (* Non-expansive *)
  ∧ (∀ n x1 x2, x1 ≼ₒ{n} x2 → ∀ m, m ≤ n → P m x1 → P m x2) (* Monotonicity *)
  ).
Proof.
  (* Provide this lemma to eauto. *)
  assert (∀ n1 n2 (x1 x2 : M), n2 ≤ n1 → x1 ≡{n1}≡ x2 → x1 ≼ₒ{n2} x2).
  { intros ????? H. eapply ora_orderN_le; last done. by rewrite H. }
  (* Now go ahead. *)
  split.
  - intros Hupred. repeat split; eauto using ora_orderN_le.
  - intros (Hdown & _ & Hmono) **. eapply Hmono; [done..|]. eapply Hdown; done.
Qed.

(** functor *)
Program Definition ouPred_map {M1 M2 : uora} (f : M2 -n> M1)
  `{!OraMorphism f} (P : ouPred M1) :
  ouPred M2 := {| ouPred_holds n x := P n (f x) |}.
Next Obligation. naive_solver eauto using ouPred_mono, ora_morphism_monotoneN. Qed.

Global Instance ouPred_map_ne {M1 M2 : uora} (f : M2 -n> M1)
  `{!OraMorphism f} n : Proper (dist n ==> dist n) (ouPred_map f).
Proof.
  intros x1 x2 Hx; split=> n' y ??.
  split; apply Hx; auto using ora_morphism_validN.
Qed.
Lemma ouPred_map_id {M : uora} (P : ouPred M): ouPred_map cid P ≡ P.
Proof. by split=> n x ?. Qed.
Lemma ouPred_map_compose {M1 M2 M3 : uora} (f : M1 -n> M2) (g : M2 -n> M3)
    `{!OraMorphism f, !OraMorphism g} (P : ouPred M3):
  ouPred_map (g ◎ f) P ≡ ouPred_map f (ouPred_map g P).
Proof. by split=> n x Hx. Qed.
Lemma ouPred_map_ext {M1 M2 : uora} (f g : M1 -n> M2)
      `{!OraMorphism f} `{!OraMorphism g}:
  (∀ x, f x ≡ g x) → ∀ x, ouPred_map f x ≡ ouPred_map g x.
Proof. intros Hf P; split=> n x Hx /=; by rewrite /ouPred_holds /= Hf. Qed.
Definition ouPredO_map {M1 M2 : uora} (f : M2 -n> M1) `{!OraMorphism f} :
  ouPredO M1 -n> ouPredO M2 := OfeMor (ouPred_map f : ouPredO M1 → ouPredO M2).
Lemma ouPredO_map_ne {M1 M2 : uora} (f g : M2 -n> M1)
    `{!OraMorphism f, !OraMorphism g} n :
  f ≡{n}≡ g → ouPredO_map f ≡{n}≡ ouPredO_map g.
Proof.
  by intros Hfg P; split=> n' y ??;
    rewrite /ouPred_holds /= (dist_le _ _ _ _(Hfg y)); last lia.
Qed.

Program Definition ouPredOF (F : uorarFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := ouPredO (uorarFunctor_car F B A);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := ouPredO_map (uorarFunctor_map F (fg.2, fg.1))
|}.
Next Obligation.
  intros F A1 ? A2 ? B1 ? B2 ? n P Q HPQ.
  apply ouPredO_map_ne, uorarFunctor_map_ne; split; by apply HPQ.
Qed.
Next Obligation.
  intros F A ? B ? P; simpl. rewrite -{2}(ouPred_map_id P).
  apply ouPred_map_ext=>y. by rewrite uorarFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' P; simpl. rewrite -ouPred_map_compose.
  apply ouPred_map_ext=>y; apply uorarFunctor_map_compose.
Qed.

#[export] Instance ouPredOF_contractive F :
  uorarFunctorContractive F → oFunctorContractive (ouPredOF F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n P Q HPQ. apply ouPredO_map_ne, uorarFunctor_map_contractive.
  destruct HPQ as [HPQ]. constructor. intros ??.
  split; by eapply HPQ.
Qed.

(** logical entailment *)
Inductive ouPred_entails {M} (P Q : ouPred M) : Prop :=
  { ouPred_in_entails : ∀ n x, ✓{n} x → P n x → Q n x }.
#[export] Hint Resolve ouPred_mono : ouPred_def.

(** logical connectives *)
Program Definition ouPred_pure_def {M} (φ : Prop) : ouPred M :=
  {| ouPred_holds n x := φ |}.
Solve Obligations with done.
Definition ouPred_pure_aux : seal (@ouPred_pure_def). by eexists. Qed.
Definition ouPred_pure {M} := unseal ouPred_pure_aux M.
Definition ouPred_pure_eq :
  @ouPred_pure = @ouPred_pure_def := seal_eq ouPred_pure_aux.

Program Definition ouPred_emp {M} : ouPred M :=
{| ouPred_holds n x := ε ≼ₒ{n} x |}.
Next Obligation.
Proof.
  intros M n1 n2 x1 x2; simpl => Hx1 Hx2 Hn.
  eapply ora_orderN_le; last eassumption.
  etrans; eauto.
Qed.

Program Definition ouPred_and_def {M} (P Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := P n x ∧ Q n x |}.
Solve Obligations with naive_solver eauto 2 with ouPred_def.
Definition ouPred_and_aux : seal (@ouPred_and_def). by eexists. Qed.
Definition ouPred_and {M} := unseal ouPred_and_aux M.
Definition ouPred_and_eq: @ouPred_and = @ouPred_and_def := seal_eq ouPred_and_aux.

Program Definition ouPred_or_def {M} (P Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := P n x ∨ Q n x |}.
Solve Obligations with naive_solver eauto 2 with ouPred_def.
Definition ouPred_or_aux : seal (@ouPred_or_def). by eexists. Qed.
Definition ouPred_or {M} := unseal ouPred_or_aux M.
Definition ouPred_or_eq: @ouPred_or = @ouPred_or_def := seal_eq ouPred_or_aux.

Program Definition ouPred_impl_def {M} (P Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∀ n' x',
       x ≼ₒ{n'} x' → n' ≤ n → ✓{n'} x' → P n' x' → Q n' x' |}.
Next Obligation.
  intros M P Q n1 n1' x1 x1' HPQ Hle1 Hn1 n2 x3 Hle2 ?; simpl in *.
  apply HPQ; eauto.
  etrans; last apply Hle2.
  eapply ora_orderN_le; eauto.
Qed.
Definition ouPred_impl_aux : seal (@ouPred_impl_def). by eexists. Qed.
Definition ouPred_impl {M} := unseal ouPred_impl_aux M.
Definition ouPred_impl_eq :
  @ouPred_impl = @ouPred_impl_def := seal_eq ouPred_impl_aux.

Program Definition ouPred_forall_def {M A} (Ψ : A → ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∀ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with ouPred_def.
Definition ouPred_forall_aux : seal (@ouPred_forall_def). by eexists. Qed.
Definition ouPred_forall {M A} := unseal ouPred_forall_aux M A.
Definition ouPred_forall_eq :
  @ouPred_forall = @ouPred_forall_def := seal_eq ouPred_forall_aux.

Program Definition ouPred_exist_def {M A} (Ψ : A → ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∃ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with ouPred_def.
Definition ouPred_exist_aux : seal (@ouPred_exist_def). by eexists. Qed.
Definition ouPred_exist {M A} := unseal ouPred_exist_aux M A.
Definition ouPred_exist_eq: @ouPred_exist = @ouPred_exist_def := seal_eq ouPred_exist_aux.

Program Definition ouPred_internal_eq_def {M} {A : ofe} (a1 a2 : A) : ouPred M :=
  {| ouPred_holds n x := a1 ≡{n}≡ a2 |}.
Solve Obligations with naive_solver eauto 2 using (dist_le (A:=A)).
Definition ouPred_internal_eq_aux : seal (@ouPred_internal_eq_def). by eexists. Qed.
Definition ouPred_internal_eq {M A} := unseal ouPred_internal_eq_aux M A.
Definition ouPred_internal_eq_eq:
  @ouPred_internal_eq = @ouPred_internal_eq_def := seal_eq ouPred_internal_eq_aux.

Program Definition ouPred_sep_def {M} (P Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∃ x1 x2, x1 ⋅ x2 ≼ₒ{n} x ∧ P n x1 ∧ Q n x2 |}.
Next Obligation.
  intros M P Q n1 n2 x y (x1&x2&Hx&?&?) ? ?.
  eexists x1, x2; repeat split; eauto using ouPred_mono.
  etrans; eapply ora_orderN_le; eauto.
Qed.
Definition ouPred_sep_aux : seal (@ouPred_sep_def). by eexists. Qed.
Definition ouPred_sep {M} := unseal ouPred_sep_aux M.
Definition ouPred_sep_eq: @ouPred_sep = @ouPred_sep_def := seal_eq ouPred_sep_aux.

Program Definition ouPred_wand_def {M} (P Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∀ n' x',
       n' ≤ n → ✓{n'} (x ⋅ x') → P n' x' → Q n' (x ⋅ x') |}.
Next Obligation.
  intros M P Q n1 n1' x1 x1' HPQ ? Hn n3 x3 ???; simpl in *.
  eapply ouPred_mono with n3 (x1 ⋅ x3);
    eauto using ora_validN_orderN, ora_monoN_r, ora_orderN_le.
Qed.
Definition ouPred_wand_aux : seal (@ouPred_wand_def). by eexists. Qed.
Definition ouPred_wand {M} := unseal ouPred_wand_aux M.
Definition ouPred_wand_eq :
  @ouPred_wand = @ouPred_wand_def := seal_eq ouPred_wand_aux.

Program Definition ouPred_plainly_def {M} (P : ouPred M) : ouPred M :=
  {| ouPred_holds n x := P n ε |}.
Solve Obligations with naive_solver eauto using ouPred_mono, ucmra_unit_validN.
Definition ouPred_plainly_aux : seal (@ouPred_plainly_def). by eexists. Qed.
Definition ouPred_plainly {M} := unseal ouPred_plainly_aux M.
Definition ouPred_plainly_eq :
  @ouPred_plainly = @ouPred_plainly_def := seal_eq ouPred_plainly_aux.

Program Definition ouPred_persistently_def {M} (P : ouPred M) : ouPred M :=
  {| ouPred_holds n x := P n (core x) |}.
Next Obligation.
  intros M P n1 n2 x1 x2 HP Hx Hn; simpl in *.
  eapply ouPred_mono; eauto. by apply ora_core_monoN.
Qed.
Definition ouPred_persistently_aux : seal (@ouPred_persistently_def). by eexists. Qed.
Definition ouPred_persistently {M} := unseal ouPred_persistently_aux M.
Definition ouPred_persistently_eq :
  @ouPred_persistently = @ouPred_persistently_def := seal_eq ouPred_persistently_aux.

Program Definition ouPred_later_def {M} (P : ouPred M) : ouPred M :=
  {| ouPred_holds n x := match n return _ with 0 => True | S n' => P n' x end |}.
Next Obligation.
  intros M P [|n1] [|n2] x1 x2; eauto using ouPred_mono, ora_orderN_S with lia.
Qed.
Definition ouPred_later_aux : seal (@ouPred_later_def). by eexists. Qed.
Definition ouPred_later {M} := unseal ouPred_later_aux M.
Definition ouPred_later_eq :
  @ouPred_later = @ouPred_later_def := seal_eq ouPred_later_aux.

Program Definition ouPred_ownM_def {M : uora} (a : M) : ouPred M :=
  {| ouPred_holds n x := a ≼ₒ{n} x |}.
Next Obligation.
  intros M a n1 n2 x1 x2; simpl => Hax1 Hx1x2 Hn.
  eapply ora_orderN_le; last eassumption.
  etrans; eauto.
Qed.
Definition ouPred_ownM_aux : seal (@ouPred_ownM_def). by eexists. Qed.
Definition ouPred_ownM {M} := unseal ouPred_ownM_aux M.
Definition ouPred_ownM_eq :
  @ouPred_ownM = @ouPred_ownM_def := seal_eq ouPred_ownM_aux.

Program Definition ouPred_ora_valid_def {M} {A : ora} (a : A) : ouPred M :=
  {| ouPred_holds n x := ✓{n} a |}.
Solve Obligations with naive_solver eauto 2 using cmra_validN_le.
Definition ouPred_ora_valid_aux : seal (@ouPred_ora_valid_def). by eexists. Qed.
Definition ouPred_ora_valid {M A} := unseal ouPred_ora_valid_aux M A.
Definition ouPred_ora_valid_eq :
  @ouPred_ora_valid = @ouPred_ora_valid_def := seal_eq ouPred_ora_valid_aux.

Local Program Definition ouPred_bupd_def {M} (Q : ouPred M) : ouPred M :=
  {| ouPred_holds n x := ∀ k yf,
      k ≤ n → ✓{k} (x ⋅ yf) → ∃ x', ✓{k} (x' ⋅ yf) ∧ Q k x' |}.
Next Obligation.
  intros M Q n1 n2 x1 x2 HQ Hord Hn k yf Hk Hxy.
  eapply ora_validN_orderN in Hxy; last by eapply ora_monoN_r, ora_orderN_le; [done | lia].
  auto.
Qed.
Local Definition ouPred_bupd_aux : seal (@ouPred_bupd_def). Proof. by eexists. Qed.
Definition ouPred_bupd := ouPred_bupd_aux.(unseal).
Global Arguments ouPred_bupd {M}.
Local Definition ouPred_bupd_unseal :
  @ouPred_bupd = @ouPred_bupd_def := ouPred_bupd_aux.(seal_eq).

Module ouPred_unseal.
Definition unseal_eqs :=
  (ouPred_pure_eq, ouPred_and_eq, ouPred_or_eq, ouPred_impl_eq, ouPred_forall_eq,
  ouPred_exist_eq, ouPred_internal_eq_eq, ouPred_sep_eq, ouPred_wand_eq,
  ouPred_plainly_eq, ouPred_persistently_eq, ouPred_later_eq, ouPred_ownM_eq,
  ouPred_ora_valid_eq, @ouPred_bupd_unseal).
Ltac unseal := (* Coq unfold is used to circumvent bug #5699 in rewrite /foo *)
  unfold bi_emp; simpl;
  unfold ouPred_emp, bupd, bi_bupd_bupd, bi_pure,
    bi_and, bi_or, bi_impl, bi_forall, bi_exist,
    bi_sep, bi_wand, bi_persistently, bi_later; simpl;
  unfold internal_eq, bi_internal_eq_internal_eq,
    plainly, bi_plainly_plainly; simpl;
  rewrite !unseal_eqs /=.
End ouPred_unseal.
Import ouPred_unseal.

Local Arguments ouPred_holds {_} !_ _ _ /.

(** BI instances *)
Lemma ouPred_bi_mixin (M : uora) :
  BiMixin
    ouPred_entails ouPred_emp ouPred_pure ouPred_and ouPred_or ouPred_impl
    (@ouPred_forall M) (@ouPred_exist M) ouPred_sep ouPred_wand
    (* ouPred_persistently *)
    .
Proof.
  split.
  - (* PreOrder ouPred_entails *)
    split.
    + by intros P; split=> x i.
    + by intros P Q Q' HP HQ; split=> x i ??; apply HQ, HP.
  - (* (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P) *)
    intros P Q. split.
    + intros HPQ; split; split=> x i; apply HPQ.
    + intros [HPQ HQP]; split=> x n; by split; [apply HPQ|apply HQP].
  - (* Proper (iff ==> dist n) (@ouPred_pure M) *)
    intros φ1 φ2 Hφ. by unseal; split=> -[|n] ?; try apply Hφ.
  - (* NonExpansive2 ouPred_and *)
    intros n P P' HP Q Q' HQ; unseal; split=> x n' ??.
    split; (intros [??]; split; [by apply HP|by apply HQ]).
  - (* NonExpansive2 ouPred_or *)
    intros n P P' HP Q Q' HQ; split=> x n' ??.
    unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
  - (* NonExpansive2 ouPred_impl *)
    intros n P P' HP Q Q' HQ; split=> x n' ??.
    unseal; split; intros HPQ x' n'' ????; apply HQ, HPQ, HP; auto.
  - (* Proper (pointwise_relation A (dist n) ==> dist n) ouPred_forall *)
    by intros A n Ψ1 Ψ2 HΨ; unseal; split=> n' x; split; intros HP a; apply HΨ.
  - (* Proper (pointwise_relation A (dist n) ==> dist n) ouPred_exist *)
    intros A n Ψ1 Ψ2 HΨ.
    unseal; split=> n' x ??; split; intros [a ?]; exists a; by apply HΨ.
  - (* NonExpansive2 ouPred_sep *)
    intros n P P' HP Q Q' HQ; split=> n' x ??.
    unseal; split; intros (x1&x2&?&?&?); ofe_subst;
      exists x1, x2; split_and!; try (apply HP || apply HQ); eauto.
    + eapply (@cmra_validN_op_l M), ora_validN_orderN; eauto.
    + eapply (@cmra_validN_op_r M), ora_validN_orderN; eauto.
    + eapply (@cmra_validN_op_l M), ora_validN_orderN; eauto.
    + eapply (@cmra_validN_op_r M), ora_validN_orderN; eauto.
  - (* NonExpansive2 ouPred_wand *)
    intros n P P' HP Q Q' HQ; split=> n' x ??.
    unseal; split; intros HPQ x' n'' ???;
      apply HQ, HPQ, HP; eauto.
    + eapply (@cmra_validN_op_r M); eauto.
    + eapply (@cmra_validN_op_r M); eauto.
  - (* φ → P ⊢ ⌜φ⌝ *)
    intros P φ ?. unseal; by split.
  - (* (φ → True ⊢ P) → ⌜φ⌝ ⊢ P *)
    intros φ P. unseal=> HP; split=> n x ??. by apply HP.
  - (* P ∧ Q ⊢ P *)
    intros P Q. unseal; by split=> n x ? [??].
  - (* P ∧ Q ⊢ Q *)
    intros P Q. unseal; by split=> n x ? [??].
  - (* (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R *)
    intros P Q R HQ HR; unseal; split=> n x ??; by split; [apply HQ|apply HR].
  - (* P ⊢ P ∨ Q *)
    intros P Q. unseal; split=> n x ??; left; auto.
  - (* Q ⊢ P ∨ Q *)
    intros P Q. unseal; split=> n x ??; right; auto.
  - (* (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R *)
    intros P Q R HP HQ. unseal; split=> n x ? [?|?]. by apply HP. by apply HQ.
  - (* (P ∧ Q ⊢ R) → P ⊢ Q → R. *)
    intros P Q R. unseal => HQ; split=> n x ?? n' x' ????. apply HQ;
      naive_solver eauto using ouPred_mono, cmra_included_includedN.
  - (* (P ⊢ Q → R) → P ∧ Q ⊢ R *)
    intros P Q R. unseal=> HP; split=> n x ? [??]. apply HP with n x; auto.
  - (* (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a *)
    intros A P Ψ. unseal; intros HPΨ; split=> n x ?? a; by apply HPΨ.
  - (* (∀ a, Ψ a) ⊢ Ψ a *)
    intros A Ψ a. unseal; split=> n x ? HP; apply HP.
  - (* Ψ a ⊢ ∃ a, Ψ a *)
    intros A Ψ a. unseal; split=> n x ??; by exists a.
  - (* (∀ a, Ψ a ⊢ Q) → (∃ a, Ψ a) ⊢ Q *)
    intros A Ψ Q. unseal; intros HΨ; split=> n x ? [a ?]; by apply HΨ with a.
  - (* (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q' *)
    intros P P' Q Q' HQ HQ'; unseal.
    split; intros n' x ? (x1&x2&?&?&?); exists x1,x2; ofe_subst x; repeat split; eauto.
    + apply HQ; auto.
      eapply (@cmra_validN_op_l M), ora_validN_orderN; eauto.
    + apply HQ'; auto.
      eapply (@cmra_validN_op_r M), ora_validN_orderN; eauto.
  - (* P ⊢ emp ∗ P *)
    intros P. rewrite /ouPred_emp. unseal; split=> n x ?? /=.
    exists (core x), x. rewrite ora_core_l; repeat split; auto.
    apply ora_order_orderN, uora_unit_order_core.
  - (* emp ∗ P ⊢ P *)
    intros P. unseal; split; intros n x ? (x1&x2&?&?&?); ofe_subst.
    eapply ouPred_mono; eauto.
    rewrite -(left_id _ _ x2). etrans; last eauto.
    by eapply ora_orderN_op.
  - (* P ∗ Q ⊢ Q ∗ P *)
    intros P Q. unseal; split; intros n x ? (x1&x2&?&?&?).
    exists x2, x1. by rewrite (comm op).
  - (* (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) *)
    intros P Q R. unseal; split; intros n x ? (x1&x2&Hx&(y1&y2&Hy&?&?)&?).
    exists y1, (y2 ⋅ x2); split_and?; auto.
    + by rewrite (assoc op); setoid_rewrite <-Hx; setoid_rewrite Hy.
    + by exists y2, x2.
  - (* (P ∗ Q ⊢ R) → P ⊢ Q -∗ R *)
    intros P Q R. unseal=> HPQR; split=> n x ?? n' x' ???; apply HPQR; auto.
    exists x, x'; split_and?; auto.
    eapply ouPred_mono; eauto using cmra_validN_op_l.
  - (* (P ⊢ Q -∗ R) → P ∗ Q ⊢ R *)
    intros P Q R. unseal=> HPQR. split; intros n x ? (?&?&?&HP&HQ).
    apply HPQR in HP.
    apply HP in HQ; eauto using ora_validN_orderN.
    eauto using ouPred_mono.
    { eapply (@cmra_validN_op_l M), ora_validN_orderN; eauto. }
Qed.

Lemma ouPred_bi_persistently_mixin (M : uora) :
  BiPersistentlyMixin ouPred_entails ouPred_emp ouPred_and
  (@ouPred_exist M) ouPred_sep ouPred_persistently.
Proof.
split.
  - (* NonExpansive ouPred_persistently *)
    intros n P1 P2 HP.
    unseal; split=> n' x; split; apply HP;
    try apply @ora_core_validN; auto; try apply _.
  - (* (P ⊢ Q) → bi_persistently P ⊢ bi_persistently Q *)
    intros P QR HP. unseal; split=> n x ? /=. by apply HP, ora_core_validN.
  - (* bi_persistently P ⊢ bi_persistently (bi_persistently P) *)
    intros P. unseal; split=> n x ?? /=. by rewrite ora_core_idemp.
  - (* emp ⊢ bi_persistently emp *)
    unseal; split => n x Hx HP /=;
      apply ora_order_orderN; apply uora_unit_order_core.
  - (* (∀ a, bi_persistently (Ψ a)) ⊢ bi_persistently (∀ a, Ψ a) *)
    by unseal.
  - (* bi_persistently (∃ a, Ψ a) ⊢ ∃ a, bi_persistently (Ψ a) *)
    by unseal.
  - (* bi_persistently P ∗ Q ⊢ bi_persistently P (ADMISSIBLE) *)
    unseal; split; intros n x ? (x1&x2&?&?&_); ofe_subst.
    eapply ouPred_mono; eauto.
    etrans; last by apply ora_core_monoN; eassumption.
    eapply ora_order_orderN, uora_core_order_op.
  - (* bi_persistently P ∧ Q ⊢ P ∗ Q *)
    intros P Q. unseal; split=> n x ? [??]; simpl in *.
    exists (core x), x; rewrite ?ora_core_l; repeat split; auto.
Qed.

Lemma ouPred_bi_later_mixin (M : uora) : BiLaterMixin
  ouPred_entails ouPred_pure ouPred_or ouPred_impl
  (@ouPred_forall M) (@ouPred_exist M) ouPred_sep
  ouPred_persistently ouPred_later.
Proof.
  split.
  - (* NonExpansive bi_later *)
    unseal; intros n P Q HPQ; split=> -[|n'] x ?? //=; try lia.
    apply HPQ, (cmra_validN_S(A:=M)); auto.
  - (* (P ⊢ Q) → ▷ P ⊢ ▷ Q *)
    intros P Q.
    unseal=> HP; split=>-[|n] x ??; [done|by apply HP; [apply (cmra_validN_S(A:=M))|]].
  - (* P ⊢ ▷ P *)
    intros P. unseal; split=> -[|n] /= x ? HP; first done.
    apply ouPred_mono with (S n) x; eauto.
  - (* (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a *)
    intros A Φ. unseal; by split=> -[|n] x.
  - (* (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a) *)
    intros A Φ. unseal; split=> -[|[|n]] x /=; eauto.
  - (* ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q *)
    intros P Q. unseal; split=> -[|n] x ? /=.
    { by exists x, (core x); rewrite ora_core_r. }
    intros (x1&x2&Hx&?&?); destruct (ora_op_extend n x x1 x2)
      as (y1&y2&Hx'&Hy1&Hy2); eauto using cmra_validN_S; simpl in *.
    exists y1, y2; split; auto; by rewrite Hy1 Hy2.
  - (* ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q) *)
    intros P Q. unseal; split=> -[|n] x ? /=; [done|intros (x1&x2&Hx&?&?)].
    exists x1, x2; eauto using ora_orderN_S.
  - (* ▷ bi_persistently P ⊢ bi_persistently (▷ P) *)
    by unseal.
  - (* bi_persistently (▷ P) ⊢ ▷ bi_persistently P *)
    by unseal.
  - (* ▷ P ⊢ ▷ False ∨ (▷ False → P) *)
    intros P. unseal; split=> -[|n] x ? /= HP; [by left|right].
    intros [|n'] x' ????; [|done].
    eapply ouPred_mono; [| eassumption | trivial].
    eapply ouPred_mono; eauto.
Qed.

Canonical Structure ouPredI (M : uora) : bi :=
  {| bi_ofe_mixin := ofe_mixin_of (ouPred M); bi_bi_mixin := ouPred_bi_mixin M;
     bi_bi_persistently_mixin := ouPred_bi_persistently_mixin M;
     bi_bi_later_mixin := ouPred_bi_later_mixin M |}.

(* Latest notation *)
Notation "✓ x" := (ouPred_ora_valid x) (at level 20) : bi_scope.

Global Instance later_contractive M : Contractive (bi_later (PROP:=ouPredI M)).
Proof.
  unseal; intros [|n] P Q HPQ; split=> -[|n'] x ?? //=; try lia.
  eapply HPQ, (cmra_validN_S(A:=M)); auto.
Qed.

Global Instance ouPred_later_contractive M : BiLaterContractive (ouPredI M).
Proof.
  exact: @later_contractive.
Qed.

Lemma later_eq_1 M {A : ofe} (x y : A) : ouPred_internal_eq(M := M) (Next x) (Next y) ⊢ ▷ (ouPred_internal_eq x y).
Proof.
  unseal. split. intros [|n]; simpl; [done|].
  intros ?? Heq; apply Heq; auto.
Qed.
Lemma later_eq_2 M {A : ofe} (x y : A) : ▷ (ouPred_internal_eq(M := M) x y) ⊢ ouPred_internal_eq (Next x) (Next y).
Proof.
  unseal. split. intros n ? ? Hn; split; intros m Hlt; simpl in *.
  destruct n as [|n]; first lia.
  eauto using dist_le with si_solver.
Qed.

Lemma ouPred_bi_internal_eq_mixin M :
  BiInternalEqMixin (ouPredI M) (@ouPred_internal_eq M).
Proof.
  split.
  - (* NonExpansive2 (@ouPred_internal_eq M A) *)
    intros A n x x' Hx y y' Hy; split=> n' z; unseal; split; intros; simpl in *.
    + by rewrite -(dist_le _ _ _ _ Hx) -?(dist_le _ _ _ _ Hy); auto.
    + by rewrite (dist_le _ _ _ _ Hx) ?(dist_le _ _ _ _ Hy); auto.
  - (* P ⊢ a ≡ a *)
    intros A P a. unseal; by split=> n x ?? /=.
  - (* a ≡ b ⊢ Ψ a → Ψ b *)
    intros A a b Ψ Hnonexp.
    unseal; split=> n x ? Hab n' x' ??? HΨ. eapply Hnonexp with n a; auto.
  - (* (∀ x, f x ≡ g x) ⊢ f ≡ g *)
    by unseal.
  - (* `x ≡ `y ⊢ x ≡ y *)
    by unseal.
  - (* Discrete a → a ≡ b ⊣⊢ ⌜a ≡ b⌝ *)
    intros A a b ?. unseal; split=> n x ?; by apply (discrete_iff n).
  - (* Next x ≡ Next y ⊢ ▷ (x ≡ y) *)
    exact: later_eq_1.
  - (* ▷ (x ≡ y) ⊢ Next x ≡ Next y *)
    exact: later_eq_2.
Qed.
Global Instance ouPred_bi_internal_eq M : BiInternalEq (ouPredI M) :=
  {| bi_internal_eq_mixin := ouPred_bi_internal_eq_mixin M |}.

Lemma ouPred_bi_plainly_mixin M : BiPlainlyMixin (ouPredI M) ouPred_plainly.
Proof.
  split.
  - (* NonExpansive ouPred_plainly *)
    intros n P1 P2 HP.
    unseal; split=> n' x; split; apply HP; eauto using @uora_unit_validN.
  - (* (P ⊢ Q) → ■ P ⊢ ■ Q *)
    intros P QR HP. unseal; split=> n x ? /=. by apply HP, uora_unit_validN.
  - (* ■ P ⊢ bi_persistently P *)
    unseal; split; simpl => ????; eapply ouPred_mono; eauto.
    eapply ora_order_orderN, uora_unit_order_core.
  - (* ■ P ⊢ ■ ■ P *)
    unseal; split=> n x ?? //.
  - (* (∀ a, ■ (Ψ a)) ⊢ ■ (∀ a, Ψ a) *)
    by unseal.
  - (* (■ P → ■ Q) -∗ ■ (■ P → Q) *)
    unseal; split=> /= n x ? HPQ n' x' ????.
    eapply ouPred_mono with n' ε=>//.
    apply (HPQ n' x); eauto.
    eapply (cmra_validN_le(A:=M)); eauto.
  - (* P ⊢ ■ emp (ADMISSIBLE) *)
    unseal; split => ???? /=; auto.
  - (* ■ P ∗ Q ⊢ ■ P *)
    intros P Q.
    unseal; split; intros n x ? (x1&x2&?&?&_); ofe_subst;
      eauto using ouPred_mono.
  - (* ▷ ■ P ⊢ ■ ▷ P *)
    by unseal.
  - (* ■ ▷ P ⊢ ▷ ■ P *)
    by unseal.
Qed.

Global Instance ouPred_bi_plainly M : BiPlainly (ouPredI M) :=
  {| bi_plainly_mixin := ouPred_bi_plainly_mixin M |}.

Global Instance ouPred_bi_prop_ext M : BiPropExt (ouPredI M).
Proof.
  intros P Q. rewrite /bi_wand_iff /internal_eq /plainly
    /bi_internal_eq_internal_eq /bi_plainly_plainly /=.
  unseal; split=> n x ? /= HPQ.
  split=> n' x' ??.
  move: HPQ=> [] /(_ n' x'); rewrite !left_id=> ?.
  move=> /(_ n' x'); rewrite !left_id=> ?. naive_solver.
Qed.

#[export] Instance ouPred_pure_forall M : BiPureForall (ouPredI M).
Proof. rewrite /BiPureForall. unseal. done. Qed.

#[export] Instance ouPred_persistently_forall M : BiPersistentlyForall (ouPredI M).
Proof. rewrite /BiPersistentlyForall. unseal. done. Qed.

#[export] Instance ouPred_persistently_impl_plainly M : BiPersistentlyImplPlainly (ouPredI M).
Proof.
  rewrite /BiPersistentlyImplPlainly. unseal.
  split=> ??? /= H ????? HP.
  eapply ouPred_mono; eauto.
  eapply H; eauto.
  eapply (cmra_validN_le(A:=M)); eauto.
Qed.

Module ouPred.
Include ouPred_unseal.
Section ouPred.
Context {M : uora}.
Implicit Types φ : Prop.
Implicit Types P Q : ouPred M.
Implicit Types A : Type.
Arguments ouPred_holds {_} !_ _ _ /.
Hint Immediate ouPred_in_entails : core.

Global Instance ownM_ne : NonExpansive (@ouPred_ownM M).
Proof.
  intros n a b Ha.
  unseal; split=> n' x ? /=. by rewrite (dist_le _ _ _ _ Ha); last lia.
Qed.
Global Instance ownM_proper: Proper ((≡) ==> (⊣⊢)) (@ouPred_ownM M) := ne_proper _.

Global Instance ora_valid_ne {A : ora} :
  NonExpansive (@ouPred_ora_valid M A).
Proof.
  intros n a b Ha; unseal; split=> n' x ? /=.
  by rewrite (dist_le _ _ _ _ Ha); last lia.
Qed.
Global Instance ora_valid_proper {A : ora} :
  Proper ((≡) ==> (⊣⊢)) (@ouPred_ora_valid M A) := ne_proper _.

Lemma bupd_ne : NonExpansive (@ouPred_bupd M).
Proof.
  intros n P Q HPQ.
  unseal; split=> n' x; split; intros HP k yf ??;
    destruct (HP k yf) as (x'&?&?); auto;
    exists x'; split; auto; apply HPQ; eauto; eapply (cmra_validN_op_l(A:=M)); eauto.
Qed.

(** BI instances *)

Global Instance ouPred_plainly_exist_1 : BiPlainlyExist (ouPredI M).
Proof.
  unfold BiPlainlyExist, plainly, bi_plainly_plainly.
  unseal; split => /= ???[??]; eauto.
Qed.

(** Limits *)
Lemma entails_lim (cP cQ : chain (ouPredO M)) :
  (∀ n, cP n ⊢ cQ n) → compl cP ⊢ compl cQ.
Proof.
  intros Hlim; split=> n m ? HP.
  eapply ouPred_holds_ne, Hlim, HP; rewrite ?conv_compl; eauto.
Qed.

(** Basic update modality *)
Notation "|==> P" := (ouPred_bupd P) : bi_scope.

Lemma bupd_intro P : P ⊢ |==> P.
Proof.
  unseal. split=> n x ? HP k yf ?; exists x; split; first done.
  apply ouPred_mono with n x; eauto using (cmra_validN_op_l(A:=M)).
Qed.
Lemma bupd_mono P Q : (P ⊢ Q) → (|==> P) ⊢ |==> Q.
Proof.
  unseal. intros HPQ; split=> n x ? HP k yf ??.
  destruct (HP k yf) as (x'&?&?); eauto.
  exists x'; split; eauto.
  eapply ouPred_in_entails; eauto. eapply (cmra_validN_op_l(A:=M)); eauto.
Qed.
Lemma bupd_trans P : (|==> |==> P) ⊢ |==> P.
Proof. unseal; split; naive_solver. Qed.
Lemma bupd_frame_r P R : (|==> P) ∗ R ⊢ |==> P ∗ R.
Proof.
  unseal; split; intros n x ? (x1&x2&Hx&HP&?) k yf ??.
  eapply ora_validN_orderN in H2; last by eapply ora_monoN_r, ora_orderN_le; [done | lia].
  destruct (HP k (x2 ⋅ yf)) as (x'&?&?); eauto.
  { by rewrite assoc. }
  exists (x' ⋅ x2); split; first by rewrite -assoc.
  exists x', x2. eauto using ouPred_mono, (cmra_validN_op_l(A:=M)), cmra_validN_op_r.
Qed.
Lemma bupd_plainly P : (|==> ■ P) ⊢ ■ P.
Proof.
  unseal; split => n x Hnx /= Hng.
  destruct (Hng n ε) as [? [_ Hng']]; try rewrite right_id; auto.
Qed.

(* Own *)
Lemma ownM_op (a1 a2 : M) :
  ouPred_ownM (a1 ⋅ a2) ⊣⊢ ouPred_ownM a1 ∗ ouPred_ownM a2.
Proof.
  rewrite /bi_sep /=; unseal. split=> n x ?; split; simpl; eauto.
  intros (x1&x2&Hx&Ha1&Ha2).
  setoid_rewrite <- Hx. etrans; first eapply ora_orderN_op; eauto.
  rewrite !(comm op x1); etrans; first eapply ora_orderN_op; eauto.
Qed.
Lemma persistently_ownM_core (a : M) :
  ouPred_ownM a ⊢ bi_persistently (ouPred_ownM (core a)).
Proof.
  rewrite /bi_persistently /=. unseal.
  split=> n x Hx /=. by apply ora_core_monoN.
Qed.
Lemma ownM_unit : ⊢ ouPred_ownM (ε:M).
Proof. unseal; split=> n x ? ?; done. Qed.

Lemma ownM_unit_discard : ouPred_ownM (ε:M) ⊢ emp.
Proof. unseal; split=> n x ? ?; done. Qed.

Lemma ownM_core_discard (a : M) : ouPred_ownM (core a) ⊢ emp.
Proof. unseal; split=> n x ? ?.
  unfold ouPred_ownM_def in *; simpl in *.
  etrans; last done.
  apply ora_order_orderN, uora_unit_order_core.
Qed.

Lemma later_ownM (a : M) : ▷ ouPred_ownM a ⊢ ∃ b, ouPred_ownM b ∧ ▷ (a ≡ b).
Proof.
  rewrite /bi_and /bi_later /bi_exist
    /internal_eq /bi_internal_eq_internal_eq /=; unseal.
  split=> -[|n] x /= ? Hax; first by eauto using ucmra_unit_leastN.
  destruct (ora_extend n x a) as (a'&Hx&?); auto using cmra_validN_S.
  exists a'. split; auto.
Qed.

Lemma ownM_order (a b : M) :
  a ≼ₒ b -> ouPred_ownM b ⊢ ouPred_ownM a.
Proof.
  rewrite ora_order_orderN.
  split => ???; unseal.
  etrans; eauto.
Qed.

Lemma bupd_ownM_updateP x (Φ : M → Prop) :
  cmra_updateP(A := uora_oraR M) x Φ → ouPred_ownM x ⊢ |==> ∃ y, ⌜Φ y⌝ ∧ ouPred_ownM y.
Proof.
  unseal=> Hup; split=> n x2 ? /= Hx k yf ? Hxy.
  eapply ora_validN_orderN in Hxy; last (eapply ora_monoN_r, ora_orderN_le; [done | lia]).
  destruct (Hup k (Some yf)) as (y&?&?); simpl in *; first done.
  eauto.
Qed.

(* Valid *)
Lemma discrete_valid {A : ora} `{!OraDiscrete A} (a : A) :
  ✓ a ⊣⊢ (⌜✓ a⌝ : ouPred M).
Proof. unseal. split=> n x _. by rewrite /= -ora_discrete_valid_iff. Qed.
Lemma ownM_valid (a : M) : ouPred_ownM a ⊢ ✓ a.
Proof.
  unseal; split=> n x Hv /= Hn; ofe_subst; eauto using ora_validN_orderN.
Qed.
Lemma ora_valid_intro {A : ora} (a : A) :
  ✓ a → bi_emp_valid (PROP:=ouPredI M) (✓ a).
Proof. unseal=> ?; split=> n x ? _ /=; by apply cmra_valid_validN. Qed.
Lemma ora_valid_elim {A : ora} (a : A) : ¬ ✓{0} a → ✓ a ⊢ (False : ouPred M).
Proof.
  intros Ha. unseal. split=> n x ??; apply Ha, cmra_validN_le with n; auto.
Qed.
Lemma plainly_ora_valid_1 {A : ora} (a : A) : ✓ a ⊢ plainly (✓ a : ouPred M).
Proof. by unseal. Qed.
Lemma ora_valid_weaken {A : ora} (a b : A) : ✓ (a ⋅ b) ⊢ (✓ a : ouPred M).
Proof. unseal; split=> n x _; apply cmra_validN_op_l. Qed.

Lemma prod_validI {A B : ora} (x : A * B) : ✓ x ⊣⊢ (✓ x.1 ∧ ✓ x.2 : ouPred M).
Proof. by unseal. Qed.
Lemma option_validI {A : ora} (mx : option A) :
  ✓ mx ⊣⊢ match mx with Some x => ✓ x | None => True : ouPred M end.
Proof. unseal. by destruct mx. Qed.

Lemma discrete_fun_validI `{Finite A} {B : A → uora} (g : discrete_fun B) :
  (✓ g : ouPred M) ⊣⊢ ∀ i, ✓ g i.
Proof. by ouPred.unseal. Qed.

Notation "P ⊢ Q" := (bi_entails (PROP:=ouPredI M) P Q).

Lemma valid_entails {A B : ora} (a : A) (b : B) :
  (∀ n, ✓{n} a → ✓{n} b) → ✓ a ⊢ ✓ b.
Proof. unseal=> Hval. split=>n x ?. apply Hval. Qed.

(* Basic update modality *)
Lemma ouPred_bupd_mixin : BiBUpdMixin (ouPredI M) ouPred_bupd.
Proof.
  split.
  - exact: bupd_ne.
  - exact: bupd_intro.
  - exact: bupd_mono.
  - exact: bupd_trans.
  - exact: bupd_frame_r.
Qed.
Global Instance ouPred_bi_bupd : BiBUpd (ouPredI M) := {| bi_bupd_mixin := ouPred_bupd_mixin |}.

End ouPred.
End ouPred.
