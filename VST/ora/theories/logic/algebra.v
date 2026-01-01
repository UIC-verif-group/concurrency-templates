From iris.algebra Require Import cmra view auth agree csum list excl gmap.
From iris.algebra.lib Require Import excl_auth frac_auth gmap_view dfrac_agree.
From iris_ora.algebra Require Import ora osum gmap agree view auth excl_auth frac_auth gmap_view.
From iris_ora.logic Require Import oupred.
From iris.prelude Require Import options.
Import ouPred.

(** Internalized properties of our ORA constructions. *)

Section oupred.
Context {M : uora}.

(* Force implicit argument M *)
Notation "P ⊢ Q" := (bi_entails (PROP:=ouPredI M) P Q).
Notation "P ⊣⊢ Q" := (equiv (A:=ouPredI M) P%I Q%I).
Notation "⊢ Q" := (bi_entails (PROP:=ouPredI M) True Q).

(*Lemma frac_validI (q : Qp) : ✓ q ⊣⊢ ⌜q ≤ 1⌝%Qp.
Proof. rewrite ouPred.discrete_valid frac_valid //. Qed.*)

Section gmap_ofe.
  Context `{Countable K} {A : ofe}.
  Implicit Types m : gmap K A.
  Implicit Types i : K.

  Lemma gmap_equivI m1 m2 : m1 ≡ m2 ⊣⊢ ∀ i, m1 !! i ≡ m2 !! i.
  Proof. by ouPred.unseal. Qed.
End gmap_ofe.

Section gmap_ora.
  Context `{Countable K} {A : ora}.
  Implicit Types m : gmap K A.

  Lemma gmap_validI m : ✓ m ⊣⊢ ∀ i, ✓ (m !! i).
  Proof. by ouPred.unseal. Qed.
  Lemma singleton_validI i x : ✓ ({[ i := x ]} : gmap K A) ⊣⊢ ✓ x.
  Proof.
    rewrite gmap_validI. apply: anti_symm.
    - rewrite (bi.forall_elim i) lookup_singleton option_validI. done.
    - apply bi.forall_intro=>j. destruct (decide (i = j)) as [<-|Hne].
      + rewrite lookup_singleton option_validI. done.
      + rewrite lookup_singleton_ne // option_validI.
        apply bi.True_intro.
  Qed.
End gmap_ora.

Section list_ofe.
  Context {A : ofe}.
  Implicit Types l : list A.

  Lemma list_equivI l1 l2 : l1 ≡ l2 ⊣⊢ ∀ i, l1 !! i ≡ l2 !! i.
  Proof. ouPred.unseal; constructor=> n x ?. apply list_dist_lookup. Qed.
End list_ofe.

Section excl.
  Context {A : ofe}.
  Implicit Types a b : A.
  Implicit Types x y : excl A.

  Lemma excl_equivI x y :
    x ≡ y ⊣⊢ match x, y with
                        | Excl a, Excl b => a ≡ b
                        | ExclBot, ExclBot => True
                        | _, _ => False
                        end.
  Proof.
    ouPred.unseal. do 2 split.
    - by destruct 1.
    - by destruct x, y; try constructor.
  Qed.
  Lemma excl_validI x :
    ✓ x ⊣⊢ if x is ExclBot then False else True.
  Proof. ouPred.unseal. by destruct x. Qed.
End excl.

Section agree.
  Context {A : ofe}.
  Implicit Types a b : A.
  Implicit Types x y : agree A.

  Lemma agree_equivI a b : to_agree a ≡ to_agree b ⊣⊢ (a ≡ b).
  Proof.
    ouPred.unseal. do 2 split.
    - intros Hx. exact: (inj to_agree).
    - intros Hx. exact: to_agree_ne.
  Qed.
  Lemma agree_validI x y : ✓ (x ⋅ y) ⊢ x ≡ y.
  Proof. ouPred.unseal; split=> r n _ ?; by apply: agree_op_invN. Qed.

  Lemma to_agree_validI a : ⊢ ✓ to_agree a.
  Proof. ouPred.unseal; done. Qed.
  Lemma to_agree_op_validI a b : ✓ (to_agree a ⋅ to_agree b) ⊣⊢ a ≡ b.
  Proof.
    apply bi.entails_anti_sym.
    - rewrite agree_validI. by rewrite agree_equivI.
    - pose (Ψ := (λ x : A, ✓ (to_agree a ⋅ to_agree x) : ouPred M)%I).
      assert (NonExpansive Ψ) as ? by solve_proper.
      rewrite (internal_eq_rewrite a b Ψ).
      eapply bi.impl_elim; first reflexivity.
      etrans; first apply bi.True_intro.
      subst Ψ; simpl.
      rewrite agree_idemp. apply to_agree_validI.
  Qed.

  Lemma to_agree_uninjI x : ✓ x ⊢ ∃ a, to_agree a ≡ x.
  Proof. ouPred.unseal. split=> n y _. exact: to_agree_uninjN. Qed.
End agree.

Section csum_ofe.
  Context {A B : ofe}.
  Implicit Types a : A.
  Implicit Types b : B.

  Lemma csum_equivI (x y : csum A B) :
    x ≡ y ⊣⊢ match x, y with
                        | Cinl a, Cinl a' => a ≡ a'
                        | Cinr b, Cinr b' => b ≡ b'
                        | CsumBot, CsumBot => True
                        | _, _ => False
                        end.
  Proof.
    ouPred.unseal; do 2 split; first by destruct 1.
      by destruct x, y; try destruct 1; try constructor.
  Qed.
End csum_ofe.

Section csum_ora.
  Context {A B : ora}.
  Implicit Types a : A.
  Implicit Types b : B.

  Lemma csum_validI (x : csum A B) :
    ✓ x ⊣⊢ match x with
                      | Cinl a => ✓ a
                      | Cinr b => ✓ b
                      | CsumBot => False
                      end.
  Proof. ouPred.unseal. by destruct x. Qed.
End csum_ora.

Section view.
  Context {A} {B : uora} (rel : view_rel A B).
  Implicit Types a : A.
  Implicit Types b : B.
  Implicit Types x y : view rel.

  Context (view_rel_order : ∀n a b1 b2, b1 ≼ₒ{n} b2 → rel n a b2 → rel n a b1).

  Local Canonical Structure viewR := (view.viewR rel view_rel_order).

  Lemma view_auth_dfrac_op_validI (relI : ouPred M) dq1 dq2 a1 a2 :
    (∀ n (x : M), rel n a1 ε ↔ relI n x) →
    ✓ (●V{dq1} a1 ⋅ ●V{dq2} a2 : viewR) ⊣⊢ ⌜✓(dq1 ⋅ dq2)⌝ ∧ a1 ≡ a2 ∧ relI.
  Proof.
    intros Hrel. apply (anti_symm _).
    - ouPred.unseal. split=> n x _ /=.
      rewrite /ouPred_holds /=.
      intros Hv; pose proof (view_auth_dfrac_op_invN _ _ _ _ _ _ Hv) as Heq.
      rewrite -Heq -view_auth_dfrac_op in Hv.
      apply view_auth_dfrac_validN in Hv as [? ?]; split; last split; try done.
      rewrite -Hrel //.
    - ouPred.unseal. split=> n x _ /=.
      intros (? & Heq & ?%Hrel).
      rewrite /ouPred_internal_eq_def /ouPred_holds in Heq.
      rewrite /ouPred_holds /= -Heq view_auth_dfrac_op_validN //.
  Qed.

  Lemma view_both_dfrac_validI_1 (relI : ouPred M) dq a b :
    (∀ n (x : M), rel n a b → relI n x) →
    ✓ (●V{dq} a ⋅ ◯V b : viewR) ⊢ ⌜✓dq⌝ ∧ relI.
  Proof.
    intros Hrel. ouPred.unseal. split=> n x _ /=.
    rewrite /ouPred_holds /= view_both_dfrac_validN. by move=> [? /Hrel].
  Qed.
  Lemma view_both_dfrac_validI_2 (relI : ouPred M) dq a b :
    (∀ n (x : M), relI n x → rel n a b) →
    ⌜✓dq⌝ ∧ relI ⊢ ✓ (●V{dq} a ⋅ ◯V b : viewR).
  Proof.
    intros Hrel. ouPred.unseal. split=> n x _ /=.
    rewrite /ouPred_holds /= view_both_dfrac_validN. by move=> [? /Hrel].
  Qed.
  Lemma view_both_dfrac_validI (relI : ouPred M) dq a b :
    (∀ n (x : M), rel n a b ↔ relI n x) →
    ✓ (●V{dq} a ⋅ ◯V b : viewR) ⊣⊢ ⌜✓dq⌝ ∧ relI.
  Proof.
    intros. apply (anti_symm _);
      [apply view_both_dfrac_validI_1|apply view_both_dfrac_validI_2]; naive_solver.
  Qed.

  Lemma view_both_validI_1 (relI : ouPred M) a b :
    (∀ n (x : M), rel n a b → relI n x) →
    ✓ (●V a ⋅ ◯V b : viewR) ⊢ relI.
  Proof. intros. by rewrite view_both_dfrac_validI_1 // bi.and_elim_r. Qed.
  Lemma view_both_validI_2 (relI : ouPred M) a b :
    (∀ n (x : M), relI n x → rel n a b) →
    relI ⊢ ✓ (●V a ⋅ ◯V b : viewR).
  Proof.
    intros. rewrite -view_both_dfrac_validI_2 //.
    apply bi.and_intro; [|done]. by apply bi.pure_intro.
  Qed.
  Lemma view_both_validI (relI : ouPred M) a b :
    (∀ n (x : M), rel n a b ↔ relI n x) →
    ✓ (●V a ⋅ ◯V b : viewR) ⊣⊢ relI.
  Proof.
    intros. apply (anti_symm _);
      [apply view_both_validI_1|apply view_both_validI_2]; naive_solver.
  Qed.

  Lemma view_auth_dfrac_validI (relI : ouPred M) dq a :
    (∀ n (x : M), relI n x ↔ rel n a ε) →
    ✓ (●V{dq} a : viewR) ⊣⊢ ⌜✓dq⌝ ∧ relI.
  Proof.
    intros. rewrite -(right_id ε op (●V{dq} a)). by apply view_both_dfrac_validI.
  Qed.
  Lemma view_auth_validI (relI : ouPred M) a :
    (∀ n (x : M), relI n x ↔ rel n a ε) →
    ✓ (●V a : viewR) ⊣⊢ relI.
  Proof. intros. rewrite -(right_id ε op (●V a)). by apply view_both_validI. Qed.

  Lemma view_frag_validI (relI : ouPred M) b :
    (∀ n (x : M), relI n x ↔ ∃ a, rel n a b) →
    ✓ (◯V b : viewR) ⊣⊢ relI.
  Proof. ouPred.unseal=> Hrel. split=> n x _. by rewrite Hrel. Qed.
End view.

Section auth.
  Context {A : uora}.
  Implicit Types a b : A.
  Implicit Types x y : auth A.

  Context (auth_order : ∀n (x y : A), ✓{n} y → x ≼ₒ{n} y → x ≼{n} y).

  Local Canonical Structure authR := (auth.authR _ auth_order).
  Local Canonical Structure authUR := (auth.authUR _ auth_order).

  Lemma auth_auth_dfrac_validI dq a : ✓ (●{dq} a : authR) ⊣⊢ ⌜✓dq⌝ ∧ ✓ (a : uora_oraR _).
  Proof.
    apply view_auth_dfrac_validI=> n. ouPred.unseal; split; [|by intros [??]].
    split; [|done]. apply ucmra_unit_leastN.
  Qed.
  Lemma auth_auth_validI a : ✓ (● a : authR) ⊣⊢ ✓ (a : uora_oraR _).
  Proof.
    by rewrite auth_auth_dfrac_validI bi.pure_True // left_id.
  Qed.

  Lemma auth_frag_validI a : ✓ (◯ a : authR) ⊣⊢ ✓ (a : uora_oraR _).
  Proof.
    apply view_frag_validI=> n x.
    rewrite auth_view_rel_exists. by ouPred.unseal.
  Qed.

  Lemma auth_auth_dfrac_op_validI dq1 dq2 a b :
    ✓ (●{dq1} a ⋅ ●{dq2} b : authR) ⊣⊢ ⌜✓(dq1 ⋅ dq2)⌝ ∧ a ≡ b ∧ ✓ (a : uora_oraR _).
  Proof.
    apply view_auth_dfrac_op_validI=> n. ouPred.unseal.
    split.
    - intros (? & ?); done.
    - split; last done. apply ucmra_unit_leastN.
  Qed.
  Lemma auth_both_dfrac_validI dq a b :
    ✓ (●{dq} a ⋅ ◯ b : authR) ⊣⊢ ⌜✓dq⌝ ∧ (∃ c, a ≡ b ⋅ c) ∧ ✓ (a : uora_oraR _).
  Proof. apply view_both_dfrac_validI=> n. by ouPred.unseal. Qed.
  Lemma auth_both_validI a b :
    ✓ (● a ⋅ ◯ b : authR) ⊣⊢ (∃ c, a ≡ b ⋅ c) ∧ ✓ (a : uora_oraR _).
  Proof.
    by rewrite auth_both_dfrac_validI bi.pure_True // left_id.
  Qed.

End auth.

Section excl_auth.
  Context {A : ofe}.
  Implicit Types a b : A.

  Lemma excl_auth_agreeI a b : ✓ (●E a ⋅ ◯E b : excl_authR A) ⊢ (a ≡ b).
  Proof.
    rewrite auth_both_validI bi.and_elim_l.
    apply bi.exist_elim=> -[[c|]|];
      by rewrite option_equivI /= excl_equivI //= bi.False_elim.
  Qed.
End excl_auth.

Section frac_auth.
  Context {A : cmra}.

(*  Lemma frac_auth_auth_validI (a : A) : ✓ (●F a : frac_authR A) ⊣⊢ ✓ a.
  Proof.
    rewrite /frac_auth_auth auth_auth_validI option_validI prod_validI /=.
    unshelve erewrite (@discrete_valid) by (apply ext_order.positive_discrete, _).
    rewrite bi.pure_True // bi.True_and //.
  Qed.

  Lemma frac_auth_frag_validI q a : ✓ (◯F{q} a : frac_authR A) ⊣⊢ ⌜✓ q⌝ ∧ ✓ a.
  Proof.
    rewrite /frac_auth_frag auth_frag_validI option_validI prod_validI /=.
    unshelve erewrite (@discrete_valid) by (apply ext_order.positive_discrete, _); done.
  Qed.

  Lemma frac_auth_frag_full_validI a : ✓ (◯F a : frac_authR A) ⊣⊢ ✓ a.
  Proof.
    rewrite frac_auth_frag_validI bi.pure_True // bi.True_and //.
  Qed.*)

  Lemma frac_auth_agreeI q a b : ✓ (●F a ⋅ ◯F{q} b : frac_authR A) ⊢ (if decide (q = 1%Qp) then a ≡ b else ∃ c, a ≡ b ⋅ c)%I.
  Proof.
    ouPred.unseal. split=> n x _ /=.
    destruct (decide _); rewrite /ouPred_holds /=.
    - subst; apply frac_auth_agreeN.
    - intros (? & _)%auth_both_validN.
      apply cmra.Some_includedN in H as [H | H].
      { inv H. }
      apply prod_includedN in H as (? & ?); auto.
  Qed.

  Lemma frac_auth_agree_fullI a b : ✓ (●F a ⋅ ◯F b : frac_authR A) ⊢ a ≡ b.
  Proof.
    rewrite frac_auth_agreeI //.
  Qed.

End frac_auth.

(*Section dfrac_agree.
  Context {A : ofe}.
  Implicit Types a b : A.

  Lemma dfrac_agree_validI dq a : ✓ (to_dfrac_agree dq a) ⊣⊢ ⌜✓ dq⌝.
  Proof.
    rewrite prod_validI /= ouPred.discrete_valid. apply bi.entails_anti_sym.
    - by rewrite bi.and_elim_l.
    - apply bi.and_intro; first done. etrans; last apply to_agree_validI.
      apply bi.True_intro.
  Qed.

  Lemma dfrac_agree_validI_2 dq1 dq2 a b :
    ✓ (to_dfrac_agree dq1 a ⋅ to_dfrac_agree dq2 b) ⊣⊢ ⌜✓ (dq1 ⋅ dq2)⌝ ∧ (a ≡ b).
  Proof.
    rewrite prod_validI /= ouPred.discrete_valid to_agree_op_validI //.
  Qed.

  Lemma frac_agree_validI q a : ✓ (to_frac_agree q a) ⊣⊢ ⌜(q ≤ 1)%Qp⌝.
  Proof.
    rewrite dfrac_agree_validI dfrac_valid_own //.
  Qed.

  Lemma frac_agree_validI_2 q1 q2 a b :
    ✓ (to_frac_agree q1 a ⋅ to_frac_agree q2 b) ⊣⊢ ⌜(q1 + q2 ≤ 1)%Qp⌝ ∧ (a ≡ b).
  Proof.
    rewrite dfrac_agree_validI_2 dfrac_valid_own //.
  Qed.
End dfrac_agree.*)

Section gmap_view.
  Context {K : Type} `{Countable K} {V : ofe}.
  Implicit Types (m : gmap K V) (k : K) (dq : dfrac) (v : V).

  Lemma gmap_view_both_validI m k dq v :
    ✓ (gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k dq v : gmap_viewR K V) ⊢
    ✓ dq ∧ m !! k ≡ Some v.
  Proof.
    rewrite /gmap_view_auth /gmap_view_frag. apply view_both_validI_1.
    intros n a. ouPred.unseal. apply gmap_view.gmap_view_rel_lookup.
  Qed.

  Lemma gmap_view_frag_op_validI k dq1 dq2 v1 v2 :
    ✓ (gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2 : gmap_viewR K V) ⊣⊢
    ✓ (dq1 ⋅ dq2) ∧ v1 ≡ v2.
  Proof.
    rewrite /gmap_view_frag -view_frag_op. apply view_frag_validI=> n x.
    rewrite gmap_view.gmap_view_rel_exists singleton_op singleton_validN.
    rewrite pair_validN to_agree_op_validN. by ouPred.unseal.
  Qed.

End gmap_view.

End oupred.
