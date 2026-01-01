Set Warnings "-hiding-delimiting-key, -redundant-canonical-projection".
Require Import flows.flows flows.multiset_flows.
Require Import Coq.Logic.ProofIrrelevance.
From iris_ora Require Export ora.

Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments pcore _ _ !_ /.

#[local] Instance Int_EqDecision : EqDecision Integers.Int.int.
Proof.
  intros x y; destruct ((Integers.Int.eq_dec x y)); [left|right]; congruence.
Qed.

#[local] Instance Int_EqDecision64 : EqDecision Integers.Int64.int.
Proof.
  intros x y; destruct ((Integers.Int64.eq_dec x y)); [left|right]; congruence.
Qed.

#[local] Instance binary64_EqDecision : EqDecision Bits.binary64.
Proof.
  intros x y; destruct x; destruct y;
    destruct (decide (s = s0)) as [Hs|Hs]; subst; rewrite / Decision; auto;
    try (right; congruence).
  destruct (decide (pl = pl0)); subst; try (pose proof (proof_irrelevance _ e e0) as -> );
      try repeat (left; congruence); try repeat (right; congruence).
  destruct (decide (e = e1)); destruct (decide (m = m0)); subst;
      try (pose proof (proof_irrelevance _ e0 e2) as ->);
      try (left; congruence); try (right; congruence).
Qed.

#[local] Instance Float_EqDecision : EqDecision Floats.float := binary64_EqDecision.

#[local] Instance binary32_EqDecision : EqDecision Bits.binary32.
Proof.
  intros x y; destruct x; destruct y;
    destruct (decide (s = s0)) as [Hs|Hs]; subst; rewrite / Decision; auto;
    try (right; congruence).
  destruct (decide (pl = pl0)); subst; try (pose proof (proof_irrelevance _ e e0) as -> );
    try repeat (left; congruence); try repeat (right; congruence).
  destruct (decide (e = e1)); destruct (decide (m = m0)); subst;
    try (pose proof (proof_irrelevance _ e0 e2) as ->);
    try (left; congruence); try (right; congruence).
Qed.

#[local] Instance Float32_EqDecision : EqDecision Floats.float32 := binary32_EqDecision.

#[local] Instance Ptrofs_EqDecision : EqDecision Integers.Ptrofs.int.
Proof.
  intros x y; destruct x as [xv Hx], y as [yv Hy];
    destruct (decide (xv = yv)) as [->|Hneq];
    try (left; f_equal; apply proof_irrelevance); try (right; congruence).
Qed.

#[local] Instance Int_Countable : Countable Integers.Int.int.
Proof.
  apply (inj_countable Integers.Int.unsigned (fun z => Some (Integers.Int.repr z))).
  intros x; now rewrite Integers.Int.repr_unsigned.
Qed.

#[local] Instance Int_Countable64 : Countable Integers.Int64.int .
Proof.
  apply (inj_countable Integers.Int64.unsigned (fun z => Some (Integers.Int64.repr z))).
  intros x; now rewrite Integers.Int64.repr_unsigned.
Qed.

#[local] Instance Float_Countable : Countable Floats.float.
Proof.
  apply (inj_countable Floats.Float.to_bits (fun p => Some (Floats.Float.of_bits p))).
  intros x; now rewrite Floats.Float.of_to_bits.
Qed.

#[local] Instance Float32_Countable : Countable Floats.float32.
Proof.
  apply (inj_countable Floats.Float32.to_bits (fun p => Some (Floats.Float32.of_bits p))).
  intros x; now rewrite Floats.Float32.of_to_bits.
Qed.

#[local] Instance Ptrofs_Countable : Countable Integers.Ptrofs.int.
Proof.
  apply (inj_countable Integers.Ptrofs.unsigned (fun z => Some (Integers.Ptrofs.repr z))).
  intros x; now rewrite Integers.Ptrofs.repr_unsigned.
Qed.

Global Instance Node_EqDecision: EqDecision Node.
Proof. intros x y; apply Val.eq. Qed.

Global Instance Node_countable : Countable Node.
Proof.
  apply (inj_countable
           (λ v,
             match v with
             | Vundef => inl O
             | Vint i => inr (inl (inl (encode i)))
             | Vlong l => inr (inl (inr (encode l)))
             | Vfloat f => inr (inr (inl (encode f)))
             | Vsingle f32 => inr (inr (inr (inl (encode f32))))
             | Vptr b ofs => inr (inr (inr (inr (encode (b, ofs)))))
             end)
           (λ x,
             match x with
             | inl O => Some Vundef
             | inr (inl (inl i)) => option_map Vint (decode i)
             | inr (inl (inr l)) => option_map Vlong (decode l)
             | inr (inr (inl f)) => option_map Vfloat (decode f)
             | inr (inr (inr (inl f32))) => option_map Vsingle (decode f32)
             | inr (inr (inr (inr p))) =>
                 option_map (fun '(b, ofs) => Vptr b ofs) (decode p)
             | _ => None
             end));
  intros v; destruct v; simpl; try rewrite decode_encode; reflexivity.
Qed.

Section flows.
  Context `{flowdom : Type} `{CCM flowdom}.
  #[local] Instance flows_order : OraOrder flowintT := fun (a b: flowintT) => a = b \/ b = intUndef.
  
  Lemma Increasing_flows : forall a, Increasing a <-> a = ε \/ a = intUndef.
  Proof.
    split; intros Ha.
    - specialize (Ha ε).
      rewrite right_id in Ha.
      inversion Ha; auto.
    - intros ?; destruct Ha.
      + subst a. rewrite left_id; hnf; auto. 
      + hnf. subst a. right. by rewrite (intComp_undef_op).
  Qed.

  Definition flows_ora_mixin : DORAMixin flowintT.
  Proof.
    split; try apply _; try done.
    - intros ???.
      rewrite Increasing_flows.
      destruct x; inversion H0; auto.
    - intros ???; inversion H0; hnf; auto.
    - intros ?????; inversion H0; subst; eexists; split; eauto; hnf; [left|right]; auto.
    - intros ?????; inversion H1; subst; auto; hnf; auto.
    - intros ????; inversion H0; subst; hnf; [left | right]; auto;
        by pose proof (intComp_undef_op y).
    - intros ????; inversion H1; subst; [auto | contradiction].
    - intros ???;
      destruct cx; unfold pcore, flowintRAcore; destruct x; intros H0;
      inversion H; subst; try eauto.
      destruct (int f0 ⋅ y); eexists; split; try done; subst; hnf; [left | right]; eauto;
      eexists.
      + rewrite (intComp_undef_op y);
        eexists; split; last first; eauto; hnf; auto.
      + inversion H0; subst. inversion H3.
      + rewrite (intComp_undef_op y).
        eexists; split; eauto; hnf; auto.
  Qed.
  
  Canonical Structure flowsRA := discreteOra flowintT flows_ora_mixin.
  Global Instance flows_ora_discrete : OraDiscrete flowintT.
  Proof.
    apply discrete_ora_discrete.
  Qed.
  
  Canonical Structure flowintUR : uora := Uora flowintT flowint_ucmra_mixin.
End flows.

Section multiset_flow.
Context `{Countable K}. 
  Global Canonical Structure multiset_flowint_ur : uora := @flowintUR (K_multiset(K := K)) _.
End multiset_flow.
