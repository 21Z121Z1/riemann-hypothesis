import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetFoldIntermediateSubgroup
section
open GlobalTheory.LKCount

namespace GlobalTheory.ConjugateFold

variable {G : Type} [Group G]

end GlobalTheory.ConjugateFold

namespace GlobalTheory.ConjugateFold

variable {G : Type} [Group G]

noncomputable def foldMap (Γ' T K : Subgroup G) (hΓT : Γ' ≤ T) (y : G)
    (p : DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) :
    {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) //
      DoubleCoset.mk T K (Quotient.out q) = DoubleCoset.mk T K y} :=
  ⟨DoubleCoset.mk Γ' K (((Quotient.out p : T) : G) * y), by
    obtain ⟨g, k, hg, hk, he⟩ := DoubleCoset.mk_out_eq_mul Γ' K (((Quotient.out p : T) : G) * y)
    rw [he, DoubleCoset.eq]
    refine ⟨(g * ((Quotient.out p : T) : G))⁻¹, T.inv_mem (T.mul_mem (hΓT hg) (Quotient.out p).2),
      k⁻¹, K.inv_mem hk, by group⟩⟩

end GlobalTheory.ConjugateFold

namespace GlobalTheory.ConjugateFold

variable {G : Type} [Group G]

end GlobalTheory.ConjugateFold

namespace GlobalTheory

variable {G : Type} [Group G] in
private lemma mem_map_conj_iff_inv_mul_mul_mem' (K : Subgroup G) (a x : G) :
    x ∈ K.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

variable {G : Type} [Group G] in
private lemma foldMap_bijective' (Γ' T K : Subgroup G) (hΓT : Γ' ≤ T) (y : G) :
    Function.Bijective (_root_.GlobalTheory.ConjugateFold.foldMap Γ' T K hΓT y) := by
  constructor
  · intro p p' h
    have h' : DoubleCoset.mk Γ' K (((Quotient.out p : T) : G) * y) =
        DoubleCoset.mk Γ' K (((Quotient.out p' : T) : G) * y) := congrArg Subtype.val h
    obtain ⟨γ, hγ, k, hk, he⟩ := (DoubleCoset.eq Γ' K _ _).1 h'
    have hmem : y * k * y⁻¹ = ((Quotient.out p : T) : G)⁻¹ * γ⁻¹ * ((Quotient.out p' : T) : G) := by
      rw [eq_mul_inv_of_mul_eq he]; group
    have hT : y * k * y⁻¹ ∈ T := by
      rw [hmem]
      exact T.mul_mem (T.mul_mem (T.inv_mem (Quotient.out p).2) (T.inv_mem (hΓT hγ))) (Quotient.out p').2
    rw [← DoubleCoset.out_eq' _ _ p, ← DoubleCoset.out_eq' _ _ p', DoubleCoset.eq]
    refine ⟨⟨γ, hΓT hγ⟩, by rw [Subgroup.mem_subgroupOf]; exact hγ, ⟨y * k * y⁻¹, hT⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem']
      refine ⟨hT, ?_⟩
      rw [show y⁻¹ * (y * k * y⁻¹) * y = k by group]
      exact hk
    · apply Subtype.ext
      push_cast
      rw [eq_mul_inv_of_mul_eq he]
      group
  · rintro ⟨q, hq⟩
    obtain ⟨t, ht, k, hk, hqe⟩ := (DoubleCoset.eq T K _ _).1 hq.symm
    refine ⟨DoubleCoset.mk (Γ'.subgroupOf T) ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T)
      ⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    change DoubleCoset.mk Γ' K (((Quotient.out (DoubleCoset.mk (Γ'.subgroupOf T)
      ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T) ⟨t, ht⟩) : T) : G) * y) = q
    obtain ⟨γ, h, hγ, hh, hout⟩ := DoubleCoset.mk_out_eq_mul (Γ'.subgroupOf T)
      ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T) ⟨t, ht⟩
    rw [hout, ← DoubleCoset.out_eq' Γ' K q, DoubleCoset.eq]
    rw [Subgroup.mem_subgroupOf] at hγ
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem'] at hh
    refine ⟨(γ : G)⁻¹, Γ'.inv_mem hγ, (y⁻¹ * h * y)⁻¹ * k, K.mul_mem (K.inv_mem hh.2) hk, ?_⟩
    rw [hqe]
    push_cast
    group

variable {G : Type} [Group G] in
private lemma card_subgroupOf_inf_map_conj_eq (Γ' T K : Subgroup G) (hΓT : Γ' ≤ T) (t : T) (y : G) :
    Nat.card (Γ'.subgroupOf T ⊓ ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T).map
        (MulAut.conj t).toMonoidHom : Subgroup T) =
      Nat.card (Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom : Subgroup G) := by
  set S : Subgroup T := Γ'.subgroupOf T ⊓ ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T).map
        (MulAut.conj t).toMonoidHom
  have e : S.map T.subtype = Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom := by
    ext x
    rw [Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem', Subgroup.mem_map]
    have hconj : ∀ s : T, (((MulAut.conj t).symm s : T) : G) = (t : G)⁻¹ * s * t := by
      intro s
      rw [MulAut.conj_symm_apply]
      push_cast
      rfl
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem', hconj] at hs
      refine ⟨hs.1, ?_⟩
      rw [show ((t : G) * y)⁻¹ * (T.subtype s) * ((t : G) * y) = y⁻¹ * ((t : G)⁻¹ * s * t) * y by
        simp only [Subgroup.coe_subtype]; group]
      exact hs.2.2
    · rintro ⟨hx, hxK⟩
      refine ⟨⟨x, hΓT hx⟩, ?_, rfl⟩
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem', hconj]
      refine ⟨hx, T.mul_mem (T.mul_mem (T.inv_mem t.2) (hΓT hx)) t.2, ?_⟩
      rw [show y⁻¹ * ((t : G)⁻¹ * x * t) * y = ((t : G) * y)⁻¹ * x * ((t : G) * y) by group]
      exact hxK
  rw [← e]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ T.subtype_injective).toEquiv

variable {G : Type} [Group G] in
private lemma card_inf_map_conj_mul_mul_eq (Γ' K : Subgroup G) {γ k : G} (hγ : γ ∈ Γ') (hk : k ∈ K) (a : G) :
    Nat.card (Γ' ⊓ K.map (MulAut.conj (γ * a * k)).toMonoidHom : Subgroup G) =
      Nat.card (Γ' ⊓ K.map (MulAut.conj a).toMonoidHom : Subgroup G) := by
  have e : (Γ' ⊓ K.map (MulAut.conj (γ * a * k)).toMonoidHom : Subgroup G) =
      (Γ' ⊓ K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj γ).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have h1 : (γ * a * k)⁻¹ * x * (γ * a * k) = k⁻¹ * (a⁻¹ * (γ⁻¹ * x * γ) * a) * k := by group
    rw [h1, Subgroup.mul_mem_cancel_right K hk, Subgroup.mul_mem_cancel_left K (K.inv_mem hk),
      Subgroup.mul_mem_cancel_right Γ' hγ, Subgroup.mul_mem_cancel_left Γ' (Γ'.inv_mem hγ)]
  rw [e]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj γ).injective).toEquiv.symm

theorem _root_.GlobalTheory.finsum_fold_intermediate : ∀ {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ), Γ' ≤ T → (∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x) → (∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite) → {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite → ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G), ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ * F (Quotient.out q) = ∑ᶠ y : DoubleCoset.Quotient (T : Set G) (K : Set G), ((_root_.GlobalTheory.LKCount.massC Γ' T (T ⊓ K.map (MulAut.conj (Quotient.out y)).toMonoidHom) : ℚ) : ℂ) * F (Quotient.out y) := by
  intro G _ Γ' T K F hΓT hF _ hfin
  have hsupp : (Function.support fun q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) =>
      ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ *
        F (Quotient.out q)).Finite :=
    hfin.subset fun q hq => right_ne_zero_of_mul hq
  refine (_root_.GlobalTheory.finsum_fiberwise_of_finite_support (A := DoubleCoset.Quotient (Γ' : Set G) (K : Set G))
    (B := DoubleCoset.Quotient (T : Set G) (K : Set G))
    (fun q => DoubleCoset.mk T K (Quotient.out q)) _ hsupp).trans (finsum_congr fun y' => ?_)
  set y := Quotient.out y'
  have hy' : DoubleCoset.mk T K y = y' := DoubleCoset.out_eq' T K y'
  have hfib : ∀ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G),
      DoubleCoset.mk T K (Quotient.out q) = DoubleCoset.mk T K y → F (Quotient.out q) = F y := by
    intro q hq
    obtain ⟨t, ht, k, hk, hqe⟩ := (DoubleCoset.eq T K _ _).1 hq.symm
    rw [hqe, hF t ht y k hk]
  let e : DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T) →
      {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) // DoubleCoset.mk T K (Quotient.out q) = y'} :=
    fun p => ⟨(_root_.GlobalTheory.ConjugateFold.foldMap Γ' T K hΓT y p).1,
      (_root_.GlobalTheory.ConjugateFold.foldMap Γ' T K hΓT y p).2.trans hy'⟩
  have hb := foldMap_bijective' Γ' T K hΓT y
  have he : Function.Bijective e := by
    constructor
    · intro p p' h
      have h' := congrArg Subtype.val h
      exact hb.1 (Subtype.ext h')
    · rintro ⟨q, hq⟩
      obtain ⟨p, hp⟩ := hb.2 ⟨q, hq.trans hy'.symm⟩
      have hp' := congrArg Subtype.val hp
      exact ⟨p, Subtype.ext hp'⟩
  rw [← finsum_eq_of_bijective e he (fun _ => rfl)]
  have hterm : ∀ p, ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out (e p).1)).toMonoidHom :
      Subgroup G) : ℕ) : ℂ)⁻¹ * F (Quotient.out (e p).1) =
      ((Nat.card ((Γ'.subgroupOf T) ⊓ ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T).map
        (MulAut.conj (Quotient.out p)).toMonoidHom : Subgroup T) : ℕ) : ℂ)⁻¹ * F y := by
    intro p
    obtain ⟨γ, k, hγ, hk, hg⟩ := DoubleCoset.mk_out_eq_mul Γ' K (((Quotient.out p : T) : G) * y)
    have hval : (e p).1 = DoubleCoset.mk Γ' K (((Quotient.out p : T) : G) * y) := rfl
    rw [card_subgroupOf_inf_map_conj_eq Γ' T K hΓT, hval, hg, card_inf_map_conj_mul_mul_eq Γ' K hγ hk,
      show γ * (((Quotient.out p : T) : G) * y) * k = (γ * ((Quotient.out p : T) : G)) * y * k by group,
      hF _ (T.mul_mem (hΓT hγ) (Quotient.out p).2) y k hk]
  rw [finsum_congr hterm]
  by_cases hFy : F y = 0
  · simp [hFy]
  haveI : Finite {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} :=
    hfin.to_subtype
  haveI : Finite (DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) :=
    Finite.of_injective
      (β := {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0})
      (fun p => ⟨(e p).1, by
        show F (Quotient.out (e p).1) ≠ 0
        rw [hfib _ ((e p).2.trans hy'.symm)]
        exact hFy⟩)
      (fun p p' h => by
        have h' := congrArg Subtype.val h
        exact he.1 (Subtype.ext h'))
  letI := Fintype.ofFinite (DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T))
  unfold _root_.GlobalTheory.LKCount.massC
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_mul, Rat.cast_sum]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointLowerBlock
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair GlobalTheory.DefLift.BilFischer

namespace GlobalTheory.CharPair.SecondBlockS

theorem pair_symm' {σ : Type} [Fintype σ] (f g : MvPolynomial σ ℂ) : pair f g = pair g f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial α c =>
    induction g using MvPolynomial.induction_on' with
    | monomial β d =>
      rw [pair_monomial, pair_monomial, coeff_monomial, coeff_monomial]
      by_cases h : α = β
      · subst h; simp; ring
      · simp [h, Ne.symm h]
    | add g g' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | add f f' h h' => simp only [map_add, LinearMap.add_apply, h, h']

theorem pair_X_pderiv {σ : Type} [Fintype σ] (f g : MvPolynomial σ ℂ) (u v : σ) :
    pair (X u * pderiv v f) g = pair f (X v * pderiv u g) := by
  rw [mul_comm, pair_mul_X, pair_symm', ← pair_mul_X, pair_symm', mul_comm]

variable {P Q S : ℕ}

def rowD (b b' : Fin Q) : Derivation ℂ (Pol P Q 0 S) (Pol P Q 0 S) :=
  ∑ c : Fin S, (X (Sum.inr b', Sum.inr c) : Pol P Q 0 S) • pderiv (Sum.inr b, Sum.inr c)

theorem rowD_apply (b b' : Fin Q) (g : Pol P Q 0 S) :
    rowD b b' g = ∑ c : Fin S, X (Sum.inr b', Sum.inr c) * pderiv (Sum.inr b, Sum.inr c) g := by
  rw [rowD, PI.RL.W.derivation_sum_apply]
  simp [Derivation.smul_apply, smul_eq_mul]

theorem rowD_X_inr_inr (b b' i : Fin Q) (c : Fin S) :
    rowD b b' (X (Sum.inr i, Sum.inr c) : Pol P Q 0 S) =
      if i = b then X (Sum.inr b', Sum.inr c) else 0 := by
  rw [rowD_apply]
  simp only [pderiv_X, Pi.single_apply, Prod.mk.injEq, mul_ite, mul_one, mul_zero, Sum.inr.injEq]
  by_cases h : i = b
  · subst h
    simp
  · simp [h]

theorem rowD_u (b b' : Fin Q) (a : Fin P) (c : Fin S) :
    rowD b b' (X (Sum.inl a, Sum.inr c) : Pol P Q 0 S) = 0 := by
  rw [rowD_apply]
  simp [pderiv_X, Pi.single_apply]

theorem rowD_mS (b b' i : Fin Q) (a : Fin P) :
    rowD b b' (mS P Q S a i) = if i = b then mS P Q S a b' else 0 := by
  simp only [mS, map_sum, Derivation.leibniz, rowD_X_inr_inr, rowD_u, smul_zero, add_zero, smul_eq_mul]
  split_ifs <;> simp

theorem rowD_detS (h : Q ≤ S) (b b' : Fin Q) :
    rowD b b' (detS P Q S h) = if b = b' then detS P Q S h else 0 := by
  rw [detS, PI.RL.W.derivation_det, Finset.sum_eq_single b]
  · simp only [Matrix.of_apply, rowD_X_inr_inr, if_true]
    split_ifs with hb
    · subst hb
      congr 1
      exact Matrix.updateRow_eq_self _ b
    · exact Matrix.det_updateRow_eq_zero (M := Matrix.of fun b c : Fin Q =>
        (X (Sum.inr b, Sum.inr (Fin.castLE h c)) : Pol P Q 0 S)) (Ne.symm hb)
  · intro i _ hi
    simp only [Matrix.of_apply, rowD_X_inr_inr, if_neg hi]
    exact Matrix.det_eq_zero_of_row_eq_zero i (by simp)
  · simp

theorem rowD_aeval (b b' : Fin Q) (G : Mdl P Q) :
    rowD b b' (aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) G) =
      aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (∑ a, X (a, b') * pderiv (a, b) G) := by
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add G G' h h' => simp only [map_add, h, h', mul_add, Finset.sum_add_distrib]
  | mul_X G v h =>
    obtain ⟨a, i⟩ := v
    rw [map_mul, Derivation.leibniz, h, aeval_X, rowD_mS]
    simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, map_add, map_sum,
      map_mul, aeval_X, pderiv_X, Pi.single_apply, Prod.mk.injEq, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · by_cases hi : i = b
      · subst hi
        rw [Finset.sum_eq_single a]
        · simp [mul_comm]
        · intro x _ hx
          simp [Ne.symm hx]
        · simp
      · simp [hi]
    · exact Finset.sum_congr rfl fun _ _ => by ring

theorem rowD_embS (h : Q ≤ S) (k' : ℕ) (b b' : Fin Q) (G : Mdl P Q) :
    rowD b b' (embS P Q S h k' G) = embS P Q S h k' (∑ a, X (a, b') * pderiv (a, b) G) +
      (if b = b' then (k' : ℂ) else 0) • embS P Q S h k' G := by
  simp only [embS, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]
  rw [Derivation.leibniz, rowD_aeval, Derivation.leibniz_pow, rowD_detS, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, add_comm, mul_comm]
  congr 1
  split_ifs
  · rcases k' with _ | k
    · simp
    · rw [Nat.cast_smul_eq_nsmul, mul_smul_comm, Nat.add_sub_cancel, ← pow_succ]
  · simp

theorem pair_fockAct1_inr_inr_embS (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (b b' : Fin Q) (G : Mdl P Q)
    (f : Pol P Q 0 S) :
    pair (fockAct1 P Q 0 S (Eab (Sum.inr b) (Sum.inr b')) f) (embS P Q S h k' G) =
      pair f (embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inr b') G)) := by
  have e : embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inr b') G) =
      rowD b b' (embS P Q S h k' G) + (if b = b' then (S : ℂ) / 2 else 0) • embS P Q S h k' G := by
    rw [rowD_embS, opS]
    simp only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_smul, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    split_ifs
    · rw [add_smul, add_assoc]
    · simp
  rw [e, fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, rowD_apply]
  simp only [GlobalTheory.CompactHarm.omE_pp (Sum.inr _, Sum.inr _) (Sum.inr _, Sum.inr _) rfl rfl,
    Finset.univ_eq_empty, Finset.sum_empty, zero_add, map_sum, map_add, map_smul, LinearMap.sum_apply,
    LinearMap.add_apply, LinearMap.smul_apply, pair_X_pderiv, Finset.sum_add_distrib,
    Prod.mk.injEq, Sum.inr.injEq, and_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul]
  refine congrArg₂ (· + ·) rfl ?_
  split_ifs
  · ring
  · simp

end GlobalTheory.CharPair.SecondBlockS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointMixedUpper
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair

open GlobalTheory.DefLift.BilFischer in
private theorem pair_symm' {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) : pair A B = pair B A := by
  classical
  induction A using MvPolynomial.induction_on' with
  | add A A' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | monomial α c =>
    induction B using MvPolynomial.induction_on' with
    | add B B' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | monomial β d =>
      rw [pair_monomial, pair_monomial, coeff_monomial, coeff_monomial]
      by_cases e : α = β
      · subst e; simp only [if_true]; ring
      · simp [e, Ne.symm e]

open GlobalTheory.DefLift.BilFischer in
private theorem pair_pderiv' {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) (v : σ) :
    pair (pderiv v A) B = pair A (B * X v) := by
  rw [pair_symm', ← pair_mul_X, pair_symm']

theorem pair_fockAct1_embS_up : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inl a) (Sum.inr b)) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inr b) G)) := by
  intro P Q S h k' a b G f
  have hom : ∀ c : Fin S, omE ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (Sum.inr b, Sum.inr c) f =
      -(pderiv (Sum.inl a, Sum.inr c) (pderiv (Sum.inr b, Sum.inr c) f)) := by
    intro c
    have h1 : linePos ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) = false := rfl
    have h2 : linePos ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) = true := rfl
    simp [omE, raiB, lowB, h1, h2]
  have hE : embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inr b) G) =
      -(embS P Q S h k' G * mS P Q S a b) := by
    simp only [opS, embS, LinearMap.neg_apply, map_neg, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, map_mul, aeval_X]
    ring
  rw [hE, fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add, hom, map_sum, map_neg,
    LinearMap.sum_apply, LinearMap.neg_apply, pair_pderiv', mS, Finset.mul_sum,
    Finset.sum_neg_distrib, mul_assoc]

end GlobalTheory.CharPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointUpperBlock
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.ActSFirstBlock

open GlobalTheory.DefLift.BilFischer

theorem pair_comm {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) : pair A B = pair B A := by
  classical
  induction A using MvPolynomial.induction_on' with
  | add A A' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | monomial α c =>
    induction B using MvPolynomial.induction_on' with
    | add B B' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | monomial β d =>
      rw [pair_monomial, pair_monomial, coeff_monomial, coeff_monomial]
      by_cases e : α = β
      · subst e; simp; ring
      · simp [e, Ne.symm e]

theorem pair_pderiv {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) (v : σ) :
    pair (pderiv v A) B = pair A (X v * B) := by
  rw [pair_comm, ← pair_mul_X, pair_comm, mul_comm]

theorem pair_X_mul {σ : Type} [Fintype σ] (A B : MvPolynomial σ ℂ) (v : σ) :
    pair (X v * A) B = pair A (pderiv v B) := by
  rw [mul_comm, pair_mul_X]

theorem omE_neg {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = false) (hv : linePos v = false)
    (F : Pol p q r s) :
    omE u v F = -(X v * pderiv u F) - (if u = v then (1 / 2 : ℂ) else 0) • F := by
  have : omE u v F = -(pderiv u (X v * F)) + (if u = v then (1 / 2 : ℂ) else 0) • F := by
    simp only [omE, raiB, lowB, hu, hv, Bool.false_eq_true, if_false]
    split_ifs <;> simp
  rw [this, Derivation.leibniz, pderiv_X, Pi.single_apply]
  by_cases e : u = v
  · subst e
    simp only [if_true, smul_eq_mul, mul_one]
    module
  · simp [e, Ne.symm e]

theorem pderiv_aeval {σ τ : Type} [Fintype σ] (m : σ → MvPolynomial τ ℂ) (v : τ) (G : MvPolynomial σ ℂ) :
    pderiv v (aeval m G) = ∑ i, aeval m (pderiv i G) * pderiv v (m i) := by
  classical
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add A B h h' => simp only [map_add, h, h', add_mul, Finset.sum_add_distrib]
  | mul_X A u h =>
    simp only [map_mul, aeval_X, Derivation.leibniz, h, smul_eq_mul, map_add, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    congr 1
    rw [Finset.sum_eq_single u]
    · simp
    · intro w _ hw
      simp [pderiv_X, Pi.single_apply, hw, Ne.symm hw]
    · simp

theorem pderiv_detS (P Q S : ℕ) (h : Q ≤ S) (a : Fin P) (c : Ix 0 S) :
    pderiv (Sum.inl a, c) (detS P Q S h) = 0 := by
  classical
  let g : Fin Q × Fin Q → Ix P Q × Ix 0 S := fun bc => (Sum.inr bc.1, Sum.inr (Fin.castLE h bc.2))
  have : detS P Q S h = aeval (fun i => X (g i)) (Matrix.det (Matrix.mvPolynomialX (Fin Q) (Fin Q) ℂ)) := by
    rw [detS, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext b c; simp [g, Matrix.mvPolynomialX]
  rw [this, pderiv_aeval]
  simp [g, pderiv_X, Pi.single_apply]

theorem pderiv_mS (P Q S : ℕ) (a a' : Fin P) (c : Fin S) (b : Fin Q) :
    pderiv (Sum.inl a', Sum.inr c) (mS P Q S a b) =
      if a = a' then X (Sum.inr b, Sum.inr c) else 0 := by
  classical
  simp only [mS, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul, Prod.mk.injEq,
    Sum.inl.injEq, Sum.inr.injEq]
  split_ifs with e
  · simp [e]
  · simp [e]

theorem euler_embS (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a a' : Fin P) (G : Mdl P Q) :
    ∑ c : Fin S, X (Sum.inl a, Sum.inr c) * pderiv (Sum.inl a', Sum.inr c) (embS P Q S h k' G) =
      embS P Q S h k' (∑ b, X (a, b) * pderiv (a', b) G) := by
  classical
  simp only [embS, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
    Derivation.leibniz, Derivation.leibniz_pow, pderiv_detS, smul_zero, zero_add, smul_eq_mul,
    pderiv_aeval, pderiv_mS, map_sum, map_mul, aeval_X, Fintype.sum_prod_type, mul_zero, mul_ite,
    Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin P))), Finset.sum_ite_eq', Finset.mem_univ, if_true, mS, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem pair_act_first_block : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a a' : Fin P) (G : Mdl P Q) (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inl a) (Sum.inl a')) f) (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inl a) (Sum.inl a') G)) := by
  intro P Q S h k' a a' G f
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [omE_neg (Sum.inl _, Sum.inr _) (Sum.inl _, Sum.inr _) rfl rfl, Finset.univ_eq_empty,
    Finset.sum_empty, zero_add, map_sum, map_sub, map_neg, map_smul, LinearMap.sum_apply,
    LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, pair_X_mul, pair_pderiv,
    opS, Module.End.mul_apply, LinearMap.mulLeft_apply, Module.End.one_apply]
  have key := congrArg (pair f) (euler_embS P Q S h k' a a' G)
  simp only [map_sum] at key
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, key]
  by_cases e : a = a'
  · simp [e]
    ring
  · simp [e]

end GlobalTheory.CharPair.ActSFirstBlock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusActsOnTypeAtValuationStatement
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_acts_on_type_at_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), FrobOnType io X := by
  first | exact @GlobalTheory.PrimePart.frobOnType_all | exact GlobalTheory.PrimePart.frobOnType_all | (intros; apply GlobalTheory.PrimePart.frobOnType_all <;> assumption)
end

