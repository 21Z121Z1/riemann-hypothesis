import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0047
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import ReciprocityTheory.SemistableReduction.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.GaussValuationDensityGenerationLocalisation
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

namespace GlobalTheory.GaussVal

section
variable {O L U Γ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L]
  [IsFractionRing O L] [Field U] [LinearOrderedCommGroupWithZero Γ] (v : Valuation U Γ)

omit [Field L] [Algebra O L] [IsFractionRing O L] in

theorem val_lt_one (g : O →+* U) (h1 : ∀ a, v (g a) ≤ 1) {ϖ : O} (hϖ : Irreducible ϖ) (h2 : v (g ϖ) < 1)
    {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) : v (g a) < 1 := by
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨y, rfl⟩ := ha
  rw [map_mul, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (h1 y)) h2

theorem isInteger_of_val_le (φ : L →+* U) (h1 : ∀ a, v (φ (algebraMap O L a)) ≤ 1) {ϖ : O} (hϖ : Irreducible ϖ)
    (h2 : v (φ (algebraMap O L ϖ)) < 1) {c : L} (hc : v (φ c) ≤ 1) : ∃ a, algebraMap O L a = c := by
  rcases ValuationRing.isInteger_or_isInteger O c with h | ⟨b, hb⟩
  · exact h
  by_cases hc0 : c = 0
  · exact ⟨0, by simp [hc0]⟩
  by_cases hu : IsUnit b
  · obtain ⟨u, rfl⟩ := hu
    refine ⟨((u⁻¹ : Oˣ) : O), ?_⟩
    rw [map_units_inv, hb, inv_inv]
  · exfalso
    have := val_lt_one v (φ.comp (algebraMap O L)) h1 hϖ h2 (a := b) hu
    rw [RingHom.comp_apply, hb] at this
    have h3 : v (φ c) * v (φ c⁻¹) = 1 := by rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc0, map_one, map_one]
    exact absurd h3 (lt_of_le_of_lt (mul_le_of_le_one_left' hc) this).ne
end

theorem val_unit {A U Γ : Type} [CommRing A] [Field U] [LinearOrderedCommGroupWithZero Γ] (v : Valuation U Γ)
    (g : A →+* U) (h1 : ∀ a, v (g a) ≤ 1) {a : A} (ha : IsUnit a) : v (g a) = 1 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  refine le_antisymm (h1 a) ?_
  have h3 : v (g a) * v (g b) = 1 := by rw [← map_mul, ← map_mul, hb, map_one, map_one]
  exact h3.symm.le.trans (mul_le_of_le_one_right' (h1 b))

theorem exists_approx {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    (c t : la.adicCompletion K) (ht : t ≠ 0) :
    ∃ (a : K) (y : la.adicCompletionIntegers K), c - algebraMap K _ a = t * (y : la.adicCompletion K) := by
  have ho : IsOpen {x : la.adicCompletion K | t⁻¹ * (c - x) ∈ la.adicCompletionIntegers K} :=
    (Valued.isOpen_valuationSubring (la.adicCompletion K)).preimage (f := fun x => t⁻¹ * (c - x)) (by fun_prop)
  obtain ⟨a, ha⟩ := (HeightOneSpectrum.denseRange_algebraMap K la).exists_mem_open ho ⟨c, by simp⟩
  exact ⟨a, ⟨_, ha⟩, by rw [mul_inv_cancel_left₀ ht]⟩

theorem gauss_dense_gen : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (U : Type) [Field U] (v : Valuation U (WithZero (Multiplicative ℤ))) (ψ : Kp X la N →+* U), (∀ a : Op X la N, v (ψ (algebraMap (Op X la N) (Kp X la N) a)) ≤ 1) → v (ψ (algebraMap (Op X la N) (Kp X la N) (unifO X la N))) < 1 → (∀ (f : B.KO →+* U), (∀ a, f a = ψ (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) → ∀ p : MvPolynomial (Idx D j N) B.KO, (∀ α, v (f (p.coeff α)) ≤ 1) → (∃ α, v (f (p.coeff α)) = 1) → v (MvPolynomial.eval₂ f (fun q => ψ (algebraMap (Op X la N) (Kp X la N) (Tv X la N q))) p) = 1) ∧ (∀ (c : X.Ol la) (γ : WithZero (Multiplicative ℤ)), γ ≠ 0 → ∃ a : B.KO, v (ψ (algebraMap (X.Ol la) (Kp X la N) c) - ψ (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) < γ) ∧ ∀ S : Subfield U, (∀ c : X.Ol la, ψ (algebraMap (X.Ol la) (Kp X la N) c) ∈ S) → (∀ q, ψ (algebraMap (Op X la N) (Kp X la N) (Tv X la N q)) ∈ S) → ∀ c : Kp X la N, ψ c ∈ S := by
  intro D B P j X la N U _ v ψ h1 h2
  have hϖ : Irreducible (unif X la) :=
    Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))
  have e1 : ∀ c : X.Ol la, algebraMap (X.Kl la) (Kp X la N) (algebraMap (X.Ol la) (X.Kl la) c) =
      algebraMap (Op X la N) (Kp X la N) (algebraMap (X.Ol la) (Op X la N) c) := fun c => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have eC : ∀ c : X.Ol la, algebraMap (Pol X la N) (Op X la N) (MvPolynomial.C c) =
      algebraMap (X.Ol la) (Op X la N) c := fun c => by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  set φ : X.Kl la →+* U := ψ.comp (algebraMap (X.Kl la) (Kp X la N)) with hφ
  have g1 : ∀ a, v (φ (algebraMap (X.Ol la) (X.Kl la) a)) ≤ 1 := fun a => by
    rw [hφ, RingHom.comp_apply, e1]; exact h1 _
  have g2 : v (φ (algebraMap (X.Ol la) (X.Kl la) (unif X la))) < 1 := by
    rw [hφ, RingHom.comp_apply, e1]; exact h2
  refine ⟨?_, ?_, ?_⟩
  · intro f hf p hp ⟨α₀, hα₀⟩
    have hf' : ∀ a, f a = φ (algebraMap B.KO (X.Kl la) a) := hf
    have hex : ∀ α, ∃ a : X.Ol la, algebraMap (X.Ol la) (X.Kl la) a = algebraMap B.KO (X.Kl la) (p.coeff α) :=
      fun α => isInteger_of_val_le v φ g1 hϖ g2 (by rw [← hf']; exact hp α)
    choose b hb using hex
    set p₀ : Pol X la N := ∑ α ∈ p.support, MvPolynomial.monomial α (b α) with hp₀
    have hs : α₀ ∈ p.support := by
      rw [MvPolynomial.mem_support_iff]
      intro h
      rw [h, map_zero, map_zero] at hα₀
      exact zero_ne_one hα₀
    have hc : p₀.coeff α₀ = b α₀ := by
      classical
      rw [hp₀, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial]
      rw [Finset.sum_ite_eq' , if_pos hs]
    have hn : p₀ ∉ gI X la N := by
      unfold gI Formalism.DV.gaussIdeal
      rw [MvPolynomial.mem_map_C_iff]
      intro h
      have := val_lt_one v (φ.comp (algebraMap (X.Ol la) (X.Kl la))) g1 hϖ g2 (h α₀)
      rw [hc, RingHom.comp_apply, hb, ← hf', hα₀] at this
      exact lt_irrefl _ this
    have hu : IsUnit (algebraMap (Pol X la N) (Op X la N) p₀) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Op X la N) (gI X la N) p₀).2 hn
    have := val_unit v (ψ.comp (algebraMap (Op X la N) (Kp X la N))) h1 hu
    rw [← this]
    congr 1
    rw [MvPolynomial.eval₂_eq, hp₀, map_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.monomial_eq, map_mul, map_mul, eC, hf', ← hb, hφ, RingHom.comp_apply, e1, Finsupp.prod,
      map_prod, map_prod]
    simp only [map_pow]
    rfl
  · intro c γ hγ
    obtain ⟨n, hn⟩ := exists_pow_lt₀ g2 (Units.mk0 γ hγ)
    have ht : algebraMap (X.Ol la) (X.Kl la) (unif X la) ^ n ≠ 0 := by
      refine pow_ne_zero _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact hϖ.ne_zero
    obtain ⟨a, y, hy⟩ := exists_approx la (algebraMap (X.Ol la) (X.Kl la) c) _ ht
    refine ⟨a, ?_⟩
    rw [IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N)]
    change v (φ _ - φ _) < γ
    rw [← map_sub, hy, map_mul, map_mul, map_pow, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (g1 y)) hn
  · intro S hO hT
    have hP : ∀ q : Pol X la N,
        ψ (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) q)) ∈ S := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C a => rw [eC]; exact hO a
      | add p q hp hq => simp only [map_add]; exact S.add_mem hp hq
      | mul_X p i hp => simp only [map_mul]; exact S.mul_mem hp (hT i)
    have hA : ∀ x : Op X la N, ψ (algebraMap (Op X la N) (Kp X la N) x) ∈ S := by
      intro x
      obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (gI X la N).primeCompl x
      have hs : ψ (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) s)) ≠ 0 :=
        (((IsLocalization.map_units (Op X la N) s).map _).map _).ne_zero
      have h' := congrArg (fun z => ψ (algebraMap (Op X la N) (Kp X la N) z)) h
      simp only [map_mul] at h'
      rw [eq_div_of_mul_eq hs h']
      exact S.div_mem (hP _) (hP _)
    intro c
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Op X la N) c
    rw [map_div₀]
    exact S.div_mem (hA _) (hA _)

end GlobalTheory.GaussVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralElementsGenericLinearSectionGaussPoint
section
namespace GlobalTheory.GaussSection

open MvPolynomial

theorem eval_mem_closure {Ω U σ : Type} [Field Ω] [Field U] (f : Ω →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (t : σ → U) (S : Set U)
    (hS : ∀ s, t s ∈ S) (p : MvPolynomial σ Ω) (hp : ∀ α, v (f (p.coeff α)) ≤ 1) :
    eval₂ f t p ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ S) := by
  rw [MvPolynomial.eval₂_eq]
  apply sum_mem
  intro α _
  apply mul_mem
  · exact Subring.subset_closure (Or.inl ⟨Set.mem_range_self _, hp α⟩)
  · apply prod_mem
    intro i _
    exact pow_mem (Subring.subset_closure (Set.mem_union_right _ (hS i))) _

theorem exists_normalise {Ω U σ : Type} [Field Ω] [Field U] (f : Ω →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (p : MvPolynomial σ Ω) (hp : p ≠ 0) :
    ∃ (c : Ω) (q : MvPolynomial σ Ω), c ≠ 0 ∧ p = C c * q ∧ (∀ α, v (f (q.coeff α)) ≤ 1) ∧
      ∃ α, v (f (q.coeff α)) = 1 := by
  classical
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hp
  obtain ⟨α₀, hα₀, hmax⟩ := p.support.exists_max_image (fun α => v (f (p.coeff α)))
    ⟨d, MvPolynomial.mem_support_iff.mpr hd⟩
  have hc : p.coeff α₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hα₀
  have hfc : 0 < v (f (p.coeff α₀)) := by
    rw [zero_lt_iff, Ne, Valuation.zero_iff, map_eq_zero]
    exact hc
  refine ⟨p.coeff α₀, C (p.coeff α₀)⁻¹ * p, hc, ?_, fun α => ?_, α₀, ?_⟩
  · rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
  · rw [coeff_C_mul, map_mul, map_mul, map_inv₀, map_inv₀, inv_mul_le_iff₀ hfc, mul_one]
    by_cases hα : α ∈ p.support
    · exact hmax α hα
    · rw [MvPolynomial.notMem_support_iff.mp hα, map_zero, map_zero]
      exact zero_le
  · rw [coeff_C_mul, inv_mul_cancel₀ hc, map_one, map_one]

theorem quotient_of_gauss {Ω U σ : Type} [Field Ω] [Field U] (f : Ω →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (t : σ → U) (S : Set U)
    (hS : ∀ s, t s ∈ S) (hS' : ∀ u ∈ S, ∃ p : MvPolynomial σ Ω, eval₂ f t p = u)
    (hG : ∀ p : MvPolynomial σ Ω, (∀ α, v (f (p.coeff α)) ≤ 1) → (∃ α, v (f (p.coeff α)) = 1) →
      v (eval₂ f t p) = 1)
    (g : U) (hg : g ∈ Subfield.closure (Set.range f ∪ S)) (hv : v g ≤ 1) :
    ∃ a ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ S),
      ∃ d ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ S), v d = 1 ∧ g * d = a := by
  classical
  by_cases hg0 : g = 0
  · exact ⟨0, zero_mem _, 1, one_mem _, map_one v, by rw [hg0, zero_mul]⟩
  have hle : Subring.closure (Set.range f ∪ S) ≤ (MvPolynomial.eval₂Hom f t).range := by
    rw [Subring.closure_le]
    rintro u (⟨c, rfl⟩ | hu)
    · exact ⟨C c, by simp⟩
    · obtain ⟨p, hp⟩ := hS' u hu
      exact ⟨p, hp⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp hg
  obtain ⟨P, rfl⟩ := hle hy
  obtain ⟨Q, rfl⟩ := hle hz
  simp only [MvPolynomial.coe_eval₂Hom] at hg0 hv ⊢
  have hz0 : eval₂ f t Q ≠ 0 := fun h => hg0 (by rw [h, div_zero])
  have hy0 : eval₂ f t P ≠ 0 := fun h => hg0 (by rw [h, zero_div])
  have hQ : Q ≠ 0 := by
    rintro rfl
    exact hz0 (eval₂_zero _ _)
  have hP : P ≠ 0 := by
    rintro rfl
    exact hy0 (eval₂_zero _ _)
  obtain ⟨c, Q', hc, rfl, hQi, hQu⟩ := exists_normalise f v Q hQ
  obtain ⟨c', P', -, rfl, hPi, hPu⟩ := exists_normalise f v P hP
  have hdQ := hG Q' hQi hQu
  have hdP := hG P' hPi hPu
  have hfc : f c ≠ 0 := (map_ne_zero f).mpr hc
  have hQ0 : eval₂ f t Q' ≠ 0 := by
    intro h
    rw [h, map_zero] at hdQ
    exact zero_ne_one hdQ
  simp only [eval₂_mul, eval₂_C] at hv ⊢
  refine ⟨f (c' / c) * eval₂ f t P',
    mul_mem (Subring.subset_closure (Or.inl ⟨Set.mem_range_self _, ?_⟩))
      (eval_mem_closure f v t S hS P' hPi),
    eval₂ f t Q', eval_mem_closure f v t S hS Q' hQi, hdQ, ?_⟩
  · have : v (f (c' / c)) = v (f c' * eval₂ f t P' / (f c * eval₂ f t Q')) := by
      rw [map_div₀, map_div₀, map_div₀, map_mul, map_mul, hdP, hdQ, mul_one, mul_one]
    rw [this]
    exact hv
  · rw [map_div₀]
    field_simp

private theorem algebraicIndependent_congr_algebra {ι R S : Type*} [CommRing R] [CommRing S] (x : ι → S)
    (A₁ A₂ : Algebra R S) (h : ∀ r, (letI := A₁; algebraMap R S r) = (letI := A₂; algebraMap R S r))
    (hx : letI := A₁; AlgebraicIndependent R x) : letI := A₂; AlgebraicIndependent R x := by
  obtain rfl := Algebra.algebra_ext A₁ A₂ h
  exact hx

theorem indep_comp {K Ω U τ : Type} [Field K] [Field Ω] [Field U] [Algebra K Ω] [Algebra Ω U]
    (v : Valuation U (WithZero (Multiplicative ℤ))) (s : τ → U)
    (hs : ∀ j, s j ∈ v.valuationSubring)
    (hG : ∀ p : MvPolynomial τ K, (∀ α, v (algebraMap Ω U (algebraMap K Ω (p.coeff α))) ≤ 1) →
      (∃ α, v (algebraMap Ω U (algebraMap K Ω (p.coeff α))) = 1) →
      v (eval₂ ((algebraMap Ω U).comp (algebraMap K Ω)) s p) = 1) :
    letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring (algebraMap Ω U)
    letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (v.valuationSubring.comap (algebraMap Ω U))
      (algebraMap K Ω)
    letI : Algebra (IsLocalRing.ResidueField
        ((v.valuationSubring.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
        (IsLocalRing.ResidueField v.valuationSubring) :=
      ((algebraMap _ (IsLocalRing.ResidueField v.valuationSubring)).comp
        (algebraMap _ (IsLocalRing.ResidueField
          (v.valuationSubring.comap (algebraMap Ω U))))).toAlgebra
    AlgebraicIndependent
      (IsLocalRing.ResidueField
        ((v.valuationSubring.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (fun j => IsLocalRing.residue v.valuationSubring ⟨s j, hs j⟩) := by
  refine algebraicIndependent_congr_algebra _
    (ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring ((algebraMap Ω U).comp (algebraMap K Ω))) _ ?_
    ((GlobalTheory.algebraicIndependent_residue_iff_gauss K U _ v τ s hs).mpr hG)
  intro r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  rfl

theorem integral_elements (K Ω U : Type) [Field K] [Field Ω] [Field U] [Algebra K Ω]
    (f : Ω →+* U) (D N : ℕ) (hD : Algebra.trdeg K Ω = D)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (s : Fin (D + 1) × Fin N → U)
    (a : Fin N → Ω) (ha : ∃ k, a k ≠ 0)
    (hrel : ∀ i : Fin D, ∑ k, s (i.succ, k) * f (a k) = 0) (hs : ∀ p, v (s p) ≤ 1)
    (hG : ∀ p : MvPolynomial (Fin (D + 1) × Fin N) K,
      (∀ α, v (f (algebraMap K Ω (p.coeff α))) ≤ 1) →
      (∃ α, v (f (algebraMap K Ω (p.coeff α))) = 1) →
      v (MvPolynomial.eval₂ (f.comp (algebraMap K Ω)) s p) = 1) :
    ∀ g ∈ Subfield.closure (Set.range f ∪ Set.range s), v g ≤ 1 →
      ∃ a ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range s),
        ∃ d ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range s),
          v d = 1 ∧ g * d = a := by
  intro g hg hv
  classical
  let _ : Algebra Ω U := f.toAlgebra
  obtain ⟨k₁, hk₁⟩ := ha
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image Finset.univ (fun k => v (f (a k)))
    ⟨k₁, Finset.mem_univ _⟩
  have ha₀ : a k₀ ≠ 0 := by
    intro h0
    have h := hk₀ k₁ (Finset.mem_univ _)
    rw [h0, map_zero, map_zero, le_zero_iff, Valuation.zero_iff, map_eq_zero] at h
    exact hk₁ h
  have hfa : f (a k₀) ≠ 0 := (map_ne_zero f).mpr ha₀
  have hva : 0 < v (f (a k₀)) := by
    rw [zero_lt_iff, Ne, Valuation.zero_iff]
    exact hfa
  have hsV : ∀ j, s j ∈ v.valuationSubring := hs
  set t : Fin N ⊕ (Fin D × {k : Fin N // k ≠ k₀}) → U :=
    Sum.elim (fun k => s (0, k)) (fun q => s (q.1.succ, q.2.1)) with ht_def
  have ht : ∀ x, t x ∈ v.valuationSubring := by
    rintro (k | q)
    · exact hsV _
    · exact hsV _
  have hcoefX : ∀ (x : Fin N ⊕ (Fin D × {k : Fin N // k ≠ k₀})) α,
      (X x : MvPolynomial _ Ω).coeff α ∈ v.valuationSubring.comap (algebraMap Ω U) := by
    intro x α
    rw [coeff_X]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hex : ∀ j : Fin (D + 1) × Fin N, ∃ q : MvPolynomial (Fin N ⊕ (Fin D × {k : Fin N // k ≠ k₀})) Ω,
      (∀ α, q.coeff α ∈ v.valuationSubring.comap (algebraMap Ω U)) ∧ MvPolynomial.aeval t q = s j := by
    rintro ⟨i, k⟩
    obtain rfl | ⟨i', rfl⟩ := Fin.eq_zero_or_eq_succ i
    · exact ⟨X (Sum.inl k), hcoefX _, by rw [aeval_X]; rfl⟩
    by_cases hk : k = k₀
    · rw [hk]
      refine ⟨∑ q : {k : Fin N // k ≠ k₀}, C (-(a q / a k₀)) * X (Sum.inr (i', q)), fun α => ?_, ?_⟩
      · rw [coeff_sum]
        refine sum_mem fun q _ => ?_
        rw [coeff_C_mul]
        refine mul_mem (neg_mem ?_) (hcoefX _ _)
        rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
          RingHom.algebraMap_toAlgebra, map_div₀, map_div₀, div_le_one₀ hva]
        exact hk₀ q (Finset.mem_univ _)
      · have hr := hrel i'
        rw [Fintype.sum_eq_add_sum_subtype_ne _ k₀] at hr
        simp only [map_sum, map_mul, aeval_C, aeval_X, RingHom.algebraMap_toAlgebra]
        have key : ∑ q : {k : Fin N // k ≠ k₀}, f (-(a q / a k₀)) * t (Sum.inr (i', q)) =
            -(∑ q : {k : Fin N // k ≠ k₀}, s (i'.succ, q.1) * f (a q)) / f (a k₀) := by
          rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [map_neg, map_div₀]
          simp only [ht_def, Sum.elim_inr]
          ring
        rw [key, div_eq_iff hfa]
        linear_combination -hr
    · exact ⟨X (Sum.inr (i', ⟨k, hk⟩)), hcoefX _, by rw [aeval_X]; rfl⟩
  choose P hPc hPe using hex
  have hcard : Fintype.card (Fin (D + 1) × Fin N) =
      Fintype.card (Fin N ⊕ (Fin D × {k : Fin N // k ≠ k₀})) + D := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by have := k₀.pos; omega⟩
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_subtype_compl,
      Fintype.card_unique]
    simp only [Nat.add_sub_cancel]
    ring
  have hind := indep_comp (K := K) (Ω := Ω) (U := U) v s hsV hG
  obtain ⟨-, -, h3⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.residueTrdeg K Ω U D hD
    (Fin N ⊕ (Fin D × {k : Fin N // k ≠ k₀})) t v.valuationSubring ht
    (Fin (D + 1) × Fin N) (fun j => ⟨s j, hsV j⟩) P hPc hcard hPe hind
  have hGΩ := (GlobalTheory.algebraicIndependent_residue_iff_gauss Ω U f v _ t ht).mp h3
  refine quotient_of_gauss f v t (Set.range s) ?_ ?_ hGΩ g hg hv
  · rintro (k | q)
    · exact ⟨(0, k), rfl⟩
    · exact ⟨(q.1.succ, q.2.1), rfl⟩
  · rintro u ⟨j, rfl⟩
    exact ⟨P j, (MvPolynomial.aeval_def _ _).symm.trans (hPe j)⟩

end GlobalTheory.GaussSection
end

