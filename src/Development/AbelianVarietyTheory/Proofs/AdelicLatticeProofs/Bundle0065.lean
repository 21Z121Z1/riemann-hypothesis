import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0041
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteAdelicDoubleCosetsOfRationalSLSubgroup
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem cf_congr_of_vanI_eq {ι : Type} [Fintype ι] [DecidableEq ι] {Γ Δ : Set (Matrix ι ι ℂ)}
    (h : vanI Γ = vanI Δ) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R) :
    CF Γ R R₀ ↔ CF Δ R R₀ := by

  have key : ∀ (S : Type) [CommRing S] [Algebra ℚ S], pts Γ S = pts Δ S := by
    intro S _ _
    simp only [pts, h]
  simp only [CF, key]

theorem cf_of_isQGroup : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  intro ι _ _

  suffices H : ∀ n : ℕ, ∀ (Γ : Set (Matrix ι ι ℂ)), Module.finrank ℂ (Submodule.span ℂ Γ) = n →
      ∀ (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ by
    intro Γ R _ _ R₀ hQ hA
    exact H _ Γ rfl R R₀ hQ hA
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Γ hn R _ _ R₀ hQ hA
    by_cases hS : SS Γ
    · exact GlobalTheory.T.classFiniteness_completelyReducible ι Γ R R₀ hQ hS hA
    · obtain ⟨e, he, hup, a, ha, ha0, hblk⟩ := GlobalTheory.T.exists_rat_idempotent_blockDiagPart_kills_span ι Γ hQ.toIsPre hS

      have hPre : IsPre (blk e '' Γ) := GlobalTheory.T.isAutStableSLMatrixGroup_image_blockDiagPart ι Γ e hQ.toIsPre he hup
      obtain ⟨hQ', hvan, hspan⟩ := GlobalTheory.T.ratZariskiClosure_of_autStable_SL_group ι (blk e '' Γ) hPre
      have hlt := GlobalTheory.T.finrank_span_blockDiagPart_image_lt ι Γ e a ha ha0 hblk
      have hcl : CF (pts (blk e '' Γ) ℂ) R R₀ :=
        ih _ (by rw [← hn, hspan]; exact hlt) _ rfl R R₀ hQ' hA
      have hblkCF : CF (blk e '' Γ) R R₀ := (cf_congr_of_vanI_eq hvan R R₀).mp hcl
      exact GlobalTheory.T.hasFiniteAdelicDoubleCosets_of_blockDiagPart_image ι Γ e R R₀ hQ he hup hA hblkCF

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormPrincipleOfIsCyclic
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem np_of_finrank_one (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (h : Module.finrank F E = 1) : NP F E := by
  intro x _ _
  refine ⟨algebraMap F E x, ?_⟩
  rw [Algebra.norm_algebraMap, h, pow_one]

theorem np_of_finrank_prime (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E] (hp : p.Prime) (h : Module.finrank F E = p) :
    NP F E := by
  by_cases h2 : p = 2
  · exact GlobalTheory.T.np_of_finrank_two' F E (h2 ▸ h)
  · exact GlobalTheory.T.np_of_odd_prime_degree' p F E hp h2 h

theorem hasseNormPrinciple_cyclic_of_finrank (n : ℕ) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], Module.finrank F E = n → IsGalois F E → IsCyclic (E ≃ₐ[F] E) → NP F E := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F E _ _ _ _ _ hn hG hC
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  by_cases h1 : n = 1
  · exact np_of_finrank_one F E (hn.trans h1)
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = n := (IsGalois.card_aut_eq_finrank F E).trans hn
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := E ≃ₐ[F] E) p (hcard ▸ hpn)
  set H : Subgroup (E ≃ₐ[F] E) := Subgroup.zpowers g with hH
  have hHc : Nat.card H = p := by rw [hH, Nat.card_zpowers, hg]
  have : H.Normal := by
    constructor
    intro a ha b
    have hc : b * a = a * b := by
      obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
      obtain ⟨i, rfl⟩ := hs a
      obtain ⟨j, rfl⟩ := hs b
      exact (Commute.zpow_zpow_self s j i).eq
    rw [hc, mul_inv_cancel_right]
    exact ha
  let M : IntermediateField F E := IntermediateField.fixedField H
  have : NumberField M := NumberField.of_module_finite F M
  have hME : Module.finrank M E = p :=
    (IntermediateField.finrank_fixedField_eq_card H).trans hHc
  have : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  have hFM : IsGalois F M := IsGalois.of_fixedField_normal_subgroup H
  have hCM : IsCyclic (M ≃ₐ[F] M) :=
    isCyclic_of_surjective (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) M)
      (AlgEquiv.restrictNormalHom_surjective E)
  have hmul : Module.finrank F M * Module.finrank M E = n :=
    (Module.finrank_mul_finrank F M E).trans hn
  have hpos : 0 < Module.finrank F M := Module.finrank_pos
  have hlt : Module.finrank F M < n := by
    rw [← hmul, hME]
    exact lt_mul_of_one_lt_right hpos hp.one_lt
  exact GlobalTheory.T.hasseNormPrinciple_of_cyclic_tower F M E hC (np_of_finrank_prime p M E hp hME) (ih _ hlt F M rfl hFM hCM)

theorem np_cyclic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], IsGalois F E → IsCyclic (E ≃ₐ[F] E) → NP F E :=
  fun F E _ _ _ _ _ hG hC => hasseNormPrinciple_cyclic_of_finrank _ F E rfl hG hC

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealPosAtOneOfRight
section
open Filter Topology

namespace GlobalTheory

theorem real_pos_at_one_of_right (L : ℂ → ℂ) (hc : ContinuousAt L 1) (h1 : L 1 ≠ 0)
    (h : ∀ s : ℂ, 1 < s.re → s.im = 0 → (L s).im = 0 ∧ 0 < (L s).re) :
    (L 1).im = 0 ∧ 0 < (L 1).re := by
  have ht : Tendsto (fun t : ℝ => L (t : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (L 1)) := by
    have h0 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (1 : ℂ)) := by
      simpa using Complex.continuous_ofReal.tendsto 1
    exact (hc.tendsto.comp h0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), (L (t : ℂ)).im = 0 ∧ 0 < (L (t : ℂ)).re := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact h t (by simpa using ht) (by simp)
  have him : (L 1).im = 0 := by
    have h2 := (Complex.continuous_im.tendsto _).comp ht
    have h3 : Tendsto (Complex.im ∘ fun t : ℝ => L (t : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun t ht => ht.1.symm)
    exact tendsto_nhds_unique h2 h3
  have hre : 0 ≤ (L 1).re :=
    ge_of_tendsto ((Complex.continuous_re.tendsto _).comp ht) (hev.mono fun t ht => ht.2.le)
  refine ⟨him, lt_of_le_of_ne hre fun h0 => h1 ?_⟩
  exact Complex.ext h0.symm him

end GlobalTheory
end

