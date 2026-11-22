import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0061
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0675
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0678
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0672
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0677
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedFieldStructure
section
noncomputable section

namespace GlobalTheory.CompanionTheory.FixedPointsCM

open NumberField IsDedekindDomain HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct

theorem exists_eq_algebraMap_of_sigR_eq {F E K : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) (hfin : Module.finrank F E = 2)
    (hσ : ∀ x, σ (σ x) = x) (u : E) (hu : σ u ≠ u) (x : K ⊗[F] E) (hx : sigR K σ x = x) :
    ∃ c : K, x = algebraMap K (K ⊗[F] E) c := by
  have hli : LinearIndependent F ![(1 : E), u] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h2 : s • (1 : E) + t • σ u = 0 := by
      have := congrArg σ h
      simpa [map_add, map_smul] using this
    have h3 : t • (σ u - u) = 0 := by
      have : t • (σ u - u) = (s • (1 : E) + t • σ u) - (s • (1 : E) + t • u) := by module
      rw [this, h, h2, sub_zero]
    have ht : t = 0 := by
      rcases smul_eq_zero.mp h3 with h4 | h4
      · exact h4
      · exact absurd (sub_eq_zero.mp h4) hu
    subst ht
    refine ⟨?_, rfl⟩
    simpa using h
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by simp [hfin]
  let b : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = u := by simp [b]
  obtain ⟨p, q, hsu⟩ : ∃ p q : F, σ u = p • (1 : E) + q • u := by
    refine ⟨b.repr (σ u) 0, b.repr (σ u) 1, ?_⟩
    have := b.sum_repr (σ u)
    rw [Fin.sum_univ_two, hb0, hb1] at this
    exact this.symm
  have hrel : (p + q * p) • (1 : E) + (q * q - 1) • u = 0 := by
    have h1 : u = p • (1 : E) + q • σ u := by
      have := hσ u
      rw [hsu] at this
      simpa [map_add, map_smul] using this.symm
    rw [hsu] at h1
    have : (p + q * p) • (1 : E) + (q * q - 1) • u = (p • (1 : E) + q • (p • (1 : E) + q • u)) - u := by module
    rw [this, ← h1, sub_self]
  obtain ⟨hp, hq⟩ := LinearIndependent.pair_iff.mp hli _ _ hrel
  have hq' : q = -1 := by
    have : (q - 1) * (q + 1) = 0 := by linear_combination hq
    rcases mul_eq_zero.mp this with h | h
    · exfalso
      have hq1 : q = 1 := sub_eq_zero.mp h
      subst hq1
      have hp0 : p = 0 := by
        have : (2 : F) * p = 0 := by linear_combination hp
        simpa using this
      apply hu
      rw [hsu, hp0]
      simp
    · linear_combination h
  subst hq'
  let B := Algebra.TensorProduct.basis K b
  have hB0 : B 0 = (1 : K) ⊗ₜ[F] (1 : E) := by simp [B, hb0]
  have hB1 : B 1 = (1 : K) ⊗ₜ[F] u := by simp [B, hb1]
  obtain ⟨a, c, hac⟩ : ∃ a c : K, x = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] u := by
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    have := B.sum_repr x
    rw [Fin.sum_univ_two, hB0, hB1] at this
    simpa [TensorProduct.smul_tmul'] using this.symm
  have hs : sigR K σ x = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] σ u := by
    rw [hac]
    simp [sigR]
  have hkey : (algebraMap F K p * c) • B 0 = (c + c) • B 1 := by
    rw [hB0, hB1]
    have h1 : a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] σ u = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] u := by rw [← hs, hx, hac]
    have h2 := add_left_cancel h1
    rw [hsu, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, neg_smul, one_smul] at h2
    have e0 : (algebraMap F K p * c) • ((1 : K) ⊗ₜ[F] (1 : E)) = p • (c ⊗ₜ[F] (1 : E)) := by
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      congr 1
      simp [Algebra.smul_def]
    have e1 : (c + c) • ((1 : K) ⊗ₜ[F] u) = c ⊗ₜ[F] u + c ⊗ₜ[F] u := by
      rw [TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
      simp
    rw [e0, e1]
    exact add_neg_eq_iff_eq_add.mp h2
  have hc : c = 0 := by
    have h1 := congrArg (fun y => B.repr y 1) hkey
    simp at h1
    have h2 : (2 : F) • c = 0 := by rw [two_smul]; exact h1.symm
    rcases smul_eq_zero.mp h2 with h | h
    · simp at h
    · exact h
  refine ⟨a, ?_⟩
  rw [hac, hc, Algebra.TensorProduct.algebraMap_apply]
  simp

theorem fixedK : PositivityTheory.SiegelWeilFormula.Gunr.FixedK := by
  intro F E _ _ _ _ _ σ h v x hx
  obtain ⟨-, hC, hfin, hconj⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσ : ∀ y, σ (σ y) = y := fun y => τ.injective (by rw [hconj, hconj, star_star])
  obtain ⟨u, hu⟩ : ∃ u, σ u ≠ u := by
    by_contra hall
    push Not at hall
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext y
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := hconj τ y
    rw [hall y] at this
    exact this.symm
  exact exists_eq_algebraMap_of_sigR_eq σ hfin hσ u hu x hx

end GlobalTheory.CompanionTheory.FixedPointsCM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumQuadraticCharacterBound
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem setIntegral_translate_of_iff {X : Type} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (m : Measure X)
    [m.IsAddHaarMeasure] {A D : Set X} (hA : MeasurableSet A) (hD : MeasurableSet D) (g : X)
    (h : ∀ y, g + y ∈ A ↔ y ∈ D) (f : X → ℂ) :
    ∫ x in A, f x ∂m = ∫ y in D, f (g + y) ∂m := by
  rw [← integral_indicator hA, ← integral_indicator hD,
    ← integral_add_left_eq_self (μ := m) (Set.indicator A f) g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ D
  · simp [Set.indicator, hy, (h y).2 hy]
  · have : g + y ∉ A := fun hh => hy ((h y).1 hh)
    simp [Set.indicator, hy, this]

theorem weyl_sq_compact_open : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [m.IsAddHaarMeasure]
    (L : AddSubgroup X), IsCompact (L : Set X) → IsOpen (L : Set X) →
    ∀ (q : X → ℂ) (B : X → X → ℂ), Continuous q → (∀ x, ‖q x‖ = 1) →
    (∀ x y, q (x + y) = q x * q y * B x y) →
    (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y y', B x (y + y') = B x y * B x y') →
    ∀ x₀ : X, ‖∫ x in {y | y - x₀ ∈ L}, q x ∂m‖ ^ 2 ≤
      (m (L : Set X)).toReal * (m {y | y ∈ L ∧ ∀ l ∈ L, B l y = 1}).toReal := by
  intro X _ _ _ _ _ _ _ m _ L hLc hLo q B hq hq1 hqB hB1 hB2 x₀
  set C : Set X := {y | y - x₀ ∈ L} with hCdef
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have hCo : IsOpen C := hLo.preimage (continuous_id.sub continuous_const)
  have hCm : MeasurableSet C := hCo.measurableSet
  have hLfin : m (L : Set X) < ⊤ := hLc.measure_lt_top
  have hmC : m C = m (L : Set X) := by
    have : C = (fun h => -x₀ + h) ⁻¹' (L : Set X) := by
      ext y; simp [hCdef, sub_eq_neg_add]
    rw [this, measure_preimage_add]
  have hCfin : m C < ⊤ := hmC ▸ hLfin
  haveI : IsFiniteMeasure (m.restrict C) := ⟨by simpa using hCfin⟩
  haveI : IsFiniteMeasure (m.restrict (L : Set X)) := ⟨by simpa using hLfin⟩
  have hq0 : ∀ x, q x ≠ 0 := fun x h => by simpa [h] using hq1 x
  have hBnorm : ∀ x y, ‖B x y‖ = 1 := fun x y => by
    have := congrArg norm (hqB x y)
    simpa [hq1] using this.symm
  have hBform : ∀ x y, B x y = q (x + y) / (q x * q y) := fun x y => by
    rw [hqB x y]; field_simp [hq0 x, hq0 y]
  have hBc : Continuous (Function.uncurry B) := by
    have : Function.uncurry B = fun p : X × X => q (p.1 + p.2) / (q p.1 * q p.2) := by
      funext p; exact hBform p.1 p.2
    rw [this]
    exact (hq.comp (continuous_fst.add continuous_snd)).div
      ((hq.comp continuous_fst).mul (hq.comp continuous_snd)) fun p => mul_ne_zero (hq0 _) (hq0 _)
  have hconj : ∀ x, (starRingEnd ℂ) (q x) * q x = 1 := fun x => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hq1]; simp
  set I : ℂ := ∫ x in C, q x ∂m with hI
  set J : X → ℂ := fun y => ∫ x in C, B x y ∂m with hJ

  have hstep : I * (starRingEnd ℂ) I = ∫ y in (L : Set X), q y * J y ∂m := by
    have h1 : I * (starRingEnd ℂ) I = ∫ x' in C, (starRingEnd ℂ) (q x') * I ∂m := by
      rw [integral_mul_const, integral_conj, mul_comm]
    have h2 : ∫ x' in C, (starRingEnd ℂ) (q x') * I ∂m
        = ∫ x' in C, ∫ y in (L : Set X), q y * B x' y ∂m ∂m := by
      refine setIntegral_congr_fun hCm fun x' hx' => ?_
      have hx'' : x' - x₀ ∈ L := hx'
      have ht : I = ∫ y in (L : Set X), q (x' + y) ∂m := by
        refine setIntegral_translate_of_iff m hCm hLm x' (fun y => ?_) q
        have e : x' + y - x₀ = (x' - x₀) + y := by abel
        simp only [hCdef, Set.mem_setOf_eq, e, SetLike.mem_coe]
        exact L.add_mem_cancel_left hx''
      rw [ht, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      beta_reduce
      rw [hqB x' y]
      calc _ = ((starRingEnd ℂ) (q x') * q x') * (q y * B x' y) := by ring
        _ = _ := by rw [hconj, one_mul]
    have h3 : ∫ x' in C, ∫ y in (L : Set X), q y * B x' y ∂m ∂m
        = ∫ y in (L : Set X), ∫ x' in C, q y * B x' y ∂m ∂m := by
      refine integral_integral_swap ?_
      have hc : Continuous (Function.uncurry fun x' y => q y * B x' y) :=
        (hq.comp continuous_snd).mul hBc
      refine Integrable.of_bound hc.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun p => ?_)
      simp [Function.uncurry, hq1, hBnorm]
    rw [h1, h2, h3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hJ]
    rw [integral_const_mul]
  have hJle : ∀ y, ‖J y‖ ≤ (m (L : Set X)).toReal := fun y => by
    have := norm_setIntegral_le_of_norm_le_const (μ := m) (s := C) (f := fun x => B x y) (C := 1)
      hCfin (fun x _ => (hBnorm x y).le)
    simpa [Measure.real, hmC] using this
  have hJ0 : ∀ y l, l ∈ L → B l y ≠ 1 → J y = 0 := fun y l hl hne => by
    have ht : J y = ∫ x in C, B (l + x) y ∂m := by
      refine setIntegral_translate_of_iff m hCm hCm l (fun x => ?_) (fun x => B x y)
      have e : l + x - x₀ = l + (x - x₀) := by abel
      simp only [hCdef, Set.mem_setOf_eq, e]
      exact L.add_mem_cancel_left hl
    have h2 : J y = B l y * J y := by
      conv_lhs => rw [ht]
      simp only [hJ, hB1, integral_const_mul]
    have h3 : (1 - B l y) * J y = 0 := by rw [sub_mul, one_mul, ← h2, sub_self]
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hne
    · exact h
  set S : Set X := {y | y ∈ L ∧ ∀ l ∈ L, B l y = 1} with hS
  have hSL : S ⊆ (L : Set X) := fun y hy => hy.1
  have hSfin : m S < ⊤ := (measure_mono hSL).trans_lt hLfin
  have hcut : ∫ y in (L : Set X), q y * J y ∂m = ∫ y in S, q y * J y ∂m := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero hLm hSL fun y hy => ?_
    have : ¬ ∀ l ∈ L, B l y = 1 := fun h => hy.2 ⟨hy.1, h⟩
    push_neg at this
    obtain ⟨l, hl, hne⟩ := this
    simp [hJ0 y l hl hne]
  have hbound : ‖∫ y in S, q y * J y ∂m‖ ≤ (m (L : Set X)).toReal * (m S).toReal := by
    have := norm_setIntegral_le_of_norm_le_const (μ := m) (s := S) (f := fun y => q y * J y)
      (C := (m (L : Set X)).toReal) hSfin (fun y _ => by simpa [hq1] using hJle y)
    simpa [Measure.real] using this
  have hsq : ‖I‖ ^ 2 = ‖I * (starRingEnd ℂ) I‖ := by
    rw [norm_mul, RCLike.norm_conj, sq]
  rw [hsq, hstep, hcut]
  exact hbound

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalZetaIntegralConvergence
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem two_cpow_ne_one {s : ℂ} (hs : 0 < s.re) : (1 : ℂ) - 2 ^ (-s) ≠ 0 := by
  intro h
  have h1 : ‖(2 : ℂ) ^ (-s)‖ = 1 := by rw [← sub_eq_zero.1 h]; simp
  have h2 : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    simp
  have h3 : (2 : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

def Jh (μ : Measure G2) (𝓕 : Set G2) (H : G2 → ℂ) (c : HeckeCharacter ℚ) (s : ℂ) : ℂ :=
  Bd μ 𝓕 H c s * 2 ^ (-s) / (1 - 2 ^ (-s))

def Ed (μ : Measure G2) (𝓕 : Set G2) (H : G2 → ℂ) (c : HeckeCharacter ℚ) (Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ) (s : ℂ) : ℂ :=
  (1 - 2 ^ (1 - s)) * (Zp μ 𝓕 H c Φ s + Zp μ 𝓕 H c⁻¹ Φ' (1 - s) - Φ 0 * Jh μ 𝓕 H c s)
    + Φ' 0 * 2 ^ (1 - s) * Bd μ 𝓕 H c (s - 1)

theorem Ed_diff {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℂ} {c : HeckeCharacter ℚ} {Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ}
    (h1 : Differentiable ℂ (Zp μ 𝓕 H c Φ)) (h2 : Differentiable ℂ (Zp μ 𝓕 H c⁻¹ Φ'))
    (h3 : Differentiable ℂ (Bd μ 𝓕 H c)) : DifferentiableOn ℂ (Ed μ 𝓕 H c Φ Φ') {s | 0 < s.re} := by
  have hp : ∀ f : ℂ → ℂ, Differentiable ℂ f → Differentiable ℂ fun s => (2 : ℂ) ^ f s := fun f hf s =>
    (hf s).const_cpow (Or.inl (by norm_num))
  have e1 : Differentiable ℂ fun s : ℂ => (2 : ℂ) ^ (1 - s) := hp _ (by fun_prop)
  have e2 : Differentiable ℂ fun s : ℂ => (2 : ℂ) ^ (-s) := hp _ (by fun_prop)
  have e3 : Differentiable ℂ fun s : ℂ => Zp μ 𝓕 H c⁻¹ Φ' (1 - s) := h2.comp (by fun_prop)
  have e4 : Differentiable ℂ fun s : ℂ => Bd μ 𝓕 H c (s - 1) := h3.comp (by fun_prop)
  have e5 : DifferentiableOn ℂ (Jh μ 𝓕 H c) {s | 0 < s.re} := by
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((h3 s).mul (e2 s)).div ((differentiableAt_const _).sub (e2 s)) (two_cpow_ne_one hs)
  unfold Ed
  exact (((differentiable_const _).sub e1).differentiableOn.mul
    ((h1.add e3).differentiableOn.sub ((differentiable_const _).differentiableOn.mul e5))).add
    (((differentiable_const _).mul e1).mul e4).differentiableOn

theorem Ed_eq {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℂ} {c : HeckeCharacter ℚ} {Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ} {s : ℂ}
    (hs : 1 < s.re)
    (hz : Zg μ 𝓕 H c Φ s = Zp μ 𝓕 H c Φ s + Zp μ 𝓕 H c⁻¹ Φ' (1 - s) + Φ' 0 * Jl μ 𝓕 H c (s - 1) - Φ 0 * Jl μ 𝓕 H c s)
    (h0 : Jl μ 𝓕 H c s * (1 - 2 ^ (-s)) = Bd μ 𝓕 H c s * 2 ^ (-s))
    (h1 : Jl μ 𝓕 H c (s - 1) * (1 - 2 ^ (-(s - 1))) = Bd μ 𝓕 H c (s - 1) * 2 ^ (-(s - 1))) :
    Ed μ 𝓕 H c Φ Φ' s = (1 - 2 ^ (1 - s)) * Zg μ 𝓕 H c Φ s := by
  have n0 := two_cpow_ne_one (s := s) (by linarith)
  have e : Jh μ 𝓕 H c s = Jl μ 𝓕 H c s := by rw [Jh, ← h0, mul_div_assoc, div_self n0, mul_one]
  rw [neg_sub] at h1
  rw [Ed, e, hz]
  linear_combination (-Φ' 0) * h1

theorem Ed_fe {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℂ} {c : HeckeCharacter ℚ} {Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ} {s : ℂ}
    (hs : Strip s)
    (b0 : Bd μ 𝓕 H c⁻¹ (-s) = 2 ^ (-s) * Bd μ 𝓕 H c s)
    (b1 : Bd μ 𝓕 H c⁻¹ (-(s - 1)) = 2 ^ (-(s - 1)) * Bd μ 𝓕 H c (s - 1)) :
    (1 - 2 ^ s) * Ed μ 𝓕 H c Φ Φ' s = (1 - 2 ^ (1 - s)) * Ed μ 𝓕 H c⁻¹ Φ' Φ (1 - s) := by
  have n0 := two_cpow_ne_one (s := s) hs.1
  have n1 := two_cpow_ne_one (s := 1 - s) (by simpa using hs.2)
  have x0 : (2 : ℂ) ^ s ≠ 0 := by simp
  have x1 : (2 : ℂ) ^ (1 - s) ≠ 0 := by simp
  have i0 : (2 : ℂ) ^ (-s) = (2 ^ s)⁻¹ := Complex.cpow_neg _ _
  have i1 : (2 : ℂ) ^ (-(1 - s)) = (2 ^ (1 - s))⁻¹ := Complex.cpow_neg _ _
  rw [neg_sub] at b1
  simp only [Ed, Jh, inv_inv, sub_sub_cancel, show 1 - s - 1 = -s by ring, b0, b1]
  rw [i0] at n0 ⊢
  rw [i1] at n1 ⊢
  generalize (2 : ℂ) ^ s = x at *
  generalize (2 : ℂ) ^ (1 - s) = y at *
  generalize Bd μ 𝓕 H c s = A at *
  generalize Bd μ 𝓕 H c (s - 1) = M at *
  have hx : x - 1 ≠ 0 := fun h => n0 (by rw [sub_eq_zero.1 h]; simp)
  have hy : y - 1 ≠ 0 := fun h => n1 (by rw [sub_eq_zero.1 h]; simp)
  have hx' : 1 - x⁻¹ = (x - 1) / x := by field_simp
  have hy' : 1 - y⁻¹ = (y - 1) / y := by field_simp
  rw [hx', hy']
  field_simp
  ring

end GlobalTheory.CompanionTheory.RSZeta

theorem GlobalTheory.CompanionTheory.RSZeta.functional_equation : Ad3.R.G1a → Ad3.R.G3 → Ad3.R.AdelicThetaPoissonSummation → Ad3.R.G4 := by
  intro hG1 hG3 hG4a μ 𝓕 mK 𝓓 hS H hH Φ hΦ c hc
  obtain ⟨hΦ', hΦ'', hrel⟩ := hG4a Φ hΦ
  have hci : IsOfFinOrder c⁻¹ := hc.inv
  have hrel' : ∀ g, th (sFA Φ) g + sFA Φ 0 = (((Dt g)⁻¹ : ℝ) : ℂ) * (th Φ (inv2 g) + Φ 0) := by
    intro g
    have h := hrel (inv2 g)
    rw [GlobalTheory.CompanionTheory.RSZeta.det_inverse_twist_involutive, GlobalTheory.CompanionTheory.RSZeta.module_det_inverse_twist, inv_inv] at h
    rw [h, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (GlobalTheory.CompanionTheory.RSZeta.Dt_pos g).ne']
    simp
  have I1 := GlobalTheory.T.integrableOn_lower_zeta_integrand μ 𝓕 mK 𝓓 H c hG1 hS hH hc
  have I2 := GlobalTheory.T.integrableOn_lower_zeta_integrand μ 𝓕 mK 𝓓 H c⁻¹ hG1 hS hH hci
  have d1 := GlobalTheory.T.differentiable_partial_zeta_integral μ 𝓕 mK 𝓓 H Φ c hG3 hS hH hΦ
  have d2 := GlobalTheory.T.differentiable_partial_zeta_integral μ 𝓕 mK 𝓓 H (sFA Φ) c⁻¹ hG3 hS hH hΦ'
  have d1' := GlobalTheory.T.differentiable_partial_zeta_integral μ 𝓕 mK 𝓓 H Φ c⁻¹⁻¹ hG3 hS hH hΦ
  have d2' := GlobalTheory.T.differentiable_partial_zeta_integral μ 𝓕 mK 𝓓 H (sFA Φ) c⁻¹ hG3 hS hH hΦ'
  have b1 := GlobalTheory.T.differentiable_boundary_zeta_term μ 𝓕 mK 𝓓 H c hS hH
  have b2 := GlobalTheory.T.differentiable_boundary_zeta_term μ 𝓕 mK 𝓓 H c⁻¹ hS hH
  refine ⟨GlobalTheory.CompanionTheory.RSZeta.Ed μ 𝓕 H c Φ (sFA Φ), GlobalTheory.CompanionTheory.RSZeta.Ed μ 𝓕 H c⁻¹ (sFA Φ) Φ,
    GlobalTheory.CompanionTheory.RSZeta.Ed_diff d1 d2 b1, GlobalTheory.CompanionTheory.RSZeta.Ed_diff d2' d1' b2, ?_, ?_, ?_⟩
  · intro s hs
    have hs1 : 0 < (s - 1).re := by simp; linarith
    have hs0 : 0 < s.re := by linarith
    refine ⟨GlobalTheory.CompanionTheory.RSZeta.Ed_eq hs (GlobalTheory.T.global_zeta_integral_functional_equation μ 𝓕 mK 𝓓 H Φ (sFA Φ) c hG1 hG3 hS hH hΦ hΦ' hrel I1 s hs)
      (GlobalTheory.T.lower_zeta_integral_boundary_relation μ 𝓕 mK 𝓓 H c hG1 hS hH hc s (I1 s hs0)) (GlobalTheory.T.lower_zeta_integral_boundary_relation μ 𝓕 mK 𝓓 H c hG1 hS hH hc _ (I1 _ hs1)),
      GlobalTheory.CompanionTheory.RSZeta.Ed_eq hs (GlobalTheory.T.global_zeta_integral_functional_equation μ 𝓕 mK 𝓓 H (sFA Φ) Φ c⁻¹ hG1 hG3 hS hH hΦ' hΦ hrel' I2 s hs)
      (GlobalTheory.T.lower_zeta_integral_boundary_relation μ 𝓕 mK 𝓓 H c⁻¹ hG1 hS hH hci s (I2 s hs0)) (GlobalTheory.T.lower_zeta_integral_boundary_relation μ 𝓕 mK 𝓓 H c⁻¹ hG1 hS hH hci _ (I2 _ hs1))⟩
  · intro s hs
    exact GlobalTheory.CompanionTheory.RSZeta.Ed_fe hs (GlobalTheory.T.boundary_zeta_term_functional_equation μ 𝓕 mK 𝓓 H c hG1 hS hH hc s) (GlobalTheory.T.boundary_zeta_term_functional_equation μ 𝓕 mK 𝓓 H c hG1 hS hH hc (s - 1))
  · intro h1 h0
    apply h1
    have : GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c 0 = 0 := by
      simpa [GlobalTheory.CompanionTheory.RSZeta.Bd] using h0
    simp [GlobalTheory.CompanionTheory.RSZeta.Ed, this]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasInfCharGLRankZero
section
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.TreeInfSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

inductive ListInf (τ : E →+* ℂ) : List (Σ M : ℕ, Submodule ℂ (Sm E M)) → Multiset ℂ → Prop
  | nil : ListInf τ [] 0
  | cons {x : Σ M : ℕ, Submodule ℂ (Sm E M)} {l : List (Σ M : ℕ, Submodule ℂ (Sm E M))} {m₀ m' : Multiset ℂ} :
      HasInfCharGL x.2 τ m₀ → ListInf τ l m' → ListInf τ (x :: l) (m₀ + m')

theorem ListInf.split (τ : E →+* ℂ) (l₁ l₂ : List (Σ M : ℕ, Submodule ℂ (Sm E M))) (m : Multiset ℂ)
    (h : ListInf τ (l₁ ++ l₂) m) : ∃ m₁ m₂, ListInf τ l₁ m₁ ∧ ListInf τ l₂ m₂ ∧ m = m₁ + m₂ := by
  induction l₁ generalizing m with
  | nil => exact ⟨0, m, .nil, h, by simp⟩
  | cons x l ih =>
    have h' : ListInf τ (x :: (l ++ l₂)) m := h
    cases h' with
    | cons h₀ h' =>
      obtain ⟨m₁, m₂, h₁, h₂, rfl⟩ := ih _ h'
      exact ⟨_, m₂, .cons h₀ h₁, h₂, by rw [add_assoc]⟩

theorem listInf_ofFn (τ : E →+* ℂ) {c : ℕ} (N : Fin c → ℕ) (V : ∀ i, Submodule ℂ (Sm E (N i)))
    (m : Fin c → Multiset ℂ) (h : ∀ i, HasInfCharGL (V i) τ (m i)) :
    ListInf τ (List.ofFn fun i => (⟨N i, V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) (∑ i, m i) := by
  induction c with
  | zero => simpa using ListInf.nil
  | succ c ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    exact .cons (h 0) (ih (fun i => N i.succ) (fun i => V i.succ) (fun i => m i.succ) (fun i => h i.succ))

theorem hasInfCharGL_rank_zero (V : Submodule ℂ (Sm E 0)) (τ : E →+* ℂ) : HasInfCharGL V τ 0 := by
  refine ⟨rfl, fun u φ _ => ?_⟩
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm]

theorem infOf_of_listInf (τ : E →+* ℂ) {N : ℕ} (t : Tr E N) (hg : t.Good) (hu : t.Untw) (m : Multiset ℂ)
    (h : ListInf τ (t.leafList.filter fun x => 0 < x.1) m) : t.InfOf τ m := by
  induction t generalizing m with
  | @leaf M V z =>
    rcases hg with ⟨rfl, rfl, rfl⟩ | ⟨hM, -, -⟩
    · have h' : ListInf τ [] m := by simpa [Tr.leafList] using h
      cases h'
      exact ⟨0, hasInfCharGL_rank_zero _ τ, by simp⟩
    · have hz : z = 0 := hu z (by simp [Tr.twists])
      subst hz
      have h' : ListInf τ [(⟨M, V⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))] m := by
        simpa [Tr.leafList, hM] using h
      cases h' with
      | cons h₀ h₁ =>
        cases h₁
        exact ⟨_, h₀, by simp⟩
  | node t₁ t₂ ih₁ ih₂ =>
    have hu₁ : t₁.Untw := fun z hz => hu z (by simp [Tr.twists, hz])
    have hu₂ : t₂.Untw := fun z hz => hu z (by simp [Tr.twists, hz])
    have h' := h
    simp only [Tr.leafList, List.filter_append] at h'
    obtain ⟨m₁, m₂, h₁, h₂, rfl⟩ := ListInf.split τ _ _ m h'
    exact ⟨m₁, m₂, ih₁ hg.1 hu₁ m₁ h₁, ih₂ hg.2 hu₂ m₂ h₂, rfl⟩

theorem treeInf : PositivityTheory.Rg.BcB.F.RS.TreeInf := by
  intro hT E _ _ _ N t P τ m hg hu hp h0 hm
  have h1 := listInf_ofFn τ P.N P.V (fun i => P.m i τ) (fun i => P.inf i τ)
  have hp' : (List.ofFn fun i => (⟨P.N i, P.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) =
      t.leafList.filter fun x => 0 < x.1 := hp
  rw [hp'] at h1
  exact GlobalTheory.BcSpehProof.hasInfCharGL_unique h0 (hT E N t τ _ (infOf_of_listInf τ t hg hu _ h1)) hm

end GlobalTheory.CompanionTheory.TreeInfSum

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianLineBundleSmoothStatement
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_line_bundle_smooth : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)), IsHermRep M A → Geo.IsSmoothHerm A := by
  first | exact @GlobalTheory.CompanionTheory.MPSmooth.smooth_of_isHermRep | exact GlobalTheory.CompanionTheory.MPSmooth.smooth_of_isHermRep | (intros; apply GlobalTheory.CompanionTheory.MPSmooth.smooth_of_isHermRep <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsRepOrderedWordOccursStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_rep_ordered_word_occurs : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → ∀ (𝔪 : Multiset (Segment k)) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL 𝔪 π → ∀ (h : ℕ) (Δ : Fin h → Segment k), IsOrderedForm Δ 𝔪 → Wd π (wtW Δ) := by
  first | exact @GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL | exact GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL | (intros; apply GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL <;> assumption)
end

