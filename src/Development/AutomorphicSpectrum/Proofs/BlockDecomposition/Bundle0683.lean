import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0001
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.StepsD
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0437
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0653
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0667
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0669
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0670

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFiniteIntegral
section
namespace GlobalTheory.CompanionTheory.Gunr

open NumberField IsDedekindDomain Filter

theorem finInt : PositivityTheory.SiegelWeilFormula.Gunr.FinInt := by
  intro F _ _ X
  have hone : ∀ x : F, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F := by
    intro x
    have hfin : {v : HeightOneSpectrum (𝓞 F) | 1 < v.valuation F x}.Finite :=
      HeightOneSpectrum.Support.finite (𝓞 F) x
    have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ¬ 1 < v.valuation F x := by
      rw [eventually_cofinite]
      simpa using hfin
    refine hev.mono fun v hv => ?_
    have e : Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, e]
    exact not_lt.mp hv
  have hall : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∀ x ∈ X, algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F :=
    (Filter.eventually_all_finset X).2 fun x _ => hone x
  exact hall

end GlobalTheory.CompanionTheory.Gunr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightRegularity
section
noncomputable section

open Ad3.LR

namespace GlobalTheory.CompanionTheory.WeightRegular

theorem weight_eq_zero_neg_det (k : ℕ) (h : M22) (hd : (Matrix.of h).det < 0) : w0 k h = 0 := by
  have hdi : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hn : ¬ 0 < ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [hdi]
    exact not_lt.mpr (inv_nonpos.mpr hd.le)
  unfold w0 Wm
  rw [if_neg hn]
  simp

theorem contDiff_entry (i j : Fin 2) : ContDiff ℝ ⊤ (fun h : M22 => h i j) :=
  (contDiff_apply_apply ℝ ℝ i j)

theorem contDiff_entryC (i j : Fin 2) : ContDiff ℝ ⊤ (fun h : M22 => ((h i j : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_entry i j)

theorem contDiff_det : ContDiff ℝ ⊤ (fun h : M22 => (Matrix.of h).det) := by
  have : (fun h : M22 => (Matrix.of h).det) = fun h : M22 => h 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    funext h
    simp [Matrix.det_fin_two]
  rw [this]
  exact ((contDiff_entry 0 0).mul (contDiff_entry 1 1)).sub
    ((contDiff_entry 0 1).mul (contDiff_entry 1 0))

theorem contDiffOn_weight_pos_det (k : ℕ) (hk : 3 ≤ k) :
    ContDiffOn ℝ ⊤ (w0 k) {h : M22 | 0 < (Matrix.of h).det} := by
  have hF : ContDiffOn ℝ ⊤ (fun h : M22 =>
      (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) *
        ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1)) *
        Complex.exp (2 * Real.pi * Complex.I *
          (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I))))
      {h : M22 | 0 < (Matrix.of h).det} := by
    intro h hh
    apply ContDiffAt.contDiffWithinAt
    have hα := GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hh
    have cα : ContDiffAt ℝ ⊤ (fun h : M22 => (h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) h :=
      ((contDiff_entryC 0 0).add ((contDiff_entryC 1 0).mul contDiff_const)).contDiffAt
    have cβ : ContDiffAt ℝ ⊤ (fun h : M22 => (h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) h :=
      ((contDiff_entryC 0 1).add ((contDiff_entryC 1 1).mul contDiff_const)).contDiffAt
    have cd : ContDiffAt ℝ ⊤ (fun h : M22 => (((Matrix.of h).det : ℝ) : ℂ)) h :=
      (Complex.ofRealCLM.contDiff.comp contDiff_det).contDiffAt
    have e : -(2 * (k : ℤ) - 1) = -(((2 * k - 1 : ℕ)) : ℤ) := by
      have : 1 ≤ 2 * k := by omega
      push_cast [Nat.cast_sub this]
      ring
    have cz : ContDiffAt ℝ ⊤ (fun h : M22 =>
        ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1))) h := by
      simp only [e, zpow_neg, zpow_natCast]
      exact (cα.pow _).inv (pow_ne_zero _ hα)
    have cq : ContDiffAt ℝ ⊤ (fun h : M22 =>
        ((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I)) h := by
      simp only [div_eq_mul_inv]
      exact cβ.mul (cα.inv hα)
    have ce : ContDiffAt ℝ ⊤ (fun h : M22 => Complex.exp (2 * Real.pi * Complex.I *
        (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I)))) h :=
      (contDiffAt_const.mul cq).cexp
    exact ((cd.pow _).mul cz).mul ce
  exact hF.congr fun h hh => GlobalTheory.CompanionTheory.WeightClosed.main k hk h hh

theorem main_analytic (k : ℕ) (hk : 3 ≤ k) :
    (∀ h : M22, (Matrix.of h).det < 0 → w0 k h = 0) ∧
      ContDiffOn ℝ ⊤ (w0 k) {h : M22 | 0 < (Matrix.of h).det} :=
  ⟨fun h hd => weight_eq_zero_neg_det k h hd, contDiffOn_weight_pos_det k hk⟩

theorem main : Ad3.LR.DTr.WeightVanishesNegDetSmoothPosDet := fun k hk =>
  ⟨(main_analytic k hk).1, (main_analytic k hk).2.of_le le_top⟩

end GlobalTheory.CompanionTheory.WeightRegular
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankExtensionBound
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenUniq

theorem nonempty_equiv_of_generic_subquotients (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (N : ℕ) {V W₁ W₂ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W₁] [Module ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂] (ρ : Representation ℂ (GL (Fin N) k) V)
    (π : Representation ℂ (GL (Fin N) k) W₁) (σ : Representation ℂ (GL (Fin N) k) W₂)
    (hρ : IsSmooth ρ)
    (hrank : Module.rank ℂ (TwJacquet ρ (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible)
    (hπρ : IsSubquotient π ρ) (hσρ : IsSubquotient σ ρ)
    (hgπ : IsGenericFor ψ π) (hgσ : IsGenericFor ψ σ) : Nonempty (π.Equiv σ) := by
  obtain ⟨A, B, hBA, ⟨e₁⟩⟩ := GlobalTheory.T.subquotient_realised_by_subreps ρ π hπρ
  obtain ⟨C, D, hDC, ⟨e₂⟩⟩ := GlobalTheory.T.subquotient_realised_by_subreps ρ σ hσρ
  have hiAB : (subQuot A B).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₁ hπ
  have hiCD : (subQuot C D).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₂ hσ
  have hAB := (GlobalTheory.T.generic_subquotient_iff_whittaker_quotient k ψ hψ N ρ hρ A B hBA).1 (hgπ.of_equiv e₁)
  have hCD := (GlobalTheory.T.generic_subquotient_iff_whittaker_quotient k ψ hψ N ρ hρ C D hDC).1 (hgσ.of_equiv e₂)
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_equiv_subQuot_of_not_le_sup ρ (twKer ρ (unipB k (Fin N)) (whitChar ψ N)) hrank
    (GlobalTheory.T.twisted_kernel_sup_distributes_subreps k ψ hψ N ρ hρ) A B C D hBA hDC hiAB hiCD hAB hCD
  exact ⟨(e₁.trans e).trans e₂.symm⟩

end GlobalTheory.CompanionTheory.GenUniq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTorusValueFormulaHoldsStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_torus_value_formula_holds : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ (ν : Fˣ →* ℂˣ) (a b : ℤ),
  (b ≤ a → Ad3.LFS.s2 ψ ν (torusPow F 2 ![a, b]) =
    sqrtQ F ^ (-(a - b)) * evalAt ![ν (unifUnit F), (ν (unifUnit F))⁻¹] (schur ![a, b])) ∧
  (a < b → Ad3.LFS.s2 ψ ν (torusPow F 2 ![a, b]) = 0) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.whittaker_torus_value_formula | exact GlobalTheory.CompanionTheory.LFUDom.whittaker_torus_value_formula | (intros; apply GlobalTheory.CompanionTheory.LFUDom.whittaker_torus_value_formula <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerUnipotentEquivariantHoldsStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_unipotent_equivariant_holds : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ (ν : Fˣ →* ℂˣ) (y : F) (g : GL (Fin 2) F),
  Ad3.LFS.s2 ψ ν (Ad3.uni2 y * g) = ((ψ y : Circle) : ℂ) * Ad3.LFS.s2 ψ ν g := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.whittaker_unipotent_left_equivariant | exact GlobalTheory.CompanionTheory.LFUDom.whittaker_unipotent_left_equivariant | (intros; apply GlobalTheory.CompanionTheory.LFUDom.whittaker_unipotent_left_equivariant <;> assumption)
end

