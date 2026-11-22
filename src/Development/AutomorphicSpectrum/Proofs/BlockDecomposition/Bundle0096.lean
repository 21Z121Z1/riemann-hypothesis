import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0030
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0080
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0086
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0079
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0084
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0083
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0062
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0085
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HuaDeterminantIntegrableOfLt
section
noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem continuous_detW (n : ℕ) : Continuous (fun b : Matrix (Fin n) (Fin n) ℂ => detW b) := by
  unfold detW
  exact Complex.continuous_re.comp (Continuous.matrix_det (by fun_prop))

theorem measurable_term (n : ℕ) (s : ℝ) :
    Measurable (fun b : hermC n => ENNReal.ofReal (detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s))) := by
  have h : Continuous (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ)) :=
    (continuous_detW n).comp continuous_subtype_val
  exact (h.measurable.pow_const _).ennreal_ofReal

theorem inner_eq (n : ℕ) (s : ℝ) (hs : (n : ℝ) + 1 / 2 < s) : ∃ K : ENNReal, K ≠ ⊤ ∧
    ∀ b' : hermC n, ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ,
      ENNReal.ofReal (detW (blk b' u d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)) =
      K * ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1))) := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨C, hC, hD⟩ := GlobalTheory.T.lintegral_power_line_scaling s (by linarith)
  have hL := GlobalTheory.T.lintegral_complex_power_finite n (2 * s - 1) (by linarith)
  set L := ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-(2 * s - 1))) with hLdef
  refine ⟨C * L, ENNReal.mul_ne_top hC hL, fun b' => ?_⟩
  have hB : (b' : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 b'.2
  have hw1 := GlobalTheory.T.one_le_detW_of_isHermitian n _ hB
  have hwA := GlobalTheory.T.detW_eq_normSq_det_one_add_I n _ hB
  have hdet : Matrix.det (1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) ≠ 0 := by
    intro h0
    rw [h0] at hwA
    simp at hwA
    linarith
  have hgm : Measurable (fun u : Fin n → ℂ => ∫⁻ d : ℝ,
      ENNReal.ofReal (detW (blk b' u d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))) := by
    apply Measurable.lintegral_prod_right'
      (f := fun p : (Fin n → ℂ) × ℝ => ENNReal.ofReal (detW (blk b' p.1 p.2 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)))
    have hc : Continuous (fun p : (Fin n → ℂ) × ℝ => detW (blk b' p.1 p.2 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) :=
      (continuous_detW _).comp (continuous_blkM.comp
        (by fun_prop : Continuous fun p : (Fin n → ℂ) × ℝ => ((b' : Matrix (Fin n) (Fin n) ℂ), p.1, p.2)))
    exact (hc.measurable.pow_const _).ennreal_ofReal
  rw [GlobalTheory.T.lintegral_linear_change_variables_complex n _ hdet _ hgm, ← hwA]
  have hv : ∀ v : Fin n → ℂ, ∫⁻ d : ℝ, ENNReal.ofReal (detW (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))
      = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) *
        (C * ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-(2 * s - 1)))) := by
    intro v
    have hr : 0 ≤ ∑ i, Complex.normSq (v i) := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    have hterm : ∀ d : ℝ, ENNReal.ofReal (detW (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))
        = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) *
          ENNReal.ofReal (((1 + ∑ i, Complex.normSq (v i)) ^ 2 +
            (d - (star v ⬝ᵥ ((b' : Matrix (Fin n) (Fin n) ℂ) *ᵥ v)).re) ^ 2) ^ (-s)) := by
      intro d
      have hh := mem_hermC.1 (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d).2
      rw [GlobalTheory.T.detW_eq_normSq_det_one_add_I _ _ hh]
      have e : ((blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : hermC (n+1)) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
          = blkM (b' : Matrix (Fin n) (Fin n) ℂ) ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d := rfl
      rw [e, GlobalTheory.T.detW_block_matrix_formula n _ hB hdet v d, ← hwA, Real.mul_rpow (by linarith) (by positivity),
        ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
    simp only [hterm]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hD (1 + ∑ i, Complex.normSq (v i)) (by linarith)]
    congr 3
    ring_nf
  simp only [hv]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ hC]
  have e2 : ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1)))
      = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ)) *
        ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) := by
    rw [← ENNReal.ofReal_mul (by linarith)]
    congr 1
    rw [show -(s - 1) = 1 + -s by ring, Real.rpow_add (by linarith), Real.rpow_one]
  rw [e2]
  ring

theorem hua_integrable : ∀ (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s → ∀ ν : Measure (hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  intro n
  induction n with
  | zero =>
    intro s _ ν hν
    have : IsFiniteMeasure ν := by
      haveI : Finite (hermC 0) := by
        haveI : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ) := inferInstance
        exact Finite.of_subsingleton
      haveI : CompactSpace (hermC 0) := Finite.compactSpace
      exact ⟨isCompact_univ.measure_lt_top⟩
    have h1 : ∀ b : hermC 0, detW (b : Matrix (Fin 0) (Fin 0) ℂ) ^ (-s) = 1 := by
      intro b
      simp [detW]
    simp only [h1]
    exact integrable_const _
  | succ n ih =>
    intro s hs ν hν
    have hs' : (n : ℝ) + 1 / 2 < s := by push_cast at hs; linarith
    have hpos : ∀ b : hermC (n + 1), 0 ≤ detW (b : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s) := fun b =>
      Real.rpow_nonneg (by linarith [GlobalTheory.T.one_le_detW_of_isHermitian _ _ (mem_hermC.1 b.2)]) _
    have hmeas := measurable_term (n + 1) s
    have hm2 : Measurable (fun b : hermC (n + 1) => detW (b : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)) :=
      (((continuous_detW (n + 1)).comp continuous_subtype_val).measurable.pow_const _)
    refine ⟨hm2.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpos)]
    obtain ⟨c, hc, hF⟩ := GlobalTheory.T.hermitian_haar_block_decomposition n ν (Measure.addHaar) hν inferInstance
    obtain ⟨K, hK, hI⟩ := inner_eq n s hs'
    rw [hF _ hmeas]
    simp only [hI]
    rw [lintegral_const_mul _ (measurable_term n (s - 1))]
    have h3 := ih (s - 1) (by linarith) Measure.addHaar inferInstance
    have hp3 : ∀ b : hermC n, 0 ≤ detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1)) := fun b =>
      Real.rpow_nonneg (by linarith [GlobalTheory.T.one_le_detW_of_isHermitian _ _ (mem_hermC.1 b.2)]) _
    have h4 := (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hp3)).1 h3.2
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc)
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hK) h4)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsDomMonoid
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem isDom_monoid : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), D.IsDom 1 ∧ ∀ t t' : D.T, D.IsDom t → D.IsDom t' → D.IsDom (t * t') := by
  intro G _ _ _ D
  refine ⟨⟨fun n hn => by simpa using hn, fun n hn => by simpa using hn,
    fun x hx => ⟨by simpa using hx, by simpa using hx⟩⟩, ?_⟩
  rintro t t' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
  refine ⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ⟨?_, ?_⟩⟩
  · have h := h1 _ (h1' n hn)
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := h2' _ (h2 n hn)
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := (h3 _ (h3' x hx).1).1
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := (h3' _ (h3 x hx).2).2
    rw [Subgroup.coe_mul]
    convert h using 1
    group

end GlobalTheory.CompanionTheory.Cass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetTraceFourthProperty
section
open Polynomial GlobalTheory.LeviDesc.Krylov

noncomputable section

namespace GlobalTheory.CompanionTheory.CharpolyConj

def compan {F : Type} [CommRing F] {r : ℕ} (P : F[X]) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun l j => if (j : ℕ) + 1 = r then -P.coeff l else if (l : ℕ) = (j : ℕ) + 1 then 1 else 0

theorem pow_mulVec_eq {F : Type} [CommRing F] [Nontrivial F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    Matrix.mulVec (y ^ r) e = ∑ l : Fin r, (-y.charpoly.coeff l) • Matrix.mulVec (y ^ (l : ℕ)) e := by
  have hch : Polynomial.aeval y y.charpoly = 0 := Matrix.aeval_self_charpoly y
  have hdeg : y.charpoly.natDegree = r := by simpa using Matrix.charpoly_natDegree_eq_dim y
  have hmon : y.charpoly.coeff r = 1 := by
    have := y.charpoly_monic.coeff_natDegree
    rwa [hdeg] at this
  rw [Polynomial.aeval_eq_sum_range, hdeg, Finset.sum_range_succ, hmon, one_smul] at hch
  have hy : y ^ r = -∑ l ∈ Finset.range r, y.charpoly.coeff l • y ^ l := eq_neg_of_add_eq_zero_right hch
  rw [hy, Finset.sum_range (fun l => y.charpoly.coeff l • y ^ l), Matrix.neg_mulVec, Matrix.sum_mulVec,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_mulVec, neg_smul]

theorem mul_krylov {F : Type} [CommRing F] [Nontrivial F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    y * krylov y e = krylov y e * compan y.charpoly := by
  ext i j
  have hl : (y * krylov y e) i j = Matrix.mulVec (y ^ ((j : ℕ) + 1)) e i := by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    rfl
  rw [hl, Matrix.mul_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · simp only [compan, Matrix.of_apply, if_pos hj, krylov_apply]
    rw [hj, pow_mulVec_eq y e, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [mul_comm]
  · have hlt : (j : ℕ) + 1 < r := lt_of_le_of_ne j.2 hj
    simp only [compan, Matrix.of_apply, if_neg hj, krylov_apply]
    rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hlt⟩ : Fin r)]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ (j : ℕ) + 1 := fun h => hb (Fin.ext h)
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h

end GlobalTheory.CompanionTheory.CharpolyConj

theorem GlobalTheory.CompanionTheory.CharpolyConj.main : PositivityTheory.Rg.Tf.Loc.A4 := by
  intro K _ n γ γ' hs hc
  obtain ⟨e, he⟩ := exists_isUnit_det_krylov_of_separable (γ : Matrix (Fin n) (Fin n) K) hs
  obtain ⟨e', he'⟩ := exists_isUnit_det_krylov_of_separable (γ' : Matrix (Fin n) (Fin n) K) (hc ▸ hs)
  have hu := (Matrix.isUnit_iff_isUnit_det _).2 he
  have hu' := (Matrix.isUnit_iff_isUnit_det _).2 he'
  have h1 := GlobalTheory.CompanionTheory.CharpolyConj.mul_krylov (γ : Matrix (Fin n) (Fin n) K) e
  have h2 := GlobalTheory.CompanionTheory.CharpolyConj.mul_krylov (γ' : Matrix (Fin n) (Fin n) K) e'
  rw [hc] at h1
  refine ⟨hu.unit * hu'.unit⁻¹, ?_⟩
  set B := hu.unit with hB
  set B' := hu'.unit with hB'
  have hBv : (B : Matrix (Fin n) (Fin n) K) = krylov (γ : Matrix (Fin n) (Fin n) K) e := rfl
  have hBv' : (B' : Matrix (Fin n) (Fin n) K) = krylov (γ' : Matrix (Fin n) (Fin n) K) e' := rfl
  set C : Matrix (Fin n) (Fin n) K := GlobalTheory.CompanionTheory.CharpolyConj.compan (γ' : Matrix (Fin n) (Fin n) K).charpoly with hC
  have key : ((B⁻¹ * γ * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((B'⁻¹ * γ' * B' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have a1 : ((B⁻¹ * γ * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = C := by
      rw [mul_assoc, Units.val_mul, Units.val_mul, hBv, h1, ← hBv, ← mul_assoc, Units.inv_mul, one_mul]
    have a2 : ((B'⁻¹ * γ' * B' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = C := by
      rw [mul_assoc, Units.val_mul, Units.val_mul, hBv', h2, ← hBv', ← mul_assoc, Units.inv_mul, one_mul]
    rw [a1, a2]
  have key' : B⁻¹ * γ * B = B'⁻¹ * γ' * B' := Units.ext key
  calc (B * B'⁻¹)⁻¹ * γ * (B * B'⁻¹) = B' * (B⁻¹ * γ * B) * B'⁻¹ := by group
    _ = B' * (B'⁻¹ * γ' * B') * B'⁻¹ := by rw [key']
    _ = γ' := by group
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JhMultMulLeOfSteps
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.CsStages

variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

theorem jhMult_add_le {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
    {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)
    (hι : Function.Injective ι) (hp : Function.Surjective p) (h0 : ∀ u, p (ι u) = 0) :
    jhMult σ ρ₁ + jhMult σ ρ₂ ≤ jhMult σ ρ := by
  refine ENat.biSup_add_biSup_le' ⟨0, occurs_zero _ _⟩ ⟨0, occurs_zero _ _⟩ fun a ha b hb => ?_
  rw [← Nat.cast_add]
  exact le_iSup₂_of_le _ (occurs_add ι p hι hp h0 ha hb) le_rfl

theorem jhMult_mul_le_of_steps (σ : Representation F G W) (ρ : Representation F G V)
    (A : Subrepresentation ρ → ℕ∞) (m : ℕ∞) (hmono : ∀ S T : Subrepresentation ρ, T ≤ S → A T ≤ A S)
    (hstep : ∀ S T : Subrepresentation ρ, T ≤ S → Nonempty ((subQuot S T).Equiv σ) → A T + m ≤ A S) :
    jhMult σ ρ * m ≤ A ⊤ := by
  have key : ∀ r, OccursTimes σ ρ r → (r : ℕ∞) * m ≤ A ⊤ := by
    rintro r ⟨S, T, h1, h2, h3⟩
    have hi : ∀ (i : ℕ) (hi : i < r), ((i + 1 : ℕ) : ℕ∞) * m ≤ A (S ⟨i, hi⟩) := by
      intro i
      induction i with
      | zero =>
        intro hi
        have := hstep _ _ (h1 ⟨0, hi⟩) (h3 ⟨0, hi⟩)
        simpa using le_trans le_add_self this
      | succ i ih =>
        intro hi
        have h4 := ih (by omega)
        have h5 := hmono _ _ (h2 ⟨i, by omega⟩ ⟨i + 1, hi⟩ (by simp [Fin.lt_def]))
        have h6 := hstep _ _ (h1 ⟨i + 1, hi⟩) (h3 ⟨i + 1, hi⟩)
        refine le_trans ?_ h6
        have : (((i + 1 + 1 : ℕ)) : ℕ∞) * m = ((i + 1 : ℕ) : ℕ∞) * m + m := by
          push_cast; ring
        rw [this]
        exact add_le_add (h4.trans h5) le_rfl
    rcases r with _ | r
    · simp
    · exact (hi r (by omega)).trans (hmono _ _ le_top)
  unfold jhMult
  rw [ENat.iSup_mul]
  refine iSup_le fun r => ?_
  rw [ENat.iSup_mul]
  exact iSup_le fun hr => key r hr

end GlobalTheory.CompanionTheory.CsStages
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralSplitColumnStatement
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_split_column : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (Φ : (Fin d → α → ℂ) → ℝ≥0∞), Measurable Φ → ∫⁻ C : Fin d → α → ℂ, Φ C = ∫⁻ C' : Fin d → {j : α // j ≠ j₀} → ℂ, ∫⁻ c : Fin d → ℂ, Φ (joinCol j₀ c C') := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.lintegral_joinCol | exact GlobalTheory.CompanionTheory.FSCrofton.lintegral_joinCol | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.lintegral_joinCol <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfLevelIsos
section
open CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerSeq

theorem lseq_transport : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' T T' : Sys.{1} W)
    (e : Sys.Hom S T (RingHom.id W)) (e' : Sys.Hom S' T' (RingHom.id W)),
    (∀ n, Function.Bijective (e.f n)) → (∀ n, Function.Bijective (e'.f n)) →
    LSeq l S S' → Nonempty (LSeq l T T') := by
  intro W _ l S S' T T' e e' h h' L
  let E : ∀ n, S.M n ≃ₗ[W] T.M n := fun n => LinearEquiv.ofBijective (e.f n) (h n)
  let E' : ∀ n, S'.M n ≃ₗ[W] T'.M n := fun n => LinearEquiv.ofBijective (e'.f n) (h' n)
  have hc : ∀ n y, T.r n (E (n + 1) y) = E n (S.r n y) := fun n y => e.comm n y
  have hc' : ∀ n y, T'.r n (E' (n + 1) y) = E' n (S'.r n y) := fun n y => e'.comm n y
  have hr : ∀ n x, (E n).symm (T.r n x) = S.r n ((E (n + 1)).symm x) := by
    intro n x
    apply (E n).injective
    rw [LinearEquiv.apply_symm_apply, ← hc, LinearEquiv.apply_symm_apply]
  refine ⟨{
    ρ := fun c b => (E b).toLinearMap ∘ₗ L.ρ c b ∘ₗ (E c).symm.toLinearMap
    ν := fun a c => (E c).toLinearMap ∘ₗ L.ν a c ∘ₗ (E a).symm.toLinearMap
    δ := fun b a => (E' a).toLinearMap ∘ₗ L.δ b a ∘ₗ (E b).symm.toLinearMap
    kill := ?_, ρ_self := ?_, ρ_succ := ?_, ν_ρ := ?_, ν_r := ?_, ex₁ := ?_, δ_r := ?_, ex₂ := ?_ }⟩
  · intro n x
    apply (E n).symm.injective
    rw [map_smul, L.kill, map_zero]
  · intro c x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [L.ρ_self, LinearEquiv.apply_symm_apply]
  · intro c b hb x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [L.ρ_succ c b hb, hr]
  · intro a c ha x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [L.ν_ρ a c ha, map_smul, LinearEquiv.apply_symm_apply]
  · intro a c ha y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hc, L.ν_r a c ha, hr]
  · intro a b c hcab x hx
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx
    have h0 : L.ρ c b ((E c).symm x) = 0 := by
      apply (E b).injective
      rw [hx, map_zero]
    obtain ⟨y, hy⟩ := L.ex₁ a b c hcab _ h0
    refine ⟨E a y, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hy, LinearEquiv.apply_symm_apply]
  · intro b a x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hc', L.δ_r]
  · intro a b c hcab x hx
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx
    have h0 : L.δ b a ((E b).symm x) = 0 := by
      apply (E' a).injective
      rw [hx, map_zero]
    obtain ⟨y, hy⟩ := L.ex₂ a b c hcab _ h0
    refine ⟨E c y, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hy, LinearEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.TowerSeq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixGaussSumCongrInvariance
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegCov

section Ring

variable {A : Type} [CommRing A]

theorem cT_mul (τ : A →+* A) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) A)
    (y : Matrix (Fin b) (Fin c) A) : cT τ (x * y) = cT τ y * cT τ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (τ : A →+* A) {a : ℕ} : cT τ (1 : Matrix (Fin a) (Fin a) A) = 1 := by
  unfold cT
  rw [Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one]

theorem cT_cT (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) {a b : ℕ} (x : Matrix (Fin a) (Fin b) A) :
    cT τ (cT τ x) = x := by
  unfold cT
  ext i j
  exact hτ (x i j)

def covEquiv (τ : A →+* A) {m n : ℕ} (G G' : Matrix (Fin n) (Fin n) A)
    (P P' : Matrix (Fin m) (Fin m) A) (hG : G * G' = 1) (hG' : G' * G = 1)
    (hP : P * P' = 1) (hP' : P' * P = 1) :
    Matrix (Fin m) (Fin n) A ≃ Matrix (Fin m) (Fin n) A where
  toFun x := P' * x * cT τ G'
  invFun y := P * y * cT τ G
  left_inv x := by
    have h : cT τ G' * cT τ G = 1 := by rw [← cT_mul, hG, cT_one]
    calc P * (P' * x * cT τ G') * cT τ G = (P * P') * x * (cT τ G' * cT τ G) := by
          simp only [Matrix.mul_assoc]
      _ = x := by rw [hP, h, Matrix.one_mul, Matrix.mul_one]
  right_inv y := by
    have h : cT τ G * cT τ G' = 1 := by rw [← cT_mul, hG', cT_one]
    calc P' * (P * y * cT τ G) * cT τ G' = (P' * P) * y * (cT τ G * cT τ G') := by
          simp only [Matrix.mul_assoc]
      _ = y := by rw [hP', h, Matrix.one_mul, Matrix.mul_one]

theorem eq_of_conj (τ : A →+* A) {n : ℕ} {h D g g' : Matrix (Fin n) (Fin n) A}
    (hg : g * g' = 1) (hD : cT τ g * h * g = D) : h = cT τ g' * D * g' := by
  have hg2 : cT τ g' * cT τ g = 1 := by rw [← cT_mul, hg, cT_one]
  rw [← hD]
  calc h = (cT τ g' * cT τ g) * h * (g * g') := by
        rw [hg2, hg, Matrix.one_mul, Matrix.mul_one]
    _ = cT τ g' * (cT τ g * h * g) * g' := by simp only [Matrix.mul_assoc]

theorem trace_cov (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) {m n : ℕ}
    (D g' : Matrix (Fin n) (Fin n) A) (E p' : Matrix (Fin m) (Fin m) A)
    (x : Matrix (Fin m) (Fin n) A) :
    Matrix.trace ((cT τ g' * D * g') * (cT τ x * (cT τ p' * E * p') * x)) =
      Matrix.trace (D * (cT τ (p' * x * cT τ g') * E * (p' * x * cT τ g'))) := by
  rw [cT_mul, cT_mul, cT_cT τ hτ]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (cT τ g')]
  simp only [Matrix.mul_assoc]

end Ring

section Red

variable {R : Type} [CommRing R]

theorem red_mul (ϖ : R) (k : ℕ) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) R)
    (y : Matrix (Fin b) (Fin c) R) : red ϖ k (x * y) = red ϖ k x * red ϖ k y := by
  unfold red
  exact Matrix.map_mul

theorem red_cT (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (k : ℕ) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) R) : red ϖ k (cT σ x) = cT (barσ σ ϖ hf k) (red ϖ k x) := by
  ext i j
  exact (barσ_mk σ ϖ hf k (x j i)).symm

theorem red_one (ϖ : R) (k : ℕ) {a : ℕ} : red ϖ k (1 : Matrix (Fin a) (Fin a) R) = 1 := by
  unfold red
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem barσ_inv (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (hσ : ∀ a, σ (σ a) = a) (k : ℕ)
    (a : R ⧸ lev ϖ k) : barσ σ ϖ hf k (barσ σ ϖ hf k a) = a := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [barσ_mk, barσ_mk, hσ]

end Red

theorem gauss_cov (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ)
    (hσ : ∀ a, σ (σ a) = a) (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ)
    (m n : ℕ) (h D g g' : Matrix (Fin n) (Fin n) R) (S E p p' : Matrix (Fin m) (Fin m) R)
    (hg : g * g' = 1) (hg' : g' * g = 1) (hp : p * p' = 1) (hp' : p' * p = 1)
    (hD : cT σ g * h * g = D) (hE : cT σ p * S * p = E) :
    (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
        χ (Matrix.trace (red ϖ k h * (cT (barσ σ ϖ hf k) x * red ϖ k S * x)))) =
      ∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
        χ (Matrix.trace (red ϖ k D * (cT (barσ σ ϖ hf k) y * red ϖ k E * y))) := by
  have hh : h = cT σ g' * D * g' := eq_of_conj σ hg hD
  have hS : S = cT σ p' * E * p' := eq_of_conj σ hp hE
  have rg : red ϖ k g * red ϖ k g' = 1 := by rw [← red_mul, hg, red_one]
  have rg' : red ϖ k g' * red ϖ k g = 1 := by rw [← red_mul, hg', red_one]
  have rp : red ϖ k p * red ϖ k p' = 1 := by rw [← red_mul, hp, red_one]
  have rp' : red ϖ k p' * red ϖ k p = 1 := by rw [← red_mul, hp', red_one]
  refine Fintype.sum_equiv
    (covEquiv (barσ σ ϖ hf k) (red ϖ k g) (red ϖ k g') (red ϖ k p) (red ϖ k p') rg rg' rp rp')
    _ _ ?_
  intro x
  have key : Matrix.trace (red ϖ k h * (cT (barσ σ ϖ hf k) x * red ϖ k S * x)) =
      Matrix.trace (red ϖ k D * (cT (barσ σ ϖ hf k) (red ϖ k p' * x * cT (barσ σ ϖ hf k) (red ϖ k g')) *
        red ϖ k E * (red ϖ k p' * x * cT (barσ σ ϖ hf k) (red ϖ k g')))) := by
    rw [hh, hS, red_mul, red_mul, red_mul, red_mul, red_cT σ ϖ hf, red_cT σ ϖ hf]
    exact trace_cov (barσ σ ϖ hf k) (barσ_inv σ ϖ hf hσ k) (red ϖ k D) (red ϖ k g') (red ϖ k E)
      (red ϖ k p') x
  exact congrArg (⇑χ) key

end GlobalTheory.CompanionTheory.SiegCov
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableZeroCountStatement
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_zero_count : ∀ (d : ℕ) (α : Type) [Fintype α] (U A : Set (V d)) (b : α → V d → ℂ), (∀ j, ContinuousOn (b j) U) → A ⊆ U → IsSigmaCompact A → Measurable (zeroCnt d A b : (Fin d → α → ℂ) → ℝ≥0∞) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt | exact GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLawOfBlockDetStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_law_of_block_det : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.ParLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEisPar.parLaw | exact GlobalTheory.CompanionTheory.RgEisPar.parLaw | (intros; apply GlobalTheory.CompanionTheory.RgEisPar.parLaw <;> assumption)
end

