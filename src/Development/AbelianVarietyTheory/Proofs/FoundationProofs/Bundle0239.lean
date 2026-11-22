import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0231

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValues
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.TraceInt

theorem pair_integral {E : Type} [Field E] [NumberField E] [StarRing E] {N N' : ℕ}
    {L : Submodule (𝓞 E) (Fin N → E)} {L' : Submodule (𝓞 E) (Fin N' → E)}
    (hL : IsSDLat E N L) (hL' : IsSDLat E N' L') {A B : Matrix (Fin N') (Fin N) E}
    (hA : ∀ x ∈ L, A.mulVec x ∈ L') (hB : ∀ x ∈ L, B.mulVec x ∈ L') :
    IsIntegral ℤ (∑ i, ∑ j, A i j * star (B i j)) := by
  obtain ⟨hLfg, hLspan, hLdual⟩ := hL
  obtain ⟨-, -, hL'dual⟩ := hL'
  obtain ⟨m, x, φ, hx, hφ, hxφ⟩ := GlobalTheory.TauLat.exists_dual_family L ⟨hLfg, hLspan⟩

  set ψ : Fin m → Fin N → E := fun k b => star (φ k b) with hψdef
  have hψ : ∀ k, ψ k ∈ L := by
    intro k
    rw [hLdual]
    intro y hy
    rw [GlobalTheory.TauLat.mem_range_iff]
    have h1 : ∑ i, star (y i) * ψ k i = starRingEnd E (φ k ⬝ᵥ y) := by
      rw [starRingEnd_apply, dotProduct, star_sum]
      simp [hψdef, star_mul', mul_comm]
    unfold stdH
    rw [h1]
    exact GlobalTheory.TauLat.integral_map _ (hφ k y hy)

  have key : ∀ i, ∑ j, A i j * star (B i j) = ∑ k, (A.mulVec (x k)) i * star ((B.mulVec (ψ k)) i) := by
    intro i
    have e1 : ∑ j, A i j * star (B i j) =
        ∑ a, ∑ b, A i a * star (B i b) * ∑ k, x k a * φ k b := by
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [hxφ, mul_ite]
    rw [e1]
    simp only [Matrix.mulVec, dotProduct, hψdef, star_sum, star_mul', star_star, Finset.mul_sum,
      Finset.sum_mul]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_comm]
  refine IsIntegral.sum _ fun k _ => ?_

  have hint : IsIntegral ℤ (∑ i, star ((A.mulVec (x k)) i) * (B.mulVec (ψ k)) i) := by
    rw [← GlobalTheory.TauLat.mem_range_iff]
    exact (hL'dual _).1 (hB _ (hψ k)) _ (hA _ (hx k))
  have h2 : ∑ i, (A.mulVec (x k)) i * star ((B.mulVec (ψ k)) i) =
      starRingEnd E (∑ i, star ((A.mulVec (x k)) i) * (B.mulVec (ψ k)) i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, starRingEnd_apply, starRingEnd_apply, star_star, mul_comm]
  rw [h2]
  exact GlobalTheory.TauLat.integral_map _ hint

theorem mulVec_mem_of_homL (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ homL D L L') : ∀ x ∈ L, A.mulVec x ∈ L' := by
  unfold homL at hA
  induction hA using Submodule.span_induction with
  | mem B hB => exact hB
  | zero => intro x _; simp
  | add B C _ _ hB hC =>
    intro x hx
    rw [Matrix.add_mulVec]
    exact L'.add_mem (hB x hx) (hC x hx)
  | smul c B _ hB =>
    intro x hx
    rw [Matrix.smul_mulVec]
    exact L'.smul_mem c (hB x hx)

theorem hYY_add_left (D : D7) {N N' : ℕ} (x x' y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (x + x') y = hYY D x y + hYY D x' y := by
  unfold hYY
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add]

theorem hYY_add_right (D : D7) {N N' : ℕ} (x y y' : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D x (y + y') = hYY D x y + hYY D x y' := by
  unfold hYY
  simp only [Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hYY_gen (D : D7) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : SD D L) (hL' : SD D L')
    {a a' : D.host.E} (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    (ha' : a' ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    {A B : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ homL D L L') (hB : B ∈ homL D L L') :
    hYY D (a • A) (a' • B) ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  have hs : IsIntegral ℤ (∑ i, ∑ j, A i j * D.host.conj (B i j)) := by
    let _ := D.host.cmStar
    have h := pair_integral (E := D.host.E) hL hL' (mulVec_mem_of_homL D hA) (mulVec_mem_of_homL D hB)
    simpa only [bridge_star_holds _ D.host] using h
  have hsum : ∑ i, ∑ j, (a • A) i j * D.host.conj ((a' • B) i j) =
      a * (∑ i, ∑ j, A i j * D.host.conj (B i j)) * D.host.conj a' := by
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have has : a * (∑ i, ∑ j, A i j * D.host.conj (B i j)) ∈ D.host.AA0 := by
    have h1 : ∀ c : 𝓞 D.host.E, (c : D.host.E) * a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
      intro c
      have h := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha
      rwa [Algebra.smul_def] at h
    rw [mul_comm]
    exact h1 ⟨_, hs⟩
  unfold hYY
  rw [hsum]
  exact (factMMUnimodular _ D.host _).1 has a' ha'

private theorem exists_ringOfIntegers_eq_conj (D : D7) (c : 𝓞 D.host.E) :
    ∃ c' : 𝓞 D.host.E, (c' : D.host.E) = D.host.conj (c : D.host.E) :=
  ⟨⟨D.host.conj (c : D.host.E),
    GlobalTheory.TauLat.integral_map (D.host.conj : D.host.E →+* D.host.E) c.isIntegral_coe⟩, rfl⟩

private theorem conjO_conjO_unimodular_class_representatives (D : D7) (z : D.host.E) : D.host.conj (D.host.conj z) = z := by
  let _ := D.host.cmStar
  rw [← bridge_star_holds _ D.host z, ← bridge_star_holds _ D.host (star z), star_star]

private theorem hYY_smul_left_eq_conj_smul_right (D : D7) {N N' : ℕ} (c c' : 𝓞 D.host.E)
    (hc : (c' : D.host.E) = D.host.conj (c : D.host.E)) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D (c • x) y = hYY D x (c' • y) := by
  unfold hYY
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, Matrix.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
  change (c : D.host.E) * x i j * D.host.conj (y i j) =
    x i j * (D.host.conj (c' : D.host.E) * D.host.conj (y i j))
  rw [hc, conjO_conjO_unimodular_class_representatives]
  ring

private theorem hYY_smul_right_eq_conj_smul_left (D : D7) {N N' : ℕ} (c c' : 𝓞 D.host.E)
    (hc : (c' : D.host.E) = D.host.conj (c : D.host.E)) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D x (c • y) = hYY D (c' • x) y := by
  have hc' : (c : D.host.E) = D.host.conj (c' : D.host.E) := by rw [hc, conjO_conjO_unimodular_class_representatives]
  exact (hYY_smul_left_eq_conj_smul_right D c' c hc' x y).symm

theorem hYY_integral : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' →
    ∀ x ∈ YYl D L L', ∀ y ∈ YYl D L L', hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  intro D N N' L L' hL hL' x hx y hy
  have hsub : ∀ (c : 𝓞 D.host.E) (a : D.host.E),
      a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) →
      (c : D.host.E) * a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro c a ha
    have h := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha
    rwa [Algebra.smul_def] at h

  have hgen : ∀ y ∈ YYl D L L', ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      ∀ A ∈ homL D L L', hYY D (a • A) y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
    intro y hy
    unfold YYl at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a', ha', B, hB, rfl⟩ := hz
      intro a ha A hA
      exact hYY_gen D hL hL' ha ha' hA hB
    | zero =>
      intro a _ A _
      unfold hYY
      simp
    | add z w _ _ hz hw =>
      intro a ha A hA
      rw [hYY_add_right]
      exact Subring.add_mem _ (hz a ha A hA) (hw a ha A hA)
    | smul c z _ hz =>
      intro a ha A hA
      obtain ⟨c', hc'⟩ := exists_ringOfIntegers_eq_conj D c
      rw [hYY_smul_right_eq_conj_smul_left D c c' hc', ← smul_assoc, Algebra.smul_def]
      exact hz _ (hsub c' a ha) A hA
  unfold YYl at hx
  induction hx using Submodule.span_induction generalizing y with
  | mem z hz =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hz
    exact hgen y hy a ha A hA
  | zero =>
    unfold hYY
    simp
  | add z w _ _ hz hw =>
    rw [hYY_add_left]
    exact Subring.add_mem _ (hz y hy) (hw y hy)
  | smul c z _ hz =>
    obtain ⟨c', hc'⟩ := exists_ringOfIntegers_eq_conj D c
    rw [hYY_smul_left_eq_conj_smul_right D c c' hc']
    exact hz _ ((YYl D L L').smul_mem c' hy)

end GlobalTheory.NormSum.TraceInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.CurveLattice

open scoped UpperHalfPlane nonZeroDivisors Real

theorem eisG_eq_G (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    {k : ℕ} (hk : k ≠ 0) : eisG Λ k = L.G (2 * k) := by
  have h1 : eisG Λ k = ∑' z : ℂ, ({w : ℂ | w ∈ Λ ∧ w ≠ 0}).indicator (fun w => (w ^ (2 * k))⁻¹) z := by
    rw [← tsum_subtype, eisG]
    exact tsum_congr fun w => one_div _
  have h2 : L.G (2 * k) = ∑' z : ℂ, (L.lattice : Set ℂ).indicator (fun w => (w ^ (2 * k))⁻¹) z := by
    rw [← tsum_subtype, PeriodPair.G]
    rfl
  rw [h1, h2]
  refine tsum_congr fun z => ?_
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Set.indicator, hk]
  · simp [Set.indicator, hz, h]

section

variable {Λ : AddSubgroup ℂ} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha

theorem indep_of_tau : LinearIndependent ℝ ![a * (τ : ℂ), a] := by
  rw [LinearIndependent.pair_iff]
  intro s t e
  have e2 : (s * τ + t : ℂ) = 0 := mul_left_cancel₀ ha (by
    simp only [Complex.real_smul] at e
    linear_combination e)
  have e3 : s = 0 := by simpa [τ.im_ne_zero] using congrArg Complex.im e2
  exact ⟨e3, by simpa [e3] using e2⟩

include h

omit ha in
theorem eq_closure_of_tau : Λ = AddSubgroup.closure {a * (τ : ℂ), a} := by
  ext x
  rw [h, AddSubgroup.mem_closure_pair]
  refine exists_congr fun m => exists_congr fun n => ?_
  rw [zsmul_eq_mul, zsmul_eq_mul, show (m : ℂ) * (a * τ) + n * a = a * (m * τ + n) by ring]

theorem discr_of_tau : TaylorLogMetric.discr Λ = (2 * π / a) ^ 12 * ModularForm.discriminant τ := by
  let L : PeriodPair := ⟨a * τ, a, indep_of_tau ha⟩
  have hL : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x := fun x => by
    rw [PeriodPair.mem_lattice]
    refine exists_congr fun m => exists_congr fun n => ?_
    rw [show (m : ℂ) * L.ω₁ + n * L.ω₂ = a * (m * τ + n) by simp only [L]; ring]
  have hh : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := fun z => by rw [h, hL]
  rw [← latticeCurve_Δ_eq_discriminant ha hL, latticeCurve_Δ, TaylorLogMetric.discr, g2, g3,
    eisG_eq_G L Λ hh (by norm_num), eisG_eq_G L Λ hh (by norm_num)]
  rfl

theorem area_of_tau : area Λ = ‖a‖ ^ 2 * τ.im := by
  have hy := τ.im_pos
  have hp : 0 < ‖a‖ ^ 2 * τ.im := by have := norm_pos_iff.2 ha; positivity
  have key : ∀ m n m' n' : ℤ, |((starRingEnd ℂ) (a * (m * (τ : ℂ) + n)) * (a * (m' * (τ : ℂ) + n'))).im| =
      ‖a‖ ^ 2 * τ.im * |((n * m' - m * n' : ℤ) : ℝ)| := fun m n m' n' => by
    rw [← abs_of_pos hp, ← abs_mul]
    congr 1
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨hp, _, (h _).2 ⟨0, 1, rfl⟩, _, (h _).2 ⟨1, 0, rfl⟩, ?_⟩
    rw [key]
    simp
  · rintro r ⟨hr, w₁, h1, w₂, h2, rfl⟩
    obtain ⟨m, n, rfl⟩ := (h _).1 h1
    obtain ⟨m', n', rfl⟩ := (h _).1 h2
    rw [key] at hr ⊢
    have h0 : (n * m' - m * n' : ℤ) ≠ 0 := fun e => by simp [e] at hr
    have : (1 : ℝ) ≤ |((n * m' - m * n' : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h0
    exact le_mul_of_one_le_right hp.le this

end

theorem mem_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ w : ℂ) :
    w ∈ lamOf D cc δ ↔ ∃ c ∈ cc, w = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, cc.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', cc.add_mem hc hc', by simp [mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, cc.neg_mem hc, by simp⟩
  · exact fun hw => AddSubgroup.subset_closure hw

theorem finrank_hostK (D : D7) : Module.finrank ℚ D.host.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K D.host.hyp.2.1.pos (D.host.sqd_sq)

theorem discr_hostK (D : D7) : NumberField.discr D.host.K = -(D.host.d : ℤ) :=
  discr_eq_neg_of_sq_eq (finrank_hostK D) D.host.hyp.2.1.squarefree
    (by have := D.host.hyp.2.2.2.1; omega)
    (Formalism.FrobeniusOrbits.SplitK.bK_sq (D.host.sqd_sq))

theorem exists_tau (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) :
    ∃ (a : ℂ) (τ : ℍ), a ≠ 0 ∧ (Ideal.absNorm cc : ℝ) = 2 * ‖a‖ ^ 2 * τ.im / √(D.host.d) ∧
      ∀ δ x : ℂ, x ∈ lamOf D cc δ ↔ ∃ m n : ℤ, δ * a * (m * (τ : ℂ) + n) = x := by
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp D.host.K.val.toRingHom
  let I : (Ideal (𝓞 D.host.K))⁰ := ⟨cc, mem_nonZeroDivisors_of_ne_zero hcc⟩
  obtain ⟨L, hL⟩ := QuadraticZeta.exists_periodPair (finrank_hostK D) (discr_hostK D) σ
    (FractionalIdeal.mk0 D.host.K I)
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  have h' : ∀ z, z ∈ σ '' (cc : FractionalIdeal (𝓞 D.host.K)⁰ D.host.K) ↔
      ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = z := fun z => by
    rw [← h, ← SetLike.mem_coe, hL]
    rfl
  have hN := QuadraticZeta.absNorm_eq_of_image (finrank_hostK D) (discr_hostK D) σ ha h'
  rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] at hN
  refine ⟨a, τ, ha, hN, fun δ x => ?_⟩
  rw [mem_lamOf]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨m, n, e⟩ := (h' _).1 ⟨(c : D.host.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
    exact ⟨m, n, by rw [mul_assoc, e]; rfl⟩
  · rintro ⟨m, n, rfl⟩
    obtain ⟨y, hy, e⟩ := (h' _).2 ⟨m, n, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨c, hc, by rw [mul_assoc, ← e]; rfl⟩

theorem lattice_of_curve : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ (lamOf D cc δ) = AddSubgroup.closure {w₁, w₂}) ∧ δ ≠ 0 ∧ TaylorLogMetric.discr (lamOf D cc δ) = 1 ∧ area (lamOf D cc δ) = ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 ∧ (∀ a : 𝓞 D.host.K, ∀ w ∈ (lamOf D cc δ), D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ (lamOf D cc δ)) := by
  intro D _ cc δ ⟨⟨hcc, _⟩, hδ⟩
  obtain ⟨a, τ, ha, hN, h⟩ := exists_tau D cc hcc
  have h1 := discr_of_tau (by simpa using ha) (h 1)
  rw [one_mul] at h1
  have hδ' : δ ^ 12 = (2 * π / a) ^ 12 * ModularForm.discriminant τ := hδ.trans h1
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have := ModularForm.discriminant_ne_zero τ
    have := Real.pi_ne_zero
    simp [*] at hδ'
  have hda : δ * a ≠ 0 := mul_ne_zero hδ0 ha
  refine ⟨⟨_, _, indep_of_tau (τ := τ) hda, eq_closure_of_tau (h δ)⟩, hδ0, ?_, ?_, ?_⟩
  · rw [discr_of_tau hda (h δ), show (2 * π / (δ * a) : ℂ) ^ 12 * ModularForm.discriminant τ =
      ((2 * π / a) ^ 12 * ModularForm.discriminant τ) / δ ^ 12 by field_simp, ← hδ',
      div_self (pow_ne_zero _ hδ0)]
  · have hd : 0 < √(D.host.d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
    rw [area_of_tau hda (h δ), hN, norm_mul]
    field_simp
  · intro b w hw
    obtain ⟨c, hc, rfl⟩ := (mem_lamOf D cc δ w).1 hw
    exact (mem_lamOf D cc δ _).2 ⟨b * c, cc.mul_mem_left b hc, by simp; ring⟩

end GlobalTheory.CurveLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.InducedType

open Formalism.FrobeniusOrbits Formalism.MainNotions.UnusedSlot33.HK

theorem sigmaOf_mul {R : Ranks} (H : Host R) (g g' : R.GG) :
    H.sigmaOf (g * g') = H.sigmaOf g * H.sigmaOf g' := map_mul (H.gal).symm g g'

theorem sigmaOf_one {R : Ranks} (H : Host R) : H.sigmaOf 1 = 1 := map_one (H.gal).symm

theorem emb_apply {R : Ranks} (H : Host R) (g : R.GG) (x : H.E) : H.emb g x = H.φ₀ (H.sigmaOf g x) := rfl

def galK {R : Ranks} (H : Host R) (g : R.Psi) : H.E ≃ₐ[H.K] H.E :=
  { (H.sigmaOf g : H.E ≃+* H.E) with
    commutes' := fun a => sigmaOf_fix_K H g g.2 a a.2 }

theorem galK_apply {R : Ranks} (H : Host R) (g : R.Psi) (x : H.E) : galK H g x = H.sigmaOf g x := rfl

theorem galK_bijective {R : Ranks} (H : Host R) : Function.Bijective (galK H) := by
  constructor
  · intro g g' h
    apply Subtype.ext
    apply (H.gal).symm.injective
    exact AlgEquiv.ext fun x => congrArg (fun f : H.E ≃ₐ[H.K] H.E => f x) h
  · intro s
    refine ⟨⟨H.galE (s.restrictScalars ℚ), ?_⟩, ?_⟩
    · rw [H.galE_mem_Psi_iff]
      exact s.commutes ⟨_, bE_mem H⟩
    · refine AlgEquiv.ext fun x => ?_
      rw [galK_apply, sigmaOf_galE]
      rfl

theorem restrict_K (D : D7) : GL3Theta.InducedCMType D := fun τ a => by
  change D.host.φ₀ (D.host.sigmaOf _ _) = _
  rw [sigmaOf_fix_K D.host _ (D.eTau τ).2 _ a.2]

theorem sum_eq_trace (D : D7) : TraceMapNormalisation D := fun y => by
  have hE := D.host.hostE_isGalois
  have h := trace_eq_sum_automorphisms (K := D.host.K) (L := D.host.E) y
  change _ = D.host.φ₀ (algebraMap D.host.K D.host.E _)
  rw [h, map_sum]
  exact Fintype.sum_bijective (galK D.host ∘ D.eTau) ((galK_bijective D.host).comp D.eTau.bijective) _ _
    (fun τ => rfl)

theorem permutes (D : D7) : EmbeddingPermutesTypes D := fun M ρ hK hM => by
  have h0 : ∀ x, D.host.φ₀ x ∈ M := fun x => by
    have := hM (D.eTau.symm 1) x
    rwa [embT, Equiv.apply_symm_apply, emb_apply, Subgroup.coe_one, sigmaOf_one] at this
  let ψ : D.host.E →+* ℂ := (ρ : M →+* ℂ).comp (D.host.φ₀.codRestrict M h0)
  have hψ : ∀ x, cj M ρ (D.host.φ₀ x) = ψ x := fun x => by
    rw [cj, TaylorLogMetric.liftM, dif_pos (h0 x)]
    rfl
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 ψ
  have hgP : g ∈ D.R.Psi := by
    rw [← galE_sigmaOf D.host g, D.host.galE_mem_Psi_iff]
    apply D.host.φ₀.injective
    rw [← emb_apply, hg, ← hψ]
    exact (hK ⟨_, bE_mem D.host⟩).2
  refine ⟨D.eTau.trans ((Equiv.mulLeft (⟨g, hgP⟩ : D.R.Psi)).trans D.eTau.symm), fun τ x => ?_⟩
  rw [embT, emb_apply, hψ, ← hg, embT, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.coe_mulLeft, Subgroup.coe_mul, emb_apply, emb_apply, sigmaOf_mul]
  rfl

theorem induced_type : ∀ D : D7, admG1 D ∧ EmbeddingPermutesTypes D :=
  fun D => ⟨⟨restrict_K D, sum_eq_trace D⟩, permutes D⟩

end GlobalTheory.InducedType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemISupInfWeightSubmoduleOfDiagonalStable
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.WeightDecomp

lemma comp_mem {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V)
    (hN : ∀ a, ∀ x ∈ N, act (Eab a a) x ∈ N) (S : Finset (Ix p q → ℚ)) :
    ∀ f : (Ix p q → ℚ) → V, (∀ ν, f ν ∈ wtSub act ν) → ∑ ν ∈ S, f ν ∈ N → ∀ ν ∈ S, f ν ∈ N := by
  first
  | exact @_root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem
  | exact _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem
  | (apply _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem ..)

theorem mem_iSup_inf_wtSub : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V),
    (∀ a, ∀ x ∈ N, act (Eab a a) x ∈ N) → ∀ x ∈ N, x ∈ (⨆ μ : Ix p q → ℚ, wtSub act μ) →
      x ∈ ⨆ μ : Ix p q → ℚ, N ⊓ wtSub act μ := by
  intro p q V _ _ act N hN x hx hx'
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx'
  have h := comp_mem act N hN f.support f hf hx
  refine Submodule.sum_mem _ fun ν hν => ?_
  exact Submodule.mem_iSup_of_mem ν ⟨h ν hν, hf ν⟩

end GlobalTheory.WeightDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDualStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_weyl_lattices_fock_dual : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (x : Pol K ι n), x ∈ VV K lam → ((∀ y ∈ delStd K lam, pairP lam (fun _ => 1) y x ∈ (algebraMap (𝓞 K) K).range) ↔ x ∈ nabStd K lam) ∧ ((∀ y ∈ nabStd K lam, pairP lam (fun _ => 1) y x ∈ (algebraMap (𝓞 K) K).range) ↔ x ∈ delStd K lam) := by
  first | exact @GlobalTheory.StdDual.std_dual | exact GlobalTheory.StdDual.std_dual | (intros; apply GlobalTheory.StdDual.std_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPairingGramMatrixValuesAndDefiniteStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sumPairingGramMatrix_values_and_definite : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Fintype C] (N : ℕ) (e : Fin N ≃ C × VVIdx lam), (∀ x y : Fin N → K, star x ⬝ᵥ sumGram lam e G *ᵥ y = ∑ c, pairK lam G (valAt lam e c x) (valAt lam e c y)) ∧ IsDefGram (sumGram lam e G) ∧ IsDefGram ((sumGram lam e G)⁻¹)ᵀ ∧ (∀ τ, IsUnit (G τ).det) := by
  first | exact @GlobalTheory.TestLat.sumGram_spec | exact GlobalTheory.TestLat.sumGram_spec | (intros; apply GlobalTheory.TestLat.sumGram_spec <;> assumption)
end

