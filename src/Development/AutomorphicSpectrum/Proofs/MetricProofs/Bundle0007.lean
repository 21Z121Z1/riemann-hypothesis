import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0002
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0002
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsOpenFlagDomainNondegenerateMinors

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffAtFrameEntry
section
open Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

def den (g : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) : ℂ := g 0 0 + g 0 1 * a

def mob (g : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) : ℂ := (g 1 0 + g 1 1 * a) / den g a

def mobD (g : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) : ℂ := g.det / den g a ^ 2

def mob1 {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (z : Fin (d + 1) → ℂ) : Fin (d + 1) → ℂ :=
  Fin.cons (mob (g (Fin.tail z)) (z 0)) (Fin.tail z)

def mob2 {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (z : Fin (d + 2) → ℂ) : Fin (d + 2) → ℂ :=
  Fin.cons (mob (g (Fin.tail (Fin.tail z))) (z 0))
    (Fin.cons (mob (g (Fin.tail (Fin.tail z))) (z 1)) (Fin.tail (Fin.tail z)))

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
end

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.contDiffAt_frame_entry {d : ℕ} (G g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ)
    (hC : ∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (p q : Fin 2) :
    ContDiffAt ℝ 2 (fun y' => ((g y')ᴴ * G y' * g y') p q) y := by
  have hg' : ∀ i j, ContDiffAt ℝ 2 (fun y' => g y' i j) y := fun i j =>
    ((ReciprocityTheory.AnForm.Osgood.osgood d Set.univ _ isOpen_univ (hg i j).differentiableOn y (Set.mem_univ _)).contDiffAt).restrict_scalars ℝ
  have hs : ∀ i j, ContDiffAt ℝ 2 (fun y' => star (g y' i j)) y := fun i j => by
    have h := (Complex.conjCLE.contDiff (n := 2)).contDiffAt.comp y (hg' i j)
    simpa [Function.comp_def] using h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  exact ((((hs 0 p).mul (hC 0 0)).add ((hs 1 p).mul (hC 1 0))).mul (hg' 0 q)).add
    ((((hs 0 p).mul (hC 0 1)).add ((hs 1 p).mul (hC 1 1))).mul (hg' 1 q))

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.contDiffAt_xiPot {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E → Matrix (Fin 2) (Fin 2) ℂ) (b : E → ℂ) (w₀ : E) (hpd : (H w₀).PosDef)
    (hC : ∀ p q, ContDiffAt ℝ 2 (fun w => H w p q) w₀) (hb : ContDiffAt ℝ 2 b w₀) :
    ContDiffAt ℝ 2 (fun w => xiPot (H w) (b w)) w₀ := by
  have hb' : ContDiffAt ℝ 2 (fun w => star (b w)) w₀ := by
    have h := (Complex.conjCLE.contDiff (n := 2)).contDiffAt.comp w₀ hb
    simpa [Function.comp_def] using h
  have h00 := hC 0 0
  have h01 := hC 0 1
  have h10 := hC 1 0
  have h11 := hC 1 1
  have hq : ContDiffAt ℝ 2 (fun w => herm2 (H w) ![1, b w] ![1, b w]) w₀ := by
    simp only [herm2, dotProduct, mulVec, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, star_one, one_mul, mul_one]
    fun_prop
  have hd : ContDiffAt ℝ 2 (fun w => (H w).det) w₀ := by
    simp only [Matrix.det_fin_two]
    fun_prop
  have hqr : ContDiffAt ℝ 2 (fun w => (herm2 (H w) ![1, b w] ![1, b w]).re) w₀ :=
    (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp w₀ hq
  have hdr : ContDiffAt ℝ 2 (fun w => (H w).det.re) w₀ :=
    (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp w₀ hd
  have hv : (![1, b w₀] : Fin 2 → ℂ) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hp1 : 0 < herm2 (H w₀) ![1, b w₀] ![1, b w₀] := by
    exact hpd.dotProduct_mulVec_pos hv
  have hp2 : 0 < (H w₀).det := hpd.det_pos
  simp only [xiPot]
  exact (hqr.log (Complex.pos_iff.1 hp1).1.ne').neg.add (contDiffAt_const.mul (hdr.log (Complex.pos_iff.1 hp2).1.ne'))
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.DenseCoordinateTorusStatement
section
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_coordinate_torus : ∀ n : ℕ, Dense {z : Fin n → ℂ | ∀ i, z i ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.dense_forall_coord_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.DoublingLimitLocalLogarithmStatement
section
open Set Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_limit_local_logarithm : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b₀ : B) (h : B × V → V) (ρ C : ℝ), 0 < ρ → 0 ≤ C → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2) → ∃ L : B × V → V, TendstoUniformlyOn (fun (k : ℕ) (p : B × V) => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k p) L atTop (ball b₀ ρ ×ˢ ball (0 : V) ρ) ∧ ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖L (b, s) - s‖ ≤ 4 * C * ‖s‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit | exact GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsConstAddEquivOfRangeEq
section
open Set

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_const_addEquiv_of_range_eq : ∀ (n g : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Countable Λ] [AddCommGroup Λ'] [Countable Λ'] (B : Set (Fin n → ℂ)), IsOpen B → IsPreconnected B → B.Nonempty → ∀ (P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))) (P' : (Fin n → ℂ) → (Λ' →+ (Fin g → ℂ))), (∀ x, DifferentiableOn ℂ (fun b => P b x) B) → (∀ x, DifferentiableOn ℂ (fun b => P' b x) B) → (∀ b ∈ B, Function.Injective (P b) ∧ Function.Injective (P' b) ∧ (P b).range = (P' b).range) → ∃ T : Λ' ≃+ Λ, ∀ b ∈ B, ∀ x, P' b x = P b (T x) := by
  intro n g Λ Λ' _ _ _ _ B hB hc hne P P' hP hP' h
  have h1 : ∀ x : Λ', ∃ y : Λ, ∀ b ∈ B, P' b x = P b y := fun x =>
    exists_const_of_section_mem_range n g Λ B hB hc hne P (fun b => P' b x) hP (hP' x)
      (fun b hb => by rw [(h b hb).2.2]; exact ⟨x, rfl⟩)
  have h2 : ∀ y : Λ, ∃ x : Λ', ∀ b ∈ B, P b y = P' b x := fun y =>
    exists_const_of_section_mem_range n g Λ' B hB hc hne P' (fun b => P b y) hP' (hP y)
      (fun b hb => by rw [← (h b hb).2.2]; exact ⟨y, rfl⟩)
  choose f hf using h1
  choose k hk using h2
  obtain ⟨b₀, hb₀⟩ := hne
  obtain ⟨hi, hi', -⟩ := h b₀ hb₀
  refine ⟨{ toFun := f, invFun := k, left_inv := ?_, right_inv := ?_, map_add' := ?_ }, ?_⟩
  · intro x
    apply hi'
    rw [← hk _ b₀ hb₀, ← hf _ b₀ hb₀]
  · intro y
    apply hi
    rw [← hf _ b₀ hb₀, ← hk _ b₀ hb₀]
  · intro x x'
    apply hi
    rw [map_add, ← hf _ b₀ hb₀, ← hf _ b₀ hb₀, ← hf _ b₀ hb₀, map_add]
  · intro b hb x
    exact hf x b hb

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHolomorphicNormalFrameStatement
section
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_sine_mobius_transform : ∀ (G g : Matrix (Fin 2) (Fin 2) ℂ), G.PosDef → IsUnit g.det → (gᴴ * G * g).PosDef ∧ (∀ a : ℂ, g 0 0 + g 0 1 * a ≠ 0 → xiPot (gᴴ * G * g) a = xiPot G ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)) - 2 * Real.log ‖g 0 0 + g 0 1 * a‖ + Real.log ‖g.det‖) ∧ ∀ a₀ a₁ : ℂ, g 0 0 + g 0 1 * a₀ ≠ 0 → g 0 0 + g 0 1 * a₁ ≠ 0 → logSin (gᴴ * G * g) a₀ a₁ = logSin G ((g 1 0 + g 1 1 * a₀) / (g 0 0 + g 0 1 * a₀)) ((g 1 0 + g 1 1 * a₁) / (g 0 0 + g 0 1 * a₁)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.xiPot_logSin_change_of_frame | exact GlobalTheory.CompanionTheory.Ar.PB.xiPot_logSin_change_of_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.xiPot_logSin_change_of_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GapEqWeightSubNext
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem toWt_toWtS_homogeneous_coeff_bound : ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ), ∃ Cst : ℝ, (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (M : ℝ), Q.IsHomogeneous n → (toWt Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (toWt Q)| ≤ Cst * M)) ∧ ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (M : ℝ), Q.IsHomogeneous n → (toWtS Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (toWtS Q)| ≤ Cst * M) :=
  @PositivityTheory.Xgp.t_poly_towt_bound

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HarmonicAnnulusMaximumPrincipleStatement
section
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_annulus_maximum_principle : ∀ (h : ℂ → ℝ) (a b : ℝ), 0 < a → a < b → ContinuousOn h {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} → (∀ z : ℂ, a < ‖z‖ → ‖z‖ < b → InnerProductSpace.HarmonicAt h z) → (∀ z : ℂ, (‖z‖ = a ∨ ‖z‖ = b) → h z ≤ 0) → ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → h z ≤ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsOpenFlagDomainNondegenerateMinorsStatement
section
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_domain_unitary_triangular : ∀ (N j : ℕ), j ≤ N → ∀ g : Matrix (Fin N) (Fin N) ℂ, InFlagDomain N j g → ∃ u b : Matrix (Fin N) (Fin N) ℂ, gramOf (sigForm N j) u = diagonal (fun i => ((sigForm N j i : ℝ) : ℂ)) ∧ b.BlockTriangular id ∧ IsUnit b.det ∧ u * g = b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.exists_unitary_translate_flag | exact GlobalTheory.CompanionTheory.Ar.PB.exists_unitary_translate_flag | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.exists_unitary_translate_flag <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalLogarithmHomomorphismStatement
section
open Set Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_logarithm_homomorphism : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (μ : B × V × V → V) (L : B × V → V) (ρ C : ℝ), 0 < ρ → 0 ≤ C → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t))) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, Tendsto (fun k : ℕ => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k (b, s)) atTop (𝓝 (L (b, s)))) → ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, μ (b, s, t) ∈ ball (0 : V) ρ → L (b, μ (b, s, t)) = L (b, s) + L (b, t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit_additive_for_law | exact GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit_additive_for_law | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit_additive_for_law <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetComparableGramBoundStatement
section
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_log_unitary_triangular_invariance : ∀ (N : ℕ) (hd : Fin N → ℝ) (k : ℕ) (g u b : Matrix (Fin N) (Fin N) ℂ), (gramOf hd u = diagonal (fun i => ((hd i : ℝ) : ℂ)) → gramLog hd k (u * g) = gramLog hd k g) ∧ (b.BlockTriangular id → IsUnit b.det → (gramHead hd k g).det ≠ 0 → gramLog hd k (g * b) = gramLog hd k g + ∑ a : Fin N, if (a : ℕ) < k then Real.log ‖b a a‖ else 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.gramLog_inv | exact GlobalTheory.CompanionTheory.Ar.PB.gramLog_inv | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.gramLog_inv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMobiusTransform
section
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gram_logDet_fderiv_norm_le : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E) (a M : ℝ), 0 < a → 0 ≤ M → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → (∀ᶠ y in nhds x, (G y).PosDef ∧ LinearIndependent ℂ (V y)ᵀ) → ((V x)ᴴ * G x * V x - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → (∀ p q, ‖G x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => G y p q) x‖ ≤ M) → (∀ p q, ‖V x p q‖ ≤ M ∧ ‖fderiv ℝ (fun y => V y p q) x‖ ≤ M) → ‖fderiv ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x‖ ≤ 3 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * M ^ 3 / a :=
  @PositivityTheory.Xgp.t_gram_grad

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorRatioRegularOfInverseStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minor_ratio_regular_of_inverse : ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (n r : ℕ) (Fm : Matrix (Fin n) (Fin r) Φ) (U : Matrix (Fin r) (Fin r) Φ) (C : Matrix (Fin r) (Fin n) Φ) (X : Φ), U.BlockTriangular id → (∀ a b, (Fm * U) a b / X ∈ R) → (∀ a b, C a b ∈ R) → (∀ a b, ∑ k, C a k * ((Fm * U) k b / X) = if a = b then 1 else 0) → ∀ (a : ℕ) (ha : a ≤ r) (J₀ : Fin a → Fin n), (Fm.submatrix J₀ (Fin.castLE ha)).det ≠ 0 → (∀ J : Fin a → Fin n, (Fm.submatrix J (Fin.castLE ha)).det / (Fm.submatrix J₀ (Fin.castLE ha)).det ∈ R) → (∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l)) * (Fm.submatrix J₀ (Fin.castLE ha)).det / X ^ a ∈ R ∧ ((∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l)) * (Fm.submatrix J₀ (Fin.castLE ha)).det / X ^ a)⁻¹ ∈ R ∧ (∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l)) * (Fm.submatrix J₀ (Fin.castLE ha)).det / X ^ a ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Metric.UnitMinor.unit_minor | exact GlobalTheory.CompanionTheory.Metric.UnitMinor.unit_minor | (intros; apply GlobalTheory.CompanionTheory.Metric.UnitMinor.unit_minor <;> assumption)
end

