import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0023
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0551
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0553
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0552
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOneAddSq
section
open Ad3 Ad3.S
open Complex MeasureTheory Filter Asymptotics
open scoped FourierTransform Real

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfWeightKernel

lemma slit_add {y : ℝ} (hy : 0 < y) (x : ℝ) : (y : ℂ) + I * x ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left; simpa using hy

lemma slit_sub {y : ℝ} (hy : 0 < y) (x : ℝ) : (y : ℂ) - I * x ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left; simpa using hy

lemma continuous_KK (α β : ℂ) {y : ℝ} (hy : 0 < y) : Continuous (KK α β y) := by
  unfold KK
  refine Continuous.mul ?_ ?_
  · exact Continuous.cpow (by fun_prop) continuous_const (slit_sub hy)
  · exact Continuous.cpow (by fun_prop) continuous_const (slit_add hy)

lemma norm_KK {α β : ℂ} (h : α.im = β.im) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖KK α β y t‖ = (y ^ 2 + t ^ 2) ^ (-(α + β).re / 2) := by
  have hmem := slit_add hy t
  have hconj : (y : ℂ) - I * t = (starRingEnd ℂ) ((y : ℂ) + I * t) := by
    simp [sub_eq_add_neg]
  unfold KK
  rw [hconj]
  generalize hw : (y : ℂ) + I * t = w at hmem
  have hw0 : w ≠ 0 := slitPlane_ne_zero hmem
  have hcw0 : (starRingEnd ℂ) w ≠ 0 := (map_ne_zero _).2 hw0
  have harg : arg w ≠ π := (mem_slitPlane_iff_arg.1 hmem).1
  have hsq : ‖w‖ ^ 2 = y ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, ← hw]; simp; ring
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  rw [norm_mul, norm_cpow_of_ne_zero hcw0, norm_cpow_of_ne_zero hw0, Complex.arg_conj, if_neg harg,
    Complex.norm_conj, ← hsq, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, div_mul_div_comm,
    ← Real.exp_add, ← Real.rpow_add hn]
  have e : -arg w * (-α).im + arg w * (-β).im = 0 := by simp [h]
  rw [e, Real.exp_zero, div_one]
  congr 1
  simp
  ring

lemma cpow_scale {y : ℝ} (hy : 0 < y) {w : ℂ} (hw : w ≠ 0) (r : ℂ) :
    ((y : ℂ) * w) ^ r = (y : ℂ) ^ r * w ^ r := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hy0 hw), cpow_def_of_ne_zero hy0, cpow_def_of_ne_zero hw,
    ← Complex.exp_add, Complex.log_ofReal_mul hy hw, ofReal_log hy.le]
  congr 1
  ring

lemma KK_scale (α β : ℂ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    KK α β y x = (y : ℂ) ^ (-α - β) * KK α β 1 (x / y) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  unfold KK
  have e1 : (y : ℂ) - I * x = y * (((1 : ℝ) : ℂ) - I * ((x / y : ℝ) : ℂ)) := by
    push_cast; field_simp
  have e2 : (y : ℂ) + I * x = y * (((1 : ℝ) : ℂ) + I * ((x / y : ℝ) : ℂ)) := by
    push_cast; field_simp
  rw [e1, e2, cpow_scale hy (slitPlane_ne_zero (slit_sub one_pos _)),
    cpow_scale hy (slitPlane_ne_zero (slit_add one_pos _)), sub_eq_add_neg (-α), cpow_add _ _ hy0]
  ring

lemma fourier_KK (α β : ℂ) {y : ℝ} (hy : 0 < y) (ξ : ℝ) :
    𝓕 (KK α β y) ξ = (y : ℂ) ^ (1 - α - β) * Phi α β (ξ * y) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [Real.fourier_real_eq_integral_exp_smul]
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℂ, G = fun u : ℝ =>
      (y : ℂ) ^ (-α - β) * (KK α β 1 u * ee (-(((ξ * y : ℝ) : ℂ) * u))) := ⟨_, rfl⟩
  have key : ∀ v : ℝ, Complex.exp (((-2 * π * v * ξ : ℝ) : ℂ) * I) • KK α β y v = G (v / y) := by
    intro v
    rw [hG]
    have e : ((-2 * π * v * ξ : ℝ) : ℂ) * I =
        2 * π * I * (-(((ξ * y : ℝ) : ℂ) * ((v / y : ℝ) : ℂ))) := by
      push_cast; field_simp
    simp only [smul_eq_mul]
    rw [KK_scale α β hy v, e, ee]
    ring
  rw [integral_congr_ae (Eventually.of_forall key), Measure.integral_comp_div G y, hG,
    integral_const_mul, abs_of_pos hy, Complex.real_smul,
    show (1 - α - β) = 1 + (-α - β) by ring, cpow_add _ _ hy0, cpow_one]
  unfold Phi
  ring

lemma summable_one_add_sq {σ : ℝ} (hσ : 1 < σ) :
    Summable fun j : ℤ => (1 + (j : ℝ) ^ 2) ^ (-σ / 2) := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow hσ) ?_
  filter_upwards [eventually_cofinite_ne 0] with j hj
  have hj' : (j : ℝ) ≠ 0 := Int.cast_ne_zero.2 hj
  have hpos : 0 < (j : ℝ) ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity)]
  have : |(j : ℝ)| ^ (-σ) = ((j : ℝ) ^ 2) ^ (-σ / 2) := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    push_cast
    ring
  rw [this]
  exact Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)

lemma unif_bound {σ : ℝ} (hσ : 1 < σ) {y : ℝ} (hy : 0 < y) :
    ∃ g : ℤ → ℝ, Summable g ∧ ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ j : ℤ,
      (y ^ 2 + (r - j) ^ 2) ^ (-σ / 2) ≤ g j := by
  obtain ⟨c, hc0, hc1, hc2⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ y ^ 2 / 3 ∧ c ≤ 1 / 2 :=
    ⟨min (y ^ 2 / 3) (1 / 2), lt_min (by positivity) (by norm_num), min_le_left _ _, min_le_right _ _⟩
  refine ⟨fun j => c ^ (-σ / 2) * (1 + (j : ℝ) ^ 2) ^ (-σ / 2),
    (summable_one_add_sq hσ).mul_left _, ?_⟩
  intro r h0 h1 j
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hj : (j : ℝ) ^ 2 ≤ 2 * (r - j) ^ 2 + 2 := by nlinarith [sq_nonneg (2 * r - j)]
  have hle : c * (1 + (j : ℝ) ^ 2) ≤ y ^ 2 + (r - j) ^ 2 := by
    have h3 : c * (1 + (j : ℝ) ^ 2) ≤ c * (3 + 2 * (r - j) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hc0.le
    nlinarith [mul_le_mul_of_nonneg_right hc2 (sq_nonneg (r - (j : ℝ)))]
  show _ ≤ c ^ (-σ / 2) * (1 + (j : ℝ) ^ 2) ^ (-σ / 2)
  rw [← Real.mul_rpow hc0.le (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)

lemma decay_KK {α β : ℂ} (h : α.im = β.im) (hσ : 1 < (α + β).re) {y : ℝ} (hy : 0 < y) :
    KK α β y =O[cocompact ℝ] fun x : ℝ => |x| ^ (-(α + β).re) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with x hx
  have hx0 : x ≠ 0 := hx
  have hpos : 0 < x ^ 2 := by positivity
  have e : |x| ^ (-(α + β).re) = (x ^ 2) ^ (-(α + β).re / 2) := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    push_cast
    ring
  rw [one_mul, Real.norm_of_nonneg (by positivity), norm_KK h hy, e]
  exact Real.rpow_le_rpow_of_nonpos hpos (by nlinarith [sq_nonneg y]) (by linarith)

theorem poisson_kernel : W0 → W2 → P1 := by
  intro _ hW2 s α β a b y hα hβ hσ hy
  have him : α.im = β.im := by simp [hα, hβ]
  obtain ⟨g, hg, hgb⟩ := unif_bound hσ hy
  have hsum : ∀ t : ℝ, (Summable fun j : ℤ => ‖KK α β y (t - j)‖) ∧
      ∑' j : ℤ, ‖KK α β y (t - j)‖ ≤ ∑' j, g j := by
    intro t
    have hle : ∀ j : ℤ, ‖KK α β y (t - j)‖ ≤ g (j - ⌊t⌋) := by
      intro j
      have e : t - j = Int.fract t - ((j - ⌊t⌋ : ℤ) : ℝ) := by
        have := Int.floor_add_fract t
        push_cast
        linarith
      rw [norm_KK him hy, e]
      exact hgb _ (Int.fract_nonneg t) (Int.fract_lt_one t).le _
    have hgs : Summable fun j : ℤ => g (j - ⌊t⌋) := (Equiv.subRight ⌊t⌋).summable_iff.2 hg
    refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hgs, ?_⟩
    calc ∑' j : ℤ, ‖KK α β y (t - j)‖ ≤ ∑' j : ℤ, g (j - ⌊t⌋) :=
          Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hgs) hgs
      _ = ∑' j, g j := (Equiv.subRight ⌊t⌋).tsum_eq g
  have hPhi : Summable fun n : ℤ => ‖Phi α β (n * y)‖ := by
    obtain ⟨Ψ, -, -, h3, h4⟩ := hW2 2 a b
    have hre : (α + β).re = s.re + a + b := by simp [hα, hβ]; ring
    have hs : s ∈ HP (1 - a - b) := by
      show 1 - a - b < s.re
      linarith
    obtain ⟨C, hC⟩ := h4 1 s.re one_pos
    have hsr : 1 - a - b - ((2 : ℕ) : ℝ) + 1 ≤ s.re := by
      have : 1 - a - b < s.re := hs
      push_cast
      linarith
    refine Summable.of_norm_bounded_eventually
      ((Real.summable_abs_int_rpow one_lt_two).mul_left (C * Real.exp (C * s.im ^ 2) / y ^ 2)) ?_
    filter_upwards [eventually_cofinite_ne 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn
    have hξ : (n : ℝ) * y ≠ 0 := mul_ne_zero hn' hy.ne'
    have hb := hC s (n * y) hξ hsr le_rfl
    rw [h3 s hs _ hξ, ← hα, ← hβ] at hb
    rw [norm_norm]
    refine hb.trans (le_of_eq ?_)
    rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, abs_mul, abs_of_pos hy, mul_pow]
    have : |(n : ℝ)| ^ 2 ≠ 0 := by positivity
    field_simp
  have hF : ∀ n : ℤ, 𝓕 (KK α β y) (n : ℝ) = (y : ℂ) ^ (1 - α - β) * Phi α β (n * y) :=
    fun n => fourier_KK α β hy n
  have hFs : Summable fun n : ℤ => 𝓕 (KK α β y) (n : ℝ) := by
    simp_rw [hF]
    exact hPhi.of_norm.mul_left _
  refine ⟨⟨∑' j, g j, hsum⟩, hPhi, fun t => ?_⟩
  have P := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable (continuous_KK α β hy) hσ
    (decay_KK him hσ hy) hFs t
  calc ∑' j : ℤ, KK α β y (t - j) = ∑' j : ℤ, KK α β y (t + j) := by
        rw [← (Equiv.neg ℤ).tsum_eq (fun j : ℤ => KK α β y (t + j))]
        refine tsum_congr fun j => ?_
        simp [sub_eq_add_neg]
    _ = ∑' n : ℤ, 𝓕 (KK α β y) (n : ℝ) * fourier n (t : UnitAddCircle) := P
    _ = _ := tsum_congr fun n => by
        rw [hF, fourier_coe_apply, ee]
        congr 2
        push_cast
        ring

end GlobalTheory.CompanionTheory.HalfWeightKernel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOverLatticeQuotientLocallyConstantStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_over_lattice_quotient_locally_constant : ∀ (G H : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] (ν : Measure G) [ν.IsAddHaarMeasure] (U : AddSubgroup G),
    IsOpen (U : Set G) → IsCompact (U : Set G) → ∀ ι : H →+ G, (∀ g, ∃ h, g - ι h ∈ U) →
    ∀ f : G → ℂ, (∀ g, ∀ u ∈ U, f (g + u) = f g) →
    Summable (fun x : H ⧸ U.comap ι => ‖f (ι (Quotient.out x))‖) → Integrable f ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_of_summable_quotient_periodic | exact GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_of_summable_quotient_periodic | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_of_summable_quotient_periodic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummablePeriodicBoundByDenominator
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Compare

theorem summable_comp_of_injective_prod {X Y Q : Type*} [Finite Q] {d : Y → ℝ}
    (hd : ∀ y, 0 ≤ d y) (hs : Summable d) (y : X → Y) (q : X → Q)
    (hinj : Function.Injective fun x => (y x, q x)) : Summable fun x => d (y x) := by
  have h1 : Summable (fun p : Y × Q => d p.1 * (fun _ : Q => (1 : ℝ)) p.2) :=
    Summable.mul_of_nonneg hs (Summable.of_finite) hd (fun _ => zero_le_one)
  have h2 := h1.comp_injective hinj
  simpa [Function.comp_def] using h2

theorem finite_quot_nsmul {M : Type*} [AddCommGroup M] [Module.Finite ℤ M] {τ : ℕ} (hτ : 0 < τ) :
    Finite (M ⧸ (nsmulAddMonoidHom τ : M →+ M).range) := by
  haveI : Module.Finite ℤ (M ⧸ (nsmulAddMonoidHom τ : M →+ M).range) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' _).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H m =>
    refine ⟨⟨(τ : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hτ.ne')⟩, ?_⟩
    have : ((τ : ℤ) • (m : M ⧸ (nsmulAddMonoidHom τ : M →+ M).range))
        = ((τ • m : M) : M ⧸ (nsmulAddMonoidHom τ : M →+ M).range) := by
      rw [natCast_zsmul]; rfl
    show ((τ : ℤ) • (m : M ⧸ (nsmulAddMonoidHom τ : M →+ M).range)) = 0
    rw [this, QuotientAddGroup.eq_zero_iff]
    exact ⟨m, rfl⟩

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]

theorem mem_hermO_iff (σ : E →ₐ[F] E) (n : ℕ) (c : hermE σ n) :
    c ∈ hermO σ n ↔ ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c.1 a b := Iff.rfl

def toInt (σ : E →ₐ[F] E) (n : ℕ) : hermO σ n →+ Matrix (Fin n) (Fin n) (𝓞 E) where
  toFun c := Matrix.of fun a b => Classical.choose ((mem_hermO_iff σ n c.1).1 c.2 a b)
  map_zero' := by
    ext a b
    have h := Classical.choose_spec ((mem_hermO_iff σ n (0 : hermO σ n).1).1 (0 : hermO σ n).2 a b)
    refine Eq.trans h ?_
    change _ = algebraMap (𝓞 E) E 0
    rw [map_zero]
    rfl
  map_add' := by
    intro c d
    ext a b
    have h1 := Classical.choose_spec ((mem_hermO_iff σ n (c + d).1).1 (c + d).2 a b)
    have h2 := Classical.choose_spec ((mem_hermO_iff σ n c.1).1 c.2 a b)
    have h3 := Classical.choose_spec ((mem_hermO_iff σ n d.1).1 d.2 a b)
    refine Eq.trans h1 ?_
    change _ = algebraMap (𝓞 E) E (_ + _)
    rw [map_add]
    exact Eq.trans rfl (Eq.symm (Eq.trans (congrArg₂ (· + ·) h2 h3) rfl))

theorem algebraMap_toInt (σ : E →ₐ[F] E) (n : ℕ) (c : hermO σ n) (a b : Fin n) :
    algebraMap (𝓞 E) E (toInt σ n c a b) = c.1.1 a b :=
  Classical.choose_spec ((mem_hermO_iff σ n c.1).1 c.2 a b)

theorem toInt_injective (σ : E →ₐ[F] E) (n : ℕ) : Function.Injective (toInt σ n) := by
  intro c d h
  apply Subtype.ext
  apply Subtype.ext
  ext a b
  rw [← algebraMap_toInt σ n c a b, ← algebraMap_toInt σ n d a b, h]

theorem finite_hermO (σ : E →ₐ[F] E) (n : ℕ) : Module.Finite ℤ (hermO σ n) :=
  Module.Finite.of_injective (toInt σ n).toIntLinearMap (toInt_injective σ n)

theorem Kc_le_add {n : ℕ} (c l : Matrix (Fin n) (Fin n) E)
    (hl : ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = l a b) : Kc c ≤ Kc (c + l) := by
  intro y hy i
  obtain ⟨o, ho⟩ := hy i
  choose m hm using hl
  refine ⟨o + ∑ j, m i j * y j, ?_⟩
  rw [Matrix.add_mulVec, Pi.add_apply, map_add, ho]
  congr 1
  simp [Matrix.mulVec, dotProduct, hm]

theorem delta_add {n : ℕ} (c l : Matrix (Fin n) (Fin n) E)
    (hl : ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = l a b) : delta (c + l) = delta c := by
  have h1 := Kc_le_add c l hl
  have h2 := Kc_le_add (c + l) (-l) (fun a b => by
    obtain ⟨o, ho⟩ := hl a b
    exact ⟨-o, by simp [ho]⟩)
  rw [add_neg_cancel_right] at h2
  unfold delta
  rw [le_antisymm h2 h1]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Compare

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Compare in

theorem summable_quot_of_le_delta_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (Λ : AddSubgroup (hermE σ n)) (t : F), t ≠ 0 → ∀ τ : ℕ, 0 < τ →
    (∀ c ∈ hermO σ n, ((τ : F) / t) • c ∈ Λ) →
    ∀ g : hermE σ n → ℝ, (∀ c, 0 ≤ g c) → (∀ c, ∀ l ∈ Λ, g (c + l) = g c) →
    ∀ C s : ℝ, (∀ c, g c ≤ C * (delta (t • c).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ Λ => g (Quotient.out x)) := by
  intro F E _ _ _ _ _ σ n Λ t ht τ hτ hΛ g hg hper C s hb hsum
  haveI : Module.Finite ℤ (hermO σ n) := finite_hermO σ n
  haveI := finite_quot_nsmul (M := hermO σ n) hτ
  let y : hermE σ n ⧸ Λ → hermE σ n ⧸ hermO σ n :=
    fun x => QuotientAddGroup.mk (t • Quotient.out x)
  have hmem : ∀ x, t • Quotient.out x - Quotient.out (y x) ∈ hermO σ n := by
    intro x
    have h : (QuotientAddGroup.mk (Quotient.out (y x)) : hermE σ n ⧸ hermO σ n)
        = QuotientAddGroup.mk (t • Quotient.out x) := QuotientAddGroup.out_eq' (y x)
    have := QuotientAddGroup.eq.1 h
    rwa [neg_add_eq_sub] at this
  let w : hermE σ n ⧸ Λ → hermO σ n := fun x => ⟨_, hmem x⟩
  let q : hermE σ n ⧸ Λ → hermO σ n ⧸ (nsmulAddMonoidHom τ : hermO σ n →+ hermO σ n).range :=
    fun x => QuotientAddGroup.mk (w x)
  have hinj : Function.Injective fun x => (y x, q x) := by
    intro x x' h
    have hy : y x = y x' := congrArg Prod.fst h
    have hq : q x = q x' := congrArg Prod.snd h
    obtain ⟨c, hc⟩ := QuotientAddGroup.eq.1 hq
    have hc' : τ • (c.1 : hermE σ n) = t • (Quotient.out x' - Quotient.out x) := by
      have := congrArg Subtype.val hc
      simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg,
        AddSubgroup.coe_nsmul] at this
      rw [this]
      simp only [w, hy, smul_sub]
      abel
    have hd : Quotient.out x' - Quotient.out x = ((τ : F) / t) • (c.1 : hermE σ n) := by
      rw [div_eq_inv_mul, mul_smul, Nat.cast_smul_eq_nsmul F τ, hc', smul_smul,
        inv_mul_cancel₀ ht, one_smul]
    have hmemΛ : Quotient.out x' - Quotient.out x ∈ Λ := hd ▸ hΛ _ c.2
    rw [← QuotientAddGroup.out_eq' x, ← QuotientAddGroup.out_eq' x']
    apply QuotientAddGroup.eq.2
    rwa [neg_add_eq_sub]
  have hdnn : ∀ z : hermE σ n ⧸ hermO σ n,
      0 ≤ (delta (Quotient.out z).1 : ℝ) ^ (-s) := fun z => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hs := summable_comp_of_injective_prod hdnn hsum y q hinj
  refine Summable.of_nonneg_of_le (fun x => hg _) (fun x => ?_) (hs.mul_left |C|)
  have hdelta : delta (t • Quotient.out x).1 = delta (Quotient.out (y x)).1 := by
    have hl : ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (w x).1.1 a b := (w x).2
    rw [← delta_add (Quotient.out (y x)).1 (w x).1.1 hl]
    congr 1
    simp [w]
  refine (hb _).trans ?_
  rw [hdelta]
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (hdnn _)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperateMultiplierPreservesSchwartzStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.temperate_multiplier_preserves_schwartz : ∀ (D : D7) (θ : InfFam D) (m n : ℕ) (q : (D.what₂.Tau → Fin m → Fin n → ℂ) → ℂ), q.HasTemperateGrowth → ∀ φ : Mx D m n → ℂ, φ ∈ schwartzA θ m n → (fun x => q (fun τ i j => compAt θ τ x i j) * φ x) ∈ schwartzA θ m n := by
  first | exact @GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA | exact GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA | (intros; apply GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusConjugateUnipotentBoundedStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_conjugate_unipotent_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Q : Set (GAd σ J)) (c : ℝ), IsCompact Q → 0 < c → ∀ s : Fin r, ∃ M : ℝ, 0 ≤ M ∧ ∀ m ∈ Q, m ∈ unipRad σ J (pre X s) → ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n), ‖(archMat σ J τ (projArch σ J w (a⁻¹ * m * a)) - 1) i j‖ ≤ M / ratio t s := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.torus_contracts_unipRad | exact GlobalTheory.CompanionTheory.RapidDecay.torus_contracts_unipRad | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.torus_contracts_unipRad <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusSiegelHeightLowerBoundStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_siegel_height_lower_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ a, IsTorus σ J X Y a → ∀ (Ω C : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minPar σ J X → IsCompact C → ∃ P : ℝ, 0 < P ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 → Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0)) ≤ P * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.FirstLower.exp_le_hgt | exact GlobalTheory.CompanionTheory.RedCov.FirstLower.exp_le_hgt | (intros; apply GlobalTheory.CompanionTheory.RedCov.FirstLower.exp_le_hgt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceGramUnitScaling
section
noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree.Dilate

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem gramR_dilate {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (u : R ⊗[F] E)
    (X : Fin 1 → Fin M → R ⊗[F] E) :
    gramR R σ J (fun p k => u * X p k) 0 0 = (u * sigR R σ u) * gramR R σ J X 0 0 := by
  simp only [gramR, HeckeCharacterZeroLocus.SiegelWeilU.hR, hform, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem half_trace_dilate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (u : Fv F v ⊗[F] E) (X : Fin 1 → Fin M → Fv F v ⊗[F] E), (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) X) = Algebra.norm (Fv F v) u * (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) X := by
  intro F E _ _ _ _ _ σ hσ M J hJ v u X
  beta_reduce
  have hX := GlobalTheory.CompanionTheory.SW.FibreRatio.gram_entry (Fv F v) hσ hJ X
  set r := algebraMap F (Fv F v) (1 / 2) *
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) with hr
  have hY : gramR (Fv F v) σ J (fun p k => u * X p k) 0 0 =
      (Algebra.norm (Fv F v) u * r) ⊗ₜ[F] (1 : E) := by
    have hN : algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.norm (Fv F v) u) = u * sigR (Fv F v) σ u :=
      GlobalTheory.Doubling.algebraMap_norm_eq hσ u
    rw [gramR_dilate, ← hN, hX,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    simp
  rw [hY]
  exact GlobalTheory.CompanionTheory.SW.FibreRatio.half_trace_tmul (Fv F v) hσ _

end GlobalTheory.CompanionTheory.AvgFree.Dilate
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCentralizerCompactPartStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_centralizer_compact_part : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (θ : G →* G), Continuous θ → ∀ (K I C : Subgroup G) (δ : G), IsCompact (K : Set G) → IsOpen (I : Set G) → IsCompact (C : Set G) → cptPart (twCent θ δ) = twCent θ δ ⊓ C → ∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧ (twCent θ δ ⊓ I.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.CentOk.centraliser_hyps | exact GlobalTheory.CompanionTheory.CentOk.centraliser_hyps | (intros; apply GlobalTheory.CompanionTheory.CentOk.centraliser_hyps <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSchwartzFunctionIntegrableStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_schwartz_function_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), dx.IsAddHaarMeasure →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
  ∀ b : HermR (AF F) σ n, Integrable (fun X => Φ X * ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X)))) dx := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.integrable_mul_phase | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.integrable_mul_phase | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.integrable_mul_phase <;> assumption)
end

