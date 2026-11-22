import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0180
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducesOfDetEvMEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0164
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0103
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0176
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSaturation
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_sat : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) → (∃ P : Polynomial T.K, P ≠ 0 ∧ P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) = 0) → ∃ f : T.K, T.an f * (b : Mero) = (a : Mero) := by
  intro Ω _ _ _ ε T a b M hM ha hb hb0 hinv ⟨P, hP, hPe⟩
  obtain ⟨_, hMD, hAE, _, hmemHs⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  obtain ⟨hNT, hid, hunit⟩ := GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units
  obtain ⟨hmapsto, _, _, hmobSL, hmobD, _⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  obtain ⟨p, u, hu, hpn, hp⟩ := GlobalTheory.T.modularFunctionFractionField_clear_denominators Ω ε T P hP
  set n := P.natDegree with hn
  have hR : ∀ i, InR ε.range (p i : ℍ → ℂ) := fun i => ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 _).1 (p i).2
  have hpD : ∀ i, DifferentiableOn ℂ (up (p i : ℍ → ℂ)) Hs := fun i => (hMD _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ (hR i))

  have hup : ∀ (g : ℂ → ℂ) (z : ℂ), z ∈ Hs → up (fun τ : ℍ => g τ) z = g z := by
    intro g z hz
    simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
  have hupT : ∀ (f : ℍ → ℂ) (τ : ℍ), up f τ = f τ := by
    intro f τ
    simp [up]

  have hxb : (((a / b : ℂ → ℂ)) : Mero) * (b : Mero) = (a : Mero) := by
    rw [← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
    filter_upwards [(hunit b hb hb0).1] with z hz
    simp [div_mul_cancel₀ _ hz]

  have hsum : ∑ i ∈ Finset.range (n + 1), T.an (T.io (p i)) * (((a / b : ℂ → ℂ)) : Mero) ^ i = 0 := by
    calc _ = T.an u * P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) := by
          rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hp i, map_mul, mul_assoc]
      _ = 0 := by rw [hPe, mul_zero]
  set F : ℂ → ℂ := fun z => ∑ i ∈ Finset.range (n + 1), up (p i : ℍ → ℂ) z * a z ^ i * b z ^ (n - i) with hF
  have e2 : F = ∑ i ∈ Finset.range (n + 1), up (p i : ℍ → ℂ) * a ^ i * b ^ (n - i) := by
    funext z; simp [hF, Finset.sum_apply]
  have hFg : (F : Mero) = 0 := by
    have e1 : (F : Mero) = Filter.Germ.coeRingHom _ F := rfl
    rw [e1, e2, map_sum]
    change ∑ i ∈ _, ((up (p i : ℍ → ℂ) * a ^ i * b ^ (n - i) : ℂ → ℂ) : Mero) = _
    simp only [Filter.Germ.coe_mul, Filter.Germ.coe_pow]
    calc _ = (b : Mero) ^ n * ∑ i ∈ Finset.range (n + 1), T.an (T.io (p i)) * (((a / b : ℂ → ℂ)) : Mero) ^ i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [T.an_io, ← hxb]
          show (up (p i : ℍ → ℂ) : Mero) * _ * _ = _ * ((up (p i : ℍ → ℂ) : Mero) * _)
          rw [mul_pow, mul_assoc, mul_assoc, ← pow_mul_pow_sub (b : Mero) hin]
          ring
      _ = 0 := by rw [hsum, mul_zero]
  have hFD : DifferentiableOn ℂ F Hs := by
    rw [e2]
    refine DifferentiableOn.sum fun i _ => ?_
    exact ((hpD i).mul (ha.pow i)).mul (hb.pow (n - i))
  have hF0 : ∀ z ∈ Hs, F z = 0 := by
    have := hid F (fun _ => 0) hFD (differentiableOn_const 0) (by rw [hFg]; rfl)
    exact this

  have haM : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => a τ) := (hMD _).2 (ha.congr fun z hz => hup a z hz)
  have hbM : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => b τ) := (hMD _).2 (hb.congr fun z hz => hup b z hz)
  have hbne : (fun τ : ℍ => b τ) ≠ 0 := by
    intro h0
    apply hb0
    have : (b : Mero) = ((0 : ℂ → ℂ) : Mero) := hAE b 0 fun z hz => by
      simpa using congrFun h0 ⟨z, hz⟩
    rw [this]; rfl
  have hinvT : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a ((γ • τ : ℍ) : ℂ) * b τ = a τ * b ((γ • τ : ℍ) : ℂ) := by
    intro γ hγ τ
    have hmD : DifferentiableOn ℂ (mob (ofSL γ)) Hs := hmobD _
    have hmap : Set.MapsTo (mob (ofSL γ)) Hs Hs := fun z hz => hmapsto _ z hz
    have h1 : DifferentiableOn ℂ (fun z => a (mob (ofSL γ) z) * b z) Hs := (ha.comp hmD hmap).mul hb
    have h2 : DifferentiableOn ℂ (fun z => a z * b (mob (ofSL γ) z)) Hs := ha.mul (hb.comp hmD hmap)
    have := hid _ _ h1 h2 (hinv γ hγ) τ (hmemHs τ)
    simpa [hmobSL] using this
  have hpn' : (p n : ℍ → ℂ) ≠ 0 := by
    intro h0; apply hpn; ext1; exact h0
  have hsumT : ∀ τ : ℍ, ∑ i ∈ Finset.range (n + 1), (p i : ℍ → ℂ) τ * (fun τ : ℍ => a τ) τ ^ i * (fun τ : ℍ => b τ) τ ^ (n - i) = 0 := by
    intro τ
    have := hF0 τ (hmemHs τ)
    simpa [hF, hupT] using this
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (R := ℚ)
  obtain ⟨h, hhR, hh⟩ := GlobalTheory.T.saturation_levelFunctions_integralRelation Ω ε M n (fun τ : ℍ => a τ) (fun τ : ℍ => b τ) (fun i => (p i : ℍ → ℂ)) hM haM hbM hbne
    hinvT hR hpn' hsumT
  let hr : ring ε.range := ⟨h, mem_ring_of_inR hhR⟩
  have hio0 : T.io (p n) ≠ 0 := by
    intro h0; apply hpn; exact T.io_inj (by rw [h0, map_zero])
  refine ⟨T.io hr / T.io (p n), ?_⟩
  have hg0 : (up (p n : ℍ → ℂ) : Mero) ≠ 0 := by
    intro h0
    have hinj : Function.Injective T.an := T.an.injective
    apply hio0; apply hinj; rw [map_zero, T.an_io]; exact h0
  have hU : IsUnit (up (p n : ℍ → ℂ) : Mero) := (hunit _ (hpD n) hg0).2
  have hrel : (up (p n : ℍ → ℂ) : Mero) * (a : Mero) = (up h : Mero) * (b : Mero) := by
    rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul]
    refine hAE _ _ fun z hz => ?_
    have e := hh ⟨z, hz⟩
    simp only [Pi.mul_apply]
    have q1 : up (p n : ℍ → ℂ) z = (p n : ℍ → ℂ) ⟨z, hz⟩ := by
      simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    have q2 : up h z = h ⟨z, hz⟩ := by
      simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    rw [q1, q2]; simpa using e
  have hf : T.an (T.io hr / T.io (p n)) * (up (p n : ℍ → ℂ) : Mero) = (up h : Mero) := by
    have : T.io hr / T.io (p n) * T.io (p n) = T.io hr := div_mul_cancel₀ _ hio0
    have := congrArg T.an this
    rw [map_mul, T.an_io, T.an_io] at this
    exact this
  apply hU.mul_left_cancel
  rw [hrel, ← hf]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinMeanSquareCuspForm
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.MeanSquareEstimates

theorem key (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ) (hc : CF k L χ h) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖qs h τ‖ ^ 2 * τ.im ^ k ≤ C) (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => ‖h n‖ ^ 2 * Real.exp (-4 * π * n * y)) ∧
      ∑' n : ℕ, ‖h n‖ ^ 2 * Real.exp (-4 * π * n * y) ≤ C / y ^ k := by
  have hp := GlobalTheory.T.hasSum_parseval_qExpansion_horizontal_line h h y hc.1.1 hc.1.1 hy
  set I := ∫ x in (0 : ℝ)..1, conj (qs h (ofComplex (x + y * Complex.I))) * qs h (ofComplex (x + y * Complex.I))
  have hr := Complex.hasSum_re hp
  have e : (fun n : ℕ => (conj (h n) * h n * ((Real.exp (-4 * π * n * y) : ℝ) : ℂ)).re) =
      fun n : ℕ => ‖h n‖ ^ 2 * Real.exp (-4 * π * n * y) := by
    funext n
    rw [Complex.conj_mul']
    norm_cast
  rw [e] at hr
  refine ⟨hr.summable, ?_⟩
  rw [hr.tsum_eq]
  have hb : ∀ x ∈ Set.uIoc (0 : ℝ) 1, ‖conj (qs h (ofComplex (x + y * Complex.I))) * qs h (ofComplex (x + y * Complex.I))‖ ≤ C / y ^ k := by
    intro x _
    have him : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
    rw [ofComplex_apply_of_im_pos him, Complex.conj_mul']
    have h1 := hC ⟨(x : ℂ) + y * Complex.I, him⟩
    have h2 : (⟨(x : ℂ) + y * Complex.I, him⟩ : ℍ).im = y := by simp [UpperHalfPlane.im]
    rw [h2] at h1
    rw [le_div_iff₀ (by positivity)]
    simpa using h1
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  calc I.re ≤ ‖I‖ := Complex.re_le_norm I
    _ ≤ C / y ^ k * |1 - 0| := this
    _ = C / y ^ k := by simp

theorem key2 (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ) (hc : CF k L χ h) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖qs h τ‖ ^ 2 * τ.im ^ k ≤ C) (t : ℝ) (ht : 0 < t) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖h n‖ ^ 2 * Real.exp (-(n : ℝ) * t) ≤ C * (4 * π) ^ k / t ^ k := by
  have hy : 0 < t / (4 * π) := by positivity
  obtain ⟨hs, hb⟩ := key k L χ h hc C hC _ hy
  have e : ∀ n : ℕ, -4 * π * n * (t / (4 * π)) = -(n : ℝ) * t := fun n => by field_simp
  simp only [e] at hs hb
  have e2 : C / (t / (4 * π)) ^ k = C * (4 * π) ^ k / t ^ k := by rw [div_pow]; field_simp
  rw [e2] at hb
  exact (hs.sum_le_tsum _ (fun n _ => by positivity)).trans hb

theorem blk (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (a0 : a 0 = 0) (k : ℕ) (D : ℝ)
    (hD : ∀ t : ℝ, 0 < t → ∀ N : ℕ, ∑ n ∈ Finset.range N, a n * Real.exp (-(n : ℝ) * t) ≤ D / t ^ k)
    (s : ℝ) (hs : 0 < s) (N : ℕ) :
    ∑ n ∈ Finset.range N, a n / (n : ℝ) ^ ((k : ℝ) + s) ≤ Real.exp 2 * D / (1 - (2 : ℝ) ^ (-s)) := by
  set x : ℝ := (2 : ℝ) ^ (-s) with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hD0 : 0 ≤ D := by
    have := hD 1 one_pos 0
    simpa using this
  set G : ℕ → ℕ → ℝ := fun j n => Real.exp 2 * (x ^ j / ((2 : ℝ) ^ j) ^ k) * (a n * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹)) with hG
  have G0 : ∀ j n, 0 ≤ G j n := fun j n => by have := ha n; positivity
  have pt : ∀ n ∈ Finset.range N, a n / (n : ℝ) ^ ((k : ℝ) + s) ≤ ∑ j ∈ Finset.range N, G j n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [a0, zero_div]; exact Finset.sum_nonneg fun j _ => G0 j 0
    set j := Nat.log 2 n
    have hj1 : 2 ^ j ≤ n := Nat.pow_log_le_self 2 hn0.ne'
    have hj2 : n < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have hjN : j < N := by
      have : j < 2 ^ j := Nat.lt_two_pow_self
      have := Finset.mem_range.mp hn
      omega
    refine le_trans ?_ (Finset.single_le_sum (fun i _ => G0 i n) (Finset.mem_range.mpr hjN))
    have npos : (0 : ℝ) < n := by exact_mod_cast hn0
    have h2j : ((2 : ℝ) ^ j) ≤ n := by exact_mod_cast hj1
    have h2j' : (n : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
      have : (n : ℝ) < ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hj2
      push_cast at this; rw [pow_succ] at this; linarith
    have P : ((2 : ℝ) ^ j) ^ k * ((2 : ℝ) ^ j) ^ s ≤ (n : ℝ) ^ k * (n : ℝ) ^ s := by gcongr
    have E : 1 ≤ Real.exp 2 * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹) := by
      rw [← Real.exp_add]; apply Real.one_le_exp
      have : (n : ℝ) * ((2 : ℝ) ^ j)⁻¹ ≤ 2 := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith
      linarith
    have hxj : x ^ j = (((2 : ℝ) ^ j) ^ s)⁻¹ := by
      rw [hxdef, Real.rpow_neg (by norm_num), inv_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
    have L : (n : ℝ) ^ ((k : ℝ) + s) = (n : ℝ) ^ k * (n : ℝ) ^ s := by
      rw [Real.rpow_add npos, Real.rpow_natCast]
    have R : G j n = a n * (Real.exp 2 * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹)) / (((2 : ℝ) ^ j) ^ k * ((2 : ℝ) ^ j) ^ s) := by
      rw [hG]; dsimp only; rw [hxj]; field_simp
    rw [L, R]
    have an := ha n
    calc a n / ((n : ℝ) ^ k * (n : ℝ) ^ s) ≤ a n / (((2 : ℝ) ^ j) ^ k * ((2 : ℝ) ^ j) ^ s) := by
          gcongr
      _ ≤ _ := by gcongr; exact le_mul_of_one_le_right an E
  calc ∑ n ∈ Finset.range N, a n / (n : ℝ) ^ ((k : ℝ) + s) ≤ ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range N, G j n :=
        Finset.sum_le_sum pt
    _ = ∑ j ∈ Finset.range N, ∑ n ∈ Finset.range N, G j n := Finset.sum_comm
    _ = ∑ j ∈ Finset.range N, Real.exp 2 * (x ^ j / ((2 : ℝ) ^ j) ^ k) *
          ∑ n ∈ Finset.range N, a n * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹) := by
        simp only [hG, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range N, Real.exp 2 * (x ^ j / ((2 : ℝ) ^ j) ^ k) * (D / (((2 : ℝ) ^ j)⁻¹) ^ k) := by
        gcongr with j _
        exact hD _ (by positivity) N
    _ = ∑ j ∈ Finset.range N, Real.exp 2 * D * x ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [inv_pow]; field_simp
    _ = Real.exp 2 * D * ∑ j ∈ Finset.range N, x ^ j := by rw [Finset.mul_sum]
    _ ≤ Real.exp 2 * D * (x ^ 0 / (1 - x)) := by
        gcongr
        rw [Finset.range_eq_Ico]; exact geom_sum_Ico_le_of_lt_one hx0 hx1
    _ = Real.exp 2 * D / (1 - x) := by rw [pow_zero]; ring

theorem geo (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) : s / 3 ≤ 1 - (2 : ℝ) ^ (-s) := by
  have L := Real.log_two_gt_d9
  have h1 : 1 + s * Real.log 2 ≤ (2 : ℝ) ^ s := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
    linarith [Real.add_one_le_exp (Real.log 2 * s)]
  have hp : 0 < 1 + s * Real.log 2 := by nlinarith
  have h2 : (2 : ℝ) ^ (-s) ≤ 1 / (1 + s * Real.log 2) := by
    rw [Real.rpow_neg (by norm_num), one_div]
    exact inv_anti₀ hp h1
  have h3 : 1 / (1 + s * Real.log 2) ≤ 1 - s / 3 := by
    rw [div_le_iff₀ hp]
    have q : 0 ≤ Real.log 2 - 1 / 3 - s * Real.log 2 / 3 := by nlinarith
    nlinarith [mul_nonneg hs.le q]
  linarith

end GlobalTheory.MeanSquareEstimates

namespace GlobalTheory

open GlobalTheory.MeanSquareEstimates in

theorem rankin_mean_square : ∀ (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ), 1 ≤ k → CF k L χ h → h 0 = 0 ∧ (∃ C : ℝ, ∀ n : ℕ, ‖h n‖ ^ 2 ≤ C * (n : ℝ) ^ k) ∧ (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s)) ∧ ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ C := by
  intro k L χ h hk hc
  obtain ⟨C, hC⟩ := hc.2
  have C0 : 0 ≤ C := le_trans (by positivity) (hC UpperHalfPlane.I)
  set D := C * (4 * π) ^ k with hDdef
  have D0 : 0 ≤ D := by positivity
  have K := key2 k L χ h hc C hC
  have K1 : ∀ t : ℝ, 0 < t → ∀ n : ℕ, ‖h n‖ ^ 2 * Real.exp (-(n : ℝ) * t) ≤ D / t ^ k := by
    intro t ht n
    refine le_trans ?_ (K t ht (n + 1))
    exact Finset.single_le_sum (f := fun m : ℕ => ‖h m‖ ^ 2 * Real.exp (-(m : ℝ) * t)) (fun m _ => by positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  have h0 : h 0 = 0 := by
    have lim : Tendsto (fun t : ℝ => D / t ^ k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega))
    have b : ‖h 0‖ ^ 2 ≤ 0 := by
      refine ge_of_tendsto lim ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      simpa using K1 t ht 0
    have : ‖h 0‖ = 0 := by nlinarith [norm_nonneg (h 0)]
    exact norm_eq_zero.mp this
  have B : ∀ s : ℝ, 0 < s → ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ Real.exp 2 * D / (1 - (2 : ℝ) ^ (-s)) :=
    fun s hs N => blk (fun n => ‖h n‖ ^ 2) (fun n => by positivity) (by simp [h0]) k D K s hs N
  have nn : ∀ s : ℝ, ∀ n : ℕ, 0 ≤ ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) := fun s n => by positivity
  refine ⟨h0, ⟨D * Real.exp 1, fun n => ?_⟩, fun s hs => summable_of_sum_range_le (nn s) (B s hs), ⟨3 * (Real.exp 2 * D), fun s hs hs1 => ?_⟩⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [h0, zero_pow (by omega : k ≠ 0)]
    have npos : (0 : ℝ) < n := by exact_mod_cast hn
    have := K1 (n : ℝ)⁻¹ (by positivity) n
    rw [neg_mul, mul_inv_cancel₀ npos.ne', inv_pow, div_inv_eq_mul] at this
    have e : ‖h n‖ ^ 2 = ‖h n‖ ^ 2 * Real.exp (-1) * Real.exp 1 := by
      rw [mul_assoc, ← Real.exp_add]; simp
    rw [e]
    calc ‖h n‖ ^ 2 * Real.exp (-1) * Real.exp 1 ≤ D * (n : ℝ) ^ k * Real.exp 1 := by gcongr
      _ = D * Real.exp 1 * (n : ℝ) ^ k := by ring
  · have T := Real.tsum_le_of_sum_range_le (nn s) (B s hs)
    have g := geo s hs hs1
    have pos : 0 < 1 - (2 : ℝ) ^ (-s) := by linarith
    calc s * ∑' n : ℕ, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ s * (Real.exp 2 * D / (1 - (2 : ℝ) ^ (-s))) := by gcongr
      _ ≤ 3 * (Real.exp 2 * D) := by
        rw [mul_div_assoc', div_le_iff₀ pos]
        have : 0 ≤ Real.exp 2 * D := by positivity
        nlinarith

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducesOfDetEvMEqZeroStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduces_of_det_evM_eq_zero' : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (τ₀ : ℍ), IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (evM s w F τ₀).det = 0 → Reduces Γ w F := by
  first | exact @GlobalTheory.OddFrame.reduces_of_det_evM_eq_zero | exact GlobalTheory.OddFrame.reduces_of_det_evM_eq_zero | (intros; apply GlobalTheory.OddFrame.reduces_of_det_evM_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumDirectionIndep
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem dif_comm (L : ℕ) (v w : ℤ × ℤ) (F : ℤ × ℤ → ℂ) :
    dif L v (dif L w F) = dif L w (dif L v F) := by
  funext x
  simp only [dif]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h : ∑ s ∈ Finset.range L, ∑ r ∈ Finset.range L, F (x + (s : ℤ) • v + (r : ℤ) • w)
      = ∑ r ∈ Finset.range L, ∑ s ∈ Finset.range L, F (x + (r : ℤ) • w + (s : ℤ) • v) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    rw [add_right_comm]
  rw [h]
  ring

theorem sum_dif_dif (L : ℕ) (w : ℤ × ℤ) (Φ G : ℤ × ℤ → ℂ) (hL : 0 < L) (hΦ : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C)
    (hw : Kills L w Φ) (hG : Summable fun x => ‖G x‖) :
    ∑' x, Φ x * dif L w (dif L w G) x = ∑' x, Φ x * G x := by
  obtain ⟨hs1, he1⟩ := GlobalTheory.T.killsTranslates_sum_mul_meanDifference_eq L w Φ G hL hΦ hw hG
  obtain ⟨_, he2⟩ := GlobalTheory.T.killsTranslates_sum_mul_meanDifference_eq L w Φ (dif L w G) hL hΦ hw hs1
  exact he2.trans he1

theorem lat_indep : ∀ (j L : ℕ) (v w : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ), 1 ≤ j → 0 < L →
    (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → Kills L w Φ → lat j 0 L v Φ τ = lat j 0 L w Φ τ := by
  intro j L v w Φ τ hj hL hΦ hv hw
  set T : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hT
  have hsv := GlobalTheory.T.summable_regularizedEisensteinLatticeTerm j L v τ hj hL
  have hsw := GlobalTheory.T.summable_regularizedEisensteinLatticeTerm j L w τ hj hL
  simp only [lat]
  calc ∑' x, Φ x * dif L v (dif L v T) x
      = ∑' x, Φ x * dif L w (dif L w (dif L v (dif L v T))) x :=
        (sum_dif_dif L w Φ _ hL hΦ hw hsv).symm
    _ = ∑' x, Φ x * dif L v (dif L v (dif L w (dif L w T))) x := by
        have c1 : ∀ F : ℤ × ℤ → ℂ, dif L w (dif L v (dif L v F)) = dif L v (dif L v (dif L w F)) := by
          intro F; rw [dif_comm L w v (dif L v F), dif_comm L w v F]
        rw [c1 T, c1 (dif L w T)]
    _ = ∑' x, Φ x * dif L w (dif L w T) x := sum_dif_dif L v Φ _ hL hΦ hv hsw

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeriesRepresentationWeightLowerBound
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem series_weight_lower_bound : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N) (τ : (ZMod g)[X] → GG g N → ℂ), IsSeries τ → ∀ f ∈ sqSet g N, ∃ w : ℝ, conv (zc (τ f)) L.e 1 = (w : ℂ) * L.e 1 ∧ (1 - 1 / (g : ℝ)) * ((torusCard g f : ℝ))⁻¹ ≤ w := by
  intro g hg N L τ hτ f hf
  obtain ⟨V, hV, hchar, hgen, hdim⟩ := hτ.2 f hf
  obtain ⟨h1, hmul, hc1, hcmul, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L
  obtain ⟨hproj, he1, -, -⟩ := GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) V V.ρ L.Mem L.chi h1 hmul hc1 hcmul
  have hz := (GlobalTheory.T.centralIdempotent_irreducible_character_props (GG g N) V).2.2.2 L.e hproj.1
  have hT : 0 < torusCard g f := ((GlobalTheory.T.squarefreeLabelTorusCard_bounds_and_mul g).1 N f hf).1
  have hr := GlobalTheory.T.rank_levelIdempotent_lower_bound_generic g N V V.ρ hgen L
  have hJ := GlobalTheory.T.card_levelDatum_group_mul_pow g N L
  have hG := GlobalTheory.T.card_generalLinearGroup_primeField g N
  have hGpos : 0 < Fintype.card (GG g N) := Fintype.card_pos
  have hgpos : 0 < g := hg.out.pos
  set k : ℕ := (if L.sharp = true then L.k else 0) with hk
  rw [← hJ, ← hdim] at hG
  have he : L.e 1 = ((Nat.card {u // L.Mem u} : ℂ))⁻¹ := he1
  set J : ℕ := Nat.card {u // L.Mem u}
  set d : ℕ := Module.finrank ℂ V
  set T : ℕ := torusCard g f
  set r : ℕ := rk V.ρ L.e
  have hJ0 : J ≠ 0 := by
    intro h
    rw [hG, h] at hGpos
    simp at hGpos
  have hd0 : d ≠ 0 := by
    intro h
    rw [hG, h] at hGpos
    simp at hGpos
  refine ⟨(r : ℝ) / ((g : ℝ) ^ k * (T : ℝ)), ?_, ?_⟩
  · rw [← hchar, hz, he, hG]
    have a1 : (J : ℂ) ≠ 0 := by exact_mod_cast hJ0
    have a2 : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
    have a3 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have a4 : (g : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
    push_cast
    field_simp
  · have a3 : (0 : ℝ) < T := by exact_mod_cast hT
    have a4 : (0 : ℝ) < (g : ℝ) ^ k := by positivity
    rw [le_div_iff₀ (mul_pos a4 a3)]
    calc (1 - 1 / (g : ℝ)) * (T : ℝ)⁻¹ * ((g : ℝ) ^ k * T) = (1 - 1 / (g : ℝ)) * (g : ℝ) ^ k := by
          field_simp
      _ ≤ r := hr

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionTransformation
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem sg_smul (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) (τ : ℍ) (hx : admitted c x) :
    sg c x (γ • τ) = sg c (act x γ) τ :=
  GlobalTheory.T.modular_law_of_s_and_t (admitted c) (sg c) (fun x γ h => GlobalTheory.T.admissible_of_sl2_action c x γ h)
    (fun x τ h => GlobalTheory.T.smoothedSiegelUnit_modularS_smul c x τ h) (fun x τ _ => GlobalTheory.T.smoothedSiegelUnit_modularGroupT_smul c x τ) γ x τ hx

end GlobalTheory.Sieg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2CoprimeFactorizationUnique
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory

theorem sl2_right_factor_of_coprime_factorizations :
    ∀ (a c : ℤ), IsCoprime a c → c ≠ 0 → ∀ (y y' β β' : Matrix (Fin 2) (Fin 2) ℤ),
      y.det = a → y'.det = a → β.det = c → β'.det = c → y * β = y' * β' →
      ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * β = β' := by
  intro a c hac hc y y' β β' hy hy' hβ hβ' hyβ
  set P : Matrix (Fin 2) (Fin 2) ℤ := β' * adjugate β with hP
  set Q : Matrix (Fin 2) (Fin 2) ℤ := adjugate y' * y with hQ
  have hPQ : a • P = c • Q := by
    have h1 : adjugate y' * y * β = a • β' := by
      rw [Matrix.mul_assoc, hyβ, ← Matrix.mul_assoc, adjugate_mul, hy', Matrix.smul_mul, Matrix.one_mul]
    have h2 : β * adjugate β = c • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [mul_adjugate, hβ]
    calc a • P = (a • β') * adjugate β := by rw [hP, Matrix.smul_mul]
      _ = adjugate y' * y * β * adjugate β := by rw [h1]
      _ = Q * (β * adjugate β) := by rw [hQ, Matrix.mul_assoc]
      _ = c • Q := by rw [h2, Matrix.mul_smul, Matrix.mul_one]
  have hdiv : ∀ i j, c ∣ P i j := by
    intro i j
    have := congrFun (congrFun hPQ i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact hac.symm.dvd_of_dvd_mul_left ⟨Q i j, this⟩
  choose M hM using hdiv
  set Mm : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of M with hMm
  have hPM : P = c • Mm := by
    ext i j; simp [hMm, hM i j]
  have hMβ : Mm * β = β' := by
    have : c • (Mm * β) = c • β' := by
      rw [← Matrix.smul_mul, ← hPM, hP, Matrix.mul_assoc, adjugate_mul, hβ, Matrix.mul_smul, Matrix.mul_one]
    ext i j
    have := congrFun (congrFun this i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hc this
  have hdet : Mm.det = 1 := by
    have h1 : P.det = c * c := by
      rw [hP, det_mul, det_adjugate, hβ, hβ']
      simp
    rw [hPM, det_smul] at h1
    simp at h1
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
    have : c ^ 2 * Mm.det = c ^ 2 * 1 := by rw [h1]; ring
    exact mul_left_cancel₀ hc2 this
  exact ⟨⟨Mm, hdet⟩, hMβ⟩

end GlobalTheory
end

