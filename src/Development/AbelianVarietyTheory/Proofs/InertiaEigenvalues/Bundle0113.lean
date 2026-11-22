import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0082
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0095
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorProperties
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.StdChar

def qe (q : ℚ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (q : ℂ))

theorem qe_add (a b : ℚ) : qe (a + b) = qe a * qe b := by
  simp only [qe, Rat.cast_add, mul_add, Complex.exp_add]

theorem qe_int (n : ℤ) : qe n = 1 := by
  simp only [qe, Rat.cast_intCast]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) = n * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem qe_eq_one {q : ℚ} (h : qe q = 1) : ∃ n : ℤ, q = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨n, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (q : ℂ) = n := by
    apply mul_left_cancel₀ h2
    rw [hn]; ring
  exact_mod_cast this

def ce (z : AddCircle (1 : ℚ)) : ℂ :=
  Quotient.liftOn' z qe (fun a b h => by
    rw [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_zmultiples_iff] at h
    obtain ⟨n, hn⟩ := h
    have hb : b = a + n := by rw [zsmul_one] at hn; linarith
    rw [hb, qe_add, qe_int, mul_one])

theorem ce_coe (q : ℚ) : ce (q : AddCircle (1 : ℚ)) = qe q := rfl

theorem ce_add (a b : AddCircle (1 : ℚ)) : ce (a + b) = ce a * ce b := by
  induction a using QuotientAddGroup.induction_on with
  | H a =>
  induction b using QuotientAddGroup.induction_on with
  | H b =>
  rw [← QuotientAddGroup.mk_add]
  exact qe_add a b

theorem ce_zero : ce 0 = 1 := by
  rw [show (0 : AddCircle (1 : ℚ)) = ((0 : ℚ) : AddCircle (1 : ℚ)) by simp, ce_coe]
  simpa using qe_int 0

theorem ce_eq_one {z : AddCircle (1 : ℚ)} (h : ce z = 1) : z = 0 := by
  induction z using QuotientAddGroup.induction_on with
  | H q =>
  obtain ⟨n, hn⟩ := qe_eq_one h
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨n, by simp [hn]⟩

section Field
variable {F : Type} [NontriviallyNormedField F]

def intSub (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] : AddSubgroup F where
  carrier := {x | ‖x‖ ≤ 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

theorem mem_intSub [IsUltrametricDist F] {x : F} : x ∈ intSub F ↔ ‖x‖ ≤ 1 := Iff.rfl

def charOf (c : F →+ AddCircle (1 : ℚ)) : AddChar F ℂ where
  toFun x := ce (c x)
  map_zero_eq_one' := by simp [ce_zero]
  map_add_eq_mul' a b := by simp [ce_add]

theorem exists_unif [IsUltrametricDist F] [ProperSpace F] :
    ∃ ϖ : F, ϖ ≠ 0 ∧ ‖ϖ‖ < 1 ∧ ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := by
  have hK : IsCompact (Metric.ball (0 : F) 1) :=
    (isCompact_closedBall (0 : F) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball 0 1)
      Metric.ball_subset_closedBall
  obtain ⟨ϖ, hϖ, hmax⟩ := hK.exists_isMaxOn ⟨0, by simp⟩ continuous_norm.continuousOn
  have hϖ1 : ‖ϖ‖ < 1 := by simpa using hϖ
  have hle : ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := fun y hy => hmax (by simpa using hy)
  obtain ⟨z, hz0, hz1⟩ := NormedField.exists_norm_lt_one F
  refine ⟨ϖ, ?_, hϖ1, hle⟩
  intro h
  have := hle z hz1
  rw [h, norm_zero] at this
  linarith

theorem exists_nat_norm_lt_one [IsUltrametricDist F] [ProperSpace F] [CharZero F] :
    ∃ N : ℕ, 0 < N ∧ ‖(N : F)‖ < 1 := by
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : F) 1).tendsto_subseq
    (x := fun n : ℕ => (n : F)) (fun n => by simpa using IsUltrametricDist.norm_natCast_le_one F n)
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq 1 one_pos
  have h := hM (M + 1) (by omega)
  have hlt : φ M < φ (M + 1) := hφ (by omega)
  refine ⟨φ (M + 1) - φ M, by omega, ?_⟩
  rw [Nat.cast_sub hlt.le, ← dist_eq_norm]
  simpa using h

variable (F) in
theorem exists_stdChar [IsUltrametricDist F] [ProperSpace F] : ∃ ψ : AddChar F ℂ, IsStdChar ψ := by
  obtain ⟨ϖ, hϖ0, hϖ1, hle⟩ := exists_unif (F := F)
  have hpos : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
  have hx : (QuotientAddGroup.mk ϖ⁻¹ : F ⧸ intSub F) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff, mem_intSub, norm_inv, not_le]
    exact one_lt_inv_iff₀.2 ⟨hpos, hϖ1⟩
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hx
  let c' : F →+ AddCircle (1 : ℚ) := AddMonoidHom.comp c (QuotientAddGroup.mk' (intSub F))
  refine ⟨charOf c', fun x hx1 => ?_, ϖ⁻¹, fun h => hc ?_, fun y hy => ?_⟩
  · show ce (c (QuotientAddGroup.mk x)) = 1
    rw [(QuotientAddGroup.eq_zero_iff x).2 hx1, map_zero, ce_zero]
  · exact ce_eq_one h
  · rw [norm_mul, norm_inv, inv_mul_le_iff₀ hpos, mul_one]
    exact hle y hy

end Field

section Props
variable {F : Type} [NontriviallyNormedField F]

theorem locConst [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) :
    IsLocallyConstant (fun x => ψ x) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨Metric.ball x 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, fun x' hx' => ?_⟩
  have h : ψ (x' - x) = 1 := hψ.1 _ (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hx').le)
  calc ψ x' = ψ (x + (x' - x)) := by rw [add_sub_cancel]
    _ = ψ x := by rw [AddChar.map_add_eq_mul, h, mul_one]

theorem norm_eq_one [IsUltrametricDist F] [ProperSpace F] [CharZero F] {ψ : AddChar F ℂ}
    (hψ : IsStdChar ψ) (x : F) : ‖ψ x‖ = 1 := by
  obtain ⟨N, hN0, hN1⟩ := exists_nat_norm_lt_one (F := F)
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hxpos) hN1
  have h1 : ψ ((N ^ k : ℕ) • x) = 1 := by
    apply hψ.1
    rw [nsmul_eq_mul, norm_mul, Nat.cast_pow, norm_pow]
    exact (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _)).trans (by rw [inv_mul_cancel₀ hxpos.ne'])
  rw [AddChar.map_nsmul_eq_pow] at h1
  have h2 : ‖ψ x‖ ^ (N ^ k) = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero k hN0.ne')).1 h2

theorem conductor [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (y : F) :
    (∀ e : F, ‖e‖ ≤ 1 → ψ (e * y) = 1) ↔ ‖y‖ ≤ 1 := by
  constructor
  · intro h
    by_contra hy
    push_neg at hy
    obtain ⟨x, hx, hxy⟩ := hψ.2
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
    have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hxle : ‖x‖ ≤ ‖y‖ := by
      have := hxy y⁻¹ (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hy)
      rwa [norm_mul, norm_inv, mul_inv_le_iff₀ hypos, one_mul] at this
    apply hx
    have := h (x * y⁻¹) (by rw [norm_mul, norm_inv, mul_inv_le_iff₀ hypos, one_mul]; exact hxle)
    rwa [mul_assoc, inv_mul_cancel₀ hy0, mul_one] at this
  · intro hy e he
    exact hψ.1 _ (by rw [norm_mul]; exact mul_le_one₀ he (norm_nonneg _) hy)

end Props

section Ext
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem conductor_trace [hU : Unram F E]
    (htr : ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y)
    (he : ∃ e : E, ‖e‖ ≤ 1 ∧ e + star e = 1)
    {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (y : E) :
    (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * y)) = 1) ↔ ‖y‖ ≤ 1 := by
  haveI := hU.ultraE
  constructor
  · intro h
    by_contra hy
    push_neg at hy
    obtain ⟨x, hx, hxy⟩ := hψ.2
    obtain ⟨e₀, he₀, hsum⟩ := he
    obtain ⟨a, ha⟩ := hU.unram y
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
    have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have ha1 : 1 < ‖a‖ := ha ▸ hy
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha1; linarith
    have hxle : ‖x‖ ≤ ‖y‖ := by
      have := hxy a⁻¹ (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ ha1)
      rw [norm_mul, norm_inv, mul_inv_le_iff₀ (norm_pos_iff.2 ha0), one_mul] at this
      rwa [ha]
    have htr1 : Algebra.trace F E e₀ = 1 := by
      apply (algebraMap F E).injective
      rw [htr, hsum, map_one]
    apply hx
    have := h (algebraMap F E x * e₀ * y⁻¹) (by
      rw [norm_mul, norm_mul, norm_inv, norm_algebraMap', mul_inv_le_iff₀ hypos]
      calc ‖x‖ * ‖e₀‖ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left he₀ (norm_nonneg _)
        _ ≤ 1 * ‖y‖ := by rw [mul_one, one_mul]; exact hxle)
    rwa [mul_assoc, inv_mul_cancel₀ hy0, mul_one, ← Algebra.smul_def, LinearMap.map_smul, htr1,
      smul_eq_mul, mul_one] at this
  · intro hy e he'
    apply hψ.1
    have hz : ‖e * y‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ he' (norm_nonneg _) hy
    rw [← norm_algebraMap' E, htr]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hz (by rw [hU.norm_star]; exact hz))

end Ext

theorem psi_conductor : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E], (∃ ψ : AddChar F ℂ, IsStdChar ψ) ∧ ∀ ψ : AddChar F ℂ, IsStdChar ψ →
    IsLocallyConstant (fun x => ψ x) ∧ (∀ x, ‖ψ x‖ = 1) ∧
    (∀ y : F, (∀ e : F, ‖e‖ ≤ 1 → ψ (e * y) = 1) ↔ ‖y‖ ≤ 1) ∧
    ∀ y : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * y)) = 1) ↔ ‖y‖ ≤ 1 := by
  intro F E _ _ _ _ hU
  haveI := hU.ultraF
  haveI := hU.charZero
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨htr, he, -⟩ := GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E
  exact ⟨exists_stdChar F, fun ψ hψ => ⟨locConst hψ, norm_eq_one hψ, conductor hψ,
    conductor_trace htr he hψ⟩⟩

end GlobalTheory.StdChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassDivisionEisensteinPowIntegralStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_division_eisensteinPow_integral : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) (f : K⟦X⟧), f ∈ A O K → ∃ (c : Fin (e * n) → O) (g : K⟦X⟧), g ∈ A O K ∧ f = ∑ k : Fin (e * n), C (algebraMap O K (c k)) * X ^ (k : ℕ) + E K l e ^ n * g := by
  first | exact @GlobalTheory.weierstrassDiv_E_pow | exact GlobalTheory.weierstrassDiv_E_pow | (intros; apply GlobalTheory.weierstrassDiv_E_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationExistsEtaleOfSubsingleton
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR

theorem weilAt_of_subsingleton (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (hK : Subsingleton A.K) : WeilAt A := by
  have h01 : (0 : A.L) = 1 := by
    rw [← map_zero (algebraMap A.K A.L), ← map_one (algebraMap A.K A.L), Subsingleton.elim (0 : A.K) 1]
  haveI hL : Subsingleton A.L := subsingleton_of_zero_eq_one h01
  have hpsi : ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ t : A.K, A.psiK ψ t = 1 := by
    intro ψ _ t
    unfold Et.psiK
    rw [Subsingleton.elim t 0, map_zero, AddChar.map_zero_eq_one]
  intro ψ hψ x μ hμ
  haveI := hμ.1
  have hpos : 0 < μ Set.univ := (isOpen_univ.measure_pos μ Set.univ_nonempty)
  have hfin : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
  have hreal : μ.real Set.univ ≠ 0 := by
    rw [measureReal_def]; exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  refine ⟨(μ.real Set.univ : ℂ)⁻¹, fun _ φ => φ, ?_, ?_⟩
  · exact ⟨fun _ _ hf => hf, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  · intro φ _
    refine ⟨?_, ?_, ?_⟩
    · intro z y; simp [hpsi ψ hψ]
    · intro s y
      have he : A.etaK (s : A.K) = 1 := by
        unfold Et.etaK eta
        rw [Subsingleton.elim (s : A.K) 1, map_one]
        rw [if_pos ⟨1, by simp⟩]
      have ha : A.absK (s : A.K) = 1 := by
        unfold Et.absK
        rw [dif_pos s.isUnit]
        rw [Subsingleton.elim (s.isUnit.unit) 1, map_one]
        rfl
      rw [he, ha, Subsingleton.elim ((s : A.K) • y) y]
      simp
    · intro y
      unfold fourB
      have : (fun x' => φ x' * A.kerL ψ x x' y) = fun _ => φ y := by
        funext x'
        unfold Et.kerL
        rw [hpsi ψ hψ, Subsingleton.elim x' y, mul_one]
      rw [this, integral_const, Complex.real_smul]
      show φ y = _
      have hc : ((μ.real Set.univ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hreal
      field_simp

end GlobalTheory.JR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowSummedRowPowEqAdditiveSystemPowerSumStatement
section
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.windowSummedRow_pow_eq_additiveSystemPowerSum : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π : Fin h → F) (L U : ℕ), 1 ≤ L → ∀ (z : Fin h → F) (r : Fin h), (rowS p ϖ lam L U (winPt p π L z) r / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) = gsum (p ^ h) (L + U) (coefB p ϖ lam π L U) z r := by
  first | exact @GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB | exact GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB | (intros; apply GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorGaussNormMul
section
namespace GlobalTheory

namespace WittGaussMul

theorem exists_lt_bound (f : ℕ → ℝ) (B : ℝ) (hB : 0 < B) (i : ℕ) (h : ∀ k < i, f k < B) :
    ∃ c, 0 ≤ c ∧ c < B ∧ ∀ k < i, f k ≤ c := by
  induction i with
  | zero => exact ⟨0, le_rfl, hB, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ i ih =>
    obtain ⟨c, hc0, hcB, hc⟩ := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    refine ⟨max c (f i), le_max_of_le_left hc0, max_lt hcB (h i (Nat.lt_succ_self i)), ?_⟩
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact le_max_of_le_left (hc k hk)
    · exact le_max_right _ _

theorem exists_first_max (f : ℕ → ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hf : ∀ n, f n ≤ r ^ n) (hpos : 0 < ⨆ n, f n) :
    ∃ i, f i = (⨆ n, f n) ∧ ∀ k < i, f k < ⨆ n, f n := by
  classical
  have hb : BddAbove (Set.range f) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (hf n).trans (pow_le_one₀ hr0.le hr1.le)⟩
  have hle : ∀ n, f n ≤ ⨆ n, f n := fun n => le_ciSup hb n
  have hex : ∃ i, f i = ⨆ n, f n := by
    by_contra hne
    push Not at hne
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hpos hr1
    obtain ⟨c, -, hcB, hc⟩ := exists_lt_bound f _ hpos M
      (fun k _ => lt_of_le_of_ne (hle k) (hne k))
    have : (⨆ n, f n) ≤ max c (r ^ M) := by
      refine ciSup_le fun n => ?_
      rcases lt_or_ge n M with h | h
      · exact le_max_of_le_left (hc n h)
      · exact le_max_of_le_right ((hf n).trans (pow_le_pow_of_le_one hr0.le hr1.le h))
    exact absurd (max_lt hcB hM) (not_lt.mpr this)
  exact ⟨Nat.find hex, Nat.find_spec hex,
    fun k hk => lt_of_le_of_ne (hle k) (Nat.find_min hex hk)⟩

end WittGaussMul

open WittGaussMul in

theorem witt_gaussNorm_mul : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ), (∀ x, 0 ≤ a x ∧ a x ≤ 1) → a 0 = 0 → a 1 = 1 → (∀ x y, a (x * y) = a x * a y) → (∀ x y, a (x + y) ≤ max (a x) (a y)) → ∀ r : ℝ, 0 < r → r < 1 → ∀ N : WittVector l R → ℝ, (∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ x y, N (x * y) = N x * N y := by
  intro l hl R _ _ _ a h01 h0 h1 hmul hadd r hr0 hr1 N hN x y
  obtain ⟨Nadd, Nneg, Nmul⟩ := GlobalTheory.T.witt_vector_gauss_norm_ultrametric l R a h01 h0 h1 hmul hadd r hr0 hr1 N hN
  set T : WittVector l R → ℕ → ℝ := fun x n => a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n
    with hT
  have hN' : ∀ x, N x = ⨆ n, T x n := hN
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hexp : ∀ n : ℕ, (0 : ℝ) < 1 / (l : ℝ) ^ n := fun n => by positivity
  have hT0 : ∀ x n, 0 ≤ T x n := fun x n =>
    mul_nonneg (Real.rpow_nonneg (h01 _).1 _) (pow_pos hr0 n).le
  have hTr : ∀ x n, T x n ≤ r ^ n := fun x n =>
    mul_le_of_le_one_left (pow_pos hr0 n).le
      (Real.rpow_le_one (h01 _).1 (h01 _).2 (hexp n).le)
  have hTN : ∀ x n, T x n ≤ N x := fun x n => by
    rw [hN']
    exact le_ciSup (f := T x)
      ⟨1, by rintro _ ⟨n, rfl⟩; exact (hTr x n).trans (pow_le_one₀ hr0.le hr1.le)⟩ n
  have hN0 : ∀ x, 0 ≤ N x := fun x => (hT0 x 0).trans (hTN x 0)
  have hTz : ∀ x n, x.coeff n = 0 → T x n = 0 := fun x n h => by
    simp only [hT, h, h0, Real.zero_rpow (hexp n).ne', zero_mul]
  have hpow : ∀ w (n : ℕ), a (w ^ n) = a w ^ n := fun w n => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hTp : ∀ (u : WittVector l R) (n : ℕ), T (u * (l : WittVector l R) ^ n) n
      = a (u.coeff 0) * r ^ n := fun u n => by
    have h := WittVector.mul_pow_charP_coeff_succ u (m := 0) (n := n)
    rw [zero_add] at h
    simp only [hT, h, hpow]
    congr 1
    have := Real.pow_rpow_inv_natCast (h01 (u.coeff 0)).1 (pow_pos hl.out.pos n).ne'
    simpa using this
  have key : ∀ x, 0 < N x → ∃ (i : ℕ) (x0 u : WittVector l R),
      x = x0 + u * (l : WittVector l R) ^ i ∧ N x0 < N x ∧
      N (u * (l : WittVector l R) ^ i) ≤ N x ∧ a (u.coeff 0) * r ^ i = N x := by
    intro x hx
    obtain ⟨i, hi, hlt⟩ := exists_first_max (T x) r hr0 hr1 (hTr x) (by rw [← hN']; exact hx)
    rw [← hN'] at hi hlt
    have hmem : WittVector.tail i x ∈ Ideal.span {((l : WittVector l R) ^ i)} := by
      rw [WittVector.mem_span_p_pow_iff_le_coeff_eq_zero]
      intro m hm
      simp [WittVector.tail, WittVector.select, WittVector.coeff_mk, not_le.mpr hm]
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨i, WittVector.init i x, u, ?_, ?_, ?_, ?_⟩
    · rw [hu, WittVector.init_add_tail]
    · obtain ⟨c, hc0, hcB, hc⟩ := exists_lt_bound (T x) _ hx i hlt
      refine lt_of_le_of_lt ?_ hcB
      rw [hN']
      refine ciSup_le fun n => ?_
      rcases lt_or_ge n i with h | h
      · have : (WittVector.init i x).coeff n = x.coeff n := by
          simp [WittVector.init, WittVector.select, WittVector.coeff_mk, h]
        have h2 : T (WittVector.init i x) n = T x n := by simp only [hT, this]
        rw [h2]; exact hc n h
      · rw [hTz]
        · exact hc0
        · simp [WittVector.init, WittVector.select, WittVector.coeff_mk, not_lt.mpr h]
    · rw [hu, hN' (WittVector.tail i x)]
      refine ciSup_le fun n => ?_
      rcases lt_or_ge n i with h | h
      · rw [hTz]
        · exact hN0 x
        · simp [WittVector.tail, WittVector.select, WittVector.coeff_mk, not_le.mpr h]
      · have : (WittVector.tail i x).coeff n = x.coeff n := by
          simp [WittVector.tail, WittVector.select, WittVector.coeff_mk, h]
        have h2 : T (WittVector.tail i x) n = T x n := by simp only [hT, this]
        rw [h2]; exact hTN x n
    · rw [← hTp, hu, ← hi]
      have : (WittVector.tail i x).coeff i = x.coeff i := by
        simp [WittVector.tail, WittVector.select, WittVector.coeff_mk]
      simp only [hT, this]
  refine le_antisymm (Nmul x y) ?_
  rcases (hN0 x).eq_or_lt with hx | hx
  · rw [← hx, zero_mul]; exact hN0 _
  rcases (hN0 y).eq_or_lt with hy | hy
  · rw [← hy, mul_zero]; exact hN0 _
  obtain ⟨i, x0, u, hxe, hx0, hu, hui⟩ := key x hx
  obtain ⟨j, y0, v, hye, hy0, hv, hvj⟩ := key y hy
  have hmain : N x * N y ≤ N ((u * v) * (l : WittVector l R) ^ (i + j)) := by
    refine le_trans (le_of_eq ?_) (hTN _ (i + j))
    rw [hTp, WittVector.mul_coeff_zero, hmul, ← hui, ← hvj]
    ring
  have hrest : N (x0 * y + (u * (l : WittVector l R) ^ i) * y0) < N x * N y := by
    refine lt_of_le_of_lt (Nadd _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Nmul _ _) (mul_lt_mul_of_pos_right hx0 hy)
    · refine lt_of_le_of_lt (Nmul _ _) ?_
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hu (hN0 _)) (mul_lt_mul_of_pos_left hy0 hx)
  have heq : (u * v) * (l : WittVector l R) ^ (i + j)
      = x * y + -(x0 * y + (u * (l : WittVector l R) ^ i) * y0) := by
    have : x * y = x0 * y + (u * (l : WittVector l R) ^ i) * (y0 + v * (l : WittVector l R) ^ j) := by
      rw [← hye, ← add_mul, ← hxe]
    rw [this]; ring
  have h3 := Nadd (x * y) (-(x0 * y + (u * (l : WittVector l R) ^ i) * y0))
  rw [← heq, Nneg] at h3
  rcases le_max_iff.mp (hmain.trans h3) with h | h
  · exact h
  · exact absurd hrest (not_lt.mpr h)

end GlobalTheory
end

