import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTwistingLineDataProjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0005
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.RankOneEisenstein.Theta2Integral
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionGood
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfForallInM
section
noncomputable section
open NumberField IsDedekindDomain Topology
open PositivityTheory.RgEis PositivityTheory.RgEis.TF

namespace GlobalTheory.CompanionTheory.RgEis.InMTopPf

variable {k : Type} [Field k] [NumberField k]

theorem natCast_isUnit (M : ℕ) (hM : M ≠ 0) : IsUnit (M : FiniteAdeleRing (𝓞 k) k) := by
  have : (M : FiniteAdeleRing (𝓞 k) k) = algebraMap k _ (M : k) := by simp
  rw [this]
  exact (IsUnit.mk0 _ (by exact_mod_cast hM)).map _

theorem inM_iff (M : ℕ) (hM : M ≠ 0) (x : FiniteAdeleRing (𝓞 k) k) :
    InM M x ↔ (((natCast_isUnit (k := k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) :
      FiniteAdeleRing (𝓞 k) k) * x ∈ OH k := by
  set u := (natCast_isUnit (k := k) M hM).unit
  have hu : (u : FiniteAdeleRing (𝓞 k) k) = M := rfl
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]

theorem isOpen_isClosed (M : ℕ) (hM : M ≠ 0) :
    IsOpen {x : FiniteAdeleRing (𝓞 k) k | InM M x} ∧ IsClosed {x : FiniteAdeleRing (𝓞 k) k | InM M x} := by
  have hS : {x : FiniteAdeleRing (𝓞 k) k | InM M x} =
      (fun x => (((natCast_isUnit (k := k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) :
        FiniteAdeleRing (𝓞 k) k) * x) ⁻¹' (OH k : Set (FiniteAdeleRing (𝓞 k) k)) := by
    ext x; exact inM_iff M hM x
  have hc : Continuous (fun x : FiniteAdeleRing (𝓞 k) k =>
      (((natCast_isUnit (k := k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) * x) :=
    continuous_const.mul continuous_id
  have ho : IsOpen (OH k : Set (FiniteAdeleRing (𝓞 k) k)) := GroundTheory.Global.isOpen_integralFiniteAdeles
  rw [hS]
  exact ⟨ho.preimage hc, (AddSubgroup.isClosed_of_isOpen (OH k).toAddSubgroup ho).preimage hc⟩

theorem exists_pow_lt' {c a : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hc : c < 1) : ∃ n : ℕ, c ^ n < a := by
  rcases eq_or_ne c 0 with rfl | hc0
  · exact ⟨1, by simpa using (zero_lt_iff.mpr ha)⟩
  obtain ⟨α, rfl⟩ := WithZero.ne_zero_iff_exists.mp hc0
  obtain ⟨β, rfl⟩ := WithZero.ne_zero_iff_exists.mp ha
  have hα : Multiplicative.toAdd α < 0 := by
    have h1 : ((α : WithZero (Multiplicative ℤ))) < ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      simpa using hc
    rw [WithZero.coe_lt_coe] at h1
    exact h1
  refine ⟨(Multiplicative.toAdd β).natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
  show Multiplicative.toAdd (α ^ ((Multiplicative.toAdd β).natAbs + 1)) < Multiplicative.toAdd β
  rw [toAdd_pow, nsmul_eq_mul]
  set a := Multiplicative.toAdd α
  set b := Multiplicative.toAdd β
  have ha1 : a ≤ -1 := by omega
  have h3 : (((b.natAbs + 1 : ℕ) : ℤ)) * a ≤ -(((b.natAbs + 1 : ℕ) : ℤ)) := by
    have : (0 : ℤ) ≤ ((b.natAbs + 1 : ℕ) : ℤ) := by positivity
    nlinarith
  push_cast at h3 ⊢
  have h4 := neg_abs_le b
  linarith

theorem natCast_apply' (v : HeightOneSpectrum (𝓞 k)) (M : ℕ) :
    (M : FiniteAdeleRing (𝓞 k) k) v = (M : v.adicCompletion k) := by
  rw [← map_natCast (algebraMap k (FiniteAdeleRing (𝓞 k) k)) M, FiniteAdeleRing.algebraMap_apply]
  exact map_natCast (algebraMap k (v.adicCompletion k)) M

theorem valued_natCast (v : HeightOneSpectrum (𝓞 k)) (n : ℕ) :
    Valued.v (n : v.adicCompletion k) = v.intValuation (n : 𝓞 k) := by
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := k) v (n : 𝓞 k)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at this
  rw [← this]
  congr 1
  simp

theorem eq_zero_of_forall_inM (x : FiniteAdeleRing (𝓞 k) k) (hx : ∀ M : ℕ, M ≠ 0 → InM M x) : x = 0 := by
  refine Subtype.ext (funext fun v => ?_)
  change x v = 0
  by_contra hxv
  set N : ℕ := Ideal.absNorm v.asIdeal with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hNmem : (N : 𝓞 k) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have hlt : v.intValuation (N : 𝓞 k) < 1 := (v.intValuation_lt_one_iff_mem _).mpr hNmem
  have hxv0 : Valued.v (x v) ≠ 0 := by simpa using hxv
  obtain ⟨n, hn⟩ := exists_pow_lt' hxv0 hlt
  obtain ⟨y, hy, hxy⟩ := hx (N ^ n) (pow_ne_zero _ hN0)
  have hcomp : x v = ((N ^ n : ℕ) : v.adicCompletion k) * y v := by
    rw [hxy]
    have h1 := natCast_apply' v (N ^ n)
    change ((N ^ n : ℕ) : FiniteAdeleRing (𝓞 k) k) v * y v = _
    rw [h1]
  have hyv : Valued.v (y v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (hy v)
  have hle : Valued.v (x v) ≤ v.intValuation (N : 𝓞 k) ^ n := by
    rw [hcomp, map_mul, valued_natCast, Nat.cast_pow, map_pow]
    exact mul_le_of_le_one_right' hyv
  exact absurd (lt_of_le_of_lt hle hn) (lt_irrefl _)

theorem inMTop : InMTop := fun k _ _ =>
  ⟨fun M hM => isOpen_isClosed M hM, fun x hx => eq_zero_of_forall_inM x hx⟩

end GlobalTheory.CompanionTheory.RgEis.InMTopPf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTwistingLineDataProjectiveStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisting_line_data_projective : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (N : ℕ) (i : X ⟶ PSpace R N), ∃ D : E.LineData X, IsTautologicalLineAt D N i := by
  first | exact @GlobalTheory.CompanionTheory.ConeTwistingSheafMap.main | exact GlobalTheory.CompanionTheory.ConeTwistingSheafMap.main | (intros; apply GlobalTheory.CompanionTheory.ConeTwistingSheafMap.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalEquationPairEntirePartBound
section
namespace GlobalTheory.CompanionTheory.EisRk1

open MeasureTheory Set Filter Topology

theorem weakFEPair_norm_Λ₀_le (P : WeakFEPair ℂ) {r M : ℝ}
    (hf : ∀ x : ℝ, 1 ≤ x → ‖P.f x - P.f₀‖ ≤ M * x ^ (-r))
    (hg : ∀ x : ℝ, 1 ≤ x → ‖P.g x - P.g₀‖ ≤ M * x ^ (-r))
    (s : ℂ) (hs₁ : s.re < r) (hs₂ : P.k - s.re < r) :
    ‖P.Λ₀ s‖ ≤ M / (r - s.re) + ‖P.ε‖ * M / (r - (P.k - s.re)) := by
  set σ := s.re with hσ
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (by simpa using hf 1 le_rfl)
  set h : ℝ → ℝ := (Ioi 1).indicator (fun t => M * t ^ (σ - 1 - r)) +
      (Ioo 0 1).indicator (fun t => ‖P.ε‖ * M * t ^ (σ - 1 + r - P.k)) with hh
  have hA : IntegrableOn (fun t : ℝ => M * t ^ (σ - 1 - r)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul M
  have hB : IntegrableOn (fun t : ℝ => ‖P.ε‖ * M * t ^ (σ - 1 + r - P.k)) (Ioo 0 1) :=
    (((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := σ - 1 + r - P.k)
      (by linarith)).1).mono_set Ioo_subset_Ioc_self).const_mul _
  have hA' := hA.integrable_indicator measurableSet_Ioi
  have hB' := hB.integrable_indicator measurableSet_Ioo
  have hint : Integrable h (volume.restrict (Ioi 0)) := (hA'.add hB').restrict
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • P.f_modif t‖ ≤ h t := by
    intro t ht
    rw [mem_Ioi] at ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
    rcases lt_trichotomy t 1 with h1 | rfl | h1
    · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).2 h1
      have e := P.hf_modif_FE t⁻¹ (inv_pos.2 ht)
      rw [one_div, inv_inv] at e
      have hg' : P.g_modif t⁻¹ = P.g t⁻¹ - P.g₀ := by
        simp [WeakFEPair.g_modif, indicator_of_mem (mem_Ioi.2 hinv),
          indicator_of_notMem (notMem_Ioo_of_ge hinv.le)]
      have hval : h t = ‖P.ε‖ * M * t ^ (σ - 1 + r - P.k) := by
        simp [hh, indicator_of_notMem (notMem_Ioi.2 h1.le), indicator_of_mem (mem_Ioo.2 ⟨ht, h1⟩)]
      rw [hval, e, hg', norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (inv_pos.2 ht) _), Real.inv_rpow ht.le]
      have hb := hg t⁻¹ hinv.le
      rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le, inv_inv] at hb
      have key : t ^ (σ - 1 + r - P.k) = t ^ (σ - 1) * (t ^ P.k)⁻¹ * t ^ r := by
        rw [sub_eq_add_neg (σ - 1 + r), Real.rpow_add ht, Real.rpow_add ht, Real.rpow_neg ht.le]
        ring
      rw [key]
      have hpos : 0 ≤ t ^ (σ - 1) * ‖P.ε‖ * (t ^ P.k)⁻¹ := by positivity
      calc t ^ (σ - 1) * (‖P.ε‖ * (t ^ P.k)⁻¹ * ‖P.g t⁻¹ - P.g₀‖)
          = (t ^ (σ - 1) * ‖P.ε‖ * (t ^ P.k)⁻¹) * ‖P.g t⁻¹ - P.g₀‖ := by ring
        _ ≤ (t ^ (σ - 1) * ‖P.ε‖ * (t ^ P.k)⁻¹) * (M * t ^ r) := mul_le_mul_of_nonneg_left hb hpos
        _ = ‖P.ε‖ * M * (t ^ (σ - 1) * (t ^ P.k)⁻¹ * t ^ r) := by ring
    · have h0 : P.f_modif 1 = 0 := by simp [WeakFEPair.f_modif]
      have hval : h 1 = 0 := by simp [hh]
      rw [h0, hval, norm_zero, mul_zero]
    · have hfm : P.f_modif t = P.f t - P.f₀ := by
        simp [WeakFEPair.f_modif, indicator_of_mem (mem_Ioi.2 h1),
          indicator_of_notMem (notMem_Ioo_of_ge h1.le)]
      have hval : h t = M * t ^ (σ - 1 - r) := by
        simp [hh, indicator_of_mem (mem_Ioi.2 h1), indicator_of_notMem (notMem_Ioo_of_ge h1.le)]
      rw [hfm, hval]
      have hb := hf t h1.le
      have key : t ^ (σ - 1 - r) = t ^ (σ - 1) * t ^ (-r) := by
        rw [sub_eq_add_neg (σ - 1), Real.rpow_add ht]
      rw [key]
      calc t ^ (σ - 1) * ‖P.f t - P.f₀‖ ≤ t ^ (σ - 1) * (M * t ^ (-r)) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = M * (t ^ (σ - 1) * t ^ (-r)) := by ring
  have hI : ∫ t in Ioi (0 : ℝ), h t = M / (r - σ) + ‖P.ε‖ * M / (r - (P.k - σ)) := by
    rw [hh, integral_add' hA'.restrict hB'.restrict, setIntegral_indicator measurableSet_Ioi,
      setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.2 (Ioi_subset_Ioi zero_le_one), Set.inter_eq_right.2 Ioo_subset_Ioi_self,
      integral_const_mul, integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith))]
    have hne : σ - 1 + r - P.k + 1 ≠ 0 := by linarith
    rw [Real.one_rpow, Real.one_rpow, Real.zero_rpow hne]
    have h1 : r - σ ≠ 0 := by linarith
    have h2 : r - (P.k - σ) ≠ 0 := by linarith
    have h3 : σ - 1 - r + 1 ≠ 0 := by linarith
    field_simp
    ring
  calc ‖P.Λ₀ s‖ = ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • P.f_modif t‖ := rfl
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • P.f_modif t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), h t :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hint
          ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hpt))
    _ = _ := hI

end GlobalTheory.CompanionTheory.EisRk1
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasCompactSupportSmallF
section
open PositivityTheory.RgEis PositivityTheory.RgEis.TF

noncomputable section

namespace GlobalTheory.CompanionTheory.TestBump

variable {ι : Type} [Fintype ι]

def nsq (y : ι → ℂ) : ℝ := ∑ j, ‖y j‖ ^ 2

lemma contDiff_coordSq (i : ι) {n : WithTop ℕ∞} : ContDiff ℝ n fun y : ι → ℂ => ‖y i‖ ^ 2 :=
  (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i)

lemma contDiff_nsq {n : WithTop ℕ∞} : ContDiff ℝ n (nsq : (ι → ℂ) → ℝ) :=
  ContDiff.sum fun j _ => contDiff_coordSq j

lemma coordSq_le_nsq (y : ι → ℂ) (i : ι) : ‖y i‖ ^ 2 ≤ nsq y :=
  Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)

lemma nsq_smul (t : ℂ) (v : ι → ℂ) : nsq (t • v) = ‖t‖ ^ 2 * nsq v := by
  simp only [nsq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

def radial : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

lemma radial_one : radial 1 = 1 :=
  radial.one_of_mem_closedBall (Metric.mem_closedBall_self radial.rIn_pos.le)

lemma radial_zero_of_le {x : ℝ} (h : x ≤ 1 / 2) : radial x = 0 := by
  refine radial.zero_of_le_dist ?_
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  change (1 / 2 : ℝ) ≤ _
  linarith

lemma radial_zero_of_ge {x : ℝ} (h : 3 / 2 ≤ x) : radial x = 0 := by
  refine radial.zero_of_le_dist ?_
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  change (1 / 2 : ℝ) ≤ _
  linarith

def angular {δ : ℝ} (hδ : 0 < δ) : ContDiffBump (1 : ℝ) :=
  ⟨δ / 2, δ, by positivity, by linarith⟩

lemma angular_one {δ : ℝ} (hδ : 0 < δ) : angular hδ 1 = 1 :=
  (angular hδ).one_of_mem_closedBall (Metric.mem_closedBall_self (angular hδ).rIn_pos.le)

lemma lt_of_angular_ne {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (h : angular hδ x ≠ 0) : 1 - δ < x := by
  by_contra hx
  refine h ((angular hδ).zero_of_le_dist ?_)
  rw [Real.dist_eq, abs_of_nonpos (by linarith [not_lt.1 hx])]
  change δ ≤ _
  linarith [not_lt.1 hx]

def bigF (i₀ : ι) {δ : ℝ} (hδ : 0 < δ) (y : ι → ℂ) : ℝ :=
  radial (nsq y) * angular hδ (‖y i₀‖ ^ 2 / nsq y)

def smallF (t : ℂ) : ℝ := radial (‖t‖ ^ 2)

lemma contDiff_bigF (i₀ : ι) {δ : ℝ} (hδ : 0 < δ) {n : ℕ∞} :
    ContDiff ℝ (n : WithTop ℕ∞) (bigF i₀ hδ) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases h : 0 < nsq y
  · exact (radial.contDiff.contDiffAt.comp y contDiff_nsq.contDiffAt).mul
      ((angular hδ).contDiff.contDiffAt.comp y
        ((contDiff_coordSq i₀).contDiffAt.div contDiff_nsq.contDiffAt h.ne'))
  · have h0 : nsq y < 1 / 2 := by linarith [not_lt.1 h]
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(contDiff_nsq (n := 0)).continuous.continuousAt.eventually (gt_mem_nhds h0)] with z hz
    simp [bigF, radial_zero_of_le (le_of_lt hz)]

lemma hasCompactSupport_bigF (i₀ : ι) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (bigF i₀ hδ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℂ) 2) fun y hy => ?_
  by_contra hne
  have hr : radial (nsq y) ≠ 0 := fun h => hne (by simp [bigF, h])
  have hlt : nsq y < 3 / 2 := by
    by_contra hge
    exact hr (radial_zero_of_ge (not_lt.1 hge))
  refine hy ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  have := coordSq_le_nsq y i
  nlinarith [norm_nonneg (y i)]

lemma contDiff_smallF {n : ℕ∞} : ContDiff ℝ (n : WithTop ℕ∞) smallF :=
  radial.contDiff.comp (contDiff_norm_sq ℝ)

lemma hasCompactSupport_smallF : HasCompactSupport smallF := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2) fun t ht => ?_
  refine radial_zero_of_ge ?_
  have : 2 < ‖t‖ := by simpa using ht
  nlinarith

end GlobalTheory.CompanionTheory.TestBump

open GlobalTheory.CompanionTheory.TestBump in

theorem GlobalTheory.CompanionTheory.TestBump.cplxBump : CplxBump := by
  classical
  intro ι _ _ i₀ δ hδ
  refine ⟨bigF i₀ hδ, smallF, contDiff_bigF i₀ hδ, hasCompactSupport_bigF i₀ hδ, contDiff_smallF,
    hasCompactSupport_smallF, ?_, ?_, fun t => radial.nonneg, fun v => mul_nonneg radial.nonneg (angular hδ).nonneg, ?_⟩
  · have h1 : nsq (Pi.single i₀ 1 : ι → ℂ) = 1 := by
      simp only [nsq]
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    simp [bigF, h1, radial_one, angular_one]
  · intro t ht
    simp [smallF, ht, radial_one]
  · intro v hv
    have hv1 : nsq v = 1 := hv
    have hFv : bigF i₀ hδ v = angular hδ (‖v i₀‖ ^ 2) := by
      simp [bigF, hv1, radial_one]
    refine ⟨fun t => ?_, fun h => ?_⟩
    · rw [hFv]
      by_cases ht : t = 0
      · subst ht
        have hz : radial (0 : ℝ) = 0 := radial_zero_of_le (by norm_num)
        simp [bigF, smallF, nsq, hz]
      · have hn : nsq (t • v) = ‖t‖ ^ 2 := by rw [nsq_smul, hv1, mul_one]
        have ht2 : ‖t‖ ^ 2 ≠ 0 := by positivity
        simp only [bigF, smallF, hn, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
        rw [mul_div_cancel_left₀ _ ht2]
    · exact lt_of_angular_ne hδ (by rwa [hFv] at h)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightTermGood
section
noncomputable section

open MeasureTheory Filter Topology Metric
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
open scoped NNReal Real Pointwise

namespace GlobalTheory.CompanionTheory.RgEisHGood

theorem differentiable_of_pointwise {K : Type} [TopologicalSpace K] [CompactSpace K] (F : ℂ → C(K, ℂ))
    (hc : Continuous F) (hp : ∀ κ, Differentiable ℂ fun z => F z κ) : Differentiable ℂ F := by
  intro c
  have hint : CircleIntegrable F c ((1 : ℝ≥0) : ℝ) := hc.continuousOn.circleIntegrable'
  have hfp := hasFPowerSeriesOn_cauchy_integral hint one_pos
  simp only [NNReal.coe_one] at hfp
  have heq : ∀ w ∈ ball c (1 : ℝ), ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) = F w := by
    intro w hw
    ext κ
    have hcau := ((hp κ).diffContOnCl (s := ball c 1)).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
    have hne : ∀ θ : ℝ, circleMap c 1 θ - w ≠ 0 := fun θ h => by
      have h1 : circleMap c 1 θ ∈ sphere c (1 : ℝ) := circleMap_mem_sphere c zero_le_one θ
      rw [sub_eq_zero.1 h] at h1
      exact (ne_of_lt (mem_ball.1 hw)) (mem_sphere.1 h1)
    have hcont : Continuous (fun θ : ℝ => deriv (circleMap c 1) θ • (circleMap c 1 θ - w)⁻¹ • F (circleMap c 1 θ)) := by
      have e : deriv (circleMap c 1) = fun θ => circleMap 0 1 θ * Complex.I := funext (deriv_circleMap c 1)
      rw [e]
      exact ((continuous_circleMap 0 1).mul continuous_const).smul
        ((((continuous_circleMap c 1).sub continuous_const).inv₀ hne).smul (hc.comp (continuous_circleMap c 1)))
    have hcomm : (∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) κ = ∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z κ := by
      have e2 := (ContinuousMap.evalCLM ℂ κ : C(K, ℂ) →L[ℂ] ℂ).intervalIntegral_comp_comm
        (hcont.intervalIntegrable (μ := volume) 0 (2 * π))
      simp only [circleIntegral]
      refine e2.symm.trans ?_
      simp [ContinuousMap.evalCLM]
    have hfin : ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) κ
        = (2 * π * Complex.I : ℂ)⁻¹ • (∮ z in C(c, (1 : ℝ)), (z - w)⁻¹ • F z) κ := rfl
    rw [hfin, hcomm]
    exact hcau
  have han : AnalyticAt ℂ F c := by
    have h1 := hfp.analyticAt
    refine h1.congr ?_
    filter_upwards [ball_mem_nhds c (one_pos : (0:ℝ) < 1)] with w hw using heq w hw
  exact han.differentiableAt

theorem exists_integralCLM {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (μ : Measure K) [IsProbabilityMeasure μ]
    (r : K → E) (hr : Continuous r) : ∃ L : C(K, ℂ) →L[ℂ] E, ∀ f : C(K, ℂ), L f = ∫ κ, f κ • r κ ∂μ := by
  haveI : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hint : ∀ f : C(K, ℂ), Integrable (fun κ => f κ • r κ) μ := fun f =>
    (f.continuous.smul hr).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let rc : C(K, E) := ⟨r, hr⟩
  let L₀ : C(K, ℂ) →ₗ[ℂ] E :=
    { toFun := fun f => ∫ κ, f κ • r κ ∂μ
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply, add_smul]
        exact integral_add (hint f) (hint g)
      map_smul' := fun a f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact integral_smul a _ }
  refine ⟨L₀.mkContinuous ‖rc‖ fun f => ?_, fun f => rfl⟩
  have hb : ∀ κ, ‖f κ • r κ‖ ≤ ‖rc‖ * ‖f‖ := fun κ => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul (rc.norm_coe_le_norm κ) (f.norm_coe_le_norm κ) (norm_nonneg _) (norm_nonneg _)
  have := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hb)
  change ‖∫ κ, f κ • r κ ∂μ‖ ≤ _
  simpa using this

theorem gauss_bound (b a : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ a →
    ‖Complex.exp (z ^ 2) * (z - 1)‖ * (1 + ‖z‖) ^ 2 ≤ M := by
  set B : ℝ := |a| + |b| with hB
  have hB0 : 0 ≤ B := by positivity
  set c : ℝ := 3 + B with hc
  refine ⟨Real.exp (B ^ 2) * (6 * Real.exp c), by positivity, fun z h1 h2 => ?_⟩
  have hx : |z.re| ≤ B := by
    rw [abs_le]; constructor
    · have := neg_abs_le b; have := abs_nonneg a; linarith
    · have := le_abs_self a; have := abs_nonneg b; linarith
  set t : ℝ := |z.im| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have hz : ‖z‖ ≤ B + t := (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  have hexp : ‖Complex.exp (z ^ 2)‖ = Real.exp (z.re ^ 2 - z.im ^ 2) := by
    rw [Complex.norm_exp]; congr 1
    simp [pow_two, Complex.mul_re]
  have h1z : ‖z - 1‖ ≤ 1 + ‖z‖ := by
    refine (norm_sub_le _ _).trans ?_
    simp [add_comm]
  have hs : 1 + ‖z‖ ≤ c + t ^ 2 - 1 := by nlinarith [sq_nonneg (t - 1)]
  have hn0 : 0 ≤ 1 + ‖z‖ := by positivity
  have hc0 : 0 ≤ c + t ^ 2 := by positivity
  have hcube : (1 + ‖z‖) ^ 3 ≤ 6 * Real.exp (c + t ^ 2) := by
    have h3 := Real.pow_div_factorial_le_exp (c + t ^ 2) hc0 3
    have h4 : (1 + ‖z‖) ^ 3 ≤ (c + t ^ 2) ^ 3 := pow_le_pow_left₀ hn0 (by linarith) 3
    have h5 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h5] at h3
    linarith [(div_le_iff₀ (by norm_num : (0:ℝ) < 6)).1 h3]
  have hre : z.re ^ 2 ≤ B ^ 2 := by
    have := sq_le_sq' (by linarith [(abs_le.1 hx).1]) (abs_le.1 hx).2
    exact this
  have him : z.im ^ 2 = t ^ 2 := by rw [ht, sq_abs]
  calc ‖Complex.exp (z ^ 2) * (z - 1)‖ * (1 + ‖z‖) ^ 2
      = Real.exp (z.re ^ 2 - z.im ^ 2) * (‖z - 1‖ * (1 + ‖z‖) ^ 2) := by
        rw [norm_mul, hexp]; ring
    _ ≤ Real.exp (z.re ^ 2 - z.im ^ 2) * ((1 + ‖z‖) ^ 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have : (1 + ‖z‖) ^ 3 = (1 + ‖z‖) * (1 + ‖z‖) ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right h1z (by positivity)
    _ ≤ Real.exp (z.re ^ 2 - z.im ^ 2) * (6 * Real.exp (c + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hcube (Real.exp_pos _).le
    _ = Real.exp (z.re ^ 2) * (6 * Real.exp c) := by
        rw [him, Real.exp_add, Real.exp_sub, Real.exp_add]
        have := (Real.exp_pos (t ^ 2)).ne'
        field_simp
    _ ≤ Real.exp (B ^ 2) * (6 * Real.exp c) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hre) (by positivity)

theorem hGood : HGood := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hprob Φ hΦ
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨L, hL⟩ := exists_integralCLM μ (fun κ => ρ κ) hρ
  let Ψ₀ : C((ℂ × G) × K, ℂ) := ⟨fun p => Φ p.1.1 (p.1.2 * p.2),
    hΦ.cont.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)))⟩
  let Ψ : C(ℂ × G, C(K, ℂ)) := Ψ₀.curry
  have hA : ∀ (z : ℂ) (g : G), avg μ ρ (fun κ => Φ z (g * κ)) = L (Ψ (z, g)) := by
    intro z g
    rw [hL]
    rfl
  refine ⟨fun g => ?_, ?_, fun b a g => ?_⟩
  · simp only [hA]
    have hF : Differentiable ℂ fun z : ℂ => Ψ (z, g) :=
      differentiable_of_pointwise _ (Ψ.continuous.comp (by fun_prop)) fun κ => hΦ.ent (g * κ)
    exact ((Complex.differentiable_exp.comp (differentiable_id.pow 2)).mul
      (differentiable_id.sub_const 1)).smul (L.differentiable.comp hF)
  · simp only [hA, Prod.mk.eta]
    exact (by fun_prop : Continuous fun y : ℂ × G => Complex.exp (y.1 ^ 2) * (y.1 - 1)).smul
      (L.continuous.comp Ψ.continuous)
  · obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds g
    obtain ⟨M, hM⟩ := hΦ.strip b a (U * (K : Set G)) (hUc.mul hK)
    obtain ⟨M2, hM2, hg⟩ := gauss_bound b a
    refine ⟨U, hU, ‖L‖ * |M| * M2, fun z h1 h2 g' hg' => ?_⟩
    rw [hA, norm_smul]
    have hΨ : ‖Ψ (z, g')‖ ≤ |M| * (1 + ‖z‖) ^ 2 := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun κ => ?_
      have h := hM z h1 h2 (g' * κ) (Set.mul_mem_mul hg' κ.2)
      exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity))
    calc ‖Complex.exp (z ^ 2) * (z - 1)‖ * ‖L (Ψ (z, g'))‖
        ≤ ‖Complex.exp (z ^ 2) * (z - 1)‖ * (‖L‖ * (|M| * (1 + ‖z‖) ^ 2)) :=
          mul_le_mul_of_nonneg_left ((L.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left hΨ (norm_nonneg _))) (norm_nonneg _)
      _ = ‖L‖ * |M| * (‖Complex.exp (z ^ 2) * (z - 1)‖ * (1 + ‖z‖) ^ 2) := by ring
      _ ≤ ‖L‖ * |M| * M2 := mul_le_mul_of_nonneg_left (hg z h1 h2) (by positivity)

end GlobalTheory.CompanionTheory.RgEisHGood
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionGoodStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_section_good : PositivityTheory.RgEis.StdGood := by
  first | exact @GlobalTheory.CompanionTheory.StdGoodAd.stdGood | exact GlobalTheory.CompanionTheory.StdGoodAd.stdGood | (intros; apply GlobalTheory.CompanionTheory.StdGoodAd.stdGood <;> assumption)
end

