import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0035
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0041
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0028

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowDegreeGeoNum
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime geoNum divSupp multAt)

theorem perfectField_of_intCast_surjective (F : Type) [Field F] (p : ℕ) (hp : p.Prime)
    (hs : Function.Surjective (Int.castRingHom F)) (h0 : ((p : ℤ) : F) = 0) : PerfectField F := by
  have := Fact.mk hp
  have : CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr (by exact_mod_cast h0)
  have hcomp : (ZMod.castHom (dvd_refl p) F).comp (Int.castRingHom (ZMod p)) = Int.castRingHom F :=
    RingHom.ext_int _ _
  have hsurj : Function.Surjective (ZMod.castHom (dvd_refl p) F) := by
    refine Function.Surjective.of_comp (g := Int.castRingHom (ZMod p)) ?_
    rw [← RingHom.coe_comp, hcomp]
    exact hs
  have : Finite F := Finite.of_surjective _ hsurj
  infer_instance

theorem linForm_single {F : Type} [Field F] {n : ℕ} (i : Fin n) : linForm (Pi.single i (1 : F)) = X i := by
  simp [linForm, Pi.single_apply]

theorem isMultiHomog_X {n : ℕ} (i : Fin n) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨(), i⟩ : MRing (PBlk n)) (fun _ => 1) := by
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hj (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
  · simp

theorem divSupp_X {n e : ℕ} {W W' : Ideal (MRing (PBlk n))} {i : Fin n} (hW : IsMultiProjPrime W)
    (hdim : ringKrullDim (MRing (PBlk n) ⧸ W) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞))
    (hi : (X ⟨(), i⟩ : MRing (PBlk n)) ∉ W) (hW' : W' ∈ divSupp W (X ⟨(), i⟩)) :
    IsMultiProjPrime W' ∧ W ≤ W' ∧ ringKrullDim (MRing (PBlk n) ⧸ W') = ((e + 1 : ℕ) : WithBot ℕ∞) := by
  have := hW.1
  refine ⟨⟨hW'.1.1.1, ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_of_mem_minimalPrimes hW.2.1 (isMultiHomog_X i)
    hW'.1, hW'.2⟩, le_sup_left.trans hW'.1.1.2, ?_⟩
  exact ReciprocityTheory.ChartRestriction.G.Geo.withBot_eq_of_add_one
    ((ReciprocityTheory.ChartRestriction.G.Geo.dim_quot_minimal_add_one W W' _ hi hW'.1).trans hdim)

theorem ChowDegreeGeoNum.proof (hS : ChowDegreeSection.Statement) (hP : ChowDegreeClosedPoint.Statement)
    (hR : ReductionModP.Statement) (hC : SectionCycleModP.Statement) (hL : PointLengthModP.Statement) :
    ChowDegreeGeoNum.Statement := by
  intro n e p W F _ hp hW hpW hdim hsurj h0
  have := perfectField_of_intCast_surjective F p hp hsurj h0
  induction e generalizing W with
  | zero =>
    obtain ⟨hI, hIdim, hX⟩ := hR n p W F hp hW hpW hsurj h0
    have hrel := hW.2.2
    have hiW : (X ⟨(), (hrel ()).choose⟩ : MRing (PBlk n)) ∉ W := (hrel ()).choose_spec
    have hpt := hP F n _ (hrel ()).choose hI (hIdim.trans hdim) (by rwa [hX])
    rw [geoNum, dif_pos hrel]
    have hrange : Set.range (fun k : Unit => (X ⟨k, (hrel k).choose⟩ : MRing (PBlk n)) - 1) =
        {(X ⟨(), (hrel ()).choose⟩ : MRing (PBlk n)) - 1} := by
      rw [Set.range_unique]
    rw [hrange, hL n p W F hp hW hpW hsurj h0 (hrel ()).choose]
    exact_mod_cast hpt
  | succ e ih =>
    obtain ⟨hI, hIdim, hX⟩ := hR n p W F hp hW hpW hsurj h0
    have hrel := hW.2.2
    have hiW : (X ⟨(), (hrel ()).choose⟩ : MRing (PBlk n)) ∉ W := (hrel ()).choose_spec
    have hXi : linForm (Pi.single (hrel ()).choose (1 : F)) ∉
        (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F)) := by
      rw [linForm_single, hX]
      exact hiW
    have hsec := hS F n e _ _ hI (hIdim.trans hdim) hXi
    rw [hC n p W F hp hW hpW hsurj h0 _ hiW,
      Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)] at hsec
    show (chowDegree _ (e + 2) : ℤ) = _
    rw [hsec, geoNum, dif_pos hrel]
    simp only [Fintype.sum_unique, one_mul, Finsupp.sum, Nat.cast_sum, Nat.cast_mul]
    have hfin := ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite W (X ⟨(), (hrel ()).choose⟩ : MRing (PBlk n))
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    classical
    have hval : ∀ W', ReciprocityTheory.ChartRestriction.G.Geo.divCycle W (X ⟨(), (hrel ()).choose⟩) W' =
        if W' ∈ divSupp W (X ⟨(), (hrel ()).choose⟩) then
          multAt (W ⊔ Ideal.span {(X ⟨(), (hrel ()).choose⟩ : MRing (PBlk n))}) W' else 0 := by
      intro W'
      simp [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
    refine Finset.sum_subset (fun W' hW' => ?_) (fun W' _ hW' => ?_) |>.trans (Finset.sum_congr rfl ?_)
    · rw [Set.Finite.mem_toFinset]
      by_contra h
      exact Finsupp.mem_support_iff.mp hW' (by rw [hval, if_neg h])
    · rw [Finsupp.notMem_support_iff.mp hW', Nat.cast_zero, zero_mul]
    · intro W' hW'
      rw [Set.Finite.mem_toFinset] at hW'
      obtain ⟨hW'p, hle, hW'dim⟩ := divSupp_X hW hdim hiW hW'
      rw [hval, if_pos hW', ih W' hW'p (hle hpW) hW'dim]
      rfl

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSheetArea
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)

open scoped ENNReal ComplexOrder

theorem gramVol_nonneg {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    0 ≤ gramVol v y := by
  unfold gramVol
  dsimp only
  set w : Fin (e + 1) → Fin n → ℂ := Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1)
  have hM : (Matrix.of fun a b => ∑ i, star (w a i) * w b i) =
      (Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i)ᴴ *
        Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have h := (Matrix.posSemidef_conjTranspose_mul_self
    (Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i)).det_nonneg
  rw [← hM] at h
  exact (Complex.nonneg_iff.1 h).1

theorem enorm_mul_eq_ofReal_add {a r : ℝ} (hr : 0 ≤ r) :
    ‖a * r‖ₑ = ENNReal.ofReal a * ENNReal.ofReal r + ENNReal.ofReal (-a) * ENNReal.ofReal r := by
  rw [← ofReal_norm, Real.norm_eq_abs, abs_mul, abs_of_nonneg hr, ← add_mul,
    ENNReal.ofReal_mul (abs_nonneg a)]
  congr 1
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha, ENNReal.ofReal_of_nonpos (by linarith : -a ≤ 0), add_zero]
  · rw [abs_of_nonpos ha, ENNReal.ofReal_of_nonpos ha, zero_add]

section Abstract

variable {E X W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_smul_mul_eq_toReal_sub {f : E → ℝ} (hf : Measurable f) (v : E) {ρ : ℂ → ℝ}
    (hρ : ∀ t, 0 ≤ ρ t) (hρc : Continuous ρ)
    (hp : ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v)) * ENNReal.ofReal (ρ t) ≠ ⊤)
    (hm : ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v)) * ENNReal.ofReal (ρ t) ≠ ⊤) :
    ∫ t : ℂ, f (t • v) * ρ t =
      (∫⁻ t : ℂ, ENNReal.ofReal (f (t • v)) * ENNReal.ofReal (ρ t)).toReal -
        (∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v)) * ENNReal.ofReal (ρ t)).toReal := by
  have hfv : Measurable fun t : ℂ => f (t • v) :=
    hf.comp (continuous_id.smul continuous_const).measurable
  have hint : Integrable (fun t : ℂ => f (t • v) * ρ t) := by
    refine ⟨(hfv.mul hρc.measurable).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ t : ℂ, ‖f (t • v) * ρ t‖ₑ
        = ∫⁻ t : ℂ, (ENNReal.ofReal (f (t • v)) * ENNReal.ofReal (ρ t) +
            ENNReal.ofReal (-f (t • v)) * ENNReal.ofReal (ρ t)) :=
          lintegral_congr fun t => enorm_mul_eq_ofReal_add (hρ t)
      _ = (∫⁻ t : ℂ, ENNReal.ofReal (f (t • v)) * ENNReal.ofReal (ρ t)) +
            ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v)) * ENNReal.ofReal (ρ t) :=
          lintegral_add_left ((ENNReal.measurable_ofReal.comp hfv).mul
            (ENNReal.measurable_ofReal.comp hρc.measurable)) _
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hp.lt_top, hm.lt_top⟩
  have key : ∀ (a : ℝ) (t : ℂ), ENNReal.ofReal (a * ρ t) = ENNReal.ofReal a * ENNReal.ofReal (ρ t) :=
    fun a t => ENNReal.ofReal_mul' (hρ t)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
  simp_rw [← neg_mul, key]

theorem finsum_integral_smul_mul_eq_toReal_sub {f : E → ℝ} (hf : Measurable f) {T : Set W}
    (hT : T.Finite) (v : W → E) (ρ : W → ℂ → ℝ) (hρ : ∀ w t, 0 ≤ ρ w t)
    (hρc : ∀ w, Continuous (ρ w))
    (hp : ∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v w)) * ENNReal.ofReal (ρ w t) ≠ ⊤)
    (hm : ∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v w)) * ENNReal.ofReal (ρ w t) ≠ ⊤) :
    ∑ᶠ w ∈ T, ∫ t : ℂ, f (t • v w) * ρ w t =
      (∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v w)) * ENNReal.ofReal (ρ w t)).toReal -
        (∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v w)) * ENNReal.ofReal (ρ w t)).toReal := by
  simp only [finsum_mem_eq_finite_toFinset_sum _ hT] at hp hm ⊢
  have hp' := fun w (hw : w ∈ hT.toFinset) =>
    ne_top_of_le_ne_top hp (Finset.single_le_sum (fun _ _ => zero_le) hw)
  have hm' := fun w (hw : w ∈ hT.toFinset) =>
    ne_top_of_le_ne_top hm (Finset.single_le_sum (fun _ _ => zero_le) hw)
  rw [ENNReal.toReal_sum hp', ENNReal.toReal_sum hm', ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun w hw =>
    integral_smul_mul_eq_toReal_sub hf (v w) (hρ w) (hρc w) (hp' w hw) (hm' w hw)

variable [MeasurableSpace X]

theorem mul_setIntegral_eq_of_lintegral_of_measurable {μ : Measure E} {ν : Measure X} {C : Set E}
    {fib : X → Set W} (hfin : ∀ x, (fib x).Finite) (v : X → W → E) (ρ : X → W → ℂ → ℝ)
    (hρ : ∀ x w t, 0 ≤ ρ x w t) (hρc : ∀ x w, Continuous (ρ x w))
    {c : ℝ} (hc : 0 ≤ c) {b : ℝ≥0∞} (hb : b ≠ 0)
    (hA : ∀ F : E → ℝ≥0∞, Measurable F →
      AEMeasurable (fun x => ∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, F (t • v x w) * ENNReal.ofReal (ρ x w t)) ν ∧
      ENNReal.ofReal c * ∫⁻ y in C, F y ∂μ =
        b * ∫⁻ x, (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, F (t • v x w) * ENNReal.ofReal (ρ x w t)) ∂ν)
    {f : E → ℝ} (hfm : Measurable f) (hf : IntegrableOn f C μ) :
    c * ∫ y in C, f y ∂μ =
      b.toReal * ∫ x, (∑ᶠ w ∈ fib x, ∫ t : ℂ, f (t • v x w) * ρ x w t) ∂ν := by
  obtain ⟨hGpm, hAp⟩ := hA (fun y => ENNReal.ofReal (f y)) (ENNReal.measurable_ofReal.comp hfm)
  obtain ⟨hGmm, hAm⟩ := hA (fun y => ENNReal.ofReal (-f y))
    (ENNReal.measurable_ofReal.comp hfm.neg)
  have hCp : ∫⁻ y in C, ENNReal.ofReal (f y) ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hf.2).ne
  have hCm : ∫⁻ y in C, ENNReal.ofReal (-f y) ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hf.neg.2).ne
  have hIp : ∫⁻ x, (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v x w)) *
      ENNReal.ofReal (ρ x w t)) ∂ν ≠ ⊤ := by
    have h1 : ENNReal.ofReal c * ∫⁻ y in C, ENNReal.ofReal (f y) ∂μ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCp
    rw [hAp] at h1
    exact fun h2 => h1 (by rw [h2, ENNReal.mul_top hb])
  have hIm : ∫⁻ x, (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v x w)) *
      ENNReal.ofReal (ρ x w t)) ∂ν ≠ ⊤ := by
    have h1 : ENNReal.ofReal c * ∫⁻ y in C, ENNReal.ofReal (-f y) ∂μ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCm
    rw [hAm] at h1
    exact fun h2 => h1 (by rw [h2, ENNReal.mul_top hb])
  have hae : (fun x => ∑ᶠ w ∈ fib x, ∫ t : ℂ, f (t • v x w) * ρ x w t) =ᵐ[ν] fun x =>
      (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v x w)) * ENNReal.ofReal (ρ x w t)).toReal -
        (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v x w)) *
          ENNReal.ofReal (ρ x w t)).toReal := by
    filter_upwards [ae_lt_top' hGpm hIp, ae_lt_top' hGmm hIm] with x hxp hxm
    exact finsum_integral_smul_mul_eq_toReal_sub hfm (hfin x) (v x) (ρ x) (hρ x) (hρc x)
      hxp.ne hxm.ne
  rw [integral_congr_ae hae, integral_sub (integrable_toReal_of_lintegral_ne_top hGpm hIp)
    (integrable_toReal_of_lintegral_ne_top hGmm hIm), integral_toReal hGpm (ae_lt_top' hGpm hIp),
    integral_toReal hGmm (ae_lt_top' hGmm hIm), integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
    mul_sub, ← ENNReal.toReal_ofReal_mul c _ hc, ← ENNReal.toReal_ofReal_mul c _ hc, hAp, hAm,
    ENNReal.toReal_mul, ENNReal.toReal_mul, mul_sub]

theorem mul_setIntegral_eq_of_lintegral {μ : Measure E} {ν : Measure X} {C : Set E}
    {fib : X → Set W} (hfin : ∀ x, (fib x).Finite) (v : X → W → E) (ρ : X → W → ℂ → ℝ)
    (hρ : ∀ x w t, 0 ≤ ρ x w t) (hρc : ∀ x w, Continuous (ρ x w))
    {c : ℝ} (hc : 0 ≤ c) {b : ℝ≥0∞} (hb : b ≠ 0)
    (hA : ∀ F : E → ℝ≥0∞, Measurable F →
      AEMeasurable (fun x => ∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, F (t • v x w) * ENNReal.ofReal (ρ x w t)) ν ∧
      ENNReal.ofReal c * ∫⁻ y in C, F y ∂μ =
        b * ∫⁻ x, (∑ᶠ w ∈ fib x, ∫⁻ t : ℂ, F (t • v x w) * ENNReal.ofReal (ρ x w t)) ∂ν)
    {f : E → ℝ} (hf : IntegrableOn f C μ) :
    c * ∫ y in C, f y ∂μ =
      b.toReal * ∫ x, (∑ᶠ w ∈ fib x, ∫ t : ℂ, f (t • v x w) * ρ x w t) ∂ν := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hf.1.ae_eq_mk)
  obtain ⟨hG0m, hA0⟩ := hA (N.indicator 1) (measurable_one.indicator hNm)
  rw [lintegral_indicator_one hNm, hN0, mul_zero, eq_comm, mul_eq_zero, or_iff_right hb,
    lintegral_eq_zero_iff' hG0m] at hA0
  have hae : (fun x => ∑ᶠ w ∈ fib x, ∫ t : ℂ, f (t • v x w) * ρ x w t) =ᵐ[ν]
      fun x => ∑ᶠ w ∈ fib x, ∫ t : ℂ, hf.1.mk f (t • v x w) * ρ x w t := by
    filter_upwards [hA0] with x hx
    refine finsum_mem_congr rfl fun w hw => integral_congr_ae ?_
    have hx' : ∫⁻ t : ℂ, N.indicator 1 (t • v x w) * ENNReal.ofReal (ρ x w t) = 0 := by
      simp only [Pi.zero_apply, finsum_mem_eq_finite_toFinset_sum _ (hfin x),
        Finset.sum_eq_zero_iff] at hx
      exact hx w ((hfin x).mem_toFinset.2 hw)
    have hm : Measurable fun t : ℂ => N.indicator 1 (t • v x w) * ENNReal.ofReal (ρ x w t) :=
      ((measurable_one.indicator hNm).comp (continuous_id.smul continuous_const).measurable).mul
        (ENNReal.measurable_ofReal.comp (hρc x w).measurable)
    rw [lintegral_eq_zero_iff' hm.aemeasurable] at hx'
    filter_upwards [hx'] with t ht
    rcases mul_eq_zero.1 ht with h | h
    · have hy : t • v x w ∉ N := by
        intro hy
        simp [Set.indicator_of_mem hy] at h
      have : f (t • v x w) = hf.1.mk f (t • v x w) := by
        by_contra hne
        exact hy (hsub hne)
      rw [this]
    · rw [ENNReal.ofReal_eq_zero] at h
      rw [le_antisymm h (hρ x w t), mul_zero, mul_zero]
  rw [integral_congr_ae hf.1.ae_eq_mk, integral_congr_ae hae]
  exact mul_setIntegral_eq_of_lintegral_of_measurable hfin v ρ hρ hρc hc hb hA
    hf.1.stronglyMeasurable_mk.measurable (hf.congr hf.1.ae_eq_mk)

end Abstract

theorem ConeSheetArea.proof (h : ConeSheetAreaLintegral.Statement) : ConeSheetArea.Statement := by
  intro n e S hS P Ψ f hP hΨ hf
  obtain ⟨hb0, -⟩ := coordBall_mass (n := n) (m := e + 1) (le_of_isArithVar_pblk hP)
  exact mul_setIntegral_eq_of_lintegral
    (fun x => ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite Unit (PBlk n) P e Ψ hP hΨ x)
    (fun x w => WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩))
    (fun x w t => ‖t‖ ^ (2 * e) *
      gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x)
    (fun x w t => mul_nonneg (pow_nonneg (norm_nonneg t) _) (gramVol_nonneg _ x))
    (fun x w => (continuous_norm.pow _).mul continuous_const)
    (by positivity) hb0.ne' (fun F hF => h n e S hS P Ψ F hP hΨ hF) hf

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSheetAreaLintegral
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre)

open scoped ENNReal

theorem gramVol_congr {e n : ℕ} {v v' : (Fin e → ℂ) → (Fin n → ℂ)} {y : Fin e → ℂ}
    (h : v =ᶠ[𝓝 y] v') : gramVol v y = gramVol v' y := by
  unfold gramVol
  rw [h.eq_of_nhds, h.fderiv_eq]

def gramForm {e n : ℕ} (p : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ))) : ℝ :=
  let w : Fin (e + 1) → Fin n → ℂ := Fin.cons p.1 fun j => p.2 (Pi.single j 1)
  (Matrix.det (Matrix.of fun a b => ∑ i, star (w a i) * w b i)).re

theorem gramVol_eq_gramForm {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    gramVol v y = gramForm (v y, fderiv ℂ v y) := rfl

theorem continuous_gramForm {e n : ℕ} :
    Continuous (gramForm : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ)) → ℝ) := by
  have hw : Continuous fun p : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ)) =>
      (Fin.cons p.1 fun j => p.2 (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) := by
    refine continuous_pi fun a => ?_
    refine Fin.cases ?_ (fun j => ?_) a
    · simpa using continuous_fst
    · simpa using continuous_snd.clm_apply continuous_const
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((continuous_apply i).comp ((continuous_apply a).comp hw)).star.mul
    ((continuous_apply i).comp ((continuous_apply b).comp hw))

theorem aemeasurable_coneTerm {e n : ℕ} {U D : Set (Fin e → ℂ)} {v : (Fin e → ℂ) → (Fin n → ℂ)}
    {F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞} (hU : IsOpen U) (hDU : D ⊆ U)
    (hv : DifferentiableOn ℂ v U) (hF : Measurable F) :
    AEMeasurable (fun x => ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v x)) *
      ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol v x)) (volume.restrict D) := by
  have ha : AEMeasurable v (volume.restrict D) :=
    (hv.continuousOn.aemeasurable hU.measurableSet).mono_measure (Measure.restrict_mono hDU le_rfl)
  have hg : AEMeasurable (fun x => gramVol v x) (volume.restrict D) := by
    have h := continuous_gramForm.measurable.comp_aemeasurable
      (ha.prodMk (measurable_fderiv ℂ v).aemeasurable)
    simpa only [Function.comp_def, ← gramVol_eq_gramForm] using h
  have hmeas : Measurable fun p : (Fin e → ℂ) × ℂ => F (p.2 • WithLp.toLp 2 (ha.mk v p.1)) *
      ENNReal.ofReal (‖p.2‖ ^ (2 * e) * hg.mk _ p.1) := by
    refine (hF.comp (measurable_snd.smul ((PiLp.continuous_toLp 2 _).measurable.comp
      (ha.measurable_mk.comp measurable_fst)))).mul ?_
    exact ENNReal.measurable_ofReal.comp
      ((measurable_snd.norm.pow_const _).mul (hg.measurable_mk.comp measurable_fst))
  refine ⟨_, hmeas.lintegral_prod_right' (ν := (volume : Measure ℂ)), ?_⟩
  filter_upwards [ha.ae_eq_mk, hg.ae_eq_mk] with x h1 h2
  simp only [h1, h2]

theorem ConeSheetAreaLintegral.proof (hPar : ConeSheetParam.Statement)
    (hArea : ConeMapArea.Statement) : ConeSheetAreaLintegral.Statement := by
  classical
  intro n e S hS P Ψ F hP hΨ hF
  obtain ⟨U, D, N, s, hUD, hdisj, hnull, hfib, hinj, hsub, hcov⟩ := hPar n e S hS P Ψ hP hΨ

  set v : (Σ k, Fin (N k)) → (Fin e → ℂ) → (Fin n → ℂ) :=
    fun i x => S *ᵥ fun p => s i.1 i.2 x ⟨(), p⟩ with hv_def
  have hvd : ∀ i : Σ k, Fin (N k), DifferentiableOn ℂ (v i) (U i.1) := by
    intro i
    have h1 : DifferentiableOn ℂ (fun x => fun p : Fin n => s i.1 i.2 x ⟨(), p⟩) (U i.1) :=
      differentiableOn_pi.2 fun p => differentiableOn_pi.1 ((hUD i.1).2.2.2 i.2) ⟨(), p⟩
    exact (Matrix.mulVecLin S).toContinuousLinearMap.differentiable.comp_differentiableOn h1

  set H : (Σ k, Fin (N k)) → (Fin e → ℂ) → ℝ≥0∞ := fun i x =>
    ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v i x)) * ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (v i) x)
    with hH_def
  have hHm : ∀ i : Σ k, Fin (N k), AEMeasurable (H i) (volume.restrict (D i.1)) := fun i =>
    aemeasurable_coneTerm (hUD i.1).1 (hUD i.1).2.2.1 (hvd i) hF

  set G : (Fin e → ℂ) → ℝ≥0∞ := fun x => ∑ᶠ w ∈ fibre P Ψ x, ∫⁻ t : ℂ,
      F (t • WithLp.toLp 2 (S *ᵥ fun i => chosenSheet P Ψ x w x ⟨(), i⟩)) *
        ENNReal.ofReal (‖t‖ ^ (2 * e) *
          gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x w x' ⟨(), i⟩) x) with hG_def

  have hGD : ∀ k, ∀ x ∈ D k, G x = ∑ j : Fin (N k), H ⟨k, j⟩ x := by
    intro k x hx
    obtain ⟨hfe, hinjx, hsh⟩ := hfib k x ((hUD k).2.2.1 hx)
    simp only [hG_def, hfe]
    rw [finsum_mem_range hinjx, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hex : ∃ γ, IsSheet P Ψ x (segre (s k j x)) γ := ⟨s k j, (hsh j).1⟩
    have hch : chosenSheet P Ψ x (segre (s k j x)) =ᶠ[𝓝 x] s k j := by
      have : chosenSheet P Ψ x (segre (s k j x)) = hex.choose := by
        simp only [chosenSheet, dif_pos hex]
      rw [this]
      exact (hsh j).2 _ hex.choose_spec
    have hval : chosenSheet P Ψ x (segre (s k j x)) x = s k j x := hch.eq_of_nhds
    have hgram : gramVol (fun x' => S *ᵥ fun i => chosenSheet P Ψ x (segre (s k j x)) x' ⟨(), i⟩) x =
        gramVol (v ⟨k, j⟩) x :=
      gramVol_congr (hch.fun_comp fun f => S *ᵥ fun i => f ⟨(), i⟩)
    simp only [hH_def, hv_def, hval, hgram]

  set G' : (Fin e → ℂ) → ℝ≥0∞ := fun x =>
    ∑' k, (D k).indicator (fun x => ∑ j : Fin (N k), H ⟨k, j⟩ x) x with hG'_def
  have hGG' : G =ᵐ[volume] G' := by
    have hae : ∀ᵐ x ∂(volume : Measure (Fin e → ℂ)), x ∈ ⋃ k, D k := by
      rw [ae_iff]
      simpa [compl_def] using hnull
    filter_upwards [hae] with x hx
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    simp only [hG'_def]
    rw [tsum_eq_single k, indicator_of_mem hk, hGD k x hk]
    intro k' hk'
    exact indicator_of_notMem (fun h => (hdisj hk').le_bot ⟨h, hk⟩) _
  have hG'm : ∀ k, AEMeasurable ((D k).indicator fun x => ∑ j : Fin (N k), H ⟨k, j⟩ x) volume :=
    fun k => (aemeasurable_indicator_iff (hUD k).2.1).2
      (Finset.aemeasurable_fun_sum _ fun j _ => hHm ⟨k, j⟩)
  refine ⟨(AEMeasurable.tsum hG'm).congr hGG'.symm, ?_⟩

  have hRHS : ∫⁻ x, G x = ∑' i : Σ k, Fin (N k), ∫⁻ x in D i.1, H i x := by
    rw [lintegral_congr_ae hGG', lintegral_tsum hG'm, ENNReal.tsum_sigma']
    refine tsum_congr fun k => ?_
    rw [lintegral_indicator (hUD k).2.1, lintegral_finsetSum' _ fun j _ => hHm ⟨k, j⟩,
      tsum_fintype]

  have hLHS : ∫⁻ y in coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P), F y
        ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      ∫⁻ y in (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0}, F y
        ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    refine setLIntegral_congr (ae_eq_set.2 ⟨hcov, ?_⟩)
    rw [sdiff_eq_empty.2 hsub, measure_empty]
  have hA := hArea n e (Σ k, Fin (N k)) (fun i => U i.1) (fun i => D i.1) v F
    (fun i => ⟨(hUD i.1).1, (hUD i.1).2.1, (hUD i.1).2.2.1, hvd i⟩) hinj hF
  rw [hLHS, hA]
  exact congrArg _ hRHS.symm

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDivSuppHorizontalArithVar
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp Xc)

theorem isMultiHomog_linForm {n : ℕ} (u : Fin n → ℤ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (fun _ => 1) := by
  classical
  intro m hm k
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at hi
  have hmi := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hi)
  subst hmi
  cases k
  simp [Finsupp.single_apply]

theorem DivSuppHorizontalArithVar.proof : DivSuppHorizontalArithVar.Statement := by
  intro n d P u H hP hu hH hHor
  obtain ⟨hK, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  obtain ⟨hHmin, hHrel⟩ := hH
  have := hPp
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.dim_quot_minimal_add_one P H _ hu hHmin
  rw [hPdim] at h1
  refine ⟨hK, ⟨hHmin.1.1, ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_of_mem_minimalPrimes hPh
    (isMultiHomog_linForm u) hHmin, hHrel⟩, hHor,
    ReciprocityTheory.ChartRestriction.G.Geo.withBot_eq_of_add_one ?_⟩
  rw [h1, show d + 1 + Fintype.card Unit = d + Fintype.card Unit + 1 by omega]

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

