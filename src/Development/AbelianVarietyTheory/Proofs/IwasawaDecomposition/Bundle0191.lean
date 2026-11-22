import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0082
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.AdeleCharTwist

theorem exists_eq_exp (g : ℝ → ℂ) (hc : Continuous g) (hn : ∀ t, ‖g t‖ = 1) (h0 : g 0 = 1)
    (hadd : ∀ s t, g (s + t) = g s * g t) :
    ∃ c : ℝ, ∀ t : ℝ, g t = Complex.exp (2 * Real.pi * Complex.I * ((c * t : ℝ) : ℂ)) := by
  have hm : ∀ a, g a ∈ Submonoid.unitSphere ℂ := fun a => by simpa [Submonoid.unitSphere] using hn a
  let χ : C(ℝ, Circle) := ⟨fun a => ⟨g a, hm a⟩, hc.subtype_mk hm⟩
  have hχ : ∀ s t, χ (s + t) = χ s * χ t := fun s t => Subtype.ext (hadd s t)
  obtain ⟨L, ⟨hL0, hL⟩, hu⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts χ 0 0
    (by rw [Circle.exp_zero]; exact Subtype.ext h0.symm)
  have hL' : ∀ t, Circle.exp (L t) = χ t := congrFun hL
  have hLa : ∀ s t, L (s + t) = L s + L t := fun s t => by
    have := hu ⟨fun t => L (s + t) - L s, by fun_prop⟩ ⟨by simp, by
      funext t
      show Circle.exp (L (s + t) - L s) = χ t
      rw [Circle.exp_sub, hL', hL', hχ, mul_div_cancel_left]⟩
    have h2 : L (s + t) - L s = L t := DFunLike.congr_fun this t
    linarith
  let l : ℝ →+ ℝ := AddMonoidHom.mk' L hLa
  refine ⟨L 1 / (2 * Real.pi), fun t => ?_⟩
  have h3 : L t = t * L 1 := by
    have := map_real_smul l L.continuous t 1
    simpa [l] using this
  have h4 : g t = (Circle.exp (L t) : ℂ) := by rw [hL']; rfl
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [h4, Circle.coe_exp, h3]
  congr 1
  push_cast
  field_simp

variable {F : Type} [Field F] [NumberField F]

theorem pairA_add (x x' : Ainf F) (y y' : Af F) :
    pairA F (x + x') (y + y') = pairA F x y + pairA F x' y' := rfl

theorem algebraMap_eq_pairA (x : F) :
    algebraMap F (AF F) x = pairA F (algebraMap F _ x) 0 + pairA F 0 (algebraMap F _ x) := by
  rw [← pairA_add, add_zero, zero_add]
  rfl

theorem denseRange_fin : DenseRange (algebraMap F (Af F)) := by
  intro y
  rw [mem_closure_iff_nhds]
  intro U hU
  have hc : Continuous fun z : Af F => y - z := continuous_const.sub continuous_id
  have hV : (fun z : Af F => y - z) ⁻¹' U ∈ 𝓝 (0 : Af F) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV
  obtain ⟨a, β, hβ, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).1 y
  refine ⟨y - N • β, hNU β hβ, a, ?_⟩
  rw [e, add_sub_cancel_right]

theorem ext_of_inf {ψ ψ' : AF F → ℂ} (hc : Continuous ψ) (hc' : Continuous ψ')
    (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (ha' : ∀ x y, ψ' (x + y) = ψ' x * ψ' y)
    (hr : ∀ a : F, ψ (algebraMap F _ a) = 1) (hr' : ∀ a : F, ψ' (algebraMap F _ a) = 1)
    (h : ∀ a : F, ψ (pairA F (algebraMap F _ a) 0) = ψ' (pairA F (algebraMap F _ a) 0)) (x : AF F) :
    ψ x = ψ' x := by
  have h1 : (fun z => ψ (pairA F z 0)) = fun z => ψ' (pairA F z 0) :=
    (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      (hc.comp (continuous_id.prodMk continuous_const)) (hc'.comp (continuous_id.prodMk continuous_const))
      (funext h)
  have h2 : (fun z => ψ (pairA F 0 z)) = fun z => ψ' (pairA F 0 z) :=
    denseRange_fin.equalizer
      (hc.comp (continuous_const.prodMk continuous_id)) (hc'.comp (continuous_const.prodMk continuous_id))
      (funext fun a => by
        have e := hr a
        have e' := hr' a
        rw [algebraMap_eq_pairA, ha, h] at e
        rw [algebraMap_eq_pairA, ha'] at e'
        exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one e) (e.trans e'.symm))
  have e : x = pairA F x.1 0 + pairA F 0 x.2 := by
    rw [← pairA_add, add_zero, zero_add]
    rfl
  rw [e, ha, ha', congrFun h1, congrFun h2]

theorem exists_nsmul_inf {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ N : ℕ, 0 < N ∧ ∀ r : 𝓞 F, ψ (pairA F (algebraMap F _ ((N : F) * r)) 0) = 1 := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (GlobalTheory.FinTranslate.ker_mem_nhds hψ.1 hψ.2.1)
  refine ⟨N, hN, fun r => ?_⟩
  have h1 : ψ (pairA F 0 (N • algebraMap F (Af F) r)) = 1 :=
    h _ fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v r
  have h2 := hψ.2.2.1 ((N : F) * r)
  rw [nsmul_eq_mul, ← map_natCast (algebraMap F (Af F)), ← map_mul] at h1
  rwa [algebraMap_eq_pairA, AddChar.map_add_eq_mul, h1, mul_one] at h2

theorem exists_realHom [IsTotallyReal F] : ∃ ρ : ℝ →+* Ainf F, Continuous ρ := by
  let e : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ := fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  exact ⟨Pi.ringHom fun w => (e w).symm.toRingHom, continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous⟩

theorem exists_trace [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ a : F, ∀ x : F, ψ (pairA F (algebraMap F _ x) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (a * x) : ℚ) : ℂ)) := by
  classical
  obtain ⟨N, hN, hNr⟩ := exists_nsmul_inf hψ
  obtain ⟨ρ, hρ⟩ := exists_realHom (F := F)
  have hρq : ∀ q : ℚ, ρ (q : ℝ) = algebraMap F (Ainf F) (q : F) := fun q =>
    RingHom.congr_fun (RingHom.ext_rat (ρ.comp (Rat.castHom ℝ)) ((algebraMap F (Ainf F)).comp (Rat.castHom F))) q
  have hadd : ∀ x y : Ainf F, ψ (pairA F (x + y) 0) = ψ (pairA F x 0) * ψ (pairA F y 0) := fun x y => by
    rw [← AddChar.map_add_eq_mul, ← pairA_add, add_zero]
  have h0 : ψ (pairA F 0 0) = 1 := ψ.map_zero_eq_one
  have key : ∀ r : 𝓞 F, ∃ c : ℚ, ∀ q : ℚ, ψ (pairA F (algebraMap F _ (q • (r : F))) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((q * c : ℚ) : ℂ)) := fun r => by
    obtain ⟨c, hc⟩ := exists_eq_exp (fun t => ψ (pairA F (ρ t * algebraMap F _ (r : F)) 0))
      (hψ.1.comp ((hρ.mul continuous_const).prodMk continuous_const)) (fun t => hψ.2.1 _)
      (by simp only [map_zero, zero_mul, h0]) (fun s t => by simp only [map_add, add_mul, hadd])
    have hq : ∀ q : ℚ, ψ (pairA F (algebraMap F _ ((q : F) * (r : F))) 0) =
        Complex.exp (2 * Real.pi * Complex.I * ((c * q : ℝ) : ℂ)) := fun q => by
      rw [← hc, hρq, map_mul]
    have h1 := hq N
    rw [Rat.cast_natCast, hNr, eq_comm, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero] at hn
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    refine ⟨n / N, fun q => ?_⟩
    rw [Rat.smul_def, hq]
    congr 2
    push_cast at hn ⊢
    rw [← hn]
    field_simp
  choose c hc using key
  let b := integralBasis F
  let φ : F →ₗ[ℚ] ℚ := b.constr ℚ fun i => c (RingOfIntegers.basis F i)
  obtain ⟨a, ha⟩ := ((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).surjective φ
  have ha' : ∀ x, Algebra.trace ℚ F (a * x) = φ x := fun x => by
    rw [← ha]; rfl
  refine ⟨a, fun x => ?_⟩
  rw [ha', ← b.sum_repr x]
  refine Finset.sum_induction _ (fun y : F => ψ (pairA F (algebraMap F _ y) 0) =
    Complex.exp (2 * Real.pi * Complex.I * ((φ y : ℚ) : ℂ))) (fun y z hy hz => ?_) ?_ fun i _ => ?_
  · rw [map_add, hadd, hy, hz, map_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp only [map_zero, h0, Rat.cast_zero, mul_zero, Complex.exp_zero]
  · rw [map_smul φ, Module.Basis.constr_basis, smul_eq_mul, ← hc, integralBasis_apply]

theorem trace_mul_ne_zero {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) {a : F}
    (h : ∀ x : F, ψ (pairA F (algebraMap F _ x) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (a * x) : ℚ) : ℂ))) : a ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := hψ.2.2.2
  refine hx (ext_of_inf (ψ' := fun _ => 1) hψ.1 continuous_const ψ.map_add_eq_mul (fun _ _ => by simp)
    hψ.2.2.1 (fun _ => rfl) (fun y => by simp [h]) x)

theorem exists_mul_eq : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ ψ' : AddChar (AF F) ℂ), IsCharAF F ψ → IsCharAF F ψ' → ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x) := by
  intro F _ _ _ ψ ψ' hψ hψ'
  obtain ⟨a, ha⟩ := exists_trace hψ
  obtain ⟨a', ha'⟩ := exists_trace hψ'
  have h0 := trace_mul_ne_zero hψ ha
  refine ⟨a' / a, div_ne_zero (trace_mul_ne_zero hψ' ha') h0, ?_⟩
  refine ext_of_inf hψ'.1 (hψ.1.comp (continuous_const.mul continuous_id)) ψ'.map_add_eq_mul
    (fun x y => by rw [mul_add, ψ.map_add_eq_mul]) hψ'.2.2.1 (fun x => by rw [← map_mul, hψ.2.2.1]) fun x => ?_
  have e : algebraMap F (AF F) (a' / a) * pairA F (algebraMap F _ x) 0 =
      pairA F (algebraMap F _ (a' / a * x)) 0 :=
    Prod.ext (map_mul (algebraMap F (Ainf F)) _ _).symm (mul_zero _)
  rw [e, ha, ha', ← mul_assoc, mul_div_cancel₀ _ h0]

end GlobalTheory.AdeleCharTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRestrictedProductMeasureCountable
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.AbsProd

theorem lintegral_prod_infinitePi {ι : Type} {V : ι → Type} [∀ i, MeasurableSpace (V i)]
    (P : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (P i)] (S : Finset ι)
    (f : ∀ i, V i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ Y, ∏ i ∈ S, f i (Y i) ∂(Measure.infinitePi P) = ∏ i ∈ S, ∫⁻ y, f i y ∂(P i) := by
  rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun S (fun i (Y : ∀ i, V i) => f i (Y i))
    (ProbabilityTheory.iIndepFun_infinitePi (P := P) hf)
    (fun i => (hf i).comp (measurable_pi_apply i))]
  exact Finset.prod_congr rfl fun i _ =>
    (measurePreserving_eval_infinitePi P i).lintegral_comp (hf i)

theorem tail_split {ι : Type} [DecidableEq ι] (c : ι → ℝ) (hs : Summable fun i => |c i - 1|)
    {T S : Finset ι} (h : T ⊆ S) :
    ∏' i : {i : ι // i ∉ T}, c i.1 = (∏ i ∈ S \ T, c i) * ∏' i : {i : ι // i ∉ S}, c i.1 := by
  have key : ∀ U : Finset ι, ∏' i : {i : ι // i ∉ U}, c i.1 = ∏' i, (if i ∈ U then 1 else c i) := by
    intro U
    have := tprod_subtype {i | i ∉ U} c
    refine this.trans (tprod_congr fun i => ?_)
    by_cases hi : i ∈ U <;> simp [Set.mulIndicator, hi]
  have hm : Multipliable fun i => (if i ∈ S then 1 else c i) := by
    have h1 : Summable fun i => (if i ∈ S then (0 : ℝ) else c i - 1) := by
      refine Summable.of_norm_bounded hs fun i => ?_
      by_cases hi : i ∈ S <;> simp [hi]
    refine (Real.multipliable_one_add_of_summable h1).congr fun i => ?_
    by_cases hi : i ∈ S <;> simp [hi]
  have hf : HasProd (fun i => if i ∈ S \ T then c i else 1) (∏ i ∈ S \ T, c i) := by
    have := hasProd_prod_of_ne_finset_one (f := fun i => if i ∈ S \ T then c i else 1)
      (s := S \ T) (L := SummationFilter.unconditional ι) (fun b hb => if_neg hb)
    rwa [Finset.prod_congr rfl (fun i hi => if_pos hi)] at this
  rw [key, key, ← hf.tprod_eq, ← hf.multipliable.tprod_mul hm]
  refine tprod_congr fun i => ?_
  by_cases hT : i ∈ T
  · simp [hT, h hT]
  · by_cases hS : i ∈ S <;> simp [hT, hS]

theorem exists_piece {ι : Type} {V : ι → Type} [∀ i, MeasurableSpace (V i)]
    (a : ∀ i, Measure (V i)) (hσ : ∀ i, SigmaFinite (a i)) (T : Finset ι) (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hs : Summable fun i => |c i - 1|)
    (ha : ∀ i ∉ T, a i Set.univ = ENNReal.ofReal (c i)) :
    ∃ ν : Measure (∀ i, V i), SFinite ν ∧ ∀ S : Finset ι, T ⊆ S → ∀ f : ∀ i, V i → ℝ≥0∞,
      (∀ i, Measurable (f i)) → ∫⁻ Y, ∏ i ∈ S, f i (Y i) ∂ν =
        (∏ i ∈ S, ∫⁻ y, f i y ∂(a i)) * ENNReal.ofReal (∏' i : {i : ι // i ∉ S}, c i.1) := by
  classical
  by_cases h0 : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := h0
    refine ⟨0, inferInstance, fun S hS f _ => ?_⟩
    rw [lintegral_zero_measure]
    by_cases hiS : i ∈ S
    · rw [Finset.prod_eq_zero hiS (by simp [hi]), zero_mul]
    · have h1 := ha i (fun h => hiS (hS h))
      have h2 : c i = 0 := by
        rw [hi] at h1
        exact le_antisymm (ENNReal.ofReal_eq_zero.1 h1.symm) (hc0 i)
      rw [tail_split c hs (Finset.subset_insert i S),
        Finset.prod_eq_zero (s := insert i S \ S) (i := i) (by simp [hiS]) h2]
      simp
  push Not at h0
  have hP : ∀ i, ∃ (P : Measure (V i)) (g : V i → ℝ≥0∞), IsProbabilityMeasure P ∧ Measurable g ∧
      (i ∉ T → ∀ y, g y = 1) ∧ ∀ f : V i → ℝ≥0∞, Measurable f →
        ∫⁻ y, f y ∂(a i) = (if i ∈ T then 1 else ENNReal.ofReal (c i)) * ∫⁻ y, g y * f y ∂P := by
    intro i
    haveI : NeZero (a i) := ⟨h0 i⟩
    by_cases hi : i ∈ T
    · refine ⟨(a i).toFinite, (a i).rnDeriv (a i).toFinite, inferInstance,
        Measure.measurable_rnDeriv _ _, fun h => (h hi).elim, fun f hf => ?_⟩
      rw [if_pos hi, one_mul]
      conv_lhs => rw [← Measure.withDensity_rnDeriv_eq (a i) (a i).toFinite
        (absolutelyContinuous_toFinite _)]
      rw [lintegral_withDensity_eq_lintegral_mul _ (Measure.measurable_rnDeriv _ _) hf]
      rfl
    · haveI : IsFiniteMeasure (a i) := ⟨by rw [ha i hi]; exact ENNReal.ofReal_lt_top⟩
      refine ⟨(a i Set.univ)⁻¹ • a i, fun _ => 1, inferInstance, measurable_const,
        fun _ _ => rfl, fun f _ => ?_⟩
      rw [if_neg hi, ← ha i hi, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
        ENNReal.mul_inv_cancel (by simpa using h0 i) (measure_ne_top _ _)]
      simp
  choose P g hP hg hg1 hint using hP
  have hG : Measurable fun Y : ∀ i, V i =>
      ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ T, g i (Y i) :=
    (Finset.measurable_prod _ fun i _ => (hg i).comp (measurable_pi_apply i)).const_mul _
  refine ⟨(Measure.infinitePi P).withDensity
    (fun Y => ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ T, g i (Y i)),
    inferInstance, fun S hS f hf => ?_⟩
  have hF : Measurable fun Y : ∀ i, V i => ∏ i ∈ S, f i (Y i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  rw [lintegral_withDensity_eq_lintegral_mul _ hG hF]
  have h1 : ∀ Y : ∀ i, V i, ((fun Y : ∀ i, V i =>
      ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ T, g i (Y i)) *
      fun Y : ∀ i, V i => ∏ i ∈ S, f i (Y i)) Y =
      ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ S, (g i (Y i) * f i (Y i)) := by
    intro Y
    rw [Pi.mul_apply, Finset.prod_mul_distrib, mul_assoc,
      Finset.prod_subset hS (fun i _ hi => hg1 i hi (Y i))]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_prod_infinitePi P S (fun i y => g i y * f i y) (fun i => (hg i).mul (hf i)),
    Finset.prod_congr rfl (fun i _ => hint i (f i) (hf i)), Finset.prod_mul_distrib,
    tail_split c hs hS, ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hc0 i),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => hc0 i)]
  have h2 : ∏ i ∈ S, (if i ∈ T then 1 else ENNReal.ofReal (c i)) =
      ∏ i ∈ S \ T, ENNReal.ofReal (c i) := by
    rw [← Finset.prod_subset (Finset.sdiff_subset (s := S) (t := T))
      (fun i hi hi' => if_pos (by simpa [hi] using hi'))]
    exact Finset.prod_congr rfl fun i hi => if_neg (Finset.mem_sdiff.1 hi).2
  rw [h2]
  ring

theorem exists_restricted_product : ∀ (ι : Type) [Countable ι] (V₀ : Type) [MeasurableSpace V₀] (V : ι → Type) [∀ i, MeasurableSpace (V i)] (L : ∀ i, Set (V i)) (m₀ : Measure V₀) (m : ∀ i, Measure (V i)), SigmaFinite m₀ → (∀ i, SigmaFinite (m i)) → (∀ i, MeasurableSet (L i)) → (∀ i, m i (L i) ≠ ∞) → (Summable fun i => |(m i (L i)).toReal - 1|) → ∃ ν : Measure (V₀ × ∀ i, V i), ν {Y | ¬ ∀ᶠ i in Filter.cofinite, Y.2 i ∈ L i} = 0 ∧ ∀ (S : Finset ι) (f₀ : V₀ → ℝ≥0∞) (f : ∀ i, V i → ℝ≥0∞), Measurable f₀ → (∀ i, Measurable (f i)) → ∫⁻ Y in {Y | ∀ i ∉ S, Y.2 i ∈ L i}, f₀ Y.1 * ∏ i ∈ S, f i (Y.2 i) ∂ν = (∫⁻ y, f₀ y ∂m₀) * (∏ i ∈ S, ∫⁻ y, f i y ∂(m i)) * ENNReal.ofReal (∏' i : {i : ι // i ∉ S}, (m i.1 (L i.1)).toReal) := by
  intro ι _ V₀ _ V _ L m₀ m h₀ hm hL hfin hs
  classical
  let a : Finset ι → ∀ i, Measure (V i) := fun T i =>
    (m i).restrict (if i ∈ T then (L i)ᶜ else L i)
  have hex := fun T : Finset ι => exists_piece (a T) (fun i => by dsimp only [a]; infer_instance) T
    (fun i => (m i (L i)).toReal) (fun i => ENNReal.toReal_nonneg) hs
    (fun i hi => by simp [a, hi, ENNReal.ofReal_toReal (hfin i)])
  choose ν hν hint using hex
  have hnull : ∀ (T : Finset ι) (i : ι) (N : Set (V i)), MeasurableSet N → a T i N = 0 →
      ν T {Y | Y i ∈ N} = 0 := by
    intro T i N hN h
    have hm' : ∀ j, Measurable (Function.update (fun j (_ : V j) => (1 : ℝ≥0∞)) i
        (N.indicator 1) j) := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self]
        exact measurable_const.indicator hN
      · rw [Function.update_of_ne hj]
        exact measurable_const
    have h1 := hint T (insert i T) (Finset.subset_insert i T) _ hm'
    rw [Finset.prod_eq_zero (Finset.mem_insert_self i T)
      (by rw [Function.update_self, lintegral_indicator_one hN, h]), zero_mul] at h1
    have hN' : MeasurableSet {Y : ∀ i, V i | Y i ∈ N} := measurable_pi_apply i hN
    rw [← lintegral_indicator_one hN', ← h1]
    refine lintegral_congr fun Y => ?_
    rw [Finset.prod_eq_single i (fun j _ hj => by rw [Function.update_of_ne hj])
      (fun h => (h (Finset.mem_insert_self i T)).elim), Function.update_self]
    rfl
  let B : Finset ι → Set (∀ i, V i) := fun S => {Y | ∀ i ∉ S, Y i ∈ L i}
  have hB : ∀ S, MeasurableSet (B S) := by
    intro S
    have : B S = ⋂ i, ⋂ (_ : i ∉ S), {Y | Y i ∈ L i} := by ext; simp [B]
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurable_pi_apply i (hL i)
  have hin : ∀ T S : Finset ι, T ⊆ S → ν T (B S)ᶜ = 0 := by
    intro T S h
    have : (B S)ᶜ = ⋃ i, ⋃ (_ : i ∉ S), {Y | Y i ∈ (L i)ᶜ} := by ext; simp [B]
    rw [this]
    refine measure_iUnion_null fun i => measure_iUnion_null fun hi => hnull T i _ (hL i).compl ?_
    have hT : i ∉ T := fun h' => hi (h h')
    simp [a, hT, Measure.restrict_apply (hL i).compl]
  have hout : ∀ T S : Finset ι, ¬ T ⊆ S → ν T (B S) = 0 := by
    intro T S h
    obtain ⟨i, hT, hS⟩ := Finset.not_subset.1 h
    refine measure_mono_null (t := {Y | Y i ∈ L i}) (fun Y hY => hY i hS) (hnull T i _ (hL i) ?_)
    simp [a, hT, Measure.restrict_apply (hL i)]
  refine ⟨m₀.prod (Measure.sum ν), ?_, fun S f₀ f hf₀ hf => ?_⟩
  · refine measure_mono_null (t := Set.univ ×ˢ ⋂ S, (B S)ᶜ) (fun Y hY => ?_) ?_
    · refine ⟨trivial, Set.mem_iInter.2 fun S hS => hY ?_⟩
      exact S.eventually_cofinite_notMem.mono fun i hi => hS i hi
    · rw [Measure.prod_prod, Measure.sum_apply_eq_zero.2
        (fun T => measure_mono_null (Set.iInter_subset _ T) (hin T T subset_rfl)), mul_zero]
  · have hF : Measurable fun Y : ∀ i, V i => ∏ i ∈ S, f i (Y i) :=
      Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
    have e : {Y : V₀ × ∀ i, V i | ∀ i ∉ S, Y.2 i ∈ L i} = Set.univ ×ˢ B S := by ext; simp [B]
    rw [e, ← Measure.prod_restrict, Measure.restrict_univ,
      lintegral_prod_mul hf₀.aemeasurable hF.aemeasurable, mul_assoc]
    congr 1
    rw [Measure.restrict_sum _ (hB S), lintegral_sum_measure,
      tsum_eq_sum (s := S.powerset) (fun T hT => by
        rw [Measure.restrict_eq_zero.2 (hout T S (by simpa using hT)), lintegral_zero_measure])]
    have h1 : ∀ i ∈ S, ∫⁻ y, f i y ∂(m i) =
        ∫⁻ y in (L i)ᶜ, f i y ∂(m i) + ∫⁻ y in L i, f i y ∂(m i) := fun i _ => by
      rw [add_comm, lintegral_add_compl _ (hL i)]
    rw [Finset.prod_congr rfl h1, Finset.prod_add, Finset.sum_mul]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTS : T ⊆ S := Finset.mem_powerset.1 hT
    rw [Measure.restrict_eq_self_of_ae_mem (s := B S) (hin T S hTS), hint T S hTS f hf,
      ← Finset.prod_sdiff hTS, mul_comm (∏ i ∈ S \ T, _)]
    congr 2
    · exact Finset.prod_congr rfl fun i hi => by simp [a, hi]
    · exact Finset.prod_congr rfl fun i hi => by simp [a, (Finset.mem_sdiff.1 hi).2]

end GlobalTheory.GaugeEx.AbsProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendLineBundleFactorial
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ExtendLineBundleComponents

theorem exists_integral_components (X : Scheme.{0}) [IsLocallyNoetherian X] [CompactSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) :
    ∃ (A : Type) (V : A → X.Opens), (∀ a b x, x ∈ V a → x ∈ V b → a = b) ∧ (∀ x, ∃ a, x ∈ V a) ∧
      ∀ a, IsIntegral (V a).toScheme ∧ CompactSpace (V a).toScheme := by
  have : IsNoetherian X := {}
  have hfin := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X))
  have heq : ∀ (x : X) (Z W : Set X), Z ∈ irreducibleComponents X → W ∈ irreducibleComponents X →
      x ∈ Z → x ∈ W → Z = W := by
    intro x Z W hZ hW hxZ hxW
    have := hX x
    exact GlobalTheory.IsNormalScheme.eq_of_mem_irreducibleComponents_of_isDomain hZ hW hxZ hxW
  have hopen : ∀ Z ∈ irreducibleComponents X, IsOpen Z := fun Z hZ => by
    have e : Zᶜ = ⋃ W ∈ irreducibleComponents X \ {Z}, W := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
      constructor
      · intro hx
        refine ⟨_, ⟨irreducibleComponent_mem_irreducibleComponents x, fun h ↦ hx ?_⟩,
          mem_irreducibleComponent⟩
        exact (show irreducibleComponent x = Z from h) ▸ mem_irreducibleComponent
      · rintro ⟨W, ⟨hW, hne⟩, hxW⟩ hxZ
        exact hne (heq x W Z hW hZ hxW hxZ)
    rw [← isClosed_compl_iff, e]
    exact hfin.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have : IsReduced X := isReduced_of_isReduced_stalk _
  let V : irreducibleComponents X → X.Opens := fun Z => ⟨Z.1, hopen Z.1 Z.2⟩
  refine ⟨irreducibleComponents X, V, fun a b x ha hb => Subtype.ext (heq x a b a.2 b.2 ha hb),
    fun x => ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, mem_irreducibleComponent⟩,
    fun a => ?_⟩
  have : IrreducibleSpace (V a).toScheme := Subtype.irreducibleSpace a.2.1
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, ?_⟩
  exact isCompact_iff_compactSpace.mp (isClosed_of_mem_irreducibleComponents a.1 a.2).isCompact

theorem uniqueFactorizationMonoid_stalk_toScheme (X : Scheme.{0}) (U : X.Opens)
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (y : U.toScheme) :
    UniqueFactorizationMonoid (U.toScheme.presheaf.stalk y) :=
  MulEquiv.uniqueFactorizationMonoid
    (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv.toMulEquiv (hX _)

end GlobalTheory.ExtendLineBundleComponents

open GlobalTheory.ExtendLineBundleComponents GlobalTheory.GenSpread in

theorem GlobalTheory.exists_lineBundle_extension_of_isDomain : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X]
    [CompactSpace X] (j : Y ⟶ X), IsOpenImmersion j → (∀ x : X, IsDomain (X.presheaf.stalk x)) →
    (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ L : LB Y, L.IsLB →
    ∃ L' : LB X, L'.IsLB ∧ LBIso (L'.pull j) L := by
  intro X Y _ _ j hj hdom hufm L hL
  obtain ⟨A, V, hd, hc, hV⟩ := exists_integral_components X hdom
  have key : ∀ a, ∃ M : LB (V a).toScheme, M.IsLB ∧
      LBIso (M.pull (j ∣_ V a)) (L.pull (j ⁻¹ᵁ V a).ι) := by
    intro a
    have := (hV a).1
    have := (hV a).2
    obtain ⟨M, hM, φ, hφ⟩ := GlobalTheory.exists_lineBundle_extension (V a).toScheme (j ⁻¹ᵁ V a).toScheme
      (j ∣_ V a) inferInstance (uniqueFactorizationMonoid_stalk_toScheme X (V a) hufm)
      (L.pull (j ⁻¹ᵁ V a).ι) (pull_isLB hL _)
    exact ⟨M, hM, φ, hφ⟩
  choose M hM hML using key
  obtain ⟨N, hN, hNM⟩ := GlobalTheory.T.exists_lineBundle_glue_disjoint_cover X A V hd hc M hM
  refine ⟨N, hN, GlobalTheory.T.lbIso_of_lbIso_on_disjoint_cover Y A (fun a => j ⁻¹ᵁ V a) (fun a b y ha hb => hd a b _ ha hb)
    (fun y => hc (j y)) _ _ (pull_isLB hN j) hL fun a => ?_⟩
  have e1 : LBIso ((N.pull j).pull (j ⁻¹ᵁ V a).ι) ((N.pull (V a).ι).pull (j ∣_ V a)) :=
    LBIso.trans (pull_isLB (pull_isLB hN j) _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _)
      (lbIso_pull_pull hN _ rfl).symm (lbIso_pull_pull hN _ (morphismRestrict_ι j (V a)).symm)
  have e2 : LBIso ((N.pull (V a).ι).pull (j ∣_ V a)) ((M a).pull (j ∣_ V a)) :=
    lbIso_pullback (hNM a) _
  exact LBIso.trans (pull_isLB (pull_isLB hN j) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hL _) e1
    (LBIso.trans (pull_isLB (pull_isLB hN _) _) (pull_isLB (hM a) _) (pull_isLB hL _) e2 (hML a))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusTensorEqModulusNorm
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem modu_eq_modu_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (u : R ⊗[F] E) (k : R), IsUnit u → algebraMap R (R ⊗[F] E) k = u * sigR R σ u → IsUnit k ∧ modu (R ⊗[F] E) u = modu R k := by
  intro F E _ _ _ _ _ σ h R _ _ _ _ _ _ _ _ _ u k hu hk
  obtain ⟨-, -, h2, hc⟩ := h
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hc, hc, star_star]
  have hss : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a e =>
      show a ⊗ₜ[F] σ (σ e) = _
      rw [hσ]
  let b : Module.Basis (Fin 2) R (R ⊗[F] E) :=
    Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h2)
  have hku : IsUnit k := by
    have h1 : IsUnit (algebraMap R (R ⊗[F] E) k) := by
      rw [hk]; exact hu.mul (hu.map _)
    have h3 := h1.map (Algebra.norm R)
    rw [Algebra.norm_algebraMap_of_basis b, Fintype.card_fin] at h3
    exact (isUnit_pow_iff two_ne_zero).1 h3
  refine ⟨hku, ?_⟩
  letI : StarRing (R ⊗[F] E) :=
    { star := sigR R σ
      star_involutive := hss
      star_mul := fun x y => by rw [map_mul, mul_comm]
      star_add := fun x y => map_add _ x y }
  haveI : ContinuousStar (R ⊗[F] E) := ⟨GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ⟩
  rw [modu, modu, dif_pos hu, dif_pos hku]
  exact GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm R (R ⊗[F] E) b.equivFun.symm
    (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap) hu.unit hku.unit hk

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawOfSquaresSelfDualSplitLatticeStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.law_of_squares_selfDual_splitLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n r : ℕ), Odd r → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (cc : Ideal (𝓞 E)), (⟨L⟩ : GenLat E n).Unimod → GenLat.SplitSupp H (⟨L⟩ : GenLat E n) → cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → Submodule.span (𝓞 E) (detSet L) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc → ∃ q : ℚ, 0 < q ∧ q ^ 2 * (((L ⊓ Formalism.L2.Pj.stdLat E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ r = (Ideal.absNorm cc : ℚ) := by
  first | exact @GlobalTheory.LawOfSquares.law_of_squares | exact GlobalTheory.LawOfSquares.law_of_squares | (intros; apply GlobalTheory.LawOfSquares.law_of_squares <;> assumption)
end

