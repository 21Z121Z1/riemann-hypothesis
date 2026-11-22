import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreIdeal
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0018

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartZeroTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartZeroTrdeg

variable {F : Type} [Field F] {n : ℕ}

def homogAt (p : MvPolynomial (Fin n) F) (j : Fin n) (N : ℕ) : MvPolynomial (Fin n) F :=
  ∑ α ∈ p.support, monomial α (coeff α p) * X j ^ (N - α.sum fun _ e => e)

theorem aeval_homogAt {L : Type} [Field L] [Algebra F L] (p : MvPolynomial (Fin n) F) (j : Fin n)
    (N : ℕ) (hN : p.totalDegree ≤ N) (z : Fin n → L) (hz : z j ≠ 0) :
    aeval z (homogAt p j N) = z j ^ N * aeval (fun m => z m * (z j)⁻¹) p := by
  conv_rhs => rw [p.as_sum]
  rw [homogAt, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hk := (le_totalDegree hα).trans hN
  simp only [map_mul, aeval_monomial, map_pow, aeval_X, mul_pow, Finsupp.prod_mul]
  have hc : (α.prod fun a => HPow.hPow (z j)⁻¹) = (z j)⁻¹ ^ (α.sum fun _ e => e) := by
    simp only [Finsupp.prod, Finsupp.sum]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [hc]
  have : z j ^ N = z j ^ (N - α.sum fun _ e => e) * z j ^ (α.sum fun _ e => e) := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [this, inv_pow]
  field_simp

theorem aeval_genPt_eq_zero_iff' (P : Ideal (MvPolynomial (Fin n) F)) (f : MvPolynomial (Fin n) F) :
    aeval (genPt P) f = 0 ↔ f ∈ P := by
  have h : aeval (genPt P) = (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ P)
      (FractionRing (MvPolynomial (Fin n) F ⧸ P))).comp (Ideal.Quotient.mkₐ F P) :=
    MvPolynomial.algHom_ext fun i => by simp [genPt]
  rw [h]
  change algebraMap _ (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (Ideal.Quotient.mk P f) = 0 ↔ _
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

end ChartZeroTrdeg

open ChartZeroTrdeg in

theorem ChartZeroTrdeg.proof (hA : AffineChartTrdeg.Statement) : ChartZeroTrdeg.Statement := by
  intro F _ n d Q hQ hdim Ω _ _ y j hy hyj
  have := hQ.isPrime
  have hXj : X j ∉ Q := fun h => hyj (by simpa using hy _ h)
  set ξ := genPt Q
  have hξ : ξ j ≠ 0 := fun h => hXj ((aeval_genPt_eq_zero_iff' Q (X j)).1 (by simpa using h))
  set gξ := aeval (R := F) (fun m => ξ m * (ξ j)⁻¹)
  set gy := aeval (R := F) (fun m => y m * (y j)⁻¹)
  have hker : ∀ p, gξ p = 0 → gy p = 0 := by
    intro p hp
    have hH : homogAt p j p.totalDegree ∈ Q := by
      rw [← aeval_genPt_eq_zero_iff', aeval_homogAt p j _ le_rfl ξ hξ]
      simp [gξ] at hp
      simp [hp]
    have := hy _ hH
    rw [aeval_homogAt p j _ le_rfl y hyj] at this
    simpa [gy, hyj] using this
  have hAξ := hA F n d Q j hQ hdim hXj
  rw [Algebra.adjoin_range_eq_range_aeval] at hAξ ⊢
  let e := Ideal.quotientKerAlgEquivOfSurjective gξ.rangeRestrict_surjective
  let φ := Ideal.Quotient.liftₐ (RingHom.ker gξ.rangeRestrict) gy.rangeRestrict fun p hp => by
    apply Subtype.ext
    exact hker p (congrArg Subtype.val hp)
  have hφ : Function.Surjective φ := by
    intro b
    obtain ⟨p, hp⟩ := gy.rangeRestrict_surjective b
    exact ⟨Ideal.Quotient.mk _ p, hp⟩
  have := trdeg_le_of_surjective (φ.comp e.symm.toAlgHom) (hφ.comp e.symm.surjective)
  exact this.trans hAξ.le

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormBirationalAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem not_dvd_pderiv_of_pderiv_ne_zero {F σ : Type*} [Field F] {g : MvPolynomial σ F}
    (hg : g ≠ 0) {i : σ} (hne : pderiv i g ≠ 0) : ¬ g ∣ pderiv i g := by
  classical
  rintro ⟨q, hq⟩
  have hi : 0 < degreeOf i g := by
    obtain ⟨m, hm⟩ := support_nonempty.2 hne
    rw [mem_support_iff, coeff_pderiv] at hm
    have h1 : m + Finsupp.single i 1 ∈ g.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
    have := monomial_le_degreeOf i h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  have hlt : degreeOf i (pderiv i g) < degreeOf i g := by
    rw [degreeOf_lt_iff hi]
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    have h1 : m + Finsupp.single i 1 ∈ g.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
    have := monomial_le_degreeOf i h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  rw [hq, degreeOf_mul_eq hg (right_ne_zero_of_mul (hq ▸ hne))] at hlt
  omega

theorem IsChowForm.exists_pderiv_ne_zero {F : Type} [Field F] [IsAlgClosed F] {p : ℕ} [hp : Fact p.Prime]
    [CharP F p] {n k : ℕ} {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P)
    {g : MvPolynomial (Fin (k + 1) × Fin n) F} (hg : IsChowForm P (k + 1) g) :
    ∃ l, pderiv (0, l) g ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon

  have hall : ∀ v, pderiv v g = 0 := by
    rintro ⟨i, l⟩
    obtain ⟨c, hc2, hc⟩ := hg.rename_swap 0 i
    have hinj : Function.Injective (Prod.map (Equiv.swap (0 : Fin (k + 1)) i) (id : Fin n → Fin n)) :=
      (Equiv.swap 0 i).injective.prodMap Function.injective_id
    have h := pderiv_rename hinj (0, l) g
    rw [hc, pderiv_C_mul, hcon l, map_zero, Prod.map_apply, Equiv.swap_apply_left, id] at h
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc2
    exact (mul_eq_zero.1 h).resolve_left fun h0 => hc0 (C_eq_zero.1 h0)

  have hexp : ∀ s ∈ g.support, ∀ v, p ∣ s v := by
    intro s hs v
    by_cases h0 : s v = 0
    · simp [h0]
    have hle : Finsupp.single v 1 ≤ s := Finsupp.single_le_iff.2 (by omega)
    have h1 := congrArg (coeff (s - Finsupp.single v 1)) (hall v)
    rw [coeff_pderiv, coeff_zero, tsub_add_cancel_of_le hle] at h1
    have h2 := (mul_eq_zero.1 h1).resolve_left (mem_support_iff.1 hs)
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same] at h2
    have h3 : ((s v : ℕ) : F) = 0 := by
      rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
      push_cast
      exact h2
    exact (CharP.cast_eq_zero_iff F p _).1 h3

  obtain ⟨h, hgh⟩ : ∃ h : MvPolynomial (Fin (k + 1) × Fin n) F, h ^ p = g := by
    have hroot : ∀ a : F, ∃ b : F, b ^ p = a := fun a => IsAlgClosed.exists_pow_nat_eq a hp.out.pos
    choose r hr using hroot
    refine ⟨∑ s ∈ g.support, monomial (Finsupp.mapRange (· / p) (Nat.zero_div p) s) (r (coeff s g)), ?_⟩
    rw [sum_pow_char]
    conv_rhs => rw [as_sum g]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : p • Finsupp.mapRange (· / p) (Nat.zero_div p) s = s := by
      ext v
      simp [Nat.mul_div_cancel' (hexp s hs v)]
    rw [monomial_pow, hr, hs']

  have hmem : ∀ q, q ∈ incIdeal P (k + 1) ↔ g ∣ q := by
    intro q
    rw [← hg.2 q, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hprime : Prime g := by
    have hI := IncIdealPrime.full F n (k + 1) P hP.isPrime hP.isRelevant
    have hspan : incIdeal P (k + 1) = Ideal.span {g} := by
      ext q
      rw [Ideal.mem_span_singleton, hmem]
    rw [hspan] at hI
    exact (Ideal.span_singleton_prime hg.1).1 hI
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hg.1 (by rw [← hgh, zero_pow hp.out.ne_zero])
  obtain ⟨q, hq⟩ := hprime.dvd_of_dvd_pow (show g ∣ h ^ p by rw [hgh])
  obtain ⟨m, hm⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.out.two_le; omega⟩
  have h1 : h * (h ^ (m + 1) * q) = h * 1 := by
    rw [mul_one]
    conv_rhs => rw [hq, ← hgh, hm]
    ring
  have hu : IsUnit (h ^ (m + 1)) := IsUnit.of_mul_eq_one q (mul_left_cancel₀ hh0 h1)
  have hu' : IsUnit h := (isUnit_pow_iff (Nat.succ_ne_zero m)).1 hu
  exact hprime.not_isUnit (hgh ▸ hu'.pow p)

theorem ChowFormBirationalAlgClosed.proof : ChowFormBirationalAlgClosed.Statement := by
  intro F _ _ n k P g c hP hg hc
  obtain _ | ⟨p, hp, hch⟩ := CharP.exists' F
  · exact ChowFormBirational.full F n k P g c hP hg hc
  have := hP.isPrime
  classical

  have hmem : ∀ h, h ∈ incIdeal P (k + 1) ↔ g ∣ h := by
    intro h
    rw [← hg.2 h, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hg0 : aeval (genSubst (genPt P) c) g = 0 :=
    (IncidenceGeneric.full F n (k + 1) P c hc g).1 ((hmem g).2 dvd_rfl)

  have hA : ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) =
      C (genPt P m) * ∑ l, aeval (genSubst (genPt P) c) (pderiv (0, l) g) * C (c l) := by
    intro m
    have h := pderiv_aeval_eq_sum (genSubst (genPt P) c) (0, m) g
    rw [hg0, map_zero] at h
    simp only [pderiv_genSubst, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Fin.succ_ne_zero, if_false, Finset.sum_const_zero, add_zero] at h
    rw [eq_comm, sub_eq_zero] at h
    rw [h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) = C (genPt P m) * ρ :=
    ⟨_, hA⟩

  obtain ⟨l, hl⟩ := IsChowForm.exists_pderiv_ne_zero (p := p) hP hg
  refine ⟨Pi.single l 1, ?_, fun m => ?_⟩
  · have hsum : (∑ l', C ((Pi.single l (1 : F) : Fin n → F) l') * pderiv (0, l') g) =
        pderiv (0, l) g := by
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [hsum, hmem]
    exact not_dvd_pderiv_of_pderiv_ne_zero hg.1 hl
  · simp only [map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_apply, hρ]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PComplexFibreCycle
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

namespace ComplexFibreCycle

theorem complexFibreIdeal_eq_map {n : ℕ} (P : Ideal (MRing (PBlk n))) :
    complexFibreIdeal P = (ObjectsChow.genericIdeal P).map (MvPolynomial.map (Rat.castHom ℂ)) := by
  have h : (MvPolynomial.map (Rat.castHom ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.map (Int.castRingHom ℂ) : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℂ) :=
    RingHom.ext fun p => by
      rw [RingHom.comp_apply, MvPolynomial.map_map,
        RingHom.ext_int ((Rat.castHom ℂ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ)]
  rw [complexFibreIdeal, ObjectsChow.genericIdeal, Ideal.map_map, h]

theorem specFirst_eq_zero_iff (hNe : SpecFirstNe.Statement) (hBot : IncIdealNeBotDim.Statement)
    (hDim : ConeDimOfChowForm.Statement) {n e : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {g : MvPolynomial (Fin (e + 1) × Fin n) ℂ} (hW : IsProjPrime W) (hg : IsChowForm W (e + 1) g)
    (u : Fin n → ℂ) : IndefiniteRowSideFullHecke.ArithBezout.specFirst u g = 0 ↔ linForm u ∈ W := by
  rw [← ObjectsChow.specFirst_eq]
  constructor
  · intro h
    by_contra hu
    exact hNe ℂ n e W g u hW hg hu h
  · intro hu
    have hbot : incIdeal W e = ⊥ := by
      by_contra hne
      have h1 := hBot ℂ n e W hW hne
      rw [hDim ℂ n (e + 1) W g hW hg] at h1
      have h2 : ((e + 1 : ℕ) : ℕ∞) ≤ ((e : ℕ) : ℕ∞) := by exact_mod_cast h1
      have h3 : e + 1 ≤ e := by exact_mod_cast h2
      omega
    have h := SpecFirstMemIncIdeal.proof ℂ n e W W g u hg le_rfl hu
    rwa [hbot, Ideal.mem_bot] at h

end ComplexFibreCycle

open ComplexFibreCycle in

theorem ComplexFibreCycle.proof (hBC : ChowFormBaseChange.Statement) (hNe : SpecFirstNe.Statement)
    (hBot : IncIdealNeBotDim.Statement) (hDim : ConeDimOfChowForm.Statement) :
    ComplexFibreCycle.Statement := by
  intro n e δ P f hP hf
  obtain ⟨c, hc, f₀, rfl, hf₀⟩ := ObjectsChow.ComplexChowFormToChowForm.proof n e δ P f hP hf
  have hI := (ObjectsChow.GenericFibreIdeal.proof n (e + 1) P hP).1
  have key := hBC ℚ n (e + 1) (ObjectsChow.genericIdeal P) f₀ (Rat.castHom ℂ) hI hf₀
  rw [← complexFibreIdeal_eq_map] at key
  obtain ⟨hprime, c', hc', g, hg, hfeq⟩ := key
  have hCne : ∀ {k : ℕ} (a : ℂ), a ≠ 0 → (C a : MvPolynomial (Fin k × Fin n) ℂ) ≠ 0 :=
    fun a ha => by rwa [Ne, C_eq_zero]
  refine ⟨hprime, ?_, fun u => ?_⟩
  · unfold IsChowFormCycle
    exact ⟨c * c', mul_ne_zero hc hc', g, hg, by rw [hfeq, ← mul_assoc, ← C_mul]⟩
  · have hsC : ∀ a : ℂ, IndefiniteRowSideFullHecke.ArithBezout.specFirst (e := e) u (C a) = C a := by
      intro a
      simp [IndefiniteRowSideFullHecke.ArithBezout.specFirst]
    rw [hfeq, map_mul, map_mul, hsC, hsC, map_prod]
    simp only [map_pow]
    constructor
    · intro h W hW hu
      apply h
      rw [Finset.prod_eq_zero hW, mul_zero, mul_zero]
      rw [(specFirst_eq_zero_iff hNe hBot hDim (hprime W hW) (hg W hW) u).mpr hu,
        zero_pow (Finsupp.mem_support_iff.mp hW)]
    · intro h
      refine mul_ne_zero (hCne c hc) (mul_ne_zero (hCne c' hc')
        (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ ?_))
      rw [Ne, specFirst_eq_zero_iff hNe hBot hDim (hprime W hW) (hg W hW) u]
      exact h W hW

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeAreaFormula
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

theorem volume_null_of_hausdorff_null {m : ℕ} {s : Set (EuclideanSpace ℂ (Fin m))}
    (hs : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) s = 0) : volume s = 0 := by
  have hdim : finrank ℝ (EuclideanSpace ℂ (Fin m)) = 2 * m := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hμ : (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) : Measure (EuclideanSpace ℂ (Fin m))) =
      Measure.hausdorffMeasure (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ) := by
    rw [hdim]
  rw [hμ] at hs
  exact Measure.absolutelyContinuous_isAddHaarMeasure volume
    (Measure.hausdorffMeasure (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ)) hs

theorem encard_iUnion_disjoint_nat {α : Type*} (s : ℕ → Set α) (hs : Pairwise (Function.onFun Disjoint s)) :
    (((⋃ i, s i).encard : ℕ∞) : ℝ≥0∞) = ∑' i, (((s i).encard : ℕ∞) : ℝ≥0∞) := by
  let _ : MeasurableSpace α := ⊤
  have hm : ∀ t : Set α, MeasurableSet t := fun _ => MeasurableSpace.measurableSet_top
  rw [← Measure.count_apply (hm _), measure_iUnion hs (fun _ => hm _)]
  simp only [Measure.count_apply (hm _)]

theorem volume_linProj_image_null {m n : ℕ} (π : Fin m → Fin n → ℂ) {s : Set (EuclideanSpace ℂ (Fin n))}
    (hs : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) s = 0) : volume (linProj π '' s) = 0 := by
  refine volume_null_of_hausdorff_null (nonpos_iff_eq_zero.1 ?_)
  have hL := (LinearMap.toContinuousLinearMap (linProjₗ π)).lipschitz.hausdorffMeasure_image_le
    (d := ((2 * m : ℕ) : ℝ)) (by positivity) s
  rw [LinearMap.coe_toContinuousLinearMap', hs, mul_zero] at hL
  exact hL

theorem ConeAreaFormula.proof (hCover : ConeGraphCover.Statement) (hArea : GraphAreaFibre.Statement) :
    ConeAreaFormula.Statement := by
  intro n m h J hJ hm hmn hfin π g hg
  obtain ⟨e, Ω, Φ, hpc, hnull⟩ := hCover n m h J hJ hm hmn hfin
  let S : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun i => graphPt (e i) (Φ i) '' Ω i
  let D := disjointed S
  have hSm : ∀ i, MeasurableSet (S i) := fun i =>
    (hpc i).1.measurableSet.image_of_continuousOn_injOn
      (continuousOn_graphPt _ (hpc i).2.1.continuousOn) (graphPt_injective_of_graphBase _ _).injOn
  have hDm : ∀ i, MeasurableSet (D i) := MeasurableSet.disjointed hSm
  have hDS : ∀ i, D i ⊆ S i := disjointed_subset S
  have hDd : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed S
  have hU : ⋃ i, D i = ⋃ i, S i := iUnion_disjointed
  have hUC : ⋃ i, D i ⊆ coneSet h J := Set.iUnion_subset fun i => (hDS i).trans (hpc i).2.2.1
  have hN : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (coneSet h J \ ⋃ i, D i) = 0 := by
    rw [hU]; exact hnull
  have hCae : coneSet h J =ᵐ[Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)] ⋃ i, D i :=
    ae_eq_set.2 ⟨hN, by rw [Set.sdiff_eq_empty.2 hUC]; exact measure_empty⟩
  have hpiece := fun i => hArea m (n - m) n (e i) (Ω i) (Φ i) (hpc i).1 (hpc i).2.1 (D i) (hDS i)
    (hDm i) (coneTangent h J) (fun x hx _ => (hpc i).2.2.2 x hx) π
  have hcount : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℂ (Fin m))),
      ((fibreCount h J π w : ℕ∞) : ℝ≥0∞) * g w =
        ∑' i, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_linProj_image_null π hN)] with w hw
    rw [ENNReal.tsum_mul_right, fibreCount, ← encard_iUnion_disjoint_nat]
    · congr 3
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨hy, rfl⟩
        by_contra hne
        exact hw ⟨y, ⟨hy, fun hyD => hne (by
          obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyD
          exact ⟨i, hi, rfl⟩)⟩, rfl⟩
      · rintro ⟨i, hi, hw'⟩
        exact ⟨hUC (Set.mem_iUnion.2 ⟨i, hi⟩), hw'⟩
    · intro i j hij
      exact (hDd hij).mono (fun y hy => hy.1) (fun y hy => hy.1)
  calc volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ y in coneSet h J, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
          ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))
      = ∑' i, volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ y in D i, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
            ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) := by
        rw [Measure.restrict_congr_set hCae, lintegral_iUnion hDm hDd, ENNReal.tsum_mul_left]
    _ = ∑' i, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w :=
        tsum_congr fun i => (hpiece i).2 g hg
    _ = Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, ((fibreCount h J π w : ℕ∞) : ℝ≥0∞) * g w := by
        rw [ENNReal.tsum_mul_left, ← lintegral_tsum
          (f := fun i w => (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w)
          fun i => (hpiece i).1.mul hg.aemeasurable, lintegral_congr_ae hcount]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralChart
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsSheet sheetDensity ptsIntegralAt pot)

theorem hermLine_h_eq {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (z : (Σ _ : Unit, PBlk n ()) → ℂ) :
    (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS).h z = ‖WithLp.toLp 2 (S *ᵥ fun i => z ⟨(), i⟩)‖ := by
  simp [IndefiniteRowSideFullHecke.ArithBezout.hermLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics,
    IndefiniteRowSideFullHecke.ArithBezout.pointMetric]

theorem measurable_fsLog {n : ℕ} (h : HermNorm n) (u : Fin n → ℂ) : Measurable (fsLog h u) := by
  unfold fsLog HermNorm.dualNorm
  simp only [Matrix.mulVec, dotProduct]
  exact Real.measurable_log.comp (Measurable.div (Continuous.measurable (by fun_prop))
    (Continuous.measurable (by fun_prop)))

theorem ConeIntegralChart.proof (hA : ConeChartArea.Statement) (hB : ChartGramMA.Statement)
    (hI : ConeChartIntegrable.Statement) : ConeIntegralChart.Statement := by
  intro n e S hS P u Ψ hP hu hΨ
  rw [hA n e S hS P Ψ _ hP hΨ (measurable_fsLog _ u)
    (fun c z hc => FsLogSmul.proof n _ u z c hc) (hI n e _ P u hP hu)]
  unfold ptsIntegralAt
  congr 1
  funext y
  refine finsum_mem_congr rfl fun w _ => ?_
  unfold chartGramDensity sheetDensity
  by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
  · simp only [dif_pos hγ]
    have hev := hγ.choose_spec.2
    have hg : fsLog (ObjectsHeight.ofPointMatrix S hS) u (fun i => hγ.choose y ⟨(), i⟩) =
        IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u (hγ.choose y) := by
      rw [ObjectsHeight.ofPointMatrix_fsLog]
    have hpot : (fun (j : Fin e) y' =>
        pot (fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS) j (hγ.choose y')) =
        fun _ y' => Real.log ‖WithLp.toLp 2 (S *ᵥ fun i => hγ.choose y' ⟨(), i⟩)‖ := by
      funext j y'
      simp only [pot, hermLine_h_eq]
    rw [hg, hpot, hB e n _ y ?_ ?_]
    · filter_upwards [hev] with y' hy'
      refine differentiableAt_pi.2 fun i => ?_
      simp only [Matrix.mulVec, dotProduct]
      exact DifferentiableAt.fun_sum fun j _ => (differentiableAt_pi.1 hy'.1 ⟨(), j⟩).const_mul _
    · obtain ⟨i, hi⟩ := hev.self_of_nhds.2.1.1 ()
      intro h0
      have h1 := Matrix.mulVec_injective_iff_isUnit.mpr hS (h0.trans (Matrix.mulVec_zero S).symm)
      exact hi (congrFun h1 i)
  · simp only [dif_neg hγ]

end GroundTheory.Heights₂.Heights
end
end

