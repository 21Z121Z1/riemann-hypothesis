import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0008

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormReducedRadical
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Helpers

variable {F : Type*} [Field F] {n k : ℕ}

private theorem mem_incIdeal_iff {P : Ideal (MvPolynomial (Fin n) F)} {g : MvPolynomial (Fin k × Fin n) F} :
    g ∈ incIdeal P k ↔ ∀ u ∈ incidence P k, aeval u g = 0 := by
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]

private theorem incidence_mono {I W : Ideal (MvPolynomial (Fin n) F)} (hIW : I ≤ W)
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence W k) : u ∈ incidence I k := by
  obtain ⟨x, hx0, hxW, hxu⟩ := hu
  exact ⟨x, hx0, fun g hg => hxW g (hIW hg), hxu⟩

private theorem exists_relComps_of_mem_incidence {J : Ideal (MvPolynomial (Fin n) F)}
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence J k) :
    ∃ W ∈ relComps J, u ∈ incidence W k := by
  obtain ⟨x, hx0, hxJ, hxu⟩ := hu
  let φ : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F := aeval x
  have hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have hJP : J ≤ RingHom.ker φ := fun g hg => RingHom.mem_ker.mpr (hxJ g hg)
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hJP
  refine ⟨W, ⟨hW, ?_⟩, x, hx0, fun g hg => RingHom.mem_ker.mp (hWP hg), hxu⟩
  by_contra hrel
  apply hx0
  funext j
  have hj : X j ∈ W := by
    by_contra hj
    exact hrel ⟨j, hj⟩
  have := RingHom.mem_ker.mp (hWP hj)
  simpa [φ] using this

private theorem mem_support_fundCycle_iff {J : Ideal (MvPolynomial (Fin n) F)} (hJ : J.IsRadical)
    {W : Ideal (MvPolynomial (Fin n) F)} : W ∈ (fundCycle J).support ↔ W ∈ relComps J := by
  classical
  rw [Finsupp.mem_support_iff]
  unfold fundCycle
  rw [Finsupp.onFinset_apply]
  constructor
  · intro h
    by_contra h'
    exact h (if_neg h')
  · intro h
    rw [if_pos h, localMult_eq_one_of_isRadical hJ h.1]
    exact one_ne_zero

end Helpers

theorem ChowFormReduced.proof_of_prime_separate (hPrime : IncIdealPrime.Statement) (hSep : IncIdealSeparate.Statement) :
    ChowFormReduced.Statement := by
  classical
  intro F _ n k J h hJh hJr hch
  have hproj : ∀ W ∈ (fundCycle J).support, IsProjPrime W :=
    fun W hW => isProjPrime_of_mem_support_fundCycle hJh hW
  have hrel : ∀ W ∈ (fundCycle J).support, W ∈ relComps J :=
    fun W hW => (mem_support_fundCycle_iff hJr).mp hW

  have hspan : ∀ g, h ∣ g ↔ ∀ W ∈ (fundCycle J).support, g ∈ incIdeal W k := by
    intro g
    rw [← hch.2 g]
    constructor
    · intro hg W hW
      exact mem_incIdeal_iff.mpr fun u hu => hg u (incidence_mono (hrel W hW).1.1.2 hu)
    · intro hg u hu
      obtain ⟨W, hW, huW⟩ := exists_relComps_of_mem_incidence hu
      exact mem_incIdeal_iff.mp (hg W ((mem_support_fundCycle_iff hJr).mpr hW)) u huW

  have hsep : ∀ W ∈ (fundCycle J).support, ∀ W' ∈ (fundCycle J).support,
      incIdeal W' k ≤ incIdeal W k → W' = W := by
    intro W hW W' hW' hle
    have hne : incIdeal W' k ≠ ⊥ := fun hb => hch.1 (by
      have := (hspan h).mp dvd_rfl W' hW'
      rwa [hb, Ideal.mem_bot] at this)
    have hWW' : W' ≤ W := hSep F n k W W' (hproj W hW) (hproj W' hW') hne hle
    exact le_antisymm hWW' ((hrel W hW).1.2 (hrel W' hW').1.1 hWW')

  have hprin : ∀ W ∈ (fundCycle J).support, ∃ q, Prime q ∧ incIdeal W k = Ideal.span {q} := by
    intro W hW
    have hPW : (incIdeal W k).IsPrime := hPrime F n k W (hproj W hW).isPrime (hproj W hW).isRelevant
    have hhW : h ∈ incIdeal W k := (hspan h).mp dvd_rfl W hW
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hch.1
    have hprod : (UniqueFactorizationMonoid.factors h).prod ∈ incIdeal W k := by
      rwa [← hu, Ideal.mul_unit_mem_iff_mem _ u.isUnit] at hhW
    obtain ⟨q, hqf, hqW⟩ := (hPW.multiset_prod_mem_iff_exists_mem _).1 hprod
    have hq : Prime q := UniqueFactorizationMonoid.prime_of_factor q hqf
    have hqh : q ∣ h := UniqueFactorizationMonoid.dvd_of_mem_factors hqf
    have hqle : Ideal.span {q} ≤ incIdeal W k := (Ideal.span_singleton_le_iff_mem _).mpr hqW
    refine ⟨q, hq, le_antisymm ?_ hqle⟩
    have hqP : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
    have hinf : (fundCycle J).support.inf (fun W' => incIdeal W' k) ≤ Ideal.span {q} := by
      intro g hg
      rw [Ideal.mem_span_singleton]
      exact dvd_trans hqh ((hspan g).mpr fun W' hW' =>
        Finset.inf_le (f := fun W' => incIdeal W' k) hW' hg)
    obtain ⟨W', hW', hle⟩ := hqP.inf_le'.mp hinf
    have hW'W : W' = W := hsep W hW W' hW' (hle.trans hqle)
    rw [← hW'W]
    exact hle
  choose! q hq hqspan using hprin

  have hdvd₁ : (∏ W ∈ (fundCycle J).support, q W) ∣ h := by
    refine Finset.prod_dvd_of_isRelPrime ?_ fun W hW => ?_
    · intro W hW W' hW' hne
      refine (hq W hW).irreducible.isRelPrime_iff_not_dvd.mpr fun hdvd => hne ?_
      have hmem : q W' ∈ incIdeal W k := by
        rw [hqspan W hW]
        exact Ideal.mem_span_singleton.mpr hdvd
      refine (hsep W hW W' hW' ?_).symm
      rw [hqspan W' hW']
      exact (Ideal.span_singleton_le_iff_mem _).mpr hmem
    · have := (hspan h).mp dvd_rfl W hW
      rw [hqspan W hW] at this
      exact Ideal.mem_span_singleton.mp this
  have hdvd₂ : h ∣ ∏ W ∈ (fundCycle J).support, q W := by
    refine (hspan _).mpr fun W hW => ?_
    rw [hqspan W hW]
    exact Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem q hW)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hdvd₁ hdvd₂
  obtain ⟨r, hr, hur⟩ := (isUnit_iff_eq_C_of_isReduced (P := (u : MvPolynomial (Fin k × Fin n) F))).mp
    u.isUnit
  refine ⟨r, hr.ne_zero, q, fun W hW => ⟨(hq W hW).ne_zero, fun g => ?_⟩, ?_⟩
  · rw [← mem_incIdeal_iff, hqspan W hW, Ideal.mem_span_singleton]
  · rw [Finset.prod_congr rfl fun W hW => by rw [fundCycle_apply_of_isRadical hJr hW, pow_one],
      ← hu, hur, mul_comm]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCycleIntegralSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem cycleIntegral_eq_sum {n : ℕ} (h : HermNorm n) (Z : ProjCycle ℂ n) (e : ℕ)
    (g : (Fin n → ℂ) → ℝ) :
    cycleIntegral h Z e g = Z.sum (fun W m => (m : ℝ) * coneIntegral h W e g) := rfl

theorem CycleIntegralSection.proof : CycleIntegralSection.Statement := by
  intro n h Z u e g
  rw [cycleIntegral_eq_sum, cycleSection,
    ← Finsupp.sum_finsetSum_index (by intro W; simp) (by intro W a b; push_cast; ring)]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finsupp.sum_smul_index' (by intro W'; simp), cycleIntegral_eq_sum, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun W' _ => ?_
  simp only [smul_eq_mul, Nat.cast_mul]
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCycleSectionChow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem isChowFormCycle_zero_one {F : Type*} [Field F] {n k : ℕ} :
    IsChowFormCycle (0 : ProjCycle F n) k 1 :=
  ⟨1, one_ne_zero, fun _ => 1, by simp, by simp⟩

theorem IsChowFormCycle.C_mul {F : Type*} [Field F] {n k : ℕ} {Z : ProjCycle F n}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowFormCycle Z k f) {c : F} (hc : c ≠ 0) :
    IsChowFormCycle Z k (C c * f) := by
  obtain ⟨c', hc', g, hg, rfl⟩ := hf
  exact ⟨c * c', mul_ne_zero hc hc', g, hg, by rw [MvPolynomial.C_mul, mul_assoc]⟩

theorem CycleSectionChow.proof (h1 : ChowFormSection.Statement) (h2 : ChowFormCycleAdd.Statement)
    (h3 : ChowFormCycleSmul.Statement) : CycleSectionChow.Statement := by
  intro n e Z f u hprime hf hadm
  obtain ⟨c, hc, g, hg, rfl⟩ := hf
  have hW : ∀ W ∈ Z.support, IsChowFormCycle (divCycle W u) e (specFirst (g W) u) :=
    fun W hW' => h1 ℂ n e W (g W) u (hprime W hW') (hg W hW') (hadm W hW')
  have key : ∀ s ⊆ Z.support, IsChowFormCycle (∑ W ∈ s, Z W • divCycle W u) e
      (∏ W ∈ s, specFirst (g W) u ^ Z W) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using (isChowFormCycle_zero_one : IsChowFormCycle (0 : ProjCycle ℂ n) e 1)
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact h2 ℂ n e _ _ _ _ (h3 ℂ n e (Z a) _ _ (hW a (hs (Finset.mem_insert_self a s))))
        (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))
  have hspec : specFirst (C c * ∏ W ∈ Z.support, g W ^ Z W) u =
      C c * ∏ W ∈ Z.support, specFirst (g W) u ^ Z W := by
    simp only [specFirst, map_mul, map_prod, map_pow, bind₁_C_right]
  rw [hspec]
  exact (key Z.support subset_rfl).C_mul hc

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCycleSectionData
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem CycleSectionData.proof (h1 : CycleSectionChow.Statement) (h2 : DivCyclePrime.Statement)
    (h3 : SpecFirstHomog.Statement) (h4 : SupportCycleSection.Statement) :
    CycleSectionData.Statement := by
  intro n e δ Z f u hZ hu
  refine ⟨?_, ?_, ?_⟩
  · intro W' hW'
    obtain ⟨W, hW, hW'W⟩ := (h4 n Z u).2 W' hW'
    exact h2 n W u (hZ.prime W hW) W' hW'W
  · exact h1 n (e + 1) Z f u hZ.prime hZ.chow hu
  · exact h3 n (e + 1) δ f u hZ.homog

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectAverage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

theorem IsChowFormCycle.ne_zero {n k : ℕ} {Z : ProjCycle ℂ n} {f : MvPolynomial (Fin k × Fin n) ℂ}
    (hf : IsChowFormCycle Z k f) : f ≠ 0 := by
  obtain ⟨c, hc, g, hg, rfl⟩ := hf
  refine mul_ne_zero ?_ ?_
  · rw [Ne, MvPolynomial.C_eq_zero]; exact hc
  · rw [Finset.prod_ne_zero_iff]
    intro W hW
    exact pow_ne_zero _ (hg W hW).1

theorem DefectAverage.proof (h1 : MahlerAverageSplit.Statement) (h2 : CycleAverage.Statement) :
    DefectAverage.Statement := by
  intro n e δ h Z f hZ
  obtain ⟨hi1, hm1⟩ := h1 n e δ h f hZ.chow.ne_zero hZ.homog
  obtain ⟨hi2, hm2⟩ := h2 n e δ h Z f hZ
  have hi : IntegrableOn (fun v => mahlerDefect h e Z f (nrmv h v)) (ballH h) := by
    unfold mahlerDefect; exact hi1.sub hi2
  refine ⟨hi, ?_⟩
  have hsub : ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) =
      (⨍ v in ballH h, mahler h e (specFirst f (nrmv h v))) -
        ⨍ v in ballH h, cycleIntegral h Z e (fsLog h (nrmv h v)) := by
    simp only [setAverage_eq, mahlerDefect]
    rw [integral_sub hi1 hi2, smul_sub]
  rw [hsub, ← hm1, hm2]
  ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectConstStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem DefectConstStep.proof (h1 : DefectSymm.Statement) (h2 : ProperSymmCycle.Statement)
    (h3 : AdmissibleAE.Statement) (h4 : CycleSectionData.Statement) : DefectConstStep.Statement := by
  intro e hA n δ h Z f u u' hd hu hu'
  have hdu := h4 n e δ Z f u hd hu
  have hdu' := h4 n e δ Z f u' hd hu'
  have rel : ∀ {Y : ProjCycle ℂ n} {g : ℕ} {d : ℕ} {F : MvPolynomial (Fin (g + 1) × Fin n) ℂ},
      IsChowCycleData Y g d F → ∀ W ∈ Y.support, IsRelevant W :=
    fun hY W hW => (hY.prime W hW).isRelevant
  have hae := (h3 n Z (rel hd)).and ((h3 n _ (rel hdu)).and (h3 n _ (rel hdu')))
  obtain ⟨v, hvZ, hvu, hvu'⟩ := hae.exists
  have s1 : IsAdmissible (cycleSection Z v) u := h2 n Z u v hd.prime hu hvZ hvu
  have s2 : IsAdmissible (cycleSection Z v) u' := h2 n Z u' v hd.prime hu' hvZ hvu'
  rw [h1 e hA n δ h Z f u v hd hu hvZ hvu s1, h1 e hA n δ h Z f v u' hd hvZ hu' s2 hvu']

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectConstZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem DefectConstZero.proof (h1 : DefectPoint.Statement) (h2 : MahlerZeroSpec.Statement) :
    DefectConstZero.Statement := by
  intro n δ h Z f u u' data hu hu'
  obtain ⟨c, hc, g, hg, hf⟩ := data.chow
  have hK : ∀ W ∈ Z.support, ∃ K : ℝ, ∀ v : Fin n → ℂ, linForm v ∉ W →
      eval (fun ij => v ij.2) (g W) ≠ 0 ∧
        Real.log ‖eval (fun ij => v ij.2) (g W)‖ - coneIntegral h W 0 (fsLog h v) = K :=
    fun W hW => h1 n h W (g W) (data.prime W hW) (hg W hW)
  choose! K hK using hK
  have key : ∀ v : Fin n → ℂ, IsAdmissible Z v →
      mahlerDefect h 0 Z f v = Real.log ‖c‖ + ∑ W ∈ Z.support, (Z W : ℝ) * K W := by
    intro v hv
    have hne : ∀ W ∈ Z.support, eval (fun ij => v ij.2) (g W) ≠ 0 := fun W hW => (hK W hW v (hv W hW)).1
    have hm : mahler h 0 (specFirst f v) = Real.log ‖eval (fun ij => v ij.2) f‖ := h2 n h f v
    unfold mahlerDefect cycleIntegral
    rw [hm, hf, map_mul, eval_C, map_prod, norm_mul, norm_prod]
    have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    have hp : ∀ W ∈ Z.support, ‖eval (fun ij => v ij.2) (g W ^ Z W)‖ ≠ 0 := by
      intro W hW
      rw [map_pow, norm_pow]
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hne W hW))
    rw [Real.log_mul hc' (Finset.prod_ne_zero_iff.mpr hp), Real.log_prod hp, add_sub_assoc,
      ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [map_pow, norm_pow, Real.log_pow, ← (hK W hW v (hv W hW)).2]
    ring
  rw [key u hu, key u' hu']

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

theorem isMultiHomog_pointForm (c : ℂ) (y : Fin n → ℂ) :
    IsMultiHomog 1 (C c * ∑ j, C (y j) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin n) ℂ) := by
  have hw : ∀ j : Fin n, groupWeight 1 n ((0 : Fin 1), j) = fun _ => 1 := by
    intro j
    funext i
    rw [Fin.fin_one_eq_zero i]
    simp [groupWeight]
  have hsum : IsWeightedHomogeneous (groupWeight 1 n)
      (∑ j, C (y j) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin n) ℂ) (fun _ => 1) := by
    rw [← mem_weightedHomogeneousSubmodule]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [mem_weightedHomogeneousSubmodule]
    have hX := isWeightedHomogeneous_X ℂ (groupWeight 1 n) ((0 : Fin 1), j)
    rw [hw j] at hX
    simpa [zero_add] using (isWeightedHomogeneous_C (groupWeight 1 n) (y j)).mul hX
  unfold IsMultiHomog
  simpa [zero_add] using (isWeightedHomogeneous_C (groupWeight 1 n) c).mul hsum

theorem DefectPoint.proof (h1 : PointLine.Statement) (h2 : PointChowForm.Statement)
    (h3 : ConeIntegralLine.Statement) (h4 : FsLogSmul.Statement) (h5 : ConeIntegralMass.Statement) :
    DefectPoint.Statement := by
  intro n h W g hW hg
  obtain ⟨y, hy0, hline, hmem⟩ := h1 n W g hW hg
  obtain ⟨c, hc, hgeq⟩ := h2 n W g y hg hy0 hline
  have hmass : coneIntegral h W 0 (fun _ => 1) = 1 := by
    have := h5 n 0 1 h W g hW hg (hgeq ▸ isMultiHomog_pointForm c y)
    simpa using this
  have hd : 0 < h.dualNorm y := h.dualNorm_pos hy0
  refine ⟨Real.log ‖c‖ + Real.log (h.dualNorm y), fun u hu => ?_⟩
  have hpair : ∑ j, u j * y j ≠ 0 := by
    intro h0
    apply hu
    rw [hmem]
    intro t
    simp only [linForm, map_sum, map_mul, eval_C, eval_X, Pi.smul_apply, smul_eq_mul]
    calc ∑ j, u j * (t * y j) = t * ∑ j, u j * y j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h0, mul_zero]
  have hev : eval (fun ij => u ij.2) g = c * ∑ j, u j * y j := by
    rw [hgeq]
    simp only [map_mul, map_sum, eval_C, eval_X]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hcone : coneIntegral h W 0 (fsLog h u) = fsLog h u y := by
    rw [h3 n h W y hline (fsLog h u) (fun t ht => h4 n h u y t ht), hmass, mul_one]
  refine ⟨by rw [hev]; exact mul_ne_zero hc hpair, ?_⟩
  rw [hev, hcone, fsLog, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hpair),
    Real.log_div (norm_ne_zero_iff.mpr hpair) hd.ne']
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDefectSymm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem DefectSymm.proof (h1 : CycleSectionData.Statement) (h2 : SpecFirstSwapMahler.Statement)
    (h3 : CycleIntegralSection.Statement) (h4 : GreenSymmetry.Statement)
    (h5 : SupportCycleSection.Statement) : DefectSymm.Statement := by
  intro e hIH n δ h Z f u u' hZ hu hu' huu' hu'u

  have A := hIH n δ h (cycleSection Z u) (specFirst f u) u' (h1 n e δ Z f u hZ hu) huu'
  have B := hIH n δ h (cycleSection Z u') (specFirst f u') u (h1 n e δ Z f u' hZ hu') hu'u
  have S := h2 n e h Z f u u' hZ.chow

  obtain ⟨c, -, g, hg, -⟩ := hZ.chow
  have G : ∀ W ∈ Z.support,
      (Z W : ℝ) * (cycleIntegral h (divCycle W u) e (fsLog h u') + coneIntegral h W (e + 1) (fsLog h u)) =
        (Z W : ℝ) * (cycleIntegral h (divCycle W u') e (fsLog h u) +
          coneIntegral h W (e + 1) (fsLog h u')) := by
    intro W hW
    congr 1
    refine h4 n e h W u u' (hZ.prime W hW) ⟨g W, hg W hW⟩ (hu W hW) (hu' W hW) ?_
    intro W' hW'
    exact huu' W' ((h5 n Z u).1 W hW hW')
  have hsum := Finset.sum_congr rfl G
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  have Cu := h3 n h Z u e (fsLog h u')
  have Cu' := h3 n h Z u' e (fsLog h u)
  have Ku : cycleIntegral h Z (e + 1) (fsLog h u) =
      ∑ W ∈ Z.support, (Z W : ℝ) * coneIntegral h W (e + 1) (fsLog h u) := rfl
  have Ku' : cycleIntegral h Z (e + 1) (fsLog h u') =
      ∑ W ∈ Z.support, (Z W : ℝ) * coneIntegral h W (e + 1) (fsLog h u') := rfl
  unfold mahlerDefect
  linarith
end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PEvalSpecFirst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem EvalSpecFirst.proof : EvalSpecFirst.Statement := by
  intro n k f v w
  change eval₂Hom (RingHom.id ℂ) w (bind₁ (specFirstVar v) f) =
    eval₂Hom (RingHom.id ℂ) (consGroup v w) f
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero => simp [specFirstVar, consGroup]
  | succ i => simp [specFirstVar, consGroup]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogPointOf
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem FsLogPointOf.proof : FsLogPointOf.Statement := by
  intro n h v y
  have hdet : IsUnit (h.matᵀ).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hd : h.dualNorm (h.pointOf y) = (HermNorm.std n).dualNorm (fun i => y i) := by
    simp only [HermNorm.dualNorm, HermNorm.pointOf, HermNorm.std, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, Matrix.transpose_one, inv_one]
  have hn : (HermNorm.std n).norm (h.mat *ᵥ v) = h.norm v := by
    simp only [HermNorm.norm, HermNorm.std, Matrix.one_mulVec]
  have hs : ∑ j, v j * h.pointOf y j = ∑ i, (h.mat *ᵥ v) i * y i := by
    have := Matrix.dotProduct_mulVec v h.matᵀ (fun i => y i)
    rw [Matrix.vecMul_transpose] at this
    simpa [dotProduct, HermNorm.pointOf] using this
  unfold fsLog nrmv
  rw [hd, hn]
  simp only [mul_assoc, ← Finset.mul_sum, hs]

end GroundTheory.Heights₂.Heights
end

