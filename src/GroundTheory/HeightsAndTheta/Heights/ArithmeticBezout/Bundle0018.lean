import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntSphere
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDivCyclePrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

theorem isHomogIdeal_iff_isHomogeneous (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsHomogIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by
  constructor
  · intro h i r hr
    have := decomposition.decompose'_apply (σ := Fin n) (R := ℂ) r i
    change (decomposition.decompose' r i : MvPolynomial (Fin n) ℂ) ∈ I
    rw [this]
    exact h r hr i
  · intro h f hf d
    exact homogeneousComponent_mem_of_mem h hf d

theorem isHomogeneous_of_mem_minimalPrimes {I P : Ideal (MvPolynomial (Fin n) ℂ)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ)) (hP : P ∈ I.minimalPrimes) :
    P.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by
  have hcore : (P.homogeneousCore (homogeneousSubmodule (Fin n) ℂ)).toIdeal.IsPrime :=
    hP.1.1.homogeneousCore
  have hle : I ≤ (P.homogeneousCore (homogeneousSubmodule (Fin n) ℂ)).toIdeal :=
    hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hP.1.2)
  have hcoreP := Ideal.toIdeal_homogeneousCore_le (homogeneousSubmodule (Fin n) ℂ) P
  rw [Ideal.IsHomogeneous.iff_eq]
  exact le_antisymm hcoreP (hP.2 ⟨hcore, hle⟩ hcoreP)

theorem DivCyclePrime.proof : DivCyclePrime.Statement := by
  intro n W u hW W' hW'
  have hmem : W' ∈ relComps (W ⊔ Ideal.span {linForm u}) := by
    by_contra hc
    apply Finsupp.mem_support_iff.mp hW'
    simp only [divCycle, fundCycle, Finsupp.onFinset_apply]
    exact if_neg hc
  obtain ⟨hmin, hrel⟩ := hmem
  have hlin : (linForm u : MvPolynomial (Fin n) ℂ) ∈ homogeneousSubmodule (Fin n) ℂ 1 := by
    rw [mem_homogeneousSubmodule]
    exact IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j
  have hJ : (W ⊔ Ideal.span {linForm u}).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) :=
    ((isHomogIdeal_iff_isHomogeneous W).mp hW.isHomog).sup
      (Ideal.homogeneous_span _ _ fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        exact hx ▸ ⟨1, hlin⟩)
  exact ⟨hmin.1.1, (isHomogIdeal_iff_isHomogeneous W').mpr
    (isHomogeneous_of_mem_minimalPrimes hJ hmin), hrel⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogAverage
section
set_option maxSynthPendingDepth 1

open MeasureTheory Matrix

namespace GroundTheory.Heights₂.Heights

theorem FsLogAverage.proof (h1 : BallAverageLinear.Statement) (h2 : FsLogPointOf.Statement)
    (h3 : SphereMeanLinearBall.Statement) (h4 : BallVolume.Statement) : FsLogAverage.Statement := by
  intro n h y hy
  set y' : Fin n → ℂ := fun i => y i with hy'def
  have hy' : y' ≠ 0 := by
    intro hz
    apply hy
    ext i
    exact congrFun hz i
  set φ : (Fin n → ℂ) → ℝ := fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y' with hφ
  have hrw : (fun v => fsLog h (nrmv h v) (h.pointOf y)) = fun v => φ (h.mat *ᵥ v) := by
    funext v
    exact h2 n h v y
  obtain ⟨hint, hle, hmean⟩ := h3 n y' hy'
  have habs : (fun w => |φ w|) = fun w => -φ w := by
    funext w
    exact abs_of_nonpos (hle w)
  have hmeanAbs : ⨍ v in ballH h, |φ (h.mat *ᵥ v)| = (harmonic (n - 1) : ℝ) / 2 := by
    rw [(h1 n h (fun w => |φ w|)).2, habs, average_neg, hmean]
    ring
  obtain ⟨_, hfin⟩ := h4 n h
  refine ⟨?_, ?_, ?_⟩
  · rw [hrw]
    exact (h1 n h φ).1.mpr hint
  · simp only [show ∀ v, fsLog h (nrmv h v) (h.pointOf y) = φ (h.mat *ᵥ v) from fun v => h2 n h v y]
    rw [← measure_smul_setAverage _ hfin.ne, hmeanAbs, smul_eq_mul, measureReal_def]
    ring
  · rw [hrw, (h1 n h φ).2]
    exact hmean

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogMeasurable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix

theorem FsLogMeasurable.proof : FsLogMeasurable.Statement := by
  intro n h
  have hn : Continuous h.norm := by
    unfold HermNorm.norm
    fun_prop
  have hd : Continuous h.dualNorm := by
    unfold HermNorm.dualNorm
    fun_prop
  have hp : Continuous h.pointOf := by
    unfold HermNorm.pointOf
    fun_prop
  have hinv : Measurable fun v : Fin n → ℂ => ((h.norm v : ℝ) : ℂ)⁻¹ :=
    (Complex.continuous_ofReal.comp hn).measurable.inv
  have hv : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => nrmv h p.1 := by
    unfold nrmv
    refine measurable_pi_lambda _ fun j => ?_
    exact (hinv.comp measurable_fst).mul ((measurable_pi_apply j).comp measurable_fst)
  have hy : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => h.pointOf p.2 :=
    hp.measurable.comp measurable_snd
  unfold fsLog
  refine Real.measurable_log.comp (Measurable.div ?_ (hd.measurable.comp hy))
  refine Measurable.norm ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp hv).mul ((measurable_pi_apply j).comp hy)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogSmul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem HermNorm.dualNorm_smul {n : ℕ} (h : HermNorm n) (t : ℂ) (y : Fin n → ℂ) :
    h.dualNorm (t • y) = ‖t‖ * h.dualNorm y := by
  unfold HermNorm.dualNorm
  rw [Matrix.mulVec_smul]
  have hs : (∑ i, ‖(t • ((h.mat)ᵀ⁻¹ *ᵥ y)) i‖ ^ 2) = ‖t‖ ^ 2 * ∑ i, ‖((h.mat)ᵀ⁻¹ *ᵥ y) i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem FsLogSmul.proof : FsLogSmul.Statement := by
  intro n h u y t ht
  unfold fsLog
  have hp : (∑ j, u j * (t • y) j) = t * ∑ j, u j * y j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring
  have ht' : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  rw [hp, h.dualNorm_smul, norm_mul, mul_div_mul_left _ _ ht']

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerAverageSplit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem mahler_specFirst_eq (h3 : EvalSpecFirst.Statement) {n e : ℕ} (h : HermNorm n)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (v : Fin n → ℂ) :
    mahler h e (specFirst f v) =
      sphereMean h e (fun w => Real.log ‖eval (consGroup v w) f‖) := by
  unfold mahler
  congr 1
  funext w
  rw [h3]

theorem MahlerAverageSplit.proof (h1 : MahlerIntegrand.Statement) (h2 : SphereMeanFubini.Statement)
    (h3 : EvalSpecFirst.Statement) : MahlerAverageSplit.Statement := by
  intro n e δ h f hf hhom
  have hint := h1 n (e + 1) δ h f hf hhom
  obtain ⟨hI, hM⟩ := h2 n e h (fun u => Real.log ‖eval u f‖) hint
  have key : (fun v => mahler h e (specFirst f (nrmv h v))) =
      fun v => sphereMean h e (fun w => Real.log ‖eval (consGroup (nrmv h v) w) f‖) := by
    funext v
    exact mahler_specFirst_eq h3 h f (nrmv h v)
  rw [key]
  exact ⟨hI, hM⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerIntegrand
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem ballProd_subset_polydisc {n k : ℕ} (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) :
    ballProd h k ⊆ LogInt.polydisc _ C := by
  intro u hu
  simp only [LogInt.polydisc, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  intro ij
  exact (hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)

theorem MahlerIntegrand.proof : MahlerIntegrand.Statement := by
  intro n k δ h f hf _
  obtain ⟨C, hC0, hC⟩ := h.li_exists_coord_le
  have e : nrmGroups h k = LogInt.normT h Finset.univ := by
    funext u ij
    simp [nrmGroups, LogInt.normT]
  rw [e]
  exact (LogInt.logNormT h C hC0 hC Finset.univ f hf).1.mono_set (ballProd_subset_polydisc h C hC0 hC)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem MahlerSection.proof (h₁ : MahlerSectionOfConst.Statement) (h₂ : DefectConstZero.Statement)
    (h₃ : DefectConstStep.Statement) : MahlerSection.Statement := by
  have hdim : ∀ e, MahlerSectionDim e := by
    intro e
    induction e with
    | zero => exact h₁ 0 h₂
    | succ e ih => exact h₁ (e + 1) (h₃ e ih)
  intro n e δ h Z f u hprime hchow hhom hadm
  exact hdim e n δ h Z f u ⟨hprime, hchow, hhom⟩ hadm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerSectionOfConst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem MahlerSectionOfConst.proof (h1 : DefectAverage.Statement) (h2 : AdmissibleAENrm.Statement)
    (h3 : BallVolume.Statement) : MahlerSectionOfConst.Statement := by
  intro e hconst n δ h Z f u data hu
  set K := mahlerDefect h e Z f u with hK
  have hrel : ∀ W ∈ Z.support, IsRelevant W := fun W hW => (data.prime W hW).isRelevant
  have hae : (fun v => mahlerDefect h e Z f (nrmv h v)) =ᵐ[volume.restrict (ballH h)] fun _ => K := by
    filter_upwards [h2 n h Z hrel] with v hv
    exact hconst n δ h Z f (nrmv h v) u data hv hu
  have havg : ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) = K := by
    rw [average_congr hae]
    obtain ⟨hpos, hfin⟩ := h3 n h
    exact setAverage_const hpos.ne' hfin.ne K
  have hmean := (h1 n e δ h Z f data).2
  rw [havg] at hmean
  have hK' : K = mahler h e (specFirst f u) - cycleIntegral h Z e (fsLog h u) := rfl
  linarith
end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerZeroSpec
section
set_option maxSynthPendingDepth 1

open MeasureTheory MvPolynomial

namespace GroundTheory.Heights₂.Heights

theorem eval_specFirst_zero {n : ℕ} (f : MvPolynomial (Fin 1 × Fin n) ℂ) (u : Fin n → ℂ)
    (v : Fin 0 × Fin n → ℂ) : eval v (specFirst f u) = eval (fun ij => u ij.2) f := by
  unfold specFirst
  show eval₂Hom (RingHom.id ℂ) v (bind₁ (specFirstVar u) f) = eval₂Hom (RingHom.id ℂ) _ f
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  obtain ⟨i, j⟩ := ij
  obtain rfl : i = 0 := Fin.fin_one_eq_zero i
  simp [specFirstVar]

theorem MahlerZeroSpec.proof : MahlerZeroSpec.Statement := by
  intro n h f u
  have hS : {v : Fin 0 × Fin n → ℂ | ∀ i : Fin 0, h.norm (fun j => v (i, j)) < 1} = Set.univ := by
    ext v; simp
  unfold mahler sphereMean
  rw [hS]
  simp_rw [eval_specFirst_zero]
  have h1 : (volume : Measure (Fin 0 × Fin n → ℂ)) Set.univ = 1 := by
    rw [volume_pi]; exact Measure.pi_empty_univ _
  exact setAverage_const (by simp [h1]) (by simp [h1]) _

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPointChowForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem PointChowForm.proof : PointChowForm.Statement := by
  intro n W g y hg hy hW
  obtain ⟨hg0, hgdiv⟩ := hg
  set φ := algebraMap ℂ (AlgebraicClosure ℂ) with hφ
  have hbij : Function.Bijective φ := IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hinj : Function.Injective φ := hbij.1
  set L : MvPolynomial (Fin 1 × Fin n) ℂ := ∑ j, C (y j) * X ((0 : Fin 1), j) with hL
  have hLu : ∀ u : Fin 1 × Fin n → AlgebraicClosure ℂ, aeval u L = ∑ j, φ (y j) * u (0, j) := by
    intro u; simp [hL, map_sum, hφ]

  have hvan : ∀ u ∈ incidence W 1, aeval u L = 0 := by
    rintro u ⟨x, hx0, hxW, hxu⟩
    choose x' hx' using fun j => hbij.2 (x j)
    have hxe : x = φ ∘ x' := funext fun j => (hx' j).symm
    have hW' : ∀ q ∈ W, eval x' q = 0 := by
      intro q hq
      have := hxW q hq
      rw [hxe, aeval_algebraMap_apply] at this
      exact hinj (by simpa using this)
    obtain ⟨t, ht⟩ := (hW x').1 hW'
    have ht0 : t ≠ 0 := by
      rintro rfl
      apply hx0
      rw [hxe, ht]
      ext j; simp
    have hsum := hxu 0
    have : ∑ j, u (0, j) * x j = φ t * aeval u L := by
      rw [hLu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hxe, ht]
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul]
      ring
    rw [this] at hsum
    exact (mul_eq_zero.1 hsum).resolve_left ((map_ne_zero φ).2 ht0)

  have h0inc : (0 : Fin 1 × Fin n → AlgebraicClosure ℂ) ∈ incidence W 1 := by
    refine ⟨φ ∘ y, ?_, ?_, ?_⟩
    · intro h
      apply hy
      ext j
      exact hinj (by simpa using congrFun h j)
    · intro q hq
      have : eval y q = 0 := (hW y).2 ⟨1, by simp⟩ q hq
      rw [aeval_algebraMap_apply]
      simp [this]
    · intro i; simp
  have hg_at0 : aeval (0 : Fin 1 × Fin n → AlgebraicClosure ℂ) g = 0 :=
    (hgdiv g).2 dvd_rfl 0 h0inc
  obtain ⟨k, hk⟩ := (hgdiv L).1 hvan

  have hL0 : L ≠ 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
    intro h
    apply hj
    have := congrArg (coeff (Finsupp.single ((0 : Fin 1), j) 1)) h
    simpa [hL, coeff_sum, coeff_C_mul, coeff_X, Finsupp.single_left_inj, Prod.ext_iff] using this
  have hk0 : k ≠ 0 := by rintro rfl; exact hL0 (by rw [hk, mul_zero])
  have hLdeg : L.totalDegree ≤ 1 := by
    rw [hL]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  have hgdeg : 1 ≤ g.totalDegree := by
    by_contra hlt
    have hgC := totalDegree_eq_zero_iff_eq_C.1 (by omega : g.totalDegree = 0)
    rw [hgC, aeval_C] at hg_at0
    apply hg0
    rw [hgC, (map_eq_zero_iff _ hinj).1 hg_at0, C_0]
  have hkdeg : k.totalDegree = 0 := by
    have := totalDegree_mul_of_isDomain hg0 hk0
    rw [← hk] at this
    omega
  obtain ⟨d, hd⟩ : ∃ d : ℂ, k = C d := ⟨_, totalDegree_eq_zero_iff_eq_C.1 hkdeg⟩
  have hd0 : d ≠ 0 := by rintro rfl; exact hk0 (by rw [hd, C_0])
  refine ⟨d⁻¹, inv_ne_zero hd0, ?_⟩
  rw [hk, hd, mul_comm g, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hd0, C_1, one_mul]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjDegreeChow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ProjDegreeChow.proof (h₁ : ProjSecDegree.Statement) (h₂ : ProjSecDomain.Statement)
    (h₃ : ProjChowNonzero.Statement) (h₄ : SecDegreeLe.Statement) (h₅ : SecDegreeGe.Statement) :
    ProjDegreeChow.Statement := by
  intro n e δ W f A hW hf hδ hA
  rw [h₁ n e W A]
  obtain ⟨hdom, hfin⟩ := h₂ n e W A hW.isPrime hA
  have hc := h₃ n e W f A hW hf hA
  have hsep : Algebra.IsSeparable (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
      (Vertical.SecAlg
        (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
        (projPar A)) :=
    ⟨fun x => PerfectField.separable_of_irreducible
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral x))⟩
  refine le_antisymm (h₄ ℂ _ n e δ W f (projPar A) hW hf hδ hfin hdom hsep fun h => hc ?_)
    (h₅ ℂ _ n e δ W f (projPar A) hW hf hδ hc).2
  rw [h, map_zero]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProperSymmCycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ProperSymmCycle.proof (h1 : ProperSymm.Statement) (h2 : SupportCycleSection.Statement) :
    ProperSymmCycle.Statement := by
  intro n Z u u' hprime hu hu' hadm W'' hW''
  obtain ⟨W, hW, hW''W⟩ := (h2 n Z u').2 W'' hW''
  have hadmW : IsAdmissible (divCycle W u) u' := fun W' hW' =>
    hadm W' ((h2 n Z u).1 W hW hW')
  exact h1 n W u u' (hprime W hW) (hu W hW) (hu' W hW) hadmW W'' hW''W

end GroundTheory.Heights₂.Heights
end

