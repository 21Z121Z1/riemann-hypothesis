import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.MemCoordIdealOfIsHomogeneous
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

namespace ResolutionL2SymmetricMeasure

set_option linter.unusedSectionVars false

variable {J : Type} [Fintype J]

theorem coneMap_of_isHomogeneous' {Ω : Type*} [CommRing Ω] [Algebra ℤ Ω] (x : J → Ω) {f : MvPolynomial J ℤ}
    {n : ℕ} (hf : f.IsHomogeneous n) :
    coneMap ℤ x f = Polynomial.C (aeval x f) * Polynomial.X ^ n := by
  simp only [coneMap, aeval_def, eval₂_eq, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = n := by
    have := hf (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp_rw [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum,
    hdeg, Polynomial.algebraMap_apply, map_mul, mul_assoc]

theorem mem_coordIdeal_of_isHomogeneous' {Ω : Type*} [CommRing Ω] [Algebra ℤ Ω] (x : J → Ω)
    {f : MvPolynomial J ℤ} {n : ℕ} (hf : f.IsHomogeneous n) (h : aeval x f = 0) : f ∈ coordIdeal ℤ x := by
  rw [coordIdeal, RingHom.mem_ker, coneMap_of_isHomogeneous' x hf, h, map_zero, zero_mul]

theorem continuous_conjPt' : Continuous (conjPt : (J → ℂ) → J → ℂ) :=
  continuous_pi fun i => Complex.continuous_conj.comp (continuous_apply i)

theorem eval_conjPt_int (f : MvPolynomial J ℤ) (z : J → ℂ) :
    eval (conjPt z) (map (Int.castRingHom ℂ) f) = conj (eval z (map (Int.castRingHom ℂ) f)) := by
  rw [eval_map, eval_map, eval₂_comp_left,
    RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ)]
  rfl

theorem measurable_rho (m : ConeMetric ℂ J) (hm : IsSmoothMetric m) : Measurable m.ρ :=
  measurable_of_continuousOn_compl_singleton 0 (hm.continuousOn.mono fun _ hz => hz)

theorem measurable_ptNorm (m : ConeMetric ℂ J) (hm : IsSmoothMetric m) (n : ℕ) (g : MvPolynomial J ℤ) :
    Measurable (ptNorm m (Int.castRingHom ℂ) n g) := by
  unfold ptNorm
  exact ((MvPolynomial.continuous_eval _).measurable.norm).div ((measurable_rho m hm).pow_const n)

theorem ptNorm_conjPt {m : ConeMetric ℂ J} (hm : IsConjInvariant m) (n : ℕ) (g : MvPolynomial J ℤ)
    (z : J → ℂ) : ptNorm m (Int.castRingHom ℂ) n g (conjPt z) = ptNorm m (Int.castRingHom ℂ) n g z := by
  unfold ptNorm
  rw [eval_conjPt_int, Complex.norm_conj, show m.ρ (conjPt z) = m.ρ z from hm z]

theorem ptNorm_eq_of_sub_mem {P : Ideal (MvPolynomial J ℤ)} {f g : MvPolynomial J ℤ} (hfg : f - g ∈ P)
    (m : ConeMetric ℂ J) (n : ℕ) {z : J → ℂ} (hz : ∀ h ∈ P, eval z (map (Int.castRingHom ℂ) h) = 0) :
    ptNorm m (Int.castRingHom ℂ) n f z = ptNorm m (Int.castRingHom ℂ) n g z := by
  have h := hz _ hfg
  rw [map_sub, eval_sub, sub_eq_zero] at h
  unfold ptNorm
  rw [h]

theorem resPt_mem {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (d : HSMDatum D Ω κ)
    (y : d.R.X) : ∀ h ∈ coordIdeal ℤ d.x, eval (resPt d y) (map (Int.castRingHom ℂ) h) = 0 :=
  (d.R.mem y y (d.R.mem_U y)).2

theorem full : ResolutionL2SymmetricMeasure.Statement := by
  intro D Ω _ _ κ _ d hmeas n f hf
  classical
  have hex : ∃ g : MvPolynomial (Ix κ) ℤ, g.IsHomogeneous n ∧ aeval d.x g = aeval d.x f := ⟨f, hf, rfl⟩
  unfold IndefiniteRowSideFullHecke.HilbertSamuel.secNorm
  rw [dif_pos hex]
  obtain ⟨hgh, hgx⟩ := hex.choose_spec
  generalize hex.choose = g at hgh hgx ⊢

  have hfg : f - g ∈ coordIdeal ℤ d.x :=
    mem_coordIdeal_of_isHomogeneous' d.x (hf.sub hgh) (by rw [map_sub, hgx, sub_self])
  unfold resolutionSectionL2Norm l2Norm
  set σ := Int.castRingHom ℂ
  have e1 : ∀ y, ptNorm d.m σ n f (resPt d y) = ptNorm d.m σ n g (resPt d y) := fun y =>
    ptNorm_eq_of_sub_mem hfg d.m n (resPt_mem d y)
  have e2 : ∀ y, ptNorm d.m σ n f (conjPt (resPt d y)) = ptNorm d.m σ n g (resPt d y) := fun y => by
    rw [ptNorm_conjPt d.conjInv, e1]
  congr 1
  simp_rw [e1, e2]
  have hψ : Measurable fun z => ptNorm d.m σ n g z ^ 2 := (measurable_ptNorm d.m d.smooth n g).pow_const 2
  have hA : AEMeasurable (resPt d) d.dV := hmeas.aemeasurable
  have hB : AEMeasurable (conjPt ∘ resPt d) d.dV := (continuous_conjPt'.measurable.comp hmeas).aemeasurable
  have hBψ : ∀ y, ptNorm d.m σ n g ((conjPt ∘ resPt d) y) ^ 2 = ptNorm d.m σ n g (resPt d y) ^ 2 := fun y => by
    rw [Function.comp_apply, ptNorm_conjPt d.conjInv]
  have iA : Integrable (fun z => ptNorm d.m σ n g z ^ 2) (d.dV.map (resPt d)) ↔
      Integrable (fun y => ptNorm d.m σ n g (resPt d y) ^ 2) d.dV :=
    integrable_map_measure hψ.aestronglyMeasurable hA
  have iB : Integrable (fun z => ptNorm d.m σ n g z ^ 2) (d.dV.map (conjPt ∘ resPt d)) ↔
      Integrable (fun y => ptNorm d.m σ n g (resPt d y) ^ 2) d.dV := by
    rw [integrable_map_measure hψ.aestronglyMeasurable hB]
    exact integrable_congr (Filter.Eventually.of_forall hBψ)
  have jA : ∫ z, ptNorm d.m σ n g z ^ 2 ∂(d.dV.map (resPt d)) =
      ∫ y, ptNorm d.m σ n g (resPt d y) ^ 2 ∂d.dV :=
    integral_map hA hψ.aestronglyMeasurable
  have jB : ∫ z, ptNorm d.m σ n g z ^ 2 ∂(d.dV.map (conjPt ∘ resPt d)) =
      ∫ y, ptNorm d.m σ n g (resPt d y) ^ 2 ∂d.dV := by
    rw [integral_map hB hψ.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall hBψ)
  unfold IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure
  rw [integral_smul_measure]
  by_cases hi : Integrable (fun y => ptNorm d.m σ n g (resPt d y) ^ 2) d.dV
  · rw [integral_add_measure (iA.2 hi) (iB.2 hi), jA, jB]
    simp
  · have hn : ¬ Integrable (fun z => ptNorm d.m σ n g z ^ 2) (d.dV.map (resPt d) + d.dV.map (conjPt ∘ resPt d)) := by
      rw [integrable_add_measure]
      exact fun h => hi (iA.1 h.1)
    rw [integral_undef hn, integral_undef hi]
    simp

end ResolutionL2SymmetricMeasure

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockMetricChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem BlockMetricChange.proof (hMeas : BlockMeasureChange.Statement)
    (hMet : BlockDefectMetricChange.Statement) : BlockMetricChange.Statement := by
  intro D K _ _ ι _ Ω _ _ I d d' hI hy hk
  have hdeg : d'.A.a = unitDeg d.k₀ := hk ▸ d'.deg
  have hle : d'.P0 ≤ mCoordIdeal d.y := hy ▸ d'.normalForm_baseLattice_le_dualSpan_sup_line
  have hp : IsSemipositiveRel d'.P0 (mCoordIdeal d.y) d'.A := hy ▸ d'.semipos

  have h1 := hMeas D K ι Ω (d.withMetric d'.A d'.P0 hdeg d'.conjInv hle hp) d' hy hk rfl
  have h2 := hMet D K ι Ω I d d'.A d'.P0 hdeg d'.conjInv hle hp hI
  refine (h1.add h2).congr_left fun n => ?_
  simp only [hsDefect, hy]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

theorem FibreNormBound.proof (h₁ : ProjAvoidingForm.Statement) (h₂ : FibreRepresentatives.Statement)
    (h₃ : FibreNormMax.Statement) (h₄ : MetricMaxComparison.Statement) : FibreNormBound.Statement := by
  intro K _ ι _ Ω _ y D A df f hV hB hA hf hfP
  obtain ⟨e, L, G, he, hL, hL0, hG, hGf⟩ := h₁ K ι Ω y D df f hV hf hfP
  obtain ⟨n, c, B, hn, hB1, hF⟩ := h₃ K ι Ω y D A.a e L hV hB he hL hL0
  obtain ⟨C, hC, hAC⟩ := h₄ K ι A hA
  choose S hS₁ hS₂ using h₂ K ι Ω y D e L he hL hL0
  refine ⟨n, c, B * C ^ n, G, S, hn, one_le_mul_of_one_le_of_one_le hB1 (one_le_pow₀ hC), hG, ?_, ?_⟩
  · intro ζ _ hGζ z hz
    obtain ⟨hzP, t, ht⟩ := hS₁ ζ z hz
    exact ⟨hzP, hGf ζ hGζ z hzP ⟨t, ht⟩⟩
  · intro τ u hu hu0
    obtain ⟨F, hF0, hFdeg, hFb⟩ := hF τ u hu hu0
    refine ⟨F, hF0, hFdeg, fun ζ hζ _ M hM hrep => ?_⟩
    have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
    have key := hFb ζ hζ (S ζ) (hS₂ ζ) (M * C ^ τ) (by positivity) (fun z hz => by
      obtain ⟨dg, dh, g, h, hg, hh, hd, hgh, hz0, hle⟩ := hrep z hz
      refine ⟨dg, dh, g, h, hg, hh, hd, hgh, hz0, ?_⟩
      have hzb := (hS₁ ζ z hz).1.1
      have h0 : 0 ≤ A.h z := (A.pos z hzb).le
      calc ‖eval z (map (Int.castRingHom ℂ) g)‖
          ≤ M * A.h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) h)‖ := hle
        _ ≤ M * (C * (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) A.a).h z) ^ τ *
              ‖eval z (map (Int.castRingHom ℂ) h)‖ := by
            gcongr
            exact hAC z hzb
        _ = M * C ^ τ * (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) A.a).h z ^ τ *
              ‖eval z (map (Int.castRingHom ℂ) h)‖ := by ring)
    have hB0 : (0 : ℝ) ≤ B := zero_le_one.trans hB1
    have hpow : C ^ (τ * n) ≤ C ^ (n * (τ + 1)) :=
      pow_le_pow_right₀ hC (by rw [Nat.mul_comm n]; exact Nat.mul_le_mul_right n (Nat.le_succ τ))
    calc ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * (M * C ^ τ) ^ n := key
      _ = B ^ (τ + 1) * M ^ n * C ^ (τ * n) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ B ^ (τ + 1) * M ^ n * C ^ (n * (τ + 1)) := by gcongr
      _ = (B * C ^ n) ^ (τ + 1) * M ^ n := by rw [mul_pow, ← pow_mul]; ring

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegGeomDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

theorem GenDegGeomDeg.proof (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    GenDegGeomDeg.Statement := by
  intro K _ ι _ Ω _ y D A hV hA
  classical
  have h := hDG K ι (mCoordIdeal y) D (fun _ => A) hV (fun _ => hA)
  have hpot : pot (fun _ : Fin D => A) = fun (_ : Fin D) z => Real.log (A.h z) := rfl
  rw [hpot] at h
  unfold geomDeg genDeg
  rw [h]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegMatAct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenDegMatAct

section Subst

variable {J : Type} [Fintype J]

def linSubst (B : Matrix J J ℚ) : MvPolynomial J ℚ →ₐ[ℚ] MvPolynomial J ℚ :=
  aeval fun i => ∑ j, C (B i j) * X j

theorem linSubst_comp (B B' : Matrix J J ℚ) :
    (linSubst B).comp (linSubst B') = linSubst (B' * B) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [linSubst, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem linSubst_one [DecidableEq J] : linSubst (1 : Matrix J J ℚ) = AlgHom.id ℚ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [linSubst, Matrix.one_apply, apply_ite C, ite_mul]

theorem exists_inv [DecidableEq J] {B : Matrix J J ℚ} (hB : IsInvMat B) : ∃ B' : Matrix J J ℚ, B * B' = 1 ∧ B' * B = 1 := by
  classical
  obtain ⟨B', h⟩ := hB
  refine ⟨B', ?_, ?_⟩ <;> rw [Matrix.ext_iff_mulVec] <;> intro v <;>
    simp [← Matrix.mulVec_mulVec, (h v).1, (h v).2]

def linEquiv [DecidableEq J] (B B' : Matrix J J ℚ) (h₁ : B * B' = 1) (h₂ : B' * B = 1) :
    MvPolynomial J ℚ ≃ₐ[ℚ] MvPolynomial J ℚ :=
  AlgEquiv.ofAlgHom (linSubst B) (linSubst B') (by rw [linSubst_comp, h₂, linSubst_one])
    (by rw [linSubst_comp, h₁, linSubst_one])

theorem isHomogeneous_linSubst (B : Matrix J J ℚ) {f : MvPolynomial J ℚ} {n : ℕ} (hf : f.IsHomogeneous n) :
    (linSubst B f).IsHomogeneous n := by
  have h := hf.aeval (fun i => ∑ j, C (B i j) * X j) (n := 1) fun i =>
    IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_C J (B i j)).mul (isHomogeneous_X ℚ j)
  simpa [linSubst] using h

end Subst

section Ideals

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem coneMap_matAct (B : Matrix J J ℚ) (x : J → Ω) :
    coneMap ℚ (matAct B x) = (coneMap ℚ x).comp (linSubst B) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [coneMap, matAct, linSubst, Finset.sum_mul, mul_assoc, Polynomial.algebraMap_apply]

theorem coordIdeal_matAct (B : Matrix J J ℚ) (x : J → Ω) :
    coordIdeal ℚ (matAct B x) = (coordIdeal ℚ x).comap (linSubst B) := by
  ext f
  simp [coordIdeal, RingHom.mem_ker, coneMap_matAct]

omit [Fintype J] in

theorem map_coordIdeal_int (x : J → Ω) :
    (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) = coordIdeal ℚ x := by
  have hring : ((coneMap ℚ x : MvPolynomial J ℚ →+* Polynomial Ω).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) = (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coneMap]
    · intro i
      simp [coneMap]
  have hker : coordIdeal ℤ x = (coordIdeal ℚ x).comap (MvPolynomial.map (Int.castRingHom ℚ)) := by
    ext f
    rw [Ideal.mem_comap]
    simp only [coordIdeal, RingHom.mem_ker]
    have h := RingHom.congr_fun hring f
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h
    rw [h]
  let _ := MvPolynomial.algebraMvPolynomial (σ := J) (R := ℤ) (S := ℚ)
  have e : algebraMap (MvPolynomial J ℤ) (MvPolynomial J ℚ) = MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  have h := IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := J))) (MvPolynomial J ℚ)
    (coordIdeal ℚ x)
  rw [e] at h
  rw [hker]
  exact h

end Ideals

section Hilbert

variable {κ : Type} [Fintype κ]

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem isWeightedHomogeneous_iff (f : MvPolynomial (Ix κ) ℚ) (m : Unit → ℕ) :
    IsWeightedHomogeneous (blockWeight (GlobalTheory κ)) f m ↔ f.IsHomogeneous (m ()) := by
  have hdeg : ∀ d : Ix κ →₀ ℕ, ∑ i : κ, d ⟨(), i⟩ = Finsupp.weight 1 d := by
    intro d
    have h1 : d.degree = Finsupp.weight 1 d := by
      rw [Finsupp.degree_eq_weight_one]
      rfl
    rw [← h1, Finsupp.degree_eq_sum, Fintype.sum_sigma]
    exact (Fintype.sum_unique (fun u : Unit => ∑ y : GlobalTheory κ u, d ⟨u, y⟩)).symm
  have hw : ∀ d : Ix κ →₀ ℕ, Finsupp.weight (blockWeight (GlobalTheory κ)) d = fun _ => Finsupp.weight 1 d := by
    intro d
    funext u
    cases u
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
    simp [blockWeight]
  simp only [IsHomogeneous, IsWeightedHomogeneous, hw]
  constructor
  · intro h d hd
    exact congrFun (h hd) ()
  · intro h d hd
    funext u
    exact h hd

theorem mem_weighted_linSubst (B : Matrix (Ix κ) (Ix κ) ℚ) {m : Unit → ℕ} {f : MvPolynomial (Ix κ) ℚ}
    (hf : f ∈ weightedHomogeneousSubmodule ℚ (blockWeight (GlobalTheory κ)) m) :
    linSubst B f ∈ weightedHomogeneousSubmodule ℚ (blockWeight (GlobalTheory κ)) m := by
  rw [mem_weightedHomogeneousSubmodule, isWeightedHomogeneous_iff] at hf ⊢
  exact isHomogeneous_linSubst B hf

theorem hilbFn_comap [DecidableEq κ] (B B' : Matrix (Ix κ) (Ix κ) ℚ) (h₁ : B * B' = 1) (h₂ : B' * B = 1)
    (P : Ideal (MRing (GlobalTheory κ) ℚ)) : NumbersDVR.hilbFn (P.comap (linSubst B)) = NumbersDVR.hilbFn P := by
  set e := linEquiv B B' h₁ h₂
  have hc : P.comap (linSubst B) = P.comap e := by
    ext f
    rfl
  have hIJ : P = (P.comap e).map (e : MRing (GlobalTheory κ) ℚ →+* MRing (GlobalTheory κ) ℚ) :=
    (Ideal.map_comap_of_surjective _ e.surjective P).symm
  set E := Ideal.quotientEquivAlg (R₁ := ℚ) (P.comap e) P e hIJ
  have hpiece : ∀ m : Unit → ℕ, (NumbersDVR.gradedPiece (P.comap e) m).map E.toLinearEquiv.toLinearMap = NumbersDVR.gradedPiece P m := by
    intro m
    ext y
    simp only [NumbersDVR.gradedPiece, Submodule.mem_map]
    constructor
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      refine ⟨e f, mem_weighted_linSubst B hf, ?_⟩
      simp [E, Ideal.quotientEquivAlg_mk]
    · rintro ⟨g, hg, rfl⟩
      refine ⟨_, ⟨e.symm g, mem_weighted_linSubst B' hg, rfl⟩, ?_⟩
      simp [E, Ideal.quotientEquivAlg_mk]
  funext m
  unfold NumbersDVR.hilbFn
  rw [hc]
  split_ifs
  · rw [← hpiece, LinearEquiv.finrank_map_eq]
  · rfl

end Hilbert

end GenDegMatAct

theorem GenDegMatAct.proof : GenDegMatAct.Statement := by
  intro D Ω _ _ κ _ x B hB
  classical
  obtain ⟨B', h₁, h₂⟩ := GenDegMatAct.exists_inv hB
  unfold genDeg
  rw [GenDegMatAct.map_coordIdeal_int, GenDegMatAct.map_coordIdeal_int, GenDegMatAct.coordIdeal_matAct]
  unfold NumbersDVR.intNum
  congr 2
  convert GenDegMatAct.hilbFn_comap B B' h₁ h₂ (coordIdeal ℚ x)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenFibreHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace GenFibreHomog

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sum_block_eq_weight (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    ∑ i, m ⟨k, i⟩ = Finsupp.weight (NumbersDVR.blockWeight ι) m k := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]

theorem isMultiHomog_of_weighted {f : MRing ι} {b : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f b) : IsMultiHomog f b := by
  intro m hm k
  rw [sum_block_eq_weight, hf (mem_support_iff.mp hm)]

theorem coeff_mConeMap {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (b : K → ℕ) (f : MRing ι) :
    coeff (Finsupp.equivFunOnFinite.symm b) (mConeMap y f) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) m c
      (rfl : Finsupp.weight (NumbersDVR.blockWeight ι) m = _)
    rw [ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_of_weighted hm),
      weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm)]
    have hX : (∏ k, (X k : MvPolynomial K Ω) ^ Finsupp.weight (NumbersDVR.blockWeight ι) m k) =
        monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (NumbersDVR.blockWeight ι) m)) 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      simp
    rw [hX, coeff_C_mul, coeff_monomial]
    by_cases h : b = Finsupp.weight (NumbersDVR.blockWeight ι) m
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm)]
      simp
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, map_add, map_add]

theorem isMultiHomogIdeal_mCoordIdeal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) :
    NumbersDVR.IsMultiHomogIdeal (R := ℤ) (mCoordIdeal y) := by
  intro f hf b
  have hf' : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  refine RingHom.mem_ker.mpr ?_
  change mConeMap y _ = 0
  rw [ProjLine.mConeMap_eq_of_isMultiHomog y
      (isMultiHomog_of_weighted (weightedHomogeneousComponent_isWeightedHomogeneous b f)),
    ← coeff_mConeMap, hf', coeff_zero, map_zero, zero_mul]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

omit [∀ k, Fintype (ι k)] in

theorem isHomogeneous_of_isMultiHomogIdeal {R : Type} [CommRing R] {I : Ideal (MvPolynomial (Σ k, ι k) R)}
    (h : NumbersDVR.IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule R (NumbersDVR.blockWeight ι)) := by
  intro b f hf
  have key : (DirectSum.decompose (weightedHomogeneousSubmodule R (NumbersDVR.blockWeight ι)) f b :
      MvPolynomial (Σ k, ι k) R) = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f :=
    weightedDecomposition.decompose'_apply R (NumbersDVR.blockWeight ι) f b
  rw [key]
  exact h f hf b

end GenFibreHomog

open GenFibreHomog in
attribute [local instance] MvPolynomial.weightedGradedAlgebra in

theorem GenFibreHomog.proof : GenFibreHomog.Statement := by
  intro K _ _ ι _ Ω _ y
  have hI := isHomogeneous_of_isMultiHomogIdeal (isMultiHomogIdeal_mCoordIdeal y)
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists _ _).mp hI
  have hJ : ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))).IsHomogeneous
      (weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι)) := by
    rw [hS, Ideal.map_span]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩
    obtain ⟨b, hb⟩ := s.2
    refine ⟨b, ?_⟩
    rw [mem_weightedHomogeneousSubmodule] at hb ⊢
    intro d hd
    apply hb
    intro h0
    apply hd
    rw [coeff_map, h0, map_zero]
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem ℚ _ hJ hf b

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

