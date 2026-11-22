import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.FibreCurve
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsIntegralLogNormRat
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0088
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0077
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0078
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSerreGraded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0063
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsNonzero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0071
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0070
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0065
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.UnipotentCharacter
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0069
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0112
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0011
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CoordRatioDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def CoordRatioDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k', ι' k') → Ω) (Φ' : Type) [Field Φ'] [CharZero Φ'] (x' : (Σ k', ι' k') → Φ'),
    IsBlockMap κ v → RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Φ') = mCoordIdeal y →
    IntermediateField.relfinrank (blockFnField (x' ∘ v)) (blockFnField x') =
      IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.FibreMultiHomog
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def FibreMultiHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (G : GenFibre v P'),
    IsBlockMap κ v → IsMultiHomogIdeal P' → IsMultiHomogIdeal (fibreIdeal κ G)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GenDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights.Inter

theorem GenDeg.of_found (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement) (hInt : ArithmeticIntersectionIntegral.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement :=
  PushforwardArithIntersection.proof arithVarZero hRat hCyc hInt

theorem GenDeg.of_pts (hPts : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) (hSec : IntersectionWithSection.Statement)
    (hCyc : ArithmeticIntersectionCycle.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement :=
  GenDeg.of_found (RatR.proof hPts) hCyc (ArithmeticIntersectionIntegral.proof hPts hSec)

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GenFibreChartDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def GenFibreChartDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (G : GenFibre v P')
    [CharZero G.Φ'] (c : ∀ k, ι k) (i : ∀ k : FibreBlock κ, fibreIdx ι' κ k),
    IsBlockMap κ v → IsMultiHomogIdeal P' → (∀ k, G.x ⟨k, c k⟩ ≠ 0) → (∀ k, G.x' ⟨k.1, i k⟩ ≠ 0) →
    Module.finrank G.Φ (IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k =>
        G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩)) =
      IntermediateField.relfinrank (blockFnField (G.x' ∘ v)) (blockFnField G.x')

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHSFull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SecMRankBound.full : SecMRankBound.Statement :=
  SecMRankBound.proof GenericFibreVar.proof

theorem SublatticeDegree.full : SublatticeDegree.Statement :=
  SublatticeDegree.proof SublatticeExtension.proof SpanningExtension.proof CovolumeLeGram.proof
    GramContraction.proof

theorem PackingStatement.of_leaves (hC : KH.CondStatement) (hG : GridSeparation.Statement) :
    ReciprocityTheory.ChartRestriction.G.Geo.PackingStatement :=
  SmallPacking.proof (NmSectionsRankBound.proof (NmSectionsFinite.proof hC) SecMRankBound.full)
    (SmallSectionsSeparated.proof hG)

theorem SuccessiveMinimaSpan.of_leaves (hC : KH.CondStatement) (hR : RelSectionsLarge.Statement) : SuccessiveMinimaSpan.Statement :=
  SuccessiveMinimaSpan.proof
    (SectionRingFinite.proof (SectionLatticeFinite.proof hC)
      (SectionSpanStep.proof (SpanStepHomog.proof (SpanStepLocal.proof (RelLatticeFinite.proof hR)))
        SerreGraded.proof))
    SectionBounded.proof SectionBoundedMul.proof

theorem G7.of_leaves (hC : KH.CondStatement) (hR : RelSectionsLarge.Statement)
    (hL2 : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement) : G7.Statement :=
  G7.proof (SuccessiveMinimaSpan.of_leaves hC hR)
    (EuclideanSections.proof (EuclideanSectionsPower.proof hL2 hP) SmallSectionsNonzero.proof
      SublatticeDegree.full (SuccessiveMinimaSpan.of_leaves hC hR))

theorem NefCountLower.of_leaves (hM : NefCountAlongMultiples.Statement)
    (hS : NefSmallSectionEventually.Statement) (hC : KH.CondStatement) (hG : GridSeparation.Statement) :
    NefCountLower.Statement :=
  NefCountLower.proof hM hS (PackingStatement.of_leaves hC hG)

theorem NefCountUpper.of_leaves (hApx : NefSmallApprox.Statement) (hCurve : NefCountUpperCurve.Statement)
    (hC : KH.CondStatement) (hG : GridSeparation.Statement) (hR : RelSectionsLarge.Statement)
    (hL2 : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement) : NefCountUpper.Statement :=
  NefCountUpper.proof hApx hCurve (G7.of_leaves hC hR hL2 hP) (PackingStatement.of_leaves hC hG)

theorem MoriwakiHS.of_leaves (hC : KH.CondStatement) (hG : GridSeparation.Statement)
    (hR : RelSectionsLarge.Statement) (hL2 : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement)
    (hM : NefCountAlongMultiples.Statement) (hS : NefSmallSectionEventually.Statement)
    (hApx : NefSmallApprox.Statement) (hCurve : NefCountUpperCurve.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement :=
  MoriwakiHS.of_found (NefCountLower.of_leaves hM hS hC hG)
    (NefCountUpper.of_leaves hApx hCurve hC hG hR hL2 hP)

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartSheetNoRatNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace ChartSheetNoRatNull

variable {n d : ℕ}

theorem differentiable_eval (P : MvPolynomial (Fin n) ℂ) :
    Differentiable ℂ (fun z : Fin n → ℂ => eval z P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [eval_add]; exact hp.add hq
  | mul_X p i hp => simp only [eval_mul, eval_X]; exact hp.mul (differentiable_apply i)

theorem exists_poly_of_not_mem {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (hJ : J.IsPrime) (hA : IsFiniteProjection J A) (hq : q ∉ J) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ ∀ x ∈ zeroSet J, eval x q = 0 → eval (A *ᵥ x) c = 0 := by
  classical
  have hv0 : Ideal.Quotient.mk J q ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hq
  have hex : ∃ k, ∃ P : Polynomial (MvPolynomial (Fin d) ℂ), P.Monic ∧ P.natDegree = k ∧
      P.eval₂ (projHom J A).toRingHom (Ideal.Quotient.mk J q) = 0 := by
    obtain ⟨P, hPm, hP⟩ := hA.finite.to_isIntegral (Ideal.Quotient.mk J q)
    exact ⟨_, P, hPm, rfl, hP⟩
  obtain ⟨P, hPm, hPk, hP⟩ := Nat.find_spec hex
  have hc0 : P.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨Q, rfl⟩ := Polynomial.X_dvd_iff.2 h0
    have hQm : Q.Monic := Polynomial.monic_X.of_mul_monic_left hPm
    have hdeg : (Polynomial.X * Q).natDegree = Q.natDegree + 1 :=
      Polynomial.natDegree_X_mul hQm.ne_zero
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_X, mul_eq_zero] at hP
    refine Nat.find_min hex (m := Q.natDegree) (by omega) ⟨Q, hQm, rfl, ?_⟩
    exact hP.resolve_left hv0
  have hQ : Ideal.Quotient.mk J (P.eval₂ (pullback A).toRingHom q) = 0 := by
    rw [Polynomial.hom_eval₂]; exact hP
  have hQJ := Ideal.Quotient.eq_zero_iff_mem.1 hQ
  refine ⟨P.coeff 0, hc0, fun x hx hqx => ?_⟩
  have h1 : eval x (P.eval₂ (pullback A).toRingHom q) = 0 := hx _ hQJ
  rw [Polynomial.hom_eval₂, hqx, Polynomial.eval₂_at_zero] at h1
  have h2 : eval x (pullback A (P.coeff 0)) = 0 := h1
  rwa [ComplexSets.eval_pullback] at h2

theorem volume_image_zero {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (hJ : J.IsPrime) (hA : IsFiniteProjection J A) (hq : q ∉ J) :
    volume ((fun x => A *ᵥ x) '' {x | x ∈ zeroSet J ∧ eval x q = 0}) = 0 := by
  obtain ⟨c, hc, hcz⟩ := exists_poly_of_not_mem hJ hA hq
  refine measure_mono_null ?_ (DiscriminantSheetCover.volume_zero_set c hc)
  rintro _ ⟨x, ⟨hx, hqx⟩, rfl⟩
  exact hcz x hx hqx

theorem isOpen_dom {U : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ} (q : MvPolynomial (Fin n) ℂ)
    (hU : IsOpen U) (hsd : DifferentiableOn ℂ s U) : IsOpen (U ∩ s ⁻¹' {x | eval x q ≠ 0}) :=
  hsd.continuousOn.isOpen_inter_preimage hU
    (isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const)

theorem differentiableOn_ratMap_comp {U : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ}
    (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) (hsd : DifferentiableOn ℂ s U) :
    DifferentiableOn ℂ (fun w => RatChart.ratMap p q (s w)) (U ∩ s ⁻¹' {x | eval x q ≠ 0}) := by
  rw [differentiableOn_pi]
  intro r
  have hs' := hsd.mono (Set.inter_subset_left (t := s ⁻¹' {x | eval x q ≠ 0}))
  have hnum : DifferentiableOn ℂ (fun w => eval (s w) (p r)) (U ∩ s ⁻¹' {x | eval x q ≠ 0}) :=
    (differentiable_eval (p r)).comp_differentiableOn hs'
  have hden : DifferentiableOn ℂ (fun w => eval (s w) q) (U ∩ s ⁻¹' {x | eval x q ≠ 0}) :=
    (differentiable_eval q).comp_differentiableOn hs'
  show DifferentiableOn ℂ (fun w => eval (s w) (p r) / eval (s w) q) _
  simp only [div_eq_mul_inv]
  exact hnum.mul (hden.inv fun w hw => hw.2)

theorem exists_det_ne_zero {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ}
    (hfin : ∀ y, (RatChart.ratFibre J p q y).Finite) {U : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ}
    (hsd : DifferentiableOn ℂ s U) (hsec : ∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    {W₀ : Set (Fin d → ℂ)} (hW₀ : IsOpen W₀) (hW₀D : W₀ ⊆ U ∩ s ⁻¹' {x | eval x q ≠ 0})
    (hne : W₀.Nonempty) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => RatChart.ratMap p q (s w)) w).det ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨y, hy⟩ := CriticalFibreInfinite.proof d d W₀ (fun w => RatChart.ratMap p q (s w)) hW₀ hne
    ((differentiableOn_ratMap_comp p q hsd).mono hW₀D)
    (fun t ht hinj => (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
      (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall t ht))
  refine hy (Set.Finite.of_finite_image (f := s) ((hfin y).subset ?_) ?_)
  · rintro _ ⟨t, ⟨htW, hty⟩, rfl⟩
    exact ⟨(hsec t (hW₀D htW).1).2, (hW₀D htW).2, hty⟩
  · intro a ha b hb hab
    rw [← (hsec a (hW₀D ha.1).1).1, ← (hsec b (hW₀D hb.1).1).1]
    exact congrArg _ hab

theorem exists_ratSheet_of_det_ne_zero {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ} {x : Fin n → ℂ}
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) (hqx : eval x q ≠ 0)
    (hdet : (ReciprocityTheory.AnForm.A.jacC (fun w => RatChart.ratMap p q (s w)) (A *ᵥ x)).det ≠ 0) :
    ∃ s', RatChart.IsRatSheetAt J p q x s' := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set D := U ∩ s ⁻¹' {x | eval x q ≠ 0} with hDdef
  have hD : IsOpen D := isOpen_dom q hU hsd
  have hyD : A *ᵥ x ∈ D := ⟨hyU, by simp only [Set.mem_preimage, hsx]; exact hqx⟩
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => RatChart.ratMap p q (s w) with hFdef
  have hFd : DifferentiableOn ℂ F D := differentiableOn_ratMap_comp p q hsd
  have hFa := SheetOnlyNull.analyticOnNhd_of_differentiableOn hD hFd
  set G : Set (Fin d → ℂ) := D ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := (SheetOnlyNull.analyticOnNhd_det_jacC hD hFd).continuousOn
    |>.isOpen_inter_preimage hD isOpen_compl_singleton
  have hinj : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w) :=
    fun w hw => (SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    refine ⟨(LinearEquiv.ofInjectiveEndo _ (hinj w hw.2)).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  obtain ⟨e, he⟩ := hequiv _ ⟨hyD, hdet⟩
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hysrc : A *ᵥ x ∈ φ.source := he.mem_toOpenPartialHomeomorph_source
  have hFx : F (A *ᵥ x) = RatChart.ratMap p q x := by simp only [hFdef, hsx]
  have hsym : φ.symm (RatChart.ratMap p q x) = A *ᵥ x := by rw [← hFx, ← hφ, φ.left_inv hysrc]
  refine ⟨s ∘ φ.symm, φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG,
    ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hyD, hdet⟩⟩,
    ?_, by simp only [Function.comp_apply, hsym, hsx],
    fun z hz => ⟨(hsec _ hz.2.1.1).2, hz.2.1.2, ?_⟩, ?_⟩
  · intro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hsymd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact ((hsd.differentiableAt (hU.mem_nhds hzG.1.1)).comp z
      hsymd.differentiableAt).differentiableWithinAt
  · show F (φ.symm z) = z
    rw [← hφ, φ.right_inv hz.1]
  · refine ⟨V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ D), inter_mem hV
      (((φ.open_source.inter hD).preimage (by fun_prop)).mem_nhds ⟨hysrc, hyD⟩), ?_⟩
    rintro x'' ⟨hx''Z, hx''V, hx''src, hx''D⟩ - -
    have hx'' : x'' = s (A *ᵥ x'') := hVs x'' ⟨hx''Z, hx''V⟩ hx''D.1
    have hR : RatChart.ratMap p q x'' = φ (A *ᵥ x'') := by
      rw [hφ]
      show RatChart.ratMap p q x'' = RatChart.ratMap p q (s (A *ᵥ x''))
      exact congrArg _ hx''
    rw [Function.comp_apply, hR, φ.left_inv hx''src]
    exact hx''

end ChartSheetNoRatNull

open ChartSheetNoRatNull in

theorem ChartSheetNoRatNull.proof : ChartSheetNoRatNull.Statement := by
  intro n d J A p q hJ _ hA hq hfin
  set B := {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧ eval x q ≠ 0 ∧
    ¬ ∃ s', RatChart.IsRatSheetAt J p q x s'} with hBdef
  choose σ Us W hUs hW hσd hWsh hxW using
    fun x : Fin n → ℂ => SheetOnlyNull.exists_sheet_nhds (J := J) (A := A) x
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hpiece : ∀ i, volume ((fun x => A *ᵥ x) '' (B ∩ W i)) = 0 := by
    intro i
    apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro _ ⟨x, ⟨hxB, hxWi⟩, rfl⟩
    obtain ⟨-, hsh⟩ := hWsh i x ⟨hxB.1, hxWi⟩
    obtain ⟨U', hU', hyU', hsd', hsx, hsec', -⟩ := hsh
    have hD' := isOpen_dom q hU' hsd'
    have hAxD : A *ᵥ x ∈ U' ∩ σ i ⁻¹' {x | eval x q ≠ 0} :=
      ⟨hyU', by simp only [Set.mem_preimage, hsx]; exact hxB.2.2.1⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD' _ hAxD
    refine ⟨Metric.ball (A *ᵥ x) r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      (convex_ball _ r).isPreconnected,
      fun w => (ReciprocityTheory.AnForm.A.jacC (fun v => RatChart.ratMap p q (σ i v)) w).det,
      (SheetOnlyNull.analyticOnNhd_det_jacC hD' (differentiableOn_ratMap_comp p q hsd')).mono hball,
      exists_det_ne_zero hfin hsd' hsec' Metric.isOpen_ball hball ⟨_, Metric.mem_ball_self hr⟩, ?_⟩
    rintro _ ⟨⟨x'', ⟨hx''B, hx''W⟩, rfl⟩, -⟩
    by_contra hne
    exact hx''B.2.2.2
      (exists_ratSheet_of_det_ne_zero (hWsh i x'' ⟨hx''B.1, hx''W⟩).2 hx''B.2.2.1 hne)
  have hBnull : volume ((fun x => A *ᵥ x) '' B) = 0 := by
    refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun i _ => hpiece i)
    rintro _ ⟨x, hxB, rfl⟩
    have hx : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxB.2.1⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_biUnion hiT ⟨x, ⟨hxB, hxi⟩, rfl⟩
  refine measure_mono_null ?_ (measure_union_null hBnull (volume_image_zero hJ hA hq))
  rintro _ ⟨x, ⟨hxZ, hxs, hnot⟩, rfl⟩
  by_cases hqx : eval x q = 0
  · exact Or.inr ⟨x, ⟨hxZ, hqx⟩, rfl⟩
  · exact Or.inl ⟨x, ⟨hxZ, hxs, hqx, hnot⟩, rfl⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PComponentsPairPoly
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

namespace ComponentsGenericCount

theorem exists_pair_poly {n d : ℕ} (J J' : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hJ : J.IsPrime) (hA : IsFiniteProjection J A) (hJJ' : ¬ J' ≤ J) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ ∀ x ∈ zeroSet J, x ∈ zeroSet J' → eval (A *ᵥ x) c = 0 := by
  obtain ⟨f, hfJ', hfJ⟩ := SetLike.not_le_iff_exists.1 hJJ'
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := (projHom J A).toRingHom.toAlgebra
  have := hJ
  have hf0 : Ideal.Quotient.mk J f ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hint : IsIntegral (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J f) := hA.finite.to_isIntegral _
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.mem_span_singleton_self _) hint)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hc)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨c, hc0, fun x hx hx' => ?_⟩
  have h1 : Ideal.Quotient.mk J (pullback A c) = Ideal.Quotient.mk J (r * f) := by
    rw [map_mul]; exact hr.symm
  have h2 := hx _ (Ideal.Quotient.eq.1 h1)
  rwa [map_sub, map_mul, hx' f hfJ', mul_zero, sub_zero, ComplexSets.FibreBound.eval_pullback] at h2

theorem encard_biUnion_le {ι α : Type*} (F : Finset ι) (S : ι → Set α) :
    (⋃ i ∈ F, S i).encard ≤ ∑ i ∈ F, (S i).encard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (by gcongr)

theorem encard_biUnion_eq {ι α : Type*} (F : Finset ι) (S : ι → Set α)
    (h : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j)) :
    (⋃ i ∈ F, S i).encard = ∑ i ∈ F, (S i).encard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert, Set.encard_union_eq, ih]
    · exact fun i hi j hj hij =>
        h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    · refine Set.disjoint_iUnion₂_right.2 fun j hj =>
        h a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) ?_
      rintro rfl
      exact ha hj

theorem exists_prod_ne_zero {ι : Type*} {k : ℕ} (F : Finset ι) (p : ι → MvPolynomial (Fin k) ℂ → Prop)
    (h : ∀ i ∈ F, ∃ P, P ≠ 0 ∧ p i P) :
    ∃ Δ : MvPolynomial (Fin k) ℂ, Δ ≠ 0 ∧
      ∀ y, eval y Δ ≠ 0 → ∀ i ∈ F, ∃ P, p i P ∧ eval y P ≠ 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a s ha ih =>
    obtain ⟨Δ, hΔ, hΔy⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨P, hP, hPa⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨P * Δ, mul_ne_zero hP hΔ, fun y hy i hi => ?_⟩
    rw [map_mul] at hy
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨P, hPa, left_ne_zero_of_mul hy⟩
    · exact hΔy y (right_ne_zero_of_mul hy) i hi

end ComponentsGenericCount

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftBlockDatum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel LiftBlockGraph

noncomputable section

theorem LiftBlockDatum.proof (hE : ResExistsStatement) (hVol : ResVolume.Statement)
    (hPts : LiftGraphPoints.Statement) (hMet : LiftGraphMetric.Statement) : LiftBlockDatum.Statement := by
  intro K _ _ ι _ Ω _ _ y D N P0 a ι' _ x' hD harith _ hP0 hsemi hconj _ hx' hgen hbir'
  have hv : ∀ j, liftCoords x' j ∈ chartLat y (a • N.a) 1 := fun j => hx' _
  have hgv := generatesOn_liftCoords y (a • N.a) x' hgen
  have harith' := isArithVar_addBlock y (a • N.a) (liftCoords x') harith hv hgv
  obtain ⟨A, hAdeg, hAconj, hAsemi, hrel⟩ :=
    hMet K ι Ω y N P0 a (Fintype.card ι') (liftCoords x') hP0 hsemi hconj hv hgv
  have hnot : ¬ (⊤ : Ideal (MRing (addIdx ι (Fintype.card ι')))) ≤ mCoordIdeal (addBlock y (liftCoords x')) :=
    fun h => harith'.2.1.1.ne_top (top_le_iff.mp h)
  obtain ⟨J, -, -, -, ⟨R⟩⟩ := hE (Option K) (addIdx ι (Fintype.card ι')) _ ⊤ D harith'
    isMultiHomogIdeal_top hnot
  let _ : MeasurableSpace R.toAnRes.X := borel _
  have : BorelSpace R.toAnRes.X := ⟨rfl⟩
  obtain ⟨dV, hdV⟩ := hVol (Option K) (addIdx ι (Fintype.card ι')) _ J D R.toAnRes harith'
  refine ⟨
    { y := addBlock y (liftCoords x'), k₀ := none, A := A, P0 := mCoordIdeal (addBlock y (liftCoords x')),
      J := J, R := R.toAnRes, meas := borel _, borel := ⟨rfl⟩, dV := dV, one_le := hD, arith := harith',
      birat := blockBirational_addBlock y x' hbir', deg := hAdeg, conjInv := hAconj, normalForm_baseLattice_le_dualSpan_sup_line := le_rfl,
      semipos := hAsemi, vol := hdV }, rfl, rfl, hrel, ?_⟩
  exact hPts K ι Ω y (a • N.a) (Fintype.card ι') (liftCoords x') hv hgv

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsChartDenNotMem
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsChartDenNotMem.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (i : (k : K) → ι k) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → ∀ J ∈ (PtsSegreChart.ideal P i).minimalPrimes,
      PtsSegreChart.chartDen Ψ ∉ J

end GroundTheory.Heights₂.Heights
end
end

