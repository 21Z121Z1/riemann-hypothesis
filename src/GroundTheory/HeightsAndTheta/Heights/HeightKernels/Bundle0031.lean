import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0012

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PProjStdMassAt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix NumberField

noncomputable section

namespace ProjectiveStandardMassAtPoint

variable {K : Type} [Field K] [NumberField K]

theorem segre_const {i : ℕ} (z : (Σ _ : Unit, ProjIdx K i) → ℂ) (q : ProjIdx K i) :
    segre (ι := projBlocks K i) z (fun _ => q) = z ⟨(), q⟩ := by
  simp [segre]

open Classical in

theorem repr_sum (τ σ : K →+* ℂ) :
    ∑ m, (canonicalEmbedding.latticeBasis K).repr (Pi.single τ 1) m * σ (integralBasis K m) =
      if σ = τ then 1 else 0 := by
  have h := congrFun ((canonicalEmbedding.latticeBasis K).sum_repr (Pi.single τ 1)) σ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, canonicalEmbedding.latticeBasis_apply,
    canonicalEmbedding.apply_at, Pi.single_apply] at h
  exact h

open Classical in

theorem embComp_planePt {i : ℕ} (τ σ : K →+* ℂ) (v : Fin i → ℂ) :
    embComp τ (fun q => projPlanePt σ v ⟨(), q⟩) = if σ = τ then v else 0 := by
  funext j
  have h : ∑ m, (canonicalEmbedding.latticeBasis K).repr (Pi.single τ 1) m *
      (σ (integralBasis K m) * v j) = (if σ = τ then 1 else 0) * v j := by
    rw [← repr_sum τ σ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  simp only [embComp, projPlanePt]
  rw [h]
  split_ifs <;> simp

theorem proj_segre_planePt {i : ℕ} (σ : K →+* ℂ) (v : Fin i → ℂ) :
    projProj (segre (ι := projBlocks K i) (projPlanePt σ v)) = v := by
  classical
  rw [projProj_apply]
  simp only [segre_const, embComp_planePt]
  rw [Finset.sum_eq_single σ (fun τ _ hτ => if_neg (Ne.symm hτ)) (by simp)]
  exact if_pos rfl

theorem h_eq (hOn : ProjPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) {z : (Σ _ : Unit, ProjIdx K (D + 1)) → ℂ}
    (hz : z ∈ mcPts (projSpaceIdeal K (D + 1))) :
    (latticeLine F).h z = Real.sqrt (∑ j, ‖projProj (segre (ι := projBlocks K (D + 1)) z) j‖ ^ 2) := by
  obtain ⟨σ, hσ⟩ := hOn K (D + 1) z hz
  have hp : projProj (segre (ι := projBlocks K (D + 1)) z) = embComp σ (fun q => z ⟨(), q⟩) := by
    rw [projProj_apply]
    simp only [segre_const]
    exact Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ) (by simp)
  show Real.sqrt (latticeNormSq F fun q => z ⟨(), q⟩) = _
  congr 1
  rw [latticeNormSq, Finset.sum_eq_single σ]
  · rw [hF, one_mulVec, dotProduct, Complex.re_sum, hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  · intro τ _ hτ
    rw [hσ τ hτ]
    simp
  · simp

theorem sheetDensity_eq (hOn : ProjPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) {y : Fin D → ℂ}
    {w : ((k : Unit) → projBlocks K (D + 1) k) → ℂ}
    (h : ∃ γ, IsSheet (projSpaceIdeal K (D + 1)) projProj y w γ) :
    sheetDensity (projSpaceIdeal K (D + 1)) projProj (fun _ z => Real.log ((latticeLine F).h z))
      (fun _ => 1) y w = maDensity (fun _ : Fin D => gbPot) y := by
  unfold sheetDensity
  rw [dif_pos h, one_mul]
  apply maDensity_congr_of_eventuallyEq
  intro j
  filter_upwards [h.choose_spec.2] with y' hy'
  obtain ⟨-, hmc, hΨ⟩ := hy'
  show Real.log ((latticeLine F).h (h.choose y')) = gbPot y'
  rw [h_eq hOn hF hmc, hΨ, gbPot, Fin.sum_univ_succ]
  simp

theorem fibre_eq (hOn : ProjPtsOnPlane.Statement) (hOf : ProjPtsOfPlane.Statement) {D : ℕ}
    (y : Fin D → ℂ) :
    fibre (projSpaceIdeal K (D + 1)) projProj y =
      Set.range fun σ : K →+* ℂ => segre (ι := projBlocks K (D + 1)) (projPlanePt σ (Fin.cons 1 y)) := by
  classical
  ext w
  constructor
  · rintro ⟨z, hz, rfl, hΨ⟩
    obtain ⟨σ, hσ⟩ := hOn K (D + 1) z hz
    refine ⟨σ, congrArg segre ?_⟩
    have hW : ∀ τ : K →+* ℂ, embComp τ (fun q => z ⟨(), q⟩) =
        embComp τ (fun q => projPlanePt σ (Fin.cons 1 y) ⟨(), q⟩) := by
      intro τ
      rw [embComp_planePt]
      by_cases hτ : σ = τ
      · subst hτ
        rw [if_pos rfl, ← hΨ, projProj_apply]
        simp only [segre_const]
        exact (Finset.sum_eq_single σ (fun τ' _ h' => hσ τ' h') (by simp)).symm
      · rw [if_neg hτ]
        exact hσ τ (Ne.symm hτ)
    funext ⟨u, m, j⟩
    cases u
    refine ((sum_emb_embComp (fun q => projPlanePt σ (Fin.cons 1 y) ⟨(), q⟩) m j).symm.trans ?_).trans
      (sum_emb_embComp (fun q => z ⟨(), q⟩) m j)
    exact Finset.sum_congr rfl fun τ _ => by rw [hW τ]
  · rintro ⟨σ, rfl⟩
    have hv : (Fin.cons 1 y : Fin (D + 1) → ℂ) ≠ 0 := fun h0 => by simpa using congrFun h0 0
    exact ⟨_, hOf K (D + 1) σ _ hv, rfl, proj_segre_planePt σ _⟩

theorem planePt_injective {D : ℕ} (y : Fin D → ℂ) :
    Function.Injective fun σ : K →+* ℂ =>
      segre (ι := projBlocks K (D + 1)) (projPlanePt σ (Fin.cons 1 y)) := by
  classical
  intro σ τ h
  have h1 := congrArg (fun w : ((k : Unit) → projBlocks K (D + 1) k) → ℂ =>
    embComp σ (fun q => w fun _ => q)) h
  simp only [segre_const, embComp_planePt] at h1
  by_contra hne
  rw [if_pos trivial, if_neg fun e => hne e.symm] at h1
  simpa using congrFun h1 0

theorem isSheet_planePt (hOf : ProjPtsOfPlane.Statement) {D : ℕ} (σ : K →+* ℂ) (y : Fin D → ℂ) :
    IsSheet (projSpaceIdeal K (D + 1)) projProj y
      (segre (ι := projBlocks K (D + 1)) (projPlanePt σ (Fin.cons 1 y)))
      (fun y' => projPlanePt σ (Fin.cons 1 y')) := by
  have hc : Differentiable ℂ (fun y' : Fin D → ℂ => (Fin.cons 1 y' : Fin (D + 1) → ℂ)) := by
    rw [differentiable_pi]
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · simpa using differentiable_apply (𝕜 := ℂ) k
  refine ⟨rfl, Filter.Eventually.of_forall fun y' => ⟨?_, ?_, proj_segre_planePt σ _⟩⟩
  · refine (differentiable_pi.mpr fun p => ?_) y'
    simp only [projPlanePt]
    exact (differentiable_pi.mp hc p.2.2).const_mul _
  · exact hOf K (D + 1) σ _ fun h0 => by simpa using congrFun h0 0

end ProjectiveStandardMassAtPoint

open ProjectiveStandardMassAtPoint in

theorem ProjStdMassAt.proof (hOn : ProjPtsOnPlane.Statement) (hOf : ProjPtsOfPlane.Statement) :
    ProjStdMassAt.Statement := by
  intro K _ _ D F hF
  have hint : ∀ y : Fin D → ℂ, ∑ᶠ w ∈ fibre (projSpaceIdeal K (D + 1)) projProj y,
      sheetDensity (projSpaceIdeal K (D + 1)) projProj (fun _ z => Real.log ((latticeLine F).h z))
        (fun _ => 1) y w = (Fintype.card (K →+* ℂ) : ℝ) * maDensity (fun _ : Fin D => gbPot) y := by
    intro y
    rw [fibre_eq hOn hOf y, finsum_mem_range (planePt_injective y),
      finsum_eq_sum_of_fintype,
      Finset.sum_congr rfl fun σ _ => sheetDensity_eq hOn hF ⟨_, isSheet_planePt hOf σ y⟩,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold ptsIntegralAt
  simp only [hint]
  rw [integral_const_mul, integral_maDensity_gbPot, mul_one]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

def HermLattice.withStdMetric {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) :
    HermLattice K i where
  lattice := F.lattice
  fg := F.fg
  span_eq := F.span_eq
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

def DualTopMetricChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F b hb) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (F.withStdMetric.degree - F.degree) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def DualTopLatticeChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T T' : Type) [Fintype T]
    [DecidableEq T] [Fintype T'] [DecidableEq T'] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T' ℤ (dualLattice (HermLattice.standard K i)))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) =
      II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine (HermLattice.standard K i) b' hb') -
        F.withStdMetric.degree *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def DualTopStandard.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine (HermLattice.standard K i) b hb) =
      (Module.finrank ℚ K : ℝ) *
        II (Fin 1) (plBlocks 1 1 (i - 1)) (grassIdeal 1 1 (i - 1)) (1 * 1 * (i - 1) + 1)
          (fun _ => fsMulti (plBlocks 1 1 (i - 1)))

def DualGeomDegStandard.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    geomDeg (dualIdeal b) (dualLine F b hb) (i - 1) =
      (Module.finrank ℚ K : ℝ) *
        geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def HermLattice.scaledExample : HermLattice ℚ 1 where
  lattice := (HermLattice.standard ℚ 1).lattice
  fg := (HermLattice.standard ℚ 1).fg
  span_eq := (HermLattice.standard ℚ 1).span_eq
  metric := fun _ => Matrix.diagonal fun _ => (4 : ℂ)
  posDef := fun _ => Matrix.PosDef.diagonal fun _ => by norm_num
  conj := fun _ => by
    ext a c
    by_cases h : a = c <;> simp [h, map_ofNat]

example : Function.Bijective (Matrix.mulVecLin
    (dualEmbMatrix (F := HermLattice.scaledExample) dualBasisStandard)) :=
  dualEmbMatrix_standard_bijective

example : Function.Bijective (Matrix.mulVecLin
    (dualEmbMatrix (F := HermLattice.scaledExample.withStdMetric) dualBasisStandard)) :=
  dualEmbMatrix_standard_bijective

example : HermLine (dualBlocks Unit) × HermLine (dualBlocks Unit) × HermLine (dualBlocks Unit) ×
    PLift (1 ≤ 1) :=
  ⟨dualLine HermLattice.scaledExample dualBasisStandard dualEmbMatrix_standard_bijective,
    dualLine HermLattice.scaledExample.withStdMetric dualBasisStandard dualEmbMatrix_standard_bijective,
    dualLine (HermLattice.standard ℚ 1) dualBasisStandard dualEmbMatrix_standard_bijective, ⟨le_rfl⟩⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StdCoordMapInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

noncomputable section

def S6.LineCoordinates.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (X : Type) [Fintype X]
    [DecidableEq X] (L : X → Submodule (𝓞 K) E.carrier),
    DirectSum.IsInternal L → (∀ x, E.rank (L x) = 1) → IsOrthogonalFamily E L →
    ∃ (n : ℕ) (e : Fin n ≃ X) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (d : (K →+* ℂ) → Fin n → ℝ)
      (ψ : E.carrier →ₗ[𝓞 K] (Fin n → K)),
      (∀ i, a i ≠ 0) ∧ (∀ σ i, 0 < d σ i) ∧ (∀ σ i, d (conjugate σ) i = d σ i) ∧
      Function.Injective ψ ∧ LinearMap.range ψ = idealLattice a ∧
      Module.finrank (𝓞 K) E.carrier = n ∧
      (∀ i, (L (e i)).map ψ = idealLattice a ⊓
        (Submodule.span K {(Pi.single i 1 : Fin n → K)}).restrictScalars (𝓞 K)) ∧
      ∀ (σ : K →+* ℂ) (v w : E.carrier),
        (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) =
          star (embVec σ (ψ v)) ⬝ᵥ (diagMetric d σ *ᵥ embVec σ (ψ w))

def S6.CoordinateDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (n : ℕ)
    (H : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (ψ : E.carrier →ₗ[𝓞 K] (Fin n → K)),
    Function.Injective ψ → Submodule.span K (LinearMap.range ψ : Set (Fin n → K)) = ⊤ →
    (∀ (σ : K →+* ℂ) (v w : E.carrier),
        (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) =
          star (embVec σ (ψ v)) ⬝ᵥ (H σ *ᵥ embVec σ (ψ w))) →
    ∀ (G : Submodule (𝓞 K) E.carrier) (ι : Type) [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K),
      LinearIndependent K u →
      G.map ψ = LinearMap.range ψ ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K) →
      E.degree G = subDegree (LinearMap.range ψ) H u

def S6.QuotientDegreeSplit.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K))
    (H : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ), Λ.FG →
    Submodule.span K (Λ : Set (Fin n → K)) = ⊤ →
    ∀ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K),
      LinearIndependent K (Sum.elim b c) → m + k = n →
      quotDegree Λ H b c = subDegree Λ H (Sum.elim b c) - subDegree Λ H b

def S6.ExtensionDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E' E E'' : HermitianBundle.{0} K)
    (Y : HermitianExtension E' E E''),
    E''.degree ⊤ = E.degree ⊤ - E.degree (LinearMap.range Y.incl)

def S6.SaturatedSpan.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (M : Type) [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] (n : ℕ) (ψ : M →ₗ[𝓞 K] (Fin n → K)), Function.Injective ψ →
    ∀ G : Submodule (𝓞 K) M, (∀ (t : 𝓞 K) (x : M), t ≠ 0 → t • x ∈ G → x ∈ G) →
      ∃ b : Fin (Module.finrank (𝓞 K) G) → Fin n → K, LinearIndependent K b ∧
        G.map ψ = LinearMap.range ψ ⊓ (Submodule.span K (Set.range b)).restrictScalars (𝓞 K)

def stdCoordMap (K : Type*) [Field K] (n : ℕ) : (Fin n → 𝓞 K) →ₗ[𝓞 K] (Fin n → K) :=
  LinearMap.pi fun i => (Algebra.linearMap (𝓞 K) K).comp (LinearMap.proj i)

theorem stdCoordMap_apply (K : Type*) [Field K] (n : ℕ) (v : Fin n → 𝓞 K) (i : Fin n) :
    stdCoordMap K n v i = (v i : K) := rfl

theorem stdCoordMap_injective (K : Type*) [Field K] (n : ℕ) :
    Function.Injective (stdCoordMap K n) := by
  intro v w h
  funext i
  exact Subtype.ext (congrFun h i)

theorem stdCoordMap_single (K : Type*) [Field K] (n : ℕ) (i : Fin n) :
    stdCoordMap K n (Pi.single i 1) = Pi.single i 1 := by
  funext j
  rw [stdCoordMap_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem stdCoordMap_span (K : Type*) [Field K] (n : ℕ) :
    Submodule.span K (LinearMap.range (stdCoordMap K n) : Set (Fin n → K)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine Submodule.subset_span ⟨Pi.single i 1, ?_⟩
  rw [stdCoordMap_single, Pi.basisFun_apply]

theorem stdCoordMap_inner (K : Type*) [Field K] [NumberField K] (n : ℕ) (σ : K →+* ℂ)
    (v w : Fin n → 𝓞 K) :
    ((HermitianBundle.standard K n).metric.form σ).inner
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) =
      star (embVec σ (stdCoordMap K n v)) ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ
        embVec σ (stdCoordMap K n w)) := by
  refine (HermitianMetric.standard_inner K (Fin n) σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v)
    ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w)).trans ?_
  rw [Matrix.one_mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [standardCoord_tmul, standardCoord_tmul]
  simp [embVec, stdCoordMap_apply, ComplexAt.ofComplex]

theorem S6.LineCoordinates.hypotheses_inhabited :
    DirectSum.IsInternal (coordLines ℚ) ∧
      (∀ x, (HermitianBundle.standard ℚ 2).rank (coordLines ℚ x) = 1) ∧
      IsOrthogonalFamily (HermitianBundle.standard ℚ 2) (coordLines ℚ) :=
  ⟨coordLines_isInternal ℚ, coordLines_rank ℚ, coordLines_orthogonal ℚ⟩

theorem S6.CoordinateDegree.hypotheses_inhabited :
    Function.Injective (stdCoordMap ℚ 2) ∧
      Submodule.span ℚ (LinearMap.range (stdCoordMap ℚ 2) : Set (Fin 2 → ℚ)) = ⊤ ∧
      (∀ (σ : ℚ →+* ℂ) (v w : Fin 2 → 𝓞 ℚ),
        ((HermitianBundle.standard ℚ 2).metric.form σ).inner
            ((1 : ComplexAt σ) ⊗ₜ[𝓞 ℚ] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 ℚ] w) =
          star (embVec σ (stdCoordMap ℚ 2 v)) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
            embVec σ (stdCoordMap ℚ 2 w))) ∧
      LinearIndependent ℚ (Pi.basisFun ℚ (Fin 2)) ∧
      (⊤ : Submodule (𝓞 ℚ) (Fin 2 → 𝓞 ℚ)).map (stdCoordMap ℚ 2) =
        LinearMap.range (stdCoordMap ℚ 2) ⊓
          (Submodule.span ℚ (Set.range (Pi.basisFun ℚ (Fin 2)))).restrictScalars (𝓞 ℚ) := by
  refine ⟨stdCoordMap_injective ℚ 2, stdCoordMap_span ℚ 2, stdCoordMap_inner ℚ 2,
    (Pi.basisFun ℚ (Fin 2)).linearIndependent, ?_⟩
  rw [(Pi.basisFun ℚ (Fin 2)).span_eq, Submodule.restrictScalars_top, inf_top_eq,
    Submodule.map_top]

theorem S6.QuotientDegreeSplit.hypotheses_inhabited :
    (idealLattice (fun _ : Fin 2 => (1 : FractionalIdeal (𝓞 ℚ)⁰ ℚ))).FG ∧
      Submodule.span ℚ (idealLattice (fun _ : Fin 2 => (1 : FractionalIdeal (𝓞 ℚ)⁰ ℚ)) :
        Set (Fin 2 → ℚ)) = ⊤ ∧
      LinearIndependent ℚ (Sum.elim
        (fun i : Fin 1 => (Pi.single (Fin.castAdd 1 i) 1 : Fin (1 + 1) → ℚ))
        fun j : Fin 1 => (Pi.single (Fin.natAdd 1 j) 1 : Fin (1 + 1) → ℚ)) ∧ 1 + 1 = 2 := by
  obtain ⟨hFG, hspan⟩ := LinesIdealLatticeFG.full ℚ 2 _ fun _ => one_ne_zero
  refine ⟨hFG, hspan, ?_, rfl⟩
  have h := (stdSumBasis ℚ 1 1).linearIndependent
  rw [← stdSumBasis_elim] at h
  simpa only [stdSumBasis_inl, stdSumBasis_inr] using h

theorem S6.ExtensionDegree.hypotheses_inhabited :
    Nonempty (HermitianExtension (HermitianBundle.integers ℚ) (HermitianBundle.standard ℚ 2)
      (HermitianBundle.integers ℚ)) :=
  ⟨HermitianExtension.standardSplit ℚ⟩

theorem S6.SaturatedSpan.hypotheses_inhabited :
    Function.Injective (stdCoordMap ℚ 2) ∧
      ∀ (t : 𝓞 ℚ) (x : Fin 2 → 𝓞 ℚ), t ≠ 0 → t • x ∈ LinearMap.range (firstIncl ℚ) →
        x ∈ LinearMap.range (firstIncl ℚ) :=
  ⟨stdCoordMap_injective ℚ 2, fun t x ht hx =>
    standardFlag_saturated (K := ℚ) 1 t x ht hx⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

