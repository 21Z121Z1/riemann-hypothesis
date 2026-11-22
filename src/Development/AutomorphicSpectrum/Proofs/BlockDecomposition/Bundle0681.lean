import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SatBridge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0654
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0666
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothKFiniteCenter
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0669
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0642
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0667
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabiliserSplittingAdelic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0590
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatBridge
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LFun

namespace GlobalTheory.CompanionTheory.SatakeBridge

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem satBridge : PositivityTheory.SphericalProduct.SatBridge := by
  intro E _ _ w n V _ _ ρ hs hi α
  constructor
  · exact GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake E w n V ρ α
  · intro h
    obtain ⟨x, hx⟩ := h.exists_vec
    exact GlobalTheory.CompanionTheory.SatComp.hasSatake_of_isSatVecGL ⟨hs, hi⟩ α hx

end GlobalTheory.CompanionTheory.SatakeBridge

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionMeetsAbovePlaceStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_meets_above_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ v : PlF E, ∃ w : Above v, w.1 ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.LocHypAbove.exists_above_mem_section | exact GlobalTheory.CompanionTheory.LocHypAbove.exists_above_mem_section | (intros; apply GlobalTheory.CompanionTheory.LocHypAbove.exists_above_mem_section <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothKFiniteCenterStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_K_finite_center : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (φ : Sm E a), (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) → MemL2Quotient (latticeGL E a) μ φ.1 → ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N := by
  first | exact @GlobalTheory.CompanionTheory.Growth.moderate_growth | exact GlobalTheory.CompanionTheory.Growth.moderate_growth | (intros; apply GlobalTheory.CompanionTheory.Growth.moderate_growth <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothingFundamentalDomainIntegral
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc

theorem lintegral_sq_le_of_average {G Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] (F : Set G) (hF : IsFundamentalDomain Γ F μ)
    (ν : Measure Y) (b : Y → ℝ≥0∞) (hb : Measurable b) (hmass : ∫⁻ y, b y ∂ν = 1)
    (k : Y → G) (hk : Continuous k) (f : G → ℂ) (hf : Continuous f)
    (hinv : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) (s : G → ℂ)
    (hs : ∀ x, ‖s x‖ₑ ≤ ∫⁻ y, b y * ‖f (x * k y)‖ₑ ∂ν) :
    ∫⁻ x in F, ‖s x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by
  set p := ν.withDensity b with hp
  haveI : IsProbabilityMeasure p := ⟨by rw [hp, withDensity_apply _ MeasurableSet.univ]; simpa using hmass⟩
  have hm : ∀ x, Continuous fun y => f (x * k y) := fun x => hf.comp (continuous_const.mul hk)
  have hsq : ∀ {X : Type _} [MeasurableSpace X] (m : Measure X) (g : X → ℂ),
      eLpNorm g 2 m ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂m := by
    intro X _ m g
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num [ENNReal.rpow_two]
  have hpt : ∀ x, ‖s x‖ₑ ^ 2 ≤ ∫⁻ y, ‖f (x * k y)‖ₑ ^ 2 ∂p := by
    intro x
    have h1 : ∫⁻ y, b y * ‖f (x * k y)‖ₑ ∂ν = ∫⁻ y, ‖f (x * k y)‖ₑ ∂p := by
      rw [hp, lintegral_withDensity_eq_lintegral_mul ν hb (hm x).measurable.enorm]
      rfl
    have h2 := eLpNorm_le_eLpNorm_of_exponent_le (p := 1) (q := 2) (μ := p) (by norm_num)
      (hm x).measurable.aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm] at h2
    rw [← hsq p]
    exact pow_le_pow_left' ((hs x).trans (h1.le.trans h2)) 2
  have hΓ : ∀ (γ : Γ) (x : G), ‖f (γ • x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2 := fun γ x => by
    rw [Subgroup.smul_def, smul_eq_mul, hinv _ γ.2]
  have htr : ∀ h : G, ∫⁻ x in F, ‖f (x * h)‖ₑ ^ 2 ∂μ = ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by
    intro h
    have hF' : IsFundamentalDomain Γ (MulOpposite.op h • F) μ := hF.smul_of_comm _
    have e1 := (measurePreserving_mul_right μ h).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.mulRight h).measurableEmbedding (fun z => ‖f z‖ₑ ^ 2) (MulOpposite.op h • F)
    have e2 : (fun x => x * h) ⁻¹' (MulOpposite.op h • F) = F := by
      ext x
      simp [Set.mem_smul_set_iff_inv_smul_mem]
    rw [e2] at e1
    rw [e1]
    exact hF'.setLIntegral_eq hF _ hΓ
  have hjoint : Measurable (Function.uncurry fun (x : G) (y : Y) => ‖f (x * k y)‖ₑ ^ 2) :=
    ((hf.comp (continuous_fst.mul (hk.comp continuous_snd))).measurable.enorm).pow_const 2
  calc ∫⁻ x in F, ‖s x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in F, ∫⁻ y, ‖f (x * k y)‖ₑ ^ 2 ∂p ∂μ := lintegral_mono hpt
    _ = ∫⁻ y, ∫⁻ x in F, ‖f (x * k y)‖ₑ ^ 2 ∂μ ∂p := lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ _y, ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ ∂p := lintegral_congr fun y => htr (k y)
    _ = ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by simp

theorem sm_sq_mass_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)] (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (F : Set (GA E N)) (β : archGroup E N → ℝ), IsFundamentalDomain (latticeGL E N) F μ → Ker ν β →
  ∀ f : GA E N → ℂ, Continuous f → (∀ γ ∈ latticeGL E N, ∀ g, f (γ * g) = f g) →
  ∫⁻ x in F, ‖sm ν β f x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by
  intro E _ _ _ N _ _ μ _ _ _ ν _ F β hF hβ f hf hinv
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  haveI : SecondCountableTopology (GA E N) := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E N
  haveI : LocallyCompactSpace (GA E N) := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E N
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.haar_right_invariant_totally_complex E N μ
  refine lintegral_sq_le_of_average μ (latticeGL E N) F hF ν (fun y => ENNReal.ofReal (β y))
    hβ.cont.measurable.ennreal_ofReal ?_ (infEmb E N) continuous_infEmb f hf hinv (sm ν β f) ?_
  · rw [← ofReal_integral_eq_lintegral_ofReal
      (hβ.cont.integrable_of_hasCompactSupport hβ.cpt) (Eventually.of_forall hβ.nonneg), hβ.mass]
    simp
  · intro x
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun y => ?_))
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (hβ.nonneg y)]

end GlobalTheory.CompanionTheory.Conc

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulInvSub
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist

variable {D : D7} {a b c n r t : ℕ}

theorem mm_jn (hn : r + t = n) (M : Mx D c a) (x : Mx D a r) (v : Mx D a t) :
    mm M (jn hn x v) = jn hn (mm M x) (mm M v) := by
  unfold jn mm
  rw [← Matrix.mul_fromCols]
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]

theorem jn_bl (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (p : Mx D r r) (q : Mx D r t) (s : Mx D t r) (u : Mx D t t) :
    mm (jn hn w v) (bl hn p q s u) = jn hn (mm w p + mm v s) (mm w q + mm v u) := by
  unfold jn PositivityTheory.Rg.Rsw.L.mm
  rw [show bl hn p q s u =
      (Matrix.fromBlocks p q s u).submatrix
        (finSumFinEquiv.trans (finCongr hn)).symm (finSumFinEquiv.trans (finCongr hn)).symm from rfl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]

theorem block_mul₂ (hn : r + t = n) (p p' : Mx D r r) (q q' : Mx D r t) (s s' : Mx D t r) (u u' : Mx D t t) :
    (bl hn p q s u * bl hn p' q' s' u' : Matrix (Fin n) (Fin n) (AE D)) =
      bl hn (mm p p' + mm q s') (mm p q' + mm q u') (mm s p' + mm u s') (mm s q' + mm u u') := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one (hn : r + t = n) :
    bl hn (1 : Mx D r r) (0 : Mx D r t) (0 : Mx D t r) (1 : Mx D t t) = (1 : Matrix (Fin n) (Fin n) (AE D)) := by
  unfold bl
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem smul_blockMatrix_sub_one (hn : r + t = n) (e : AE D) (p : Mx D r r) (q : Mx D r t) (s : Mx D t r) (u : Mx D t t)
    (h₁ : e • (p - 1) = p - 1) (h₂ : e • q = q) (h₃ : e • s = s) (h₄ : e • (u - 1) = u - 1) :
    e • (bl hn p q s u - 1) = bl hn p q s u - 1 := by
  have h : bl hn p q s u - 1 = bl hn (p - 1) q s (u - 1) := by
    rw [← blockRowSubstitution_one hn]
    unfold bl
    ext i j
    simp only [Matrix.sub_apply, Matrix.submatrix_apply]
    rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
      rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> simp
  rw [h]
  unfold bl
  ext i j
  simp only [Matrix.smul_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> simp only [Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  · exact congrFun (congrFun h₁ i) j
  · exact congrFun (congrFun h₂ i) j
  · exact congrFun (congrFun h₃ i) j
  · exact congrFun (congrFun h₄ i) j

def shU (hn : r + t = n) (y : Mx D r t) : GL (Fin n) (AE D) where
  val := bl hn 1 y 0 1
  inv := bl hn 1 (-y) 0 1
  val_inv := by
    rw [block_mul₂]
    simpa [mm] using blockRowSubstitution_one hn
  inv_val := by
    rw [block_mul₂]
    simpa [mm] using blockRowSubstitution_one hn

def colU (hn : r + t = n) (g : GL (Fin t) (AE D)) : GL (Fin n) (AE D) where
  val := bl hn 1 0 0 g.1
  inv := bl hn 1 0 0 (g⁻¹).1
  val_inv := by
    rw [block_mul₂]
    have : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simpa [mm, this] using blockRowSubstitution_one hn
  inv_val := by
    rw [block_mul₂]
    have : (g⁻¹).1 * g.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simpa [mm, this] using blockRowSubstitution_one hn

theorem smul_inv_sub (e : AE D) (g : GL (Fin t) (AE D)) (h : e • (g.1 - 1) = g.1 - 1) :
    e • ((g⁻¹).1 - 1) = (g⁻¹).1 - 1 := by
  have h1 : (g⁻¹).1 * g.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (g⁻¹).1 - 1 = - ((g⁻¹).1 * (g.1 - 1)) := by
    rw [Matrix.mul_sub, h1, Matrix.mul_one, neg_sub]
  rw [h2, smul_neg, ← Matrix.mul_smul, h]

theorem trans_int {X N : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace N] [MeasurableSpace N]
    [BorelSpace N] (σ : Measure X) (lam : Measure N) (k : N → X → ℂ) (f : X → ℂ) (Θ : X ≃ₜ X) (c : N ≃ₜ N) (κ₁ κ₂ : ℝ≥0)
    (h₁ : σ.map Θ = κ₁ • σ) (h₂ : lam.map c = κ₂ • lam) (hk : ∀ x, ∀ᵐ z ∂σ, k x z = k (c x) (Θ z)) :
    ∫ x, ∫ z, f (Θ z) * k x z ∂σ ∂lam = ((κ₁ * κ₂ : ℝ≥0) : ℂ) * ∫ x, ∫ z, f z * k x z ∂σ ∂lam := by
  have hin : ∀ x, ∫ z, f (Θ z) * k x z ∂σ = (κ₁ : ℂ) * ∫ z, f z * k (c x) z ∂σ := by
    intro x
    have e₁ : ∫ z, f (Θ z) * k x z ∂σ = ∫ z, (fun w => f w * k (c x) w) (Θ z) ∂σ :=
      integral_congr_ae ((hk x).mono fun z hz => by simp only [hz])
    have e₃ := Θ.measurableEmbedding.integral_map (μ := σ) (fun w => f w * k (c x) w)
    rw [e₁, ← e₃, h₁, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  simp only [hin]
  rw [integral_const_mul]
  have e₂ : ∫ x, ∫ z, f z * k (c x) z ∂σ ∂lam = ∫ x, (fun u => ∫ z, f z * k u z ∂σ) (c x) ∂lam := rfl
  have e₄ := c.measurableEmbedding.integral_map (μ := lam) (fun u => ∫ z, f z * k u z ∂σ)
  rw [e₂, ← e₄, h₂, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  push_cast
  ring

theorem map_val_rel {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (ν : Measure X) (i : X → Y) (Θ : X → X) (T : Y → Y)
    (κ : ℝ≥0) (hi : Measurable i) (hΘ : Measurable Θ) (hT : Measurable T) (hc : ∀ z, i (Θ z) = T (i z)) (h : ν.map Θ = κ • ν) :
    (ν.map i).map T = κ • ν.map i := by
  rw [Measure.map_map hT hi]
  have : T ∘ i = i ∘ Θ := funext fun z => (hc z).symm
  rw [this, ← Measure.map_map hi hΘ, h, Measure.map_smul]

end GlobalTheory.CompanionTheory.OrbExist

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceLocalElementStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_local_element : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), IsSplitAt w →
  ratW n w δ * thetaGL n (RingHom.id _) (ratW n w (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ)) = locEl n w δ := by
  first | exact @GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL | exact GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL | (intros; apply GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableSingleSegmentStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_integrable_single_segment : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSocleGL k → Zl.CasselmanNecSq k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible → IsSqIntCoeff π → IsL 𝔪 π → 𝔪.card = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one | exact GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one | (intros; apply GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabiliserSplittingAdelicStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliser_splitting_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ (ι : HA (AF F) σ J →* stabilizer₂ (AF F) σ J) (π : stabilizer₂ (AF F) σ J →* HA (AF F) σ J), Continuous ι ∧ Continuous π ∧ (∀ u, π (ι u) = u) ∧ (∀ u ∈ HFinIn (AF F) σ J, ι u ∈ ratP (AF F) σ J) ∧ (∀ p ∈ ratP (AF F) σ J, π p ∈ HFinIn (AF F) σ J) ∧ (∃ K : Set (stabilizer₂ (AF F) σ J), IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ ratP (AF F) σ J, π γ = 1 ∧ γ * m ∈ K) ∧ (∀ (k : ℕ) (u : HA (AF F) σ J) (a : Fin 1 → Fin k → AF F ⊗[F] E) (Y : Fin k → Fin M → AF F ⊗[F] E), actW (AF F) σ (hypOne J) (ι u : HA (AF F) σ (hypOne J)) (consA a Y) = consA a (actW (AF F) σ J u Y)) ∧ ∀ (k : ℕ) (Y : Fin k → Fin M → E), LinearIndependent E Y → ∃ l : π.ker → Fin 1 → Fin k → AF F ⊗[F] E, Continuous l ∧ (∀ x y, l (x * y) = l x + l y) ∧ Function.Surjective l ∧ (∀ m : π.ker, (m : stabilizer₂ (AF F) σ J) ∈ ratP (AF F) σ J → l m ∈ ratA (F := F) (E := E) k) ∧ ∀ (m : π.ker) (a : Fin 1 → Fin k → AF F ⊗[F] E), actW (AF F) σ (hypOne J) ((m : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) (consA a (ratTup (AF F) Y)) = consA (a + l m) (ratTup (AF F) Y) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct.stab_structure | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct.stab_structure | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct.stab_structure <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabilizerIndexNeZeroStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_index_ne_zero : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K K' : Subgroup G) (d : G) (f : G → ℂ),
  Continuous θ → IsCompact (K : Set G) → IsOpen (K' : Set G) → (∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x) →
  ∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k))).index ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SplitIndex.rStab_index_ne_zero_of_compact | exact GlobalTheory.CompanionTheory.SplitIndex.rStab_index_ne_zero_of_compact | (intros; apply GlobalTheory.CompanionTheory.SplitIndex.rStab_index_ne_zero_of_compact <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistCompactPartInProdStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swap_twist_compact_part_in_prod : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → d ∈ K → d' ∈ K →
  cptPart (twCent (MonoidHom.id H) (d * σ d')) ≤ K →
  (∀ g : H, g⁻¹ * (d * σ d') * MonoidHom.id H g ∈ K → ∃ t ∈ twCent (MonoidHom.id H) (d * σ d'), t⁻¹ * g ∈ K) →
  cptPart (twCent (swTw σ) (d, d')) ≤ K.prod K ∧
    ∀ y : H × H, y⁻¹ * (d, d') * swTw σ y ∈ K.prod K → ∃ t ∈ twCent (swTw σ) (d, d'), ∃ k ∈ K.prod K, y = t * k := by
  first | exact @GlobalTheory.CompanionTheory.SplitUnit.main | exact GlobalTheory.CompanionTheory.SplitUnit.main | (intros; apply GlobalTheory.CompanionTheory.SplitUnit.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistCompactPartLeStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swap_twist_compact_part_le : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  PositivityTheory.Rg.BcB.G8.Fin.Good (MonoidHom.id H) K (d * σ d') → ∀ y : H × H,
  twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (swTw σ) (d, d')) ∧
    (twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (swTw σ) (d, d'))) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SplitCpt.split_cpt | exact GlobalTheory.CompanionTheory.SplitCpt.split_cpt | (intros; apply GlobalTheory.CompanionTheory.SplitCpt.split_cpt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedLanglandsFactorsSquareIntegrableStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_langlands_factors_square_integrable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSocleGL k → Zl.CasselmanNecTemp k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible → IsTemperedCoeff π → IsL 𝔪 π → ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x ∧ ∀ (a : Fin h) (t : kˣ) (c : ℂ), Zl.ScalarBy (x a) t c → ‖c‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.TemperedCore.exists_lFactors_unitary | exact GlobalTheory.CompanionTheory.TemperedCore.exists_lFactors_unitary | (intros; apply GlobalTheory.CompanionTheory.TemperedCore.exists_lFactors_unitary <;> assumption)
end

