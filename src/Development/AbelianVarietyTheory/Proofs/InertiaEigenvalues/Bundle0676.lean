import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0667
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.AdmissibleDesigns.Bundle0001
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdeal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetDiagonalBlockActsByInfinitesimalCharac

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActEquivSymmApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RallisCusp

open GlobalTheory.MixModel

variable {D : D7} (W : HSp D)

theorem exists_gqMat (γ : GQ W) : ∃ c : Matrix (Fin W.rank) (Fin W.rank) D.host.E, rat c = mt W γ :=
  mem_ratMx.1 ((mem_GQ_iff W γ).1 γ.2)

def gqMat (γ : GQ W) : Matrix (Fin W.rank) (Fin W.rank) D.host.E := Classical.choose (exists_gqMat W γ)

theorem rat_gqMat (γ : GQ W) : rat (gqMat W γ) = mt W γ := Classical.choose_spec (exists_gqMat W γ)

theorem gqMat_map (γ : GQ W) : (gqMat W γ).map (incA D) = mt W γ := rat_gqMat W γ

theorem gqMat_mul (γ δ : GQ W) : gqMat W (γ * δ) = gqMat W γ * gqMat W δ :=
  rat_injective (by rw [rat_mul, rat_gqMat, rat_gqMat, rat_gqMat]; rfl)

theorem gqMat_one : gqMat W 1 = 1 := rat_injective (by rw [rat_gqMat, rat_one]; rfl)

theorem gqMat_inv_mul (γ : GQ W) : gqMat W γ⁻¹ * gqMat W γ = 1 := by
  rw [← gqMat_mul, inv_mul_cancel, gqMat_one]

theorem gqMat_mul_inv (γ : GQ W) : gqMat W γ * gqMat W γ⁻¹ = 1 := by
  rw [← gqMat_mul, mul_inv_cancel, gqMat_one]

theorem gqMat_unitary (γ : GQ W) : (gqMat W γ)ᴴ * W.gram * gqMat W γ = W.gram := by
  apply rat_injective
  rw [rat_mul, rat_mul, rat_conjTranspose, rat_gqMat]
  exact mt_rel W γ

def actEquiv (γ : GQ W) :
    ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) ≃ₗ[D.host.E] ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :=
  LinearEquiv.prodCongr
    (LinearEquiv.ofLinear (Matrix.toLin' (gqMat W γ)) (Matrix.toLin' (gqMat W γ⁻¹))
      (by rw [← Matrix.toLin'_mul, gqMat_mul_inv, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, gqMat_inv_mul, Matrix.toLin'_one]))
    (LinearEquiv.refl _ _)

theorem actEquiv_apply (γ : GQ W) (y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :
    actEquiv W γ y = (gqMat W γ *ᵥ y.1, y.2) := rfl

theorem isotropic_mulVec (γ : GQ W) (x x' : Fin W.rank → D.host.E) :
    star (gqMat W γ *ᵥ x) ⬝ᵥ W.gram *ᵥ (gqMat W γ *ᵥ x') = star x ⬝ᵥ W.gram *ᵥ x' := by
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, gqMat_unitary]

def lagAct (γ : GQ W) (Y : Lag W) : Lag W :=
  ⟨Y.1.map (actEquiv W γ : _ →ₗ[D.host.E] _), by rw [LinearEquiv.finrank_map_eq]; exact Y.2.1, by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    simp only [LinearEquiv.coe_coe, actEquiv_apply]
    rw [isotropic_mulVec]
    exact Y.2.2 y hy y' hy'⟩

theorem mem_lagAct (γ : GQ W) (Y : Lag W) (y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :
    y ∈ (lagAct W γ Y).1 ↔ (gqMat W γ⁻¹ *ᵥ y.1, y.2) ∈ Y.1 := by
  show y ∈ Y.1.map (actEquiv W γ : _ →ₗ[D.host.E] _) ↔ _
  rw [Submodule.mem_map_equiv]
  rfl

theorem lagAct_one (Y : Lag W) : lagAct W 1 Y = Y := by
  apply Subtype.ext
  ext y
  rw [mem_lagAct, inv_one, gqMat_one, Matrix.one_mulVec]

theorem lagAct_mul (γ δ : GQ W) (Y : Lag W) : lagAct W (γ * δ) Y = lagAct W γ (lagAct W δ Y) := by
  apply Subtype.ext
  ext y
  rw [mem_lagAct, mem_lagAct, mem_lagAct, _root_.mul_inv_rev, gqMat_mul]
  simp only [Matrix.mulVec_mulVec]

theorem isLagFrame_lagAct (γ : GQ W) (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E ×
    Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : IsLagFrame W Y C) :
    IsLagFrame W (lagAct W γ Y) (gqMat W γ * C.1, C.2) := by
  unfold IsLagFrame at h ⊢
  change _ = Submodule.map (actEquiv W γ).toLinearMap Y.1
  rw [← h, Submodule.map_span, ← Set.range_comp]
  congr 2

abbrev NGLag (W : HSp D) : Type := {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥}

theorem lagAct_ne_bot (γ : GQ W) (Y : Lag W) (h : Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥) :
    (lagAct W γ Y).1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.ne_bot_iff _ |>.1 h
  refine (Submodule.ne_bot_iff _).2 ⟨gqMat W γ *ᵥ x, ?_, ?_⟩
  · rw [Submodule.mem_comap, LinearMap.inl_apply, mem_lagAct, Matrix.mulVec_mulVec, gqMat_inv_mul, Matrix.one_mulVec]
    exact hx
  · intro h0
    apply hx0
    have := congrArg (fun v => gqMat W γ⁻¹ *ᵥ v) h0
    simpa [Matrix.mulVec_mulVec, gqMat_inv_mul] using this

def ngAct (γ : GQ W) (Y : NGLag W) : NGLag W := ⟨lagAct W γ Y.1, lagAct_ne_bot W γ Y.1 Y.2⟩

theorem ngAct_one (Y : NGLag W) : ngAct W 1 Y = Y := Subtype.ext (lagAct_one W Y.1)

theorem ngAct_mul (γ δ : GQ W) (Y : NGLag W) : ngAct W (γ * δ) Y = ngAct W γ (ngAct W δ Y) :=
  Subtype.ext (lagAct_mul W γ δ Y.1)

end GlobalTheory.RallisCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOMapHaar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem actO_map_haar : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (μ : Measure (WO S T)),
    μ.IsAddHaarMeasure → μ.map (actO S T g h) = μ := by
  intro D S T g h μ hμ
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have hL : Continuous (fun x : Mx D T.rank S.rank =>
      (HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Mx D T.rank S.rank)) :=
    continuous_const.matrix_mul continuous_id
  have hR : Continuous (fun x : Mx D T.rank S.rank =>
      (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) : Mx D T.rank S.rank)) :=
    continuous_id.matrix_mul continuous_const
  have e : actO S T g h =
      (fun x : Mx D T.rank S.rank =>
        (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) : Mx D T.rank S.rank)) ∘
      (fun x : Mx D T.rank S.rank =>
        (HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Mx D T.rank S.rank)) := rfl
  rw [e, ← Measure.map_map hR.measurable hL.measurable, GlobalTheory.T.map_mt_mul_left_adelicMatrix_haar_eq D T S.rank h μ hμ]
  exact GlobalTheory.T.map_mul_right_unitaryAdelicMatrix_addHaar D S T.rank g⁻¹ μ hμ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolicStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGL_iwasawa_decomposition_standardParabolic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (x : GA E N), ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GA E (n i)) (k : Kinf E N) (g : GL (Fin N) (Af E)), x = u * leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g) := by
  first | exact @GlobalTheory.IwasawaAdelic.iwasawa | exact GlobalTheory.IwasawaAdelic.iwasawa | (intros; apply GlobalTheory.IwasawaAdelic.iwasawa <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFormulaOfKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.AdjUp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def upVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) : GA D (Vc D i) → (R.cV i).W :=
  fun h => ∑ k, upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h • b k

theorem inner_upVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) (k : Fin n) (h : GA D (Vc D i)) :
    ⟪b k, upVec R i t v b y h⟫_ℂ = upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h :=
  b.orthonormal.inner_right_fintype _ k

theorem val_zero (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    val R i v 0 = 0 := by
  funext g
  simp [val]

theorem upLift_zero {V W : HSp D} (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W))
    (𝓖 : Set (GA D W)) (f : WO V W → ℂ) (h : GA D V) : upLift om ν 𝓖 f 0 h = 0 := by
  simp [upLift]

end GlobalTheory.AdjUp

end

namespace GlobalTheory.AdjUp

theorem adjoint_formula_of_kernel {H₁ H₂ W Gv Gw : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [FiniteDimensional ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [MeasurableSpace Gv] [MeasurableSpace Gw]
    (th : H₁ →ₗ[ℂ] H₂) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ W) (μW : Measure Gw) (μV : Measure Gv)
    (φ : H₂ → Gw → ℂ) (ψ : H₁ → Gw → ℂ) (ext : H₁ →ₗ[ℂ] (Gv → W)) (K : Fin n → H₂ → Gv → ℂ) (P c : ℝ)
    (hP0 : 0 ≤ P) (hc : 0 < c)
    (hPW : ∀ y z, ⟪y, z⟫_ℂ = (P : ℂ) * ∫ g, star (φ y g) * φ z g ∂μW)
    (hφ : ∀ u, φ (th u) = ψ u) (hφ0 : φ 0 = 0) (hK0 : ∀ k h, K k 0 h = 0)
    (hcV : ∀ u u', ⟪u, u'⟫_ℂ = (c : ℂ) * ∫ h, ⟪ext u h, ext u' h⟫_ℂ ∂μV ∧
      ∀ a a' : W, Integrable (fun h => star ⟪a, ext u h⟫_ℂ * ⟪a', ext u' h⟫_ℂ) μV)
    (h3 : ∀ y u, ∫ g, star (φ y g) * ψ u g ∂μW = ∫ h, ⟪∑ k, K k y h • b k, ext u h⟫_ℂ ∂μV)
    (h4 : ∀ y, ∃ u, ext u = fun h => ∑ k, K k y h • b k) :
    ∃ a : ℝ, 0 < a ∧ ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ =
      (a : ℂ) * ∑ k, ∫ h, star (K k x h) * K k y h ∂μV := by
  choose U hU using h4
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hcoord : ∀ y k h, ⟪b k, ext (U y) h⟫_ℂ = K k y h := fun y k h => by
    rw [hU y]; exact b.orthonormal.inner_right_fintype _ k
  have hadj : ∀ y u, ⟪LinearMap.adjoint th y, u⟫_ℂ = (((P / c : ℝ)) : ℂ) * ⟪U y, u⟫_ℂ := by
    intro y u
    rw [LinearMap.adjoint_inner_left, hPW, hφ, h3, (hcV (U y) u).1, hU y, Complex.ofReal_div]
    field_simp
  have hsum : ∀ x y h, ⟪ext (U x) h, ext (U y) h⟫_ℂ = ∑ k, star (K k x h) * K k y h := by
    intro x y h
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hcoord, ← hcoord, ← inner_conj_symm]
    rfl
  by_cases hzero : P = 0
  · refine ⟨1, one_pos, fun x y => ?_⟩
    have h0 : ∀ z : H₂, z = 0 := fun z => by
      have := hPW z z
      rw [hzero, Complex.ofReal_zero, zero_mul] at this
      exact inner_self_eq_zero.1 this
    rw [h0 x, h0 y, map_zero, inner_zero_left]
    simp [hK0]
  · have hpos : 0 < P := lt_of_le_of_ne hP0 (Ne.symm hzero)
    refine ⟨P ^ 2 / c, by positivity, fun x y => ?_⟩
    have hint : ∀ k ∈ Finset.univ, Integrable (fun h => star (K k x h) * K k y h) μV := by
      intro k _
      have := (hcV (U x) (U y)).2 (b k) (b k)
      simpa only [hcoord] using this
    have e1 : ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ =
        (((P / c : ℝ)) : ℂ) * (((P / c : ℝ)) : ℂ) * ⟪U x, U y⟫_ℂ := by
      rw [hadj x, ← inner_conj_symm, hadj y, map_mul, Complex.conj_ofReal, inner_conj_symm, mul_assoc]
    have e2 : ⟪U x, U y⟫_ℂ = (c : ℂ) * ∑ k, ∫ h, star (K k x h) * K k y h ∂μV := by
      rw [(hcV (U x) (U y)).1, ← integral_finset_sum _ hint]
      simp only [hsum]
    rw [e1, e2]
    push_cast
    field_simp

end GlobalTheory.AdjUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorAllOfTateDualityEulerCharStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoAnnihilator_all_of_tateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.BKaAll D := by
  first | exact @GlobalTheory.BKaRows.bkaAll_of_hypotheses | exact GlobalTheory.BKaRows.bkaAll_of_hypotheses | (intros; apply GlobalTheory.BKaRows.bkaAll_of_hypotheses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimFormulaAllLocalSituationsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_dimFormula_all_localSituations : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm12 D := by
  first | exact @GlobalTheory.blochKatoDim_at_every_local_situation | exact GlobalTheory.blochKatoDim_at_every_local_situation | (intros; apply GlobalTheory.blochKatoDim_at_every_local_situation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoFiniteTrivialRepUnramifiedColumnPlacesA
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ColumnUnramified

theorem blochKatoFinite_trivialRep_unramified_columnPlaces : ∀ (D : D7) (i : D.nd.Loc) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i), Formalism.MainNotions.EmbeddingTypes.UnramifiedTrivialH1f (D := D) i dc := by
  intro D i dc w hw _ C
  rw [GlobalTheory.BridgeInertia.inertEq D i w hw]
  exact GlobalTheory.T.unramified_trivial_local (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i))
    (D.nbr i w hw).Kw C.LL

end GlobalTheory.ColumnUnramified
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoHypothesisGlobalStepAtQd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.BKAtQD

theorem admBK_embeddingTypeJumps : ∀ (D : D7), EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.LiteratureHypotheses (D := D) →
    ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.admBK i := by
  intro D hBK hLit i hi w hw C
  obtain ⟨-, hTD, -⟩ := hLit i hi
  exact ⟨(hTD w hw C).1, (hTD w hw C).2,
    fun _ => TruncatedSeriesCountingIdentities.bkBAt_of_core _ _ _ (hBK _ _).2.2.2.1 (GlobalTheory.AdmBK.litGoodO_all _ _)⟩

end GlobalTheory.BKAtQD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerCharStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, LocalSituation.Conclusion5 D := by
  first | exact @GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ | exact GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ | (intros; apply GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalConditionAllLocalizationsStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_localCondition_all_localizations : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.admBK i := by
  first | exact @GlobalTheory.AdmBK.admBK_loc_of_blochKato_tateDuality_euler | exact GlobalTheory.AdmBK.admBK_loc_of_blochKato_tateDuality_euler | (intros; apply GlobalTheory.AdmBK.admBK_loc_of_blochKato_tateDuality_euler <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdealStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliDet_block_levi_congr_mod_upperBlockIdeal : ∀ (A : Type) [Ring A] [Algebra ℂ A] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (X : Fin N → Fin N → A), Formalism.REAL.GlRel X → ∀ u : ℂ, Formalism.REAL.qdet X (u + ((N : ℂ) - 1) / 2) - (List.ofFn fun i : Fin c => Formalism.REAL.qdet (fun p q : Fin (n i) => X (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩)) (u + ((n i : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) i : ℂ) / 2)).prod ∈ Submodule.span ℂ {y : A | ∃ (p q : Fin N) (w : A), blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w} := by
  first | exact @GlobalTheory.CapHC.qdet_blocks_congr | exact GlobalTheory.CapHC.qdet_blocks_congr | (intros; apply GlobalTheory.CapHC.qdet_blocks_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetDiagonalBlockActsByInfinitesimalCharacStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliDet_diagonalBlock_acts_by_infinitesimalCharacter : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (τ : E →+* ℂ) (i : Fin c) (M : Multiset ℂ), (π i).HasInfChar τ M → ∀ (u : ℂ) (ψ : Sm E N), (fun m => ψ.1 (leviEmb (Ad E) (stdBlocks n h) m)) ∈ tensorForms π → ∀ m, (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩)) (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) = (M.map (u + ·)).prod * ψ.1 (leviEmb (Ad E) (stdBlocks n h) m) := by
  first | exact @GlobalTheory.BlockCap.qdet_block_levi | exact GlobalTheory.BlockCap.qdet_block_levi | (intros; apply GlobalTheory.BlockCap.qdet_block_levi <;> assumption)
end

