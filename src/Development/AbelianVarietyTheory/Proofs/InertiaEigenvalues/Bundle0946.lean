import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0941
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonOfScalar
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0015
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0017
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0023
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0024
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0022
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0025
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0027
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0025
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0938
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0940
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0929
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0539
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0542
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0920
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0790
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0942
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0167
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecEqZeroOfComplex

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitalIntegralLinearDescentCutoffStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegral_linearDescent_cutoff : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → (∀ g, 0 ≤ α g) → (∀ g : GL (Fin r) F, (∃ v w : Fin r → F, f' ((g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), v, w, lam) ≠ 0) → ∀ s₀ : A.Kˣ, ∫ s, α (g * LinDesc.tm A hG s₀ * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1) → ∀ κ₀ : ℂ, (∀ a : A.K, IsUnit a → ∀ g : GL (Fin r) F, omega (act g (LinDesc.pt A hG lam 1 a)) = κ₀ * eta ((g : Matrix (Fin r) (Fin r) F).det) * A.etaK a) → ∀ a : A.K, IsUnit a → orbG M f' (LinDesc.pt A hG lam 1 a) = κ₀ * A.orbK μK (LinDesc.desc A M hG lam α f') a := by
  first | exact @GlobalTheory.JR.LinDesc.orb_descent_unit | exact GlobalTheory.JR.LinDesc.orb_descent_unit | (intros; apply GlobalTheory.JR.LinDesc.orb_descent_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SectionIntegralEqualCharAbelianLocus
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer

namespace GlobalTheory.EqCharGood

theorem existsUnique_mulVec_of_inCell {V K : Type} [CommRing V] [CommRing K] (φ : V →+* K)
    (hφ : Function.Injective φ) {n r : ℕ} (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) V)
    (hc : GlobalTheory.Reg.InCell ix u) (cv : Fin n → V) (aK : Fin r → K)
    (h : (u.map φ).mulVec aK = fun i => φ (cv i)) : ∃! a, u.mulVec a = cv := by
  let A : Matrix (Fin r) (Fin r) V := u.submatrix ix id
  have hlow : A.BlockTriangular OrderDual.toDual := fun i j hij => hc.1 i j hij
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_lowerTriangular A hlow]
    exact Finset.prod_eq_one fun i _ => hc.2 i
  have hAu : IsUnit A.det := hdet ▸ isUnit_one
  have hAK : IsUnit (A.map φ).det := by
    have e : (A.map φ).det = φ A.det := (RingHom.map_det φ A).symm
    rw [e, hdet, map_one]; exact isUnit_one
  have hinjA : ∀ v w : Fin r → V, A.mulVec v = A.mulVec w → v = w := fun v w hvw => by
    have := congrArg (A⁻¹).mulVec hvw
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  have hinjAK : ∀ v w : Fin r → K, (A.map φ).mulVec v = (A.map φ).mulVec w → v = w := fun v w hvw => by
    have := congrArg ((A.map φ)⁻¹).mulVec hvw
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAK, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  have hrow : ∀ (v : Fin r → V), A.mulVec v = fun i => u.mulVec v (ix i) := fun v => rfl
  let a : Fin r → V := A⁻¹.mulVec (fun i => cv (ix i))
  have ha : A.mulVec a = fun i => cv (ix i) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mulVec]
  have hmap : ∀ (M : Matrix (Fin n) (Fin r) V) (v : Fin r → V),
      (M.map φ).mulVec (fun i => φ (v i)) = fun i => φ (M.mulVec v i) := fun M v => by
    funext i
    exact (RingHom.map_mulVec φ M v i).symm
  have haK : (fun i => φ (a i)) = aK := by
    refine hinjAK _ _ ?_
    have e1 : (A.map φ).mulVec (fun i => φ (a i)) = fun i => φ (cv (ix i)) := by
      funext i
      exact (congrFun (hmap u a) (ix i)).trans (congrArg φ (congrFun ha i))
    rw [e1]
    funext i
    exact (congrFun h (ix i)).symm
  refine ⟨a, ?_, fun a' ha' => hinjA _ _ ((hrow a').trans ((funext fun i => congrFun ha' (ix i)).trans ha.symm))⟩
  funext i
  apply hφ
  have := congrFun (hmap u a) i
  rw [haK, h] at this
  exact this.symm

end GlobalTheory.EqCharGood

namespace GlobalTheory.EqCharGood

set_option maxHeartbeats 2000000 in

theorem inV_of_extIn_eqChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → ∀ y : IntFr Xo c T io, (letI := io.toAlgebra; ExtIn Y (abLocus Y.t.G) T io y.1.x) → evI y f ∈ (algebraMap T.V T.Fr).range := by
  intro E _ _ _ H Dw l Xo c a n f hf la Y hP T io hio y hy
  classical
  obtain ⟨hE, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hS := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  obtain ⟨k, hk⟩ := exists_factor T io hio
  obtain ⟨y', z, h1, h2, h3, h4⟩ := hy
  have hs : y' ≫ Y.s = spMap (k.comp (la.valuation c.F).valuationSubring.subtype) := by
    have e1 : spMap (algebraMap T.V T.Fr) ≫ (y' ≫ Y.s) =
        spMap (algebraMap T.V T.Fr) ≫ spMap (k.comp (la.valuation c.F).valuationSubring.subtype) := by
      rw [← Category.assoc, ← h3, Category.assoc, GlobalTheory.TraitDataIntrinsic.j_s, ← Category.assoc, h2, sp_comp,
        sp_comp, ← RingHom.comp_assoc, hk]
    obtain ⟨φ, hφ⟩ : ∃ φ : (la.valuation c.F).valuationSubring →+* T.V, y' ≫ Y.s = spMap φ :=
      ⟨(Spec.preimage (y' ≫ Y.s)).hom, by simp [spMap]⟩
    rw [hφ, sp_comp, sp_comp] at e1
    rw [hφ]
    congr 1
    have e2 := CommRingCat.hom_ext_iff.1 (Spec.map_injective e1)
    exact RingHom.ext fun x => hinj (RingHom.congr_fun e2 x)
  let _ : Algebra c.F T.V := k.toAlgebra
  let _ : Algebra c.F T.Fr := io.toAlgebra
  obtain ⟨zV, hzV1, hzV2⟩ := exists_lift Y y' k hs h4
  obtain ⟨J, _, M, hM⟩ := GlobalTheory.Reg.exists_finite_mchart_cover E H Dw l Xo c (la.valuation c.F).valuationSubring _ Y hP
  obtain ⟨j, hj⟩ := hM (y' (IsLocalRing.closedPoint T.V))
  obtain ⟨-, -, h3'⟩ := GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c _ _ Y
  obtain ⟨-, -, -, h4'⟩ := h3' (M j).U (M j).hU
  obtain ⟨f₀, hf₀, -⟩ := h4' T.V y' hj
  obtain ⟨ΛV⟩ := GlobalTheory.Reg.MChart.nonempty_lift E H Dw l Xo c _ _ Y (M j) T.V f₀ zV hzV2 (hzV1.trans hf₀.symm)
  have hzj : z ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp f₀) ≫ (M j).hU.fromSpec := by
    rw [h3, ← hf₀, ← Category.assoc, sp_comp]
  have hK := GlobalTheory.Reg.MChart.nonempty_lift E H Dw l Xo c _ _ Y (M j) T.Fr _ z h2 hzj
  rw [h1] at hK
  obtain ⟨ΛK⟩ := hK
  obtain ⟨g, hg, hgi⟩ := GlobalTheory.Reg.MChart.Lift.exists_coordinates E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1 ΛK
  let W : ValuationSubring T.Fr := (valV T.V).valuationSubring
  have hW : ∀ x, x ∈ W → InV T x := fun x h => IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h
  choose ix u b huW hu0 hu1 hbt hbd hgub using
    fun τ => GlobalTheory.exists_integral_pivot_decomposition T.Fr W _ _ (g τ) (hgi τ)
  choose u₀' hu₀' using fun τ i j => hW _ (huW τ i j)
  let u₀ : ∀ τ : E →+* ℂ, Matrix (Fin (M j).n) (Fin (Dw.mult τ)) T.V := fun τ => Matrix.of fun i j' => u₀' τ i j'
  have hu₀ : ∀ τ i j', algebraMap T.V T.Fr (u₀ τ i j') = u τ i j' := hu₀'
  have hcell : ∀ τ, GlobalTheory.Reg.InCell (ix τ) (u₀ τ) := fun τ =>
    ⟨fun i j hij => hinj (by rw [hu₀, map_zero]; exact hu0 τ i j hij),
     fun i => hinj (by rw [hu₀, map_one]; exact hu1 τ i)⟩

  have heigMap : ∀ τ (cv : Fin (M j).n → T.V),
      (M j).Eig ((algebraMap T.V T.Fr).comp f₀) τ (fun i => algebraMap T.V T.Fr (cv i)) ↔ (M j).Eig f₀ τ cv := by
    intro τ cv
    refine forall_congr' fun a' => ?_
    have key : ∀ i, algebraMap T.V T.Fr ((((M j).ρ a').map f₀).mulVec cv i) =
        ((((M j).ρ a').map ((algebraMap T.V T.Fr).comp f₀)).mulVec (fun i => algebraMap T.V T.Fr (cv i))) i :=
      fun i => by rw [RingHom.map_mulVec]; rfl
    have key2 : ∀ i, algebraMap T.V T.Fr ((algebraMap c.F T.V (embK c τ a') • cv) i) =
        (algebraMap c.F T.Fr (embK c τ a') • fun i => algebraMap T.V T.Fr (cv i)) i := fun i => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      exact congrArg (· * _) (RingHom.congr_fun hk _)
    constructor
    · intro h
      funext i
      apply hinj
      rw [key, key2]
      exact congrFun h i
    · intro h
      funext i
      rw [← key, ← key2, h]
  have humap : ∀ τ, (u₀ τ).map (algebraMap T.V T.Fr) = u τ := fun τ => Matrix.ext fun i j' => hu₀ τ i j'
  have heigK : ∀ τ i, (M j).Eig ((algebraMap T.V T.Fr).comp f₀) τ (fun j' => u τ j' i) := by
    intro τ i a'
    have hgc : ∀ i, (M j).Eig ((algebraMap T.V T.Fr).comp f₀) τ (fun j' => g τ j' i) := fun i =>
      (GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK τ _ _ (hg τ i)).mp (y.1.eig τ i)
    have hG := (GlobalTheory.Reg.CellChart.mul_eq_smul_iff_cols (((M j).ρ a').map ((algebraMap T.V T.Fr).comp f₀))
      (algebraMap c.F T.Fr (embK c τ a')) (g τ)).mpr fun i => hgc i a'
    have hd : IsUnit (b τ).det := by
      rw [Matrix.det_of_upperTriangular (hbt τ)]
      exact (Finset.prod_ne_zero_iff.mpr fun i _ => hbd τ i).isUnit
    have hU : ((M j).ρ a').map ((algebraMap T.V T.Fr).comp f₀) * u τ = algebraMap c.F T.Fr (embK c τ a') • u τ := by
      have e : u τ = g τ * (b τ)⁻¹ := by rw [hgub τ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
      rw [e, ← Matrix.mul_assoc, hG, Matrix.smul_mul]
    exact (GlobalTheory.Reg.CellChart.mul_eq_smul_iff_cols _ _ _).mp hU i
  have heigV : ∀ τ i, (M j).Eig f₀ τ (fun j' => u₀ τ j' i) := fun τ i =>
    (heigMap τ _).mp (by simpa only [hu₀] using heigK τ i)
  obtain ⟨hv1, hv2, hv3⟩ := GlobalTheory.Reg.vec_bijective E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK
  have hbasis : ∀ τ cv, (M j).Eig f₀ τ cv → ∃! a, (u₀ τ).mulVec a = cv := by
    intro τ cv hcv
    have hcvK := (heigMap τ cv).mpr hcv
    obtain ⟨w, hw, -⟩ := hv1 (fun i => algebraMap T.V T.Fr (cv i))
    have htan := hv2 _ _ hw
    have heig := (GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK τ _ _ hw).mpr hcvK
    obtain ⟨a0, ha0, -⟩ := y.1.basis τ w htan heig
    have hv := (GlobalTheory.T.isCombAt_iff_coordinate_combination E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK _ (fun i j' => g τ j' i) (y.1.u τ) a0 w
      (hg τ)).mp ha0
    have heq : (∑ i, a0 i • fun j' => g τ j' i) = fun i => algebraMap T.V T.Fr (cv i) := (hv3 w htan).unique hv hw
    refine GlobalTheory.EqCharGood.existsUnique_mulVec_of_inCell (algebraMap T.V T.Fr) hinj (ix τ) (u₀ τ) (hcell τ) cv
      ((b τ).mulVec a0) ?_
    rw [humap, Matrix.mulVec_mulVec, ← hgub τ, ← heq]
    funext j'
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  obtain ⟨yV, -, hyV⟩ := GlobalTheory.Reg.exists_frPt_tie hS E H Dw l Xo c _ _ Y (M j) T.V f₀ _ ΛV u₀ heigV hbasis
  let φ : T.V →ₐ[c.F] T.Fr := ⟨algebraMap T.V T.Fr, fun x => RingHom.congr_fun hk x⟩
  obtain ⟨zK, hzK⟩ := hE.bc _ _ φ yV
  have htK := GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c _ _ Y (M j) T.V T.Fr f₀ φ u₀ yV zK hyV hzK
  have hint : Integral T io zK := GlobalTheory.Reg.tie_integral hS E H Dw l Xo c _ _ Y (M j) hP T io f₀ ix u₀ hcell zK
    (GlobalTheory.Reg.CellChart.tie_congr htK (fun _ => rfl) (fun _ _ _ => rfl))
  have htu : (M j).Comparison₂ ((algebraMap T.V T.Fr).comp f₀) u zK :=
    GlobalTheory.Reg.CellChart.tie_congr htK (fun _ => rfl) (fun τ i j' => hu₀ τ i j')
  obtain ⟨t, ht⟩ := GlobalTheory.Reg.frBor_of_tie E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1 zK ΛK u b
    (GlobalTheory.Reg.CellChart.lift_point_unique htu.choose ΛK) (fun τ => ⟨hbt τ, hbd τ⟩)
    (by rw [show (fun τ => u τ * b τ) = g from funext fun τ => (hgub τ).symm]; exact hg) htu
  show InV T (evI y f)
  rw [inV_of_frBor hf y ⟨zK, hE.test _ zK, hint⟩ t ht]
  show InV T (evR Xo c f zK)
  rw [(GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hf T.V).1 T.Fr φ yV zK hzK]
  exact ⟨_, rfl⟩

end GlobalTheory.EqCharGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarAndSizeBound
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem rowsAD_in_setting : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ),
    Setup L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) →
    KillingConditions.StarAD L X ∧ KillingConditions.BBLe L X 7200 := by
  intro hP D L P nch HW F Cm X C₂ hS hC hp2 hBCD
  have hstep : KillingConditions.StepAD L X :=
    { a09 := GlobalTheory.T.admissible_at_inert hP D L P nch HW F Cm X C₂ hS hC hp2 hBCD
      a78 := GlobalTheory.T.unramified_places_declared hP D L P nch HW F Cm X C₂ hS
      goodR := hS.canon.fam.good }
  have hst1 : TruncatedSeriesCountingIdentities.IntegralityFromMetric D := GlobalTheory.T.integralityFromMetric_of_designConditionAll hP.artin hP.bk hP.tate hP.euler D hS.facts.duties.2.2.1
  have h78 := GlobalTheory.T.splitCase_bound_at_point_of_admitted_items_alt hP.artin hP.tate hP.euler D
  have hG2 : ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admG2 i (X.r i) (X.ρ i) π :=
    fun i hi π hπ => (GlobalTheory.T.set_point_good hP D L P nch HW F Cm X C₂ hS i hi π hπ).2.1
  refine ⟨GlobalTheory.T.starInequality_rowsAD_of_global_theorems D L HW X (rowC C₂) hS.canon.data hstep hst1 h78 hG2 hS.kill hS.sha, ?_⟩
  have h := GlobalTheory.T.nonPlacePart_localBound_le_middleRange D L P HW X (rowC C₂) 120 (by norm_num) hS.canon.data
    (GlobalTheory.T.joint_condition_adm5 hP D L P nch HW F Cm X C₂ hS)
  have e : (60 : ℝ) * 120 = 7200 := by norm_num
  rwa [e] at h

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfAdmittedHypothesesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theoremB_of_admittedHypotheses : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 13 * max CA 0 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp := by
  first | exact @GlobalTheory.TheoremB.theoremB_of_admitted | exact GlobalTheory.TheoremB.theoremB_of_admitted | (intros; apply GlobalTheory.TheoremB.theoremB_of_admitted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorIsThetaFunctionTwoStepModelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftVector_isThetaFunction_twoStepModel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0) (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ (R.Q t) → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eQ) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg (fun x => if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) (R.vP i t) := by
  first | exact @GlobalTheory.ConjTwist.isThetaAt_vP_twoStep | exact GlobalTheory.ConjTwist.isThetaAt_vP_twoStep | (intros; apply GlobalTheory.ConjTwist.isThetaAt_vP_twoStep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaWeilTwist
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilTwistSeries

theorem twist_val_mem {D : D7} {pd : ℕ} {k : Type} [Field k] {σ : k →+* ℂ} {δ : Formalism.L2.Host.HChar D.host.E}
    {δc : (AE D)ˣ →* Circle} (h : IsTwist pd σ δ δc) (x : (AE D)ˣ) : ((δc x : Circle) : ℂ) ∈ σ.fieldRange := by
  obtain ⟨hE, ⟨n, hn, ho⟩, -, ht, -, hv⟩ := h
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  have hfin := (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ δ).1
  have hu : ∀ v, v ∉ hfin.toFinset → δ.UnrAt v := fun v hv' => by
    by_contra hc
    exact hv' (hfin.mem_toFinset.2 hc)
  refine GlobalTheory.TwistValues.char_mem δc δ hE hn ho σ.fieldRange (fun P k => ?_) x
  exact GlobalTheory.TwistValues.locK_mem δ (GlobalTheory.RationalValues.unitsIn σ.fieldRange) hfin.toFinset ht
    (GlobalTheory.TypeValues.inf_eq_one δ hn ho) hu
    (fun v hv' => by
      obtain ⟨y, hy⟩ := hv v (hu v hv')
      show ((δ.val v : ℂˣ) : ℂ) ∈ σ.fieldRange
      refine ⟨y, ?_⟩
      rw [hy, Formalism.L2.Host.HChar.valTw]
      simp) P k

theorem theta_weil_twist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
      ∀ (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist C.d.pd C.σ₂ δ δc →
      ∀ om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ),
        IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).1
          (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).2 om →
      ∀ s ∈ GfC (Vc D i), ∀ f : WO (Vc D i) (Wc D i) → ℂ,
        IsLevDatum R.ψ (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (T.Q.l.M * C.d.pd) C.σ₂.fieldRange (R.vacP i) f →
      ∀ w ∈ ratVec R i (c0L i) C.σ₂.fieldRange,
        ∃ c ∈ C.σ₂.fieldRange, ∃ dd : GA D (Wc D i) → ℂ, (MuVal (Wc D i) δc dd ∨ MuVal (Wc D i) δc⁻¹ dd) ∧
          ∀ g, thetaKO om s g (harmVec R i u w f) = c * (dd g * thetaKO (R.ωP i A.μ0) s g (harmVec R i u w f)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hJ hL hG hFam hMod hP hT i hV hpin gramR c0R c0L hB u hu C hC δ δc hδ om hom s hs
    f hf w hw
  have hψ : IsStdChar D R.ψ (-1) := (hP.ωP i A.μ0).std
  have hvac := (hP.vP i A.μ0).1
  have hθ : IsInfFam R.θ := hvac.2.inf
  have hf0 : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := GlobalTheory.OneMapRef.isThetaFunO_of_isVacO hvac
  obtain ⟨P, e, Φ, -, -, -, -, -, hTh⟩ := hf
  have hft : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hθ hTh hf0
  have hH : IsThetaFunO R.ψ (Vc D i) (Wc D i) (harmVec R i u w f) :=
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ _ _ _ _ hft _
  have hxi : R.xi A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0))
  have hmu : R.toLevCh.mu A.μ0 = Lift.tup R.mu0 (1 : (AE D)ˣ →* Circle) := by
    unfold LevCh.mu
    rw [hxi]
  have hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh R.mu0 R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh R.mu0 R.eta ((i : ℕ) + 1)).2 (R.ωP i A.μ0) := by
    have h := hP.ωP i A.μ0
    rw [hmu, GlobalTheory.SplitChange.chrTh_tup] at h
    simpa only [mul_one] using h
  rw [GlobalTheory.SplitChange.chrTh_tup] at hom
  have hδH : IsHeckeChar D δc := hδ.1.1
  have hδF : ∀ a, δc (idF D a) = 1 := GlobalTheory.GridWeil.triv_base hδ.1 hδ.2.2.1
  obtain ⟨nV, hnV, -⟩ := GlobalTheory.Member.exists_muVal D (Vc D i) δc hδH hδF
  obtain ⟨nW, hnW, -⟩ := GlobalTheory.Member.exists_muVal D (Wc D i) δc hδH hδF
  obtain ⟨x, hx⟩ := hnV.1 s
  refine ⟨(nV s)⁻¹, ?_, nW, Or.inl hnW, fun g => ?_⟩
  · rw [hnV.2 s x hx]
    exact inv_mem (twist_val_mem hδ x)
  · rw [GlobalTheory.SplitChange.thetaKO_twist hω hδH hδF hom hnV hnW s g hH]
    ring

end GlobalTheory.WeilTwistSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaLieAlgebraUnitaryGroupOfJacquetRallis
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem unitLemma_lie_and_group (hM : ∀ r : ℕ, GlobalTheory.JR.UnitMatch r) :
    UnitLemmaLie ∧ UnitLemmaGroup :=
  have hL : UnitLemmaLie := GlobalTheory.T.unitLemmaSelfAdjointLie_of_count_limit_descent (GlobalTheory.T.relativeFundamentalLemmaCountIdentity_of_unitMatch hM) GlobalTheory.T.unitary_lattice_count_ratio_tendsto GlobalTheory.T.linearLatticeCountDescent_proof
  ⟨hL, GlobalTheory.T.unitLemma_unitary_group_odd_residue_of_lie hL⟩

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedEnlargementCutCocyclesBlochKatoStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedEnlargement_cut_cocycles_blochKato : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    (∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π),
      (fun g => liftQ C.le D.R.r (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C (WpO D.nd i ρ π)))) ∧
    (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c),
      (fun g => liftQ C.le 1 (z g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c)))) ∧
    (∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1),
      (fun g => liftQ C.le 1 (z g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) (IK (D.nbr i w hw).Kw)) := by
  first | exact @GlobalTheory.UseLoc.Cases.main | exact GlobalTheory.UseLoc.Cases.main | (intros; apply GlobalTheory.UseLoc.Cases.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightZeroSectionValueOnMarkedPeriodSpaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightZeroSection_value_on_markedPeriodSpace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (a : Tp) (C : GlobalTheory.Member.Ctx (M.dδ a).Xo₂ (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (Wc D i) D.R.r), C.OK → C.ι = iotaW T i → C.x₀ = T.x₀ ((i : ℕ) + 1) M.s0 → ∀ (f : Rul (M.dδ a).Xo₂ (M.dδ a).c₂) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ), f ∈ sec (M.dδ a).Xo₂ (M.dδ a).c₂ 0 0 → (∀ u : GA D (Wc D i), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ a).l₂.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1) → (∀ γ ∈ GQ (Wc D i), xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) γ)) = 1) → GlobalTheory.OneMapAll.CXiAt (Wc D i) (rank_Wc i) (inC M.c') { M.dδ a with cδ := f } (M.U₂ a) (M.dict₂ a) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) xi c0 → ∀ (y : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ (CAt ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)))) (k : Fin C.F.n) P, IsPeriod (C.F.Di k) (fun j => relab (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (C.e j).1) P → y.x = C.F.u k P → ∀ h γ : GA D (Wc D i), C.Mark h k γ → toC (evR (M.dδ a).Xo₂ (M.dδ a).c₂ f y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) (γ * h))) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.MarkVal.val_on_marked_space | exact GlobalTheory.MarkVal.val_on_marked_space | (intros; apply GlobalTheory.MarkVal.val_on_marked_space <;> assumption)
end

