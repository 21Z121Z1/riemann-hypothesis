import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0651
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0657
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffsInIdealOfPowerSeriesIffImageStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffsInIdealOfPowerSeries_iff_image : ∀ (B Q σ : Type) [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B) (f : MvPowerSeries σ Q), (In N f ↔ ∃ s : MvPowerSeries σ B, (∀ α, coeff α s ∈ N) ∧ map (algebraMap B Q) s = f) ∧ ∀ g : MvPowerSeries σ Q, In N f → In N g → ∀ a : B, In N (f + algebraMap B Q a • g) ∧ In N (f - g) := by
  first | exact @GlobalTheory.series_in_ideal_iff_image | exact GlobalTheory.series_in_ideal_iff_image | (intros; apply GlobalTheory.series_in_ideal_iff_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffsInIdealSolutionOfUnipotentSeriesMatrixStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffsInIdeal_solution_of_unipotent_series_matrix : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (N : Ideal B) (M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) B)), (∀ i j, constantCoeff (M i j) = if i = j then 1 else 0) → ∀ (v g : Fin d → MvPowerSeries (Fin d) Q), (∀ i, ∑ j, v j * map (algebraMap B Q) (M j i) = g i) → (∀ i, In N (g i)) → ∀ j, In N (v j) := by
  first | exact @GlobalTheory.InvSolve.solve | exact GlobalTheory.InvSolve.solve | (intros; apply GlobalTheory.InvSolve.solve <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyClassPullbackReductionPairs
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

section PairNat

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Y Y' : Scheme.{0}}
  {φ : X' ⟶ X} {χ : Y' ⟶ Y} {ψ : Y ⟶ X} {ψ' : Y' ⟶ X'}

theorem pre_le_pre (e : ψ' ≫ φ = χ ≫ ψ) {V : Y.Opens} {U : X.Opens} (hp : V ≤ ψ ⁻¹ᵁ U) :
    χ ⁻¹ᵁ V ≤ ψ' ⁻¹ᵁ (φ ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, e, Scheme.Hom.comp_preimage]
  exact fun x hx ↦ hp hx

variable [IsAffineHom φ] [IsAffineHom χ]

def prePairMap (e : ψ' ≫ φ = χ ≫ ψ) (p : Pair ψ) : Pair ψ' :=
  ⟨(preU χ p.1.1, preU φ p.1.2), pre_le_pre e p.2⟩

theorem prePairMap_mono (e : ψ' ≫ φ = χ ≫ ψ) : Monotone (prePairMap e) := fun _ _ h ↦
  show _ ∧ _ from ⟨preU_mono χ (Pair.le_fst h), preU_mono φ (Pair.le_snd h)⟩

def preFun (e : ψ' ≫ φ = χ ≫ ψ) : (Pair ψ)ᵒᵖ ⥤ (Pair ψ')ᵒᵖ := (prePairMap_mono e).functor.op

variable {s' : X' ⟶ Sp R'} {q' : Y' ⟶ Sp R'}

variable (s' q') in

def preCoefPair (e : ψ' ≫ φ = χ ≫ ψ) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) :
    CoefMap (RingHom.id R') (OPre φ s') (pairFst ψ ⋙ OPre χ q') where
  G := pairSnd ψ
  α p := secPull s' q' (prePairMap e p.unop)
  naturality a b := (pairPull w').naturality ((preFun e).map a) b
  smul p := semiHom_secPull w' (prePairMap e p.unop)

end PairNat

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem red_preimage_pairs : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' Y Y' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (φ : X' ⟶ X) (χ : Y' ⟶ Y) [IsAffineHom χ] (h : φ ≫ s = s' ≫ spMap σ) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')), ψ' ≫ φ = χ ≫ ψ → IsAffineHom φ → (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x → ∃ c : Z1 (pairFst ψ ⋙ OPre χ q'), (∀ a b (u : a ⟶ b), c.1 a b u = preα χ q q' ((pairFst ψ).obj b) ((pairPull w).α b (f _ _ ((pairPull w).G.map u)))) ∧ GlobalTheory.CatCoh.H1.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 (pullHO1 w' x)) ∧ ∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z → ∃ c : Z2 (pairFst ψ ⋙ OPre χ q'), (∀ a b d (u : a ⟶ b) (u' : b ⟶ d), c.1 a b d u u' = preα χ q q' ((pairFst ψ).obj d) ((pairPull w).α d (v _ _ _ ((pairPull w).G.map u) ((pairPull w).G.map u')))) ∧ GlobalTheory.CatCoh.H2.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 (pullHO2 w' z) := by
  intro R R' _ _ σ X X' Y Y' s s' q q' φ χ _ h ψ ψ' w w' e hφ
  haveI := hφ
  have H := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h
  let m := preCoefPair s' q' e w'
  let Φ := preFun (φ := φ) (χ := χ) e
  have hα : ∀ (p : (Pair ψ)ᵒᵖ) (b : (OAff s).obj ((pairSnd ψ).obj p)),
      m.α p (preα φ s s' ((pairSnd ψ).obj p) b) =
        preα χ q q' ((pairFst ψ).obj p) ((pairPull w).α p b) := by
    intro p b
    have k1 := congrArg (fun t ↦ t.hom b) (Scheme.Hom.appLE_comp_appLE ψ' φ _ _ _
      (prePair φ p.unop.1.2).2 (prePairMap e p.unop).2)
    have k2 := congrArg (fun t ↦ t.hom b) (Scheme.Hom.appLE_comp_appLE χ ψ _ _ _
      p.unop.2 (prePair χ p.unop.1.1).2)
    have k3 : ∀ (g₁ g₂ : Y' ⟶ X) (_ : g₁ = g₂) (h1 : (preU χ p.unop.1.1).1 ≤ g₁ ⁻¹ᵁ p.unop.1.2.1)
        (h2 : (preU χ p.unop.1.1).1 ≤ g₂ ⁻¹ᵁ p.unop.1.2.1) (x : Γ(X, p.unop.1.2.1)),
        (g₁.appLE _ _ h1).hom x = (g₂.appLE _ _ h2).hom x := by
      rintro _ _ rfl _ _ _; rfl
    refine k1.trans (Eq.trans ?_ k2.symm)
    exact k3 _ _ e _ _ b
  let θ1 : ((preRes φ s').comp m).G ⟶ ((pairPull w').comp (CoefMap.restrict (OPair ψ' q') Φ)).G :=
    { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
  let θ2 : ((pairRes ψ' q').comp (CoefMap.restrict (OPair ψ' q') Φ)).G ⟶
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).G :=
    { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
  have h1 : ∀ T b, ((pairPull w').comp (CoefMap.restrict (OPair ψ' q') Φ)).α T
      (mp (OAff s') (θ1.app T) b) = ((preRes φ s').comp m).α T b := fun T b ↦ by
    exact congrArg (((pairPull w').comp (CoefMap.restrict (OPair ψ' q') Φ)).α T) (mp_id (OAff s') _ b)
  have h2 : ∀ T b, (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).α T
      (mp (OAff q') (θ2.app T) b) = ((pairRes ψ' q').comp (CoefMap.restrict (OPair ψ' q') Φ)).α T b :=
    fun T b ↦ by
      exact congrArg ((CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).α T) (mp_id (OAff q') _ b)
  refine ⟨fun f x hr ↦ ?_, fun v z hr ↦ ?_⟩
  · obtain ⟨c0, hc0, hcl⟩ := (H.1 f x).1 hr
    refine ⟨m.pullbackOneCocycle c0, fun a b u ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleOne_apply, hc0]; exact hα b _
    · rw [← CoefMap.pullCohomologyOne_class, hcl, ← CoefMap.pullCohomologyOne_comp]
      exact (CoefMap.pullCohomologyOne_eq_of_natTrans _ _ θ1 h1 x).trans ((CoefMap.pullCohomologyOne_comp _ _ x).trans
        ((congrArg _ (isPullO_pullHO1 w' x)).trans ((CoefMap.pullCohomologyOne_comp _ _ _).symm.trans
          (CoefMap.pullCohomologyOne_eq_of_natTrans _ _ θ2 h2 _))))
  · obtain ⟨c0, hc0, hcl⟩ := (H.2.1 v z).1 hr
    have k : (pairRes ψ' q').pull2 (pullHO2 w' z) = (pairPull w').pull2 z :=
      (LinearEquiv.ofBijective _ (pairRes_pull2_bijective ψ' q')).apply_symm_apply _
    refine ⟨m.pullbackTwoCocycle c0, fun a b d u u' ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleTwo_apply, hc0]; exact hα d _
    · rw [← CoefMap.pullCohomologyTwo_class, hcl, ← CoefMap.pullCohomologyTwo_comp]
      exact (CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ θ1 h1 z).trans ((CoefMap.pullCohomologyTwo_comp _ _ z).trans
        ((congrArg _ k.symm).trans ((CoefMap.pullCohomologyTwo_comp _ _ _).symm.trans
          (CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ θ2 h2 _))))

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousCofilteredAffineLimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

abbrev isoSpecSp (X : Scheme.{0}) [IsAffine X] : sch.obj X ⟶ sp Γ(X, ⊤) := sch.map X.isoSpec.hom

theorem pull_isoSpecSp_inv (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (X : Scheme.{0}) [IsAffine X]
    (x : H R (sch.obj X) F n) : pull R (isoSpecSp X) F n (pull R (sch.map X.isoSpec.inv) F n x) = x := by
  rw [← pull_comp, ← sch.map_comp, Iso.hom_inv_id, sch.map_id, pull_id]

theorem pull_isoSpecSp_inv' (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (X : Scheme.{0}) [IsAffine X]
    (x : H R (sp Γ(X, ⊤)) F n) : pull R (sch.map X.isoSpec.inv) F n (pull R (isoSpecSp X) F n x) = x := by
  rw [← pull_comp, ← sch.map_comp, Iso.inv_hom_id, sch.map_id, pull_id]

theorem isoSpecSp_naturality {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    isoSpecSp X ≫ spMap f.appTop.hom = sch.map f ≫ isoSpecSp Y := by
  simp only [isoSpecSp, spMap, CommRingCat.ofHom_hom, ← sch.map_comp, Scheme.isoSpec_hom_naturality]

theorem pull_isoSpecSp_naturality (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (z : H R (sp Γ(Y, ⊤)) F n) :
    pull R (sch.map f) F n (pull R (isoSpecSp Y) F n z) = pull R (isoSpecSp X) F n (pull R (spMap f.appTop.hom) F n z) := by
  rw [← pull_comp, ← pull_comp, isoSpecSp_naturality]

theorem contCone_of_affine_limit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i)) → ContCone R F (sch.mapCone c) := by
  intro R _ F hF I _ _ G c hc hG
  haveI : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let c' : Cocone (G ⋙ Scheme.Γ.rightOp).leftOp := coconeLeftOpOfCone (Scheme.Γ.rightOp.mapCone c)
  have hc' : IsColimit c' := isColimitCoconeLeftOpOfCone _ (isLimitOfPreserves Scheme.Γ.rightOp hc)
  have hb := GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary R F hF Iᵒᵖ _ c' hc'
  intro n
  obtain ⟨h1, h2⟩ := hb n
  refine ⟨fun x => ?_, fun i y hy => ?_⟩
  · obtain ⟨j, y', hy'⟩ := h1 (pull R (sch.map c.pt.isoSpec.inv) F n x)
    refine ⟨j.unop, pull R (isoSpecSp (G.obj j.unop)) F n y', ?_⟩
    change pull R (sch.map (c.π.app j.unop)) F n _ = x
    refine (pull_isoSpecSp_naturality R F n (X := c.pt) (Y := G.obj j.unop) (c.π.app j.unop) y').trans ?_
    change pull R (isoSpecSp c.pt) F n (pull R (spMap (c'.ι.app j).hom) F n y') = x
    rw [hy', pull_isoSpecSp_inv]
  · change pull R (sch.map (c.π.app i)) F n y = 0 at hy
    let y' : H R (sp Γ(G.obj i, ⊤)) F n := pull R (sch.map (G.obj i).isoSpec.inv) F n y
    have hyy : y = pull R (isoSpecSp (G.obj i)) F n y' := (pull_isoSpecSp_inv R F n _ y).symm
    have hz : pull R (spMap (c'.ι.app (op i)).hom) F n y' = 0 := by
      have e : pull R (isoSpecSp c.pt) F n (pull R (spMap (c.π.app i).appTop.hom) F n y') = 0 := by
        rw [← pull_isoSpecSp_naturality R F n (X := c.pt) (Y := G.obj i) (c.π.app i) y', ← hyy]
        exact hy
      have e2 := congrArg (pull R (sch.map c.pt.isoSpec.inv) F n) e
      rw [pull_isoSpecSp_inv', map_zero] at e2
      exact e2
    obtain ⟨k, f, hk⟩ := h2 (op i) y' hz
    refine ⟨k.unop, f.unop, ?_⟩
    change pull R (sch.map (G.map f.unop)) F n y = 0
    rw [hyy]
    refine (pull_isoSpecSp_naturality R F n (X := G.obj k.unop) (Y := G.obj i) (G.map f.unop) y').trans ?_
    change pull R (isoSpecSp (G.obj k.unop)) F n (pull R (spMap ((G ⋙ Scheme.Γ.rightOp).leftOp.map f).hom) F n y') = 0
    rw [hk]
    exact AddMonoidHom.map_zero _

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleGlobalOneFormsFiniteProjectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glob1_finite_and_projective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Module.Finite R (Glob1 F) ∧ Module.Projective R (Glob1 F) := by
  first | exact @GlobalTheory.AbCoh.compatibleGlobalOneForms_finite_projective | exact GlobalTheory.AbCoh.compatibleGlobalOneForms_finite_projective | (intros; apply GlobalTheory.AbCoh.compatibleGlobalOneForms_finite_projective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckePartialLSeriesEntireBoundedStripsStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_heckePartialLSeries_entire_bounded_strips : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (M : Ideal (𝓞 K)) (F : 𝓞 K → ℂ), M ≠ ⊥ → (∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) → (∀ (u : (𝓞 K)ˣ) (α : 𝓞 K), F ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips Λ ∧ ∀ s : ℂ, 1 < s.re → Λ s = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s := by
  first | exact @GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded | exact GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded | (intros; apply GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHermitianFormUnitaryChartSection
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.SUChartSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_eq_dot (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    hermC τ G u v = u ⬝ᵥ (G.map τ *ᵥ fun l => conj (v l)) := by
  simp only [hermC, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hermC_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ)
    (u v : Fin r → ℂ) :
    hermC τ G (M *ᵥ u) (M *ᵥ v) = u ⬝ᵥ (gram τ G M *ᵥ fun l => conj (v l)) := by
  have hc : (fun l => conj ((M *ᵥ v) l)) = M.map (starRingEnd ℂ) *ᵥ fun l => conj (v l) := by
    funext l
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [hermC_eq_dot, hc, FrameDegreeData.gram_eq, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem gram_secM (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {w : V (nd X)}
    (hw : cpt X x w ∈ X.dom) (τ : X.Ψ) :
    gram τ.1 X.Gm (secM X x w τ) = gram τ.1 X.Gm 1 := by
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ)
  have hgx : secM X x w τ * mat x τ = mat (rmul (cpt X x w) (FrameDegreeData.bOf X (cpt X x w))) τ := by
    rw [secM, Matrix.nonsing_inv_mul_cancel_right _ _ hu, bOf_cpt X hx, yM, ← Matrix.mul_assoc]
    rfl
  have key : (mat x τ)ᵀ * gram τ.1 X.Gm (secM X x w τ) * (mat x τ).map (starRingEnd ℂ) =
      (mat x τ)ᵀ * gram τ.1 X.Gm 1 * (mat x τ).map (starRingEnd ℂ) := by
    rw [← FrameDegreeData.gram_mul, hgx, FrameDegreeData.ortho_bOf X hw τ, ← hx τ, ← FrameDegreeData.gram_mul, Matrix.one_mul]
  have huT : IsUnit (mat x τ)ᵀ.det := by rwa [Matrix.det_transpose]
  have huC : IsUnit ((mat x τ).map (starRingEnd ℂ)).det := by
    rw [show (mat x τ).map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (mat x τ) from rfl, ← RingHom.map_det, isUnit_iff_ne_zero, map_ne_zero]
    exact det_ne_of_orth X hx τ
  have h2 := congrArg (fun M => ((mat x τ)ᵀ)⁻¹ * M * ((mat x τ).map (starRingEnd ℂ))⁻¹) key
  simp only [Matrix.mul_assoc] at h2
  simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ huT, Matrix.mul_nonsing_inv_cancel_right _ _ huC,
    ← Matrix.mul_assoc] using h2

theorem hermC_secM (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {w : V (nd X)}
    (hw : cpt X x w ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (secM X x w τ *ᵥ u) (secM X x w τ *ᵥ v) = hermC τ.1 X.Gm u v := by
  rw [hermC_mulVec, gram_secM X hx hw τ, ← hermC_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]

end GlobalTheory.SUChartSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComulChartSubSubstMemPSmul
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

namespace GlobalTheory

theorem comul_ev_sub_ev₂_subst_mem :
    ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ)
      (F : MvPowerSeries (Fin d) O), ∃ t : G.A n ⊗[O] G.A n,
        Coalgebra.comul (R := O) (c.ev n F) - c.ev₂ n (subst c.μ F) = (p : O) • t := by
  intro p O _ G d c n F
  have hμ : HasSubst c.μ := hasSubst_of_constantCoeff_zero c.isLaw.const
  let φ₁ : MvPowerSeries (Fin d) O →ₐ[O] G.A n ⊗[O] G.A n :=
    (Bialgebra.comulAlgHom O (G.A n)).comp (c.ev n)
  let φ₂ : MvPowerSeries (Fin d) O →ₐ[O] G.A n ⊗[O] G.A n := (c.ev₂ n).comp (substAlgHom hμ)
  have h1 : ∀ f, φ₁ f = Coalgebra.comul (R := O) (c.ev n f) := fun f => rfl
  have h2 : ∀ f, φ₂ f = c.ev₂ n (subst c.μ f) := fun f => by
    simp only [φ₂, AlgHom.comp_apply, coe_substAlgHom]
  have hpoly : φ₁.comp (MvPolynomial.coeToMvPowerSeries.algHom O) =
      φ₂.comp (MvPolynomial.coeToMvPowerSeries.algHom O) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp only [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, MvPolynomial.coe_X,
      Algebra.algebraMap_self, MvPowerSeries.map_id, RingHom.id_apply]
    rw [h1, h2, (c.isEval n).1 i, subst_X hμ, c.comul]
  obtain ⟨N₁, hN₁⟩ := (c.isEval n).2 1
  obtain ⟨N₂, hN₂⟩ := (c.isEval₂ n).2 1
  set N := max N₁ N₂
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N) F
  set T := F - (P : MvPowerSeries (Fin d) O)
  have hT : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α T = 0 := by
    intro α hα
    simp only [T, P, map_sub, MvPolynomial.coeff_coe, coeff_trunc']
    rw [if_pos, sub_self]
    intro i
    show α i ≤ N
    exact le_of_lt (lt_of_le_of_lt (Finsupp.le_degree i α) hα)
  have hPe : φ₁ (P : MvPowerSeries (Fin d) O) = φ₂ (P : MvPowerSeries (Fin d) O) := by
    have := congrArg (fun ψ => ψ P) hpoly
    simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using this
  obtain ⟨a, ha⟩ := hN₁ T fun α hα => hT α (lt_of_lt_of_le hα (le_max_left _ _))
  obtain ⟨b, hb⟩ := hN₂ (subst c.μ T) fun β hβ =>
    coeff_subst_eq_zero_of_degree_lt O (Fin d) (Fin d ⊕ Fin d) c.μ T N c.isLaw.const hT β
      (lt_of_lt_of_le hβ (le_max_right _ _))
  rw [pow_one] at ha hb
  refine ⟨Coalgebra.comul (R := O) a - b, ?_⟩
  have hF : F = (P : MvPowerSeries (Fin d) O) + T := by simp [T]
  rw [← h1, ← h2, hF, map_add, map_add, hPe, add_sub_add_left_eq_sub, h1, h2, ha, hb,
    ← Bialgebra.comulAlgHom_apply, map_mul, map_natCast, Bialgebra.comulAlgHom_apply,
    ← mul_sub, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSkewMemProductSpecialUnitaryLieAlgebra
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.SUChartSection

theorem conj_mem_realLie : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (Y : X.Ψ → Matrix (Fin r) (Fin r) ℂ), (∀ τ a b, Y τ b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) + ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (Y τ a b) = 0) → (∀ τ a, Y τ a a = 0) → (fun τ => ((mat x τ * Y τ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Fin r → Fin r → ℂ)) ∈ realLie X.Ψ X.Gm := by
  intro E _ _ _ r X x hx Y hY hd
  intro τ
  set A : Matrix (Fin r) (Fin r) ℂ := mat x τ with hAdef
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ)
  set D : Matrix (Fin r) (Fin r) ℂ := A * Y τ * A⁻¹ with hDdef
  have hDA : D * A = A * Y τ := by
    rw [hDdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · change (A * Y τ * A⁻¹).trace = 0
    rw [Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
    simp only [Matrix.trace, Matrix.diag, hd, Finset.sum_const_zero]
  · intro u w
    change hermC τ.1 X.Gm (D *ᵥ u) w + hermC τ.1 X.Gm u (D *ᵥ w) = 0
    clear_value D
    set Gt : Matrix (Fin r) (Fin r) ℂ := X.Gm.map τ.1 with hGt
    have hform : ∀ u v : Fin r → ℂ, hermC τ.1 X.Gm u v = u ⬝ᵥ (Gt *ᵥ (fun b => conj (v b))) := by
      intro u v
      simp only [hermC, dotProduct, mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [hGt, Matrix.map_apply]
      ring
    have hconj : ∀ v : Fin r → ℂ, (fun b => conj ((D *ᵥ v) b)) = D.map (starRingEnd ℂ) *ᵥ (fun b => conj (v b)) := by
      intro v
      funext b
      simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    set M : Matrix (Fin r) (Fin r) ℂ := Dᵀ * Gt + Gt * D.map (starRingEnd ℂ) with hMdef
    have hsum : hermC τ.1 X.Gm (D *ᵥ u) w + hermC τ.1 X.Gm u (D *ᵥ w) =
        u ⬝ᵥ (M *ᵥ (fun b => conj (w b))) := by
      rw [hform, hform, hconj, hMdef, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]
      congr 1
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]
    have hJ : Aᵀ * Gt * A.map (starRingEnd ℂ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
      rw [hGt, ← FrameDegreeData.gram_eq]
      exact hx τ
    have hkey : Aᵀ * M * A.map (starRingEnd ℂ) = 0 := by
      have e1 : Aᵀ * M * A.map (starRingEnd ℂ) =
          (D * A)ᵀ * Gt * A.map (starRingEnd ℂ) + Aᵀ * Gt * (D * A).map (starRingEnd ℂ) := by
        rw [hMdef, Matrix.transpose_mul, Matrix.map_mul]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      have e2 : (D * A)ᵀ * Gt * A.map (starRingEnd ℂ) + Aᵀ * Gt * (D * A).map (starRingEnd ℂ) =
          (Y τ)ᵀ * (Aᵀ * Gt * A.map (starRingEnd ℂ)) + (Aᵀ * Gt * A.map (starRingEnd ℂ)) * (Y τ).map (starRingEnd ℂ) := by
        rw [hDA, Matrix.transpose_mul, Matrix.map_mul]
        simp only [Matrix.mul_assoc]
      rw [e1, e2, hJ]
      ext a b
      simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
        Matrix.map_apply, Matrix.zero_apply]
      exact hY τ a b
    have hAt : IsUnit Aᵀ.det := by rwa [Matrix.det_transpose]
    have hAc : IsUnit (A.map (starRingEnd ℂ)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact hA.map _
    have hM : M = 0 := by
      calc M = Aᵀ⁻¹ * (Aᵀ * M * A.map (starRingEnd ℂ)) * (A.map (starRingEnd ℂ))⁻¹ := by
            rw [Matrix.mul_assoc Aᵀ, Matrix.nonsing_inv_mul_cancel_left _ _ hAt,
              Matrix.mul_nonsing_inv_cancel_right _ _ hAc]
        _ = 0 := by rw [hkey, Matrix.mul_zero, Matrix.zero_mul]
    rw [hsum, hM, Matrix.zero_mulVec, dotProduct_zero]

end GlobalTheory.SUChartSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffQuasiLogarithmMultiplicationDefect
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogDefect

theorem constantCoeff_defect : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ f : MvPowerSeries (Fin d) Q, QL μ ⊤ f → ∀ n : ℕ, constantCoeff (defect μ n f) = 0 := by
  intro p _ B O Q _ _ _ _ θ _ d μ hμ f hf n
  have hU : ∀ j, constantCoeff (up Q (nmul μ n) j) = 0 := by
    intro j
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_nmul hμ.const n j, map_zero]
  unfold defect
  rw [map_sub, constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hU) hU hf.1, sub_zero]
  simp [hf.1]

end GlobalTheory.QLogDefect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstOfForallConstantCoeffZeroStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_subst_of_forall_constantCoeff_zero : ∀ (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ R), (∀ i, constantCoeff (a i) = 0) → ∀ g : MvPowerSeries σ R, constantCoeff (subst a g) = constantCoeff g := by
  first | exact @GlobalTheory.constantCoeff_subst_of_constantCoeff_zero | exact GlobalTheory.constantCoeff_subst_of_constantCoeff_zero | (intros; apply GlobalTheory.constantCoeff_subst_of_constantCoeff_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtPsiOfNotMemZeroSetStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffAt_psi_chart_of_not_mem_zeroSet : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ y, y ∉ A.zeroSet s → ∀ i, y ∈ (A.chart i).source → ContDiffAt ℝ ∞ (psi A L s ∘ (A.chart i).symm) (A.chart i y) := by
  first | exact @GlobalTheory.OTY.contDiffAt_psi_of_notMem_zeroSet | exact GlobalTheory.OTY.contDiffAt_psi_of_notMem_zeroSet | (intros; apply GlobalTheory.OTY.contDiffAt_psi_of_notMem_zeroSet <;> assumption)
end

