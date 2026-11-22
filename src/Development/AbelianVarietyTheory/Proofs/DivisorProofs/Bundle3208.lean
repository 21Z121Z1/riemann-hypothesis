import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3174
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3175
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3166
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0745
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3161
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3133
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsNoethModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithFunctionFieldCharZeroTrdegStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projArith_functionField_charZero_trdeg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → CharZero X.functionField ∧ Algebra.trdeg ℤ X.functionField = D := by
  first | exact @GlobalTheory.ArithFnField.charZero_and_trdeg_functionField | exact GlobalTheory.ArithFnField.charZero_and_trdeg_functionField | (intros; apply GlobalTheory.ArithFnField.charZero_and_trdeg_functionField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithResidueCharFibreStructureStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projArith_residueCharFibre_structure : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → (∀ x : X, x ∈ fib X 0 ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ x ∈ fib X ℓ) ∧ (∀ ℓ : ℕ, ℓ ≠ 0 → IsClosed (fib X ℓ)) ∧ (∀ x y : X, x ⤳ y → y ∈ fib X 0 → x ∈ fib X 0) ∧ (∀ ℓ : ℕ, topologicalKrullDim (fib X ℓ) ≤ D) ∧ ∀ W : Set X, IsClosed W → ∃ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) ∧ W ⊆ closure (W ∩ fib X 0) ∪ ⋃ ℓ ∈ S, fib X ℓ := by
  first | exact @GlobalTheory.IntFib.fib_structure | exact GlobalTheory.IntFib.fib_structure | (intros; apply GlobalTheory.IntFib.fib_structure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceOrderArithVarietyFubiniStudyDegreStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ), IsArithVar (PSpace.str k D) D ∧ gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) ∧ Nat.card (k →+* ℂ) = Module.finrank ℤ k := by
  first | exact @GlobalTheory.PSpaceDeg.main | exact GlobalTheory.PSpaceDeg.main | (intros; apply GlobalTheory.PSpaceDeg.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiCoordinateNormChartEqCoordinateNormPadicDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiNormCoord

open Formalism.L2.Pj

variable {R : Type} [CommRing R] [IsDomain R]

theorem valF_eq {D : DegPre R} {χ : D.X} {r : R} (j : PUnit → D.P.L.ι)
    (h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j)
    (e : ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val) :
    valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) r := by
  unfold valF
  rw [dif_pos (by exact h)]
  have e1 : ∀ (h' : ⊤ ≤ 𝟙 (Sp (FractionRing R)) ⁻¹ᵁ (D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j),
      (Scheme.Hom.appLE (𝟙 (Sp (FractionRing R)))
        ((D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j) ⊤ h').hom ((D.psi χ).s j).val
      = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val := by
    intro h'
    rfl
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((e1 h).trans e.symm)).trans ?_
  have e2 : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    have : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op = 𝟙 _ := rfl
    simp only [DegPre.toOpen, RingHom.comp_apply, this, CategoryTheory.Functor.map_id]
    rfl
  rw [e2]
  have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have n' := congrArg (fun f => (f ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).hom r) n
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at n'
  exact n'.symm

theorem exists_unit_valF {D : DegPre R} {χ : D.X} {r : R} (hr : PsiCoord D χ r) (j : PUnit → D.P.L.ι)
    (hj : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit)) :
    ∃ u : Rˣ, valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) (u * r) := by
  obtain ⟨j₀, hj₀, h₀, e₀⟩ := hr
  have h := PsiCoordLocal.generic_le D χ j hj
  obtain ⟨u, hu⟩ := PsiCoordLocal.exists_trans D χ j j₀ hj hj₀ h h₀
  let φ := RingEquiv.ofBijective _ (PsiCoordLocal.toOpen_top_bijective (R := R))
  refine ⟨Units.map φ.symm.toMonoidHom u, valF_eq j h ?_⟩
  have k : DegPre.toOpen (R := R) ⊤ (Units.map φ.symm.toMonoidHom u : Rˣ) = u := φ.apply_symm_apply u.val
  rw [map_mul, map_mul, k, e₀]
  exact (congrArg Units.val hu).symm

theorem norm_unit {S C : Type} [CommRing S] [NormedField C] (f : S →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (u : Sˣ) :
    ‖f u‖ = 1 := by
  have h : ‖f u‖ * ‖f (u⁻¹ : Sˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm (hf _) ?_
  calc (1 : ℝ) = ‖f u‖ * ‖f (u⁻¹ : Sˣ)‖ := h.symm
    _ ≤ ‖f u‖ * 1 := mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)
    _ = _ := mul_one _

theorem main : ∀ (p : ℕ) [Fact p.Prime] (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra (FractionRing W) (PadicAlgCl p)], (∀ x : FractionRing W, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) → ∀ (D : DegData W (maximalIdeal W)) (y : D.toPre.X), (∃ r, Formalism.L2.Pj.PsiCoord D.toPre y r) ∧ ∀ r, Formalism.L2.Pj.PsiCoord D.toPre y r → ∀ t : ℝ, (GlobalTheory.UnifTorsK.PsiNormAt p D.toPre y t ↔ ‖algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ r)‖ = t) := by
  intro p _ W _ _ _ _ hball D y
  haveI : CharZero W :=
    ((algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W))).charZero
  have hf : ∀ a : W, ‖((algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W))) a‖ ≤ 1 :=
    fun a => (hball _).2 ⟨a, rfl⟩
  refine ⟨((GlobalTheory.PsiCoordLocal.main W D inferInstance y).1).imp fun r h => h.1, fun r hr t => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨j₀, hj₀, h₀, e₀⟩ := hr
    have := h j₀ hj₀
    rwa [valF_eq j₀ h₀ e₀] at this
  · intro j hj
    obtain ⟨u, hu⟩ := exists_unit_valF hr j hj
    rw [hu, map_mul, map_mul, norm_mul]
    have := norm_unit _ hf u
    simp only [RingHom.comp_apply] at this
    rw [this, _root_.one_mul, h]

end GlobalTheory.PsiNormCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiCoordinateNormInvariantDegDataPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UnifTorsK.psiNormAt_pull : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (r : ℝ), GlobalTheory.UnifTorsK.PsiNormAt p D (hD.xe χ) r ↔ GlobalTheory.UnifTorsK.PsiNormAt p D' χ r := by
  intro p _ V V' _ _ _ _ _ _ _ _ φ hφ hn D D' hD χ r
  have key := GlobalTheory.T.norm_psi_pull_localRingsOfIntegers p V V' φ hφ hn D D' hD χ
  refine ⟨fun H j' hj' => ?_, fun H j hj => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart D.P.isLB ((D.c (hD.xe χ)).left (IsLocalRing.closedPoint V))
    have hi' := ((IsLocalRing.closedPoint_mem_iff (R := V) ((D.c (hD.xe χ)).left ⁻¹ᵁ D.P.L.U i)).1 hi).ge
    exact (key i (j' PUnit.unit) hi' hj').trans (H (fun _ => i) hi')
  · obtain ⟨i, hi⟩ := exists_chart D'.P.isLB ((D'.c χ).left (IsLocalRing.closedPoint V'))
    have hi' := ((IsLocalRing.closedPoint_mem_iff (R := V') ((D'.c χ).left ⁻¹ᵁ D'.P.L.U i)).1 hi).ge
    exact (key (j PUnit.unit) i hj hi').symm.trans (H (fun _ => i) hi')
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackBaseFormFlagCellCoordinates
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2

theorem pullback_cell : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (α : (atlas X σ).Fld), (atlas X σ).IsForm α → ∀ x : (atlas Y σ).Pt, x.pt ∈ cellSet E E' φ f hf c A u → (atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α x = pull (fderiv ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd) (pull (bsL ε) ((atlas X σ).loc α c (bsL ε (cellMap ε f hf c u x.pt)))) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u n ε α hα x hx
  have hs : ptMap σ f hf x.pt ∈ ((atlas X σ).e c).source := hx.2
  rw [GlobalTheory.CxForm.pullback_eq_chart _ _ _ _ (atlas X σ) (atlas Y σ) (ptMap σ f hf) α (GlobalTheory.T.varietyComplexPointsMap_isHolomorphic F σ X Y f hf) hα x c hs]
  have hb : bsL ε (cellMap ε f hf c u x.pt) = c.e (ptMap σ f hf x.pt) := bsL_pt _ _ _
  have hloc : (atlas X σ).loc α c (c.e (ptMap σ f hf x.pt)) = α ⟨(c, ptMap σ f hf x.pt), hs⟩ :=
    (atlas X σ).loc_crd α ⟨(c, ptMap σ f hf x.pt), hs⟩
  rw [hb, hloc, ← GlobalTheory.T.pullbackComplexFormsLinearMap_comp_linear]
  congr 1
  have he : (atlas X σ).e c ∘ ptMap σ f hf ∘ x.ch.symm = bsL ε ∘ (cellMap ε f hf c u ∘ x.ch.symm) := by
    funext w
    simp only [Function.comp_apply, cellMap, bsL_pt]
    rfl
  have hd : DifferentiableAt ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd :=
    (GlobalTheory.T.flagCellCoordinates_contDiffAt_etaleChart F σ X Y ι m E E' φ f hf hR c A u n ε x hx).differentiableAt (by norm_num)
  rw [he, fderiv_comp x.crd (bsL ε).differentiableAt hd, ContinuousLinearMap.fderiv]

end GlobalTheory.FlagCell2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPolarizedLevelTripleOfSubringLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegBaseChange

open GlobalTheory.CechPic

theorem spMap_subtype_comp_inclusion {R : Type} [CommRing R] {R₁ R₂ : Subring R} (h : R₁ ≤ R₂) :
    spMap R₂.subtype ≫ spMap (Subring.inclusion h) = spMap R₁.subtype := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem pullbackTriple_of_le : ∀ (R : Type) [CommRing R] (R₁ R₂ : Subring R) (h : R₁ ≤ R₂) (g M : ℕ) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std g M → (𝟙_ (Over (Sp R)) ⟶ A)) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), IsAbelianScheme A₁ → SmoothOfRelativeDimension g A₁.hom → P.IsLB → P₁.IsLB → IsPullbackTriple A P lv A₁ P₁ lv₁ (spMap R₁.subtype) → ∃ (A₂ : Over (Sp R₂)) (_ : GrpObj A₂) (lv₂ : Std g M → (𝟙_ (Over (Sp R₂)) ⟶ A₂)) (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₂ ∧ SmoothOfRelativeDimension g A₂.hom ∧ IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π ∧ Geo.Tor.IsSquare π π₂ ∧ IsPullbackTriple A P lv A₂ (P₁.pull π₂) lv₂ (spMap R₂.subtype) := by
  intro R _ R₁ R₂ h g M A _ P lv A₁ _ P₁ lv₁ hab hsm hP hP₁ H
  haveI := hab.comm
  obtain ⟨φ, φ₂, hφ, s₁, s₂, iso, hl⟩ := H
  have e := spMap_subtype_comp_inclusion h
  have pb₂ := Pdiv.PullbackComparison.isGrpPullback (spMap (Subring.inclusion h)) A₁
  have sq₂ := Pdiv.PullbackComparison.isSquare (spMap (Subring.inclusion h)) A₁
  have hw : φ ≫ A₁.hom = (A.hom ≫ spMap R₂.subtype) ≫ spMap (Subring.inclusion h) := by
    rw [hφ.1.w, Category.assoc, e]
  let ψ : A.left ⟶ ((Over.pullback (spMap (Subring.inclusion h))).obj A₁).left := pb₂.1.lift φ _ hw
  have hψ₁ : ψ ≫ Pdiv.PullbackComparison.pφ (spMap (Subring.inclusion h)) A₁ = φ := pb₂.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ ((Over.pullback (spMap (Subring.inclusion h))).obj A₁).hom = A.hom ≫ spMap R₂.subtype :=
    pb₂.1.lift_snd _ _ _
  have hψ : IsGrpPullback A ((Over.pullback (spMap (Subring.inclusion h))).obj A₁) (spMap R₂.subtype) ψ :=
    pb₂.cancel (by rw [hψ₁, e]; exact hφ) hψ₂
  obtain ⟨ψ₂, sqψ⟩ := GlobalTheory.SiegDesc.exists_isSquare hψ₂
  have hc : ψ₂ ≫ Pdiv.PullbackComparison.pφ₂ (spMap (Subring.inclusion h)) A₁ = φ₂ :=
    GlobalTheory.SiegDesc.isSquare_comp hψ₁ sqψ sq₂ ⟨s₁, s₂⟩
  refine ⟨(Over.pullback (spMap (Subring.inclusion h))).obj A₁, inferInstance,
    fun a => GlobalTheory.SiegelPull.secPull pb₂ (lv₁ a), Pdiv.PullbackComparison.pφ _ A₁, Pdiv.PullbackComparison.pφ₂ _ A₁, ?_, ?_, pb₂, sq₂,
    ψ, ψ₂, hψ, sqψ.1, sqψ.2, ?_, fun a => ?_⟩
  · exact
      { comm := inferInstance
        smooth := by have := hab.smooth; show Smooth (pullback.snd _ _); infer_instance
        proper := by have := hab.proper; show IsProper (pullback.snd _ _); infer_instance
        geomConnected := by
          have := hab.geomConnected
          show GeometricallyConnected (pullback.snd _ _); infer_instance }
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback pb₂.1 hsm
  · have hP₂ := pull_isLB hP₁ (Pdiv.PullbackComparison.pφ₂ (spMap (Subring.inclusion h)) A₁)
    refine (cls_eq_iff hP (pull_isLB hP₂ ψ₂)).1 ?_
    rw [(cls_eq_iff hP (pull_isLB hP₁ φ₂)).2 iso, cls_pull hP₂ ψ₂, cls_pull hP₁ _ hP₂, ← pull_comp, hc]
    rfl
  · apply pb₂.1.hom_ext
    · rw [Category.assoc, hψ₁, hl a, Category.assoc, GlobalTheory.SiegelPull.secPull_left, ← Category.assoc, e]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (lv a), Category.assoc, Over.w]
      rfl

end GlobalTheory.SiegBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNormsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (u : SmFn p) (a b : ℤ), (upperParabolic P u).H a b = P.H a b ∧ (∀ f, NV (upperParabolic P u) a b f = NV P a b f) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), val (upperParabolic P u) a b σ y f = val P a b σ y f * (Real.exp (-(a * u.u σ y) / 2) : ℝ) ∧ (upperParabolic P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(a * u.u σ y) / 2) := by
  first | exact @GlobalTheory.HSAmp.upAtPrime_groups_values_norms | exact GlobalTheory.HSAmp.upAtPrime_groups_values_norms | (intros; apply GlobalTheory.HSAmp.upAtPrime_groups_values_norms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTorsionPointLiftSectionTorusExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalTorsionPoint_lift_section_torusExtension : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (N : ℕ), 1 ≤ N → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A) (p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N), xb.left = spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ x.left → p.y = 0 → QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb → ∃ (h : 𝟙_ (Over (Sp V)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp V)))), h ^ N = 1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors N g ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g ∧ IntTerm.Ext U.toUnifPre x h ∧ GtPt.IsPullF (AlgebraicClosure (FractionRing V)) (toUnit (TF (R := V) (AlgebraicClosure (FractionRing V)))).left g p.g := by
  first | exact @GlobalTheory.Poinc.TorsLift.lift | exact GlobalTheory.Poinc.TorsLift.lift | (intros; apply GlobalTheory.Poinc.TorsLift.lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionPropertiesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularNonvanishingLocusSection_properties : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (g : X.functionField), g ∈ P.H a b → IsOpen (NV P a b g) ∧ (genericPoint X ∈ NV P a b g ↔ g ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → NV P (n * a) (n * b) (g ^ n) = NV P a b g) ∧ (∀ f ∈ P.H a b, ∀ z ∈ NV P a b g, RegAt z (f / g) ∧ (z ∈ NV P a b f ↔ UnitAt z (f / g))) ∧ ∀ f ∈ P.H a b, ∀ (σ : k →+* ℂ) (y : CxPts p σ), under y ∈ NV P a b g → P.nu a b σ y f = ‖ratVal (f / g) y‖ * P.nu a b σ y g ∧ 0 < P.nu a b σ y g := by
  first | exact @GlobalTheory.HSAmp.nv_rules | exact GlobalTheory.HSAmp.nv_rules | (intros; apply GlobalTheory.HSAmp.nv_rules <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalBundleDescendsSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleDiagSubring

theorem relAmple_diag_subring : ∀ (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsAbelianScheme A₁ → P.IsLB → P₁.IsLB → IsGrpPullback A A₁ (spMap R₁.subtype) φ → Geo.Tor.IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → Out.RelAmple A (diagPull A P) → ∃ F : Finset R, ∀ (R₂ : Subring R) (h : R₁ ≤ R₂), (F : Set R) ⊆ R₂ → ∀ (A₂ : Over (Sp R₂)) [GrpObj A₂] (π : A₂.left ⟶ A₁.left) (π₂ : (A₂ ⊗ A₂).left ⟶ (A₁ ⊗ A₁).left), IsGrpPullback A₂ A₁ (spMap (Subring.inclusion h)) π → Geo.Tor.IsSquare π π₂ → Out.RelAmple A₂ (diagPull A₂ (P₁.pull π₂)) := by
  intro R _ R₁ _ A _ P A₁ _ P₁ φ φ₂ hA₁ hP hP₁ hφ sq e hamp
  classical
  have := hA₁.proper
  have := hA₁.smooth
  let M : LB A₁.left := diagPull A₁ P₁
  have hM : M.IsLB := pull_isLB hP₁ _
  have hL : (diagPull A P).IsLB := pull_isLB hP _
  have e' : LBIso (diagPull A P) (M.pull φ) := GlobalTheory.SiegelPull.diag_iso sq e
  have hspan := GlobalTheory.CompanionTheory.PolSpread.span_good R₁.subtype A A₁ hM hL hφ.1 e' hamp
  have h1 : (1 : R) ∈ Ideal.span (R₁.subtype '' GlobalTheory.CompanionTheory.PolSpread.good A₁ M) := by rw [hspan]; trivial
  obtain ⟨c, hc, hs⟩ := Submodule.mem_span_set.1 h1
  choose! t ht hty using fun y (hy : y ∈ c.support) => hc hy
  refine ⟨c.support.image c, fun R₂ h hF A₂ _ π π₂ hπ sq₂ => ?_⟩
  let τ : R₁ →+* R₂ := Subring.inclusion h
  have hmem : ∀ y ∈ c.support, c y ∈ R₂ := fun y hy =>
    hF (Finset.mem_coe.2 (Finset.mem_image_of_mem c hy))
  have hT : Ideal.span (τ '' (t '' (c.support : Set R))) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have e1 : (1 : R₂) = ∑ y ∈ c.support.attach, (⟨c y.1, hmem y.1 y.2⟩ : R₂) * τ (t y.1) := by
      apply Subtype.ext
      refine (OneMemClass.coe_one R₂).trans (hs.symm.trans ?_)
      rw [Finsupp.sum, ← Finset.sum_attach]
      simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, smul_eq_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      have : ((τ (t y.1) : R₂) : R) = y.1 := hty y.1 y.2
      rw [this]
    rw [e1]
    exact Ideal.sum_mem _ fun y _ => Ideal.mul_mem_left _ _
      (Ideal.subset_span ⟨t y.1, ⟨y.1, y.2, rfl⟩, rfl⟩)
  have hB := GlobalTheory.CompanionTheory.PolSpread.relAmple_of_span τ A₁ hM _
    (by rintro _ ⟨y, hy, rfl⟩; exact ht y hy) hT
  have hπ' : Out.RelAmple (Over.mk A₂.hom) (M.pull π) :=
    GlobalTheory.FibreAmple.relAmple_of_factor hM (IsPullback.of_hasPullback A₁.hom (spMap τ)) hπ.1 (𝟙 _)
      (Category.id_comp _) (pull_isLB hM _) (GlobalTheory.lbIso_refl (pull_isLB hM _)) hB
  have : IsProper (Over.mk A₂.hom).hom := MorphismProperty.of_isPullback (P := @IsProper) hπ.1 ‹_›
  have hMπ : (M.pull π).IsLB := pull_isLB hM π
  have hL₂ : (diagPull A₂ (P₁.pull π₂)).IsLB := pull_isLB (pull_isLB hP₁ π₂) _
  have e₂ : LBIso (diagPull A₂ (P₁.pull π₂)) (M.pull π) :=
    GlobalTheory.SiegelPull.diag_iso sq₂ (GlobalTheory.lbIso_refl (pull_isLB hP₁ π₂))
  have e₃ : LBIso (M.pull π) ((M.pull π).pull (𝟙 _)) :=
    GlobalTheory.FibreAmple.lbIso_pull_comp (Category.id_comp π).symm (GlobalTheory.lbIso_refl hMπ)
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull (A := Over.mk A₂.hom) (A' := A₂) (f := 𝟙 _) (φ := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) hMπ hL₂
    (LBIso.trans hL₂ hMπ (pull_isLB hMπ _) e₂ e₃) hπ'

end GlobalTheory.AmpleDiagSubring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointEqFinrankQuotientsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueDegree_genericPoint_eq_finrank_quotients : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) [IsIntegral (PSpace k D)] (π : X ⟶ PSpace k D), π ≫ PSpace.str k D = p → ∀ x : Fin (D + 1) → X.functionField, x 0 ≠ 0 → (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) → π (genericPoint X) = genericPoint (PSpace k D) → π.residueDegree (genericPoint X) = Module.finrank (Subfield.closure (Set.range (GlobalTheory.toFunctionField p) ∪ Set.range fun j : Fin D => x j.succ / x 0)) X.functionField := by
  first | exact @GlobalTheory.GenericResidueDegree.residueDegree_eq_finrank_quotients | exact GlobalTheory.GenericResidueDegree.residueDegree_eq_finrank_quotients | (intros; apply GlobalTheory.GenericResidueDegree.residueDegree_eq_finrank_quotients <;> assumption)
end

