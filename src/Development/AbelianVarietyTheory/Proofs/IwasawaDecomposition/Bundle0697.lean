import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0679
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0591
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellAtlasFromLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0680
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbelianPartSectionSqEqOfThickeningPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_section_sq_eq_of_thickening_points : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ (α : D.toPre.X) (α' : D'.toPre.X), (∀ κ, D'.toPre.famφB α' κ ≫ Φ.hom.left = Φ.hom.left ≫ D.toPre.famφB α κ) → ∀ (s : D.toPre.SecB 2 α) (s' : D'.toPre.SecB 2 α'), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (r ≫ (U.gt e).pG.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' (r ≫ (U'.gt e).pG.left) z J' ^ 2) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' ρ z J' ^ 2 := by
  first | exact @GlobalTheory.sq_corr_of_thickenings | exact GlobalTheory.sq_corr_of_thickenings | (intros; apply GlobalTheory.sq_corr_of_thickenings <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcLieBasisExponentialCoordsHasSumStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_lieBasis_exponentialCoords_hasSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (M : GChart Y) (hM : ⊤ ≤ χ ⁻¹ᵁ M.U) (e : Fin g → Out.GtPt a.D₀ (epsR ℂ)) (v : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (z : Fin g → Fin g → ℂ) (hn : M.n = g) (v' : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → (∀ k, GlobalTheory.ArcQ.LieImg W (e k) (v k) ∧ GlobalTheory.ArcQ.AnVec Ha (e k) (z k)) → IsLieBasis v → (Matrix.of z).det ≠ 0 → (∀ i, (v' i).left ≫ W.m.φ = spMap (dualMap (ev χ M.U hM)) ≫ M.v₀ (Fin.cast hn.symm i)) → (∀ i, IsLieComb (A i) v (v' i)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → ∀ i, (∀ k, Summable (fun m : ℕ => PowerSeries.coeff m (A i k) * eTwoPi w ^ m)) ∧ ∀ j, Wv (Fin.cast hg.symm i) j = ∑ k, (∑' m : ℕ, PowerSeries.coeff m (A i k) * eTwoPi w ^ m) * z k j := by
  first | exact @GlobalTheory.ArcLieCoord.lie_coords_hasSum | exact GlobalTheory.ArcLieCoord.lie_coords_hasSum | (intros; apply GlobalTheory.ArcLieCoord.lie_coords_hasSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedPsdRationalRadicalConeSubsetIntConeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balancedPsdRationalRadicalCone_subset_intCone : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] [Module.Free ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X], psdCone bar X ⊆ psdCone (id : ℤ → ℤ) X := by
  first | exact @GlobalTheory.PolFan.psdCone_subset_psdCone_int | exact GlobalTheory.PolFan.psdCone_subset_psdCone_int | (intros; apply GlobalTheory.PolFan.psdCone_subset_psdCone_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFrameTriangularThroughStalkFrames
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions
  Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.GoodMetric GlobalTheory.LieBase

namespace GlobalTheory.ShFam.CarriesAt

theorem diag_mul_of_blockTriangular {R : Type} [CommRing R] {n : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA h, zero_mul]
  · rw [hB h, mul_zero]

theorem isUnit_diag_of_blockTriangular {R : Type} [CommRing R] {n : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : A.BlockTriangular id) (hd : IsUnit A.det) (i : Fin n) : IsUnit (A i i) := by
  rw [Matrix.det_of_upperTriangular hA] at hd
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => A j j) (Finset.mem_univ i)) hd

theorem tri_of_carries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (k : Type) [Field k] (φ : c.F →+* k) (x : Sp k ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp k ⟶ C.Y.X), C.Carries p g → ∀ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y) (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), p = spMap ψ ≫ stalkPt C.Y y → f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t → ∃ t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri ψ g t' := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C k _ φ x g p hC y ψ φ₁ f t hp hf
  obtain ⟨y₁, ψ₁, φ₂, f₁, t₁, t₁', hp₁, hf₁, hg₁⟩ := hC

  have hsp : p (IsLocalRing.closedPoint k) ⤳ y := by
    have : p (IsLocalRing.closedPoint k) ∈ Set.range (C.Y.X.fromSpecStalk y) := by
      rw [hp]
      exact ⟨spMap ψ (IsLocalRing.closedPoint k), rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hsp₁ : p (IsLocalRing.closedPoint k) ⤳ y₁ := by
    have : p (IsLocalRing.closedPoint k) ∈ Set.range (C.Y.X.fromSpecStalk y₁) := by
      rw [hp₁]
      exact ⟨spMap ψ₁ (IsLocalRing.closedPoint k), rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hψ : ψ = (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)
    have e1 := spMap_stalkClosedPointTo p
    have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ C.Y.X.fromSpecStalk y = C.Y.X.fromSpecStalk _ :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
    have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom) =
        spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom ≫ spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
      simp [spMap, Spec.map_comp]
    rw [e3, Category.assoc, e2, e1]
    exact hp.symm
  have hψ₁ : ψ₁ = (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp₁).hom := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y₁)).1 ?_)
    have e1 := spMap_stalkClosedPointTo p
    have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp₁).hom ≫ C.Y.X.fromSpecStalk y₁ = C.Y.X.fromSpecStalk _ :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp₁
    have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp₁).hom) =
        spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom ≫ spMap (C.Y.X.presheaf.stalkSpecializes hsp₁).hom := by
      simp [spMap, Spec.map_comp]
    rw [e3, Category.assoc, e2, e1]
    exact hp₁.symm
  set ψp := (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom with hψpdef
  set ρ := (C.Y.X.presheaf.stalkSpecializes hsp).hom with hρdef
  set ρ₁ := (C.Y.X.presheaf.stalkSpecializes hsp₁).hom with hρ₁def
  set alg := algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint k))) C.Y.X.functionField with halgdef
  have hinj : Function.Injective alg := IsFractionRing.injective _ _
  have halg : algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField = alg.comp ρ := algebraMap_eq_comp_specializes hsp
  have halg₁ : algebraMap (C.Y.X.presheaf.stalk y₁) C.Y.X.functionField = alg.comp ρ₁ :=
    algebraMap_eq_comp_specializes hsp₁
  have hxp : spMap ρ ≫ stalkPt C.Y y = stalkPt C.Y (p (IsLocalRing.closedPoint k)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hxp₁ : spMap ρ₁ ≫ stalkPt C.Y y₁ = stalkPt C.Y (p (IsLocalRing.closedPoint k)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp₁
  have hpp : spMap ψp ≫ stalkPt C.Y (p (IsLocalRing.closedPoint k)) = p := spMap_stalkClosedPointTo p

  have c1 : alg.comp (ρ.comp φ₁) = constF e C.Y := by rw [← RingHom.comp_assoc, ← halg, hf.2.1]
  have c2 : alg.comp (ρ₁.comp φ₂) = constF e C.Y := by rw [← RingHom.comp_assoc, ← halg₁, hf₁.2.1]
  have hρφ : ρ₁.comp φ₂ = ρ.comp φ₁ := RingHom.ext fun a => hinj
    ((RingHom.congr_fun c2 a).trans (RingHom.congr_fun c1 a).symm)
  have hgen : genericPt C.Y ≫ C.π ≫ genι Z = spMap alg ≫ stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z := by
    rw [hf.1, halg, ← hxp]
    simp [spMap, Spec.map_comp]
  have hx0 : x = p ≫ C.π ≫ genι Z := by rw [hg₁.1, hp₁, Category.assoc]
  have hxk : x = spMap ψp ≫ stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z := by
    rw [hx0, ← Category.assoc (spMap ψp), hpp]
  have hxψ : x = spMap ψ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z := by
    rw [hx0, hp, Category.assoc]
  have hφk : φ = ψ.comp φ₁ := by
    rw [hg₁.2.1, hψ₁, hψ, RingHom.comp_assoc, RingHom.comp_assoc, hρφ]

  obtain ⟨f', hf'⟩ := f.exists_isMap (x' := stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z) ρ rfl
    (by rw [← hxp, Category.assoc])
  obtain ⟨f₁', hf₁'⟩ := f₁.exists_isMap (x' := stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z) ρ₁ hρφ.symm
    (by rw [← hxp₁, Category.assoc])
  obtain ⟨fF, hfF⟩ := f'.exists_isMap alg c1.symm hgen
  obtain ⟨f₁F, hf₁F⟩ := f₁'.exists_isMap alg c1.symm hgen
  obtain ⟨fk, hfk⟩ := f.exists_isMap ψ hφk hxψ
  obtain ⟨f₁k, hf₁k⟩ := f₁.exists_isMap ψ₁ hg₁.2.1 hg₁.1
  have iF : f.IsMap (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) fF := fun τ i => by
    rw [hfF τ i, hf' τ i, ← Category.assoc (spMap (dualMap alg)), ← spMap_dualMap_comp, ← halg]
  have i₁F : f₁.IsMap (algebraMap (C.Y.X.presheaf.stalk y₁) C.Y.X.functionField) f₁F := fun τ i => by
    rw [hf₁F τ i, hf₁' τ i, ← Category.assoc (spMap (dualMap alg)), ← spMap_dualMap_comp, ← halg₁]
  have ik : f'.IsMap ψp fk := fun τ i => by
    rw [hfk τ i, hf' τ i, ← Category.assoc (spMap (dualMap ψp)), ← spMap_dualMap_comp, ← hψ]
  have i₁k : f₁'.IsMap ψp f₁k := fun τ i => by
    rw [hf₁k τ i, hf₁' τ i, ← Category.assoc (spMap (dualMap ψp)), ← spMap_dualMap_comp, ← hψ₁]

  have key : ∀ τ, (fk.co g τ).BlockTriangular id ∧ ∀ i, IsUnit (fk.co g τ i i) := by
    intro τ
    have hU := EigFrame.Tri.co (τ := τ) hf iF
    have hU₁ := EigFrame.Tri.co (τ := τ) hf₁ i₁F
    have hU₁t : (f₁F.co C.f0 τ).BlockTriangular id := fun a i h => hU₁.1 a i h
    have hU₁d : IsUnit (f₁F.co C.f0 τ).det := f₁F.isUnit_det_co C.f0 τ
    have hW : fF.co f₁F τ = fF.co C.f0 τ * (f₁F.co C.f0 τ)⁻¹ := by
      rw [← fF.co_mul f₁F C.f0 τ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU₁d, Matrix.mul_one]
    have hWt : (fF.co f₁F τ).BlockTriangular id := by
      haveI := Matrix.invertibleOfIsUnitDet _ hU₁d
      rw [hW]
      exact Matrix.BlockTriangular.mul (fun a i h => hU.1 a i h) (Matrix.blockTriangular_inv_of_blockTriangular hU₁t)
    have hM : fF.co f₁F τ = (f'.co f₁' τ).map alg := EigFrame.IsMap.co τ hfF hf₁F hgen
    have hMt : (f'.co f₁' τ).BlockTriangular id := fun a i h => hinj (by
      have := hWt h
      rw [hM, Matrix.map_apply] at this
      rw [this, map_zero])
    have hMu : ∀ i, IsUnit (f'.co f₁' τ i i) := isUnit_diag_of_blockTriangular hMt (f'.isUnit_det_co f₁' τ)
    have hN := EigFrame.Tri.co (τ := τ) hg₁ hf₁k
    have hNt : (f₁k.co g τ).BlockTriangular id := fun a i h => hN.1 a i h
    have hMk : fk.co f₁k τ = (f'.co f₁' τ).map ψp := EigFrame.IsMap.co τ ik i₁k hxk
    have hMkt : (fk.co f₁k τ).BlockTriangular id := fun a i h => by
      rw [hMk, Matrix.map_apply, hMt h, map_zero]
    have hQ : fk.co g τ = fk.co f₁k τ * f₁k.co g τ := (fk.co_mul f₁k g τ).symm
    refine ⟨hQ ▸ hMkt.mul hNt, fun i => ?_⟩
    rw [hQ, diag_mul_of_blockTriangular hMkt hNt, hMk, Matrix.map_apply, hN.2 i]
    exact ((hMu i).map ψp).mul (Units.isUnit _)
  refine ⟨fun τ i => ((key τ).2 i).unit, hxψ, hφk, fun τ i => ⟨fun a => fk.co g τ a i, ((key τ).2 i).unit_spec.symm,
    fun a ha => (key τ).1 ha, ?_⟩⟩
  rw [← funext (hfk τ)]
  exact fk.co_spec g τ i

end GlobalTheory.ShFam.CarriesAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimLeOfAddCellGenerators
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

theorem carrierDim_le_of_add_cell : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ lab : InvFun O), IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (b : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β₀ → ∀ (c₀ : ℝ) (c : Fin b → ℝ), 0 < c₀ → (∀ k, 0 ≤ c k) → toReal β = c₀ • toReal β₀ + ∑ k, c k • toReal (v k) → lab.evalZ β₀ ≤ lab.evalZ β := by
  intro O _ bar q ψ lab hlab X _ _ _ _ hX b v hv β₀ hβ₀ hp₀ β hβ hp hin c₀ c hc₀ hc hrel
  obtain ⟨e, he, he'⟩ := hin
  have hw : ∀ k, 0 ≤ c₀ * e k + c k := fun k => add_nonneg (mul_nonneg hc₀.le (he k)) (hc k)
  have hcomb : toReal β = ∑ k, (c₀ * e k + c k) • toReal (v k) := by
    rw [hrel, he', Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, add_smul]
  have hβv : InRCone v β := ⟨_, hw, hcomb⟩
  have hne : ({k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k}).Nonempty := ⟨_, b, v, hv, hβv, rfl⟩
  obtain ⟨m, τ, hτ, hβτ, hrank⟩ := Nat.sInf_mem hne
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hτ.strict
  have hψτ : ((ℓ β : ℤ) : ℝ) = N * ψ.evalZ β := by
    obtain ⟨d, hd, hde⟩ := hβτ
    rw [apply_eq_of_toReal_eq hde ℓ]
    have A := (linearOn_iff ψ τ).1 hτ.linear d hd
    rw [← hde, evalR_toReal] at A
    rw [A, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [h1 i]; ring
  have hψv : ψ.evalZ β = c₀ * ψ.evalZ β₀ + ∑ k, c k * ψ.evalZ (v k) := by
    have A := (linearOn_iff ψ v).1 hv.linear _ hw
    rw [← hcomb, evalR_toReal] at A
    have B := (linearOn_iff ψ v).1 hv.linear e he
    rw [← he', evalR_toReal] at B
    rw [A, B, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hℓv : ((ℓ β : ℤ) : ℝ) = c₀ * ℓ β₀ + ∑ k, c k * ℓ (v k) := by
    rw [apply_eq_of_toReal_eq hcomb ℓ, apply_eq_of_toReal_eq he' ℓ, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hk : ∀ k, (N : ℝ) * ψ.evalZ (v k) ≤ ℓ (v k) := fun k => h2 _ (hv.mem k) (hv.nonneg k)
  have h0 : (N : ℝ) * ψ.evalZ β₀ ≤ ℓ β₀ := h2 _ hβ₀ hp₀
  have heq : (N : ℝ) * ψ.evalZ β₀ = ℓ β₀ := by
    have hsum : ∑ k, c k * (N * ψ.evalZ (v k)) ≤ ∑ k, c k * (ℓ (v k) : ℝ) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk k) (hc k)
    have E : c₀ * (ℓ β₀ : ℝ) + ∑ k, c k * (ℓ (v k) : ℝ) = c₀ * (N * ψ.evalZ β₀) + ∑ k, c k * (N * ψ.evalZ (v k)) := by
      rw [← hℓv, hψτ, hψv, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun k _ => by ring
    by_contra hne'
    have hlt : (N : ℝ) * ψ.evalZ β₀ < ℓ β₀ := lt_of_le_of_ne h0 hne'
    have := mul_lt_mul_of_pos_left hlt hc₀
    linarith
  obtain ⟨kk, d, hkk, hd⟩ := h3 β₀ hβ₀ hp₀ heq
  have hβ₀τ : InRCone τ β₀ := by
    refine ⟨fun i => (d i : ℝ) / kk, fun i => by positivity, LinearMap.ext₂ fun a b' => ?_⟩
    have h := LinearMap.congr_fun₂ hd a b'
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h
    have hR : (kk : ℝ) * (β₀ a b' : ℝ) = ∑ i, (d i : ℝ) * (τ i a b' : ℝ) := by exact_mod_cast h
    have hkR : (kk : ℝ) ≠ 0 := by positivity
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    calc (β₀ a b' : ℝ) = ((kk : ℝ) * (β₀ a b' : ℝ)) / kk := by field_simp
      _ = _ := by rw [hR, Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  have hle := Nat.sInf_le (s := {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
      InRCone γ β₀ ∧ genRank γ = k}) ⟨m, τ, hτ, hβ₀τ, rfl⟩
  rw [hlab X hX β hβ hp, hlab X hX β₀ hβ₀ hp₀]
  exact_mod_cast hle.trans hrank.le

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierMatrixTransfer
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl.IntPt

section Lin

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem span_cols {n k : ℕ} (hk : k ≤ n) (a a' : Matrix (Fin n) (Fin n) R) (h2 : a' * a = 1)
    (ξ : Fin k → Fin n → K) (hξ : LinearIndependent K ξ)
    (h0 : ∀ (l : Fin k) (j : Fin n), k ≤ (j : ℕ) → ∑ i, algebraMap R K (a j i) * ξ l i = 0) :
    LinearIndependent K (fun (l : Fin k) => algebraMap R K ∘ fun i => a' i (Fin.castLE hk l)) ∧
      Submodule.span K (Set.range fun (l : Fin k) => algebraMap R K ∘ fun i => a' i (Fin.castLE hk l)) =
        Submodule.span K (Set.range ξ) := by
  set φ := algebraMap R K with hφ
  set c : Fin k → Fin n → K := fun l => φ ∘ fun i => a' i (Fin.castLE hk l) with hc
  have hmap : a'.map φ * a.map φ = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hmem : ∀ l, ξ l ∈ Submodule.span K (Set.range c) := fun l => by
    have e : ξ l = ∑ j : Fin n, (∑ i, φ (a j i) * ξ l i) • (fun r => φ (a' r j)) := by
      have := Matrix.mulVec_mulVec (ξ l) (a'.map φ) (a.map φ)
      rw [hmap, Matrix.one_mulVec] at this
      refine this.symm.trans ?_
      funext r
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : k ≤ (j : ℕ)
    · rw [h0 l j hj, zero_smul]
      exact Submodule.zero_mem _
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, not_le.1 hj⟩, ?_⟩)
      rfl
  have hle : Submodule.span K (Set.range ξ) ≤ Submodule.span K (Set.range c) :=
    Submodule.span_le.2 (Set.range_subset_iff.2 hmem)
  have hf : Module.finrank K (Submodule.span K (Set.range ξ)) = k := by
    simpa using finrank_span_eq_card hξ
  have hc' : Module.finrank K (Submodule.span K (Set.range c)) ≤ k := by
    simpa [Set.finrank] using finrank_range_le_card (R := K) c
  have heq : Submodule.span K (Set.range ξ) = Submodule.span K (Set.range c) :=
    Submodule.eq_of_le_of_finrank_le hle (hc'.trans hf.ge)
  refine ⟨linearIndependent_iff_card_eq_finrank_span.2 ?_, heq.symm⟩
  rw [Set.finrank, ← heq, hf]
  simp

theorem unimod {M k n : ℕ} (hk : k ≤ n) (A : Matrix (Fin (M + 1)) (Fin n) R) (A' : Matrix (Fin n) (Fin (M + 1)) R)
    (hA : A' * A = 1) (a a' : Matrix (Fin n) (Fin n) R) (h1 : a * a' = 1) :
    Ideal.span (Set.range (plk (fun l : Fin k => A.mulVec fun i => a' i (Fin.castLE hk l)) id)) = ⊤ := by
  have h := GlobalTheory.FlagEmb.CauchyBinet.lform_plk R M k (Fin k) (Fin n) (fun j r => (a * A') j r)
    (fun l : Fin k => A.mulVec fun i => a' i (Fin.castLE hk l)) (Fin.castLE hk) id
  have hm : (Matrix.of fun l l' : Fin k => ∑ r, (a * A') (Fin.castLE hk l') r *
      (A.mulVec fun i => a' i (Fin.castLE hk (id l))) r) = 1 := by
    ext l l'
    have e : ∑ r, (a * A') (Fin.castLE hk l') r * (A.mulVec fun i => a' i (Fin.castLE hk (id l))) r =
        (a * a') (Fin.castLE hk l') (Fin.castLE hk l) := by
      have : (a * A').mulVec (A.mulVec fun i => a' i (Fin.castLE hk (id l))) =
          a.mulVec fun i => a' i (Fin.castLE hk (id l)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hA, Matrix.mul_one]
      exact congrFun this (Fin.castLE hk l')
    rw [Matrix.of_apply, e, h1, Matrix.one_apply, Matrix.one_apply]
    by_cases hl : l = l'
    · simp [hl]
    · rw [if_neg (fun e => hl (Fin.castLE_injective hk e).symm), if_neg hl]
  rw [hm, Matrix.det_one] at h
  rw [Ideal.eq_top_iff_one, ← h]
  exact Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)

end Lin

theorem main : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (s : Z ⟶ Sp O) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)), q ≫ PSpace.str O _ = f ≫ s → ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (z : Sp R ⟶ Z) (α : C.A) (_ : ⊤ ≤ z ⁻¹ᵁ C.B α) (n' : ℕ) (a : Matrix (Fin n') (Fin (C.n α)) R) (a' : Matrix (Fin (C.n α)) (Fin n') R) (y : Sp K ⟶ Z') (hy : ⊤ ≤ (y ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin k → Fin (C.n α) → K), a * a' = 1 → a' * a = 1 → y ≫ f = spMap (algebraMap R K) ≫ z → Car Em f q y α hy ξ → (∀ (l : Fin k) (j : Fin n'), k ≤ (j : ℕ) → ∑ i, algebraMap R K (a j i) * ξ l i = 0) → ∃ y₀ : Sp R ⟶ PSpace O (plN N k), y₀ ≫ PSpace.str O _ = z ≫ s ∧ y ≫ q = spMap (algebraMap R K) ≫ y₀ := by
  intro O _ Z Z' s C N k Em f q hq R K _ _ _ z α hz n' a a' y hy ξ h1 h2 hyz hcar h0
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  obtain rfl : n' = C.n α := by simpa using Matrix.square_of_invertible a a' h1 h2
  obtain ⟨hli, hiff, -⟩ := GlobalTheory.T.carrier_independent_span_iff O Z Z' C N k Em f q K y α hy ξ hcar
  have hk : k ≤ C.n α := by simpa using hli.fintype_card_le_finrank
  obtain ⟨l1, l2⟩ := span_cols hk a a' h2 ξ hli h0
  obtain ⟨g, hv, e⟩ := (hiff _).2 ⟨l1, l2⟩
  obtain ⟨A', hA'⟩ := Em.linv α
  set φ := algebraMap R K with hφ
  let g₀ : O →+* R := (Spec.preimage (z ≫ s)).hom
  have hg₀ : spMap g₀ = z ≫ s := Spec.map_preimage (z ≫ s)
  have hAz : A'.map (ev z _ hz) * (Em.A α).map (ev z _ hz) = 1 := by
    rw [← Matrix.map_mul, hA', Matrix.map_one _ (map_zero _) (map_one _)]
  have hu := unimod hk _ _ hAz a a' h1
  refine ⟨pt g₀ _ hu, by rw [GlobalTheory.ProjSpace.pt_str, hg₀], ?_⟩
  have hg : g = φ.comp g₀ := by
    have h5 : spMap (φ.comp g₀) = spMap φ ≫ spMap g₀ := by
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    have h3 : spMap g = spMap (φ.comp g₀) := by
      have h4 := congrArg (· ≫ PSpace.str O _) e
      simp only [Category.assoc, GlobalTheory.ProjSpace.pt_str, hq] at h4
      rw [← h4, ← Category.assoc, hyz, Category.assoc, h5, hg₀]
    exact congrArg (·.hom) (Spec.map_injective h3)
  have hev : ev (y ≫ f) _ hy = φ.comp (ev z _ hz) :=
    (GlobalTheory.FlagMod.ev_congr hyz _ hy (hyz ▸ hy)).trans (GlobalTheory.FlagMod.ev_spMap φ z _ hz _)
  have hp : plk (fun l : Fin k => ((Em.A α).map (ev (y ≫ f) _ hy)).mulVec (φ ∘ fun i => a' i (Fin.castLE hk l))) id =
      φ ∘ plk (fun l : Fin k => ((Em.A α).map (ev z _ hz)).mulVec fun i => a' i (Fin.castLE hk l)) id := by
    rw [GlobalTheory.FlagEmb.map_plk]
    congr 1
    funext l
    funext r
    have hm : (Em.A α).map (φ.comp (ev z _ hz)) = ((Em.A α).map (ev z _ hz)).map φ := by
      rw [Matrix.map_map]
      rfl
    rw [hev, hm]
    exact (RingHom.map_mulVec φ ((Em.A α).map (ev z _ hz)) _ r).symm
  have hpt : ∀ (c : O →+* K) (v w : Fin (plN N k + 1) → K) (hv : Ideal.span (Set.range v) = ⊤)
      (hw : Ideal.span (Set.range w) = ⊤), v = w → pt c v hv = pt c w hw := by
    rintro c v w hv hw rfl
    rfl
  rw [e, GlobalTheory.ProjSpace.spMap_pt]
  subst hg
  exact hpt _ _ _ _ _ hp

end GlobalTheory.GrCl.IntPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellAtlasFromLatticeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_atlas_from_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (D : LCrd M π) (σ : E →+* ℂ) (α : A.ch.ι → D.C.A) (cv Dv : ∀ a, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a) (a k b : ℕ) (hk : k ≤ Dw.mult σ) (X' : Scheme.{0}) (f : X' ⟶ X) (q : X' ⟶ PSpace V (plN D.N k)) (κ : ∀ j : A.ch.ι, GPm (Dw.mult σ) a b → (Sp (MvPolynomial (GVar (Dw.mult σ) a k b) (A.ch.R j)) ⟶ X')) (ty' : (E →+* ℂ) → Finset ℕ), a ≤ k → k ≤ b → (a ∈ ty σ ∨ a = 0) → (b ∈ ty σ ∨ b = Dw.mult σ) → (∀ e ∈ ty σ, e ≤ a ∨ b ≤ e) → (∀ j, ⊤ ≤ A.ch.χ j ⁻¹ᵁ D.C.B (α j)) → IsFrVec D A σ α cv → (∀ j, LeftInv (Dv j) (cv j)) → CellCl (π ≫ M.s) A.ch (fun j => (A.alg j).comp V.subtype) (fun j => gxi a b hk (cv j)) f q κ → ty' σ = insert k (ty σ) → (∀ σ', σ' ≠ σ → ty' σ' = ty σ') → ∃ A' : Atlas M (f ≫ π) ty', GRel D A σ hk f q A' := by
  first | exact @GlobalTheory.GrCl.CellAtlas.exists_cellAtlas | exact GlobalTheory.GrCl.CellAtlas.exists_cellAtlas | (intros; apply GlobalTheory.GrCl.CellAtlas.exists_cellAtlas <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellGeneratorOnRayOfLinIndepSubcellStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cellGenerator_on_ray_of_linIndep_subcell : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m n : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (c : Fin n → ℝ), IsCell bar φ δ → IsCell bar φ γ → LinearIndependent ℤ δ → (∀ j, 0 ≤ c j) → ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ j) → ∀ i, ∃ (j : Fin n) (a b : ℕ), 0 < a ∧ 0 < b ∧ a • δ i = b • γ j := by
  first | exact @GlobalTheory.PolFan.cell_gen_on_ray | exact GlobalTheory.PolFan.cell_gen_on_ray | (intros; apply GlobalTheory.PolFan.cell_gen_on_ray <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnIntegralTransvections
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem killsTransv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N),
    1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (ξ : Fin N → E) (s : E),
    ξ ∈ X.Λ → herm X.Gm ξ ξ = 0 → cc s = s → IsIntegral ℤ s → ∀ γ : X.Γ,
    ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm ξ (X.m * s * X.κ0) →
    φ γ = 1 := by
  intro E _ _ _ N X hE φ ξ s hξ hiso hs hsint γ hγ
  by_cases h0 : ξ = 0
  · subst h0
    have h1 : ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = 1 := by
      rw [hγ]; ext a b; simp [transvMat, Matrix.one_apply]
    have : γ = 1 := by
      apply Subtype.ext; apply Units.ext; simpa using h1
    rw [this, map_one]
  obtain ⟨u, hu0, hureal, hkill⟩ := GlobalTheory.T.character_trivial_on_unit_transvections E N X hE φ ξ hξ h0 hiso
  obtain ⟨c, hc0, u', hu'⟩ := GlobalTheory.T.exists_int_multiple_of_integer E u hu0
  have hcE : (c : E) = (u : E) * (u' : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) hu'
    simpa using this
  have huE : (u : E) ≠ 0 := by
    intro h; exact hu0 (RingOfIntegers.coe_eq_zero_iff.mp h)
  have hu'real : cc (u' : E) = u' := by
    have e : (u' : E) = (c : E) * (u : E)⁻¹ := by
      rw [hcE]; field_simp
    rw [e, cc_mul, cc_inv, cc_intCast, hureal]
  have hu'int : IsIntegral ℤ (u' : E) := RingOfIntegers.isIntegral_coe u'
  set n := c.natAbs with hn
  have hnpos : n ≠ 0 := Int.natAbs_ne_zero.mpr hc0
  obtain ⟨t, ht, htint, hut⟩ : ∃ t : E, cc t = t ∧ IsIntegral ℤ t ∧
      (u : E) * t = (n : E) * s := by
    rcases Int.natAbs_eq c with h | h
    · refine ⟨(u' : E) * s, by rw [cc_mul, hu'real, hs], hu'int.mul hsint, ?_⟩
      have : ((n : ℤ) : E) = (c : E) := by rw [← h]
      rw [← Int.cast_natCast, this, hcE]; ring
    · refine ⟨-((u' : E) * s), by rw [cc_neg, cc_mul, hu'real, hs], (hu'int.mul hsint).neg, ?_⟩
      have : ((n : ℤ) : E) = -(c : E) := by rw [h, Int.cast_neg, neg_neg]
      rw [← Int.cast_natCast, this, hcE]; ring
  have hmat : ((γ ^ n : X.Γ) : GL (Fin N) E) = (γ : GL (Fin N) E) ^ n := Subgroup.coe_pow _ _ _
  have hγn : (((γ ^ n : X.Γ) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) =
      transvMat X.Gm ξ (X.m * (u * t) * X.κ0) := by
    rw [hmat, Units.val_pow_eq_pow_val, hγ, transvMat_pow X.Gm ξ hiso, hut]
    congr 1; ring
  have hk := hkill t ht htint (γ ^ n) hγn
  rw [map_pow] at hk
  have h2 : n • Multiplicative.toAdd (φ γ) = 0 := by
    rw [← toAdd_pow, hk, toAdd_one]
  rw [nsmul_eq_mul, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact absurd (by exact_mod_cast h2) hnpos
  · exact Multiplicative.toAdd.injective (by rw [h2, toAdd_one])

end GlobalTheory.UnipKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureInverseRealSymmetricGram
section
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.RealGram

open GlobalTheory.HermFrame Filter

theorem curv_inv_of_real : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E), GlobalTheory.HermFrame.MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, GlobalTheory.HermFrame.mddbar H z ξ η = 0) → ∀ ξ η, GlobalTheory.HermFrame.curv (fun x => (H x)⁻¹) z ξ η = -((GlobalTheory.HermFrame.conn H z η)ᵀᴴ * GlobalTheory.HermFrame.conn H z ξ)ᵀ := by
  intro E _ _ _ _ g H z h2 hu hs hh hdd ξ η
  have hsz : (H z)ᵀ = H z := hs.self_of_nhds.eq
  have hhz : (H z)ᴴ = H z := hh.self_of_nhds.eq
  have he : (fun x => (H x)⁻¹) =ᶠ[𝓝 z] fun x => dualGram (H x) :=
    hs.mono fun x hx => by
      show (H x)⁻¹ = (H x)⁻¹ᵀ
      rw [transpose_nonsing_inv, hx.eq]
  have hbar : (mdbar H z η)ᵀ = mdbar H z η := by
    rw [← mdbar_transpose]; exact mdbar_congr (hs.mono fun x hx => hx.eq) η
  have hdel : (mdel H z η)ᴴ = mdbar H z η := conjTranspose_mdel hh η
  have key : (conn H z η)ᵀᴴ = (H z)ᵀ⁻¹ * (mdbar H z η)ᵀ := by
    rw [conn, transpose_mul, transpose_transpose, conjTranspose_mul, hdel, transpose_nonsing_inv,
      transpose_transpose, hsz, hbar, conjTranspose_nonsing_inv, hhz]
  rw [curv_congr he, curv_dual h2 hu, curv_eq h2 hu, hdd, transpose_zero, Matrix.mul_zero,
    sub_zero, key, conn, Matrix.mul_assoc, Matrix.mul_assoc]

end GlobalTheory.RealGram
end

