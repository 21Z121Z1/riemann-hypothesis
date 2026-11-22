import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RTensorInjectiveOfFlatBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0056

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TautologicalFamilyRefinementCompatibleLieAlgebra
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.TieUp

theorem exists_lift {ι : Type} {m k : ι → ℕ} {R K : Type} [CommRing R] [Field K] (a : R →+* K)
    (ha : Function.Injective a) {O : Subring K} (hO : ∀ x ∈ O, ∃ r, a r = x) {G : Mat m K} (hG : Par k O G) :
    ∃ G' : Mat m R, G'.map a = G ∧ ∀ τ, IsUnit (G' τ).det := by
  have h1 : ∀ τ i j, ∃ r, a r = G τ i j := fun τ i j => hO _ ((hG τ).1 i j)
  choose G' hG' using h1
  let G'' : Mat m R := fun τ => Matrix.of (G' τ)
  have e : G''.map a = G := by
    funext τ; ext i j; exact hG' τ i j
  refine ⟨G'', e, fun τ => ?_⟩
  obtain ⟨r, hr⟩ := hO _ (hG τ).2.2.1
  have hd : a (G'' τ).det = (G τ).det := by
    rw [← e]; exact a.map_det (G'' τ)
  refine IsUnit.of_mul_eq_one r (ha ?_)
  rw [map_mul, hd, hr, map_one, mul_inv_cancel₀ (hG.det_ne τ)]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B Y : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (k : (E →+* ℂ) → ℕ) (S' : Fr (ratOf Y) Dw.mult k) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X), Tied e B j f₀ S A₀ → Refines S S' φ f → ∃ (g₀ : EigFrame Z (constF e Y) (genericPt Y ≫ (f ≫ j) ≫ genι Z)) (A₁ : Mat Dw.mult Y.Fn), Tied e Y (f ≫ j) g₀ S' A₁ ∧ f₀.Coord (φ : B.Fn →+* Y.Fn) g₀ (A₁ * (A₀.map φ)⁻¹) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e B Y j f₀ S A₀ k S' φ f hT hR
  obtain ⟨A₁, hA₁⟩ := S'.nonempty (genericPoint Y.X)
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := Fr.det_ne hA₁
  have hmapd : ∀ {A : Mat Dw.mult B.Fn}, (∀ τ, (A τ).det ≠ 0) →
      ∀ τ, (A.map (φ : B.Fn →+* Y.Fn) τ).det ≠ 0 := fun {A} hA τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hA τ)
  have hgen : genericPt Y ≫ f = spMap (φ : B.Fn →+* Y.Fn) ≫ genericPt B := hR.hom
  have hx : genericPt Y ≫ (f ≫ j) ≫ genι Z = spMap (φ : B.Fn →+* Y.Fn) ≫ genericPt B ≫ j ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, hgen, Category.assoc]
  have hc : constF e Y = (φ : B.Fn →+* Y.Fn).comp (constF e B) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hst₀ : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f₀ inferInstance
  obtain ⟨g₀, hg₀⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f₀ Y.Fn (constF e Y)
    (genericPt Y ≫ (f ≫ j) ≫ genι Z) (φ : B.Fn →+* Y.Fn) inferInstance hst₀ hx hc).2
    (A₁ * (A₀.map (φ : B.Fn →+* Y.Fn))⁻¹) fun τ => by
      rw [Pi.mul_apply, Matrix.det_mul, Pi.inv_apply, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact Ne.isUnit (mul_ne_zero (hA₁d τ) (inv_ne_zero (hmapd hA₀d τ)))
  refine ⟨g₀, A₁, ⟨hA₁, fun y A' hA' => ?_⟩, hg₀⟩
  obtain ⟨A, hA⟩ := S.nonempty (f y)
  obtain ⟨φ₁, fA, hfA⟩ := hT.2 (f y) A hA
  have hAd : ∀ τ, (A τ).det ≠ 0 := Fr.det_ne hA
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  let aY : Y.X.presheaf.stalk y →+* Y.Fn := algebraMap (Y.X.presheaf.stalk y) Y.X.functionField
  let aB : B.X.presheaf.stalk (f y) →+* B.Fn := algebraMap (B.X.presheaf.stalk (f y)) B.X.functionField
  let σ : B.X.presheaf.stalk (f y) →+* Y.X.presheaf.stalk y := (f.stalkMap y).hom
  have hcomp : (φ : B.Fn →+* Y.Fn).comp aB = aY.comp σ :=
    RingHom.ext fun a => map_algebraMap_stalk hR.hom y a
  obtain ⟨G, hG, hGd⟩ := exists_lift aY (IsFractionRing.injective (Y.X.presheaf.stalk y) Y.X.functionField)
    (fun x hx => mem_O_ratOf.1 hx) (hR.sub y A' hA' A hA)
  have hstA : fA.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ fA inferInstance
  have hσ : spMap σ ≫ stalkPt B (f y) = stalkPt Y y ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hx' : stalkPt Y y ≫ (f ≫ j) ≫ genι Z = spMap σ ≫ stalkPt B (f y) ≫ j ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, ← hσ, Category.assoc]
  obtain ⟨f', hf'⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA (Y.X.presheaf.stalk y) (σ.comp φ₁)
    (stalkPt Y y ≫ (f ≫ j) ≫ genι Z) σ inferInstance hstA hx' rfl).2 G hGd
  have hst' : f'.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f' inferInstance
  have haY : spMap aY ≫ stalkPt Y y = genericPt Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)
  have hx'' : genericPt Y ≫ (f ≫ j) ≫ genι Z = spMap aY ≫ stalkPt Y y ≫ (f ≫ j) ≫ genι Z := by
    rw [← haY, Category.assoc]
  have hc' : constF e Y = aY.comp (σ.comp φ₁) := by
    rw [← RingHom.comp_assoc, ← hcomp, RingHom.comp_assoc, hc, hfA.2.1]
  obtain ⟨T, hTc, -⟩ := ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f' Y.Fn (constF e Y)
    (genericPt Y ≫ (f ≫ j) ≫ genι Z) aY inferInstance hst' hx'' hc').1 g₀).1
  have h1 := GlobalTheory.ShFam.CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f' _ _ _ g₀ σ aY G T inferInstance hf' hTc
  have h2 := GlobalTheory.ShFam.CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f₀ _ _ _ g₀ aB (φ : B.Fn →+* Y.Fn) _ _
    inferInstance hfA hg₀
  rw [hcomp] at h2
  have hu := ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA Y.Fn (constF e Y)
    (genericPt Y ≫ (f ≫ j) ≫ genι Z) (aY.comp σ) inferInstance hstA h1.1 h1.2.1).1 g₀).1.unique h1 h2
  have hG' : G.map aY = A' * (A.map (φ : B.Fn →+* Y.Fn))⁻¹ := hG
  rw [hG', Mat.map_mul, Mat.map_inv, ← mul_assoc, ← mul_assoc, mul_assoc A₁, Mat.inv_mul (hmapd hA₀d), mul_one] at hu
  have hT' : T = A₁ * A'⁻¹ := by
    have h3 := congrArg (fun M => M * A.map (φ : B.Fn →+* Y.Fn) * A'⁻¹) hu
    rwa [mul_assoc (T * A'), mul_assoc A₁, Mat.inv_mul (hmapd hAd), mul_one, mul_one, mul_assoc,
      Mat.mul_inv hA'd, mul_one] at h3
  exact ⟨σ.comp φ₁, f', hT' ▸ hTc⟩

end GlobalTheory.ShFam.TieUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionSectionEqPushedTraitPointLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricTorsionSection_eq_pushed_trait_point_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (k : ℕ)
    (s : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t.G)),
    (∀ (A : Type) [CommRing A] (a : R →+* A) τ h, s A a τ h ^ k = 1) →
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (a' : R →+* A') (f : A →+* A') τ h τ' h',
      a' = f.comp a → (∀ χ, (τ' χ : A') = f (τ χ : A)) → (s A' a' τ' h').left = spMap f ≫ (s A a τ h).left) →
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (a' : R →+* A')
      (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ) →
    ∀ (X' : Type) [AddCommGroup X'] (ρ : P.D.toPre.X →+ X')
      (V : Type) [CommRing V] [IsLocalRing V] (ψ : R →+* V) (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
      (j : splitTorus (Sp V) X' ⟶ tV.G) [IsMonHom j]
      (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
      (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ))),
      m₀'.φ = m₀.φ ≫ mV.φ →
      GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    ∀ (U : Type) [CommRing U] [IsLocalRing U] (u : V →+* U), IsLocalHom u → IsUnit (k : U) →
    ∀ (τU : Multiplicative X' →* Uˣ) (τ : Multiplicative P.D.toPre.X →* Uˣ) (h : τ ^ k = 1),
      τU ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τU (Multiplicative.ofAdd (ρ χ))) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) X'),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τU (Multiplicative.ofAdd χ))) →
      (s U (u.comp ψ) τ h).left = (z ≫ j).left ≫ mV.φ := by
  first | exact @GlobalTheory.TorSecLocal.toric_torsion_section_overLocal | exact GlobalTheory.TorSecLocal.toric_torsion_section_overLocal | (intros; apply GlobalTheory.TorSecLocal.toric_torsion_section_overLocal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharacterCocycleDescent
section
set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LineNorm

theorem tensor_eq_zero_of_sections {R B : Type} [CommRing R] [CommRing B] [Algebra R B] [Module.Free R B]
    (inj : ∀ b : B, (∀ σ : B →ₐ[R] R, σ b = 0) → b = 0) (s : B ⊗[R] B)
    (h : ∀ σ τ : B →ₐ[R] R, Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _) s = 0) : s = 0 := by
  classical
  let e := Module.Free.chooseBasis R B
  have h1 : ∀ σ : B →ₐ[R] R, TensorProduct.lid R B (σ.toLinearMap.rTensor B s) = 0 := by
    intro σ
    refine inj _ fun τ => ?_
    rw [← h σ τ]
    clear h
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  have h2 : ∀ f : B →ₗ[R] R, TensorProduct.rid R B (f.lTensor B s) = 0 := by
    intro f
    refine inj _ fun σ => ?_
    have : σ (TensorProduct.rid R B (f.lTensor B s)) = f (TensorProduct.lid R B (σ.toLinearMap.rTensor B s)) := by
      clear h h1
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [mul_comm]
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [this, h1, map_zero]
  refine (Algebra.TensorProduct.basis B e).ext_elem fun i => ?_
  have : (Algebra.TensorProduct.basis B e).repr s i = TensorProduct.rid R B ((e.coord i).lTensor B s) := by
    clear h h1 h2
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.smul_def, mul_comm]
    | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb]
  rw [this, h2]
  simp

theorem exists_groupLike_of_sections {R B : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing B]
    [Algebra R B] [Module.Finite R B] [Module.Free R B]
    (inj : ∀ b : B, (∀ σ : B →ₐ[R] R, σ b = 0) → b = 0) (Δ : B →ₐ[R] B ⊗[R] B) (ε : B →ₐ[R] R)
    (κ : (B →ₐ[R] R) → R)
    (hmul : ∀ σ τ : B →ₐ[R] R,
      κ ((Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).comp Δ) = κ σ * κ τ)
    (hone : κ ε = 1) : ∃ b : B, (∀ σ : B →ₐ[R] R, σ b = κ σ) ∧ Δ b = b ⊗ₜ b := by
  classical
  let C := FractionRing R
  have hinj : Function.Injective (algebraMap R C) := IsFractionRing.injective R C
  let j : (B →ₐ[R] R) → (B →ₐ[R] C) := fun σ => (Algebra.ofId R C).comp σ
  have hj : Function.Injective j := fun σ τ h => AlgHom.ext fun b => hinj (AlgHom.congr_fun h b)
  obtain ⟨d, a, hd, ha⟩ := GlobalTheory.exists_smul_fun_eq_eval_points R C B
    (Function.extend j (fun σ => algebraMap R C (κ σ)) 0)
  have ha' : ∀ σ : B →ₐ[R] R, σ a = d * κ σ := by
    intro σ
    apply hinj
    have := ha (j σ)
    rw [hj.extend_apply] at this
    rw [map_mul, ← this]
    rfl
  have hε : ε a = d := by rw [ha', hone, mul_one]
  have hΔ : d • Δ a = a ⊗ₜ a := by
    rw [← sub_eq_zero]
    refine tensor_eq_zero_of_sections inj _ fun σ τ => ?_
    have h1 := ha' ((Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).comp Δ)
    rw [hmul, AlgHom.comp_apply] at h1
    rw [map_sub, map_smul, h1, Algebra.TensorProduct.lift_tmul, ha', ha', smul_eq_mul]
    ring
  have key : ∀ f : B →ₗ[R] R, d ∣ f a := by
    intro f
    refine GlobalTheory.dvd_of_smul_apply_eq_smul R C B
      ((TensorProduct.rid R B).toLinearMap ∘ₗ f.lTensor B ∘ₗ Δ.toLinearMap) ε.toLinearMap d (f a) a
      hd (by simpa [hε] using hd) ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply]
    rw [← map_smul, ← map_smul, hΔ]
    simp
  let e := Module.Free.chooseBasis R B
  choose g hg using fun i => key (e.coord i)
  have hb : a = d • ∑ i, g i • e i := by
    conv_lhs => rw [← e.sum_repr a]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_smul, ← hg i, Module.Basis.coord_apply]
  have hv : ∀ σ : B →ₐ[R] R, σ (∑ i, g i • e i) = κ σ := fun σ =>
    mul_left_cancel₀ hd (by rw [← ha', ← smul_eq_mul, ← map_smul, ← hb])
  refine ⟨∑ i, g i • e i, hv, ?_⟩
  rw [← sub_eq_zero]
  refine tensor_eq_zero_of_sections inj _ fun σ τ => ?_
  have h1 := hv ((Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).comp Δ)
  rw [hmul, AlgHom.comp_apply] at h1
  rw [map_sub, h1, Algebra.TensorProduct.lift_tmul, hv, hv, sub_self]

end GlobalTheory.LineNorm

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineNorm

private theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

theorem IsFinPart.exists_comul {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {x : Sp R ⟶ X}
    {q : ℕ} {B : Type} [CommRing B] [Algebra R B] {u : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G}
    (hu : IsFinPart t x q u) : ∃ Δ : B →ₐ[R] B ⊗[R] B,
      ∀ (S : Type) [CommRing S] (φ : R →+* S) (w w' : Over.mk (spMap φ ≫ x) ⟶ t.G) (ν : B ⊗[R] B →+* S),
        ν.comp (algebraMap R (B ⊗[R] B)) = φ →
        spMap (ν.comp (Algebra.TensorProduct.includeLeft (S := R)).toRingHom) ≫ u.left = w.left →
        spMap (ν.comp (Algebra.TensorProduct.includeRight).toRingHom) ≫ u.left = w'.left →
        spMap (ν.comp Δ.toRingHom) ≫ u.left = (w * w').left := by
  let p : ∀ _ : B →ₐ[R] B ⊗[R] B, (Over.mk (spMap (algebraMap R (B ⊗[R] B)) ≫ x) ⟶
      Over.mk (spMap (algebraMap R B) ≫ x)) := fun i =>
    Over.homMk (spMap i.toRingHom) (by
      simp only [Over.mk_left, Over.mk_hom]
      rw [← Category.assoc, sp_comp]
      congr 2
      exact i.comp_algebraMap)
  let i₁ : B →ₐ[R] B ⊗[R] B := Algebra.TensorProduct.includeLeft (S := R)
  let i₂ : B →ₐ[R] B ⊗[R] B := Algebra.TensorProduct.includeRight
  obtain ⟨δ, hδ, hδ'⟩ := hu.mul _ _ (p i₁ ≫ u) (p i₂ ≫ u) ⟨i₁.toRingHom, i₁.comp_algebraMap, rfl⟩
    ⟨i₂.toRingHom, i₂.comp_algebraMap, rfl⟩
  refine ⟨⟨δ, fun r => RingHom.congr_fun hδ r⟩, ?_⟩
  intro S _ φ w w' ν hν h1 h2
  let g : Over.mk (spMap φ ≫ x) ⟶ Over.mk (spMap (algebraMap R (B ⊗[R] B)) ≫ x) :=
    Over.homMk (spMap ν) (by
      simp only [Over.mk_left, Over.mk_hom]
      rw [← Category.assoc, sp_comp, hν])
  have e1 : w = g ≫ p i₁ ≫ u := by
    ext1
    rw [← h1, ← sp_comp, Category.assoc]
    rfl
  have e2 : w' = g ≫ p i₂ ≫ u := by
    ext1
    rw [← h2, ← sp_comp, Category.assoc]
    rfl
  rw [e1, e2, ← MonObj.comp_mul, ← sp_comp, Category.assoc, Over.comp_left, ← hδ']
  rfl

theorem exists_groupLike_unit_of_isFinPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (x : Sp R ⟶ X) (q : ℕ) (B : Type) [CommRing B] [Algebra R B] (u : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G), IsFinPart t x q u → ∀ κ : (B →ₐ[R] R) → Rˣ, (∀ (σ σ' σ'' : B →ₐ[R] R) (w w' : Over.mk (spMap (RingHom.id R) ≫ x) ⟶ t.G), spMap σ.toRingHom ≫ u.left = w.left → spMap σ'.toRingHom ≫ u.left = w'.left → spMap σ''.toRingHom ≫ u.left = (w * w').left → κ σ'' = κ σ * κ σ') → ∃ b : Bˣ, (∀ σ : B →ₐ[R] R, σ (b : B) = (κ σ : R)) ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (w w' : Over.mk (spMap φ ≫ x) ⟶ t.G) (β β' β'' : B →+* S), β.comp (algebraMap R B) = φ → β'.comp (algebraMap R B) = φ → β''.comp (algebraMap R B) = φ → spMap β ≫ u.left = w.left → spMap β' ≫ u.left = w'.left → spMap β'' ≫ u.left = (w * w').left → β'' (b : B) = β (b : B) * β' (b : B) := by
  intro E _ _ _ H X t R _ _ _ x q B _ _ u hu κ hκ
  haveI := hu.finite
  haveI := hu.free
  obtain ⟨Δ, hΔ⟩ := hu.exists_comul
  obtain ⟨ε₀, hε, hε'⟩ := hu.one R (RingHom.id R)
  let ε : B →ₐ[R] R := ⟨ε₀, fun r => RingHom.congr_fun hε r⟩
  have hone : κ ε = 1 := by
    have := hκ ε ε ε 1 1 hε' hε' (by rw [_root_.mul_one]; exact hε')
    exact left_eq_mul.mp this
  let p : ∀ _ : B →ₐ[R] R, (Over.mk (spMap (RingHom.id R) ≫ x) ⟶
      Over.mk (spMap (algebraMap R B) ≫ x)) := fun i =>
    Over.homMk (spMap i.toRingHom) (by
      simp only [Over.mk_left, Over.mk_hom]
      rw [← Category.assoc, sp_comp]
      congr 2
      exact i.comp_algebraMap)
  have hmul : ∀ σ τ : B →ₐ[R] R,
      κ ((Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).comp Δ) = κ σ * κ τ := by
    intro σ τ
    refine hκ σ τ _ (p σ ≫ u) (p τ ≫ u) rfl rfl ?_
    refine hΔ R (RingHom.id R) _ _ (Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).toRingHom
      (Algebra.TensorProduct.lift σ τ (fun _ _ => Commute.all _ _)).comp_algebraMap ?_ ?_
    · change _ = spMap σ.toRingHom ≫ u.left
      congr 2
      ext b
      simp
    · change _ = spMap τ.toRingHom ≫ u.left
      congr 2
      ext b
      simp
  obtain ⟨b, hb, hb'⟩ := exists_groupLike_of_sections hu.inj Δ ε (fun σ => (κ σ : R))
    (fun σ τ => by simp only [hmul, Units.val_mul]) (by simp only [hone, Units.val_one])
  obtain ⟨c, hc, -⟩ := exists_groupLike_of_sections hu.inj Δ ε (fun σ => (((κ σ)⁻¹ : Rˣ) : R))
    (fun σ τ => by simp only [hmul, mul_inv, Units.val_mul]) (by simp only [hone, inv_one, Units.val_one])
  have hbc : b * c = 1 := by
    rw [← sub_eq_zero]
    refine hu.inj _ fun σ => ?_
    rw [map_sub, map_mul, hb, hc, map_one, Units.mul_inv, sub_self]
  refine ⟨⟨b, c, hbc, by rw [_root_.mul_comm, hbc]⟩, hb, ?_⟩
  intro S _ φ w w' β β' β'' h h' h'' k k' k''
  letI : Algebra R S := φ.toAlgebra
  let a : B →ₐ[R] S := ⟨β, fun r => RingHom.congr_fun h r⟩
  let a' : B →ₐ[R] S := ⟨β', fun r => RingHom.congr_fun h' r⟩
  let ν : B ⊗[R] B →ₐ[R] S := Algebra.TensorProduct.lift a a' (fun _ _ => Commute.all _ _)
  have h3 := hΔ S φ w w' ν.toRingHom ν.comp_algebraMap
    (by rw [← k]; congr 2; ext y; simp [ν, a]) (by rw [← k']; congr 2; ext y; simp [ν, a'])
  have h4 : β'' = ν.toRingHom.comp Δ.toRingHom :=
    hu.mono S _ _ (h''.trans (ν.comp Δ).comp_algebraMap.symm) (k''.trans h3.symm)
  have h5 : β'' b = ν (Δ b) := by rw [h4]; rfl
  change β'' b = β b * β' b
  rw [h5, hb', Algebra.TensorProduct.lift_tmul]
  rfl

end GlobalTheory.LineNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionFlatLocallyQuasiFinite
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibreFlatGen

open FibreFlat FiniteFibreFlat MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false in

theorem flat_of_flatOver_fields {X Y S : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Y ⟶ S) (h1 : Flat (f ≫ g))
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) : Flat f := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S with ih
  · refine IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_
    let u := S.affineCover.f i
    have sq := IsPullback.of_hasPullback f (pullback.fst g u)
    have sq' := IsPullback.of_hasPullback g u
    haveI := isLocallyNoetherian_of_isOpenImmersion (pullback.fst g u)
    haveI := isLocallyNoetherian_of_isOpenImmersion (pullback.fst f (pullback.fst g u))
    refine ih (pullback.snd f (pullback.fst g u)) (pullback.snd g u)
      (MorphismProperty.of_isPullback (sq.paste_vert sq') h1)
      (fun k _ t => flatOver_of_comp_base (u := u) ?_) ⟨_, rfl⟩
    rw [← pullback.condition]
    exact (H k _).target sq
  obtain ⟨R, rfl⟩ := hS
  wlog hA : ∃ A, Y = Spec A generalizing X Y with ih
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    haveI := isLocallyNoetherian_of_isOpenImmersion (Y.affineCover.f i)
    haveI := isLocallyNoetherian_of_isOpenImmersion (pullback.fst f (Y.affineCover.f i))
    exact ih (pullback.snd f (Y.affineCover.f i)) (Y.affineCover.f i ≫ g)
      (by rw [e]; infer_instance) (fun k _ t => (H k t).target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hA
  wlog hX : ∃ B, X = Spec B generalizing X with ih
  · refine IsZariskiLocalAtSource.of_openCover X.affineCover fun i => ?_
    haveI := isLocallyNoetherian_of_isOpenImmersion (X.affineCover.f i)
    exact ih (X.affineCover.f i ≫ f) (by rw [Category.assoc]; infer_instance)
      (fun k _ t => (H k t).source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1
  rw [Flat.SpecMap_iff] at h1 ⊢
  letI : Algebra R A := g.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra R B := (g ≫ f).hom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Flat R B := h1
  haveI : IsNoetherianRing A := (isLocallyNoetherian_Spec (R := A)).1 inferInstance
  haveI : IsNoetherianRing B := (isLocallyNoetherian_Spec (R := B)).1 inferInstance
  refine flat_of_flat_fibres (R := R) (A := A) (B := B) fun k C _ _ _ t h e => ?_
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)
  have := H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip
    (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      exact e)
  rw [Flat.SpecMap_iff] at this
  exact RingHom.flat_algebraMap_iff.mp this

theorem flat_and_locallyQuasiFinite_torsion : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ q : ℕ, q ≠ 0 → Flat (torsion G q).hom ∧ LocallyQuasiFinite (torsion G q).hom := by
  intro S _ G _ hG q hq
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have hm := MulEtaleDvr.isMonHom_mulN G q
  have : LocallyOfFiniteType ((mulN G q).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType (mulN G q).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ((mulN G q).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact (mulN G q).left := QuasiCompact.of_comp _ G.hom
  have hq' : LocallyQuasiFinite (mulN G q).left :=
    locallyQuasiFinite_of_finite_geometric_ker _ G G _ hm inferInstance inferInstance fun K _ _ t => by
      have h₀ := finite_torsion_semiAbelian K ((Over.pullback t).obj G)
        (IsSemiAbelian.pullback t G hG) q (Nat.pos_of_ne_zero hq)
      have h₁ := FewZeros.finite_torsion_of_mulEquiv
        (TorsionLift.ptsEquiv t G (𝟙_ (Over (Sp K))) t (Category.id_comp t)) q h₀
      simp only [MulUnramified.comp_mulN]
      exact h₁
  have hf : Flat (mulN G q).left := by
    have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
    refine flat_of_flatOver_fields _ G.hom (by rw [Over.w]; infer_instance) fun k _ t => ?_
    exact flatOver_of_pullback _ t (IntDiv.flat_fibre G (mulN G q) k t)
  exact ⟨MorphismProperty.of_isPullback (P := @Flat) (MulEtaleDvr.isPullback_torsion G q) hf,
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (MulEtaleDvr.isPullback_torsion G q) hq'⟩

end GlobalTheory.FibreFlatGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivOfAbSt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Cht

theorem trivOfAbSt : TrivOfAbSt := by
  intro E _ _ _ H Dw l Xo c O _ β Y p C P A _ hab
  have hloc : IsLocalHom A.f := ⟨fun a ha => by
    by_contra h
    exact (mem_maximalIdeal _).1 ((mem_maximalIdeal_ball (A.f a)).2 (A.f_loc a ((mem_maximalIdeal _).2 h))) ha⟩
  have e1 : spMap A.f (closedPoint _) = closedPoint A.R := comap_closedPoint A.f
  have e2 : P.yt (closedPoint ↥(intO ↥C.S)) = A.ι (closedPoint A.R) := by
    have h := congrArg (fun g : Sp ↥(intO ↥C.S) ⟶ Y.X => g (closedPoint ↥(intO ↥C.S))) A.fac
    exact h.symm.trans ((Scheme.Hom.comp_apply _ _ _).trans (congrArg A.ι e1))
  have h₁ : closedPoint A.R ∈ abLocus A.t.G :=
    (abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 _).1 (e2 ▸ hab)
  have hmax : (maximalIdeal A.R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (A.R ⧸ maximalIdeal A.R ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have hle : maximalIdeal A.R ^ (0 + 1) ≤ (closedPoint A.R).asIdeal := by
    rw [zero_add, pow_one]; exact le_rfl
  obtain ⟨q, hq⟩ : closedPoint A.R ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (maximalIdeal A.R ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hle
  let g := A.U.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hq' : thick A.R (maximalIdeal A.R) 0 q ∈ abLocus A.t.G := by
    rw [← hq] at h₁; exact h₁
  exact ArcNotAbelian.subsingleton_of_mem_abLocus A.t.G A.t.semi _ hF _ q hq' A.U.D.toPre.X g.i g.i_hom

end GlobalTheory.LocM.Cht
end
end

