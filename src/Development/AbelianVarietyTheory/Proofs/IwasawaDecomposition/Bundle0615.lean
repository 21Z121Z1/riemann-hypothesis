import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0592
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0186
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0182
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0177
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVariety
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.TieBase

theorem spMap_trans {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_affine_factor {Y : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (h : x (IsLocalRing.closedPoint R) ∈ U) :
    ∃ ψ : Γ(Y, U) →+* R, spMap ψ ≫ hU.fromSpec = x := by
  obtain ⟨ψ, hψ⟩ := EigLoc.exists_stalk_factor x _ (specializes_refl _)
  refine ⟨ψ.comp (Y.presheaf.germ U _ h).hom, ?_⟩
  have hg : spMap (Y.presheaf.germ U _ h).hom ≫ hU.fromSpec = Y.fromSpecStalk _ := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk h]; rfl
  rw [spMap_trans, Category.assoc, hg, hψ]

theorem par_zero_iff {ι : Type} {m : ι → ℕ} {R K : Type} [CommRing R] [Field K] (a : R →+* K)
    (ha : Function.Injective a) (O : Subring K) (hO : ∀ x, x ∈ O ↔ ∃ r, a r = x) (P : Mat m K) :
    Par 0 O P ↔ ∃ G : Mat m R, (∀ τ, IsUnit (G τ).det) ∧ P = G.map a := by
  constructor
  · intro hP
    have hent : ∀ τ i j, ∃ r, a r = P τ i j := fun τ i j => (hO _).1 ((hP τ).1 i j)
    choose G₀ hG using hent
    let G : Mat m R := fun τ => Matrix.of (G₀ τ)
    have hGP : P = G.map a := by
      funext τ i j
      exact (hG τ i j).symm
    refine ⟨G, fun τ => ?_, hGP⟩
    obtain ⟨s, hs⟩ := (hO _).1 (hP τ).2.2.1
    have hdet : a (G τ).det = (P τ).det := by
      rw [hGP]
      exact RingHom.map_det a (G τ)
    refine isUnit_iff_exists_inv.2 ⟨s, ha ?_⟩
    rw [map_mul, hdet, hs, map_one, mul_inv_cancel₀ (hP τ).2.1]
  · rintro ⟨G, hG, rfl⟩ τ
    have hdet : (G.map a τ).det = a (G τ).det := (RingHom.map_det a (G τ)).symm
    obtain ⟨u, hu⟩ := hG τ
    refine ⟨fun i j => (hO _).2 ⟨G τ i j, rfl⟩, ?_, ?_, fun i j hi _ => absurd hi (Nat.not_lt_zero _)⟩
    · rw [hdet, ← hu]
      exact (u.isUnit.map a).ne_zero
    · rw [hdet, ← hu]
      exact (hO _).2 ⟨((u⁻¹ : Rˣ) : R), by rw [map_units_inv]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem frames_iff {R R₁ K : Type} [CommRing R] [CommRing R₁] [IsLocalRing R₁] [Field K] {φ : c.F →+* R}
    {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (hf : f.Stable) (ψ : R →+* R₁) (a : R₁ →+* K) (ha : Function.Injective a)
    {x₁ : Sp R₁ ⟶ Z.X} (hx : x₁ = spMap ψ ≫ x) {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} (f₀ : EigFrame Z φ₀ x₀)
    {T : Mat Dw.mult K} (hT : f.Coord (a.comp ψ) f₀ T) (A : Mat Dw.mult K) :
    ((∀ τ, (A τ).det ≠ 0) ∧ ∃ (φ₁ : c.F →+* R₁) (g : EigFrame Z φ₁ x₁), g.Coord a f₀ A⁻¹) ↔
      ∃ G : Mat Dw.mult R₁, (∀ τ, IsUnit (G τ).det) ∧ A * T = G.map a := by
  have hU := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R φ x f K φ₀ x₀ (a.comp ψ) inferInstance hf hT.1 hT.2.1).1 f₀
  have huniq : ∀ B, f.Coord (a.comp ψ) f₀ B → B = T := fun B hB => hU.1.unique hB hT
  constructor
  · rintro ⟨hA, φ₁, g, hg⟩
    have hφ₁ : φ₁ = ψ.comp φ := by
      apply RingHom.ext
      intro r
      apply ha
      have h := RingHom.congr_fun (hg.2.1.symm.trans hT.2.1) r
      simpa using h
    subst hφ₁
    obtain ⟨hE, hunits⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ ψ inferInstance hf hx rfl).1 g
    obtain ⟨G, hG, -⟩ := hE
    refine ⟨G, hunits G hG, ?_⟩
    have hc := GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ g K φ₀ x₀ f₀ ψ a G A⁻¹ inferInstance hG hg
    rw [← huniq _ hc, ← mul_assoc, Mat.mul_inv hA, one_mul]
  · rintro ⟨G, hG, hAT⟩
    obtain ⟨g, hfg⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ ψ inferInstance hf hx rfl).2 G hG
    have hgs : g.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z R₁ (ψ.comp φ) x₁ g inferInstance
    have hx₀ : x₀ = spMap a ≫ x₁ := by rw [hT.1, hx, spMap_trans, Category.assoc]
    have hφ₀ : φ₀ = a.comp (ψ.comp φ) := hT.2.1.trans (RingHom.comp_assoc _ _ _)
    obtain ⟨⟨B, hB, -⟩, -⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R₁ (ψ.comp φ) x₁ g K φ₀ x₀ a inferInstance hgs hx₀ hφ₀).1 f₀
    have hc := GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ g K φ₀ x₀ f₀ ψ a G B inferInstance hfg hB
    have hTB : B * G.map a = T := huniq _ hc
    have hGd : ∀ τ, (G.map a τ).det ≠ 0 := fun τ => by
      have h := ((hG τ).map a).ne_zero
      rw [RingHom.map_det] at h
      exact h
    have hAB : A * B = 1 := by
      calc A * B = A * B * (G.map a * (G.map a)⁻¹) := by rw [Mat.mul_inv hGd, mul_one]
      _ = A * (B * G.map a) * (G.map a)⁻¹ := by simp only [mul_assoc]
      _ = 1 := by rw [hTB, hAT, Mat.mul_inv hGd]
    have hAτ : ∀ τ, A τ * B τ = 1 := fun τ => congrFun hAB τ
    have hAd : ∀ τ, (A τ).det ≠ 0 := fun τ hd => by
      have h := congrArg Matrix.det (hAτ τ)
      rw [Matrix.det_mul, hd, zero_mul, Matrix.det_one] at h
      exact zero_ne_one h
    have hAi : A⁻¹ = B := funext fun τ => Matrix.inv_eq_right_inv (hAτ τ)
    refine ⟨hAd, ψ.comp φ, g, ?_⟩
    rw [hAi]
    exact hB

variable {F : Type} [Field F]

theorem genericPt_eq (B : GlobalTheory.ProjVar.Var F) (y : B.X) :
    genericPt B = spMap (algebraMap (B.X.presheaf.stalk y) B.X.functionField) ≫ stalkPt B y := by
  unfold genericPt stalkPt
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)]
  rfl

theorem genericPt_str (e : F ≃+* c.F) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) : (genericPt B ≫ j) ≫ genStr Z = spMap (constF e B) := by
  have hs : genericPt B ≫ B.str = spMap (algebraMap F B.Fn) := by
    apply ext_of_isAffine
    unfold genericPt spMap
    rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_mono (Scheme.ΓSpecIso _).hom,
      Scheme.ΓSpecIso_naturality]
    ext a
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [IsScalarTower.algebraMap_apply F Γ(B.X, ⊤) B.Fn, GlobalTheory.ProjVar.Var.algebraMap_Γ,
      GlobalTheory.Cartier.CartierDiv.algebraMap_top, CommRingCat.inv_hom_apply]
    have hmap : (Spec (B.X.presheaf.stalk (genericPoint B.X))).presheaf.map
        (homOfLE (le_top : (⊤ : (Spec (B.X.presheaf.stalk (genericPoint B.X))).Opens) ≤ ⊤)).op = 𝟙 _ := by
      rw [show (homOfLE (le_top : (⊤ : (Spec (B.X.presheaf.stalk (genericPoint B.X))).Opens) ≤ ⊤)) = 𝟙 _ from rfl]
      exact CategoryTheory.Functor.map_id _ _
    rw [hmap, CommRingCat.hom_id, RingHom.id_apply]
    exact CommRingCat.hom_inv_apply _ _
  have hid : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [← spMap_trans, RingEquiv.toRingHom_comp_symm_toRingHom]
    simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
  unfold constF
  rw [spMap_trans, ← hs, ← hj]
  simp only [Category.assoc, hid, Category.comp_id]

def fam (e : F ≃+* c.F) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) :
    Fr (ratOf B) Dw.mult 0 where
  S (y : B.X) := {A | (∀ τ, (A τ).det ≠ 0) ∧ ∃ (φ : c.F →+* B.X.presheaf.stalk y)
    (f : EigFrame Z φ (stalkPt B y ≫ j ≫ genι Z)),
    f.Coord (algebraMap (B.X.presheaf.stalk y) B.X.functionField) f₀ A⁻¹}
  loc (z : B.X) := by
    obtain ⟨U, hU, φ, f, hz, hφ, hf⟩ := GlobalTheory.T.exists_affine_stable_lie_eigenspace_frame E H Dw l Xo c O β Z (j z)
    have key : ∀ y : B.X, j y ∈ U → ∃ ψ : Γ(gen Z, U) →+* B.X.presheaf.stalk y,
        spMap ψ ≫ hU.fromSpec = stalkPt B y ≫ j := fun y hy =>
      exists_affine_factor _ hU (by
        show j (B.X.fromSpecStalk y (IsLocalRing.closedPoint _)) ∈ U
        rw [Scheme.fromSpecStalk_closedPoint]; exact hy)
    have key' : ∀ (y : B.X) (ψ : Γ(gen Z, U) →+* B.X.presheaf.stalk y), spMap ψ ≫ hU.fromSpec = stalkPt B y ≫ j →
        spMap ((algebraMap (B.X.presheaf.stalk y) B.X.functionField).comp ψ) ≫ hU.fromSpec = genericPt B ≫ j :=
      fun y ψ h => by rw [spMap_trans, Category.assoc, h, genericPt_eq B y, Category.assoc]
    obtain ⟨ψ₀, hψ₀⟩ := key z hz
    have h₀ := key' z ψ₀ hψ₀
    obtain ⟨⟨T, hT, -⟩, hu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ φ _ f B.Fn (constF e B) (genericPt B ≫ j ≫ genι Z)
      ((algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp ψ₀) inferInstance hf
      (by rw [← Category.assoc, ← h₀, Category.assoc])
      (EigLoc.spMap_inj (by rw [← genericPt_str e B j hj, ← h₀, Category.assoc, hφ, ← spMap_trans]))).1 f₀
    have hTd : ∀ τ, (T τ).det ≠ 0 := fun τ => (hu T hT τ).ne_zero
    refine ⟨j ⁻¹ᵁ U, T⁻¹, hz, fun τ => ?_, fun (y : B.X) hy A => ?_⟩
    · exact (Matrix.isUnit_det_of_right_inverse (congrFun (Mat.inv_mul hTd) τ)).ne_zero
    · obtain ⟨ψ, hψ⟩ := key y hy
      have e1 : (algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp ψ₀ =
          (algebraMap (B.X.presheaf.stalk y) B.X.functionField).comp ψ :=
        EigLoc.spMap_inj ((cancel_mono hU.fromSpec).1 (h₀.trans (key' y ψ hψ).symm))
      rw [e1] at hT
      have ha : Function.Injective (algebraMap (B.X.presheaf.stalk y) B.X.functionField) :=
        IsFractionRing.injective _ _
      rw [Mat.inv_inv hTd]
      refine (frames_iff f hf ψ _ ha (by rw [← Category.assoc, ← hψ, Category.assoc]) f₀ hT A).trans
        (par_zero_iff _ ha _ (fun x => mem_O_ratOf (Y := B) (y := y) (g := x)) _).symm

end GlobalTheory.ShFam.TieBase

open GlobalTheory.ShFam.TieBase in

theorem GlobalTheory.ShFam.TieBase.exists_tied : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z), j ≫ genStr Z ≫ spMap e.toRingHom = B.str → ∃ (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn), Tied e B j f₀ S A₀ := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e B j hj
  have hx : (genericPt B ≫ j) ≫ genι Z = genericPt B ≫ j ≫ genι Z := Category.assoc _ _ _
  obtain ⟨f₀⟩ : Nonempty (EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) := by
    rw [← hx]
    exact EigLoc.exists_eigFrame E H Dw l Xo c O β Z B.Fn (constF e B) (genericPt B ≫ j) (genericPt_str e B j hj)
  refine ⟨f₀, fam e B j hj f₀, 1, ?_⟩
  unfold GlobalTheory.ShFam.Tied
  refine ⟨?_, ?_⟩
  · have hst : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z B.Fn (constF e B) _ f₀ inferInstance
    have hsp : spMap (RingHom.id B.Fn) = 𝟙 _ := by simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
    obtain ⟨⟨A₁, hA₁, huq⟩, hu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z B.Fn (constF e B) _ f₀ B.Fn (constF e B) _
      (RingHom.id B.Fn) inferInstance hst (by rw [hsp, Category.id_comp]) (RingHom.id_comp _).symm).1 f₀
    have h2 := GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z B.Fn (constF e B) _ f₀ B.Fn (constF e B) _ f₀ B.Fn (constF e B) _ f₀
      (RingHom.id B.Fn) (RingHom.id B.Fn) A₁ A₁ inferInstance hA₁ hA₁
    have hm : A₁.map (RingHom.id B.Fn) = A₁ := by
      funext τ i j
      rfl
    rw [RingHom.id_comp, hm] at h2
    have hsq : A₁ * A₁ = A₁ := huq _ h2
    have hdet : ∀ τ, (A₁ τ).det ≠ 0 := fun τ => (hu A₁ hA₁ τ).ne_zero
    have h1 : A₁ = 1 := by
      calc A₁ = A₁⁻¹ * (A₁ * A₁) := by rw [← mul_assoc, Mat.inv_mul hdet, one_mul]
      _ = 1 := by rw [hsq, Mat.inv_mul hdet]
    have hinv : (1 : Mat Dw.mult B.Fn)⁻¹ = 1 := funext fun τ => by simp
    have halg : @algebraMap (B.X.presheaf.stalk (genericPoint B.X)) B.X.functionField _ _
        (AlgebraicGeometry.stalkFunctionFieldAlgebra (X := B.X) (genericPoint B.X)) = RingHom.id _ := by
      ext r
      show (B.X.presheaf.stalkSpecializes _).hom r = r
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    show (∀ τ, ((1 : Mat Dw.mult B.Fn) τ).det ≠ 0) ∧ ∃ (φ : c.F →+* B.X.presheaf.stalk (genericPoint B.X))
      (f : EigFrame Z φ (stalkPt B (genericPoint B.X) ≫ j ≫ genι Z)),
      f.Coord (@algebraMap (B.X.presheaf.stalk (genericPoint B.X)) B.X.functionField _ _
        (AlgebraicGeometry.stalkFunctionFieldAlgebra (X := B.X) (genericPoint B.X))) f₀ (1 : Mat Dw.mult B.Fn)⁻¹
    refine ⟨fun τ => by simp, constF e B, f₀, ?_⟩
    rw [halg, hinv, ← h1]
    exact hA₁
  · intro y A hA
    have hA' : (∀ τ, (A τ).det ≠ 0) ∧ ∃ (φ : c.F →+* B.X.presheaf.stalk y)
        (f : EigFrame Z φ (stalkPt B y ≫ j ≫ genι Z)),
        f.Coord (algebraMap (B.X.presheaf.stalk y) B.X.functionField) f₀ A⁻¹ := hA
    obtain ⟨-, φ, f, hf⟩ := hA'
    exact ⟨φ, f, by rw [one_mul]; exact hf⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
section
noncomputable section

section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.ProjBlowup

theorem eq_top_of_forall_notMem {W : Scheme.{0}} (I : W.IdealSheafData) (h : ∀ w, w ∉ I.support) : I = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, eq_bot_iff]
  exact fun w hw => (h w hw).elim

theorem effCartier_top (W : Scheme.{0}) : FinalTheorems.EffCartier (⊤ : W.IdealSheafData) := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, 1, hx, one_mem _, by simp⟩

theorem mem_support_comap {W X : Scheme.{0}} (J : X.IdealSheafData) (g : W ⟶ X) (w : W) :
    w ∈ (J.comap g).support ↔ g w ∈ J.support := by
  rw [Scheme.IdealSheafData.support_comap]; rfl

theorem exists_blowup {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hs : IsProjOver s) (J : X.IdealSheafData) :
    ∃ (X' : Scheme.{0}) (b : X' ⟶ X), FinalTheorems.Blowup b J ∧ IsProjOver (b ≫ s) ∧
      ∀ V : X.Opens, (∀ x ∈ V, x ∉ J.support) → IsIso (b ∣_ V) := by
  obtain ⟨L, m, σ, hσ⟩ := GlobalTheory.T.exists_sections_generate_ideal_projective R X s hs J
  have : IsProper (PSpace.str R m) := isProper_str R m
  have : LocallyOfFiniteType s := by
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str R n
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let U : X.Opens := J.support.compl
  have hU : ∀ x : U.toScheme, U.ι x ∉ J.support := fun x => x.2
  have htop : ∀ {W : Scheme.{0}} (g : W ⟶ X), (∀ w, g w ∉ J.support) → J.comap g = ⊤ := fun g hg =>
    eq_top_of_forall_notMem _ fun w hw => hg w ((mem_support_comap J g w).1 hw)
  obtain ⟨φ, hφ, hφσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X U _ L m σ U.ι (U.ι ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ U.ι hσ)
    (by rw [htop _ hU]; exact effCartier_top _)
  let b := graphClosure.fst s (PSpace.str R m) U.ι φ hφ.symm
  let c := graphClosure.snd s (PSpace.str R m) U.ι φ hφ.symm
  let j := graphClosure.incl s (PSpace.str R m) U.ι φ hφ.symm
  have hjb : j ≫ b = U.ι := graphClosure.incl_fst ..
  have hjc : j ≫ c = φ := graphClosure.incl_snd ..
  have hbc : Proportional σ b c := .of_comp j (by rwa [hjb, hjc])
  refine ⟨_, b, ⟨GlobalTheory.T.effCartier_of_proportional_sections R X _ U _ L m σ b c j (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ b hσ) hbc inferInstance inferInstance fun t => ?_,
    fun W g hg => ?_⟩, ?_,
    fun V hV => graphClosure.isIso_fst_restrict_of_le _ _ _ _ _ V (by rw [Scheme.Opens.opensRange_ι]; exact hV)⟩
  · rw [mem_support_comap, ← Scheme.Hom.comp_apply, hjb]; exact hU t
  · obtain ⟨ψ, hψ, hψσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X W _ L m σ g (g ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ g hσ) hg
    have hd := GlobalTheory.T.isSchemeTheoreticallyDominant_compl_effCartier W _ hg
    let d := Scheme.Opens.ι (X := W) (J.comap g).support.compl
    have hdU : ∀ t, (d ≫ g) t ∉ J.support := fun t ht => t.2 ((mem_support_comap J g _).2 ht)
    let w := IsOpenImmersion.lift U.ι (d ≫ g) (by
      rintro _ ⟨t, rfl⟩
      exact ⟨⟨_, hdU t⟩, rfl⟩)
    have hw : w ≫ U.ι = d ≫ g := IsOpenImmersion.lift_fac ..
    have hw' : d ≫ ψ = w ≫ φ := GlobalTheory.T.eq_of_proportional_to_generating_sections R X _ L m σ (d ≫ g) _ _ (htop _ hdU ▸ GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ (d ≫ g) hσ)
      (by rw [Category.assoc, hψ, Category.assoc, hφ, reassoc_of% hw]) (hψσ.comp d) (hw ▸ hφσ.comp w)
    have key : ∀ h : W ⟶ _, h ≫ b = g → d ≫ h = w ≫ j := fun h hh => by
      have H := graphClosure.isPullback_incl s (PSpace.str R m) U.ι φ hφ.symm
      have e : w ≫ U.ι = (d ≫ h) ≫ b := by rw [hw, Category.assoc, hh]
      have h1 := H.lift_fst w (d ≫ h) e
      rw [Category.comp_id] at h1
      rw [← H.lift_snd w (d ≫ h) e, h1]
    have hl := graphClosure.lift_fst s (PSpace.str R m) U.ι φ hφ.symm g ψ hψ.symm d w hw.symm hw'
    exact ⟨_, hl, fun h hh => hom_ext_of_isSchemeTheoreticallyDominant d b ((key h hh).trans (key _ hl).symm)
      (hh.trans hl.symm)⟩
  · obtain ⟨n, i, hi, e⟩ := ProjSpace.isProjOver_of_isPullback (IsPullback.of_hasPullback s (PSpace.str R m)) hs
      (ProjSpace.isProjOver_pspace_str R m)
    exact ⟨n, graphClosure.ι s (PSpace.str R m) U.ι φ hφ.symm ≫ i, inferInstance, by
      rw [Category.assoc, e, graphClosure.ι_fst_assoc]⟩

theorem exists_section_of_isIso_restrict {N X : Scheme.{0}} (f : N ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] :
    ∃ j : U.toScheme ⟶ N, IsPullback j (𝟙 _) f U.ι ∧ ((f ⁻¹ᵁ U : N.Opens) : Set N) ⊆ Set.range j := by
  have h₁ : IsPullback (inv (f ∣_ U)) (𝟙 _) (f ∣_ U) (𝟙 _) := .of_horiz_isIso ⟨by simp⟩
  have hj : IsPullback (inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι) (𝟙 _) f U.ι := by
    simpa using h₁.paste_horiz (isPullback_morphismRestrict f U).flip
  refine ⟨_, hj, fun x hx => ?_⟩
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback hj x ⟨f x, hx⟩ rfl
  exact ⟨y, hy⟩

theorem exists_normal_model {O : Type} [CommRing O] [IsDedekindDomain O] {X : Scheme.{0}} (s : X ⟶ Sp O) (V : X.Opens)
    (hs : IsProjOver s) (hV : Geo.Tor.IsNormalScheme V.toScheme) [Flat (V.ι ≫ s)]
    (hc : ∀ x : V.toScheme, CharZero (V.toScheme.residueField x)) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ X), IsFinite ν ∧ Geo.Tor.IsNormalScheme N ∧ IsProjOver (ν ≫ s) ∧ Flat (ν ≫ s) ∧
      IsIso (ν ∣_ V) ∧ Dense ((ν ⁻¹ᵁ V : N.Opens) : Set N) := by
  have : LocallyOfFiniteType s := by
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str O n
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have hN : GlobalTheory.IsNormalScheme V.toScheme := .of_pred hV
  have hfin : IsFinite V.ι.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType (o := .of O) V.ι s fun x _ => hc x
  have H := isPullback_toNormalization_of_mono (𝟙 _) V.ι V.ι (Category.id_comp _).symm
  have : Flat (V.ι.toNormalization ≫ V.ι.fromNormalization ≫ s) := by simpa
  refine ⟨_, V.ι.fromNormalization, hfin, IsNormalScheme.pred _, isProjOver_comp_of_isFinite _ hs,
    flat_normalization V.ι _, ?_, ?_⟩
  · have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict V.ι.fromNormalization V) H.flip
    rw [← e]
    infer_instance
  · refine V.ι.toNormalization.denseRange.mono ?_
    rintro _ ⟨x, rfl⟩
    change V.ι.fromNormalization (V.ι.toNormalization x) ∈ V
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact x.2

end GlobalTheory.ProjBlowup

end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.ProjBlowup

section
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem isDiscreteValuationRing_coeff {l : Level H} (c : Coeff l) (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    IsDiscreteValuationRing (c.V W) := by
  have := c.fin
  have : NumberField c.F := {}
  refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp ?_).1
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

theorem sameFlag_refl (ty : (E →+* ℂ) → Finset ℕ) {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X)
    (u : Vecs Dw t R) (hu : ∀ τ i, IsTanAtG t x (u τ i)) : SameFlag ty t x u u := by
  intro τ k _ i hi
  refine ⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne (fun e => by subst e; omega) _, ?_⟩
  refine (LieMet.isComb_iff (fun j => LieMet.tanOf (hu τ j)) (Pi.single i 1) (LieMet.tanOf (hu τ i))).2 ?_
  rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp),
    Pi.single_eq_same, one_smul]

theorem isTrans_id (i : Idx H p) (mu : SABMap (Y i).t (Y i).t (𝟙 _)) (h : mu.φ = 𝟙 _) :
    LocM.IsTrans (Y := Y) i i (𝟙 _) mu := by
  have e : spMap (RingHom.id (i.c.V W)) = 𝟙 _ := Spec.map_id _
  have H₀ : IsPullback (𝟙 _) (Y i).s (Y i).s (spMap (RingHom.id (i.c.V W))) := by
    rw [e]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨RingHom.id _, H₀.isoPullback.hom, 𝟙 _, fun _ => rfl, by simp, by simp, inferInstance, by simp,
    fun a => ?_, fun a => ?_⟩
  · rw [Nat.div_self (by have := i.l.three_le; omega), pow_one, h]; simp
  · rw [Nat.div_self i.l.A_pos, pow_one, h]; simp

theorem natImg_refl (Z : Mdl Y i₀) {k : Type} [Field k] (w : Sp k ⟶ Z.X) (hw : Set.range w ⊆ Z.opn) :
    NatImg Z Z w w := by
  obtain ⟨mu, hmu⟩ := ObjMaps.exists_sab_id (Y Z.i).t
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (Z.cover.ge (hw ⟨default, rfl⟩))
  have hA : IsAffineOpen (Z.U a).1 := (Z.U a).2
  have hr : Set.range w ⊆ Set.range hA.fromSpec := by
    rintro _ ⟨x, rfl⟩
    rw [IsAffineOpen.range_fromSpec, Subsingleton.elim x default]
    exact ha
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hA.fromSpec w hr)
  have hφ' : spMap φ.hom ≫ Z.chart a = w := by
    have := IsOpenImmersion.lift_fac hA.fromSpec w hr
    rw [← hφ] at this
    exact this
  have hf := GlobalTheory.T.isFrame_baseChange_ringHom E H Dw _ _ _ _ _ _ _ φ.hom _ _ (Z.frame a)
  rw [← Category.assoc, hφ'] at hf
  have hfl : Z.FlagAt w ((Z.fr a).bc φ.hom) :=
    ⟨a, φ.hom, hφ', hf, sameFlag_refl _ _ _ _ fun τ i => (hf.1 τ i).1⟩
  refine ⟨𝟙 _, mu, (Z.fr a).bc φ.hom, isTrans_id _ mu hmu, by simp, hfl, ?_⟩
  simpa only [hmu, Category.comp_id] using hfl

theorem exists_isNBlow (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (J : Z.Idl) :
    ∃ Z', IsNBlow Z J Z' := by
  have := isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have hs : IsProjOver Z.s := ⟨Z.n, Z.I.subschemeι, inferInstance, rfl⟩
  obtain ⟨X', b, hb, hbs, hiso⟩ := exists_blowup Z.s hs J.1
  let U : Z.X.Opens := ⨆ a, (Z.U a).1
  have hU : (U : Set Z.X) = Z.opn := by rw [← Z.cover]; exact TopologicalSpace.Opens.coe_iSup _
  have hbU := hiso U fun x hx hJ => J.2 x hJ (hU.le hx)
  have := Z.flat
  have hN : GlobalTheory.IsNormalScheme Z.X := Z.normal
  have e₀ : (b ⁻¹ᵁ U).ι ≫ b = b ∣_ U ≫ U.ι := (morphismRestrict_ι b U).symm
  have : IsOpenImmersion ((b ⁻¹ᵁ U).ι ≫ b) := by rw [e₀]; infer_instance
  have : Flat ((b ⁻¹ᵁ U).ι ≫ b ≫ Z.s) := by rw [← Category.assoc]; infer_instance
  have hV : GlobalTheory.IsNormalScheme (b ⁻¹ᵁ U).toScheme := .of_isOpenImmersion ((b ⁻¹ᵁ U).ι ≫ b)
  obtain ⟨N, ν, hfin, hn, hpr, hfl, hν, hd⟩ := exists_normal_model (b ≫ Z.s) (b ⁻¹ᵁ U) hbs hV.pred fun x => by
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show ((b ⁻¹ᵁ U).ι ≫ b) x ∈ U from x.2)
    exact charZero_of_injective_ringHom ((((b ⁻¹ᵁ U).ι ≫ b).residueFieldMap x).hom.comp
      ((Z.X.evaluation (Z.U a).1 _ ha).hom.comp (Z.alg a))).injective
  have hνb : IsIso ((ν ≫ b) ∣_ U) := by
    rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hbU
  obtain ⟨j, hj, hjr⟩ := exists_section_of_isIso_restrict (ν ≫ b) U
  have hjd : Dense (Set.range j) := hd.mono hjr
  obtain ⟨Z', e, hi, hty, hmap⟩ := GlobalTheory.T.isPullback_of_normal_flat_proj E H Dw Xo p W Y i₀ Z N (ν ≫ b) U j hU
    (by rwa [Category.assoc]) hn (by rwa [Category.assoc]) hj hjd
  refine ⟨Z', hi, hty, X', b, e.hom ≫ ν, hb, inferInstance, ?_⟩
  rw [Category.assoc]
  refine hmap Z (ν ≫ b) ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl, fun _ => subset_rfl⟩ fun k _ w => ?_
  rw [hj.w, Category.id_comp]
  refine natImg_refl Z _ ?_
  rintro _ ⟨x, rfl⟩
  exact hU.le (w x).2

end

end GlobalTheory.ProjBlowup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelZeroLogConstant
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj

namespace GlobalTheory.LineNorm

attribute [local instance] Over.cartesianMonoidalCategory

theorem fromModel_const : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (a : F) (n : ℕ), a ≠ 0 → n ≠ 0 → FromModel Y 0 (fun _ => 1) (fun _ e _ => Real.log (e.w (algebraMap F (AlgebraicClosure F) a)) / n) := by
  intro F _ _ Y a n ha hn
  obtain ⟨M, -⟩ := GlobalTheory.IntModel.exists_model F Y 0
  have ha' : algebraMap F Y.Fn a ≠ 0 := (map_ne_zero _).2 ha
  have hu (x : Y.X) : UnitAt x (algebraMap F Y.Fn a) :=
    (unitAt_iff ha').2 ⟨Y.regAt_algebraMap x a, map_inv₀ (algebraMap F Y.Fn) a ▸ Y.regAt_algebraMap x a⁻¹⟩
  have hL := LB.isLB_pull (LB.isLB_triv M.X) M.j
  refine ⟨M, LB.triv M.X, ⟨n, Nat.pos_of_ne_zero hn⟩, fun _ => Units.mk0 _ ha', LB.isLB_triv M.X,
    ⟨hL, fun i j h => ?_, fun _ x _ => ?_⟩, fun v e y yt i _ _ => ?_⟩
  · obtain rfl : i = j := Subsingleton.elim (α := PUnit → PUnit) _ _
    have := congrArg (fun u : Γ(Y.X, _)ˣ => fnOf _ h.1 u.val) (hL.g_self i)
    rw [Units.val_one, map_one] at this
    rw [← (this.symm.trans (fnOf_resG _ h.1 _)), _root_.one_mul]
  · rw [smul_zero]
    exact (CartierDiv.isEqn_zero x).iff_unitAt.2 (by simpa using hu x)
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have h := GlobalTheory.TrueGeo.OfLattice.valAt_const y.1 y.2 a
    simp only [PNat.mk_coe, inv_one, one_pow, _root_.one_mul, Units.val_mk0, h]
    field_simp

end GlobalTheory.LineNorm
end
end

