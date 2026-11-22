import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0612
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameOrbitLiftOfArc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameOrbitUnipotentOrderTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousInvariantsNorms
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBasicOpenOfMemClosure

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenFrameBasePointLiftsUniqueFlagSpace
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F]

theorem spMap_inj' {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have h1 : CommRingCat.ofHom f = CommRingCat.ofHom g := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h1

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem stalkPt_genStr (B : GlobalTheory.ProjVar.Var F) (e : F ≃+* c.F) (j : B.X ⟶ gen Z)
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) (z : B.X) (φA : c.F →+* B.X.presheaf.stalk z)
    (hφ : constF e B = (algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp φA) :
    stalkPt B z ≫ j ≫ genStr Z = spMap φA := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (stalkPt B z ≫ j ≫ genStr Z)
  have hgen : spMap (algebraMap (B.X.presheaf.stalk z) B.X.functionField) ≫ stalkPt B z = genericPt B :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec B.X).specializes trivial)
  have hpt : genericPt B ≫ B.str = spMap (algebraMap F B.Fn) := (ratOf B).pt_s
  have key : ((algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp ψ.hom).comp e.toRingHom =
      algebraMap F B.Fn := by
    apply spMap_inj'
    rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces, ← hpt, ← hj, ← hgen,
      show spMap ψ.hom = stalkPt B z ≫ j ≫ genStr Z from hψ]
    simp only [Category.assoc]
  have hψeq : ψ.hom = φA := by
    ext a
    apply IsFractionRing.injective (B.X.presheaf.stalk z) B.X.functionField
    have e1 := RingHom.congr_fun key (e.symm a)
    have e2 := RingHom.congr_fun hφ a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] at e1
    simp only [constF, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at e2
    exact e1.trans e2
  rw [← hψ, ← hψeq]
  try rfl

private theorem coord_unique' {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {φ : c.F →+* R} {φ' : c.F →+* R'} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x}
    {ψ₁ ψ₂ : R →+* R'} {g : EigFrame Z φ' x'} {M₁ M₂ : Mat Dw.mult R'} (hψ : ψ₁ = ψ₂)
    (h₁ : f.Coord ψ₁ g M₁) (h₂ : f.Coord ψ₂ g M₂) : M₁ = M₂ := by
  subst hψ
  obtain ⟨hx, hφ, -⟩ := id h₁
  exact ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ ψ₁ inferInstance
    (GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing _ _ _ _ _ _ _ _ _ _ _ _ f inferInstance) hx hφ).1 g).1.unique h₁ h₂

private theorem coord_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [IsLocalRing R'']
    {φ : c.F →+* R} {φ' : c.F →+* R'} {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X}
    {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x} {g : EigFrame Z φ' x'} {k : EigFrame Z φ'' x''}
    {ψ : R →+* R'} {ψ' : R' →+* R''} {M : Mat Dw.mult R'} {M' : Mat Dw.mult R''}
    (h₁ : f.Coord ψ g M) (h₂ : g.Coord ψ' k M') : f.Coord (ψ'.comp ψ) k (M' * M.map ψ') :=
  GlobalTheory.T.lie_eigenspace_frame_coordinates_comp _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ g _ _ _ k ψ ψ' M M' inferInstance h₁ h₂

private theorem exists_coord_unit_det_of_baseChange {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {φ : c.F →+* R} {φ' : c.F →+* R'} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x)
    (ψ : R →+* R') (hx : x' = spMap ψ ≫ x) (hφ : φ' = ψ.comp φ) (g : EigFrame Z φ' x') :
    ∃ M : Mat Dw.mult R', f.Coord ψ g M ∧ ∀ τ, IsUnit (M τ).det := by
  have H := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ ψ inferInstance
    (GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing _ _ _ _ _ _ _ _ _ _ _ _ f inferInstance) hx hφ).1 g
  obtain ⟨M, hM, -⟩ := H.1
  exact ⟨M, hM, H.2 M hM⟩

section Lifts

variable (e : F ≃+* c.F) (C : FlagCpt Z e) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
  (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn)
  (S' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn) (φ : B.Fn →ₐ[F] C.Y.Fn) (f : C.Y.X ⟶ B.X)

theorem coord_iff (hπ : C.π = f ≫ j) (hT : Tied e B j f₀ S A₀) (hT' : Tied e C.Y C.π C.f0 S' A₁)
    (hC : f₀.Coord (φ : B.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹)) (hR : Refines S S' φ f)
    {K : Type} [Field K] {χ : c.F →+* K} {x : Sp K ⟶ gen Z} (p : Sp K ⟶ C.Y.X) (hx : (p ≫ f) ≫ j = x)
    (g : EigFrame Z χ (x ≫ genι Z))
    {A : Mat Dw.mult B.Fn} (_hA : A ∈ S.S (f (p (IsLocalRing.closedPoint K))))
    {φA : c.F →+* B.X.presheaf.stalk (f (p (IsLocalRing.closedPoint K)))}
    {fA : EigFrame Z φA (stalkPt B (f (p (IsLocalRing.closedPoint K))) ≫ j ≫ genι Z)}
    (hfA : fA.Coord (algebraMap _ B.X.functionField) f₀ (A₀ * A⁻¹))
    {h : Mat Dw.mult K} (hh : fA.Coord (Scheme.stalkClosedPointTo (R := .of K) (p ≫ f)).hom g h)
    {A' : Mat Dw.mult C.Y.Fn} (hA' : A' ∈ S'.S (p (IsLocalRing.closedPoint K)))
    {φ₁ : c.F →+* C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))}
    {f₁ : EigFrame Z φ₁ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z)}
    (hf₁ : f₁.Coord (algebraMap _ C.Y.X.functionField) C.f0 (A₁ * A'⁻¹)) :
    (∀ τ, (((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p)) τ).det ≠ 0) ∧
    ∀ h' : Mat Dw.mult K, f₁.Coord (Scheme.stalkClosedPointTo (R := .of K) p).hom g h' ↔
      h = h' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) := by
  obtain ⟨hA₀g, -⟩ := id hT
  obtain ⟨hA₁g, -⟩ := id hT'
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := Fr.det_ne hA₁g
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  have hA₀φ : ∀ τ, ((A₀.map φ) τ).det ≠ 0 := by
    intro τ
    have e0 : ((A₀.map φ) τ).det = (φ : B.Fn →+* C.Y.Fn) (A₀ τ).det :=
      (RingHom.map_det (φ : B.Fn →+* C.Y.Fn) (A₀ τ)).symm
    rw [e0]
    exact (map_ne_zero _).2 (Fr.det_ne hA₀g τ)
  have hσ : (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField).comp (f.stalkMap (p (IsLocalRing.closedPoint K))).hom =
      (φ : B.Fn →+* C.Y.Fn).comp (algebraMap (B.X.presheaf.stalk (f (p (IsLocalRing.closedPoint K)))) B.X.functionField) := by
    ext a
    exact (map_algebraMap_stalk hR.hom _ a).symm
  have hxC : stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z =
      spMap (f.stalkMap (p (IsLocalRing.closedPoint K))).hom ≫ (stalkPt B (f (p (IsLocalRing.closedPoint K))) ≫ j ≫ genι Z) := by
    rw [hπ]
    show C.Y.X.fromSpecStalk _ ≫ (f ≫ j) ≫ genι Z =
      Spec.map (f.stalkMap _) ≫ B.X.fromSpecStalk _ ≫ j ≫ genι Z
    simp only [Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
  obtain ⟨-, hφf₁, -⟩ := id hf₁
  obtain ⟨-, hφfA, -⟩ := id hfA
  have hφ₁ : φ₁ = (f.stalkMap (p (IsLocalRing.closedPoint K))).hom.comp φA := by
    ext a
    apply IsFractionRing.injective (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField
    have e1 := RingHom.congr_fun hφf₁ a
    have e2 := RingHom.congr_fun hφfA a
    have e3 := RingHom.congr_fun hσ (φA a)
    simp only [RingHom.comp_apply] at e1 e2 e3 ⊢
    rw [← e1, e3, ← e2]
    simp [constF]
  obtain ⟨N, hN, hNu⟩ := exists_coord_unit_det_of_baseChange fA (f.stalkMap (p (IsLocalRing.closedPoint K))).hom hxC hφ₁ f₁
  have h2 := coord_comp' hfA hC
  have h4 := coord_comp' hN hf₁
  have h5 := coord_unique' hσ h4 h2
  rw [Mat.map_mul, Mat.map_inv] at h5
  try simp only [AlgHom.coe_toRingHom] at h5
  have hNeq : N.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) = A' * (A.map φ)⁻¹ := by
    calc N.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) = (A' * A₁⁻¹) * (A₁ * A'⁻¹ * N.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField)) := by
          simp only [← mul_assoc]
          rw [mul_assoc A' A₁⁻¹ A₁, Mat.inv_mul hA₁d, mul_one, Mat.mul_inv hA'd, one_mul]
      _ = (A' * A₁⁻¹) * (A₁ * (A₀.map φ)⁻¹ * (A₀.map φ * (A.map φ)⁻¹)) := by rw [h5]
      _ = A' * (A.map φ)⁻¹ := by
          simp only [← mul_assoc]
          rw [mul_assoc A' A₁⁻¹ A₁, Mat.inv_mul hA₁d, mul_one, mul_assoc A' (A₀.map φ)⁻¹ (A₀.map φ),
            Mat.inv_mul hA₀φ, mul_one]
  have hval : ∀ n : C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K)),
      (ratOf C.Y).val p ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n) = (Scheme.stalkClosedPointTo (R := .of K) p).hom n := by
    intro n
    calc (ratOf C.Y).val p ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n)
        = (ratOf C.Y).val (spMap (Scheme.stalkClosedPointTo (R := .of K) p).hom ≫ C.Y.X.fromSpecStalk (p (IsLocalRing.closedPoint K))) ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n) := by
          exact congrArg (fun q : Sp K ⟶ C.Y.X => (ratOf C.Y).val q ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n))
            (spMap_stalkClosedPointTo p).symm
      _ = (Scheme.stalkClosedPointTo (R := .of K) p).hom n := val_ratOf _ _
  have hM : (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) = N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom := by
    rw [← hNeq]
    funext τ
    ext a b
    exact hval (N τ a b)
  have hdetN : ∀ τ, ((N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom) τ).det ≠ 0 := by
    intro τ
    have e0 : ((N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom) τ).det = (Scheme.stalkClosedPointTo (R := .of K) p).hom (N τ).det := (RingHom.map_det (Scheme.stalkClosedPointTo (R := .of K) p).hom (N τ)).symm
    rw [e0]
    exact ((hNu τ).map _).ne_zero
  have hdetM : ∀ τ, (((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p)) τ).det ≠ 0 := by
    rw [hM]; exact hdetN
  have hev : (Scheme.stalkClosedPointTo (R := .of K) (p ≫ f)).hom = (Scheme.stalkClosedPointTo (R := .of K) p).hom.comp (f.stalkMap (p (IsLocalRing.closedPoint K))).hom := by
    rw [Scheme.stalkClosedPointTo_comp]; try rfl
  have fwd : ∀ h' : Mat Dw.mult K, f₁.Coord (Scheme.stalkClosedPointTo (R := .of K) p).hom g h' → h = h' * N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom := by
    intro h' hh'
    exact coord_unique' hev hh (coord_comp' hN hh')
  obtain ⟨hxg, hχ, -⟩ := id hh
  have hxg' : x ≫ genι Z = spMap (Scheme.stalkClosedPointTo (R := .of K) p).hom ≫ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z) := by
    rw [hxC, hxg, hev, spMap_comp_moduli_spaces, Category.assoc]
  have hχ' : χ = (Scheme.stalkClosedPointTo (R := .of K) p).hom.comp φ₁ := by
    rw [hχ, hev, hφ₁, RingHom.comp_assoc]
  obtain ⟨h'', hh'', -⟩ := exists_coord_unit_det_of_baseChange f₁ (Scheme.stalkClosedPointTo (R := .of K) p).hom hxg' hχ' g
  refine ⟨hdetM, fun h' => ⟨fun hh' => ?_, fun heq => ?_⟩⟩
  · rw [fwd h' hh', hM]
  · have e1 := fwd h'' hh''
    rw [← hM] at e1
    have e2 : h'' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) =
        h' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) := e1.symm.trans heq
    have e3 : h'' = h' := by
      calc h'' = h'' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) *
            ((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p))⁻¹ := by rw [mul_assoc, Mat.mul_inv hdetM, mul_one]
        _ = h' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) *
            ((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p))⁻¹ := by rw [e2]
        _ = h' := by rw [mul_assoc, Mat.mul_inv hdetM, mul_one]
    rw [← e3]
    exact hh''

end Lifts

theorem flagex_lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (S' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn) (φ : B.Fn →ₐ[F] C.Y.Fn) (f : C.Y.X ⟶ B.X), j ≫ genStr Z ≫ spMap e.toRingHom = B.str → C.π = f ≫ j → Tied e B j f₀ S A₀ → Tied e C.Y C.π C.f0 S' A₁ → f₀.Coord (φ : B.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → Refines S S' φ f → ∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z) (x' : Sp K ⟶ B.X), x' ≫ j = x → x ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C B j f₀ S A₀ S' A₁ φ f hj hπ hT hT' hC hR K _ χ x x' hx' hxs g
  obtain ⟨A, hA⟩ := S.nonempty (x' (IsLocalRing.closedPoint K))
  obtain ⟨-, hTie⟩ := id hT
  obtain ⟨φA, fA, hfA⟩ := hTie _ A hA
  have hx'f : spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ stalkPt B (x' (IsLocalRing.closedPoint K)) = x' := spMap_stalkClosedPointTo x'
  obtain ⟨-, hφA, -⟩ := id hfA
  have hsg := stalkPt_genStr B e j hj (x' (IsLocalRing.closedPoint K)) φA hφA
  have hχ : χ = (Scheme.stalkClosedPointTo (R := .of K) x').hom.comp φA := by
    apply spMap_inj'
    calc spMap χ = x ≫ genStr Z := hxs.symm
      _ = (x' ≫ j) ≫ genStr Z := by rw [hx']
      _ = ((spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ stalkPt B (x' (IsLocalRing.closedPoint K))) ≫ j) ≫ genStr Z := by rw [hx'f]
      _ = spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ (stalkPt B (x' (IsLocalRing.closedPoint K)) ≫ j ≫ genStr Z) := by simp only [Category.assoc]
      _ = spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ spMap φA := by rw [hsg]
      _ = spMap ((Scheme.stalkClosedPointTo (R := .of K) x').hom.comp φA) := (spMap_comp_moduli_spaces _ _).symm
  have hxg : x ≫ genι Z = spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ (stalkPt B (x' (IsLocalRing.closedPoint K)) ≫ j ≫ genι Z) := by
    calc x ≫ genι Z = (x' ≫ j) ≫ genι Z := by rw [hx']
      _ = ((spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ stalkPt B (x' (IsLocalRing.closedPoint K))) ≫ j) ≫ genι Z := by rw [hx'f]
      _ = _ := by simp only [Category.assoc]
  obtain ⟨h, hh, hu⟩ := exists_coord_unit_det_of_baseChange fA (Scheme.stalkClosedPointTo (R := .of K) x').hom hxg hχ g
  have hPar : Par (0 : (E →+* ℂ) → ℕ) ⊤ h := fun τ =>
    ⟨fun _ _ => Subring.mem_top _, (hu τ).ne_zero, Subring.mem_top _, fun i _ hi => by simp at hi⟩
  obtain ⟨p, ⟨hp1, hp2⟩, huniq⟩ := hR.lifts K x' A hA h hPar
  obtain ⟨-, hTie'⟩ := id hT'
  have key : ∀ q : Sp K ⟶ C.Y.X, q ≫ f = x' → (Bears S' φ A h q ↔ C.Carries q g) := by
    intro q hq
    subst hq
    rw [GlobalTheory.T.carriesFlags_iff_adaptedFrame_at_image _ _ _ _ _ _ _ _ _ _ e C S' A₁ K χ (x ≫ genι Z) g q hT']
    constructor
    · rintro ⟨A', hA', hPar'⟩
      obtain ⟨φ₁, f₁, hf₁⟩ := hTie' _ A' hA'
      have hci := coord_iff e C B j f₀ S A₀ S' A₁ φ f hπ hT hT' hC hR q hx' g hA hfA hh hA' hf₁
      refine ⟨A', hA', φ₁, f₁, h * ((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val q))⁻¹, hf₁, ?_, hPar'⟩
      rw [hci.2, mul_assoc, Mat.inv_mul hci.1, mul_one]
    · rintro ⟨A', hA', φ₁, f₁, h', hf₁, hh', hPar'⟩
      have hci := coord_iff e C B j f₀ S A₀ S' A₁ φ f hπ hT hT' hC hR q hx' g hA hfA hh hA' hf₁
      refine ⟨A', hA', ?_⟩
      rw [(hci.2 h').1 hh', mul_assoc, Mat.mul_inv hci.1, mul_one]
      exact hPar'
  exact ⟨p, ⟨hp1, (key p hp1).1 hp2⟩, fun q hq => huniq q ⟨hq.1, (key q hq.1).2 hq.2⟩⟩

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClosedImmersionBlowupGeneratingSections
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.AnForm.R

namespace GlobalTheory.ProjBlowup

theorem exists_blowup_graph {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hs : IsProjOver s) (J : X.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (hσ : Generates J σ) :
    ∃ (G : Scheme.{0}) (b : G ⟶ X) (c : G ⟶ PSpace R m) (hc : b ≫ s = c ≫ PSpace.str R m),
      FinalTheorems.Blowup b J ∧ Proportional σ b c ∧ IsClosedImmersion (pullback.lift b c hc) := by
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
  have hc : b ≫ s = c ≫ PSpace.str R m := graphClosure.condition ..
  have hι : pullback.lift b c hc = graphClosure.ι s (PSpace.str R m) U.ι φ hφ.symm := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]; rfl
    · rw [pullback.lift_snd]; rfl
  refine ⟨_, b, c, hc, ⟨GlobalTheory.T.effCartier_of_proportional_sections R X _ U _ L m σ b c j (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ b hσ) hbc inferInstance
    inferInstance fun t => ?_, fun W g hg => ?_⟩, hbc, ?_⟩
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
  · rw [hι]; infer_instance

theorem exists_iso_of_blowup {X X' G : Scheme.{0}} (J : X.IdealSheafData) (b : X' ⟶ X) (b₀ : G ⟶ X)
    (hb : FinalTheorems.Blowup b J) (hb₀ : FinalTheorems.Blowup b₀ J) : ∃ e : X' ⟶ G, IsIso e ∧ e ≫ b₀ = b := by
  obtain ⟨e, he, -⟩ := hb₀.2 X' b hb.1
  obtain ⟨e', he', -⟩ := hb.2 G b₀ hb₀.1
  have h1 : e ≫ e' = 𝟙 X' := by
    obtain ⟨_, -, hu⟩ := hb.2 X' b hb.1
    rw [hu (e ≫ e') (by show (e ≫ e') ≫ b = b; rw [Category.assoc, he', he]), hu (𝟙 X') (Category.id_comp _)]
  have h2 : e' ≫ e = 𝟙 G := by
    obtain ⟨_, -, hu⟩ := hb₀.2 G b₀ hb₀.1
    rw [hu (e' ≫ e) (by show (e' ≫ e) ≫ b₀ = b₀; rw [Category.assoc, he, he']), hu (𝟙 G) (Category.id_comp _)]
  exact ⟨e, ⟨e', h1, h2⟩, he⟩

theorem exists_closedImmersion_of_generates : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X X' : Scheme.{0})
    (s : X ⟶ Sp R) (J : X.IdealSheafData)
    (b : X' ⟶ X) (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec), IsProjOver s → FinalTheorems.Blowup b J →
    GlobalTheory.ProjBlowup.Generates J σ → ∃ (c : X' ⟶ PSpace R m) (hc : b ≫ s = c ≫ PSpace.str R m),
      GlobalTheory.ProjBlowup.Proportional σ b c ∧ IsClosedImmersion (pullback.lift b c hc) := by
  intro R _ _ X X' s J b L₀ m σ hs hb hσ
  obtain ⟨G, b₀, c₀, hc₀, hb₀, hp₀, hi₀⟩ := exists_blowup_graph s hs J L₀ m σ hσ
  obtain ⟨e, he, heb⟩ := exists_iso_of_blowup J b b₀ hb hb₀
  have hc : b ≫ s = (e ≫ c₀) ≫ PSpace.str R m := by rw [← heb, Category.assoc, Category.assoc, hc₀]
  have hp : Proportional σ b (e ≫ c₀) := heb ▸ hp₀.comp e
  have hl : pullback.lift b (e ≫ c₀) hc = e ≫ pullback.lift b₀ c₀ hc₀ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, heb]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
  refine ⟨e ≫ c₀, hc, hp, ?_⟩
  rw [hl]
  infer_instance

end GlobalTheory.ProjBlowup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDescendingLetterChainStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descending_letter_chain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Letter Dw), letterOf Dw st = some x → ∃ (n : ℕ) (u : Fin n → Let Dw.mult) (k : Fin n), Down u ∧ Down (u ∘ Fin.castLE k.2.le) ∧ Down (u ∘ Fin.castLE (Nat.succ_le_of_lt k.2)) ∧ u k = x ∧ ∀ (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (y : Sp C ⟶ X) (fr : Vecs Dw t C) (p : ℕ), lnStep t y fr p false st = Real.log (grNorm t y (latDR t y) (fun i => fr (u i).1 (u i).2) k) := by
  first | exact @GlobalTheory.Proof.exists_descending_letter_chain.step_position | exact GlobalTheory.Proof.exists_descending_letter_chain.step_position | (intros; apply GlobalTheory.Proof.exists_descending_letter_chain.step_position <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDlogUniqueModuloPStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dlog_unique_modulo_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (O : Type) [CommRing O] (x : Sp O ⟶ X) (p n : ℕ) (c : TorsChar t x (p ^ n)) (g : ℕ) (e : Fin g → (Sp (DualNumber O) ⟶ t.G.left)), (∀ i, IsTanAtG t x (e i)) → (∃ h : Fin g → O, DlogIs t p n c e h) ∧ ∀ h h' : Fin g → O, DlogIs t p n c e h → DlogIs t p n c e h' → ∀ i, h i - h' i ∈ Ideal.span {(p : O) ^ n} := by
  first | exact @GlobalTheory.DlogEx.dlog_exists_unique | exact GlobalTheory.DlogEx.dlog_exists_unique | (intros; apply GlobalTheory.DlogEx.dlog_exists_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagCellOfNonvanishingLeadingMinorsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagCell_of_nonvanishing_leading_minors : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (M : ℕ) (D c u : Let m → Fin (M + 1) → K) (w : Pm m), LeftInv D c → InBlock c u → (∀ τ j hj, ∑ q, lform D (wLet w ∘ std τ j hj) q * plk u (std τ j hj) q ≠ 0) → ∃ (x : CellVar m → K) (d : Let m → K), (∀ z, d z ≠ 0) ∧ Tri (cellVec c w x) u d := by
  first | exact @GlobalTheory.FlagEmb.CellLU.exists_cell | exact GlobalTheory.FlagEmb.CellLU.exists_cell | (intros; apply GlobalTheory.FlagEmb.CellLU.exists_cell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianPeriodLatticeBasisSameSignatureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianPeriodLatticeBasis_same_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw Di : Datum H) (τ : E →+* ℂ), Di.p = Dw.p ∧ Di.q = Dw.q → ∃ (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E), IsPerBasis Di x hm := by
  first | exact @GlobalTheory.ShFam.Hor.PerBasis.exists_isPerBasis | exact GlobalTheory.ShFam.Hor.PerBasis.exists_isPerBasis | (intros; apply GlobalTheory.ShFam.Hor.PerBasis.exists_isPerBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameOrbitLiftOfArcStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphicFrameOrbit_lift_of_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → ∃ (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), (∀ w : ℂ, T < w.im → eTwoPi w ∈ Metric.ball (0 : ℂ) r) ∧ IsOrbit (U.X k) T M γ xx ∧ IsLift U k y T xx := by
  first | exact @GlobalTheory.ShFam.ArcLift.exists_orbit_lift | exact GlobalTheory.ShFam.ArcLift.exists_orbit_lift | (intros; apply GlobalTheory.ShFam.ArcLift.exists_orbit_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameOrbitUnipotentOrderTwoStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphicFrameOrbit_unipotent_order_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N), IsOrbit X T M γ x → ∃ (M' : ℕ) (γ' : GL (Fin N) E), IsOrbit X T M' γ' x ∧ ((γ' : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 := by
  first | exact @GlobalTheory.ShFam.OrbitUnip.exists_isOrbit_unipotent | exact GlobalTheory.ShFam.OrbitUnip.exists_isOrbit_unipotent | (intros; apply GlobalTheory.ShFam.OrbitUnip.exists_isOrbit_unipotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousInvariantsNormsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_invariants_norms : ∀ (A A' : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [CommRing A'] [IsDomain A'] [Algebra A A'] [Module.Finite A A'], Function.Injective (algebraMap A A') → ∀ (σ J : Type) [Fintype σ] [Fintype J] (ℓ : J → σ → A'), ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial σ A), (∀ i, (B i).IsHomogeneous d) ∧ ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] (x : A →+* C) (T : σ → C) (N : ℝ), (∀ x' : A' →+* C, x'.comp (algebraMap A A') = x → (⨆ j, ‖∑ s, x' (ℓ j s) * T s‖) = N) → N ^ (d : ℕ) = ⨆ i, ‖MvPolynomial.eval₂ x T (B i)‖ := by
  first | exact @GlobalTheory.NormFam.norm_of_family | exact GlobalTheory.NormFam.norm_of_family | (intros; apply GlobalTheory.NormFam.norm_of_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralFlagCellOfValuedFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_flagCell_of_valuedField : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (A : ValuationSubring K) (M : ℕ) (c u : Let m → Fin (M + 1) → K), InBlock c u → (∀ τ, LinearIndependent K fun j : Fin (m τ) => u ⟨τ, j⟩) → ∃ (w : Pm m) (x : CellVar m → K) (d : Let m → K), (∀ v, x v ∈ A) ∧ (∀ z, d z ≠ 0) ∧ Tri (cellVec c w x) u d := by
  first | exact @GlobalTheory.FlagEmb.exists_integral_cell | exact GlobalTheory.FlagEmb.exists_integral_cell | (intros; apply GlobalTheory.FlagEmb.exists_integral_cell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsProjOverFiniteFibreProductStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isProjOver_finite_fibreProduct : ∀ (O : Type) [CommRing O] (ι : Type) [Finite ι] (X : Scheme.{0}) (s : X ⟶ Sp O) (Y : ι → Scheme.{0}) (f : ∀ i, Y i ⟶ Sp O), IsProjOver s → (∀ i, IsProjOver (f i)) → ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ i, P ⟶ Y i), IsProjOver (p0 ≫ s) ∧ (∀ i, p i ≫ f i = p0 ≫ s) ∧ ∀ (Z : Scheme.{0}) (a : Z ⟶ X) (b : ∀ i, Z ⟶ Y i), (∀ i, b i ≫ f i = a ≫ s) → ∃! h : Z ⟶ P, h ≫ p0 = a ∧ ∀ i, h ≫ p i = b i := by
  first | exact @GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod | exact GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod | (intros; apply GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsProjOverIsIsoMorphismRestrict
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ChowLemma

theorem exists_dominant_lift {X X' : Scheme.{0}} (π : X' ⟶ X) {U W : X.Opens} (h : U ≤ W)
    (t : U.toScheme ⟶ X') [IsDominant t] (ht : t ≫ π = U.ι) :
    ∃ σ : U.toScheme ⟶ (π ⁻¹ᵁ W).toScheme, IsDominant σ ∧ σ ≫ (π ⁻¹ᵁ W).ι = t ∧
      σ ≫ π ∣_ W = X.homOfLE h := by
  have hr : Set.range t ⊆ Set.range (π ⁻¹ᵁ W).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change π (t x) ∈ W
    rw [← Scheme.Hom.comp_apply, ht]
    exact h x.2
  have e := IsOpenImmersion.lift_fac (π ⁻¹ᵁ W).ι t hr
  refine ⟨IsOpenImmersion.lift (π ⁻¹ᵁ W).ι t hr, ?_, e, ?_⟩
  · have : IsDominant (IsOpenImmersion.lift (π ⁻¹ᵁ W).ι t hr ≫ (π ⁻¹ᵁ W).ι) := by
      rwa [e]
    exact IsDominant.of_comp_of_isOpenImmersion _ (π ⁻¹ᵁ W).ι
  · rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, reassoc_of% e, ht, X.homOfLE_ι]

theorem exists_isProjOver_isIso_morphismRestrict : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp R) [IsProper f], ∃ (X' : Scheme.{0}) (π : X' ⟶ X) (U : X.Opens), IsProjOver (π ≫ f) ∧ (U : Set X).Nonempty ∧ IsIso (π ∣_ U) := by
  first
  | exact @_root_.GlobalTheory.BasicOpenLocalExtension.chow_integral
  | exact _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral
  | (apply _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> assumption)
  | (intros; apply _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BasicOpenLocalExtension.chow_integral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BasicOpenLocalExtension.chow_integral ..)

end GlobalTheory.ChowLemma
end

