import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2269
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaEqOfMkEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
set_option autoImplicit false
noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

def ValAt {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {V : Scheme.{0}} (ℓ : V ⟶ X') {M : Type}
    (w : M → (V ⟶ G.left)) (p : (torsion G n).left) (c : M) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Sp Ω ⟶ Spec ((torsion G n).left.presheaf.stalk p)) (z : Sp Ω ⟶ V),
    y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion G n).hom = z ≫ ℓ →
      y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion.ι G n).left = z ≫ w c

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem etaSec_w (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (b : Dw.La) :
    (i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ) ≫ TF.Y.t.G.hom = ℓ ≫ φ ≫ (barComp TF.Y Z).ι := by
  have h1 := TF.Y.m.cart.1.w
  have h2 := Over.w (TF.Y.oF.eta b)
  simp only [Category.assoc] at h1 ⊢
  rw [h1, ← Category.assoc ((TF.Y.oF.eta b).left), h2, reassoc_of% hℓ, j₀_ι]
  exact congrArg (i₀ TF.Y Z ≫ ·) (Category.id_comp _)

def etaSec (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (b : Dw.La) : V₀ TF.Y Z ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left :=
  pullback.lift _ _ (etaSec_w TF Z φ ℓ hℓ b)

theorem eta_eq_of_mk_eq (TF : TorFlag Xo c) {b b' : Dw.La}
    (h : (Submodule.Quotient.mk b : LevelMod Dw l) = Submodule.Quotient.mk b') :
    TF.Y.oF.eta b = TF.Y.oF.eta b' := by
  rw [Submodule.Quotient.eq] at h
  have := TF.Y.oF.eta_add b' (b - b')
  rwa [add_sub_cancel, TF.Y.oF.eta_ker _ h, mul_one] at this

def etaSecL (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (x : LevelMod Dw l) : V₀ TF.Y Z ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left :=
  Quot.liftOn x (etaSec TF Z φ ℓ hℓ) fun b b' h => by
    have e := eta_eq_of_mk_eq TF (b := b) (b' := b') (Quot.sound h)
    unfold etaSec
    congr 2
    rw [e]

theorem etaSecL_w (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (x : LevelMod Dw l) :
    etaSecL TF Z φ ℓ hℓ x ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom = ℓ := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact pullback.lift_snd _ _ _

theorem etaSecL_ψ (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (b : Dw.La) :
    etaSecL TF Z φ ℓ hℓ (Submodule.Quotient.mk b) ≫ GlobalTheory.EqvAct.pullψ TF Z φ =
      i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ :=
  pullback.lift_fst _ _ _

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMvPolynomialEval2HomRestrictSmallerAffines
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.EtaleRestrict

theorem etale_eval₂_res : ∀ (X Y : Scheme.{0}) (q : Y ⟶ X) (ι : Type) (U U' : X.Opens) (hU' : U' ≤ U), IsAffineOpen U → IsAffineOpen U' → ∀ (W W' : Y.Opens) (hW' : W' ≤ W), IsAffineOpen W → IsAffineOpen W' → ∀ (hWU : W ≤ q ⁻¹ᵁ U) (hW'U' : W' ≤ q ⁻¹ᵁ U') (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N).Etale → (MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))).Etale := by
  intro X Y q ι U U' hU' hU hU'a W W' hW' hW hW'a hWU hW'U' N hN
  have h1 : (resG Y hW').Etale := GlobalTheory.TopForm.etale_resG hW hW'a hW'
  have h2 : ((resG Y hW').comp (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N)).Etale :=
    RingHom.Etale.stableUnderComposition _ _ hN h1
  have h3 : (resG X hU').Etale := GlobalTheory.TopForm.etale_resG hU hU'a hU'
  have h4 : (MvPolynomial.map (σ := ι) (resG X hU')).Etale := by
    algebraize [resG X hU']
    letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := Γ(X, U)) (S := Γ(X, U'))
    exact RingHom.Etale.isStableUnderBaseChange Γ(X, U) Γ(X, U') (MvPolynomial ι Γ(X, U)) (MvPolynomial ι Γ(X, U')) h3
  have h5 : (MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))).comp
      (MvPolynomial.map (resG X hU')) = (resG Y hW').comp (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE,
        ← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    · intro i
      simp
  rw [← h5] at h2
  algebraize [MvPolynomial.map (σ := ι) (resG X hU'),
    MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a)),
    (MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))).comp
      (MvPolynomial.map (resG X hU'))]
  exact Algebra.Etale.of_restrictScalars (R := MvPolynomial ι Γ(X, U)) _ _

end GlobalTheory.EtaleRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFormallyUnramifiedStandardSmoothSameRelDi
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem etale_of_formallyUnramified_of_relDim : ∀ (A B C : Type) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (g : ℕ),
    Algebra.IsStandardSmoothOfRelativeDimension g A B →
    Algebra.IsStandardSmoothOfRelativeDimension g A C →
    Algebra.FormallyUnramified B C → Algebra.Etale B C := by
  intro A B C _ _ _ _ _ _ _ g hB hC hU
  have : Algebra.IsStandardSmooth A B := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : Algebra.IsStandardSmooth A C := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have hs : Function.Surjective (KaehlerDifferential.mapBaseChange A B C) := fun x =>
    (KaehlerDifferential.exact_mapBaseChange_map A B C x).mp (Subsingleton.elim _ _)
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange A B C) := by
    rcases subsingleton_or_nontrivial C with hC0 | hC0
    · intro x y _
      exact Subsingleton.elim (α := TensorProduct B C Ω[B⁄A]) x y
    · have : Nontrivial B := (algebraMap B C).domain_nontrivial
      have : Module.Free B Ω[B⁄A] := Algebra.IsStandardSmooth.free_kaehlerDifferential
      have : Module.Free C Ω[C⁄A] := Algebra.IsStandardSmooth.free_kaehlerDifferential
      have hr : Module.rank C Ω[C⁄A] = Module.rank C (TensorProduct B C Ω[B⁄A]) := by
        rw [Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g, Module.rank_baseChange,
          Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g]
        simp
      obtain ⟨e⟩ := nonempty_linearEquiv_of_rank_eq hr
      have h2 : Function.Surjective (e.toLinearMap ∘ₗ KaehlerDifferential.mapBaseChange A B C) :=
        e.surjective.comp hs
      have h3 := OrzechProperty.injective_of_surjective_endomorphism _ h2
      exact fun x y hxy => h3 (by simp [hxy])
  have : Algebra.FormallySmooth B C := by
    rw [Algebra.formallySmooth_iff]
    constructor
    · exact Module.Projective.of_free
    · refine subsingleton_of_forall_eq 0 fun x => ?_
      have h₁ : Algebra.H1Cotangent.δ A B C x = 0 := by
        apply hinj
        rw [map_zero]
        exact (Algebra.H1Cotangent.exact_δ_mapBaseChange A B C).apply_apply_eq_zero x
      obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ A B C x).mp h₁
      rw [Subsingleton.elim y 0, map_zero]
  have : Algebra.FormallyEtale B C := Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
  have : Algebra.FinitePresentation B C := Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A B C
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvcCompOfIso
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ProdGlue

theorem evc_comp_of_iso {S : Scheme.{0}} {A B' B Y : Over S} (j : B' ⟶ B) {P : LB (A ⊗ B).left} (hP : P.IsLB)
    {Q : LB (A ⊗ B').left} (hQ : Q.IsLB) (h : LBIso (P.pull (A ◁ j).left) Q) (a : Y ⟶ A) (u : Y ⟶ B') :
    evc hP a (u ≫ j) = evc hQ a u := by
  have e : cls Q hQ = CechPic.pull (A ◁ j).left (cls P hP) :=
    ((cls_eq_iff (pull_isLB hP _) hQ).2 h).symm.trans (cls_pull hP _ _)
  rw [evc, evc, e, ← pull_comp, ← Over.comp_left, lift_whiskerLeft]

end GlobalTheory.DualCon.ProdGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineHolFrames
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.ShFam.HolFrames

theorem exists_affine_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) {T : Scheme.{0}} (io : T ⟶ gen Y) (y : T) :
    ∃ (W : T.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(T, W))
      (_ : EigFrame Y φ (((show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io) ≫ genι Y)),
      y ∈ W ∧ ((show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io) ≫ genStr Y = spMap φ := by
  obtain ⟨U, hU, φ, f, hy, hφ, -⟩ := GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H D l Xo c O β Y (io y)
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWU⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (a := y) (u := (io ⁻¹ᵁ U : T.Opens)) hy (io ⁻¹ᵁ U).2
  have hW : IsAffineOpen W := hW
  have e : (show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io =
      spMap (io.appLE U W hWU).hom ≫ (show Sp Γ(gen Y, U) ⟶ gen Y from hU.fromSpec) :=
    (IsAffineOpen.SpecMap_appLE_fromSpec io hU hW hWU).symm
  obtain ⟨g, -⟩ := exists_bc f (io.appLE U W hWU).hom (φ' := (io.appLE U W hWU).hom.comp φ)
    (x' := ((show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io) ≫ genι Y) rfl (by rw [e, Category.assoc])
  refine ⟨W, hW, _, g, hyW, ?_⟩
  rw [e, Category.assoc, spMap_comp₂]
  exact congrArg _ hφ

open GlobalTheory.Points GlobalTheory.ShFam.EigLoc in

theorem exists_affine_holFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (e : c.F →+* ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsOpenImmersion io → io ≫ genStr Y = B.str → ∃ (W : B.X → B.X.Opens) (hW : ∀ y, IsAffineOpen (W y)) (φ : ∀ y, c.F →+* Γ(B.X, W y)) (fr : ∀ y, EigFrame Y (φ y) (((show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) ≫ io) ≫ genι Y)) (a : B.X → GlobalTheory.CxPts B.str e → CxFr Y e), (∀ y, y ∈ W y) ∧ (∀ y, ((show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) ≫ io) ≫ genStr Y = spMap (φ y)) ∧ (∀ y p, (a y p).1.1 = p.1 ≫ io) ∧ (∀ y p (h : p ∈ GlobalTheory.CxPts.ptsIn B.str e (W y)) ρ i, (a y p).2.v ρ i = spMap (Chart.dualMapR (GlobalTheory.CxPts.evHom h)) ≫ (fr y).v ρ i) ∧ ∀ y (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (A : Set V) (x : V → GlobalTheory.CxPts B.str e), IsOpen A → IsHolTo A (fun b => (x b).1) → Set.MapsTo x A (GlobalTheory.CxPts.ptsIn B.str e (W y)) → HolFam A (fun b => a y (x b)) := by
  intro E _ _ _ H D l Xo c O _ β Y e B io _ hio
  choose U hU φ fr hy hφ using fun y => exists_affine_frame Y io y
  have hov : ∀ p : GlobalTheory.CxPts B.str e, (p.1 ≫ io) ≫ genStr Y = spMap e := fun p => by
    rw [Category.assoc, hio, p.2]
  have hp : ∀ y (p : GlobalTheory.CxPts B.str e) (h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y)),
      spMap (GlobalTheory.CxPts.evHom h) ≫ (show Sp Γ(B.X, U y) ⟶ B.X from (hU y).fromSpec) = p.1 := fun y p h =>
    specMap_valMap_fromSpec (hU y) p.1 h
  have hx : ∀ y (p : GlobalTheory.CxPts B.str e) (h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y)), (p.1 ≫ io) ≫ genι Y =
      spMap (GlobalTheory.CxPts.evHom h) ≫ ((show Sp Γ(B.X, U y) ⟶ B.X from (hU y).fromSpec) ≫ io) ≫ genι Y := fun y p h => by
    rw [← hp y p h]
    simp only [Category.assoc]
  have ex : ∀ y (p : GlobalTheory.CxPts B.str e), ∃ g : EigFrame Y e ((p.1 ≫ io) ≫ genι Y),
      ∀ h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y), ∀ ρ i,
        g.v ρ i = spMap (Chart.dualMapR (GlobalTheory.CxPts.evHom h)) ≫ (fr y).v ρ i := fun y p => by
    by_cases h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y)
    · obtain ⟨g, hg⟩ := exists_bc (fr y) (GlobalTheory.CxPts.evHom h) (φ' := e) (spMap_inj (by
        rw [spMap_comp₂, ← hφ y, ← hov p, ← hp y p h]
        simp only [Category.assoc])) (hx y p h)
      exact ⟨g, fun _ => hg⟩
    · obtain ⟨g⟩ := exists_eigFrame E H D l Xo c O β Y ℂ e _ (hov p)
      exact ⟨g, fun h' => (h h').elim⟩
  choose g hg using ex
  refine ⟨U, hU, φ, fr, fun y p => ⟨⟨p.1 ≫ io, hov p⟩, g y p⟩, hy, hφ, fun _ _ => rfl, hg,
    fun y V _ _ _ A x hA hol hm => ⟨fun W f => by
      simp only [valAt'_eq_valR, valR_comp]
      exact hol (io ⁻¹ᵁ W) ((io.app W).hom f), fun ρ i => ?_⟩⟩
  exact holTan_dualMap hA ((fr y).v ρ i) (fun b hb => GlobalTheory.CxPts.evHom (hm hb)) (fun a => ⟨_,
    (hol (U y) a).2.mono fun b hb => ⟨hb, hm hb⟩, fun b hb => (GlobalTheory.CxPts.ev_eq (hm hb) a).symm⟩)
    fun b hb => hg y _ (hm hb) ρ i

end GlobalTheory.ShFam.HolFrames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineIntersectionCharts
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue

theorem chart_inter_factor : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → ∀ (R1 R2 : Type) [CommRing R1] [CommRing R2] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X), IsOpenImmersion ξ1 → IsOpenImmersion ξ2 → ∃ (A : Type) (_ : CommRing A) (w : Sp A ⟶ X) (a1 : R1 →+* A) (a2 : R2 →+* A), IsOpenImmersion w ∧ spMap a1 ≫ ξ1 = w ∧ spMap a2 ≫ ξ2 = w ∧ Set.range w = Set.range ξ1 ∩ Set.range ξ2 := by
  intro R _ X s hP R1 R2 _ _ ξ1 ξ2 h1 h2
  obtain ⟨N, i, hi, hs⟩ := hP
  have : IsProper (PSpace.str R N) := isProper_str R N
  have : IsProper s := by rw [← hs]; infer_instance
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from s]; infer_instance⟩
  have hU : IsAffineOpen (ξ1.opensRange ⊓ ξ2.opensRange) :=
    (isAffineOpen_opensRange ξ1).inf (isAffineOpen_opensRange ξ2)
  have hr1 : Set.range hU.fromSpec.base ⊆ Set.range ξ1.base := by
    rw [hU.range_fromSpec]; intro x hx; exact hx.1
  have hr2 : Set.range hU.fromSpec.base ⊆ Set.range ξ2.base := by
    rw [hU.range_fromSpec]; intro x hx; exact hx.2
  refine ⟨Γ(X, ξ1.opensRange ⊓ ξ2.opensRange), inferInstance, hU.fromSpec,
    (Spec.preimage (IsOpenImmersion.lift ξ1 hU.fromSpec hr1)).hom,
    (Spec.preimage (IsOpenImmersion.lift ξ2 hU.fromSpec hr2)).hom, inferInstance, ?_, ?_, ?_⟩
  · simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  · simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  · show Set.range hU.fromSpec.base = _
    rw [hU.range_fromSpec]
    rfl

end GlobalTheory.UnitGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffinePreimageLe
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Tube

theorem exists_affine_preimage_le :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) [UniversallyClosed f] (s : S) (W : X.Opens), (∀ x, f x = s → x ∈ W) → ∃ U : S.Opens, IsAffineOpen U ∧ s ∈ U ∧ f ⁻¹ᵁ U ≤ W := by
  intro X S f _ s W hW
  have hc : IsClosed (f '' (W : Set X)ᶜ) := f.isClosedMap _ W.isOpen.isClosed_compl
  have hs : s ∈ (f '' (W : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, rfl⟩
    exact hx (hW x rfl)
  obtain ⟨U, hU, hsU, hUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show s ∈ (⟨_, hc.isOpen_compl⟩ : S.Opens) from hs)
  refine ⟨U, hU, hsU, fun x hx => ?_⟩
  by_contra hxW
  exact hUV hx ⟨x, hxW, rfl⟩

end GlobalTheory.Tube
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAveragingProjectionBalancedFormsStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_averaging_projection_balancedForms : ∀ (O : Type) [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] (n c : ℕ) (b : Fin n → O) (T : Matrix (Fin n) (Fin n) ℤ), 0 < c → (∀ s t, T s t = T t s) → (∀ (a : O) (g : O →ₗ[ℤ] O →ₗ[ℤ] ℤ), ∑ s, ∑ t, T s t * g (b s * a) (b t) = ∑ s, ∑ t, T s t * g (b s) (b t * bar a)) → ∑ s, ∑ t, T s t • (bar (b s) * b t) = (c : O) → (∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ s, ∑ t, T s t * v s * v t) → ∃ P : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X, (∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → P β ∈ GlobalTheory.PolFan.balForms bar X) ∧ (∀ β ∈ GlobalTheory.PolFan.balForms bar X, P β = (c : ℤ) • β) ∧ ∀ l : X →ₗ[ℤ] ℤ, l ≠ 0 → P (GlobalTheory.PolFan.sqForm l) ≠ 0 ∧ ∀ x, 0 ≤ P (GlobalTheory.PolFan.sqForm l) x x := by
  first | exact @GlobalTheory.Poinc.exists_avg_proj_balForms | exact GlobalTheory.Poinc.exists_avg_proj_balForms | (intros; apply GlobalTheory.Poinc.exists_avg_proj_balForms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenAffineOpenMeetingFibresGrpScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.chartAroundUnit (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (s : Sp R) :
    ∃ f : R, s ∈ Set.range (spMap (algebraMap R (Localization.Away f))) ∧ ∃ W : A.left.Opens,
      IsAffineOpen W ∧ ∀ t ∈ Set.range (spMap (algebraMap R (Localization.Away f))),
        ∃ x ∈ W, A.hom x = t := by
  let e : Sp R ⟶ A.left := (η[A]).left
  have he : e ≫ A.hom = 𝟙 (Sp R) := Over.w (η[A])
  have hpt : ∀ t : Sp R, A.hom (e t) = t := by
    intro t
    rw [← Scheme.Hom.comp_apply, he]
    rfl
  obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := e s) trivial
  have hrange : ∀ f : R, Set.range (spMap (algebraMap R (Localization.Away f))) =
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
    intro f
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have hopen : IsOpen (e ⁻¹' (W : Set A.left)) := W.isOpen.preimage e.continuous
  obtain ⟨_, ⟨f, rfl⟩, hsf, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      (a := s) hsW hopen
  refine ⟨f, ?_, W, hW, ?_⟩
  · rw [hrange]; exact hsf
  · intro t ht
    rw [hrange] at ht
    exact ⟨e t, hsub ht, hpt t⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCellChoose
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem GlobalTheory.LogPole.exists_basicOpen_cell_choose : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J), W ≤ toBase TF Z ⁻¹ᵁ U.1 → W ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k → Nonempty W → ∃ a : Γ(TF.Y.X, U.1), TF.Y.X.basicOpen a ≤ LogKS.interior TF.Y ⊓ barComp TF.Y Z ⊓ (TF.X.F.M k).U ∧ ∃ w : Y₀ TF.X Z, w ∈ W ∧ w ∈ U₀ TF.X Z ∧ toBase TF Z w ∈ TF.Y.X.basicOpen a := by
  intro E _ _ _ H Dw l Xo c TF Z U W k hWU hWk hW
  obtain ⟨⟨w₁, hw₁⟩⟩ := hW
  obtain ⟨w, hwW, hw0⟩ := (dense_U₀ TF.X Z).inter_open_nonempty (W : Set (Y₀ TF.X Z)) W.isOpen ⟨w₁, hw₁⟩
  have hcomp : toBase TF Z w = TF.X.π w.1 := Scheme.Hom.comp_apply _ _ _
  have hU : toBase TF Z w ∈ U.1 := hWU hwW
  have hI : toBase TF Z w ∈ LogKS.interior TF.Y := by
    rw [hcomp]; exact hw0
  have hB : toBase TF Z w ∈ barComp TF.Y Z := by
    rw [hcomp]; exact w.2
  have hM : toBase TF Z w ∈ (TF.X.F.M k).U := by
    rw [hcomp]; exact TF.X.F.le k (hWk hwW)
  obtain ⟨a, ha, hxa⟩ := U.2.exists_basicOpen_le
    (V := LogKS.interior TF.Y ⊓ barComp TF.Y Z ⊓ (TF.X.F.M k).U) ⟨toBase TF Z w, ⟨⟨hI, hB⟩, hM⟩⟩ hU
  exact ⟨a, ha, w, hwW, hw0, hxa⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenNbhdPointMemOpenStatement
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_nbhd_point_mem_open : ∀ (S : Type) [CommRing S] (X : Scheme.{0}) (x : Sp S ⟶ X) (V : X.Opens) (q : PrimeSpectrum S), x q ∈ V → ∃ f₀ : S, f₀ ∉ q.asIdeal ∧ ⊤ ≤ (spMap (algebraMap S (Localization.Away f₀)) ≫ x) ⁻¹ᵁ V := by
  first | exact @GlobalTheory.nbhd_basicOpen_of_mem | exact GlobalTheory.nbhd_basicOpen_of_mem | (intros; apply GlobalTheory.nbhd_basicOpen_of_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenTopFormFrameOfStalkKaehlerBasis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.FrameSpread

open GlobalTheory.TopForm

theorem exists_basicOpen_isFrame_dOn : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x₀ : X) (hx : x₀ ∈ U.1) (x : Fin n → Γ(X, U.1)), (letI := ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1)).toAlgebra; ∃ bs : Module.Basis (Fin n) (X.presheaf.stalk x₀) Ω[X.presheaf.stalk x₀⁄k], ∀ i, bs i = KaehlerDifferential.D k (X.presheaf.stalk x₀) ((X.presheaf.germ U.1 x₀ hx).hom (x i))) → ∃ s : Γ(X, U.1), x₀ ∈ X.basicOpen s ∧ GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p fun i => resG X (X.basicOpen_le s) (x i)) := by
  intro k _ X p n _ U x₀ hx x hbs
  obtain ⟨V, ω, hxV, hω⟩ := TopForm.exists_isFrame p n x₀
  obtain ⟨s, hsV, hxs⟩ := U.2.exists_basicOpen_le ⟨x₀, hxV⟩ hx
  have hWU : X.basicOpen s ≤ U.1 := X.basicOpen_le s
  have hWaff : IsAffineOpen (X.basicOpen s) := U.2.basicOpen s
  have hωW := hω.res hWaff hsV
  set η : FormsOn p n (X.basicOpen s) := TopForm.dOn p (fun i => resG X hWU (x i)) with hη
  set J : Γ(X, X.basicOpen s) := hωW.gen.repr η with hJdef
  have hJ : J • TopForm.resForm hsV ω = η := hωW.gen.repr_smul η
  obtain ⟨bs, hbs⟩ := hbs
  set ρ : Γ(X, X.basicOpen s) →+* X.presheaf.stalk x₀ := (X.presheaf.germ (X.basicOpen s) x₀ hxs).hom with hρ
  have hgerm : ∀ a : Γ(X, U.1), ρ (resG X hWU a) = (X.presheaf.germ U.1 x₀ hx).hom a := fun a => by
    have := TopCat.Presheaf.germ_res X.presheaf (homOfLE hWU) x₀ hxs
    exact congrArg (fun φ => (ConcreteCategory.hom φ) a) this
  have hρα : ρ.comp (algX p (X.basicOpen s)) = (X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1) := by
    rw [← resG_comp_algX p hWU]
    ext a
    exact hgerm _
  have hfe : letI := ρ.toAlgebra; Algebra.FormallyEtale Γ(X, X.basicOpen s) (X.presheaf.stalk x₀) := by
    letI := ρ.toAlgebra
    haveI := hWaff.isLocalization_stalk ⟨x₀, hxs⟩
    exact Algebra.FormallyEtale.of_isLocalization (hWaff.primeIdealOf ⟨x₀, hxs⟩).asIdeal.primeCompl
  have h1 : IsFreeGen (X.presheaf.stalk x₀) (TopForm.formMap n ρ hρα (TopForm.resForm hsV ω)) := by
    letI := (algX p (X.basicOpen s)).toAlgebra
    letI := ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1)).toAlgebra
    letI := ρ.toAlgebra
    haveI : IsScalarTower k Γ(X, X.basicOpen s) (X.presheaf.stalk x₀) :=
      IsScalarTower.of_algebraMap_eq' hρα.symm
    haveI : Algebra.FormallyEtale Γ(X, X.basicOpen s) (X.presheaf.stalk x₀) := hfe
    exact hωW.gen.of_isBaseChange (isBaseChange_exteriorPower
      (KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, X.basicOpen s) (X.presheaf.stalk x₀)) n)
  have h2 : IsFreeGen (X.presheaf.stalk x₀)
      (dForm ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1))
        (fun i => (X.presheaf.germ U.1 x₀ hx).hom (x i))) :=
    isFreeGen_dForm _ bs hbs
  have h3 : TopForm.formMap n ρ hρα η = ρ J • TopForm.formMap n ρ hρα (TopForm.resForm hsV ω) := by
    rw [← hJ, map_smulₛₗ]
  have h4 : TopForm.formMap n ρ hρα η = dForm ((X.presheaf.germ U.1 x₀ hx).hom.comp (algX p U.1))
      (fun i => (X.presheaf.germ U.1 x₀ hx).hom (x i)) := by
    rw [hη, dOn, formMap_dForm]
    simp only [hgerm]
  have hu : IsUnit (ρ J) := h1.smul_iff.1 (h3 ▸ h4 ▸ h2)
  have hxJ : x₀ ∈ X.basicOpen J := (X.mem_basicOpen J x₀ hxs).2 hu
  obtain ⟨t, htJ, hxt⟩ := U.2.exists_basicOpen_le ⟨x₀, hxJ⟩ hx
  refine ⟨t, hxt, ?_⟩
  have hJW : X.basicOpen J ≤ X.basicOpen s := X.basicOpen_le J
  have hte : X.basicOpen t ≤ X.basicOpen s := htJ.trans hJW
  have hframe := hωW.res (U.2.basicOpen t) hte
  have e : TopForm.dOn p (fun i => resG X (X.basicOpen_le t) (x i)) =
      resG X hte J • TopForm.resForm hte (TopForm.resForm hsV ω) := by
    rw [← resForm_smul, hJ, hη, resForm_dOn]
    simp only [resG_resG]
  rw [e]
  refine ⟨U.2.basicOpen t, hframe.gen.smul_iff.2 ?_⟩
  have hu' : IsUnit (resG X hJW J) := X.toRingedSpace.isUnit_res_basicOpen J
  have := hu'.map (resG X htJ)
  rwa [resG_resG] at this

end GlobalTheory.FrameSpread
end

