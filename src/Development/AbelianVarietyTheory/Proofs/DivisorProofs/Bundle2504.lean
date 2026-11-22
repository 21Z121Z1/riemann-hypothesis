import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2444
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermOriginConstantSectionEqOriginStalkConstants
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GermConst

theorem germ_constFn_origin : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (O : G.left.Opens) (hO : origin G ∈ O) (r : R), (G.left.presheaf.germ O (origin G) hO).hom (constFn G.hom O r) = constO G r := by
  intro R _ _ G _ O hO r
  have e := Scheme.Hom.appLE_map G.hom (U := ⊤) (V := ⊤) (fun _ _ => trivial) (homOfLE (le_top : O ≤ ⊤)).op
  have h : constFn G.hom O r = (G.left.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom (constFn G.hom ⊤ r) := by
    unfold constFn
    rw [← e]
    rfl
  rw [h, TopCat.Presheaf.germ_res_apply]
  rfl

end GlobalTheory.GermConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsAreConstantAbelianSchemeNoetheriaStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalFunctionsAreConstant_abelianScheme_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → Const A.hom := by
  first | exact @GlobalTheory.LiftSys.const_of_isAbelianScheme | exact GlobalTheory.LiftSys.const_of_isAbelianScheme | (intros; apply GlobalTheory.LiftSys.const_of_isAbelianScheme <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormEqZeroOfAffineCoverRestrictions
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverForms

open KaehlerDifferential

theorem exists_pow_smul_eq_zero {R C B : Type} [CommRing R] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra R B] (g : C →ₐ[R] B) (f : C)
    (hloc : @IsLocalization.Away C _ f B _ g.toRingHom.toAlgebra)
    (L : Ω[C⁄R] →ₗ[R] Ω[B⁄R]) (hD : ∀ c, L (D R C c) = D R B (g c))
    (hs : ∀ (c : C) (α : Ω[C⁄R]), L (c • α) = g c • L α)
    (α : Ω[C⁄R]) (h : L α = 0) : ∃ m : ℕ, f ^ m • α = 0 := by
  letI : Algebra C B := g.toRingHom.toAlgebra
  haveI : IsScalarTower R C B := IsScalarTower.of_algebraMap_eq (fun r => (g.commutes r).symm)
  have hL : ∀ β, L β = KaehlerDifferential.map R R C B β := by
    intro β
    have hβ : β ∈ Submodule.span C (Set.range (D R C)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hβ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      rw [hD, KaehlerDifferential.map_D]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul c x _ hx =>
      rw [hs, hx, (KaehlerDifferential.map R R C B).map_smul]
      exact algebraMap_smul B c _
  haveI := KaehlerDifferential.isLocalizedModule_map R C B (Submonoid.powers f)
  have h' : KaehlerDifferential.map R R C B α = KaehlerDifferential.map R R C B 0 := by
    rw [← hL, h, map_zero]
  obtain ⟨⟨c, hc⟩, hc0⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) h'
  obtain ⟨m, rfl⟩ := hc
  refine ⟨m, ?_⟩
  simpa [Submonoid.smul_def] using hc0

theorem eq_zero_of_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), CompactSpace X → ∃ (n : ℕ) (V : Fin n → AffOp X), ∀ w : GlobForm s, (∀ k, evForm s (V k) w = 0) → w = 0 := by
  intro R _ X s hX
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨t.card, fun k => Opposite.op (t.equivFin.symm k).1, fun w hw => ?_⟩
  have hcov : ∀ x : X, ∃ U ∈ t, x ∈ (U.1 : Set X) := fun x => by
    simpa using ht (Set.mem_univ x)
  have hV0 : ∀ U ∈ t, w.1 (Opposite.op U) = 0 := fun U hU => by
    have : evForm s (Opposite.op (t.equivFin.symm (t.equivFin ⟨U, hU⟩)).1) w = 0 := hw _
    have e : t.equivFin.symm (t.equivFin ⟨U, hU⟩) = ⟨U, hU⟩ := Equiv.symm_apply_apply _ _
    rw [e] at this
    exact this
  apply Subtype.ext
  funext W
  obtain ⟨W₀⟩ := W
  have hW : IsAffineOpen W₀.1 := W₀.2
  let S : Set Γ(X, W₀.1) := {f | ∃ U ∈ t, X.basicOpen f ≤ U.1}
  have hS : Ideal.span S = ⊤ := by
    rw [← hW.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun f => X.basicOpen_le _) ?_
    intro x hx
    obtain ⟨U, hU, hxU⟩ := hcov x
    obtain ⟨f, hf, hxf⟩ := hW.exists_basicOpen_le (V := U.1) ⟨x, hxU⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, U, hU, hf⟩, hxf⟩
  let α : Ω[Sec s W₀.1⁄R] := w.1 (Opposite.op W₀)
  let I : Ideal (Sec s W₀.1) := LinearMap.ker (LinearMap.toSpanSingleton (Sec s W₀.1) _ α)
  have hrad : ∀ f ∈ S, f ∈ I.radical := by
    rintro f ⟨U, hU, hf⟩
    let D' : X.affineOpens := ⟨X.basicOpen f, hW.basicOpen f⟩
    let φ : (Opposite.op W₀ : AffOp X) ⟶ Opposite.op D' := (homOfLE (X.basicOpen_le f)).op
    let ψ : (Opposite.op U : AffOp X) ⟶ Opposite.op D' := (homOfLE hf).op
    have h0 : p1 (OAff s) φ α = 0 := by
      have e1 := w.2 φ
      have e2 := w.2 ψ
      rw [hV0 U hU, map_zero] at e2
      exact e1.symm.trans e2
    obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero (mp (OAff s) φ) f
      (hW.isLocalization_basicOpen f) (p1 (OAff s) φ) (p1_D (OAff s) φ) (oneFormsMapOfFunctorMorphism_smul (OAff s) φ) α h0
    exact ⟨m, by simpa [I] using hm⟩
  have hI : I = ⊤ := by
    rw [← Ideal.radical_eq_top, eq_top_iff]
    have h2 := Ideal.span_le.2 hrad
    exact (show (⊤ : Ideal (Sec s W₀.1)) ≤ Ideal.span S from hS.ge).trans h2
  have h1 : (1 : Sec s W₀.1) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

end GlobalTheory.CoverForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalUnitTripleFibreProductInvariantSetGroupCoo
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNorm.RigidW

theorem triple_ext {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g h : Z ⟶ Triple f)
    (h1 : g ≫ pullback.fst _ _ ≫ pullback.fst f f = h ≫ pullback.fst _ _ ≫ pullback.fst f f)
    (h2 : g ≫ pullback.fst _ _ ≫ pullback.snd f f = h ≫ pullback.fst _ _ ≫ pullback.snd f f)
    (h3 : g ≫ pullback.snd _ _ ≫ pullback.snd f f = h ≫ pullback.snd _ _ ≫ pullback.snd f f) : g = h := by
  have c := pullback.condition (f := pullback.snd f f) (g := pullback.fst f f)
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using h1
    · simpa only [Category.assoc] using h2
  · apply pullback.hom_ext
    · simp only [Category.assoc, ← c]
      simpa only [Category.assoc] using h2
    · simpa only [Category.assoc] using h3

theorem appTop_comp {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom x = g.appTop.hom (h.appTop.hom x) := by
  rw [Scheme.Hom.comp_appTop]; rfl

section
variable {K : Type} [Field K] {A A' B : Over (Sp K)} [GrpObj B] (q : A ⟶ A')

theorem snd_hom : pullback.snd (q ▷ B).left (q ▷ B).left ≫ (A ⊗ B).hom =
    pullback.fst (q ▷ B).left (q ▷ B).left ≫ (A ⊗ B).hom := by
  rw [← Over.w (q ▷ B), pullback.condition_assoc]

variable (B) in

def W0 : Over (Sp K) :=
  Over.mk (pullback.fst _ _ ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (A ⊗ B).hom : Triple (q ▷ B).left ⟶ Sp K)

def p1 : W0 B q ⟶ A ⊗ B := Over.homMk (pullback.fst _ _ ≫ pullback.fst _ _) (by simp [W0])

def p2 : W0 B q ⟶ A ⊗ B := Over.homMk (pullback.fst _ _ ≫ pullback.snd _ _) (by
  simp only [W0, Over.mk_hom]; rw [Category.assoc, snd_hom])

def p3 : W0 B q ⟶ A ⊗ B := Over.homMk (pullback.snd _ _ ≫ pullback.snd _ _) (by
  simp only [W0, Over.mk_hom]; rw [Category.assoc, snd_hom, ← pullback.condition_assoc, snd_hom])

theorem rigidityTripleFibreProductFirstCoord_left : (p1 q).left = pullback.fst _ _ ≫ pullback.fst (q ▷ B).left (q ▷ B).left := rfl
theorem rigidityTripleFibreProductSecondCoord_left : (p2 q).left = pullback.fst _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left := rfl
theorem rigidityTripleFibreProductThirdCoord_left : (p3 q).left = pullback.snd _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left := rfl

theorem p12 : p1 q ≫ q ▷ B = p2 q ≫ q ▷ B := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, rigidityTripleFibreProductFirstCoord_left, rigidityTripleFibreProductSecondCoord_left]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)

theorem p23 : p2 q ≫ q ▷ B = p3 q ≫ q ▷ B := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, rigidityTripleFibreProductThirdCoord_left, rigidityTripleFibreProductSecondCoord_left]
  exact (congrArg (· ≫ _) pullback.condition).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm))

end
end GlobalTheory.DescNorm.RigidW

namespace GlobalTheory.DescNorm.RigidW
section
variable {K : Type} [Field K] {A A' B : Over (Sp K)} [GrpObj B] (q : A ⟶ A')

def beta : W0 B q ⟶ B := p1 q ≫ snd A B

theorem rigidityTripleSecondCoord_snd_eq_groupCoord : p2 q ≫ snd A B = beta q := by
  rw [beta, ← whiskerRight_snd q B, ← Category.assoc, ← Category.assoc, p12]

theorem rigidityTripleThirdCoord_snd_eq_groupCoord : p3 q ≫ snd A B = beta q := by
  rw [← rigidityTripleSecondCoord_snd_eq_groupCoord, ← whiskerRight_snd q B, ← Category.assoc, ← Category.assoc, p23]

def E (u : W0 B q ⟶ A ⊗ B) : B ⊗ W0 B q ⟶ A ⊗ B := lift (snd B (W0 B q) ≫ u ≫ fst A B) (fst B (W0 B q))

theorem E_eq {u v : W0 B q ⟶ A ⊗ B} (h : u ≫ q ▷ B = v ≫ q ▷ B) : E q u ≫ q ▷ B = E q v ≫ q ▷ B := by
  have h' : u ≫ fst A B ≫ q = v ≫ fst A B ≫ q := by
    have := congrArg (· ≫ fst A' B) h
    simpa using this
  apply CartesianMonoidalCategory.hom_ext
  · simp [E, h']
  · simp [E]

theorem E_left_eq {u v : W0 B q ⟶ A ⊗ B} (h : u ≫ q ▷ B = v ≫ q ▷ B) :
    (E q u).left ≫ (q ▷ B).left = (E q v).left ≫ (q ▷ B).left := by
  rw [← Over.comp_left, ← Over.comp_left, E_eq q h]

theorem lift_E (x : W0 B q ⟶ B) (u : W0 B q ⟶ A ⊗ B) : lift x (𝟙 _) ≫ E q u = lift (u ≫ fst A B) x := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [E]

def eL : (B ⊗ W0 B q).left ⟶ Triple (q ▷ B).left :=
  pullback.lift (pullback.lift (E q (p1 q)).left (E q (p2 q)).left (E_left_eq q (p12 q)))
    (pullback.lift (E q (p2 q)).left (E q (p3 q)).left (E_left_eq q (p23 q)))
    ((pullback.lift_snd _ _ _).trans (pullback.lift_fst _ _ _).symm)

theorem eL_1 : eL q ≫ pullback.fst _ _ ≫ pullback.fst (q ▷ B).left (q ▷ B).left = (E q (p1 q)).left := by
  rw [eL, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]
theorem eL_2 : eL q ≫ pullback.fst _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left = (E q (p2 q)).left := by
  rw [eL, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]
theorem eL_3 : eL q ≫ pullback.snd _ _ ≫ pullback.snd (q ▷ B).left (q ▷ B).left = (E q (p3 q)).left := by
  rw [eL, ← Category.assoc, pullback.lift_snd, pullback.lift_snd]

theorem sec_beta : (lift (beta q) (𝟙 (W0 B q))).left ≫ eL q = 𝟙 _ := by
  apply triple_ext
  · rw [Category.assoc, eL_1, ← Over.comp_left, lift_E]
    refine (congrArg Over.Hom.left (?_ : lift (p1 q ≫ fst A B) (beta q) = p1 q)).trans
      ((rigidityTripleFibreProductFirstCoord_left q).trans (Category.id_comp _).symm)
    apply CartesianMonoidalCategory.hom_ext <;> simp [beta]
  · rw [Category.assoc, eL_2, ← Over.comp_left, lift_E]
    refine (congrArg Over.Hom.left (?_ : lift (p2 q ≫ fst A B) (beta q) = p2 q)).trans
      ((rigidityTripleFibreProductSecondCoord_left q).trans (Category.id_comp _).symm)
    apply CartesianMonoidalCategory.hom_ext <;> simp [rigidityTripleSecondCoord_snd_eq_groupCoord]
  · rw [Category.assoc, eL_3, ← Over.comp_left, lift_E]
    refine (congrArg Over.Hom.left (?_ : lift (p3 q ≫ fst A B) (beta q) = p3 q)).trans
      ((rigidityTripleFibreProductThirdCoord_left q).trans (Category.id_comp _).symm)
    apply CartesianMonoidalCategory.hom_ext <;> simp [rigidityTripleThirdCoord_snd_eq_groupCoord]

theorem lift_one (u : W0 B q ⟶ A ⊗ B) : lift (u ≫ fst A B) (1 : W0 B q ⟶ B) = u ≫ zb A B := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [zb]
  · simp [zb, MonObj.comp_one]

theorem sec_one : (lift (1 : W0 B q ⟶ B) (𝟙 (W0 B q))).left ≫ eL q = rhoW q := by
  apply triple_ext
  · rw [Category.assoc, eL_1, ← Over.comp_left, lift_E, lift_one, Over.comp_left, rigidityTripleFibreProductFirstCoord_left]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (rhoZ_fst q).symm)).trans (rhoW_fst_assoc q _).symm
  · rw [Category.assoc, eL_2, ← Over.comp_left, lift_E, lift_one, Over.comp_left, rigidityTripleFibreProductSecondCoord_left]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (rhoZ_snd q).symm)).trans (rhoW_fst_assoc q _).symm
  · rw [Category.assoc, eL_3, ← Over.comp_left, lift_E, lift_one, Over.comp_left, rigidityTripleFibreProductThirdCoord_left]
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (rhoZ_snd q).symm)).trans (rhoW_snd_assoc q _).symm

theorem rhoW_appTop (hB : IsAbelianScheme B) (D : Γ(Triple (q ▷ B).left, ⊤)) : (rhoW q).appTop.hom D = D := by
  have hs : Function.Surjective ((snd B (W0 B q)).left.appTop).hom :=
    surjective_app_of_isAbelianScheme GlobalTheory.SemiRigid.globalFns _ (Out.TLinPf.isAb_pullback (W0 B q).hom B hB) ⊤
  obtain ⟨F, hF⟩ := hs ((eL q).appTop.hom D)
  have hsnd : ∀ x : W0 B q ⟶ B, (lift x (𝟙 (W0 B q))).left ≫ (snd B (W0 B q)).left = 𝟙 _ := fun x => by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have key : ∀ x : W0 B q ⟶ B, ((lift x (𝟙 (W0 B q))).left ≫ eL q).appTop.hom D = F := by
    intro x
    calc ((lift x (𝟙 (W0 B q))).left ≫ eL q).appTop.hom D
        = (lift x (𝟙 (W0 B q))).left.appTop.hom ((eL q).appTop.hom D) := appTop_comp _ _ _
      _ = (lift x (𝟙 (W0 B q))).left.appTop.hom ((snd B (W0 B q)).left.appTop.hom F) := by rw [hF]
      _ = ((lift x (𝟙 (W0 B q))).left ≫ (snd B (W0 B q)).left).appTop.hom F := (appTop_comp _ _ _).symm
      _ = F := by rw [hsnd x, Scheme.Hom.id_appTop]; rfl
  have h1 : D = F := by
    have h := key (beta q)
    rw [sec_beta] at h
    exact h
  have h0 := key 1
  rw [sec_one] at h0
  exact h0.trans h1.symm

end

theorem gm_rhoW_eq_gm_id_of_abelian : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj B] (q : A ⟶ A'), IsAbelianScheme B →
    ∀ (D : Γ(Triple (q ▷ B).left, ⊤)ˣ) (w : Triple (q ▷ B).left), gm (rhoW q) w ⊤ D = gm (𝟙 _) w ⊤ D := by
  intro K _ A A' B _ q hB D w
  have := gm_comp_top (𝟙 _) (rhoW q) w D D (rhoW_appTop q hB D.val)
  rwa [Category.id_comp] at this

end GlobalTheory.DescNorm.RigidW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmSpMapUnitOn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.PsiMono
variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def fracPt (ρ : V →+* V₁) (hρ : Function.Injective ρ) : (TK V₁).left ⟶ (TK V).left :=
  spMap (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ)

theorem fracPt_comp (ρ : V →+* V₁) (hρ : Function.Injective ρ) : fracPt ρ hρ ≫ jK V = jK V₁ ≫ spMap ρ := by
  simp only [fracPt, spMap, jK, TK, Over.mk_hom, ← Spec.map_comp]
  congr 1
  ext x
  simp [IsFractionRing.map, IsLocalization.map_eq]

theorem gm_spMap_unitOn {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (z : Sp R') (k : Rˣ) :
    gm (spMap f) z ⊤ (unitOn k) = gm (𝟙 _) z ⊤ (unitOn (Units.map f.toMonoidHom k)) := by
  have h := gm_pull (𝟙 _) (spMap f) z ⊤ trivial (unitOn k)
  rw [Category.id_comp] at h
  refine h.symm.trans (congrArg _ ?_)
  ext
  have e := congrArg (fun g => g.hom (k : R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [unitOn, pullU, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  exact e.symm

theorem val_scaleGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (c : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (scaleGen t c) r z J = gm r z ⊤ c * val t r z J :=
  gm_scaleGen t c r z _ (hJ.mem φ r)

theorem prod_zpow_swap {F : Type} [Field F] {I C : Type} [Fintype I] [Fintype C] (x : I → F) (e : C → I → ℤ)
    (w : C → ℤ) (h : ∀ c, ∏ i, x i ^ e c i ≠ 0) :
    ∏ c, (∏ i, x i ^ e c i) ^ w c = ∏ i, x i ^ ∑ c, w c * e c i := by
  classical
  have hz : ∀ i, x i = 0 → ∀ c, e c i = 0 := by
    intro i hi c
    by_contra hne
    exact h c (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, zero_zpow _ hne]))
  set y : I → F := fun i => if x i = 0 then 1 else x i with hy
  have hy0 : ∀ i, y i ≠ 0 := fun i => by
    by_cases hi : x i = 0 <;> simp [hy, hi]
  have hxy : ∀ i (n : ℤ), (x i = 0 → n = 0) → x i ^ n = y i ^ n := by
    intro i n hn
    by_cases hi : x i = 0
    · rw [hn hi]; simp
    · simp [hy, hi]
  have l1 : ∀ c, ∏ i, x i ^ e c i = ∏ i, y i ^ e c i :=
    fun c => Finset.prod_congr rfl fun i _ => hxy i _ fun hi => hz i hi c
  have l2 : ∀ i, x i ^ ∑ c, w c * e c i = y i ^ ∑ c, w c * e c i := fun i => hxy i _ fun hi => by
    simp [hz i hi]
  simp_rw [l1, l2, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  have key : ∀ (a : F), a ≠ 0 → ∀ (s : Finset C) (n : C → ℤ), ∏ c ∈ s, a ^ n c = a ^ ∑ c ∈ s, n c := by
    intro a ha s n
    induction s using Finset.induction_on with
    | empty => simp
    | insert c s hc ih => rw [Finset.prod_insert hc, Finset.sum_insert hc, ih, zpow_add₀ ha]
  rw [key _ (hy0 i)]
  exact congrArg _ (Finset.sum_congr rfl fun c _ => mul_comm _ _)

abbrev fracOver (ρ : V →+* V₁) (hρ : Function.Injective ρ) : Over (Sp V) := Over.mk (fracPt ρ hρ ≫ jK V)

theorem psi_val (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (hρ : Function.Injective ρ) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2))))
    (hw : ∀ κ : (TK V₁).left ⟶ (TK V).left, κ ≫ jK V = jK V₁ ≫ spMap ρ → ∀ mu z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.psi (e mu)) (𝟙 _) z J' =
        gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
            pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
          ∏ a, ∏ b, val (Q.tau (mu a) (mu b)) κ z J ^ W a b)
    (τ₀ : Gens Q) {n : ℕ} (s : Fin n → V) (ε : Fin n → LinearMap.BilinForm ℤ Q.X) (hτ : TauIn Q τ₀ s ε)
    {W₀ : Type} [CommRing W₀] (ib : W₀ →+* V) (B₀ : Over (Sp W₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left)
    (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀)) (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε))
    (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left) (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂))
    (h₀ : ∀ (T : Over (Sp V)) (a b : Q.X) z J J', Good M₀ z J → Good Q.M.L z J' →
      val (τ₀ a b) (toUnit T).left z J' =
        lamVal w₀ (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left z J J' * val (τ₁ a b) (T.hom ≫ spMap ib) z J)
    (mu : Fin 8 → Q.X) (z : (TK V₁).left) (J : ((TK V₁).left ⟶ Q.B.left) → Q.M.L.ι)
    (J' : ((TK V₁).left ⟶ D.P.A.left) → D.P.L.ι) (J₀ : ((TK V₁).left ⟶ B₀.left) → M₀.ι)
    (hJ : Good Q.M.L z J) (hJ' : Good D.P.L z J') (hJ₀ : Good M₀ z J₀) :
    ∃ u : (FractionRing V₁)ˣ, (u : FractionRing V₁) = ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ qW W (ε i) mu ∧
      val (D.psi (e mu)) (𝟙 _) z J' =
        gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
            pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
          (∏ a, ∏ b, (lamVal (Z := (TK V₁).left) w₀ (lift (toUnit (fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (fracOver ρ hρ) ≫ Q.c (mu b))).left
              z J₀ J * val (τ₁ (mu a) (mu b)) ((fracPt ρ hρ ≫ jK V) ≫ spMap ib) z J₀) ^ W a b) *
          gm (𝟙 _) z ⊤ (unitOn u) := by
  classical
  have hL : Q.M.L.IsLB := Q.M.isLB
  choose k hk hkv using fun a b => (hτ a b).2
  have htau : ∀ a b, val (Q.tau a b) (fracPt ρ hρ) z J =
      gm (fracPt ρ hρ) z ⊤ (unitOn (k a b)) * val (τ₀ a b) (fracPt ρ hρ ≫ jK V) z J := by
    intro a b
    let t₁ := scaleGen (LB.pullGen Q.M.L (lamPts (Q.c a) (Q.c b)) negε (τ₀ a b) (toUnit (TK V)).left) (unitOn (k a b))
    have hc : LB.Gen.Corr Q.M.L _ _ _ _ (Q.tau a b) t₁ := corr_of_val hL fun y J₁ hJ₁ => by
      rw [val_scaleGen _ _ _ _ hJ₁, val_pull hJ₁, Category.id_comp]
      exact hkv a b y J₁ hJ₁
    rw [val_corr hJ hc (fracPt ρ hρ), val_scaleGen _ _ _ _ hJ, val_pull hJ]
    rfl
  have hunit : ∀ a b, gm (fracPt ρ hρ) z ⊤ (unitOn (k a b)) =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ).toMonoidHom
        (k a b))) := fun a b => gm_spMap_unitOn _ z _
  have hbase : ∀ a b, val (τ₀ a b) (fracPt ρ hρ ≫ jK V) z J =
      lamVal (Z := (TK V₁).left) w₀ (lift (toUnit (fracOver ρ hρ) ≫ Q.c a) (toUnit (fracOver ρ hρ) ≫ Q.c b)).left z J₀ J *
        val (τ₁ a b) ((fracPt ρ hρ ≫ jK V) ≫ spMap ib) z J₀ := fun a b => h₀ (fracOver ρ hρ) a b z J₀ J hJ₀ hJ
  have hfk : ∀ a b, ((Units.map (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ).toMonoidHom
      (k a b) : (FractionRing V₁)ˣ) : FractionRing V₁) =
        ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ ε i a b := by
    intro a b
    show IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ (k a b : FractionRing V) = _
    rw [hk a b, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀]
    simp [IsFractionRing.map, IsLocalization.map_eq]
  refine ⟨∏ a, ∏ b, Units.map (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ).toMonoidHom
      (k (mu a) (mu b)) ^ W a b, ?_, ?_⟩
  · simp_rw [Units.coe_prod, Units.val_zpow_eq_zpow_val, hfk]
    have hne : ∀ c : Fin 8 × Fin 8, ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ ε i (mu c.1) (mu c.2) ≠ 0 :=
      fun c => by rw [← hfk]; exact Units.ne_zero _
    have e := prod_zpow_swap (fun i => algebraMap V₁ (FractionRing V₁) (ρ (s i)))
      (fun (c : Fin 8 × Fin 8) i => ε i (mu c.1) (mu c.2)) (fun (c : Fin 8 × Fin 8) => W c.1 c.2) hne
    rw [Fintype.prod_prod_type] at e
    simp only [Fintype.sum_prod_type] at e
    rw [e]
    rfl
  · rw [hw (fracPt ρ hρ) (fracPt_comp ρ hρ) mu z J J' hJ hJ', _root_.mul_assoc]
    congr 1
    clear hw h₀ hkv hk hτ hfk
    simp only [htau, hunit, hbase]
    simp only [unitOn, map_prod, map_zpow, mul_zpow, Finset.prod_mul_distrib]
    exact _root_.mul_comm _ _

theorem psi_val_of (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (hρ : Function.Injective ρ) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (hS : SharpRef W Q ρ D e) (τ₀ : Gens Q) {n : ℕ} (s : Fin n → V)
    (ε : Fin n → LinearMap.BilinForm ℤ Q.X) (hτ : TauIn Q τ₀ s ε) {W₀ : Type} [CommRing W₀] (ib : W₀ →+* V)
    (hB : FromBase Q τ₀ ib) :
    ∃ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
      (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
        (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))),
      (∀ a, IsMonHom (pr a)) ∧
      (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) ∧
      w.IsGen ∧ (∀ mu a, (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = spMap ρ ≫ (Q.c (mu a)).left) ∧
      ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀))
        (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε))
        (β : Q.B.left ⟶ B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left)
        (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)),
        IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.B B₀ (spMap ib) β ∧ IsSquare β β₂ ∧ w₀.IsGen ∧
        (∀ a, (Q.c a).left ≫ β = spMap ib ≫ (c₀ a).left) ∧ (∀ a b, (τ₁ a b).IsGen) ∧
        (∀ (T : Over (Sp V)) (a b : Q.X) z J J', Good M₀ z J → Good Q.M.L z J' →
          val (τ₀ a b) (toUnit T).left z J' =
            lamVal w₀ (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left z J J' * val (τ₁ a b) (T.hom ≫ spMap ib) z J) ∧
        ∀ (mu : Fin 8 → Q.X) (z : (TK V₁).left) (J : ((TK V₁).left ⟶ Q.B.left) → Q.M.L.ι)
          (J' : ((TK V₁).left ⟶ D.P.A.left) → D.P.L.ι) (J₀ : ((TK V₁).left ⟶ B₀.left) → M₀.ι),
          Good Q.M.L z J → Good D.P.L z J' → Good M₀ z J₀ →
          ∃ u : (FractionRing V₁)ˣ,
            (u : FractionRing V₁) = ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ qW W (ε i) mu ∧
            val (D.psi (e mu)) (𝟙 _) z J' =
              gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
                  pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
                (∏ a, ∏ b, (lamVal (Z := (TK V₁).left) w₀
                    (lift (toUnit (fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (fracOver ρ hρ) ≫ Q.c (mu b))).left
                    z J₀ J * val (τ₁ (mu a) (mu b)) ((fracPt ρ hρ ≫ jK V) ≫ spMap ib) z J₀) ^ W a b) *
                gm (𝟙 _) z ⊤ (unitOn u) := by
  obtain ⟨pr, w, h1, h2, h3, h4, hw⟩ := hS
  obtain ⟨B₀, _, _, M₀, c₀, τ₁, β, β₂, w₀, g1, g2, g3, g4, g5, g6, g7, h₀⟩ := hB
  exact ⟨pr, w, h1, h2, h3, h4, B₀, inferInstance, inferInstance, M₀, c₀, τ₁, β, β₂, w₀, g1, g2, g3, g4, g5, g6, g7, h₀,
    fun mu z J J' J₀ hJ hJ' hJ₀ => psi_val W Q ρ hρ D e pr w hw τ₀ s ε hτ ib B₀ M₀ c₀ τ₁ β₂ w₀ h₀ mu z J J' J₀ hJ hJ' hJ₀⟩

end GlobalTheory.Poinc.PsiMono

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelCoinvariantStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_coinvariant : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.KCoinv := by
  first | exact @GlobalTheory.KCoinvGood.kCoinv | exact GlobalTheory.KCoinvGood.kCoinv | (intros; apply GlobalTheory.KCoinvGood.kCoinv <;> assumption)
end

