import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0171
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0472
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0462
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicTermMeanInvariantUnipotentRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
import Formalism.LocalRingCardinality.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPinT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaValueIdentityUnitFramesStatement
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_theta_value_identity_unitFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U →
  ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
    admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z →
  ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (Pm : (F.Di (ik k)).La →+ (Fin g → ℂ)) (Pm' : (F.Di (ik k')).La →+ (Fin g → ℂ)),
    IsPeriod (F.Di (ik k)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm →
    IsPeriod (F.Di (ik k')) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm' →
    (U.un k x).x = F.u (ik k) Pm → (U.un k' x').x = F.u (ik k') Pm' →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ : (Fin g → ℂ) → ℂ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di (ik k)).EF a b) →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex (ik k) Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (F.ex (ik k) Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' (U.un k x).x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
        Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) →
    (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
      pt ≫ Formalism.L2.PjFree.gxFst (U.un k x).x = (F.ex (ik k) Pm z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j)) = θ z * fr j z) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ' : (Fin g → ℂ) → ℂ),
    Hm'.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) →
    (∀ a b, (hermForm Hm' (Pm' a) (Pm' b)).im = (F.Di (ik k')).EF a b) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (F.ex (ik k') Pm' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (F.ex (ik k') Pm' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' (U.un k' x').x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a j z, ‖χl' (Pm' a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' (Pm' a) * Complex.exp (Real.pi * hermForm Hm' z (Pm' a) +
        Real.pi / 2 * hermForm Hm' (Pm' a) (Pm' a)) * fr' j (z + Pm' a))) →
    (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k' x').x),
      pt ≫ Formalism.L2.PjFree.gxFst (U.un k' x').x = (F.ex (ik k') Pm' z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd (U.un k' x').x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (U.un k' x').x).U (fun _ => j)) ((U.un k' x').s.f (fun _ => j)) = θ' z * fr' j z) →
  ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (wm : Fin (Ideal.absNorm P ^ i) → (Fin g → ℂ)),
    (∀ a, ∃ b, h (Pm a) = Pm' b) ∧ (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) ∧
    (∀ m, ∃ b, h (wm m) = Pm' b) ∧
    ∀ w, ∃ j, ⊤ ≤ (F.ex (ik k') Pm' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j ∧
      Formalism.L2.PjFree.toC (t none : CAt σ) * θ' (h w) * fr' j (h w) =
        ∑ m, θ ((p : ℂ) • (w + wm m)) * fr' j (h w + h (wm m)) := by
  first | exact @GlobalTheory.HeckeValueId.hecke_theta_value_identity | exact GlobalTheory.HeckeValueId.hecke_theta_value_identity | (intros; apply GlobalTheory.HeckeValueId.hecke_theta_value_identity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeUniversalIsogenyOnFibresLinearAtRingPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

open GlobalTheory.HeckeFrCompare (gx_ext toFib_fst toFib_fst_assoc toFib_snd)
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (push toFib)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

def overCast {T' X : Scheme.{0}} {u v : T' ⟶ X} (e : u = v) : (Over.mk u : Over X) ⟶ Over.mk v :=
  Over.homMk (𝟙 _) (by simp [e])

@[simp] theorem overCast_left {T' X : Scheme.{0}} {u v : T' ⟶ X} (e : u = v) : (overCast e).left = 𝟙 _ := rfl

theorem overCast_comp_left {T' X : Scheme.{0}} {u v : T' ⟶ X} (e : u = v) {G : Over X} (a : Over.mk v ⟶ G) :
    (overCast e ≫ a).left = a.left := by
  rw [Over.comp_left, overCast_left, Category.id_comp]

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] {h : Sp T ⟶ Z.Hk} {x x' : Sp T ⟶ Xo.X}

@[reassoc] theorem hkLift_act (hx : x = h ≫ Z.π₁) (r : 𝓞 E) :
    (Over.mk x ◁ Xo.univ.t.act.act r).left ≫ hkLift Z h hx = hkLift Z h hx ≫ (Z.o₁.t.act.act r).left := by
  refine Z.m₁.cart.1.hom_ext ?_ ?_
  · rw [Category.assoc, hkLift_φ, Category.assoc, Z.m₁.act, hkLift_φ_assoc, ← Over.comp_left, whiskerLeft_snd,
      Over.comp_left]
  · rw [Category.assoc, hkLift_hom, Category.assoc, Over.w, hkLift_hom, ← Category.assoc, ← Over.comp_left,
      whiskerLeft_fst]

def hkLiftPt (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    (Over.mk (t ≫ h) : Over Z.Hk) ⟶ Z.o₁.t.G :=
  Over.homMk (toFib x t a ≫ hkLift Z h hx) (by
    rw [Category.assoc, hkLift_hom, toFib_fst_assoc]; rfl)

theorem hkLiftPt_left (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    (hkLiftPt Z hx t a).left = toFib x t a ≫ hkLift Z h hx := rfl

theorem hkLiftPt_φ (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    (hkLiftPt Z hx t a).left ≫ Z.m₁.cm.F = a.left := by
  rw [hkLiftPt_left, Category.assoc, hkLift_φ, toFib_snd]

theorem hkLiftPt_mul (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a₁ a₂ : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    hkLiftPt Z hx t (a₁ * a₂) = hkLiftPt Z hx t a₁ * hkLiftPt Z hx t a₂ := by
  have e : (t ≫ h) ≫ Z.π₁ = t ≫ x := by rw [hx, Category.assoc]
  have key := Z.m₁.cart.2 (Over.mk (t ≫ h)) (hkLiftPt Z hx t a₁) (hkLiftPt Z hx t a₂) (overCast e ≫ a₁)
    (overCast e ≫ a₂) (by rw [overCast_comp_left, hkLiftPt_φ]) (by rw [overCast_comp_left, hkLiftPt_φ])
  refine Over.OverMorphism.ext (Z.m₁.cart.1.hom_ext ?_ ?_)
  · rw [hkLiftPt_φ, ← key, ← MonObj.comp_mul, overCast_comp_left]
  · rw [Over.w, Over.w]

theorem push_hkMap (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) {T' : Scheme.{0}} (t : T' ⟶ Sp T)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    push (hkMap Z hx hx') t a = (hkLiftPt Z hx t a ≫ Z.ψ).left ≫ Z.m₂.cm.F := by
  rw [push, hkMap_snd, Over.comp_left, hkLiftPt_left]
  simp only [Category.assoc]

theorem isLinHom_hkMap (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) : IsLinHom (hkMap Z hx hx') := by
  haveI : IsMonHom Z.ψ := Z.isog.1.1
  refine ⟨hkMap_fst Z hx hx', fun T' t a₁ a₂ b₁ b₂ h₁ h₂ => ?_, fun r => ?_⟩
  · have e : (t ≫ h) ≫ Z.π₂ = t ≫ x' := by rw [hx', Category.assoc]
    have key := Z.m₂.cart.2 (Over.mk (t ≫ h)) (hkLiftPt Z hx t a₁ ≫ Z.ψ) (hkLiftPt Z hx t a₂ ≫ Z.ψ) (overCast e ≫ b₁)
      (overCast e ≫ b₂) (by rw [overCast_comp_left, h₁, push_hkMap]) (by rw [overCast_comp_left, h₂, push_hkMap])
    rw [push_hkMap, hkLiftPt_mul, MonObj.mul_comp, ← key, ← MonObj.comp_mul, overCast_comp_left]
  · have w : ∀ z : Sp T ⟶ Xo.X, (Over.mk z ◁ Xo.univ.t.act.act r).left ≫ (snd (Over.mk z) Xo.univ.t.G).left =
        (snd (Over.mk z) Xo.univ.t.G).left ≫ (Xo.univ.t.act.act r).left := fun z => by
      rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
    have w₀ : ∀ z : Sp T ⟶ Xo.X, (Over.mk z ◁ Xo.univ.t.act.act r).left ≫ (fst (Over.mk z) Xo.univ.t.G).left =
        (fst (Over.mk z) Xo.univ.t.G).left := fun z => by
      rw [← Over.comp_left, whiskerLeft_fst]
    have hψ : (Z.o₁.t.act.act r).left ≫ Z.ψ.left = Z.ψ.left ≫ (Z.o₂.t.act.act r).left := by
      rw [← Over.comp_left, Z.isog.1.2.2.2.2.1 r, Over.comp_left]
    refine gx_ext ?_ ?_
    · rw [Category.assoc, hkMap_fst, w₀, Category.assoc, w₀, hkMap_fst]
    · rw [Category.assoc, hkMap_snd, hkLift_act_assoc, reassoc_of% hψ, Z.m₂.act, Category.assoc, w,
        hkMap_snd_assoc]

end GlobalTheory.HeckeEx

end

theorem GlobalTheory.HeckeEx.isLinHom_hkMap_target : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), IsLinHom (hkMap Z hx hx') :=
  fun _ _ _ _ _ _ _ _ _ _ _ Z _ _ _ _ _ hx hx' => GlobalTheory.HeckeEx.isLinHom_hkMap Z hx hx'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeUniversalIsogenyOnFibresPreservesOrigin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

private theorem one_left_eq_eSec {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {Y : Scheme.{0}} (y : Y ⟶ S) :
    (1 : Over.mk y ⟶ G).left = y ≫ eSec G := by
  rw [eSec]
  show (toUnit _ ≫ η[G]).left = _
  rw [Over.comp_left]
  congr 1

private theorem eSec_hom {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] : eSec G ≫ G.hom = 𝟙 _ := by
  rw [eSec]
  have := Over.w η[G]
  simpa using this

theorem hkMap_ptSec_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkMap Z hx hx' = (ptSecT Xo.univ.t.G (1 : Over.mk x' ⟶ Xo.univ.t.G)).left := by
  intro E _ _ _ H Dw l Xo P p i Z T _ h x x' hx hx'
  have key₁ : (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkLift Z h hx = h ≫ eSec Z.o₁.t.G := by
    apply Z.m₁.cart.1.hom_ext
    · rw [Category.assoc, hkLift_φ, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_snd, one_left_eq_eSec, Category.assoc,
        Z.m₁.cm.e_comm, Z.m₁.base, ← Category.assoc, ← hx]
    · rw [Category.assoc, hkLift_hom, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_fst_assoc, Category.assoc, eSec_hom]
      simp
  haveI := Z.isog.1.1
  have hψ : eSec Z.o₁.t.G ≫ Z.ψ.left = eSec Z.o₂.t.G := by
    rw [eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  apply GlobalTheory.HeckeFrCompare.gx_ext
  · rw [Category.assoc, hkMap_fst, ptSecT, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_fst, GlobalTheory.HeckeFrCompare.lift_l_fst]
    rfl
  · rw [Category.assoc, hkMap_snd, ← Category.assoc, key₁, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_snd, one_left_eq_eSec,
      Category.assoc, ← Category.assoc (eSec _), hψ, Z.m₂.cm.e_comm, Z.m₂.base, ← Category.assoc, ← hx']

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianFormDualFlagEqReducedFrameCoordinatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianForm_dualFlag_eq_reduced_frame_coordinates : ∀ {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D)) (ew : EAf D), Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) g e0 f0 z0 bw bwd ew → ∀ (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Bool), IsFrame β (II D).L → LocAt g e0 f0 z0 bw bwd ew β PP w → ∀ u ∈ (II D).Lf, (∀ p (h1 : hA (II D) (flagV D.R.rS D.R.k (Yc D 0).rank f0 e0 (dualOrRevBasis w bw bwd) (-z0) p) u ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), resS D.host.F PP ⟨_, h1⟩ = redV β PP u p) ∧ (∀ i (h1 : hA (II D) ((if w then bw else bwd) i) u ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), resS D.host.F PP ⟨_, h1⟩ = 0) := by
  first | exact @GlobalTheory.SeeConjGroup.CoefRead.coef_read | exact GlobalTheory.SeeConjGroup.CoefRead.coef_read | (intros; apply GlobalTheory.SeeConjGroup.CoefRead.coef_read <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumScalarSmulMemCompletedModulus
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.HalfScalarHat

open GlobalTheory.FunObj.HatFrame

theorem smul_map_mem_genGrp {D : D7} {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (𝔪 : Ideal (𝓞 D.host.E)) {g : Matrix (Fin m) (Fin n) D.host.E} (hg : g ∈ M)
    {t : Formalism.L2.Herm.intAf D.host.F D.host.E} (ht : t ∈ Formalism.L2.DIV.idS D.host.F 𝔪) :
    (t : EAf D) • g.map (eToEAf D) ∈ genGrp D.host.F (𝔪 • M) := by
  have hgen : ∀ a ∈ 𝔪, ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) •
      g.map (eToEAf D) ∈ genGrp D.host.F (𝔪 • M) := by
    intro a ha
    refine AddSubgroup.subset_closure ⟨1, one_mem _, a • g, Submodule.smul_mem_smul ha hg, ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, Formalism.L2.DIV.oToS_coe, smul_eq_mul, eToEAf,
      Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]
  have hspan : t ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((Formalism.L2.DIV.oToS D.host.F D.host.E) '' (𝔪 : Set (𝓞 D.host.E))) := ht
  clear ht
  induction hspan using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, ha, rfl⟩ := hu
    exact hgen a ha
  | zero =>
    simp only [ZeroMemClass.coe_zero, zero_smul]
    exact zero_mem _
  | add u v _ _ hu hv =>
    simp only [AddMemClass.coe_add, add_smul]
    exact add_mem hu hv
  | smul r u _ hu =>
    simp only [smul_eq_mul, MulMemClass.coe_mul, mul_smul]
    exact smul_mem_genGrp _ _ r.2 _ hu

theorem tmul_split {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (x : A ⊗[R] B) (b g : A) (α : B) :
    x * ((b * g) ⊗ₜ[R] α) = x * ((b ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] α)) * (g ⊗ₜ[R] (1 : B)) := by
  simp only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem v_triple_le {D : D7} {w : HeightOneSpectrum (𝓞 D.host.E)} {s x y z : EAf D} {c : WithZero (Multiplicative ℤ)} (h : s = x * (y * z))
    (hx : GlobalTheory.StdFrames.cpt (D := D) w x = 1) (hy : Valued.v (GlobalTheory.StdFrames.cpt (D := D) w y) ≤ c)
    (hz : Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ 1) : Valued.v (GlobalTheory.StdFrames.cpt (D := D) w s) ≤ c := by
  subst h
  rw [map_mul, hx, one_mul, map_mul, map_mul]
  calc Valued.v (GlobalTheory.StdFrames.cpt (D := D) w y) * Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ c * 1 :=
        mul_le_mul' hy hz
    _ = c := mul_one c

theorem scalar_mem_idS {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {s x y z : EAf D}
    (h : s = x * (y * z)) (e1 : ∀ w ∈ G.pl.W0, GlobalTheory.StdFrames.cpt (D := D) w x = 1)
    (e2 : ∀ w ∉ G.pl.W0, GlobalTheory.StdFrames.cpt (D := D) w x = 0)
    (hy : ∀ w ∈ G.pl.W0, Valued.v (GlobalTheory.StdFrames.cpt (D := D) w y) ≤ WithZero.exp (-(cosExp G w : ℤ)))
    (hz : z ∈ GlobalTheory.StdFrames.OA D) :
    ∃ t ∈ Formalism.L2.DIV.idS D.host.F G.modul, t.1 = s := by
  have hz' : ∀ w, Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ 1 := fun w =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((GlobalTheory.StdFrames.mem_OA_iff z).1 hz w)
  have hs : s ∈ GlobalTheory.StdFrames.OA D := by
    rw [GlobalTheory.StdFrames.mem_OA_iff]
    intro w
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hw : w ∈ G.pl.W0
    · refine v_triple_le h (e1 w hw) ((hy w hw).trans ?_) (hz' w)
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    · rw [h, map_mul, e2 w hw, zero_mul, map_zero]
      exact zero_le'
  refine ⟨⟨s, hs⟩, ?_, rfl⟩
  rw [GlobalTheory.FunObj.Comparison₂.mem_idS_modul]
  intro w hw
  exact v_triple_le h (e1 w hw) (hy w hw) (hz' w)

theorem toEAf_pair {D : D7} (α : Formalism.L2.Herm.Af D.host.F) (x : D.host.E) :
    toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = x ⊗ₜ[D.host.F] α := rfl

theorem map_toEAf_smul {D : D7} {m n : ℕ} (e : AE D) (X : Mx D m n) :
    (e • X).map (toEAf D) = toEAf D e • X.map (toEAf D) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem infPart_smul {D : D7} {m n : ℕ} {e : AE D} (he : infPart D e = 0) (X : Mx D m n) (i : Fin m) (j : Fin n) :
    infPart D ((e • X) i j) = 0 := by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, he, zero_mul]

theorem smul_pair {D : D7} {m n : ℕ} (x : EAf D) (α : Formalism.L2.Herm.Af D.host.F) (b : D.host.E)
    (g : Matrix (Fin m) (Fin n) D.host.E) :
    x • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * g i j) : Mx D m n).map (toEAf D) =
      (x * ((b ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) : EAf D) * ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D))) •
        g.map (eToEAf D) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, toEAf_pair, eToEAf,
    Algebra.TensorProduct.includeLeftRingHom_apply]
  exact tmul_split _ b (g i j) α

end GlobalTheory.HalfScalarHat

open GlobalTheory.FunObj.HatFrame GlobalTheory.HalfScalarHat in
theorem GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)) (e : AE D), IsIdemSum e G.pl.W0 → ∀ α ∈ intAf D.host.F, ∀ b : D.host.E, (∀ w ∈ G.pl.W0, Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ))) → ∀ g ∈ M, e • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * g i j) : Mx D m n) ∈ hatMx (G.modul • M) := by
  intro D T L sc G m n M e he α hα b hb g hg
  obtain ⟨hinf, h1, h0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_iff]
  refine ⟨fun i j => infPart_smul hinf _ i j, ?_⟩
  rw [map_toEAf_smul, smul_pair]
  have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ GlobalTheory.StdFrames.OA D :=
    Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩)
  obtain ⟨t, ht, hts⟩ := scalar_mem_idS G rfl h1 h0
    (fun w hw => by rw [GlobalTheory.FunObj.Comparison₂.cpt_tmul]; exact hb w hw) hα'
  rw [← hts]
  exact smul_map_mem_genGrp M G.modul hg ht
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceHomLatticeIndexEqLocalComponentIndexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_homLattice_index_eq_localComponent_index : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ g : Gv T v, GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v g))) = ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w)).relIndex (((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w)).map (GlobalTheory.InertHomIdx.lmul (locMat D.sp.cm.sig T.gram h g).1)) := by
  first | exact @GlobalTheory.InertHomIdx.idx_latF_moved | exact GlobalTheory.InertHomIdx.idx_latF_moved | (intros; apply GlobalTheory.InertHomIdx.idx_latF_moved <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAdelicGlueVectorOfSelfDualPrimitiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdelicGlueVector_of_selfDual_primitive : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsLattice D.host.E L₀ → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) → IsPrim Y z (glueLat Y X ι z u L₀ x₀) → IsGlueVec X u L₀ (vA X x₀) := by
  first | exact @GlobalTheory.AdIsom.SelfDualGlue.isGlueVec_of_isSDIn | exact GlobalTheory.AdIsom.SelfDualGlue.isGlueVec_of_isSDIn | (intros; apply GlobalTheory.AdIsom.SelfDualGlue.isGlueVec_of_isSDIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicTermMeanInvariantUnipotentRadicalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicTermMean_invariant_unipotentRadical : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E) (m : Matrix (Fin s) (Fin r) D.host.E), IsIsoFrame W L → m.rank = s → ∀ (n' : NI W L) f, IsThetaFunO ψ V W f → ∫ n in 𝓝, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map (L * m) (incA D))) (ω ((n : GA D V), (n' : GA D W)) f)) 0 ∂κ = ∫ n in 𝓝, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map (L * m) (incA D))) (ω ((n : GA D V), 1) f)) 0 ∂κ := by
  first | exact @GlobalTheory.IsoTermMean.mean_isoTerm_invariant | exact GlobalTheory.IsoTermMean.mean_isoTerm_invariant | (intros; apply GlobalTheory.IsoTermMean.mean_isoTerm_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionFourth
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.BigTop.PtAt.nmjT_at_tied : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (B : RealTB Rc P Dcf Spf Zscf S) (_ : RealPins B.Q) (_ : RealRec B.Q), NChTie D ex.nch → DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I → GlobalTheory.ExportPin.ClassSumPinT B.Q → NMjT B.Q B.Q.cG B.Q.Sx B.Q.nexp ex.nch := by
  intro D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR hTie hDiv hPin
  obtain ⟨jD, eM, hAg, hKs, hSum, hEmb, hLi⟩ := GlobalTheory.T.lattice_family_adoption_first D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR hTie
  have hLat := GlobalTheory.T.lattice_family_adoption_second D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR jD eM hTie hAg hSum
  have hTh := GlobalTheory.T.lattice_family_adoption_third D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hP hR jD eM hDiv hPin hAg hSum
  exact ⟨jD, hAg, ⟨{ eMj := eM, eMj_li := hLi, eMj_lat := hLat, eMj_th := hTh, ks := hKs, eMj_sum := hSum, embW_Ks := hEmb }⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearMapChainCompositeUpdateAddStatement
section
open GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearMapChainComposite_update_add : ∀ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ)
    (A B : V j₀ →ₗ[ℂ] V (j₀ + 1)) (n : ℕ), j₀ < n →
    chainTo (Function.update k j₀ (A + B)) n = chainTo (Function.update k j₀ A) n + chainTo (Function.update k j₀ B) n := by
  first | exact @GlobalTheory.chainTo_update_add | exact GlobalTheory.chainTo_update_add | (intros; apply GlobalTheory.chainTo_update_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearMapChainCompositeUpdateSmulStatement
section
open GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearMapChainComposite_update_smul : ∀ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ)
    (c : ℂ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) (n : ℕ), j₀ < n →
    chainTo (Function.update k j₀ (c • A)) n = c • chainTo (Function.update k j₀ A) n := by
  first | exact @GlobalTheory.ChainSmul.chainTo_update_smul | exact GlobalTheory.ChainSmul.chainTo_update_smul | (intros; apply GlobalTheory.ChainSmul.chainTo_update_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSpanAddSmulLatticeOfFrameCoeffsZmodStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_add_smul_lattice_of_frame_coeffs_zmod : ∀ (I : AutInst) (g : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Af I.F), Formalism.L2.SG.Pf.BunEx.Unip.FH I g e0 f0 z0 bw bwd ew → ∀ v ∈ I.Lf, ∀ (Se : Set (Fin r)) (Sb : Set (Fin k)), (∀ a, a ∉ Se → ZMod' I g (hA I (f0 a) v)) → (∀ a, ZMod' I g (hA I (e0 a) v)) → ZMod' I g (hA I z0 v) → (∀ i, i ∉ Sb → ZMod' I g (hA I (bwd i) v)) → (∀ i, ZMod' I g (hA I (bw i) v)) → v ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo I g (e0 '' Se ∪ bw '' Sb) := by
  first | exact @GlobalTheory.mo_of_coef_mod | exact GlobalTheory.mo_of_coef_mod | (intros; apply GlobalTheory.mo_of_coef_mod <;> assumption)
end

