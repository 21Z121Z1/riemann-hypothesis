import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeIntEmbEmbP
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocGenOfThickenings
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrameOfFreeSec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0577
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0639
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0024
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0641
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegrallyClosedInFractionFieldPowerSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0640
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RosLevel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv.Transport

abbrev Frame {X Y : Scheme.{0}} (L : LB X) (ψ : Y ⟶ X) : Type :=
  LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => 1)

abbrev cocφ {X : Scheme.{0}} {G : Over X} [GrpObj G] {O : Type} [CommRing O] (a : OAct O G) (bar : O → O) (c : O) :
    Fin 4 → (G.left ⟶ G.left) :=
  ![(a.act (1 + c * bar c)).left, (a.act c).left, 𝟙 _, (a.act (c * bar c)).left]

abbrev cocε : Fin 4 → ℤ := ![1, -2, -1, -1]

section Defs

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

def Lies {T : Scheme.{0}} (x' : T ⟶ G.left) (b : T ⟶ D.toPre.P.A.left) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T) (y : Z ⟶ (thickObj R I e G).left),
    y ≫ fGl I G e = r ≫ x' → y ≫ pGl U e = r ≫ b

def FrRel {T : Scheme.{0}} (x' : T ⟶ G.left) (b : T ⟶ D.toPre.P.A.left) (g' : Frame U.LG.L x')
    (g : Frame D.toPre.P.L b) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T) (y : Z ⟶ (thickObj R I e G).left), y ≫ fGl I G e = r ≫ x' →
    ∀ (z : Z) (JM) (JL), Good D.toPre.P.L z JM → Good U.LG.L z JL →
      val g r z JM = wVal U e z JM JL y * val g' r z JL

def RosLevel (f g : G ⟶ G) (a b : D.toPre.P.A ⟶ D.toPre.P.A)
    (uG : LB.Gen (LB.LinComb U.LG.L (rosatiφ G f g) rosatiε))
    (uB : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A a b) rosatiε)) : Prop :=
  ∀ (e : ℕ) (T : Over (Sp (R ⧸ I ^ (e + 1)))) (x y : T ⟶ thickObj R I e G) (z : T.left) (JM) (JL),
    Good D.toPre.P.L z JM → Good U.LG.L z JL →
      val uB (Z := T.left) (lift (push (U.gt e).pG x) (push (U.gt e).pG y)).left z JM =
        wVal U e z JM JL ((x ≫ (Over.pullback (thick R I e)).map f) * y).left *
          (wVal U e z JM JL (x ≫ (Over.pullback (thick R I e)).map f).left)⁻¹ * (wVal U e z JM JL y.left)⁻¹ *
          (wVal U e z JM JL (x * (y ≫ (Over.pullback (thick R I e)).map g)).left)⁻¹ * wVal U e z JM JL x.left *
          wVal U e z JM JL (y ≫ (Over.pullback (thick R I e)).map g).left *
          val uG (Z := T.left) (lift (push (fstG I e G) x) (push (fstG I e G) y)).left z JL

def CocLevel {O : Type} [CommRing O] (a : OAct O G) (b : OAct O D.toPre.P.A) (bar : O → O) (c : O)
    (βG : LB.Gen (LB.LinComb U.LG.L (cocφ a bar c) cocε))
    (βB : LB.Gen (LB.LinComb D.toPre.P.L (cocφ b bar c) cocε)) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ G.left) (y : Fin 4 → (Z ⟶ (thickObj R I e G).left)),
    (∀ k, y k ≫ fGl I G e = x ≫ cocφ a bar c k) →
    ∀ (z : Z) (JM) (JL), Good D.toPre.P.L z JM → Good U.LG.L z JL →
      val βB (y 2 ≫ pGl U e) z JM = (∏ k, wVal U e z JM JL (y k) ^ cocε k) * val βG x z JL

end Defs

def RosSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D A G), IsSemiAbelian G →
    ∀ (f g : G ⟶ G) [IsMonHom f] [IsMonHom g] (a b : D.toPre.P.A ⟶ D.toPre.P.A) [IsMonHom a] [IsMonHom b],
    (∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map f ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map a) →
    (∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map b) →
    ∀ (uG : LB.Gen (LB.LinComb U.LG.L (rosatiφ G f g) rosatiε))
      (uB : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A a b) rosatiε)), uG.IsGen → uB.IsGen →
      LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ uG (zero2 G)) (LB.oneGen U.LG.L) →
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uB (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L) →
      RosLevel U f g a b uG uB

end GlobalTheory.RayEv.Transport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabMapExtendsDense
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef.TriplePull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem range_j {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j = abLocus Y.t.G ∩ Y.s ⁻¹' Set.range (spMap β) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have hy : Y.jQ y ∈ Set.range Y.jQ := ⟨y, rfl⟩
    rw [← Y.ab_gen] at hy
    refine ⟨hy, ?_⟩
    rw [Set.mem_preimage, ← Set.mem_preimage, ← Scheme.Pullback.range_fst]
    exact ⟨Y.jQ y, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [Set.mem_preimage, ← Set.mem_preimage, ← Scheme.Pullback.range_fst] at h2
    obtain ⟨p, rfl⟩ := h2
    have hp : p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := h1
    rw [Y.ab_gen] at hp
    obtain ⟨y, rfl⟩ := hp
    exact ⟨y, rfl⟩

theorem factor_j {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {T : Scheme.{0}} (f : T ⟶ Y.X)
    (hf : Set.range f ⊆ Set.range Y.j) (h : T ⟶ Sp c.F) (hh : h ≫ spMap β = f ≫ Y.s) :
    ∃ u : T ⟶ Xo.XF c, u ≫ Y.j = f := by
  haveI := Y.jQ_open
  let p : T ⟶ pullback Y.s (spMap β) := pullback.lift f h hh.symm
  have hp : Set.range p ⊆ Set.range Y.jQ := by
    rintro _ ⟨x, rfl⟩
    rw [← Y.ab_gen]
    show (p ≫ pullback.fst _ _) x ∈ abLocus _
    rw [pullback.lift_fst]
    exact ((range_j Y).le (hf ⟨x, rfl⟩)).1
  refine ⟨IsOpenImmersion.lift Y.jQ p hp, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

end GlobalTheory.TorRef.TriplePull

namespace GlobalTheory.TorRef.TriplePull

theorem sab_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ξ' : Sp R' ⟶ Z.X) (t' : SAB H (Sp R')), IsCN R' → Dense (ξ' ⁻¹' Set.range Z.j) → SABMap t' X.t (ξ' ≫ π) → Nonempty (SABMap t' Z.t ξ') := by
  intro E _ _ _ H D l Xo c X Z π hπ R' _ _ _ ξ' t' hR hd m
  obtain ⟨hN, hIC, -, -⟩ := hR
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  obtain ⟨t'', ⟨n''⟩⟩ := exists_sabPull ξ' Z.t
  have hU : IsOpen (ξ' ⁻¹' Set.range Z.j) := by
    have e : ξ' ⁻¹' Set.range Z.j =
        abLocus t''.G ∩ (ξ' ≫ Z.s) ⁻¹' Set.range (spMap (algebraMap (𝓞 c.F) c.F)) := by
      rw [range_j, Set.preimage_inter]
      congr 1
      ext x
      exact abLocus_pullback abLocusOne Z.t.semi n''.cart.1 x
    rw [e]
    exact (GlobalTheory.AbLocusOpen.isOpen_abLocus_local t''.G t''.semi).inter (GlobalTheory.T.preimage_generic_fiber_isOpen _ _ _ _)
  let U : (Sp R').Opens := ⟨_, hU⟩
  have hUr : Set.range (U.ι ≫ ξ') ⊆ Set.range Z.j := by
    rintro _ ⟨x, rfl⟩
    have hx : U.ι x ∈ (U : Set (Sp R')) := by rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
    exact hx
  obtain ⟨h, hh⟩ := GlobalTheory.T.factor_through_generic_fiber (𝓞 c.F) c.F U.toScheme ((U.ι ≫ ξ') ≫ Z.s) (by
    rintro _ ⟨x, rfl⟩
    exact ((range_j Z).le (hUr ⟨x, rfl⟩)).2)
  obtain ⟨u, hu⟩ := factor_j Z (U.ι ≫ ξ') hUr h hh
  obtain ⟨t₀, ⟨n₀⟩⟩ := exists_sabPull u Z.oF.t
  have hp0 : IsProper t₀.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n₀.cart.1 Z.oF.proper
  obtain ⟨a1, -⟩ := ObjMaps.exists_sab_comp Z.m n₀
  obtain ⟨a, -⟩ := ObjMaps.exists_sab_cancel n'' (hu ▸ a1 : SABMap t₀ Z.t (U.ι ≫ ξ'))
  obtain ⟨zx, -⟩ := ObjMaps.exists_sab_cancel X.m0.toSABMap
    (by rw [Category.id_comp]; exact Z.m0.toSABMap : SABMap Z.oF.t Xo.univ.t (𝟙 _ ≫ pullback.fst _ _))
  obtain ⟨c1, -⟩ := ObjMaps.exists_sab_comp zx n₀
  obtain ⟨c2, -⟩ := ObjMaps.exists_sab_comp X.m c1
  have hux : (u ≫ 𝟙 _) ≫ X.jQ ≫ pullback.fst _ _ = U.ι ≫ ξ' ≫ π := by
    rw [Category.comp_id]
    change u ≫ X.j = _
    rw [← hπ, ← Category.assoc, hu, Category.assoc]
  obtain ⟨a', -⟩ := ObjMaps.exists_sab_cancel m (hux ▸ c2 : SABMap t₀ X.t (U.ι ≫ ξ' ≫ π))
  haveI : IsNoetherianRing R' := hN
  haveI : IsIntegrallyClosed R' := hIC
  have hNorm : Geo.Tor.IsNormalScheme (Sp R') := GlobalTheory.IsNormalScheme.pred _
  have hDom : IsDominant U.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact hd⟩
  obtain ⟨b, -⟩ := sabExtNormalSt_of_homExtNormalSt GlobalTheory.homExtNormal E H (Sp R') U.toScheme U.ι hNorm
    inferInstance hDom t₀ t' t'' a' a hp0
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp n'' b
  exact ⟨(Category.id_comp ξ') ▸ n⟩

end GlobalTheory.TorRef.TriplePull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelAtOfKnownTheorem
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegLoc

def SiegAt (g : ℕ) (φ : InvFun ℤ) (n : ℕ) : Prop :=
  ∃ (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) (_ : IsOpenImmersion j)
    (G : Over S) (_ : GrpObj G) (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ),
    IsProjOver s ∧ SmoothOfRelativeDimension (g * (g + 1) / 2) s ∧ j ≫ s = F.s ∧
    (∀ x : S, x ∈ closure (Set.range j ∩ s ⁻¹' {s x})) ∧
    IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧ IsGrpPullback F.univ.A G j e ∧ abLocus G = Set.range j ∧
    1 ≤ d ∧ (∀ x : S, HasChart F s j e φ BD d x) ∧
    1 ≤ N ∧ IsGenerated (lbPow (hodge G g) N) ∧
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (hodge G g) (N * k)) (CechPic.dual BD.lb))

theorem siegAt_of_siegelToroidalIntegral (h : GlobalTheory.Published.SiegelToroidalIntegral) (g : ℕ) (hg : 1 ≤ g) :
    ∃ φ : InvFun ℤ, IsPolFan id g φ ∧ ∀ n : ℕ, 3 ≤ n → Odd n → SiegAt g φ n :=
  h g hg

def AgreesPsd (g : ℕ) (φs φ : InvFun ℤ) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Projective ℤ X], Module.finrank ℤ X ≤ g →
    ∀ B ∈ psdCone (id : ℤ → ℤ) X, evalR φs B = evalR φ B

end GlobalTheory.SiegLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimpLabMinValOne
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Sub

variable {O : Type} [CommRing O] (bar : O → O) (q : ℕ)

def LinOnCells (φ χ : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ → χ.LinearOn γ

def Subordinate (φ' φ : InvFun O) : Prop :=
  ∀ χ : InvFun O, LinOnCells bar q φ χ → LinOnCells bar q φ' χ

def SimpLab (φ lab : InvFun O) : Prop :=
  (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ k : ℕ, 0 < k → lab.evalZ ((k : ℤ) • β) = lab.evalZ β) ∧
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ →
      ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ X), IsCell bar φ δ ∧ LinearIndependent ℤ δ ∧
        Function.Injective (fun i => lab.evalZ (δ i)) ∧
        ∀ j, ∃ a : Fin m' → ℝ, (∀ i, 0 ≤ a i) ∧ toReal (γ j) = ∑ i, a i • toReal (δ i)

variable {bar q}

theorem linOnCells_self (φ : InvFun O) : LinOnCells bar q φ φ := fun _ _ _ _ _ _ _ _ h => h.linear

theorem Subordinate.refl (φ : InvFun O) : Subordinate bar q φ φ := fun _ h => h

theorem Subordinate.trans {φ'' φ' φ : InvFun O} (h₁ : Subordinate bar q φ'' φ') (h₂ : Subordinate bar q φ' φ) :
    Subordinate bar q φ'' φ := fun χ h => h₁ χ (h₂ χ h)

theorem Subordinate.linearOn {φ' φ : InvFun O} (h : Subordinate bar q φ' φ) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] (hX : Module.finrank O X ≤ q) {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell bar φ' γ) : φ.LinearOn γ :=
  h φ (linOnCells_self φ) X hX m γ hγ

end Sub

section Inhab

def zeroFun (O : Type) [CommRing O] : InvFun O where
  toFun _ _ := 0
  inv _ _ _ _ _ := rfl
  zero _ := rfl

@[simp] theorem zeroFun_evalZ {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    (β : LinearMap.BilinForm ℤ X) : (zeroFun O).evalZ β = 0 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  simp only [InvFun.evalZ, (zeroFun O).eval_eq hr]
  rfl

example : LinOnCells id 1 (InvFun.minVal ℤ) (InvFun.minVal ℤ) := linOnCells_self _

example : Subordinate id 1 (InvFun.minVal ℤ) (InvFun.minVal ℤ) := Subordinate.refl _

end Inhab

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SkewEqSumRankOneIsotropicStatement
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_eq_sum_rank_one_isotropic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (G : Matrix (Fin N) (Fin N) E) (κ : E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → cc κ = -κ → κ ≠ 0 → ∀ (W : Submodule E (Fin N → E)), (∀ u ∈ W, ∀ v ∈ W, herm G u v = 0) → ∀ n : Matrix (Fin N) (Fin N) E, IsSkew G n → (∀ y, n.mulVec y ∈ W) → ∃ (d : ℕ) (ξ : Fin d → Fin N → E) (t : Fin d → E), (∀ j, ξ j ∈ W) ∧ (∀ j, cc (t j) = t j) ∧ n = ∑ j, (t j * κ) • rk1 G (ξ j) (ξ j) := by
  first | exact @GlobalTheory.UnipKill.skew_eq_sum_rk1 | exact GlobalTheory.UnipKill.skew_eq_sum_rk1 | (intros; apply GlobalTheory.UnipKill.skew_eq_sum_rk1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

namespace GlobalTheory.CycAwayReg
open NumberField

theorem isDedekindDomain_closure {Ω K : Type} [Field Ω] [CharZero Ω] [Field K] [CharZero K] {n : ℕ} [NeZero n]
    [IsCyclotomicExtension {n} ℚ K] (φ : K →+* Ω) {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    IsDedekindDomain (Subring.closure {φ ζ, (n : Ω)⁻¹}) := by
  haveI : NumberField K := IsCyclotomicExtension.numberField {n} ℚ _
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef
  let io : 𝓞 K →+* Ω := φ.comp (algebraMap _ K)
  have hio : Function.Injective io := φ.injective.comp RingOfIntegers.coe_injective
  have hmem : ∀ x, io x ∈ T := by
    intro x
    obtain ⟨y, hy⟩ := (IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton hζ).isIntegral_iff.1
      (RingOfIntegers.isIntegral_coe x)
    have h1 : (y : K) ∈ Subring.closure ({ζ} : Set K) := by
      exact Algebra.mem_adjoin_iff.1 y.2 |> fun h => (Subring.closure_le.2 (by
        rintro _ (⟨r, rfl⟩ | h)
        · exact intCast_mem (Subring.closure ({ζ} : Set K)) r
        · exact Subring.subset_closure h)) h
    have h2 : Subring.closure ({ζ} : Set K) ≤ T.comap φ := by
      rw [Subring.closure_le]
      rintro _ rfl
      exact Subring.subset_closure (Or.inl rfl)
    have h3 : io x = φ y := congrArg φ hy.symm
    rw [h3]
    exact h2 h1
  letI : Algebra (𝓞 K) T := (io.codRestrict _ hmem).toAlgebra
  have hL : IsLocalization (Submonoid.powers (n : 𝓞 K)) T := by
    refine GlobalTheory.CycAway.isLocalization_of_le_closure h0 _ _ (fun x y h => hio (congrArg (fun z : T => (z : Ω)) h))
      (Subring.subset_closure (Or.inr rfl)) (Subring.closure_mono ?_)
    rintro x (rfl | h)
    · exact Or.inl ⟨hζ.toInteger, rfl⟩
    · exact Or.inr h
  have hn' : (n : 𝓞 K) ≠ 0 := by exact_mod_cast NeZero.ne n
  exact IsLocalization.isDedekindDomain _ (powers_le_nonZeroDivisors_of_noZeroDivisors hn') _

theorem isDedekindDomain_cycAway_of_ne_zero {n : ℕ} (hn : n ≠ 0) : IsDedekindDomain (cycAway n) := by
  haveI : NeZero n := ⟨hn⟩
  let K := CyclotomicField n ℚ
  let φ : K →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ)).toRingHom
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  have hz : IsPrimitiveRoot (φ (IsCyclotomicExtension.zeta n ℚ K)) n := hζ.map_of_injective φ.injective
  have he : IsPrimitiveRoot (zeta n) n := Complex.isPrimitiveRoot_exp n hn
  obtain ⟨k, hk, hkc⟩ := hz.eq_pow_of_pow_eq_one he.pow_eq_one
  have hζk := hζ.pow_of_coprime k (hz.pow_iff_coprime (Nat.pos_of_ne_zero hn) k |>.1 (hkc ▸ he))
  have := isDedekindDomain_closure φ hζk
  rwa [map_pow, hkc] at this

theorem isDedekindDomain_cycAway (n : ℕ) : IsDedekindDomain (cycAway n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : cycAway 0 = cycAway 1 := by
      have hb : ∀ m : ℕ, m ≤ 1 → cycAway m = ⊥ := by
        intro m hm
        refine le_antisymm (Subring.closure_le.2 ?_) bot_le
        rintro _ (rfl | rfl)
        · interval_cases m <;> simp [zeta]
        · interval_cases m <;> simp
      rw [hb 0 zero_le_one, hb 1 le_rfl]
    rw [h]
    exact isDedekindDomain_cycAway_of_ne_zero one_ne_zero
  · exact isDedekindDomain_cycAway_of_ne_zero hn.ne'

end GlobalTheory.CycAwayReg

namespace GlobalTheory.CycAwayReg

theorem smooth_over_projective_factorial : ∀ (n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (X : Scheme.{0}) (p : X ⟶ S), IsProjOver s → Smooth s → Smooth p → QuasiCompact p → IsLocallyNoetherian X ∧ CompactSpace X ∧ ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  intro n S s X p hproj hs hp hq
  haveI : IsDedekindDomain (cycAway n) := isDedekindDomain_cycAway n
  haveI : IsRegularRing (cycAway n) := inferInstance
  haveI : Smooth (p ≫ s) := inferInstance
  refine ⟨LocallyOfFiniteType.isLocallyNoetherian (p ≫ s), ?_, fun x => ?_⟩
  · obtain ⟨N, i, hi, hcomp⟩ := hproj
    haveI : IsProper (PSpace.str (cycAway n) N) := isProper_str (cycAway n) N
    haveI : CompactSpace S := by
      rw [← hcomp] at *
      exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str (cycAway n) N)
    exact QuasiCompact.compactSpace_of_compactSpace p
  · haveI : IsRegularRing (X.presheaf.stalk x) :=
      GlobalTheory.ExtendRig.isRegularRing_stalk GlobalTheory.isRegularRing_of_smooth (cycAway n) (p ≫ s) x
    haveI : IsRegularLocalRing (X.presheaf.stalk x) := IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
    haveI : IsDomain (X.presheaf.stalk x) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
    exact ⟨inferInstance, GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE _⟩

end GlobalTheory.CycAwayReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_periodLattice_complexSemiAbelian_eq_top : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsSemiAbelian G → ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective (e) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) ∧ (∀ w, ∃! v : epsPt (y) ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt (y) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) → Submodule.span ℂ {z | e z = 1} = ⊤ := by
  first | exact @GlobalTheory.PeriodSpan.span_ker_eq_top | exact GlobalTheory.PeriodSpan.span_ker_eq_top | (intros; apply GlobalTheory.PeriodSpan.span_ker_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpansAt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayExist

def SpansAt {X : Scheme.{0}} (G : Over X) (L : LB G.left) {S : Type} [CommRing S] (x0 : Sp S ⟶ X) (k : ℕ) : Prop :=
  ∀ s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd (Over.mk x0) G).left) fun _ => (k : ℤ)),
    ∃ (N : ℕ) (c : Fin N → S) (σ : Fin N → H0 L k), ∀ y J, Good L y J → sval s (𝟙 _) y J =
      ∑ i, gs (fst (Over.mk x0) G).left y ⊤ (toΓ S (c i)) * sval (σ i) (snd (Over.mk x0) G).left y J

def VanMod {R : Type} [CommRing R] (I : Ideal R) (l : ℕ) (Z : Over (Sp R)) {B : Scheme.{0}} {L : LB B} {K : Type}
    [Fintype K] {φ : K → (Z.left ⟶ B)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) : Prop :=
  ∀ (T : Scheme.{0}) (r : T ⟶ Z.left) (t : T ⟶ Sp (R ⧸ I ^ (l + 1))), r ≫ Z.hom = t ≫ thick R I l →
    ∀ y J, Good L y J → sval s r y J = 0

end GlobalTheory.RayExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitTorsAlgClosedFractionField
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineNorm

theorem splitTors_of_isAlgClosed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (R : Type) [CommRing R] [IsDomain R] [IsAlgClosed (FractionRing R)] (x : Sp R ⟶ X) (q : ℕ), q ≠ 0 → SplitTors t x q := by
  intro E _ _ _ H X _ t R _ _ _ x q hq Ω _ io w hw
  have hqf : LocallyQuasiFinite (torsion t.G q).hom := (GlobalTheory.T.torsion_flat_locallyQuasiFinite X t.G t.semi q hq).2
  let _ : Algebra (FractionRing R) Ω := io.toAlgebra
  have hic : IsIntegrallyClosedIn (FractionRing R) Ω := by
    rw [isIntegrallyClosedIn_iff]
    refine ⟨io.injective, fun {z} hz => ?_⟩
    exact (minpoly.degree_eq_one_iff.mp (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hz)))
  let l := GlobalTheory.KernelNoTorsion.torsionLift w hw
  have hl : l ≫ torsion.ι t.G q = w := GlobalTheory.KernelNoTorsion.torsionLift_ι w hw
  obtain ⟨x₀, h₀, -⟩ := GlobalTheory.OnePoint.exists_point_of_locallyQuasiFinite (K := FractionRing R) (torsion t.G q).hom Ω l.left
    (spMap (algebraMap R (FractionRing R)) ≫ x) (by
      rw [Over.w l]
      change spMap _ ≫ x = spMap io ≫ spMap _ ≫ x
      rw [← Category.assoc, ← Spec.map_comp]
      rfl)
  refine ⟨x₀ ≫ (torsion.ι t.G q).left, ?_⟩
  rw [← hl, Over.comp_left, ← h₀, Category.assoc]

end GlobalTheory.LineNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitTorsOfGenericLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTors_of_generic_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (x : Sp R ⟶ Y.X) (y : Sp (FractionRing R) ⟶ Xo.XF c), spMap (algebraMap R (FractionRing R)) ≫ x = y ≫ Y.j → ∀ N : ℕ, N ∣ l.A → GlobalTheory.LineNorm.SplitTors Y.t x N := by
  first | exact @GlobalTheory.HTLine.splitTors_of_moduli | exact GlobalTheory.HTLine.splitTors_of_moduli | (intros; apply GlobalTheory.HTLine.splitTors_of_moduli <;> assumption)
end

