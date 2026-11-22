import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToPullChartIffOfFlat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0583
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdlAlongEqIdealAlong
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone GlobalTheory.LocM

namespace GlobalTheory.LocM

theorem stalkId_ofIdealTop {Y : Scheme.{0}} [IsAffine Y] (K : Ideal Γ(Y, ⊤)) (y : Y) :
    FinalTheorems.stalkId (Scheme.IdealSheafData.ofIdealTop K) y = K.map (Y.presheaf.germ ⊤ y trivial).hom := by
  rw [ds_stalkId_eq_map _ ⟨⊤, isAffineOpen_top Y⟩ y trivial, Scheme.IdealSheafData.ofIdealTop_ideal,
    Ideal.map_map, ← CommRingCat.hom_comp]
  congr 2
  exact Y.presheaf.germ_res (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)) y (by trivial)

theorem ideal_top_ofIdealTop {Y : Scheme.{0}} [IsAffine Y] (K : Ideal Γ(Y, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop K).ideal ⟨⊤, isAffineOpen_top Y⟩ = K := by
  rw [Scheme.IdealSheafData.ofIdealTop_ideal]
  have : Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [← Y.presheaf.map_id]; rfl
  rw [this]
  simp

theorem comap_eq_ofIdealTop (X : Scheme.{0}) (J : X.IdealSheafData) (R : Type) [CommRing R] [IsLocalRing R]
    (χ : Sp R ⟶ X) (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
    J.comap χ = Scheme.IdealSheafData.ofIdealTop ((J.ideal U).map (χ.appLE U.1 ⊤ hle).hom) := by
  refine (GlobalTheory.Vanishing.eq_comap_of_stalk fun z => ?_).symm
  have hz : χ z ∈ U.1 := hle trivial
  rw [stalkId_ofIdealTop, ds_stalkId_eq_map J U _ hz, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc]
  congr 3
  exact (Sp R).presheaf.germ_res (homOfLE hle) z (by trivial)

theorem idlAlong_eq_idealAlong (X : Scheme.{0}) (J : X.IdealSheafData) (R : Type) [CommRing R] [IsLocalRing R]
    (χ : Sp R ⟶ X) : idlAlong J χ = idealAlong J χ := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
  unfold idlAlong idealAlong
  rw [comap_eq_ofIdealTop X J R χ ⟨U, hU⟩ hle, ideal_top_ofIdealTop, ds_stalkId_eq_map J ⟨U, hU⟩ _ hx,
    Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
  congr 2

end GlobalTheory.LocM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntStepZero
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag

attribute [local instance] Over.cartesianMonoidalCategory in
open scoped CategoryTheory.Obj in

theorem exists_affine_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Y : Scheme.{0}} (t : SAB H Y) (y : Y) :
    ∃ (U : Y.Opens) (n : ℕ), y ∈ U ∧ ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Y), ⊤ ≤ z ⁻¹ᵁ U →
      Nonempty (Module.Basis (Fin n) S (TanM z t.G)) := by
  have := t.semi.smooth
  obtain ⟨U, hU, hy, -, n, v₀, hv⟩ := GlobalTheory.exists_affine_lieBasis_baseChange Y t.G y ⊤ trivial
  refine ⟨U, n, hy, fun S _ z hz => ?_⟩
  have key : ∀ (f : Γ(Y, U) →+* S) (z : Sp S ⟶ Y), spMap f ≫ hU.fromSpec = z →
      Nonempty (Module.Basis (Fin n) S (TanM z t.G)) := by
    rintro f _ rfl
    have h := isGrpPullback_pullback t.G (spMap f ≫ hU.fromSpec)
    obtain ⟨v', -, hb⟩ := hv S f _ _ h
    let u : Fin n → TanM (spMap f ≫ hU.fromSpec) t.G := fun j =>
      ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT (pushHom h (epsR S) (v' j)) ((ReciprocityTheory.ChartRestriction.G.PullbackSections.isTangent_iff h _).1 (hb.1 j))
    have h1 : FrameBC.Full u := (FrameBC.full_iff h (fun _ => rfl)).1 hb
    refine ⟨Module.Basis.mk (v := u) (Fintype.linearIndependent_iff.2 fun a ha => congrFun
      ((h1 0).unique ha.symm (by simp : (0 : TanM _ t.G) = ∑ i, (0 : Fin n → S) i • u i))) fun w _ => ?_⟩
    obtain ⟨a, rfl, -⟩ := h1 w
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact key _ z (spMap_ev z hU hz)

theorem initSpan_zero' {K N : Type} [CommRing K] [AddCommGroup N] [Module K N] {m : ℕ} (u : Fin m → N) :
    initSpan K u 0 = ⊥ := by
  simp [initSpan]

theorem intStep_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ), IntStep A σ 0 := by
  intro E _ _ _ H Dw l Xo c V _ M X π ty A σ x
  obtain ⟨U₀, n, hx, hb⟩ := exists_affine_basis M.t (π x)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((π ⁻¹ᵁ U₀ : X.Opens) : Set X) from hx) (π ⁻¹ᵁ U₀).isOpen
  obtain ⟨b⟩ := hb _ (tau hU ≫ π) (le_preimage_map π hle (tau_le hU le_rfl))
  refine ⟨U, hU, n, b.reindex (Equiv.emptySum (Fin 0) (Fin n)).symm, hxU, fun K _ w hw u _ j hj => ?_⟩
  obtain rfl : j = 0 := Nat.le_zero.1 hj
  rw [initSpan_zero', initSpan_zero']

end GlobalTheory.DRFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

namespace GlobalTheory.LineNorm

attribute [local instance] Over.cartesianMonoidalCategory

section Models

variable {F : Type} [Field F] [NumberField F]

abbrev PtFn (Y : Var F) : Type := ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ

def FromModel (Y : Var F) (Δ : Y.Dv) (t : Y.X → Y.Fnˣ) (φ : PtFn Y) : Prop :=
  ∃ (M : GlobalTheory.TrueGeo.Model Y) (L : LB M.X) (m : ℕ+) (r : (L.pull M.j).ι → Y.Fnˣ), L.IsLB ∧
    Presents ((m : ℕ) • Δ) (L.pull M.j) r ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X) (i : (L.pull M.j).ι),
      spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit) →
      ((m : ℕ) : ℝ) * φ v e y = Real.log (e.w (valAt y.1 (((t (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Fnˣ) : Y.Fn)))

def Generates {Y : Var F} (M : GlobalTheory.TrueGeo.Model Y) (t : Y.X → Y.Fnˣ) (V : M.X.Opens) (d : ℕ) {n : ℕ}
    (s : Fin n → Y.Fn) : Prop :=
  ∀ y : Y.X, M.j y ∈ V → (∀ i, RegAt y (s i * (((t y)⁻¹ ^ d : Y.Fnˣ) : Y.Fn))) ∧
    ∃ i, UnitAt y (s i * (((t y)⁻¹ ^ d : Y.Fnˣ) : Y.Fn))

def LocMax {Y : Var F} (M : GlobalTheory.TrueGeo.Model Y) (t : Y.X → Y.Fnˣ) (φ : PtFn Y) (z : M.X) : Prop :=
  ∃ (V : M.X.Opens) (d : ℕ+) (n : ℕ) (s : Fin n → Y.Fn), z ∈ V ∧ Generates M t V d s ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X),
      spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ V →
      ((d : ℕ) : ℝ) * φ v e y =
        Real.log (⨆ i, e.w (valAt y.1 (s i * (((t (below y.1))⁻¹ ^ (d : ℕ) : Y.Fnˣ) : Y.Fn))))

end Models

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def IsTanBasis {R : Type} [CommRing R] (x : Sp R ⟶ X) {g : ℕ} (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (e i)) ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (w : Sp (DualNumber S) ⟶ t.G.left),
    IsTanAtG t (spMap φ ≫ x) w →
      ∃! a : Fin g → S, IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ e i) a w

def IsIndep {R : Type} [CommRing R] (x : Sp R ⟶ X) {m : ℕ} (u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  ∀ cf cf' w, IsCombAtG t x u cf w → IsCombAtG t x u cf' w → cf = cf'

def minor {R : Type} [CommRing R] {m g k : ℕ} (a : Fin m → Fin g → R) (hk : k ≤ m) (s : Fin k → Fin g) : R :=
  (Matrix.of fun l i => a (Fin.castLE hk l) (s i)).det

def DlogIs {O : Type} [CommRing O] {x : Sp O ⟶ X} (p n : ℕ) (c : TorsChar t x (p ^ n)) {g : ℕ}
    (e : Fin g → (Sp (DualNumber O) ⟶ t.G.left)) (h : Fin g → O) : Prop :=
  ∀ (a : Fin g → O) (v : Sp (DualNumber O) ⟶ t.G.left), IsCombAtG t x e a v →
    ∀ w : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ Ideal.span {(p : O) ^ n}))) ≫ x) ⟶ t.G,
      w.left = spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}))) ≫ v →
        (c.χ _ w : DualNumber (O ⧸ Ideal.span {(p : O) ^ n})).snd =
          Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) (∑ i, h i * a i)

def SplitTors {R : Type} [CommRing R] (x : Sp R ⟶ X) (q : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] (io : FractionRing R →+* Ω)
    (w : Over.mk (spMap (io.comp (algebraMap R (FractionRing R))) ≫ x) ⟶ t.G), w ^ q = 1 →
      ∃ w₀ : Sp (FractionRing R) ⟶ t.G.left, spMap io ≫ w₀ = w.left

def Thru {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (u : Sp B ⟶ t.G.left) {S : Type} [CommRing S]
    (φ : R →+* S) (w : Sp S ⟶ t.G.left) : Prop :=
  ∃ β : B →+* S, β.comp (algebraMap R B) = φ ∧ spMap β ≫ u = w

structure IsFinPart {R : Type} [CommRing R] (x : Sp R ⟶ X) (q : ℕ) {B : Type} [CommRing B] [Algebra R B]
    (u : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G) : Prop where
  finite : Module.Finite R B
  free : Module.Free R B
  tors : u ^ q = 1
  mono : ∀ (S : Type) [CommRing S] (β β' : B →+* S), β.comp (algebraMap R B) = β'.comp (algebraMap R B) →
    spMap β ≫ u.left = spMap β' ≫ u.left → β = β'
  isOpen : ∀ (S : Type) [CommRing S] (φ : R →+* S) (w : Over.mk (spMap φ ≫ x) ⟶ t.G), w ^ q = 1 →
    (∀ 𝔪 : Ideal S, 𝔪.IsMaximal →
      Thru t u.left ((Ideal.Quotient.mk 𝔪).comp φ) (spMap (Ideal.Quotient.mk 𝔪) ≫ w.left)) → Thru t u.left φ w.left
  one : ∀ (S : Type) [CommRing S] (φ : R →+* S), Thru t u.left φ (1 : Over.mk (spMap φ ≫ x) ⟶ t.G).left
  mul : ∀ (S : Type) [CommRing S] (φ : R →+* S) (w w' : Over.mk (spMap φ ≫ x) ⟶ t.G),
    Thru t u.left φ w.left → Thru t u.left φ w'.left → Thru t u.left φ (w * w').left
  sect : ∀ (k : Type) [Field k] (β : B →+* k), ∃ σ : B →ₐ[R] R, β = (β.comp (algebraMap R B)).comp σ.toRingHom
  inj : ∀ b : B, (∀ σ : B →ₐ[R] R, σ b = 0) → b = 0

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

open Classical in

def stepLog (ρ : Y.X ⟶ X) {m : ℕ}
    (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (q : ℕ) (i : Fin m) : PtFn Y :=
  fun v ε y =>
    if hp : (resP v).Prime then
      haveI := Fact.mk hp
      let ψ : Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        Real.log (grNorm t (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ)
          (lat t (resP v) (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ) (decide (resP v = q)))
          (fun l => spMap (dualMap ψ) ≫ f (below y.1) l) i)
    else 0

structure IsFlagFrame (ρ : Y.X ⟶ X) {m : ℕ} (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left))
    (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ) : Prop where
  tan : ∀ y l, IsTanAtG t (stalkPt Y y ≫ ρ) (f y l)
  tri : ∀ y i, ∃ cf : Fin m → Y.Fn, cf i = d y i ∧ (∀ k, i < k → cf k = 0) ∧
    IsCombAtG t (genericPt Y ≫ ρ)
      (fun k => spMap (dualMap (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField)) ≫ f y k) cf (u₀ i)
  indep : ∀ y (k : Type) [Field k] (ψ : Y.X.presheaf.stalk y →+* k),
    IsIndep t (spMap ψ ≫ stalkPt Y y ≫ ρ) (fun l => spMap (dualMap ψ) ≫ f y l)

end Tangent

end GlobalTheory.LineNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
section
set_option autoImplicit false

noncomputable section

open Topology

namespace GlobalTheory.ShFam.Hor.LogCh

def IsLatBasis {g r : ℕ} (K : Set (Fin g → ℂ)) (b : Fin r → Fin g → ℂ) : Prop :=
  LinearIndependent ℝ b ∧ ∀ w, w ∈ K ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • b j

def IsLatFam {n g : ℕ} (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) : Prop :=
  IsOpen B ∧ (∀ b ∈ B, ∃ H : AddSubgroup (Fin g → ℂ), (H : Set (Fin g → ℂ)) = K b) ∧
    IsOpen {q : (Fin n → ℂ) × (Fin g → ℂ) | q.1 ∈ B ∧ q.2 ∉ K q.1} ∧
    ∀ b₀ ∈ B, ∀ w₀ ∈ K b₀, ∃ ζ : (Fin n → ℂ) → Fin g → ℂ, ζ b₀ = w₀ ∧ AnalyticAt ℂ ζ b₀ ∧
      ∀ᶠ q in 𝓝 (b₀, w₀), q.2 ∈ K q.1 ↔ q.2 = ζ q.1

section Exp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

def IsExpAt (t : SAB H X) (y : Sp ℂ ⟶ X) {g : ℕ} (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) : Prop :=
  (∀ v w, e (v + w) = e v * e w) ∧
    (∀ w, ∃! v, IsTanAtG t y v ∧ IsDerivAt0 (fun u => (e u).left) w v) ∧
    ∀ v, IsTanAtG t y v → ∃! w, IsDerivAt0 (fun u => (e u).left) w v

end Exp

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTangentOfUniqueIntegralLift
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.LatPush

open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (mu : SABMap t' t f)

theorem exists_ptEquiv {T : Scheme.{0}} (q : T ⟶ X') (q' : T ⟶ X) (h : q ≫ f = q') :
    ∃ e : (Over.mk q ⟶ t'.G) ≃* (Over.mk q' ⟶ t.G), ∀ g, (e g).left = g.left ≫ mu.φ := by
  subst h
  refine ⟨MulEquiv.ofBijective (pushHom mu.cart (Over.mk q)) ⟨fun a b hab => ?_, fun a => ?_⟩, fun g => rfl⟩
  · exact Over.OverMorphism.ext (mu.cart.1.hom_ext (congrArg (fun z => z.left) hab)
      ((Over.w a).trans (Over.w b).symm))
  · obtain ⟨w, h1, h2⟩ := OpenReg.exists_lift mu q a.left (Over.w a)
    exact ⟨Over.homMk w h1, Over.OverMorphism.ext h2⟩

theorem spMap_alg {O B B' : Type} [CommRing O] [CommRing B] [CommRing B'] [Algebra O B] [Algebra O B']
    (φ : B →ₐ[O] B') : spMap φ.toRingHom ≫ spMap (algebraMap O B) = spMap (algebraMap O B') := by
  rw [OpenReg.spMap_comp]
  congr 1
  exact RingHom.ext fun a => φ.commutes a

theorem dualMap_alg {O O' : Type} [CommRing O] [CommRing O'] (φ : O →+* O') :
    spMap (dualMap φ) ≫ spMap (algebraMap O (DualNumber O)) =
      spMap (algebraMap O' (DualNumber O')) ≫ spMap φ := by
  rw [OpenReg.spMap_comp, OpenReg.spMap_comp, GlobalTheory.Frames.FramedBaseChange.dualMap_comp_alg]

theorem dlogDvd_iff {O : Type} [CommRing O] (x : Sp O ⟶ X') (p m : ℕ) (v : Sp (DualNumber O) ⟶ t'.G.left)
    (hv : v ≫ t'.G.hom = spMap (algebraMap O (DualNumber O)) ≫ x) :
    DlogDvd t' x p m v ↔ DlogDvd t (x ≫ f) p m (v ≫ mu.φ) := by
  choose e he using fun (B : Type) [CommRing B] [Algebra O B] =>
    exists_ptEquiv mu (spMap (algebraMap O B) ≫ x) (spMap (algebraMap O B) ≫ x ≫ f) (Category.assoc _ _ _)
  constructor
  · intro h n c g hg
    let c' : TorsChar t' x (p ^ n) :=
      { χ := fun B _ _ _ g => c.χ B (e B g)
        mul := fun B _ _ _ g g' h1 h2 => by
          rw [map_mul]
          exact c.mul B _ _ (by rw [← map_pow, h1, map_one]) (by rw [← map_pow, h2, map_one])
        nat := fun B B' _ _ _ _ _ _ φ g g' h1 h2 =>
          c.nat B B' φ _ _ (by rw [← map_pow, h1, map_one]) (by rw [he, he, h2, Category.assoc]) }
    obtain ⟨g', rfl⟩ := (e _).surjective g
    refine h n c' g' (mu.cart.1.hom_ext ?_ ?_)
    · rw [← he, hg, Category.assoc]
    · rw [Over.w, Category.assoc, hv, ← Category.assoc, OpenReg.spMap_comp]
      show spMap _ ≫ x = spMap _ ≫ x
      congr 2
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl']
  · intro h n c g hg
    let c' : TorsChar t (x ≫ f) (p ^ n) :=
      { χ := fun B _ _ _ g => c.χ B ((e B).symm g)
        mul := fun B _ _ _ g g' h1 h2 => by
          rw [map_mul]
          exact c.mul B _ _ (by rw [← map_pow, h1, map_one]) (by rw [← map_pow, h2, map_one])
        nat := fun B B' _ _ _ _ _ _ φ g g' h1 h2 =>
          c.nat B B' φ _ _ (by rw [← map_pow, h1, map_one]) (mu.cart.1.hom_ext
            (by rw [← he, Category.assoc, ← he, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, h2])
            (by
              rw [Over.w, Category.assoc, Over.w]
              show spMap _ ≫ x = spMap _ ≫ spMap _ ≫ x
              rw [← Category.assoc, spMap_alg])) }
    have := h n c' (e _ g) (by rw [he, hg, Category.assoc])
    simpa only [c', MulEquiv.symm_apply_apply] using this

theorem lat_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (mu : SABMap t' t f) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ) (b : Bool) (xO : Sp ↥(intO C) ⟶ X'), (∀ y : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ xO ≫ f → y = xO ≫ f) → ∀ v, IsTanAtG t' (spMap (intO C).subtype ≫ xO) v → (v ∈ lat t' p (spMap (intO C).subtype ≫ xO) b ↔ v ≫ mu.φ ∈ lat t p (spMap (intO C).subtype ≫ xO ≫ f) b) := by
  intro E _ _ _ H X X' t t' f mu C _ _ p b xO hu v hv
  cases b
  · constructor
    · rintro ⟨y, hy, vO, h1, h2⟩
      exact ⟨y ≫ f, by rw [← Category.assoc, hy, Category.assoc], vO ≫ mu.φ,
        (OpenReg.tan_iff mu rfl h1.1).2 h1, by rw [← Category.assoc, h2]⟩
    · rintro ⟨y, hy, vO, h1, h2⟩
      obtain rfl := hu y hy
      obtain ⟨w, a1, rfl⟩ := OpenReg.exists_lift mu (spMap (algebraMap _ (DualNumber ↥(intO C))) ≫ xO) vO
        (by rw [h1.1, Category.assoc])
      refine ⟨xO, rfl, w, (OpenReg.tan_iff mu rfl a1).1 h1, mu.cart.1.hom_ext ?_ ?_⟩
      · rw [Category.assoc, h2]
      · rw [Category.assoc, a1, hv.1, ← Category.assoc, dualMap_alg, Category.assoc]
  · constructor
    · rintro ⟨y, hy, m, vO, h1, h2, h3⟩
      exact ⟨y ≫ f, by rw [← Category.assoc, hy, Category.assoc], m, vO ≫ mu.φ,
        (OpenReg.tan_iff mu rfl h1.1).2 h1, by rw [← Category.assoc, h2, Category.assoc],
        (dlogDvd_iff mu y p m vO h1.1).1 h3⟩
    · rintro ⟨y, hy, m, vO, h1, h2, h3⟩
      obtain rfl := hu y hy
      obtain ⟨w, a1, rfl⟩ := OpenReg.exists_lift mu (spMap (algebraMap _ (DualNumber ↥(intO C))) ≫ xO) vO
        (by rw [h1.1, Category.assoc])
      refine ⟨xO, rfl, m, w, (OpenReg.tan_iff mu rfl a1).1 h1, mu.cart.1.hom_ext ?_ ?_,
        (dlogDvd_iff mu xO p m w a1).2 h3⟩
      · rw [Category.assoc, h2, Category.assoc]
      · rw [Category.assoc, a1, Category.assoc, hv.1, ← Category.assoc, dualMap_alg, ← Category.assoc,
          ← Category.assoc, OpenReg.epsMul_over]

end GlobalTheory.ShFam.LatPush
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsometryConjTransvectionScale
section
namespace GlobalTheory.UnipKill

open ReciprocityTheory.ChartRestriction.G.FD NumberField

theorem mul_rk1_self_of_scale {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    (G g : Matrix (Fin N) (Fin N) E) (ξ : Fin N → E) (ε : E) (hg : IsIsom G g)
    (hξ : g.mulVec ξ = ε • ξ) (hc : cc ε = ε) (h0 : ε ≠ 0) :
    g * rk1 G ξ ξ = ε ^ 2 • (rk1 G ξ ξ * g) := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  have h1 : g.mulVec (ε⁻¹ • ξ) = ξ := by
    rw [Matrix.mulVec_smul, hξ, smul_smul, inv_mul_cancel₀ h0, one_smul]
  have h2 : herm G (g.mulVec x) ξ = ε⁻¹ * herm G x ξ := by
    have h3 := hg x (ε⁻¹ • ξ)
    rw [h1, herm_smul_right, cc_inv, hc] at h3
    exact h3
  rw [← Matrix.mulVec_mulVec, one_add_smul_vecMulVec_mulVec, Matrix.mulVec_smul, hξ, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, one_add_smul_vecMulVec_mulVec, h2, smul_smul, smul_smul]
  congr 1
  field_simp

theorem mul_transvMat_of_scale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (G g : Matrix (Fin N) (Fin N) E) (ξ : Fin N → E) (ε : E), IsIsom G g → g.mulVec ξ = ε • ξ →
    cc ε = ε → ε ≠ 0 → ∀ α : E, g * transvMat G ξ α = transvMat G ξ (ε ^ 2 * α) * g := by
  intro E _ _ _ N G g ξ ε hg hξ hc h0 α
  rw [transvMat_eq, transvMat_eq, mul_add, add_mul, mul_one, one_mul, mul_smul_comm,
    smul_mul_assoc, mul_rk1_self_of_scale G g ξ ε hg hξ hc h0, smul_smul, mul_comm α]

end GlobalTheory.UnipKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorFlagDensityGlueLowerUnitriangular
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

variable {r p q : ℕ}

theorem blockDiag_conj (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (a : Matrix (Fin p) (Fin p) ℂ)
    (b : Matrix (Fin q) (Fin q) ℂ) :
    (fromBlocks a 0 0 b)ᴴ * S * fromBlocks a 0 0 b =
      fromBlocks (aᴴ * S.toBlocks₁₁ * a) (aᴴ * S.toBlocks₁₂ * b) (bᴴ * S.toBlocks₂₁ * a) (bᴴ * S.toBlocks₂₂ * b) := by
  conv_lhs => rw [← fromBlocks_toBlocks S]
  simp [fromBlocks_conjTranspose, fromBlocks_multiply]

theorem schur_blockDiag_conj (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (a : Matrix (Fin p) (Fin p) ℂ)
    {b : Matrix (Fin q) (Fin q) ℂ} (hb : IsUnit b.det) :
    schur ((fromBlocks a 0 0 b)ᴴ * S * fromBlocks a 0 0 b) = aᴴ * schur S * a := by
  have hb' : IsUnit bᴴ.det := by rw [det_conjTranspose]; exact hb.star
  rw [blockDiag_conj, schur, schur]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
  rw [mul_nonsing_inv_cancel_left _ _ hb, nonsing_inv_mul_cancel_left _ _ hb']

theorem reindex_conj_glue {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) (A : Matrix (Fin r) (Fin r) ℂ)
    (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) :
    reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
      (fromBlocks (uni w.2.2) 0 0 (uni w.2.1))ᴴ * shear (reindex e e A) (toMat w.1) *
        fromBlocks (uni w.2.2) 0 0 (uni w.2.1) := by
  have h1 : reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
      (reindex e e (uni (glue e w)))ᴴ * reindex e e A * reindex e e (uni (glue e w)) := by
    simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
  have h2 : fromBlocks (uni w.2.2) (toMat w.1 * uni w.2.1) 0 (uni w.2.1) =
      (fromBlocks 1 (toMat w.1) 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *
        fromBlocks (uni w.2.2) 0 0 (uni w.2.1) := by
    simp [fromBlocks_multiply]
  rw [h1, reindex_uni_glue he, h2, shear]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem dens_glue : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ) (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)), IsUnit (shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det → dens A (glue e w) = dens (shear (reindex e e A) (toMat w.1)).toBlocks₂₂ w.2.1 * ‖(shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det‖ ^ (-(2 * p : ℤ)) * dens (schur (shear (reindex e e A) (toMat w.1))) w.2.2 := by
  intro r p q e he A w hS
  have hR := reindex_conj_glue he A w
  set S := shear (reindex e e A) (toMat w.1) with hSdef
  set H := (uni (glue e w))ᴴ * A * uni (glue e w) with hH
  have h22 : (reindex e e H).toBlocks₂₂ = (uni w.2.1)ᴴ * S.toBlocks₂₂ * uni w.2.1 := by
    rw [hR, blockDiag_conj, toBlocks_fromBlocks₂₂]
  have hd : (reindex e e H).toBlocks₂₂.det = S.toBlocks₂₂.det := by
    rw [h22, det_mul, det_mul, det_conjTranspose, det_uni]; simp
  have hs : schur (reindex e e H) = (uni w.2.2)ᴴ * schur S * uni w.2.2 := by
    rw [hR, schur_blockDiag_conj _ _ (by rw [det_uni]; exact isUnit_one)]
  obtain ⟨m1, m2⟩ := GlobalTheory.T.leadingMinor_blockDecomposition r p q e he H (hd ▸ hS)
  rw [hd, hs] at m2
  rw [h22] at m1
  unfold dens
  rw [← hH, ← Equiv.prod_comp e.symm, Fintype.prod_sum_type]
  have a1 : ∀ a : Fin q, lminor H (e.symm (Sum.inr a)).castSucc =
      lminor ((uni w.2.1)ᴴ * S.toBlocks₂₂ * uni w.2.1) a.castSucc := fun a => m1 _ _ (by simp [he.2])
  have a2 : ∀ a : Fin p, lminor H (e.symm (Sum.inl a)).castSucc =
      S.toBlocks₂₂.det * lminor ((uni w.2.2)ᴴ * schur S * uni w.2.2) a.castSucc := fun a => m2 _ _ (by simp [he.1])
  simp only [a1, a2, norm_mul, mul_zpow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← zpow_natCast, ← _root_.zpow_mul, neg_mul]
  ring

end GlobalTheory.FlagFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorSignsOverBoundedFlagDomainStatement
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leading_minor_signs_over_bounded_flag_domain : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ y : Low r → ℂ, toMat (base e y) ∈ hcDom p q → ∀ i : Fin (r + 1), 0 < psgn q i * (lminor ((uni y)ᴴ * A * uni y) i).re := by
  first | exact @GlobalTheory.FlagFibre.signs_over_dom | exact GlobalTheory.FlagFibre.signs_over_dom | (intros; apply GlobalTheory.FlagFibre.signs_over_dom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesCompStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_eigenspace_frame_coordinates_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (R' : Type) [CommRing R'] (φ' : c.F →+* R') (x' : Sp R' ⟶ Z.X) (g : EigFrame Z φ' x') (R'' : Type) [CommRing R''] (φ'' : c.F →+* R'') (x'' : Sp R'' ⟶ Z.X) (h : EigFrame Z φ'' x'') (ψ : R →+* R') (ψ' : R' →+* R'') (A : Mat Dw.mult R') (A' : Mat Dw.mult R''), IsLocalRing R'' → f.Coord ψ g A → g.Coord ψ' h A' → f.Coord (ψ'.comp ψ) h (A' * A.map ψ') := by
  first | exact @GlobalTheory.ShFam.CoordComp.coord_comp | exact GlobalTheory.ShFam.CoordComp.coord_comp | (intros; apply GlobalTheory.ShFam.CoordComp.coord_comp <;> assumption)
end

