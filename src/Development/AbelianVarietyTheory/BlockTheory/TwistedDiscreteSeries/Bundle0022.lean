import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CommutingRationalGroups
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levV (i : Fin D.R.m) (t : T) : Bridge.LevDat D (Vc D i) := levEnv (Vc D i) (R.βV i) (R.datVt i t)

def IsLiftV (i : Fin D.R.m) (t : T) (g : G) (κ : (levV R i t).Q) : Prop :=
  rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((κ : Bridge.Gf (Vc D i)) : GL _ _)) = R.eG g

def IsLiftW (i : Fin D.R.m) (g : G) (κ : GA D (Wc D i)) : Prop :=
  IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ

def IsAlgV (i : Fin D.R.m) (t : T) (c : G → ℂ) (κ : G → (levV R i t).Q) (x y : (R.HV i t).H) : Prop :=
  (R.HV i t).e y = ∑ g, c g • Bridge.g0Act (levV R i t).ch (κ g) ((R.HV i t).e x)

def algW (i : Fin D.R.m) (c : G → ℂ) : MMap (R.MW i (sg0 D A)) →ₗ[ℂ] MMap (R.MW i (sg0 D A)) :=
  postOn _ (gaL (Wc D i) (R.βW i) (R.datWp i R.triv) R.eG c)

theorem algW_eC (i : Fin D.R.m) :
    algW R i (RealDat.eC (A := A) (sg0 D A)) = postOn _ (R.eWf i (sg0 D A)) := rfl

structure Commutes (i : Fin D.R.m) (t : T) : Prop where

  liftV : ∀ g, ∃ κ, IsLiftV R i t g κ

  liftW : ∀ g, ∃ κ, IsLiftW R i g κ

  act : ∀ g κ, IsLiftV R i t g κ → ∀ x : (R.HV i t).H,
    ∃ y : (R.HV i t).H, (R.HV i t).e y = Bridge.g0Act (levV R i t).ch κ ((R.HV i t).e x)

  grp : ∀ g κ, IsLiftV R i t g κ → ∀ x y : (R.HV i t).H,
    (R.HV i t).e y = Bridge.g0Act (levV R i t).ch κ ((R.HV i t).e x) →
      R.thF i t y = FWT.actW R i (sg0 D A) g (R.thF i t x)

  grpAt : ∀ g κ κ', IsLiftV R i t g κ → IsLiftW R i g κ' → ∀ x y : (R.HV i t).H,
    (R.HV i t).e y = Bridge.g0Act (levV R i t).ch κ ((R.HV i t).e x) →
      ∀ v h, R.thF i t y v h = R.thF i t x v (h * κ')

  alg : ∀ (c : G → ℂ) (κ : G → (levV R i t).Q), (∀ g, IsLiftV R i t g (κ g)) → ∀ x y : (R.HV i t).H,
    IsAlgV R i t c κ x y → R.thF i t y = algW R i c (R.thF i t x)

  good : ∀ κ : G → (levV R i t).Q, (∀ g, IsLiftV R i t g (κ g)) → ∀ x y : (R.HV i t).H,
    IsAlgV R i t (RealDat.eC (A := A) (sg0 D A)) κ x y → R.thF i t y = postOn _ (R.eWf i (sg0 D A)) (R.thF i t x)

  goodG : ∀ κ : G → (levV R i t).Q, (∀ g, IsLiftV R i t g (κ g)) → ∀ x y : (R.HV i t).H,
    IsAlgV R i t (RealDat.eC (A := A) (sg0 D A)) κ x y → R.thG i t y = R.thG i t x

  ratGrp : ∀ (g : G) (f : (A.MtCSD i t).Forms),
    R.thF i t (R.jV i t (A.leftGroupActionLift i t g f)) = FWT.actW R i (sg0 D A) g (R.thF i t (R.jV i t f))

  ratGood : ∀ f : (A.MtCSD i t).Forms,
    R.thF i t (R.jV i t ((A.MtCSD i t).gaOp (A.leftGroupActionLift i t) (idemOf A.X) f)) =
      postOn _ (R.eWf i (sg0 D A)) (R.thF i t (R.jV i t f))

  ratGoodG : ∀ f : (A.MtCSD i t).Forms,
    R.thG i t (R.jV i t ((A.MtCSD i t).gaOp (A.leftGroupActionLift i t) (idemOf A.X) f)) = R.thG i t (R.jV i t f)

def ThetaCommutes (F : Face D A) : Prop :=
  R.Char F → ∀ (i : Fin D.R.m) (t : T), Commutes R i t

end GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeSupportLattices
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Forms

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] [Fintype G] (Φ : FormsL LL Ks WL W G)

def ball (la : HeightOneSpectrum (𝓞 Ks)) : Set Φ.WK := {f | ∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1}

def resW (hL : WL →ₗ[LL] WL) (hW : ∀ x ∈ Φ.WK, hL x ∈ Φ.WK) : Φ.WK →ₗ[Ks] Φ.WK :=
  (hL.restrictScalars Ks).restrict hW

def LiesOver (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra Ks K'] (O : ValuationSubring K') : Prop :=
  ∀ x : Ks, algebraMap Ks K' x ∈ O ↔ FinitePlace.mk la x ≤ 1

def latK (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra Ks K'] (O : ValuationSubring K') :
    Submodule O (K' ⊗[Ks] Φ.WK) :=
  Submodule.span O ((fun f : Φ.WK => (1 : K') ⊗ₜ[Ks] f) '' ball Φ la)

def latKIn (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra Ks K'] (O : ValuationSubring K')
    (V : Submodule LL WL) : Submodule O (K' ⊗[Ks] Φ.WK) :=
  latK Φ la O ⊓ (((V.restrictScalars Ks).comap Φ.WK.subtype).baseChange K').restrictScalars O

def latL (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra LL K'] (O : ValuationSubring K') :
    Submodule O (K' ⊗[LL] WL) :=
  Submodule.span O ((fun f : Φ.WK => (1 : K') ⊗ₜ[LL] (f : WL)) '' ball Φ la)

def latLIn (la : HeightOneSpectrum (𝓞 Ks)) {K' : Type} [Field K'] [Algebra LL K'] (O : ValuationSubring K')
    (V : Submodule LL WL) : Submodule O (K' ⊗[LL] WL) :=
  latL Φ la O ⊓ (V.baseChange K').restrictScalars O

structure Keeps (la : HeightOneSpectrum (𝓞 Ks)) (hL : WL →ₗ[LL] WL) (hW : ∀ x ∈ Φ.WK, hL x ∈ Φ.WK) : Prop where

  sup : ∀ f : Φ.WK, (∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) → ∀ y : Φ.Pt la, Φ.nrm la y ⟨hL f, hW f f.2⟩ ≤ 1

  rho : ∀ g : G, hL ∘ₗ Φ.ρ g = Φ.ρ g ∘ₗ hL

  eOp : ∀ eC : G → LL, hL ∘ₗ Φ.eOp eC = Φ.eOp eC ∘ₗ hL

  typeP : ∀ (J : Subgroup G) (lam : J →* LLˣ), ∀ x ∈ Φ.typeP J lam, hL x ∈ Φ.typeP J lam

  good : ∀ eC : G → LL, ∀ x ∈ Φ.good eC, hL x ∈ Φ.good eC

  overK : ∀ (K' : Type) [Field K'] [Algebra Ks K'] (O : ValuationSubring K'), LiesOver la O →
    (∀ x ∈ latK Φ la O, (resW Φ hL hW).baseChange K' x ∈ latK Φ la O) ∧
    ∀ (J : Subgroup G) (lam : J →* LLˣ),
      (∀ x ∈ latKIn Φ la O (Φ.typeP J lam), (resW Φ hL hW).baseChange K' x ∈ latKIn Φ la O (Φ.typeP J lam)) ∧
      ∀ eC : G → LL, ∀ x ∈ latKIn Φ la O (Φ.Wgood J lam eC),
        (resW Φ hL hW).baseChange K' x ∈ latKIn Φ la O (Φ.Wgood J lam eC)

  overL : ∀ (K' : Type) [Field K'] [Algebra LL K'] [Algebra Ks K'] [IsScalarTower Ks LL K'] (O : ValuationSubring K'),
    LiesOver la O →
    (∀ x ∈ latL Φ la O, hL.baseChange K' x ∈ latL Φ la O) ∧
    ∀ (J : Subgroup G) (lam : J →* LLˣ),
      (∀ x ∈ latLIn Φ la O (Φ.typeP J lam), hL.baseChange K' x ∈ latLIn Φ la O (Φ.typeP J lam)) ∧
      ∀ eC : G → LL, ∀ x ∈ latLIn Φ la O (Φ.Wgood J lam eC), hL.baseChange K' x ∈ latLIn Φ la O (Φ.Wgood J lam eC)

end Forms

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def hkC {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) : ℂ :=
  ((((R.C.mu0 i).val P : ℂˣ) : ℂ) ^ k)⁻¹ * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹

theorem two_mul_half : 2 * (D.R.nV / 2) = D.R.nV := Nat.two_mul_div_two_of_even (kapDom D).2

def IsHkData {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))) : Prop :=
  Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ k ≤ D.R.r ∧
    IsHeckeAt (Wc D i) P k α ∧ Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc

def OffChar {Ks : Type} [Field Ks] [NumberField Ks] (P : Formalism.L2.DIV.Pl D.host.E) (la : HeightOneSpectrum (𝓞 Ks)) : Prop :=
  ∀ p : ℕ, p.Prime → (p : 𝓞 D.host.E) ∈ P.asIdeal → (p : 𝓞 Ks) ∉ la.asIdeal

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def ConstPinned (i : Fin D.R.m) : Prop :=
  ∃ (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ),
    O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange ∧
    O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) ∧
    O.OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O.s0) ph

theorem constPinned_of (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m) (hp : OMPins T R κ v₀ O i)
    (hr : OneMapRow0 T R κ v₀ O i) (hc : CTie T R κ v₀ O i) : ConstPinned T R κ v₀ i :=
  ⟨O i, (hc hr).choose, hp.1, hp.2, (hc hr).choose_spec⟩

structure ReadAt0 (i : Fin D.R.m) : Prop where
  ex : ∀ hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i, JEvAt T R κ v₀ i (sg0 D A) hV
  inj : Function.Injective ((R.FW i).j (sg0 D A))
  rho : RhoIs (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (actW R i (sg0 D A)) (R.FW i).chi (R.FW i).ρ
  const : ConstPinned T R κ v₀ i

theorem readAt0_of (hj : JEvExists T R κ v₀) (fw : FWTie T R κ v₀) (hu : R.LUnif) (i : Fin D.R.m)
    (hc : ConstPinned T R κ v₀ i) : ReadAt0 T R κ v₀ i where
  ex hV := hj i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV
  inj := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    by_contra h
    have h1 := (hu i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h)
    exact h1.ne_zero 0 hx
  rho := (hu i (sg0 D A)).2.2
  const := hc

def HkSupAt (i : Fin D.R.m) : Prop :=
  ∀ (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))), IsHkData R i P k α Rc →
    ∀ (hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)),
      HeckeJ.IsHkJ (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (heckeOn (R.MW i (sg0 D A)) Rc) (hkC R i P k) hL →
      ∀ (hW : ∀ x ∈ (R.FW i).WK, hL x ∈ (R.FW i).WK) (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OffChar P la →
        Keeps (R.FW i) la hL hW

def HkSup : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), R.Char F →
    ∀ (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
      (_fw : FWTie T R κ v₀) (i : Fin D.R.m), ReadAt0 T R κ v₀ i → HkSupAt T R i

end GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Local

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def heckeScalar (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) : ℂ :=
  (((R.C.mu0 i).val P : ℂˣ) : ℂ) ^ (-(k : ℤ)) * ((Nat.card (kP P) : ℕ) : ℂ) ^ (-((k * (D.R.nV / 2) : ℕ) : ℤ))

def GoodPlace (P : Pl D.host.E) : Prop :=
  Bridge.SplitOff P (R.Sb : Set (Pl D.host.E)) ∧ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal

def IsCosetSys (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) (Rc : Finset (GA D (Wc D i))) : Prop :=
  ∃ α : GA D (Wc D i), IsHeckeAt (Wc D i) P k α ∧ Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc

def ReadAs (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) (Rc : Finset (GA D (Wc D i)))
    (hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) : Prop :=
  HeckeJ.IsHkJ (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (heckeOn (R.MW i (sg0 D A)) Rc) (heckeScalar R i P k) hL

def RationalHeckeAt (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) : Prop :=
  ∃ hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL),
    (∀ Rc, IsCosetSys R i P k Rc → ReadAs R i P k Rc hL) ∧ ∀ x ∈ (R.FW i).WK, hL x ∈ (R.FW i).WK

def RationalHecke (i : Fin D.R.m) : Prop :=
  ∀ P : Pl D.host.E, GoodPlace R P → ∀ k : ℕ, k ≤ D.R.r → RationalHeckeAt R i P k

theorem readAs_iff (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) (Rc : Finset (GA D (Wc D i)))
    (hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) :
    ReadAs R i P k Rc hL ↔ ∀ x, (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (hL x)) =
      heckeScalar R i P k • heckeOn (R.MW i (sg0 D A)) Rc ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) x)) := Iff.rfl

theorem RationalHeckeAt.row {i : Fin D.R.m} {P : Pl D.host.E} {k : ℕ} (h : RationalHeckeAt R i P k)
    {α : GA D (Wc D i)} (hα : IsHeckeAt (Wc D i) P k α) {Rc : Finset (GA D (Wc D i))}
    (hR : Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc) :
    HeckeJ.HkJRow (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (heckeOn (R.MW i (sg0 D A)) Rc)
      (heckeScalar R i P k) (R.FW i).WK := by
  obtain ⟨hL, h1, h2⟩ := h
  exact ⟨hL, h1 Rc ⟨α, hα, hR⟩, h2⟩

theorem heckeScalar_zero (i : Fin D.R.m) (P : Pl D.host.E) : heckeScalar R i P 0 = 1 := by
  simp [heckeScalar]

theorem readAs_id (i : Fin D.R.m) (P : Pl D.host.E) : ReadAs R i P 0 {1} LinearMap.id := by
  intro x
  rw [heckeScalar_zero, one_smul]
  ext v g
  simp [heckeOn, postOn, heckeLin]

end Local

section Comparison₂

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def RationalHeckeUnpinned : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) → ∀ i : Fin D.R.m, RationalHecke R i

def FramePinned (i : Fin D.R.m) : Prop :=
  ∃ O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0), OMPins T R κ v₀ O i ∧ CTie T R κ v₀ O i

def RationalHeckeTie : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) → ∀ i : Fin D.R.m, FramePinned T R κ v₀ i → RationalHecke R i

theorem RationalHeckeUnpinned.tie (h : RationalHeckeUnpinned T R F κ v₀) : RationalHeckeTie T R F κ v₀ :=
  fun hc ht i _ => h hc ht i

end Comparison₂

def RationalHeckeTieAll : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    RationalHeckeTie T R F κ v₀

end GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ContainsRayField {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (M : ℕ) : Prop :=
  ∀ 𝔓 : HeightOneSpectrum (𝓞 L), ((M : ℕ) : 𝓞 L) ∉ 𝔓.asIdeal →
    ∃ (f : ℕ) (α : 𝓞 K),
      Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm (𝔓.asIdeal.comap (RingOfIntegers.mapRingHom φ)) ^ f ∧
      (𝔓.asIdeal.comap (RingOfIntegers.mapRingHom φ)) ^ f = Ideal.span {α} ∧ ((M : ℕ) : 𝓞 K) ∣ α - 1

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Tuple

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

variable (D) in

def embK : D.host.K →+* D.what₂.LL := D.embE.comp (algebraMap D.host.K D.host.E)

def tupLevel (t : T0) : ℕ :=
  D.host.g 0 * D.host.g 1 * ∏ q ∈ (R.Q t).image (fun PP => Nat.card (kP PP)), q

structure FieldHyp (t : T0) : Prop where
  xi : ∀ x, ((R.xi t x : Circle) : ℂ) ∈ D.what₂.embLL.fieldRange
  eta : ∀ P, Formalism.L2.Host.etaAlg D.host R.C.eta P ∈ D.what₂.embLL.fieldRange
  roots : ∀ PP ∈ R.Q t, ∃ z : D.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP))
  comp : ContainsRayField (embK D) (tupLevel R t)

def RatAt (i : Fin D.R.m) (ph : ℂ) (t : T0) : Prop :=
  ∀ x₀ : A.fam.amb.FL i t, ∃ y : Fin (R.nW i) → D.what₂.LL,
    (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y) = ph • R.thF i t (R.jV i t x₀) ∧
    ph • R.thG i t (R.jV i t x₀) =
      (R.FW i).j (sg0 D A) ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y)

theorem proj_clause (i : Fin D.R.m) (ph : ℂ) (t : T0) (hG : R.thP_thG)
    (hinj : Function.Injective (R.HW i (sg0 D A)).e)
    (hρ : RhoIs (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i _).e (actW R i _) (R.FW i).chi (R.FW i).ρ)
    (x : (R.HV i t).H) (y : Fin (R.nW i) → D.what₂.LL)
    (h : (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y) = ph • R.thF i t x) :
    ph • R.thG i t x = (R.FW i).j (sg0 D A) ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y) := by
  apply hinj
  rw [map_smul, hG i t x, ← map_smul, ← h, Arith.FormsL.eOp, LinearMap.sum_apply, map_sum, map_sum]
  have key : ∀ g : G, (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A)
      ((((idemOf A.X).coeff g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (R.FW i).ρ g) y)) =
      RealDat.eC (A := A) (sg0 D A) g • actW R i _ g ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y)) := by
    intro g
    rw [LinearMap.smul_apply, map_smulₛₗ, map_smul, hρ g y, smul_smul, ← map_mul, mul_assoc, Units.inv_mul, mul_one]
    rfl
  rw [Finset.sum_congr rfl fun g _ => key g]
  generalize (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) y) = Φ
  ext v h
  simp [RealDat.eWf, gaL, actW, postOn, LinearMap.sum_apply, Finset.sum_apply]
  first | rfl | exact Finset.sum_congr rfl fun _ _ => rfl

end Tuple

def RatThetaAt (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m) : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) → RhoTie R → OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → QGuard R →
    ∀ t : T0, FieldHyp R t → RatAt R i (ph i) t

def RatTheta : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m),
    RatThetaAt T R F κ v₀ O ph i

end GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta
end
end

