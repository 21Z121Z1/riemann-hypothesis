import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.Bundle0001

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CharacterPartsGaps
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

namespace GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps

def Gap (D : D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (n : ℕ), n + 1 < D.R.r →
    (D.R.r : ℚ) ≤ Formalism.L2.NTheta.lamAt (D.hc τ) n - Formalism.L2.NTheta.lamAt (D.hc τ) (n + 1)

def finS (D : D7) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  primesOf ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)

abbrev EigSys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def EEc (P : LevelP R.Pg D.R.r ℂ) (c : EigSys D) : Submodule ℂ (MMap (R.MY 0)) :=
  partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) (finS D) c ⊓ R.EEat P

def Wc' (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) (c : EigSys D) : Submodule ℂ (MMap (R.MW i (sg0 D A))) :=
  partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)) (finS D) c ⊓
    R.Wat i (sg0 D A) P

def MatchAt (P P' : LevelP R.Pg D.R.r ℂ) : Prop :=
  ∀ (i : Fin D.R.m) (c : EigSys D),
    FiniteDimensional ℂ (EEc R P c) ∧ FiniteDimensional ℂ (Wc' R i P' c) ∧
      Module.finrank ℂ (EEc R P c) = Module.finrank ℂ (Wc' R i P' c)

def MatchAll : Prop :=
  MatchAt R R.triv R.triv ∧ ∀ b : Bool, MatchAt R (R.levR F b) (R.levL F b (sg0 D A))

end

def PartsMatch : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    Gap D → GlobalTheory.GLq.ESerTie D → R.toLevCh.Is A.μ0 → R.IsGrp F → IsInfFam R.θ → MatchAll R F

def PartsMatchChar : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    Gap D → GlobalTheory.GLq.ESerTie D → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsChain → R.IsThP → R.IsScal F →
      MatchAll R F

theorem PartsMatch.char (h : PartsMatch) : PartsMatchChar :=
  fun D G _ _ Pl0 T A Ks _ _ _ R F hg he hl hG _ hM _ _ _ => h D G Pl0 T A Ks R F hg he hl hG hM.inf

theorem mem_finS (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    v ∈ finS D ↔ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  unfold finS
  rw [mem_primesOf]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  exact_mod_cast mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

end GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CommutingLevelOperators
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsFinIntertwiner (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W)
    (φ : W →ₗ[ℂ] (GA D V → ℂ)) : Prop :=
  ∀ (k : GfC V) (w : W), φ (σ k w) = fun g => φ w (g * (k : GA D V))

def isoFun (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) :
    Submodule ℂ (GA D V → ℂ) :=
  ⨆ (φ : W →ₗ[ℂ] (GA D V → ℂ)) (_ : IsFinIntertwiner V σ φ), LinearMap.range φ

def IsoRep {H : Type} [Group H] {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ H W) (σ' : Representation ℂ H W') : Prop :=
  ∃ e : W ≃ₗ[ℂ] W', ∀ k w, e (σ k w) = σ' k (e w)

section Chain

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

abbrev Sys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

open Classical in

def typePl : Finset (HeightOneSpectrum (𝓞 D.host.F)) := R.Pg.image fun PP => PP.under (𝓞 D.host.F)

def rowLev : Option Bool → LevelP R.Pg D.R.r ℂ
  | none => R.triv
  | some b => R.levR F b

def heckePart (P : LevelP R.Pg D.R.r ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : Sys D) :
    Submodule ℂ (MMap (R.MY 0)) :=
  partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) Sb c ⊓ R.EEat P

def Differ (P : LevelP R.Pg D.R.r ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c c' : Sys D) : Prop :=
  ∃ w d Rp, Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) Sb w d Rp ∧
    c w (dualLab d) ≠ c' w (dualLab d)

def isoPart (P : LevelP R.Pg D.R.r ℂ) {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GfC (Yc D 0)) W) : Set (MMap (R.MY 0)) :=
  {u | u ∈ R.EEat P ∧ ∀ v, u v ∈ isoFun (Yc D 0) σ}

variable (t : T)

def eY (j : ℕ) : (GA D (Yc D j) → ℂ) →ₗ[ℂ] (GA D (Yc D j) → ℂ) :=
  gaL (Yc D j) (R.βY j) (R.datYt t j R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL)

def eX : (GA D D.sp.X' → ℂ) →ₗ[ℂ] (GA D D.sp.X' → ℂ) :=
  gaL D.sp.X' R.βX (R.datXt t) R.eG (RealDat.eC (A := A) D.what₂.embLL)

def toX : (R.HX t).H →ₗ[ℂ] (SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) := R.cX.toMap R.prX ∘ₗ (R.HX t).e

def lastStep : (R.HX t).H →ₗ[ℂ] R.CC t (D.R.m - 1) := R.ioX t ∘ₗ (R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict

def InProjectedFormSpace (P : LevelP R.Pg D.R.r ℂ) (f : (R.HX t).H) : Prop :=
  (∀ v, HasType D.sp.X' R.βX (withP (R.datXt t) P) (toX R t f v)) ∧ eX R t ∘ₗ toX R t f = toX R t f

def dn (f : (R.HX t).H) : MMap (R.MY 0) := PiTensorProduct.lift.symm (R.thDn t f)

def UpStep (k : ℕ) (u : MMap (R.MY k)) (x : MMap (R.MY (k + 1))) : Prop :=
  PiTensorProduct.lift x ∈ R.CC t (k + 1) ∧ ∀ y : R.CC t (k + 1), ∃ a : ℂ,
    IsMultIP (R.MY k) (R.νY t k) (R.fdY t k) u (PiTensorProduct.lift.symm (R.ioY t k y).1) a ∧
    IsMultIP (R.MY (k + 1)) (R.νY t (k + 1)) (R.fdY t (k + 1)) x (PiTensorProduct.lift.symm y.1) a

def UpIter (u : MMap (R.MY 0)) (j : ℕ) : MMap (R.MY j) → Prop :=
  Nat.rec (motive := fun j => MMap (R.MY j) → Prop) (fun x => x = u)
    (fun j ih x => ∃ y, ih y ∧ UpStep R t j y x) j

def UpTop (u : MMap (R.MY 0)) (x : (R.HX t).H) : Prop :=
  ∃ y, UpIter R t u (D.R.m - 1) y ∧ ∀ f : (R.HX t).H,
    IsMultIP (R.MY (D.R.m - 1)) (R.νY t (D.R.m - 1)) (R.fdY t (D.R.m - 1)) y
      (PiTensorProduct.lift.symm (lastStep R t f).1) (inner ℂ x f)

def LiftsOrth (u u' : MMap (R.MY 0)) : Prop :=
  (∀ j, 1 ≤ j → j < D.R.m → ∀ x x', UpIter R t u j x → UpIter R t u' j x' →
    IsMultIP (R.MY j) (R.νY t j) (R.fdY t j) x x' 0) ∧
  ∀ x x', UpTop R t u x → UpTop R t u' x' → inner ℂ x x' = (0 : ℂ)

variable (P : LevelP R.Pg D.R.r ℂ)

def UpExists : Prop :=
  ∀ u ∈ R.EEat P, (∀ j, j < D.R.m → ∃! x, UpIter R t u j x) ∧ ∃! x, UpTop R t u x

def UpIsAdjoint : Prop := ∀ u : R.HE.H, UpTop R t (R.HE.e u) (LinearMap.adjoint (R.Th t) u)

def StepsCommute : Prop :=
  (∀ k, k + 1 < D.R.m → ∀ y : R.CC t (k + 1), ∃ y' : R.CC t (k + 1), y'.1 = eY R t (k + 1) ∘ₗ y.1 ∧
    (R.ioY t k y').1 = eY R t k ∘ₗ (R.ioY t k y).1) ∧
  ∀ f : (R.HX t).H, ∃ f' : (R.HX t).H, toX R t f' = eX R t ∘ₗ toX R t f ∧
    (lastStep R t f').1 = eY R t (D.R.m - 1) ∘ₗ (lastStep R t f).1

def UpLiftInProjectedFormSpace : Prop := ∀ u ∈ R.EEat P, ∀ x, UpTop R t u x → InProjectedFormSpace R t P x

def DnIntoEE : Prop := ∀ f, InProjectedFormSpace R t P f → dn R t f ∈ R.EEat P

def DnUpMapsEE : Prop := ∀ u ∈ R.EEat P, ∀ x, UpTop R t u x → dn R t x ∈ R.EEat P

def HeckeOrth : Prop :=
  ∀ Sb, typePl R ⊆ Sb → ∀ c c', Differ R P Sb c c' →
    ∀ u ∈ heckePart R P Sb c, ∀ u' ∈ heckePart R P Sb c', LiftsOrth R t u u'

def HeckeKept : Prop :=
  ∀ Sb, typePl R ⊆ Sb → ∀ c, ∀ u ∈ heckePart R P Sb c, ∀ x, UpTop R t u x → dn R t x ∈ heckePart R P Sb c

def IsoOrth : Prop :=
  ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GfC (Yc D 0)) W) (σ' : Representation ℂ (GfC (Yc D 0)) W'),
    σ.IsIrreducible → σ'.IsIrreducible → ¬ IsoRep σ σ' →
    ∀ u ∈ isoPart R P σ, ∀ u' ∈ isoPart R P σ', LiftsOrth R t u u'

def IsoKept : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC (Yc D 0)) W), σ.IsIrreducible →
    ∀ u ∈ isoPart R P σ, ∀ x, UpTop R t u x → dn R t x ∈ isoPart R P σ

structure Common : Prop where
  upExists : UpExists R t P
  upIsAdjoint : UpIsAdjoint R t
  stepsCommute : StepsCommute R t
  upIntoProjectedForms : UpLiftInProjectedFormSpace R t P
  dnIntoEE : DnIntoEE R t P
  dnUpMapsEE : DnUpMapsEE R t P

def GoodTypes : Prop :=
  ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k ∧
      (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
      ∀ (v : D.nd.PlG k) (j : Fin D.R.m) (PP : Pl D.host.E), R.C.P.Div k PP →
        ∀ (a : ℕ) (u : (kP PP)ˣ), (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = L.gen 1 → (u : kP PP) = (a : kP PP) →
          L.teich (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
              ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) =
            ((R.chi ((j : ℕ) + 1) PP u : ℂˣ) : ℂ) ∨
          L.teich (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
              ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) =
            (((R.chi ((j : ℕ) + 1) PP u)⁻¹ : ℂˣ) : ℂ)

structure HidaSetting : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP
  scal : R.IsScal F
  params : ∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)
  good : GoodTypes R

def OneFinitePart : Prop :=
  HidaSetting R F → ∀ (t : T) (b : Option Bool),
    Common R t (rowLev R F b) ∧ HeckeOrth R t (rowLev R F b) ∧ HeckeKept R t (rowLev R F b)

def OneFinitePartIsotypic : Prop :=
  HidaSetting R F → ∀ (t : T) (b : Option Bool),
    Common R t (rowLev R F b) ∧ IsoOrth R t (rowLev R F b) ∧ IsoKept R t (rowLev R F b)

example (P : LevelP R.Pg D.R.r ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : Sys D) : ¬ Differ R P Sb c c :=
  fun ⟨_, _, _, _, h⟩ => h rfl

end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DefiniteIndexDimensionCounts
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Objects

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def levW (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) : Subgroup (GL (Fin (Wc D i).rank) (EAf D)) :=
  lev D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i P)

def levK (i : Fin D.R.m) : Subgroup (GL (Fin (Wc D i).rank) (EAf D)) := levW R i R.triv

abbrev Cls (i : Fin D.R.m) : Type := Cl D.sp.cm (Wc D i).gram (levK R i)

def clsOf (i : Fin D.R.m) (x : UA D.sp.cm (Wc D i).gram) : Cls R i := Quotient.mk'' x

def levB (b : Bool) : LevelP R.Pg D.R.r ℂ := R.levL F b (sg0 D A)

def dimRho (i : Fin D.R.m) : ℕ := ∏ ρ, Module.finrank ℂ ((R.MW i (sg0 D A)).H ρ)

def dK (i : Fin D.R.m) : ℕ := Module.finrank ℂ (R.Wall i (sg0 D A))

def allAt (b : Bool) (i : Fin D.R.m) : Submodule ℂ (MMap (R.MW i (sg0 D A))) :=
  Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (levB R F b))) (levChi _ (R.βW i) (R.datWp i (levB R F b)))

def d0 (b : Bool) (i : Fin D.R.m) : ℕ := Module.finrank ℂ (allAt R F b i)

def dGood (b : Bool) (i : Fin D.R.m) : ℕ := Module.finrank ℂ (R.Wat i (sg0 D A) (levB R F b))

def repB (b : Bool) (i : Fin D.R.m) : Representation ℂ (F.lvl b).P (R.HW i (sg0 D A)).H :=
  (R.gW i (sg0 D A)).comp (F.lvl b).P.subtype

def PrincipalCount (i : Fin D.R.m) : Prop :=
  Finite (Cls R i) ∧ Nonempty (Cls R i) ∧ (∀ c : Cls R i, Gam c = ⊥) ∧
    (∀ ρ, FiniteDimensional ℂ ((R.MW i (sg0 D A)).H ρ)) ∧ 1 ≤ dimRho R i ∧
    FiniteDimensional ℂ (R.Wall i (sg0 D A)) ∧ dK R i = Nat.card (Cls R i) * dimRho R i ∧ 1 ≤ dK R i

def ActsFreely (b : Bool) (i : Fin D.R.m) : Prop :=
  (∀ u ∈ (levB R F b).H, ∃ κ ∈ levW R i (levB R F b), rTup (R.βW i) (R.datWp i (levB R F b)) κ = u) ∧
    ∀ x κ : UA D.sp.cm (Wc D i).gram, (κ : GL (Fin (Wc D i).rank) (EAf D)) ∈ levW R i (levB R F b) →
      clsOf R i (x * κ) = clsOf R i x → rTup (R.βW i) (R.datWp i (levB R F b)) (κ : GL (Fin (Wc D i).rank) (EAf D)) = 1

def FreeCount (b : Bool) (i : Fin D.R.m) : Prop :=
  (∃ N : ℕ, Nat.card (F.lvl b).P * N = dK R i ∧
      Nonempty ((repB R F b i).asModule ≃ₗ[MonoidAlgebra ℂ (F.lvl b).P] (Fin N → MonoidAlgebra ℂ (F.lvl b).P))) ∧
    Nat.card (F.lvl b).P * d0 R F b i = dK R i ∧ 1 ≤ d0 R F b i

def GoodShare (δ : ℝ) (b : Bool) (i : Fin D.R.m) : Prop :=
  (1 - δ) * (d0 R F b i : ℝ) ≤ (dGood R F b i : ℝ) ∧ 0 < (1 - δ) * (d0 R F b i : ℝ)

structure HidaSetting : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP
  scal : R.IsScal F

theorem GoodShare.ne_bot {δ : ℝ} {b : Bool} {i : Fin D.R.m} (h : GoodShare R F δ b i) :
    R.Wat i (sg0 D A) (levB R F b) ≠ ⊥ := by
  intro h0
  have h1 : (0 : ℝ) < dGood R F b i := lt_of_lt_of_le h.2 h.1
  unfold dGood at h1
  rw [h0, finrank_bot] at h1
  simp at h1

end Objects

theorem exists_last (D : D7) : ∃ i : Fin D.R.m, (i : ℕ) + 1 = D.R.m :=
  ⟨⟨D.R.m - 1, by have := D.R.two_le_m; omega⟩, by have := D.R.two_le_m; show D.R.m - 1 + 1 = _; omega⟩

def DefiniteFree : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), HidaSetting R F → ∀ i : Fin D.R.m, (i : ℕ) + 1 = D.R.m →
    PrincipalCount R i ∧ ∀ b : Bool, ActsFreely R F b i ∧ FreeCount R F b i

def DefiniteGoodShare : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x₀ ≤ L.sc.x →
    Formalism.MainNotions.SizesAt L → GlobalTheory.GLq.ESerTie D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
      (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
      (R : RealDat D A Ks) (F : Face D A), HidaSetting R F → ∀ i : Fin D.R.m, (i : ℕ) + 1 = D.R.m →
      ∀ b : Bool, GoodShare R F (Real.exp (-(L.sc.x ^ (L.sc.ez / 7)))) b i

def GoodVectorsDefinite : Prop := DefiniteFree ∧ DefiniteGoodShare

end GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DownUpLambdaOperators
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators

theorem typeIdeal_ne (D : D7) :
    Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)} ≠ 0 := by
  rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
  exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

def typePlaces (D : D7) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (Ideal.finite_factors (typeIdeal_ne D)).toFinset

theorem mem_typePlaces (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    v ∈ typePlaces D ↔ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  rw [typePlaces, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]

abbrev Eig (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

def LowGaps (D : D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (j : ℕ) (h : j + 1 < D.R.m),
    4 * (D.R.N D.R.m : ℚ) ^ 3 + 2 * (D.R.t : ℚ) + 6 ≤ (D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def InFirstRow {Pg : Finset (Pl D.host.E)} {r : ℕ} (PP : Pg) (g : G0 Pg r) : Prop :=
  (∀ PP' : Pg, PP' ≠ PP → g PP' = 1) ∧
    ∀ a b : Fin r, 0 < (a : ℕ) → (g PP : Matrix (Fin r) (Fin r) (kP PP.1)) a b = (1 : Matrix (Fin r) (Fin r) (kP PP.1)) a b

open Classical in

def GoodTypes (R : RealDat D A Ks) : Prop :=
  ∀ χ ∈ A.X, IsAbsIrrChar χ ∧ ∀ (PP : R.Pg) (j : Fin D.R.m) (s : ℤˣ),
    ∑ g ∈ Finset.univ.filter (fun g : G => InFirstRow PP (R.eG g)),
      (((R.chi ((j : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP))) ^ (s : ℤ) : ℂˣ) : ℂ) * D.what₂.embLL (χ g) = 0

def TwistOffDatum (R : RealDat D A Ks) : Prop :=
  ∀ t, ∀ PP ∈ R.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

def partE (R : RealDat D A Ks) (c : Eig D) : Submodule ℂ R.HE.H :=
  (partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) (typePlaces D) c ⊓
    R.EEat R.triv).comap R.HE.e

def partW (R : RealDat D A Ks) (i : Fin D.R.m) (c : Eig D) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv))
      (typePlaces D) c ⊓ R.Wat i (sg0 D A) R.triv).comap (R.HW i (sg0 D A)).e

def dnUp (R : RealDat D A Ks) (t : T) : R.HE.H →ₗ[ℂ] R.HE.H := R.Th t ∘ₗ LinearMap.adjoint (R.Th t)

def IsLam (R : RealDat D A Ks) (lam : T → ℕ → Eig D → ℝ) : Prop :=
  ∀ (i : Fin D.R.m) (t : T), Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (partW R i) (lam t ((i : ℕ) + 1))

def Concl (R : RealDat D A Ks) : Prop :=
  ∃ lam : T → ℕ → Eig D → ℝ, (∀ t j c, 0 < lam t j c) ∧ IsLam R lam ∧ Lift.ThmB D.R.m (dnUp R) (partE R) lam

def ThmBAt (R : RealDat D A Ks) (F : Face D A) : Prop :=
  LowGaps D → R.toLevCh.Is A.μ0 → TwistOffDatum R → GoodTypes R →
    R.IsGrp F → R.IsFam → R.IsModels → R.IsChain → R.IsThP → Concl R

theorem Concl.scalar_pos {R : RealDat D A Ks} (h : Concl R) (t : T) (c : Eig D) :
    ∃ l : ℝ, 0 < l ∧ ∀ x ∈ partE R c, dnUp R t x = (l : ℂ) • x := by
  obtain ⟨lam, hpos, -, κ, hκ, hK⟩ := h
  exact ⟨_, mul_pos hκ (Finset.prod_pos fun j _ => hpos t j c), hK t c⟩

theorem Concl.of_match {R : RealDat D A Ks} (h : Concl R) (hm : ∀ c, partE R c ≠ ⊥ → ∀ i, partW R i c ≠ ⊥) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ lam, IsLam R lam → Lift.IsKap D.R.m (dnUp R) (partE R) lam κ := by
  obtain ⟨lam, -, hl, κ, hκ, hK⟩ := h
  refine ⟨κ, hκ, fun lam' hl' t c x hx => ?_⟩
  by_cases h0 : partE R c = ⊥
  · rw [h0, Submodule.mem_bot] at hx
    rw [hx, map_zero, smul_zero]
  · rw [hK t c x hx]
    congr 3
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    have := Lift.IsLamP.unique (hl ⟨j - 1, by omega⟩ t) (hl' ⟨j - 1, by omega⟩ t) (hm c h0 _)
    rwa [show j - 1 + 1 = j by omega] at this

end

def ThmB : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ThmBAt R F

end GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VectorLevelCharacters
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.VectorLevelCharacters

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev levV (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Subgroup (GA D (Vc D i)) :=
  levG (Vc D i) (R.βV i) (R.toLevCh.datVt i t)

abbrev chV (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (κ : GA D (Vc D i)) : ℂ :=
  levChi (Vc D i) (R.βV i) (R.toLevCh.datVt i t) κ

abbrev levW (R : RealDat D A Ks) (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) :=
  levG (Wc D i) (R.βW i) (R.toLevCh.datWp i R.toLevCh.triv)

def VecLevelAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  VecLaw (R.ωP i t) (levV R i t) (fun κ => (chV R i t κ)⁻¹) (levW R i) (fun _ => 1) (R.vP i t)

def VecLevelOf (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 → R.thP_ωP → R.thP_vP → ∀ (i : Fin D.R.m) (t : T), VecLevelAt R i t

theorem principalLevelCharacter_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (R.toLevCh.datWp i R.toLevCh.triv) k = 1 := by
  have h : ∀ x, Formalism.L2.DIV.ext1 (R.toLevCh.datWp i R.toLevCh.triv).P.H (R.toLevCh.datWp i R.toLevCh.triv).P.chi x = 1 :=
    fun x => subgroupCharExtension_one_apply _ x
  unfold levChi Formalism.L2.DIV.levFn
  rw [h]
  simp [LevCh.datWp, datY]

end

def VecLevel (D : D7) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), VecLevelOf R

end GlobalTheory.IndefiniteRowSideFullHecke.VectorLevelCharacters

end
end

