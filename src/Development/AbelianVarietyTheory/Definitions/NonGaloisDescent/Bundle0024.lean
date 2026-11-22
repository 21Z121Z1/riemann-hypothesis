import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def segSum (rc : IrrGL (w.adicCompletion E) → WD h) (l : List (Segment (w.adicCompletion E))) : WD h :=
  sumList (l.map fun Δ => ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len))

structure LawsMin (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (w.adicCompletion E) → WD h) : Prop where

  bij : Function.Bijective rc

  dim : ∀ x, (rc x).lpDim = x.1

  one : ∀ χ hχ, rc (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)

  eps : ∀ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ → ψ ≠ 1 →
    ∀ (m : ℕ) (π : IrrRep (GL (Fin (m + 1)) (w.adicCompletion E))) (τ : IrrRep (GL (Fin m) (w.adicCompletion E))),
      IsCuspidal π.ρ → HasPairEps ψ π.ρ τ.ρ (e ψ ((rc (cls π)).lpChar (rc (cls τ))))

  cusp : ∀ x, x.IsCusp ↔ IsIrrWD (rc x)

  langlands : ∀ (l : List (Segment (w.adicCompletion E))) (x : IrrGL (w.adicCompletion E)),
    IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep → rc x = segSum rc l

structure LawsLit (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (w.adicCompletion E) → WD h) : Prop
    extends LawsMin a ha e rc where

  twist : ∀ x χ hχ, rc (x.tw χ hχ) = (rc x).lpChar (rc (.ofChar χ hχ))

  central : ∀ (x : IrrGL (w.adicCompletion E)) ω, HasCentralChar x.rep ω →
    ∀ σ, ((rc x).eig σ).prod = (ω (a σ) : ℂ)

  dual : ∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Nonempty (π'.ρ.Equiv (contra π.ρ)) →
    rc (cls π') = (rc (cls π)).lpDual

variable (h) in

def IsRecLit (rc : IrrGL (w.adicCompletion E) → WD h) : Prop :=
  ∃ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A),
    IsDeligneEps ε ∧ LawsLit a ha (ε E w h) rc

theorem Laws.toLit {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
    {rc : IrrGL (w.adicCompletion E) → WD h} (H : Laws a ha ε rc) : LawsLit a ha (ε E w h) rc :=
  { bij := H.bij, dim := H.dim, one := H.one, eps := H.eps, cusp := H.cusp, langlands := H.langlands,
    twist := H.twist, central := H.central, dual := H.dual }

theorem IsRec.toLit {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) : IsRecLit h rc :=
  let ⟨a, ha, ε, hε, H⟩ := H; ⟨a, ha, ε, hε, H.toLit⟩

section Transport

def RepRel {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k')
    (x : IrrGL k) (x' : IrrGL k') : Prop :=
  ∃ (n : ℕ) (π : IrrRep (GL (Fin n) k)) (π' : IrrRep (GL (Fin n) k')) (e : π.V ≃ₗ[ℂ] π'.V),
    x = cls π ∧ x' = cls π' ∧ ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)

variable {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

def WeilRel (φ : Ω ≃+* Ω') (σ : Weil h) (σ' : Weil h') : Prop :=
  ∀ z, φ ((σ : G E Ω) z) = (σ' : G E' Ω') (φ z)

def WDRel (φ : Ω ≃+* Ω') (y : WD h) (y' : WD h') : Prop :=
  ∃ (n : ℕ) (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ)), WD.mk b = y ∧ WD.mk b' = y' ∧
    b.N = b'.N ∧ ∀ (σ : Weil h) (σ' : Weil h'), WeilRel φ σ σ' → b.ρ σ = b'.ρ σ'

variable (A A' w w') in

structure PlaceIso (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E') : Prop where

  mem : ∀ z, φ z ∈ A' ↔ z ∈ A

  ext : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)

  cont : Continuous i

  loc : ∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)

end Transport

theorem PlaceIso.refl : PlaceIso A w A w (RingEquiv.refl Ω) (RingHom.id E) (RingEquiv.refl _) :=
  ⟨fun _ => Iff.rfl, fun _ => rfl, continuous_id, fun _ => rfl⟩

end GlobalTheory.LocLanglands

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DownLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev Sys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

def chiW (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : (AE D)ˣ →* Circle :=
  (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1

def chiV (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : (AE D)ˣ →* Circle :=
  (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2

def valW (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)) : ℂˣ :=
  GlobalTheory.LFun.val (F := D.host.F) (chiW R i t) w

def valV (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)) : ℂˣ :=
  GlobalTheory.LFun.val (F := D.host.F) (chiV R i t) w

def str (q : ℕ) (z : ℂ) (n : ℕ) : Multiset ℂ :=
  (Multiset.range n).map fun k : ℕ => z * (q : ℂ) ^ (((n : ℂ) - 1) / 2 - (k : ℂ))

def IsEigV (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i t).H) (s : Sys D) (y : (R.HV i t).H) : Prop :=
  ∀ P d, GlobalTheory.Hk3.Good R t P → GlobalTheory.Hk3.IsLab (Vc D i) P d → h P (Finsupp.single d 1) y = s P d • y

def HasString (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (s : Sys D) : Prop :=
  ∃ B : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B ∧
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good R t w →
    ∃ B' : Multiset ℂ, (B w).map (fun a : ℂˣ => (a : ℂ)) =
        B' + str (Ideal.absNorm w.asIdeal) (valV R i t w : ℂ) D.R.t ∧
      ∀ a ∈ B', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)

def downInt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) : ℂ :=
  ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g f * l (R.extV i t y h) ∂(R.νV i t)

def SomeLift (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) : Prop :=
  ∃ f l g, IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ downInt R i t y f l g ≠ 0

def NonVan (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s, HasString R i t s → ∀ y, IsEigV R i t h s y → y ≠ 0 → SomeLift R i t y

def GoodVt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) : Prop :=
  ∀ l : (R.cV i).W →ₗ[ℂ] ℂ,
    gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (RealDat.eC (A := A) (sg0 D A)) (fun h => l (R.extV i t y h)) =
      fun h => l (R.extV i t y h)

open Classical in

def mirC (R : RealDat D A Ks) (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool) (ε : ℤ) (g : G) : ℂ :=
  if (∀ PP', PP' ≠ PP → R.eG g PP' = 1) ∧
      (if tr then ∀ x, ∃ c : kP PP.1, (R.eG g PP : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).mulVec x - x = c • a
        else ∀ x, a ⬝ᵥ x = 0 → (R.eG g PP : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).mulVec x = x) then
    ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) ^ ε : ℂˣ) : ℂ)
  else 0

def NoChi (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) : Prop :=
  ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), ε = 1 ∨ ε = -1 → ∀ l : (R.cV i).W →ₗ[ℂ] ℂ,
    gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (mirC R i PP a tr ε) (fun h => l (R.extV i t y h)) = 0

def FinLike (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ c : WO (Vc D i) (Wc D i) →₀ ℂ, (∀ u ∈ c.support, u.map (infPart D) = 0) →
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u (R.vP i t)) = 0 →
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u f) = 0

def GenInf (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ y, R.thF i t y = 0 → ∀ f, FinLike R i t f → ∀ l g, downInt R i t y f l g = 0

def GenFin (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ y, NoChi R i t y → (∀ f, FinLike R i t f → ∀ l g, downInt R i t y f l g = 0) → ¬ SomeLift R i t y

def GoodNoChi (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop := ∀ y, GoodVt R i t y → NoChi R i t y

def GoodMem (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ y, GoodVt R i t y → (R.HW i (sg0 D A)).e (R.thG i t y) = R.thF i t y

def TypeNZ (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s, HasString R i t s → ∀ y, IsEigV R i t h s y → GoodVt R i t y →
    R.thG i t y = 0 → y = 0

def partW (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (c : Sys D) : Submodule ℂ (MMap (R.MW i (sg0 D A))) :=
  partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv))
    (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c

def DownEig (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s, ∃ c, ∀ y, IsEigV R i t h s y → R.thF i t y ∈ partW R i t c

def UnrCorr (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (ok : Pl D.host.E → Prop) : Prop :=
  ∀ h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s c y, IsEigV R i t h s y → R.thF i t y ≠ 0 → R.thF i t y ∈ partW R i t c →
    ∀ B B' : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B →
      GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B' → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good R t w → ok w →
        (B w).map (fun a : ℂˣ => (a : ℂ)) =
          (B' w).map (fun a : ℂˣ => ((a * valV R i t w * (valW R i t w)⁻¹ : ℂˣ) : ℂ)) +
            str (Ideal.absNorm w.asIdeal) (valV R i t w : ℂ) D.R.t

def ParamsEx (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  (∀ h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s y, IsEigV R i t h s y → y ≠ 0 →
    ∃ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B) ∧
  ∀ c, partW R i t c ≠ ⊥ → ∃ B', GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B' ∧
    ∀ w, GlobalTheory.Hk3.Good R t w → ∀ a ∈ B' w, ‖(a : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)

def Saturated (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s, HasString R i t s → ∃ c, ∀ y, IsEigV R i t h s y → GoodVt R i t y →
    ∃ x : (R.HW i (sg0 D A)).H, (R.HW i (sg0 D A)).e x ∈ partW R i t c ⊓ R.Wat i (sg0 D A) R.triv ∧
      LinearMap.adjoint (R.thG i t) x = y

end GlobalTheory.DownLift

end
end

