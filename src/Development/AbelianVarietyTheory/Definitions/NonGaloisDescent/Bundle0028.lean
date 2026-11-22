import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain

namespace GlobalTheory.CoefDuty

variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb}

def Built (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) : Prop :=
  ∃ Sp : NdSpec A.pl M C big L.X L.T, Nonempty (AutSpec A M tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam)

def BuiltEx (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) : Prop :=
  ∀ big, ∃ L, Built A M C tup big L

def EvO (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (P : D7 → Prop) : Prop :=
  ∃ big, ∀ L, Built A M C tup big L → P (withLoc L)

def ExtOf (L₀ L₁ : LocAll (lay0 D)) (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc) : Prop :=
  L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ ∧
    Nonempty (LocExt L₀.lay.fixZ.nd L₁.lay.fixZ.nd L₀.lay.fixZ.naut L₁.lay.fixZ.naut i₀ i₁)

end GlobalTheory.CoefDuty

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JointApproxOfMem
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong TensorProduct

namespace GlobalTheory.CongPhi

def phiSum {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (x : WD h) (σ : Weil h) (n : ℕ) : ℂ :=
  ((x.charPol σ).roots.map (· ^ n)).sum

def JointApprox {k Γ : Type} [NormedField k] [Group Γ] {a : ℕ} (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k))
    (S : ℕ → k) (s : (Γ →* GL (Fin a) k) → ℕ → k) : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ (t : Finset (Γ →* GL (Fin a) k)) (c : (Γ →* GL (Fin a) k) → k),
    (t : Set (Γ →* GL (Fin a) k)) ⊆ C ∧ (∀ g : Γ, ‖trc r g - ∑ ρ ∈ t, c ρ * trc ρ g‖ ≤ ε) ∧
      ∀ j ≤ n, ‖S j - ∑ ρ ∈ t, c ρ * s ρ j‖ ≤ ε

section Local

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

def IsPhiD (T : ↥(Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ) ≃ₗ[LL] ↥(Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ)) : Prop :=
  ∀ x, ((T x : ↥(Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ)) : V ⊗[Qp] B) = Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := V) x

open Classical in

def phiTr (m : ℤ) : LL :=
  if h : ∃ T, IsPhiD PD ρ T then
    LinearMap.trace LL _ ((h.choose ^ ((Module.finrank Qp K₀ : ℤ) * m) : ↥(Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ) ≃ₗ[LL] ↥(Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ)) :
      ↥(Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ) →ₗ[LL] ↥(Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ))
  else 0

open Classical in

def phiLetter (m : ℤ) : LL := phiTr PD ρ m / (Module.finrank Qp K₀ : LL)

end Local

section Om

variable {l : ℕ} [Fact l.Prime]

def matRep {K : FinExt l} (L : FinExt l) {a : ℕ} (r' : ↥(GK K) →* GL (Fin a) ↥L.1) :
    Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥L.1 ≃ₐ[↥L.1] _) : _ →* _).comp ((Units.coeHom _).comp r')

def IsMod {K : FinExt l} {a : ℕ} (ρ : ↥(GK K) →* GL (Fin a) (Om l)) (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) :
    Prop :=
  ∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ g).val i j

def CrysLe (P : LocPrime l) (K : FinExt l) {a : ℕ} (ρ : ↥(GK K) →* GL (Fin a) (Om l)) (N : ℕ) : Prop :=
  ∃ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1), IsMod ρ L r' ∧ Formalism.WeaklyAdmissibleFiltrations.IsCrys (P.PD K) (matRep L r') ∧
    Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD K) (matRep L r') ≤ Formalism.WeaklyAdmissibleFiltrations.FilV (P.PD K) (LL := ↥L.1) (V := Fin a → ↥L.1) (-(N : ℤ)) ∧
    Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD K) (matRep L r') ⊓ Formalism.WeaklyAdmissibleFiltrations.FilV (P.PD K) (LL := ↥L.1) (V := Fin a → ↥L.1) ((N : ℤ) + 1) = ⊥

open Classical in

def phiOm (P : LocPrime l) (K : FinExt l) {a : ℕ} (ρ : ↥(GK K) →* GL (Fin a) (Om l)) (m : ℤ) : Om l :=
  if h : ∃ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1), IsMod ρ L r' then
    ((phiLetter (P.PD K) (matRep h.choose h.choose_spec.choose) m : ↥h.choose.1) : Om l)
  else 0

end Om

def ClosedPhi : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (hA : IsPlaceOver A w),
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
      (hBw : Pst.Induces Bw),
    ∀ (J : (E →+* Qbar l) → Multiset ℤ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → IsSSRep r →
    ∀ C : Set (G E Ω →* GL (Fin a) (Qbar l)),
      (∀ ρ ∈ C, Continuous ρ ∧ IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ (J τ)) →
    ∀ (σ : Weil hA) (S : ℕ → Qbar l),
      JointApprox r C S (fun ρ n => ι.symm (phiSum (wdAt P ι Bw hA hBw (ρ.comp (Dec (F := E) A).subtype)) σ n)) →
      ∀ n : ℕ, phiSum (wdAt P ι Bw hA hBw (r.comp (Dec (F := E) A).subtype)) σ n = ι (S n)

end GlobalTheory.CongPhi

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
section
noncomputable section

namespace GlobalTheory.TwInputs

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

def EigTrue (D : D7) (cf : CharFrame D) (Rw : RowSide D) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : Prop :=
  ∀ (j : Fin D.R.m) σ, D.what₂.isot (j.1 + 1) σ ≠ ⊥ → D.nd.goodRow σ → ∀ P, IsSplitPl D.host P → P ∉ Sb →
    D.naut.unr (Rw.locR σ P) ∧ ∀ k, 1 ≤ k → k ≤ D.R.r → D.what₂.embLL (eig (j.1 + 1) σ k P : D.what₂.LL) =
      ((normV P : ℕ) : ℂ) ^ (k * (D.R.r - k) / 2) * ((D.naut.frobEig (Rw.locR σ P)).map fun a =>
        a⁻¹ * (((cf.mu0 j).val P : ℂˣ) : ℂ)⁻¹ * (((normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹).esymm k

def EigOcc (D : D7) (S : RatDat D.ntw) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → ∃ x ∈ goodL D S θ j, x ≠ 0 ∧
    ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ Sb → hL j k P x = ((eig j σ k P : ↥D.LL0) : D.what₂.LL) • x

def RowParam (D : D7) (Rw : RowSide D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → ∃ π, GlobalTheory.EigTie.IsRowPar Rw σ π

def NoFormsOff (D : D7) : Prop := ∀ i j, j ∉ Finset.Icc 1 D.R.m → ∀ b, Subsingleton (D.nexp.Fm i j b)

def MeetsAll (D : D7) : Prop := ∀ i j b (W : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)), W ≠ ⊥ →
  GStable D.nexp i j b W → (∀ x ∈ W, eG D.nexp i j b x = x) → W ⊓ Fm0 D.nexp i j b ≠ ⊥

def CommAll (D : D7) : Prop := ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ g x,
  D.nexp.hkF i j b k P (D.nexp.actG i j b g x) = D.nexp.actG i j b g (D.nexp.hkF i j b k P x)

def FullAll (D : D7) : Prop := ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b,
  Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i j b : Set (D.nexp.Fm i j b)) = ⊤

end GlobalTheory.TwInputs

end
end

