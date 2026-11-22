import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open Classical

namespace GlobalTheory.HubX

def epJ (D : D7) : Bool := if h : AdmissibleParameterJ.ConclusionJa D then Exists.choose h else true

theorem epJ_eq {D : D7} (h : AdmissibleParameterJ.ConclusionJa D) : epJ D = Exists.choose h := dif_pos h

def dcOf (D : D7) (i : D.nd.Loc) : TruncatedSeriesCountingIdentities.Decl D i :=
  if h : GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) ∧ ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc (epJ D) then
    Exists.choose h.2 else KillingConditions.allRows i

variable {D : D7}

def cBof (L : SizeData₂ D) (i : D.nd.Loc) : ℕ :=
  GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV)

def hOf (L : SizeData₂ D) : ℕ := ⌊2 * L.sc.b⌋₊ + 1

def c0of (L : SizeData₂ D) (i : D.nd.Loc) (_u : HeightOneSpectrum (𝓞 D.host.E)) : ℕ :=
  5 + Nat.log (D.nd.l i) (2 * hOf L) + (4 * D.R.n * D.R.nV) * (4 + 2 * Nat.log (D.nd.l i) (2 * hOf L))

def ourX (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (r : FamilyRepresentationConstants.RFam D) (ρ : FamilyRepresentationConstants.RhoFam D)
    (e' : D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℕ) (exc : Finset ℕ) (I : TwIn D) : KillingConditions.HubData D :=
  KillingConditions.canon L HW R r ρ (dcOf D) e' (cBof L) (c0of L) exc ⌊L.etaSz⌋₊ I

structure Canon (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D) : Prop where
  fam : GlobalTheory.PtCore.PtFam D X.r X.ρ
  data : KillingConditions.DataAD L HW X R
  dc : ∀ i, ¬ TwistedPlaces.InertK D (D.nd.l i) → X.dc i = dcOf D i
  cB : X.cB = cBof L
  c0 : X.c0 = c0of L
  eta : X.eta = ⌊L.etaSz⌋₊

theorem canon_ourX (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (r : FamilyRepresentationConstants.RFam D) (ρ : FamilyRepresentationConstants.RhoFam D)
    (e' : D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℕ) (exc : Finset ℕ) (I : TwIn D)
    (h : GlobalTheory.PtCore.PtFam D r ρ) : Canon L HW R (ourX L HW R r ρ e' exc I) := by
  have hs : ∀ l, TwistedPlaces.SplitK D l → ¬ TwistedPlaces.InertK D l := by
    intro l h1 h2
    unfold TwistedPlaces.SplitK at h1
    unfold TwistedPlaces.InertK at h2
    rw [h1] at h2
    rcases h2 with h2 | h2 <;> cases h2
  refine ⟨h, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, rfl, rfl, rfl⟩
  · intro i hi; simp only [ourX, KillingConditions.canon, if_pos hi]; rfl
  · intro i _ hb; simp only [ourX, KillingConditions.canon, if_pos hb]
  · intro i _ hb; simp only [ourX, KillingConditions.canon, if_neg hb]
  · intro i hi π lam; simp only [ourX, KillingConditions.canon, if_pos hi]
  · intro i hi π; simp only [ourX, KillingConditions.canon, if_pos hi]
  · intro i _; rfl
  · intro i hi π lam; simp only [ourX, KillingConditions.canon, if_neg (hs _ hi)]
  · intro i hi π; simp only [ourX, KillingConditions.canon, if_neg (hs _ hi)]
  · intro i lam; exact Iff.rfl
  · intro i hi; simp only [ourX, KillingConditions.canon, if_neg hi]

def CondCB (L : SizeData₂ D) (X : KillingConditions.HubData D) (c : ℝ) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) →
    (X.cB i : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L

section H0

variable (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (l : ℕ) [Fact l.Prime]
  (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)

def invariantsCountConstant (M0 h0 : ℕ) (T : LocLat (LocalSituation.sit LT HW l (AI l) K s LL h).G (LocalSituation.sit LT HW l (AI l) K s LL h).Qp
    (LocalSituation.sit LT HW l (AI l) K s LL h).LL (LocalSituation.sit LT HW l (AI l) K s LL h).O) : ℕ :=
  LocalSituation.cLL l (LocalSituation.mN l s (M0 + h0)) (padicValNat l ((LocalSituation.sit LT HW l (AI l) K s LL h).degKj (LocalSituation.mN l s (M0 + h0))) -
    padicValNat l (LocalSituation.sit LT HW l (AI l) K s LL h).degK) (LocalSituation.Jset (LocalSituation.sit LT HW l (AI l) K s LL h) T) 0 1

end H0

def wLat (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i))
    (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))) g v) :
    LocLat ↥(GK (D.nbr i u hu).Kw) ℚ_[D.nd.l i] (Br.LLw (D.nbr i u hu)) (Br.Ow (D.nbr i u hu)) :=
  { V := Fin D.R.r → Br.LLw (D.nbr i u hu)
    ρ := matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u)))
    cont := hc
    L := Br.lat (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u)) }

def JointCond_H0Wall (D : D7) (HW : HWOf D.loc) (_F : FonOf D.loc D.locA HW) (X : Formalism.MainNotions.N.KillingConditions.HubData D) (M0 h0 : ℕ) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → Formalism.MainNotions.TwistedPlaces.SplitK D (D.nd.l i) →
    ∀ u ∈ (X.dc i).col, ∀ π ∈ D.nd.Zgood i, ∃ (hu : u ∈ placesOver D.host.E (D.nd.l i)) (s : ℕ)
      (hs : Good (D.nbr i u hu).Kw s (D.nbr i u hu).LL)
      (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i (X.ρ i) π).comp (decS D.nd u))) g v),
      IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i u hu).Kw) (wLat D i (X.ρ i) π u hu hc).ρ ∧
      (∀ a ∈ Formalism.MainNotions.LocalSituation.Jset (Formalism.MainNotions.LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i u hu).Kw s
        (D.nbr i u hu).LL hs) (wLat D i (X.ρ i) π u hu hc), -(M0 : ℤ) ≤ a ∧ a ≤ h0) ∧
      (∀ τ, ¬ IsJumpV ((D.loc (D.nd.l i)).PD (D.nbr i u hu).Kw) (wLat D i (X.ρ i) π u hu hc).ρ τ 0) ∧
        invariantsCountConstant D.loc HW D.locA (D.nd.l i) (D.nbr i u hu).Kw s (D.nbr i u hu).LL hs M0 h0
          (wLat D i (X.ρ i) π u hu hc) ≤ X.c0 i u

section T2

variable (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def tTwoLocalLattice {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hc : ∀ v, Continuous fun g => matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) g v)
    (L2 : Lattice (O := ↥(OL C.LL)) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)))) :
    LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
  { V := Fin D.R.r → ↥C.LL.1, ρ := matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)), cont := hc, L := L2 }

def DecompositionInvariantsCondition (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (M0 h0 : ℕ) : Prop :=
  D.nd.l i ≠ 2 ∧ ∀ u ∈ dc.col, ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    IsConjPl D.host u w → (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1 ∧
      ∀ (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hs : Good (D.nbr i w hw).Kw 1 C.LL)
      (hc : ∀ v, Continuous fun g => matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) g v)
      (L2 : Lattice (O := ↥(OL C.LL)) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)))),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) ∧
      (∀ a ∈ Formalism.MainNotions.LocalSituation.Jset (Formalism.MainNotions.LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs)
        (tTwoLocalLattice D i ρ π C hc L2), -(M0 : ℤ) ≤ a ∧ a ≤ h0) ∧
      (∀ τ, ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) τ 0) ∧
      invariantsCountConstant D.loc HW D.locA (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hs M0 h0 (tTwoLocalLattice D i ρ π C hc L2) ≤ c0 u

end T2

def MuUnr (D : D7) : Prop :=
  ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → ∀ w ∈ placesOver D.host.E (D.nd.l i),
    D.naut.unr (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)

def DepthZeroG (D : D7) : Prop :=
  ∀ i : D.nd.Loc, ∀ w ∈ D.nd.S i, (∃ k, w ∈ placesOver D.host.E (D.host.g k)) →
    ∀ P : D.naut.AV i, ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 w),
      D.naut.inePol (D.naut.locV i P w) σ = (Polynomial.X - 1) ^ D.R.nV

def LgcG (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ w ∈ D.nd.S i, (∃ k, w ∈ placesOver D.host.E (D.host.g k)) → ∀ x, ∃ P, D.naut.ptV i P = some x ∧
      D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w =
        D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)

end GlobalTheory.HubX

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

def IsEps {l : ℕ} [Fact l.Prime] (ε : OCb l) : Prop := ε.untilt = 1 ∧ ∃ δ : OCb l, δ ^ l = ε ∧ δ.untilt ≠ 1

def muOf {l : ℕ} [Fact l.Prime] (x : OCb l) : Ainf l := WittVector.teichmuller l x - 1

section General

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {G : Type} [Group G] [TopologicalSpace G]

variable (l O) in

def toB : OA l O →ₐ[O] OB l O := (toOB l O).comp (toOCr l O)

variable {t ϖ} in

def IsCrisCmp {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O} (I : Ident t ϖ P T)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) : Prop :=
  ∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclL t ϖ P c) = TWincl (inclO l O) T z →
    jB (fun i => toB l O (c i)) = TWincl (toB l O) T z

def IsCrisVal (P : PhiMod O K l e a ι) {T : LocLat G ℚ_[l] K O}
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (w : ι → OW l O) (b : TW (OB l O) T) : Prop :=
  ∃ (m : OA l O) (c : ι → OA l O), IsUnit (toB l O m) ∧ inclO l O m • w = inclL t ϖ P c ∧
    toB l O m • b = jB fun i => toB l O (c i)

abbrev actB (s : G →* GQ l) (T : LocLat G ℚ_[l] K O) (g : G) : TW (OB l O) T →ₗ[O] TW (OB l O) T :=
  TWact (galOB O (s g)) T g

def IsCobOf (s : G →* GQ l) (T : LocLat G ℚ_[l] K O) (b : TW (OB l O) T) (c : G → T.V) : Prop :=
  ∀ (g : G) (n : ℕ) (x : ↥T.L.T), (x : T.V) = (l : K) ^ n • c g →
    (1 : OB l O) ⊗ₜ[O] x = (l : O) ^ n • (actB s T g b - b)

variable [TameDescentExponentData K l e a]

variable (K) in

def Covers (h : GQ l) (γ : TameGal K l e a) : Prop :=
  ∀ f f' : ZMod a → A O K, (∀ τ, (f' τ : K⟦X⟧) = ringAct γ (fun σ => (f σ : K⟦X⟧)) τ) →
    galOA O h (ϖ.iTot t K f) = ϖ.iTot t K f'

variable {t ϖ} in

def IsGalDesc (s : G →* GQ l) {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O} (I : Ident t ϖ P T)
    (Δ : Descent P) : Prop :=
  ∀ (g : G) (γ : TameGal K l e a), Covers K t ϖ (s g) γ → ∀ v v' : ME P, v'.1 = Δ.act γ v.1 →
    I.act (s g) g (toW t ϖ P v) = toW t ϖ P v'

def IsHoriz (s : G →* GQ l) (P : PhiMod O K l e a ι) {T : LocLat G ℚ_[l] K O}
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) : Prop :=
  ∀ g : G, s g ∈ GK (ϖ.field a) → ∀ (d : P.D) (h : P.xi d ∈ P.MMl),
    actB s T g (jB (toBcris t ϖ P ⟨P.xi d, h⟩)) = jB (toBcris t ϖ P ⟨P.xi d, h⟩)

structure GalDat (s : G →* GQ l) {η H : ℕ} (D : BKDat O K l e a ι η H) (T : LocLat G ℚ_[l] K O) where

  I : Ident t ϖ D.toPhiMod T

  jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T
  cmp : IsCrisCmp I jB
  desc : IsGalDesc s I D.desc
  stable : ∀ g : G, ∀ v ∈ LA t ϖ D.toPhiMod, I.act (s g) g v ∈ LA t ϖ D.toPhiMod
  horiz : IsHoriz t ϖ s D.toPhiMod jB

namespace GalDat

variable {t ϖ} {s : G →* GQ l} {η H : ℕ} {D : BKDat O K l e a ι η H} {T : LocLat G ℚ_[l] K O}
  (R : GalDat t ϖ s D T)

def IsPotential (y : Vec K a ι) (b : TW (OB l O) T) : Prop :=
  ∃ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O) (σ : D.MMl) (b₀ : TW (OB l O) T),
    phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ ∧ σ.1 ∈ D.desc.inv ∧ D.conn σ.1 = D.zeta y ∧
    IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ ∧ b = R.jB (toBcris t ϖ D.toPhiMod σ) - b₀

def ClassOf (y : Vec K a ι) (c : G → T.V) : Prop := ∃ b, R.IsPotential y b ∧ IsCobOf s T b c

end GalDat

end General

section Ql

variable {l : ℕ} [hl : Fact l.Prime]

variable (l) in

abbrev Gl : Type := ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l))

variable (l) in

abbrev sQ : Gl l →* GQ l := (GK (Formalism.MainNotions.ElementDenominator.qlExt l)).subtype

abbrev QLat (LL : FinExt l) : Type 1 := LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)

def inclG (F : FinExt l) : ↥(GK F) →* Gl l :=
  Subgroup.inclusion (GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := F) bot_le)

def resF {LL : FinExt l} (T : QLat LL) (F : FinExt l) : LocLat ↥(GK F) ℚ_[l] ↥LL.1 ↥(OL LL) :=
  resLoc T (inclG F) (continuous_subtype_val.subtype_mk _)

variable {e : ℕ} (a : ℕ) [NeZero a] (ϖ : PiSys l e) (Pl : LocPrime l) {LL : FinExt l}

def TameType (T : QLat LL) (Sig : Finset (ZMod e)) : Prop :=
  ∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∀ w : ↥LL.1, (w : Om l) * ϖ.seq 0 = (g : GQ l) (ϖ.seq 0) →
    ∀ x ∈ Dcris (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ,
      Polynomial.aeval (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B))
        (∏ c ∈ Sig, (Polynomial.X - Polynomial.C (w ^ c.val))) x = 0

structure IsGood (T : QLat LL) (Sig : Finset (ZMod e)) (U : Finset ℤ) : Prop where
  crys : IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ
  type : TameType a ϖ Pl T Sig
  jumps : ∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ (U : Set ℤ)

variable [NeZero e] [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a]

structure Pack (η H : ℕ) (T : QLat LL) where

  n : ℕ

  D : BKDat ↥(OL LL) ↥LL.1 l e a (Fin n) η H

  R : GalDat (thetaW a LL) ϖ (sQ l) D T
  isBK : IsBK (T := resF T (ϖ.field a)) (R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _))

end Ql

end GlobalTheory.BKGal
end
end

