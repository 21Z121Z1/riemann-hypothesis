import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.LevelLetterCocycles.VKEqOfFrac
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.LinearIndependentSmulOfNeZero
import Formalism.CharacterColumnKernels.IdempotentNormalForms.Bundle0001
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
import Formalism.SharpRestriction.LevelLetterCocycles.ThmELiftAtOf
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingEveryOrdering
import Formalism.SharpRestriction.LevelLetterCocycles.ThmELiftAtBc
import Formalism.SharpRestriction.LevelLetterCocycles.BoundedNumeratorPowerSummability
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.T2SpaceLatticeVOfGoodSituation
import Formalism.SharpRestriction.LevelLetterCocycles.ZlWCbInjective
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0002

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ExistsGoodPlacesEveryConjugate
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.MainNotions.N.TwAll

section Conj

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem psiAt_side_zpow {Γ A : Type} [Group Γ] [CommGroup A] (b b' : Bool) (ψ : Γ →* A) (a : ℤ) :
    ∃ a' : ℤ, a'.natAbs = a.natAbs ∧ Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b' (ψ ^ a) = Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ ^ a') := by
  cases b <;> cases b'
  · exact ⟨a, rfl, rfl⟩
  · refine ⟨-a, Int.natAbs_neg a, ?_⟩
    simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, zpow_neg]
  · refine ⟨-a, Int.natAbs_neg a, ?_⟩
    simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, zpow_neg]
  · exact ⟨a, rfl, rfl⟩

end Conj

end Formalism.MainNotions.N.TwAll

namespace Formalism.MainNotions

open Formalism.MainNotions.N.TwAll

def TwGoodAll (D : D7) (I : TwIn D) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : Prop :=
  ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) → TwGoodOne D I i b Q k' (ψ ^ a)

theorem TwGoodAll.one {D : D7} {I : TwIn D} {i : D.ntw.Tw} {b : Bool} {Q : Finset (PlE D.host)} {k' : ℕ}
    {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ} (h : TwGoodAll D I i b Q k' ψ) : TwGoodOne D I i b Q k' ψ := by
  have := h 1 (by simp)
  rwa [zpow_one] at this

theorem TwGoodAll.side {D : D7} {I : TwIn D} {i : D.ntw.Tw} {b : Bool} {Q : Finset (PlE D.host)} {k' : ℕ}
    {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ} (h : TwGoodAll D I i b Q k' ψ) (b' : Bool) :
    TwGoodAll D I i b' Q k' ψ := by
  intro a ha
  obtain ⟨a', h1, h2⟩ := psiAt_side_zpow b b' ψ a
  unfold TwGoodOne
  rw [h2]
  exact h a' (by rw [h1]; exact ha)

def rawPack {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) : TwPack D := ⟨C.twI w, C.Q w, C.k' w, C.psi' w⟩

def TwConjAllAt (D : D7) (C : NChoice D) : Prop :=
  ∀ w w', TwistedAt D w → TwistedAt D w' → C.twI w' = C.twI w →
    ∃ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l (C.twI w)) ∧
      rawPack C w' = ⟨C.twI w, C.Q w, C.k' w, C.psi' w ^ a⟩

def IntegralHeckeEveryConjugate (D : D7) (bkP : BlochKatoReduction.BK D) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.pin bkP) i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.FullRk D.nexp E i j b (IntegralHeckeForms.SgJ D.nexp E i j b)) →
    ∀ S : ∀ (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b),
      (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.BasisOf D.nexp i j b (IntegralHeckeForms.SgJ D.nexp E i j b) (S j b)) →
    ∀ A : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ),
      ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) →
        IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.pin bkP) E N0 i eps' S A Q k' (ψ' ^ a)

def TwADOne (D : D7) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : Prop :=
  BlochKatoReduction.Gen.partAT (BlochKatoReduction.bk0 D) i Q k' (BlochKatoReduction.Gen.psiAt b ψ) (twEps D i) ∧
    BlochKatoReduction.Gen.partD i Q k' (BlochKatoReduction.Gen.psiAt b ψ) (twEps D i)

def TwADAt (D : D7) (C : NChoice D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → TwADOne D (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w)

end Formalism.MainNotions

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section Kill

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

end Kill

end Formalism.MainNotions.N.KillingConditions

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section C6

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

def SelTie (C : NChoice D) : Prop :=
  ∀ i : D.nd.Loc, Formalism.MainNotions.TwistedPlaces.TwLoc D i →
    ∀ π ∈ D.nd.Zgood i, ∃ s : D.ntw.Sig (C.twI (D.nd.w i)),
      Formalism.MainNotions.BlochKatoReduction.Gen.goodS (Formalism.MainNotions.BlochKatoReduction.bk0 D) (C.twI (D.nd.w i)) s ∧
      (Formalism.MainNotions.BlochKatoReduction.Gen.sLen (Formalism.MainNotions.BlochKatoReduction.bk0 D) (C.twI (D.nd.w i)) s (C.k' (D.nd.w i)) (C.Q (D.nd.w i))
                (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt (D.ntw.side _ s) (psiW C (D.nd.w i))) ≠ ⊤ → Br.sFin D.loc D.nbr i (ρ i) π) ∧
      ENNReal.ofReal (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) ≤
        Formalism.MainNotions.BlochKatoReduction.Gen.sLen (Formalism.MainNotions.BlochKatoReduction.bk0 D) (C.twI (D.nd.w i)) s (C.k' (D.nd.w i)) (C.Q (D.nd.w i))
          (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt (D.ntw.side _ s) (psiW C (D.nd.w i)))

def CondTie (C : NChoice D) : Prop :=
  ∀ i : D.nd.Loc, Formalism.MainNotions.TwistedPlaces.TwLoc D i → ∀ v ∈ D.nd.Q i,
    ((lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) : ℚ) : ℝ) ≤
      Formalism.MainNotions.BlochKatoReduction.Gen.tameVal (D.ntw.l (C.twI (D.nd.w i))) (psiW C (D.nd.w i)) (D.nd.plOm.1 v)

end C6

end Formalism.MainNotions.N.KillingConditions

namespace Formalism.MainNotions.LatticeVariant

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt nval SetHyp PsiOk partA partAT partC partD)
open scoped TensorProduct

section All

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}

variable (Y) in
open Classical in

def AdmRunEveryConjugate (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (N0 : X.Tw → ℕ) : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ A0 : Finset (PlE D.host),
  ∀ (J : ℕ) (sd : Fin J → Bool) (h : Fin J → ∀ Q M, LamO X i Q M) (v : Fin J → ℝ),
    (∀ x, 0 ≤ v x) → (∀ x, Good Y i A0 (h x) (v x)) →
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (M : ℕ)
      (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k')ˣ),
      PsiOk i A0 Q k' ψ' ∧ ψ'.comp (X.art i Q) = χ.comp (Y.delU i Q M) ∧
      ∃ ep : Fin J → ℝ, (∀ x, 0 ≤ ep x) ∧ ∑ x, ep x ≤ eps' ∧
      ∀ a : ℤ, a.natAbs.Coprime (X.l i) →
        PsiOk i A0 Q k' (ψ' ^ a) ∧ (ψ' ^ a).comp (X.art i Q) = (χ ^ a).comp (Y.delU i Q M) ∧
        partA bkP i Q k' (ψ' ^ a) eps' ∧ partAT bkP i Q k' (ψ' ^ a) eps' ∧
        partC N0 i Q k' (ψ' ^ a) eps' ∧ partD i Q k' (ψ' ^ a) eps' ∧
        ∀ x, evA i Q M k' (psiAt (sd x) (χ ^ a)) (h x Q M) ≠ 0 ∧
          nval (X.Ok i k') (X.l i) (evA i Q M k' (psiAt (sd x) (χ ^ a)) (h x Q M)) ≤ v x + ep x

variable (Y) in

def admissibleIndexBoundAllPowers (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (N0 : X.Tw → ℕ) : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ F : Formalism.MainNotions.IntegralHeckeForms.RFam Y i,
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, Formalism.MainNotions.IntegralHeckeForms.ABHyp Y i F j b) →
    ∀ A0 : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
      ∀ a : ℤ, a.natAbs.Coprime (X.l i) →
        PsiOk i A0 Q k' (ψ' ^ a) ∧ partAT bkP i Q k' (ψ' ^ a) eps' ∧
        partC N0 i Q k' (ψ' ^ a) eps' ∧ partD i Q k' (ψ' ^ a) eps' ∧
        Formalism.MainNotions.IntegralHeckeForms.partAB Y i F Q k' (ψ' ^ a) eps'

end All

end Formalism.MainNotions.LatticeVariant

namespace Formalism.MainNotions.IntegralHeckeForms

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

section All

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}

variable (Y) in

def goodTwistExistsAllCoprimePowers (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (E : ExpDat Y) (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, FullRk Y E i j b (SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, BasisOf Y i j b (SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    ∀ a : ℤ, a.natAbs.Coprime (X.l i) → GoodTw Y bkP E N0 i eps' S A Q k' (ψ' ^ a)

end All

end Formalism.MainNotions.IntegralHeckeForms

namespace Formalism.MainNotions

end Formalism.MainNotions

namespace Formalism.MainNotions.N.TwAll

open Formalism.MainNotions.BlochKatoReduction.Gen (nval)

theorem nval_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ) : nval O l 0 = 0 := by
  unfold nval
  simp

section Tame

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}

end Tame

end Formalism.MainNotions.N.TwAll

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.MainNotions.N.TwAll

section DensityAveraging

variable {D : D7}

def TameCyc (C : NChoice D) : Prop :=
  ∀ i : D.nd.Loc, Formalism.MainNotions.TwistedPlaces.TwLoc D i → ∀ v ∈ D.nd.Q i, ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
    ∃ m : ℤ, (C.psi' (D.nd.w i)).comp (D.ntw.art (C.twI (D.nd.w i)) (C.Q (D.nd.w i))) σ =
      ((C.psi' (D.nd.w i)).comp (D.ntw.art (C.twI (D.nd.w i)) (C.Q (D.nd.w i))) (D.nd.gam0 i v)) ^ m

end DensityAveraging

end Formalism.MainNotions.N.KillingConditions

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FinLev
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def FinLev (W : LocWach PD LL O v n) : Prop :=
  ∀ (a : ZMod n) (e : ℕ) (H : ℕ → ℕ), ∃ D : ℕ, ∀ u ∈ W.AΔ, ∃ (c : Fin D → O) (w : LetA O n),
    w ∈ W.AΔ ∧ (letE a : LetA O n) * u =
      letE a * ∑ j : Fin D, algebraMap O (LetA O n) (c j) * W.π₀ ^ (j : ℕ) +
        W.π₀ * (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ H t) ^ 2 * (letE a * w)

end Formalism.MainNotions.UnusedSlot80.UGen
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LemCStep
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def LemC (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' S : ℕ) (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) (c : ZMod n) : Prop :=
  ∀ x (hx : x ∈ NcS W T (c - 1)), (∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → up τ = true →
    x ∈ FilL W T Pt c τ (b τ)) → ∀ f, IsCoord W Pt π' Eπ h' S up b c f →
    f ⊗ₜ mkL W T π' c x hx ∈ InvL W T Pt π' Eπ h' c ⊤

def LemN {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' M ρ : ℕ) (c : ZMod n) (α : FrA W π' Eπ h' M c) : Prop :=
  ∀ x hx y hy, x ∈ NL W T₂ Pt π' Eπ h' c → α T₂ ⟨x, hx⟩ = mkP W T₂ π' Eπ h' M c y hy →
    LiftsBy W F π' Eπ h' ρ c y

def LemK {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (π' Eπ : LetA O n) (h' M ρ : ℕ) (c : ZMod n)
    (α : FrA W π' Eπ h' M c) : Prop :=
  ∀ x (hx : x ∈ NcS W T₂ (c - 1)) (h1 : algebraMap (LetA O n) W.EE (letE c) ⊗ₜ mkL W T₂ π' c x hx ∈ LamLA W T₂ π' Eπ h' c ⊤) y hy,
    α T₂ ⟨_, h1⟩ = mkP W T₂ π' Eπ h' M c y hy → LiftsBy W F π' Eπ h' ρ c y

end Local

section Record

def lemCR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (S η h' : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) c,
      1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ → (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) →
      (∀ τ, η < b τ) → (∀ τ, b τ + S ≤ h') → LemC ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' S up b c

def lemNR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (h' : ℕ) c α β,
      IsFrame ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') (sigA l (sK l K) h') c α β → 1 ≤ h' → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ →
      F.Onto → (∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h')) → (∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      LemN ((HW l).W K 1 LL hG) F (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') (rhoA l (eK K) h') c α

def lemKR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (h' : ℕ) c α β,
      IsFrame ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') (sigA l (sK l K) h') c α β → 1 ≤ h' → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ →
      F.Onto → (∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h')) → (∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      LemK ((HW l).W K 1 LL hG) F π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') (rhoA l (eK K) h') c α

end Record

def LemCStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → lemCR D HW

def LemNStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → lemNR D HW

def LemKStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → lemKR D HW

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfUnramifiedLifting
section
noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem finiteDimensional_max_unramified (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) := by
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have h : K0 K ≤ K.1 := inf_le_left
  exact FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion h).injective

theorem fd_Ks (K : FinExt l) (s : ℕ) : FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  classical
  have hpos : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos _
  have hfin : Set.Finite {x : Om l | x ^ (l ^ s) = 1} :=
    (Polynomial.nthRoots (l ^ s) (1 : Om l)).toFinset.finite_toSet.subset fun x hx => by
      simpa [Polynomial.mem_nthRoots hpos] using hx
  haveI : Finite {x : Om l | x ^ (l ^ s) = 1} := hfin.to_subtype
  haveI : FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ s) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x hx =>
      IsIntegral.of_pow hpos (by rw [hx]; exact isIntegral_one)
  haveI := finiteDimensional_max_unramified K
  unfold Ks
  exact IntermediateField.finiteDimensional_sup _ _

def bigLL (K LL : FinExt l) : FinExt l :=
  ⟨LL.1 ⊔ IntermediateField.normalClosure ℚ_[l] ↥(Ks K 1) (Om l), by
    have := LL.2
    have := fd_Ks K 1
    exact IntermediateField.finiteDimensional_sup _ _⟩

theorem le_bigLL (K LL : FinExt l) : LL.1 ≤ (bigLL K LL).1 := le_sup_left

theorem unram_of_caseA {K LL : FinExt l} (hA : CaseA K LL) :
    Function.Bijective (algebraMap ↥(K0 K) ↥K.1) := by
  refine ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun y => ⟨⟨y, ⟨y.2, hA.1 y.2⟩⟩, ?_⟩⟩
  apply Subtype.ext
  rfl

def BrRest {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] (W : LocWach PD LL O v n)
    [Fintype (K →ₐ[Qp] LL)] : Prop :=
  ∃ e : W.DD W.one, UnitGen W e ∧ BKExt W e ∧ ∀ hR : Ring9 W, Realised2 hR e

theorem brHyp2_of_rec (P : LocPrime l) {K LL : FinExt l} (hA : CaseA K LL) (h5 : 5 ≤ l)
    [NeZero (finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)]
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (finrank ℚ_[l] ↥(K0 K))) (hs : W.s = 1) {Cc : ℝ}
    (h5W : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h6W : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W) (h9W : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (h2a : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexFirstProperty W) (hwx : Formalism.MainNotions.LiftingTheory.coreWX W) (hwr : Formalism.MainNotions.LiftingTheory.coreWR W Cc)
    (htools : ToolsAlg W) (hf1 : F1 W) (hf2 : F2 W) (hH : HodgeExact (P.PD K) ↥LL.1 ↥(OL LL))
    (hrest : BrRest W) : BrHyp2 W Cc := by
  refine ⟨hs, unram_of_caseA hA, ?_, h5W, h6W, h9W, h2a, hwx, hwr, htools, hf1, hf2, hH, ?_, ?_, hrest⟩
  · rw [P.PD_p K]
    exact h5
  · unfold ValRing
    refine ⟨fun a b h => Subtype.ext h, fun x hx => ⟨⟨x, (P.v_O LL x).1 hx⟩, rfl⟩, fun o => ?_⟩
    exact (P.v_O LL _).2 o.2
  · rw [P.PD_p K]
    exact complete_OL LL

end Formalism.MainNotions.WachCoordinates.Br
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.NormOfVOne
section
noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation Topology Filter

variable {l : ℕ} [hl : Fact l.Prime]

theorem zetaQ_pow (P : LocPrime l) (j k : ℕ) : P.ζQ (j + k) ^ (l ^ k) = P.ζQ j := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, P.ζQ_succ, ih]

theorem chiQ_norm (P : LocPrime l) (h : GQ l) : ‖(P.χQ h : ℚ_[l])‖ = 1 := by
  have hroot : P.ζQ 1 ^ l = 1 := by
    have h0 := zetaQ_pow P 0 1
    rwa [zero_add, P.ζQ_zero, pow_one] at h0
  have hle : ∀ g : GQ l, ‖(P.χQ g : ℚ_[l])‖ ≤ 1 := by
    intro g
    obtain ⟨a, ha, -⟩ := P.χQ_cyc g 1 (P.ζQ 1) (by rwa [pow_one])
    have hA : ‖(a : ℚ_[l])‖ ≤ 1 := by
      have h2 : ‖((a : ℤ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((0 : ℕ) : ℤ)) := by
        first
          | exact (Padic.norm_int_le_pow_iff_dvd (a : ℤ) 0).2 (by simp)
          | exact (padicNormE.norm_int_le_pow_iff_dvd (a : ℤ) 0).2 (by simp)
      simpa using h2
    have hl1 : (l : ℝ) ^ (-((1 : ℕ) : ℤ)) ≤ 1 := by
      have h3 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_lt.le
      simp only [Nat.cast_one, zpow_neg, zpow_one]
      first
        | exact inv_le_one_of_one_le₀ h3
        | exact inv_le_one h3
    calc ‖(P.χQ g : ℚ_[l])‖ = ‖((P.χQ g : ℚ_[l]) - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ max ‖(P.χQ g : ℚ_[l]) - a‖ ‖(a : ℚ_[l])‖ := by
        first
          | exact Padic.nonarchimedean _ _
          | exact padicNormE.nonarchimedean _ _
          | exact IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (ha.trans hl1) hA
  have h1 := hle h
  have h2 := hle h⁻¹
  have hmul : ‖(P.χQ h : ℚ_[l])‖ * ‖(P.χQ h⁻¹ : ℚ_[l])‖ = 1 := by
    rw [← norm_mul, ← Units.val_mul, ← map_mul]
    simp
  exact le_antisymm h1 (by nlinarith [norm_nonneg (P.χQ h : ℚ_[l]), norm_nonneg (P.χQ h⁻¹ : ℚ_[l])])

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionRingInput
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

def SecondPropositionHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → u2R D HW

end Formalism.MainNotions.N.Ln34

end
end

