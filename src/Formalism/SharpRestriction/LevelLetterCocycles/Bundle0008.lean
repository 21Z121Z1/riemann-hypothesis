import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ReducibleThreeDim
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0011
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0013
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0012

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.AutomorphicSideWildInertia
section
noncomputable section

namespace Formalism.MainNotions.AutomorphicSideWildInertia

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

def ResidualIrreducibleGood (D : D7) : Prop := ResidualIrreducibleRankR D

def AdmRhoBar (D : D7) : Prop :=
  SumRepresentations.tie0 D ∧ SumRepresentations.adm2 D ∧ SumRepresentations.ArchimedeanSignatureMatching D ∧ SumRepresentations.adm5 D ∧ SumRepresentations.Conclusion41 D ∧ SumRepresentations.Conclusion42 D ∧ ArithmeticCylinders.adm3 D ∧ ArithmeticCylinders.ArchimedeanSignatureMatching D

def ResidualIrreducibleTheorem (D : D7) : Prop := AdmRhoBar D → ResidualIrreducibleGood D

def WildInertiaTrivial (D : D7) : Prop := GlobalDatumLocalisationCondition D

def AdmWild (D : D7) : Prop := SigTie D ∧ SumRepresentations.tie0 D ∧ SumRepresentations.adm2 D ∧ SumRepresentations.ArchimedeanSignatureMatching D ∧ SumRepresentations.Conclusion41 D

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal in

def WildGap (D : D7) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ s : D.ntw.Sig i, ¬ SideLoc D i (D.ntw.side i s) → ∀ k, D.host.g k ≠ D.ntw.l i →
    ∀ v ∈ placesOver D.host.E (D.host.g k), ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
      ∀ σ : G D.host.E D.nd.Om, Formalism.MainNotions.BlochKatoReduction.IsWild A σ → Formalism.MainNotions.BlochKatoReduction.Gen.rbar D.ntw i s σ = 1

def WildInertiaTheorem (D : D7) : Prop := AdmWild D → WildGap D → WildInertiaTrivial D

def AutomorphicSideConclusion (D : D7) (bkP : BlochKatoReduction.BK D) : Prop := BlochKatoReduction.adm1 bkP

def AutomorphicSideHypotheses (D : D7) : Prop :=
  SigTie D ∧ SumRepresentations.tie0 D ∧ SumRepresentations.adm2 D ∧ SumRepresentations.ArchimedeanSignatureMatching D ∧ SumRepresentations.Conclusion41 D ∧ SumRepresentations.CuspidalGaloisUnramified D ∧ SumRepresentations.Conclusion42 D

def AutomorphicSideOpenCase (D : D7) (bkP : BlochKatoReduction.BK D) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ s : D.ntw.Sig i, ¬ SideLoc D i (D.ntw.side i s) → BlochKatoReduction.Gen.IsotypicValuationAtRing bkP i s

def AutomorphicSideTheorem (D : D7) (bkP : BlochKatoReduction.BK D) : Prop := AutomorphicSideHypotheses D → AutomorphicSideOpenCase D bkP → AutomorphicSideConclusion D bkP

end Formalism.MainNotions.AutomorphicSideWildInertia
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.HerrCohomologyExtensions
section
noncomputable section

namespace Formalism.MainNotions.HerrCohomologyExtensions

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Ties

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def UnitGen (e : W.DD W.one) (e₀ : W.one.V) : Prop :=
  e ∈ W.N W.one ∧ W.N W.one = Submodule.span (LetA O n) {e} ∧
    Submodule.span W.EE {e} = (⊤ : Submodule W.EE (W.DD W.one)) ∧
    W.φD W.one e = e ∧ (∀ g, W.γD W.one g e = e) ∧ W.one.L.T = Submodule.span O {e₀}

def clsK (T : LocLat G Qp LL O) (κ : G → T.V) (hκ : κ ∈ latticeCocycles T.L) : LatticeCohomology T.L :=
  Submodule.Quotient.mk (⟨κ, hκ⟩ : ↥(latticeCocycles T.L))

def IsCocOf {T Tp : LocLat G Qp LL O} (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (e₀ : W.one.V) (κ : G → T.V) : Prop :=
  IsSESLat (Qp := Qp) ι π ∧ ∃ t ∈ Tp.L.T, π.f t = e₀ ∧ ∀ g, ι.f (κ g) = Tp.ρ g t - t

def ExtKs (e : W.DD W.one) (e₀ : W.one.V) : Prop :=
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (κ : G → T.V) (hκ : κ ∈ latticeCocycles T.L), IsCocOf W ι π e₀ κ →
    ∀ (x : W.DD Tp) (c : O), W.map π x = c • e →
    ∀ w : ↥(W.divisibleCocycles T), W.map ι (w : W.DD T × W.DD T).1 = W.φD Tp x - x →
      W.map ι (w : W.DD T × W.DD T).2 = W.γ Tp x - x →
      W.cl T w = c • Formalism.MainNotions.DeltaInvariantLattices.res W.GKs T (clsK T κ hκ)

def ExtK (e : W.DD W.one) (e₀ : W.one.V) : Prop :=
  W.s = 1 → PD.p ≠ 2 →
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (κ : G → T.V) (hκ : κ ∈ latticeCocycles T.L), IsCocOf W ι π e₀ κ →
    ∀ (x : W.DD Tp) (c : O), W.map π x = c • e → (∀ δ ∈ W.DelF, W.γD Tp δ x = x) →
    ∀ w : ↥(W.wachCocyclesDelta T), W.map ι (w : W.DD T × W.DD T).1 = W.φD Tp x - x →
      W.map ι (w : W.DD T × W.DD T).2 = W.γD Tp W.gamK x - x →
      W.clK T w = c • clsK T κ hκ

def CrystallineExtensionImage (e : W.DD W.one) (e₀ : W.one.V) : Prop :=
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L) (M h : ZMod n → ℕ)
    (κ : G → T.V) (hκ : κ ∈ latticeCocycles T.L), IsCocOf W ι π e₀ κ →
    IsCrys PD T.ρ → IsCrys PD Tp.ρ → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h →
    ∀ c : O, (∃ x ∈ W.N Tp, W.map π x = c • e) →
      ∃ (y z : W.DD T) (hw : (y, z) ∈ W.divisibleCocycles T),
        y ∈ Formalism.MainNotions.DeltaInvariantLattices.invN W T (W.Q ^ Formalism.MainNotions.DeltaInvariantLattices.mx M) ∧ z ∈ Formalism.MainNotions.DeltaInvariantLattices.aN W T W.X ∧
        W.cl T ⟨(y, z), hw⟩ = c • Formalism.MainNotions.DeltaInvariantLattices.res W.GKs T (clsK T κ hκ)

def HerrExt : Prop :=
  ∃ (e : W.DD W.one) (e₀ : W.one.V), UnitGen W e e₀ ∧ ExtKs W e e₀ ∧ ExtK W e e₀

theorem invariant_cocycle_le_gamma_cocycle (h1 : W.s = 1) (h2 : PD.p ≠ 2) (T : LocLat G Qp LL O) : W.wachCocyclesDelta T ≤ W.divisibleCocycles T := by
  intro w hw
  have hg : W.gamK = W.gam := W.gamK_eq_one h1 h2
  unfold LocWach.wachCocyclesDelta herrZ1Δ at hw
  rw [hg] at hw
  exact hw.1

def ClKRes : Prop :=
  ∀ (h1 : W.s = 1) (h2 : PD.p ≠ 2) (T : LocLat G Qp LL O) (w : ↥(W.wachCocyclesDelta T)),
    Formalism.MainNotions.DeltaInvariantLattices.res W.GKs T (W.clK T w) = W.cl T ⟨(w : W.DD T × W.DD T), invariant_cocycle_le_gamma_cocycle W h1 h2 T w.2⟩

end Ties

def TheoremCConstantsRange (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (R : ℕ → Prop) (k₁ k₂ k₃ k₄ k₅ C : ℝ) : Prop :=
  Formalism.MainNotions.RamifiedCoefficientChains.TheoremCConstantsRange D HW F R k₁ k₂ k₃ k₄ k₅ C

def aux₃ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.aux₃ D HW F C

def Conclusion2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.Conclusion2 D HW F C

def adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm1 D HW F Cm

def adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm2 D HW F

def adm3 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm3 D HW F

def ArchimedeanSignatureMatching (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.ArchimedeanSignatureMatching D HW F

def adm5 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm5 D HW F

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm6 D HW F

def adm7 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm7 D HW F C

def adm8 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm8 D HW F

def adm9 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm9 D HW F

def adm10 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm10 D HW F CA CB CK

def adm11 (D : D7) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm11 D

def adm12 (D : D7) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm12 D

def adm13 (D : D7) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm13 D

def adm14 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm14 D HW F

def adm15 (D : D7) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm15 D

def adm16 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    HerrExt ((HW l).W K s LL h)

def adm17 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ClKRes ((HW l).W K s LL h)

def adm18 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ((HW l).W K s LL h).ClNat ∧ Formalism.MainNotions.DeltaInvariantLattices.ClKNatG ((HW l).W K s LL h)

def admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) : Prop :=
  adm1 D HW F Cm ∧ adm2 D HW F ∧ adm3 D HW F ∧ ArchimedeanSignatureMatching D HW F ∧ adm5 D HW F ∧ adm6 D HW F ∧ adm7 D HW F CR ∧ adm8 D HW F ∧ adm9 D HW F ∧
    adm10 D HW F CA CB CK ∧ adm11 D ∧ adm12 D ∧ adm13 D ∧ adm14 D HW F ∧ adm15 D ∧ adm16 D HW F ∧ adm17 D HW F ∧
    adm18 D HW F

def Stmt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (C CR CA CB CK : ℝ) : Prop := admitted D HW F Cm CR CA CB CK → aux₃ D HW F C

end Formalism.MainNotions.HerrCohomologyExtensions
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
section
noncomputable section

namespace Formalism.MainNotions.IdempotentChoiceDepthZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Obj51

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))

def IsOrthogonalIdempotentDecomposition (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) (S : IdempotentChoiceData N i) : Prop :=

  (InR N i r S.eB ∧ InR N i r S.e1 ∧ S.eB * S.eB = S.eB ∧ S.e1 * S.e1 = S.e1 ∧
    S.eB * S.e1 = 0 ∧ S.e1 * S.eB = 0 ∧
    (∀ x, ((S.eB x).map (toK N i)).rank = R.t) ∧ (∀ x, ((S.e1 x).map (toK N i)).rank = 1)) ∧

  (∀ g u, S.e ((mapM (toK N i) (rO N i r π) g).mulVec u) =
      ((mapM (toK N i) (rhoO N i ρ π) g).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (S.e u).2 c)) ∧
  (∀ a, InR' N r S a → ∀ u, S.e (((a S.π').map (toK N i)).mulVec u) =
      (((S.ψρ a).map (toK N i)).mulVec (S.e u).1,
        fun c : Fin R.t => toK N i (S.ψχ c a) * (S.e u).2 c)) ∧
  (∀ A : Matrix (Fin R.r) (Fin R.r) (N.O i), ∃ a, InR' N r S a ∧ S.ψρ a = A) ∧

  (∃ w ∈ placesOver H.E (N.l i), S.g0 ∈ Ine (F := H.E) (N.plOm.1 w)) ∧
  orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) S.g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) =
    N.l i - 1 ∧

  (InR N i r S.X0 ∧ S.eB * S.X0 = S.X0 ∧ S.X0 * S.eB = S.X0 ∧
    ∀ u, S.e (((S.X0 π).map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) S.g0 : (N.O i)ˣ) : N.O i) * (S.e u).2 c)) ∧

  ((∀ f ∈ N.T i, (fun x' => f (S.p x')) ∈ S.T') ∧ (∀ c ∈ Finset.Icc 1 R.t, S.rr c ∈ S.T') ∧
    S.T' = Algebra.adjoin (N.O i) ((fun f : N.X i → N.O i => fun x' => f (S.p x')) '' (N.T i : Set _) ∪
      (fun c => S.rr c) '' (Finset.Icc 1 R.t : Set ℕ)) ∧
    (∃ b : Fin R.t.factorial → S.X' → N.O i, (∀ k, b k ∈ S.T') ∧
      ∀ f ∈ S.T', ∃! cf : Fin R.t.factorial → N.T i,
        f = ∑ k, ((fun x' => (cf k : N.X i → N.O i) (S.p x')) : S.X' → N.O i) * b k) ∧
    (∀ x, Nat.card {x' // S.p x' = x} = R.t.factorial)) ∧

  (∀ x', ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c x')) =
    Matrix.det ((Polynomial.X : Polynomial (N.O i)) • (S.eB (S.p x')).map (Polynomial.C (R := N.O i)) -
      (S.X0 (S.p x')).map (Polynomial.C (R := N.O i)) + 1 -
      (S.eB (S.p x')).map (Polynomial.C (R := N.O i)))) ∧

  (S.p S.π' = π ∧ ∀ c ∈ Finset.Icc 1 R.t,
    S.rr c S.π' = ((chiU N i c S.g0 : (N.O i)ˣ) : N.O i)) ∧

  ((∀ x', ((Eel N S x').map (toK N i)).rank = 1) ∧
    (∀ x', Eel N S x' * Eel N S x' = del51 N S x' • Eel N S x') ∧
    (∀ u, S.e (((Eel N S S.π').map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => if (c : ℕ) = 0 then toK N i (del51 N S S.π') * (S.e u).2 c else 0)) ∧
    IsUnit (del51 N S S.π')) ∧

  CharpolyCoeffsInSubalgebra N i S.T' (fun x' => rO N i r (S.p x'))

end Obj51

end Formalism.MainNotions.IdempotentChoiceDepthZero
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheoremOfExplicit
section
noncomputable section

namespace Formalism.MainNotions.ElementDenominator

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Orbit

variable {G LL : Type} [Group G] [Field LL] (I : Subgroup G) [hI : I.Normal] (Fr : G)

def frobChar : (I →* LLˣ) →* (I →* LLˣ) :=
  MonoidHom.compHom' (MulAut.conjNormal Fr⁻¹ : I ≃* I).toMonoidHom

end Orbit

section Iner

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)

end Iner

section PartII

variable {l : ℕ} [Fact l.Prime]
    {K₀' K' B BdR : Type} [Field K₀'] [Field K'] [Algebra ℚ_[l] K₀'] [Algebra ℚ_[l] K']
    [Algebra K₀' K'] [IsScalarTower ℚ_[l] K₀' K'] [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B]
    [Algebra ↥(K0 (qlExt l)) B] [IsScalarTower ℚ_[l] ↥(K0 (qlExt l)) B] [Algebra K₀' B]
    [IsScalarTower ℚ_[l] K₀' B] [Algebra ℚ_[l] BdR] [Algebra ↥(K0 (qlExt l)) BdR]
    [Algebra ↥(qlExt l).1 BdR] [IsScalarTower ℚ_[l] ↥(qlExt l).1 BdR]
    [IsScalarTower ↥(K0 (qlExt l)) ↥(qlExt l).1 BdR] [IsScalarTower ℚ_[l] ↥(K0 (qlExt l)) BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower ℚ_[l] K' BdR] [IsScalarTower K₀' K' BdR]
    [IsScalarTower ℚ_[l] K₀' BdR]
    (PC : PotCrysData ↥(GK (qlExt l)) ℚ_[l] ↥(K0 (qlExt l)) ↥(qlExt l).1 K₀' K' B BdR)
    (LL : FinExt l)

def HypT (T₁ T₂ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (N η H : ℕ)
    (U : Finset ℤ) (Sig : Finset (PC.Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK (qlExt l))) : Prop :=
  PC.IsPotCrys T₁.ρ ∧ PC.IsPotCrys T₂.ρ ∧ F.Onto ∧
    PC.IsFrob Fr ∧ FrobStable PC.Iner Fr Sig ∧ 1 ∈ Sig ∧ Sig.card ≤ N ∧ 2 ≤ N ∧
    PC.InertiaThrough T₁.ρ Sig ∧ PC.InertiaThrough T₂.ρ Sig ∧
    (∀ u ∈ U, -(η : ℤ) ≤ u ∧ u ≤ H) ∧ (0 : ℤ) ∈ U ∧ U.card ≤ N + 1 ∧ 1 ≤ η ∧ η < H ∧
    (∀ τ, JumpsInV PC.PD T₁.ρ τ (U : Set ℤ)) ∧ (∀ τ, JumpsInV PC.PD T₂.ρ τ (U : Set ℤ))

def thmTLift (C : ℕ) : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (N η H : ℕ)
    (U : Finset ℤ) (Sig : Finset (PC.Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK (qlExt l))),
    HypT PC LL T₁ T₂ F N η H U Sig Fr → C * (H * N ^ 2 + N ^ 3) < l →
      F.LiftF PC.PD (C * (N * rPrime PC.Iner Fr Sig + η * (N + rPrime PC.Iner Fr Sig)))

def expT (N r' η : ℕ) : ℕ :=
  2 * (2 * N * r') + 2 * η + (N + 1) * η + (η * (r' + 1) + 2 * N * r') + η * (r' + 1) + 1

def thmTExp : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (N η H : ℕ)
    (U : Finset ℤ) (Sig : Finset (PC.Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK (qlExt l))),
    HypT PC LL T₁ T₂ F N η H U Sig Fr → 40 * (H * N ^ 2 + N ^ 3) < l →
      F.LiftF PC.PD (expT N (rPrime PC.Iner Fr Sig) η)

variable {PC LL}

variable (PC LL)

end PartII

def LiftingClause (D : D7) (C : ℕ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K' : FinExt l) (h : (qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (qlExt l))) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc l).PD (qlExt l)).actB g (algebraMap ↥(K0 K') (D.loc l).R.B c) =
        algebraMap ↥(K0 K') (D.loc l).R.B c')
    (LL : FinExt l), thmTLift (pc (D.loc l) h hN hF hS) LL C

def ExplicitLiftingClause (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K' : FinExt l) (h : (qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (qlExt l))) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc l).PD (qlExt l)).actB g (algebraMap ↥(K0 K') (D.loc l).R.B c) =
        algebraMap ↥(K0 K') (D.loc l).R.B c')
    (LL : FinExt l), thmTExp (pc (D.loc l) h hN hF hS) LL

def TwoStep {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (l g g₀ e e' : ℕ)
    (Z Bc I : Submodule O M) : Prop :=
  ∃ s s₀ : Finset M, s.card ≤ g ∧ Submodule.span O (s : Set M) ⊔ Bc = Z ∧
    s₀.card ≤ g₀ ∧ (s₀ : Set M) ⊆ Z ∧
    (∀ p ∈ Z, (l ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) ∧
    (∀ p ∈ Submodule.span O (s₀ : Set M), (l ^ e' : ℕ) • p ∈ I)

theorem len_ne_top {O : Type} [CommRing O] [IsDedekindDomain O] (x : O) (h : x ≠ 0) :
    Module.length O (O ⧸ Ideal.span {x}) ≠ ⊤ := by
  rw [Module.length_ne_top_iff]
  apply isFiniteLength_quotient_span_singleton
  rwa [mem_nonZeroDivisors_iff_ne_zero]

theorem len_le_nat {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (l p g g₀ y e' k : ℕ)
    (Z Bc I : Submodule O M) (h : TwoStep l g g₀ y e' Z Bc I) (hB : Bc ≤ I) (hp : p = l)
    (hk : Module.length O (O ⧸ Ideal.span {((p : ℕ) : O)}) = (k : ℕ∞)) :
    ∃ m : ℕ, Module.length O (↥Z ⧸ I.comap Z.subtype) = (m : ℕ∞) ∧ m ≤ (g * y + g₀ * e') * k := by
  subst hp
  obtain ⟨s, s₀, hs, hgen, hs₀, hsub, h1, h2⟩ := h
  have key := Formalism.IrreducibleCountingLemmas.WindowSums.colength_bound_two_layers O M p g g₀ y e' Z Bc I s s₀ hs hgen hB hs₀ hsub h1 h2
  rw [hk] at key
  have hcol : Module.length O (↥Z ⧸ I.comap Z.subtype) ≤ (((g * y + g₀ * e') * k : ℕ) : ℕ∞) := by
    push_cast
    exact key
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hcol)
  refine ⟨m, hm.symm, ?_⟩
  rw [← hm] at hcol
  exact_mod_cast hcol

section PartI

variable {l : ℕ} [Fact l.Prime]

theorem lenOl_finite (P : LocPrime l) (K LL : FinExt l) :
    ∃ k : ℕ, lenOl (P.PD K) (O := ↥(OL LL)) = (k : ℕ∞) := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsDedekindDomain ↥(OL LL) := integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1
  have hne : lenOl (P.PD K) (O := ↥(OL LL)) ≠ ⊤ := by
    apply len_ne_top
    rw [P.PD_p K]
    intro h
    have h2 := congrArg (Subtype.val : ↥(OL LL) → ↥LL.1) h
    have h3 : ((l : ℕ) : ↥LL.1) = 0 := by simpa using h2
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h3)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
  exact ⟨k, hk.symm⟩

theorem colLe_mono (P : LocPrime l) (K LL : FinExt l) {T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)}
    (F : LatHom T₁.L T₂.L) {b b' : ℝ} (hb : b ≤ b') (h : colLe P K LL F b) : colLe P K LL F b' := by
  obtain ⟨m, k, h1, h2, h3⟩ := h
  exact ⟨m, k, h1, h2, h3.trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg k))⟩

theorem colLe_of_twoStep (P : LocPrime l) (K LL : FinExt l)
    {T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)} (F : LatHom T₁.L T₂.L) (g g₀ y e' : ℕ)
    (h : TwoStep l g g₀ y e' (latticeFiniteCocycles (P.PD K) T₂.L) (latticeCoboundaries T₂.L) (F.ImF (P.PD K))) :
    colLe P K LL F ((g : ℝ) * y + (g₀ : ℝ) * e') := by
  obtain ⟨k, hk⟩ := lenOl_finite P K LL
  obtain ⟨m, hm, hmk⟩ := len_le_nat l (P.PD K).p g g₀ y e' k _ _ _ h le_sup_right (P.PD_p K) hk
  refine ⟨m, k, hm, hk, ?_⟩
  exact_mod_cast hmk

def HypA (P : LocPrime l) (K LL : FinExt l) (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (F : LatHom T₁.L T₂.L) (r S η m h : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
    (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) : Prop :=
  IsCrys (P.PD K) T₁.ρ ∧ IsCrys (P.PD K) T₂.ρ ∧ F.Onto ∧
    finrank ↥LL.1 T₂.V = r ∧
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) ∧
    (∀ τ, η < b τ) ∧
    (∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) T₂.ρ τ a ≤ m) ∧
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) ∧
    (finrank ↥(K0 K) ↥K.1 = 2 ∨ ∀ τ τ', intersection_update_fsHerm_neg_one K τ = intersection_update_fsHerm_neg_one K τ' → up τ = up τ')

def thmAOpen (P : LocPrime l) (K LL : FinExt l) (c CK : ℝ) : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    ∃ (g y e' : ℕ) (ρ σ κ : ℝ),
      TwoStep l g (finrank ℚ_[l] ↥(K0 K) * finrank ↥(K0 K) ↥K.1 * (finrank ↥(K0 K) ↥K.1 + 1) * m) y e'
        (latticeFiniteCocycles (P.PD K) T₂.L) (latticeCoboundaries T₂.L) (F.ImF (P.PD K)) ∧
      g ≤ 2 * ((finrank ℚ_[l] ↥(K0 K) * finrank ↥(K0 K) ↥K.1 + 1) * r) ∧
      ρ ≤ 9 * ((finrank ↥(K0 K) ↥K.1 * h : ℕ) : ℝ) / l + 3 ∧
      σ ≤ 9 * ((finrank ↥(K0 K) ↥K.1 * h : ℕ) : ℝ) / l + 3 ∧
      κ ≤ (finrank ↥(K0 K) ↥K.1 : ℝ) *
        ((S : ℝ) + (S : ℝ) / ((l : ℝ) - 1) + Real.logb l ((h : ℝ) + S)) ∧
      (y : ℝ) ≤ c * (ρ + σ) + κ + η + 1 + Real.logb l h ∧
      (e' : ℝ) ≤ CK * ((h : ℝ) + 1)

end PartI

def TheoremAOpenPart (D : D7) (c CK : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → thmAOpen (D.loc l) K LL c CK

end Formalism.MainNotions.ElementDenominator

end
end

