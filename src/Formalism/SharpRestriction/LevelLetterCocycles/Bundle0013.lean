import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0011
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0007

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ExtensionClauses
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot35

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def CocycleClassImage (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm17 D HW F

def AdmExtC (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P8 D HW F ∧ Formalism.MainNotions.HerrComplexNaturality.HerrExtensionUpToUnit D HW F

def ExtensionClassTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmExtC D HW F → CocycleClassImage D HW F

def InvariantCocycleClassImage (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm18 D HW F

def AdmExtCΔ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P8 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F ∧ Formalism.MainNotions.HerrComplexNaturality.HerrExtensionUpToUnit D HW F

def InvariantCocycleClassTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmExtCΔ D HW F → InvariantCocycleClassImage D HW F

def CyclotomicCorollaryBound (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm20 D HW F

def CyclotomicLiftingBoundTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := CyclotomicCorollaryBound D HW F

def AdmDss (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P2 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.gammaSemisimpleQuotientGlobal D HW F

def ProductKillsPoleQuotient (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm19 D HW F

def SemisimpleProductTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmDss D HW F Cm → ProductKillsPoleQuotient D HW F

def SemisimpleAtLetter (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm18 D HW F

def SemisimpleLetterTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmDss D HW F Cm → SemisimpleAtLetter D HW F

end Formalism.MainNotions.UnusedSlot35
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def FiltrationPropertiesEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.WachCoordinates.adm7 D HW F Cm

def AdmTools (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def FiltrationPropertiesTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmTools D HW F Cm → FiltrationPropertiesEtale D HW F Cm

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def Pi0LatticeCondition (W : LocWach PD LL O v n) : Prop := ∀ g : W.Gam, ∃ u ∈ W.AΔ, W.γA g W.π₀ = W.π₀ * u

end Core

def GammaPreservesUniformiser (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h => Pi0LatticeCondition ((HW l).W K 1 LL h.2.2)

def AdmPi0 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def UniformiserGammaTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmPi0 D HW F → GammaPreservesUniformiser D HW F

def AdmSat (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def SaturationArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm5 D HW F
def SaturationTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmSat D HW F → SaturationArcLifting D HW F
def SaturationEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm8 D HW F
def SaturationTheoremEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmSat D HW F → SaturationEtale D HW F

def FirstFiltrationHypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P2 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F ∧ Formalism.MainNotions.HerrComplexNaturality.HerrNaturality D HW F

def FirstFiltrationArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm6 D HW F
def FirstFiltrationTheoremCaseA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := FirstFiltrationHypotheses D HW F → FirstFiltrationArcLifting D HW F
def FirstFiltrationEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm9 D HW F
def FirstFiltrationTheoremEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := FirstFiltrationHypotheses D HW F → FirstFiltrationEtale D HW F

def SecondFiltrationHypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P7 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.Pr2b D HW F

def SecondFiltrationArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm7 D HW F
def SecondFiltrationTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := SecondFiltrationHypotheses D HW F ∧ FirstFiltrationArcLifting D HW F → SecondFiltrationArcLifting D HW F
def SecondFiltrationEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm10 D HW F
def FamilyMassExplicitOfVolumeAgreement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := SecondFiltrationHypotheses D HW F ∧ FirstFiltrationEtale D HW F → SecondFiltrationEtale D HW F

def KillerAtLevels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.KillerLevL D.loc D.locA HW F

def AdmKillLev (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def KillerLevelsTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmKillLev D HW F Cm → KillerAtLevels D HW F

def KillerBoundWithConstant (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm8 D HW F C

def AdmKillA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := KillerAtLevels D HW F ∧ GammaPreservesUniformiser D HW F

def KillerWithConstantTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := AdmKillA D HW F → KillerBoundWithConstant D HW F C

def KillerAtLevelsSecondForm (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.WachCoordinates.adm11 D HW F

def KillerWachCoordinatesTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := GammaPreservesUniformiser D HW F → KillerAtLevelsSecondForm D HW F

def RootMultiplicityTwo (D : D7) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm9 D

def RelayArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm11 D HW F

def AdmRelayA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.LiftingTheory.ConclusionH D HW F ∧ Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F ∧
    SaturationArcLifting D HW F ∧ FirstFiltrationArcLifting D HW F ∧ SecondFiltrationArcLifting D HW F

def RelayTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmRelayA D HW F → RelayArcLifting D HW F

def ArcLiftingCoordinates (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm12 D HW F Cm

def AdmArcA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.LiftingTheory.ConclusionH D HW F ∧
    Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F ∧ Formalism.MainNotions.LiftingTheory.WachAnnihilatorAll D HW F ∧ SaturationArcLifting D HW F

def ArcCoordinatesTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmArcA D HW F Cm → ArcLiftingCoordinates D HW F Cm

def SplittingArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm13 D HW F Cm

def AdmSplitA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P8 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.LiftingTheory.WachAnnihilatorAll D HW F ∧ Formalism.MainNotions.LiftingTheory.adm23 D HW F ∧
    Formalism.MainNotions.HerrComplexNaturality.HerrExtensionClass D HW F ∧ FirstFiltrationArcLifting D HW F ∧ RelayArcLifting D HW F ∧ ArcLiftingCoordinates D HW F Cm

def SplittingTheoremArcLifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmSplitA D HW F Cm → SplittingArcLifting D HW F Cm

def UniversalComponentCaseA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.ArcLiftingSetup.adm14 D HW F Cm

def AdmUnivA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := SaturationArcLifting D HW F ∧ KillerAtLevels D HW F ∧ GammaPreservesUniformiser D HW F ∧ ArcLiftingCoordinates D HW F Cm

def UniversalComponentTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := AdmUnivA D HW F Cm → UniversalComponentCaseA D HW F Cm

def H1fBaseChangeFree (D : D7) : Prop := Formalism.MainNotions.WachCoordinates.adm13 D

def H1fBaseChangeTheorem (D : D7) : Prop := H1fBaseChangeFree D

end Formalism.MainNotions.UnusedSlot80
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FinrankMaxUnramifiedSubfieldPadicFinExtPos
section
noncomputable section

namespace Formalism.MainNotions.N.PreambleDegrees

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.PreambleDegrees.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem finrank_sup_adjoin (F : IntermediateField ℚ_[l] (Om l)) (y : Om l) :
    finrank ℚ_[l] ↥(F ⊔ IntermediateField.adjoin ℚ_[l] {y}) = finrank ℚ_[l] ↥F * (minpoly F y).natDegree := by
  have hint : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup, ← IntermediateField.adjoin.finrank hint]
  exact (Module.finrank_mul_finrank ℚ_[l] ↥F ↥(IntermediateField.adjoin F {y})).symm

theorem Ks_eq (K : FinExt l) (s : ℕ) {z : Om l} (hz : IsPrimitiveRoot z (l ^ s)) :
    Ks K s = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {z} := by
  have : NeZero (l ^ s) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩
  unfold Ks
  congr 1
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one (show x ^ (l ^ s) = 1 from hx)
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _
  · exact IntermediateField.adjoin.mono _ _ _ (by rintro x rfl; exact hz.pow_eq_one)

theorem finrank_Ks (K : FinExt l) {s : ℕ} (hs : 0 < s) :
    finrank ℚ_[l] ↥(Ks K s) = finrank ℚ_[l] ↥(K0 K) * (l ^ (s - 1) * (l - 1)) := by
  have hz := ζQ_primitive l s
  rw [Ks_eq K s hz, finrank_sup_adjoin, natDegree_minpoly_eq (F := K0 K) inf_le_right hs hz,
    Nat.totient_prime_pow Fact.out hs]

theorem finrank_maxUnramifiedSubfield_padicFinExt_pos (K : FinExt l) : 0 < finrank ℚ_[l] ↥(K0 K) := by
  have := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).injective
  exact finrank_pos

theorem sqrt_notMem (y : Om l) (hy : y ^ 2 = -(l : Om l)) : y ∉ MaximalUnramifiedExtension l := by
  intro h
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hn : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    have e : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := (map_natCast _ _).symm
    rw [e]
    exact (PadicAlgCl.norm_extends l _).trans Padic.norm_p
  have h0 : y ≠ 0 := by
    rintro rfl
    have : (l : Om l) = 0 := by simpa using hy.symm
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)
  obtain ⟨k, hk⟩ := norm_Kur_zpow h h0
  have h2 : ‖y‖ ^ 2 = (l : ℝ)⁻¹ := by rw [← norm_pow, hy, norm_neg, hn]
  have h3 : (l : ℝ) ^ (k * 2) = (l : ℝ) ^ (-1 : ℤ) := by
    rw [zpow_mul, ← hk, zpow_neg_one, ← h2]; norm_cast
  have := zpow_right_injective₀ hl0 hl1.ne' h3
  omega

theorem deg_two (K : FinExt l) (y : Om l) (hy : y ^ 2 = -(l : Om l))
    (hK : K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y}) :
    finrank ℚ_[l] ↥K.1 = finrank ℚ_[l] ↥(K0 K) * 2 := by
  have hint : IsIntegral (K0 K) y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  have h1 : finrank ℚ_[l] ↥K.1 = finrank ℚ_[l] ↥(K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y}) :=
    congrArg (fun F : IntermediateField ℚ_[l] (Om l) => finrank ℚ_[l] ↥F) hK
  rw [h1, finrank_sup_adjoin]
  congr 1
  have hle : (minpoly (K0 K) y).natDegree ≤ 2 := by
    have hm : (Polynomial.X ^ 2 + Polynomial.C (l : ↥(K0 K))).Monic := Polynomial.monic_X_pow_add_C _ (by norm_num)
    have hd : (Polynomial.X ^ 2 + Polynomial.C (l : ↥(K0 K))).natDegree = 2 := Polynomial.natDegree_X_pow_add_C
    rw [← hd]
    refine Polynomial.natDegree_le_of_dvd (minpoly.dvd _ _ ?_) hm.ne_zero
    simp [hy]
  have hne : (minpoly (K0 K) y).natDegree ≠ 1 := by
    rw [Ne, minpoly.natDegree_eq_one_iff]
    rintro ⟨c, hc⟩
    exact sqrt_notMem y hy (hc ▸ c.2.2)
  have := minpoly.natDegree_pos hint
  omega

theorem preamble_degree_clauses (D : D7) : Formalism.MainNotions.EmbeddingTypeJumps.DegreeClauses D := by
  intro i hl w hw
  obtain ⟨⟨y, hy, hK⟩, -⟩ := Formalism.MainNotions.EmbeddingTypeJumps.preamble_first_clauses D i hl w hw
  have h2 := deg_two _ y hy hK
  have hp := finrank_maxUnramifiedSubfield_padicFinExt_pos (D.nbr i w hw).Kw
  have ht := Module.finrank_mul_finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1
  have hodd : D.nd.l i % 2 = 1 := by
    obtain ⟨-, -, h3, h7, -⟩ := D.host.hyp
    rcases hl with h | h <;> rw [h] <;> omega
  refine ⟨Nat.eq_of_mul_eq_mul_left hp (ht.trans h2), ?_⟩
  rw [finrank_Ks _ one_pos, h2]
  obtain ⟨k, hk⟩ : ∃ k, D.nd.l i - 1 = 2 * k := ⟨(D.nd.l i - 1) / 2, by omega⟩
  rw [hk, Nat.mul_div_cancel_left _ two_pos]
  simp only [Nat.sub_self, pow_zero]
  ring

theorem scaled_lattice_nonzero_holds (D : D7) : Formalism.MainNotions.EmbeddingTypeJumps.Conclusion0 D := Formalism.MainNotions.EmbeddingTypeJumps.preamble_of_degree_clauses D (preamble_degree_clauses D)

theorem vdeg (K : FinExt l) {m : ℕ} (hm : 0 < m) :
    padicValNat l (finrank ℚ_[l] ↥(Ks K m)) - padicValNat l (finrank ℚ_[l] ↥(Ks K 1)) = m - 1 := by
  have hp := finrank_maxUnramifiedSubfield_padicFinExt_pos K
  have h1 : 0 < l - 1 := by have := (Fact.out : l.Prime).one_lt; omega
  have e : finrank ℚ_[l] ↥(Ks K m) = l ^ (m - 1) * finrank ℚ_[l] ↥(Ks K 1) := by
    rw [finrank_Ks K hm, finrank_Ks K one_pos]; simp only [Nat.sub_self, pow_zero]; ring
  have h0 : finrank ℚ_[l] ↥(Ks K 1) ≠ 0 := by
    rw [finrank_Ks K one_pos]
    exact Nat.mul_ne_zero hp.ne' (Nat.mul_ne_zero (pow_pos (Fact.out : l.Prime).pos _).ne' h1.ne')
  rw [e, padicValNat.mul (pow_pos (Fact.out : l.Prime).pos _).ne' h0, padicValNat.prime_pow]
  omega

theorem gK_zero (K : FinExt l) (h2 : finrank ℚ_[l] ↥K.1 = finrank ℚ_[l] ↥(K0 K) * 2) :
    padicValNat l (finrank ℚ_[l] ↥(Ks K 1)) - padicValNat l (finrank ℚ_[l] ↥K.1) = 0 := by
  have hp := finrank_maxUnramifiedSubfield_padicFinExt_pos K
  have hl := (Fact.out : l.Prime).one_lt
  have h1 : padicValNat l (l - 1) = 0 := padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  rw [finrank_Ks K one_pos, h2]
  simp only [Nat.sub_self, pow_zero, one_mul]
  rw [padicValNat.mul hp.ne' (by omega), padicValNat.mul hp.ne' (by omega), h1]
  omega

end Formalism.MainNotions.N.PreambleDegrees
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.IsTruncIff
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN eY IsRem fMX pullJ IsSer IsTrunc TCase)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsSerZ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : W.DD T)
    (c : ℕ → W.DD T) : Prop :=
  c 0 = 0 ∧ (∀ y, DL W T i (c y) ∧ c y ∈ W.N T) ∧
    ∀ K : ℕ, ∃ j : ℕ, InPN W T K (((PD.p : ℕ) : O) ^ j •
      (((PD.p : ℕ) : O) ^ eY PD.p K • ζ -
        ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (eY PD.p K - eY PD.p y) •
          (W.γ T (W.π₀ ^ y • c y) - W.π₀ ^ y • c y)))

def IsTrZ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (j M X σ : ℕ)
    (ζ t : W.DD T) : Prop :=
  ∃ (c : ℕ → W.DD T) (r s : ℕ → LetA O n), IsSerZ W T i ζ c ∧
    (∀ y, IsRem W j M X y (r y) ∧
      ((PD.p : ℕ) : LetA O n) ^ eY PD.p y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y) ∧
    t = ∑ y ∈ Finset.range (max M X + 1), s y • ((W.φD T) ^ j) (c y)

theorem isTrunc_iff (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (j M X σ : ℕ)
    (w z : W.DD T) :
    IsTrunc W T i j M X σ w z ↔ ∃ t, IsTrZ W T i j M X σ (W.γ T w - w) t ∧
      z = ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w - t := by
  constructor
  · rintro ⟨c, r, s, hc, hr, rfl⟩
    exact ⟨_, ⟨c, r, s, hc, hr, rfl⟩, rfl⟩
  · rintro ⟨t, ⟨c, r, s, hc, hr, rfl⟩, rfl⟩
    exact ⟨c, r, s, hc, hr, rfl⟩

def TTool2Z [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → ∀ (j M X σ : ℕ), TCase PD.p j M X σ →
  ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n),
    (∀ ζ, DL W T i ζ → InPN W T 1 ζ → ∃ t, IsTrZ W T i j M X σ ζ t) ∧
    (∀ ζ t, DL W T i ζ → InPN W T 1 ζ → IsTrZ W T i j M X σ ζ t →
      DL W T (i + (j : ZMod n)) t ∧ t ∈ pullJ W T i j ∧
      ∃ p ∈ pullJ W T i j,
        ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) ζ - (W.γ T t - t) = fMX W M X • p) ∧
    (∀ (a a' : O) (ζ ζ' t t' t'' : W.DD T), DL W T i ζ → InPN W T 1 ζ → DL W T i ζ' →
      InPN W T 1 ζ' → IsTrZ W T i j M X σ ζ t → IsTrZ W T i j M X σ ζ' t' →
      IsTrZ W T i j M X σ (a • ζ + a' • ζ') t'' →
      ∃ p ∈ pullJ W T i j, t'' - (a • t + a' • t') = fMX W M X • p) ∧
    (∀ ζ t, DL W T i ζ → InPN W T M ζ → j = 1 → X ≤ (PD.p - 1) * M →
      IsTrZ W T i j M X σ ζ t → ∃ p ∈ pullJ W T i j, t = fMX W M X • p)

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LetterConditionGlobal
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

def LetterConditionLocal (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (y : ℕ), 1 ≤ y →
  ∀ (dop : W.DD T →ₗ[O] W.DD T), (∀ z, W.π₀ • dop z = W.γ T z - z) →
  ∀ (cc : ℤ → O), (∀ x : ℤ, (-((PD.p : ℕ) : O)) * cc x = (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) - 1) →
  ∀ X : Finset ℤ,
    (∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i → IsJumpV PD T.ρ τ a → 1 ≤ j → j ≤ y →
      a + (j : ℤ) ∈ X) →
    ∀ z : W.DD T, Formalism.MainNotions.LiftingTheory.InNΔi W T i (qA W ^ y • z) →
      Formalism.MainNotions.LiftingTheory.InNΔi W T i
        (Polynomial.aeval dop (∏ x ∈ X, (Polynomial.X - Polynomial.C (cc x))) z)

def LetterConditionGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (_F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    LetterConditionLocal ((HW l).W K s LL h)

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LocalFormOfThreeInputs
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)

def genA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    ∃ s : Finset (↥(GK K) → T₂.V),
      s.card ≤ 2 * ((finrank ℚ_[l] ↥(K0 K) * finrank ↥(K0 K) ↥K.1 + 1) * r) ∧
      Submodule.span ↥(OL LL) (s : Set (↥(GK K) → T₂.V)) ⊔ latticeCoboundaries T₂.L = latticeFiniteCocycles (P.PD K) T₂.L

def liftA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    ∃ J : Finset ℤ, J ⊆ Finset.Icc (-(h : ℤ)) (2 * h) ∧ (0 : ℤ) ∉ J ∧
      F.LiftF (P.PD K) (expLift l h J)

def killA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    ∃ s h' : ℕ, finrank ↥(K0 K) ↥K.1 * s = l - 1 ∧ 1 ≤ h' ∧ h' ≤ h + S + 1 ∧
      ∃ s₀ : Finset (↥(GK K) → T₂.V),
        s₀.card ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥(K0 K) ↥K.1 * (finrank ↥(K0 K) ↥K.1 + 1) * m ∧
        (s₀ : Set (↥(GK K) → T₂.V)) ⊆ latticeFiniteCocycles (P.PD K) T₂.L ∧
        ∀ p ∈ latticeFiniteCocycles (P.PD K) T₂.L,
          (l ^ YA l (finrank ↥(K0 K) ↥K.1) s h' S η : ℕ) • p ∈
            Submodule.span ↥(OL LL) (s₀ : Set (↥(GK K) → T₂.V)) ⊔ F.ImF (P.PD K)

theorem claimA_of_steps (hG : genA P K LL) (hL : liftA P K LL) (hK : killA P K LL) :
    claimA P K LL := by
  intro T₁ T₂ F r S η m h up b hH
  obtain ⟨s, hs, hgen⟩ := hG T₁ T₂ F r S η m h up b hH
  obtain ⟨J, hJ, h0, hlift⟩ := hL T₁ T₂ F r S η m h up b hH
  obtain ⟨σ, h', hes, hh', hle, s₀, hs₀, hsub, hkill⟩ := hK T₁ T₂ F r S η m h up b hH
  refine ⟨σ, h', s.card, J, hes, hh', hle, hJ, h0, hs, s, s₀, le_rfl, hgen, hs₀, hsub, hkill, ?_⟩
  intro p hp
  have hpZ : p ∈ latticeFiniteCocycles (P.PD K) T₂.L := (Submodule.span_le.mpr hsub) hp
  have h1 := hlift p hpZ
  have e1 : ((l ^ expLift l h J : ℕ) : ↥(OL LL)) =
      ((((P.PD K).p : ℕ) : ↥(OL LL))) ^ expLift l h J := by
    rw [P.PD_p K]; push_cast; rfl
  rw [← Nat.cast_smul_eq_nsmul ↥(OL LL), e1]
  exact h1

end Local

def genR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → genA (D.loc l) K LL

def liftR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → liftA (D.loc l) K LL

def killR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → killA (D.loc l) K LL

theorem local_form_of_three_inputs (D : D7) (hG : genR D) (hL : liftR D) (hK : killR D) : LocalTheoremAtGoodExtensions D :=
  fun l _ hl K LL hg =>
    claimA_of_steps (D.loc l) K LL (hG l hl K LL hg) (hL l hl K LL hg) (hK l hl K LL hg)

theorem local_theorem_of_three_inputs (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CA CB CK C : ℝ) (hC : 160 ≤ C)
    (hG : Adm1 D HW F Cm CA CB CK → genR D) (hL : Adm1 D HW F Cm CA CB CK → liftR D)
    (hK : Adm1 D HW F Cm CA CB CK → killR D) : IntegralityFromMetric D HW F Cm CA CB CK C :=
  fun hA => local_theorem_of_good_extensions D C hC (local_form_of_three_inputs D (hG hA) (hL hA) (hK hA))

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RestPt
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

structure RestPt {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop where

  ng0 : D.nd.l i ≠ D.host.g 0
  ng1 : D.nd.l i ≠ D.host.g 1

  good : GoodR D.nd i r

  chi1 : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw),
    Formalism.WeaklyAdmissibleFiltrations.IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)

  block : EmbeddingTypes.ambBlock i r ρ π

  chi : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ), 1 ≤ c → c ≤ D.R.t →
    Formalism.WeaklyAdmissibleFiltrations.IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c)))

  g3 : AbsIrreducibleDistinct D i r

  cont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))

  rho : IsRhoOf D.nd i π (ρ π)

  ss : IsSSRep (rhoChiK D i (ρ π))

  eps : TruncatedSeriesCountingIdentities.CyclotomicInertiaImage i

  shape : TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible i

end Formalism.MainNotions.N

end
end

