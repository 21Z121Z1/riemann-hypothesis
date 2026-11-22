import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0016
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
section
noncomputable section

open scoped InnerProductSpace
open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.MiS
open Formalism Formalism.IndefR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FreeSingleHomotopyEquivDiscreteChains

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def MidData (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (d : (R.toCx3 F).MIDat F.fc) : Prop :=
  (R.toCx3 F).MIUnit d ∧ (R.toCx3 F).MIid (F.eV (R.toCx3 F).zs) sEE d

def PtNZ (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop :=
  ∀ u, ∃ t, ∃ φ, ∃ v : Fin ((F.fc (R.toCx3 F).zs).Df1.nV t) → D.what₂.LL, (F.fc (R.toCx3 F).zs).Dc.Pt u t φ v ≠ 0

open scoped InnerProductSpace in

def PairZeroAt (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (d : (R.toCx3 F).MIDat F.fc)
    (u : (F.fc (R.toCx3 F).zs).Dc.Mem) : Prop :=
  ∀ t (φ : Fin ((F.fc (R.toCx3 F).zs).Dc.a u) → D.what₂.LL) (v : Fin ((F.fc (R.toCx3 F).zs).Df1.nV t) → D.what₂.LL),
    ⟪sEE (d.V ((R.toCx3 F).Θ t ((R.toCx3 F).jR t (F.eV (R.toCx3 F).zs t v)))),
      (F.fc (R.toCx3 F).zs).Sp.Pu u ((d.U u).mulVec (cpt A3.fam3.F.v0.embedding φ))⟫_ℂ = 0

def AltAt (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (d : (R.toCx3 F).MIDat F.fc) : Prop :=
  ∀ u, (∃ t, ∃ φ, ∃ v : Fin ((F.fc (R.toCx3 F).zs).Df1.nV t) → D.what₂.LL, (F.fc (R.toCx3 F).zs).Dc.Pt u t φ v ≠ 0) ∨
    PairZeroAt R F sEE d u

end FreeSingleHomotopyEquivDiscreteChains

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A)

def OpsUnit (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ) : Prop :=
  (∀ e ∈ X.EEl true, V e ∈ X.EEl true ∧ ‖V e‖ = ‖e‖) ∧
    ∀ u x, fnorm ((fc X.zs).Dc.Xc u Bs.v0) ((U u).mulVec x) = fnorm ((fc X.zs).Dc.Xc u Bs.v0) x

def IdBase (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH)
    (V : X.EE →ₗ[ℂ] X.EE) (a : (fc X.zs).Dc.Mem → ℂ)
    (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ) : Prop :=
  ∀ u (φ : Fin ((fc X.zs).Dc.a u) → K) (F : Fin ((fc X.zs).Df1.nV Bs.μ0) → K),
    Bs.v0.embedding ((fc X.zs).Dc.Pt u Bs.μ0 φ F) =
      a u * ⟪sEE (V (X.Θ Bs.μ0 (X.jR Bs.μ0 (eV Bs.μ0 F)))), (fc X.zs).Sp.Pu u ((U u).mulVec (cpt Bs.v0.embedding φ))⟫_ℂ

def IdTup (ζ : (fc X.zs).Dc.Mem → Bs.Tup → K) : Prop :=
  (∀ u, ζ u Bs.μ0 = 1) ∧ (∀ u t, ∃ n : ℕ, 0 < n ∧ ζ u t ^ n = 1) ∧ X.MatrixIdentityOffBase cr ζ

def CxTies (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) : Prop :=
  (fc X.zs).Df1.WF ∧ X.H2 cr true ∧ X.RATmu cr true ∧ X.JIsoR cv ∧ X.RatLev cr cv true ∧ X.DnLev cv true ∧
    X.UpLev cv true ∧ X.CoordinatesInGoodPart cr cv true ∧ X.EVTie cr cv eV

def datOf (V : X.EE →ₗ[ℂ] X.EE) (a : (fc X.zs).Dc.Mem → ℂ)
    (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ) (ζ : (fc X.zs).Dc.Mem → Bs.Tup → K) :
    X.MIDat fc :=
  ⟨V, a, U, fun u t => Bs.v0.embedding (ζ u t)⟩

variable {X cr cv}

end Gen

end GlobalTheory.MiS

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
section
noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2
namespace GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def On (S : Set ℝ) (Q : ∀ {D : D7} {X : HidaSetting D}, Full X → D.what₂.Word → Prop) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (_ : SIso D.s (sOf hF)) (u : D.what₂.Word),
      1 ≤ large₂.CGam → Ties D → LocalBesselAndTopKernel.FamilyMidVolume D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y →
      (Y.tO u u).AbsConv → Q Y u

def Led1 (Q : ∀ {D : D7} {X : HidaSetting D}, Full X → D.what₂.Word → Prop) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ thr : ℝ, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (_ : SIso D.s (sOf hF)) (u : D.what₂.Word),
      1 ≤ large₂.CGam → Ties D → LocalBesselAndTopKernel.FamilyMidVolume D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → DataNW D → ConcTie X Y →
      (Y.tO u u).AbsConv → Q Y u

def AmpAt (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cpr C C2 Ch δ : ℝ) : Prop :=
  UnitaryVolumeMass.stL2prod D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch ∧ UnitaryVolumeMass.stABSprod D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch ∧
    UnitaryVolumeMass.stDEC D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr C Ch δ

def AmpOn (S : Set ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C C2 Ch : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ Cpr δ : ℝ, 0 < δ → ∃ thr : ℝ,
    ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl → ∀ (D : D7) (large₂ : SizeData₂ D), 1 ≤ large₂.CGam → Ties D → LocalBesselAndTopKernel.FamilyMidVolume D →
      TFrameAt D → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 Cpr C C2 Ch δ

def CntAt (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 c3 cH cS c4 : ℝ) : Prop :=
  (∀ C, c3 ≤ C → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 C) ∧ UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH ∧
    UnitaryVolumeMass.stSW D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cS ∧ UnitaryVolumeMass.PartnerCountBound D large₂ u u C' Cl Cg cb Cu cT CT C0 1 c4

def CntOn (S : Set ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, ∃ c3 cH cS c4 thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word), CntAt D large₂ u C' Cl Cg cb Cu cT CT C0 c3 cH cS c4

def CountBoundOn (S : Set ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, ∃ c3 cH thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word),
      (∀ C, c3 ≤ C → UnitaryVolumeMass.MeanFlagPairCount D large₂ u u C' Cl Cg cb Cu cT CT C0 1 3 C) ∧ UnitaryVolumeMass.stHH D large₂ u u C' Cl Cg cb Cu cT CT C0 1 cH

def SmallAt (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 δ : ℝ) : Prop :=
  UnitaryVolumeMass.stWeyl D ∧ VanishingOnXAndXPlus.PlaneWaveIsometry D large₂ C' Cl Cg cb Cu cT CT C0 ∧ UnitaryVolumeMass.stTprod D large₂ C' Cl Cg cb Cu cT CT C0 δ ∧
    UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 ∧ (Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt D u)

def SmallOn (S : Set ℝ) : Prop :=
  ∀ Cg cb Cu cT CT δ : ℝ, 0 < cb → 0 < cT → 0 < δ → ∃ thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), Ties D → LocalBesselAndTopKernel.FamilyMidVolume D → SmallAt D large₂ C' Cl Cg cb Cu cT CT C0 δ

def TieAt {D : D7} {X : HidaSetting D} {Y : Full X} (hF : FinX Y) (hI : SIso D.s (sOf hF)) (large₂ : SizeData₂ D) (u : D.what₂.Word)
    (T : TermTie D) (Z : LoopTie D large₂ T u u 1) : Prop :=
  Formalism.L2.SG.LoopTieOf.JtPin hF hI T ∧ Formalism.L2.SG.LoopTieOf.WRowPin hF hI T ∧ Formalism.L2.SG.LoopTieOf.FibreCount Y ∧
    BridgeLemma.TermPtsTie T Z ∧ @BridgeLemma.LatticeDeterminantFactorization D T u u ∧ BridgeLemma₂.wordPairEntriesInLattice T u u ∧ BridgeLemma₂.wordPairTermInjective T Z

def TieOn (S : Set ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, ∃ cV thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (u : D.what₂.Word),
      Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y →
      ∃ (T : TermTie D) (Z : LoopTie D large₂ T u u 1), TieAt hF hI large₂ u T Z ∧
        UnitaryVolumeMass.stVol D large₂ T u u 1 Z C' Cl Cg cb Cu cT CT C0 1 cV

def RowsPtAt {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) : Prop :=
  (Y.tO u u).RowBig (epsL D) (ddC X Y u u) ∧ (Y.tO u u).RowNotScalar (epsL D) (ddC X Y u u)

def RowsPt : Prop :=
  ∀ Cg cb Cu cT CT C0 CG : ℝ, 0 < cb → 0 < cT → 1 ≤ CG → ∃ thr : ℝ, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (_ : SIso D.s (sOf hF)) (u : D.what₂.Word),
      large₂.CGam = CG → Ties D → LocalBesselAndTopKernel.FamilyMidVolume D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y →
      (Y.tO u u).AbsConv → RowsPtAt Y u
end GlobalTheory.Core.Deg
end
end

