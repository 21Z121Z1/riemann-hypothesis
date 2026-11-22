import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ParBoundW (D : D7) : Prop := ForStage D fun c _ s => ∀ (u : s.CC c) B, IsPar u B →
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B s.V.rank ((s.V.rank : ℝ) / 2)

def ChainLW (D : D7) : Prop := ∀ c : Com D, c.Is → ∀ B : GlobalTheory.LFun.Fam D.host.E,
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) →
  ∀ k < D.R.m, LNe c (c.chT (k + 1)) (chainPar c B k)

def Com.eps {D : D7} (c : Com D) (k : ℕ) : (AE D)ˣ →* Circle := if Odd k then c.η⁻¹ else 1

def ChainUp (D : D7) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → ∀ c : Com D, c.Is → ∀ s₀ : PiLocalization₂ D, s₀.Is c 0 →
    ∀ k ≤ D.R.m, ∀ (s : PiLocalization₂ D) (Θ : s.CC c →ₗ[ℂ] s₀.CC c), Reach c s₀ k s Θ → s.Is c k ∧
      ∀ ipD₀ ip₀ ipD ip, IsMet c s₀ ipD₀ ip₀ → IsMet c s ipD ip → ∀ (u : s₀.CC c) B, IsPar u B →
        ∃ x : s.CC c, (∀ y, ip y x = ip₀ (Θ y) u) ∧ IsPar x (chainPar c B k)

example {D : D7} (c : Com D) : c.eps 0 = 1 := by simp [Com.eps]

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
section
noncomputable section

namespace GlobalTheory.Core.Rk.Exh

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Classical in

def under (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Finset (FinPl D) := Z.image fun PP => PP.under (𝓞 D.host.F)

def prinDat (A : HSp D) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Formalism.L2.DIV.LevDat D.host.E ℂ A.rank :=
  Formalism.IndefR.Lev.datW A.rank Z (Formalism.L2.DIV.LevelP.triv _ _ _) Formalism.IndefR.Lev.Frm.B

def prin (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Subgroup (GA D A) :=
  Formalism.IndefR.Lev.levG A β (prinDat A Z)

def prinInf (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Set (GA D A) :=
  {g | Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.lev D.sp.cm A.gram β (prinDat A Z)}

def NoLift (ψ : AddChar (AF D.host.F) ℂ) {A W : HSp D} (om : WRep A W) (m : Measure (GA D A)) (u : GA D A → ℂ) : Prop :=
  ∀ f, IsThetaFunO ψ A W f → ∀ h, up om m f u h = 0

def Kills (ψ : AddChar (AF D.host.F) ℂ) {A W : HSp D} (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W) (m : Measure (GA D A))
    (u : GA D A → ℂ) : Prop :=
  ∀ φ, IsThetaFunO ψ (dblSp A) W φ → ∀ h,
    Eis.dblInt A χ⁻¹ m (fun g => thetaKO omh g h φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0

structure Defin (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) : Prop where
  inf : IsInfFam θ
  sig : HSpace.SigOK A
  pos : HSpace.IsPosDef A
  cart : IsCartanFrame A cA
  one : ∀ τ, IsCartanInv (gramAt D A τ) 1
  cA_eq : ∀ τ, cA τ * (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) = Formalism.UG.Jpq (A.sig (tauE D τ)).1 (A.sig (tauE D τ)).2 * cA τ
  maj : IsMaj A a
  maj_eq : ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * 1) * compAt θ τ a.1 = 1

structure Places (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop where
  frame : Formalism.L2.DIV.IsFrame β (frameLat A)
  idem : ∃ e : AE D, IsIdemSum e Z
  two : ∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v

structure Form (θ : InfFam D) (A : HSp D) (cA : CptF A) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D))
    (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (χW : (AE D)ˣ →* Circle) (r t : ℕ) (u : GA D A → ℂ) (par : LFun.Fam D.host.E) : Prop where
  mem : u ∈ A0 θ A cA
  fix : ∀ κ ∈ prin A β Z, ∀ g, u (g * κ) = u g
  param : LFun.IsParamFun D.sp.cm.sig A.gram (frameLat A) (under Z : Set (FinPl D)) u par
  unr : LFun.UnrOff χW (under Z : Set (FinPl D))
  str : ∃ c, GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (under Z : Set (FinPl D)) r t c par (LFun.val (F := D.host.F) χW) (LFun.val (F := D.host.F) χW)

structure Occ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {A W : HSp D} (sW : RealMat W) (om : WRep A W) (m : Measure (GA D A))
    (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (u : GA D A → ℂ) (Φ : WO A W → ℂ) : Prop where
  cart : ∀ τ, IsCartanInv (gramAt D W τ) (sW τ)
  fock : IsFockVec ψ θ A W (fun _ => 1) sW Φ
  sph : IsSphOff ψ A W (frameLat A) (frameLat W) (under Z) Φ
  fix : ∀ κ ∈ prin A β Z, om (κ, 1) Φ = Φ
  real : ∀ ν 𝓕, IsCovolOne (ratL W A) ν 𝓕 → ∀ mR : Measure (GinfC A), mR.IsHaarMeasure →
    ∫ b : GinfC A, wcoef om ν 𝓕 Φ Φ b * rcoef m u u b ∂mR ≠ 0

def DownNe (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A W : HSp D) (t : ℕ) (χA χW : (AE D)ˣ →* Circle) (om : WRep A W)
    (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E))
    (m : Measure (GA D A)) (u : GA D A → ℂ) (par : LFun.Fam D.host.E) (sW : RealMat W) (Φ : WO A W → ℂ),
    Defin θ A cA a → HSpace.SigOK W → 0 < W.rank → A.rank = W.rank + t → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) →
    IsWeilDatumO ψ A W χA χW om → Places A β Z → m.IsHaarMeasure → Form θ A cA β Z χW W.rank t u par →
    Occ ψ θ sW om m β Z u Φ → ¬ NoLift ψ om m u

example (ψ : AddChar (AF D.host.F) ℂ) {A W : HSp D} (om : WRep A W) (m : Measure (GA D A)) : NoLift ψ om m 0 := by
  intro f _ h
  simp [up, AutomorphicL2Unitary.descend]

end GlobalTheory.Core.Rk.Exh

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SiegelWeilFock
section
noncomputable section

namespace GlobalTheory.Core.Rk.IP

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SiegelWeilFock (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → A.rank < B.rank →
    (wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank) →
  ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a →
  ∀ (θ : InfFam D) (sS : RealMat (dblSp A)) (sB : RealMat B), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) →
    (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
      sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ mH : Measure (GA D B), mH.IsHaarMeasure →
  ∀ φ : WO (dblSp A) B → ℂ, IsFockVec ψ θ (dblSp A) B sS sB φ →
    (∀ g, Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧
    Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 φ) (sZero A B)) (sZero A B) (ThetaMean.thetaMean omh mH φ)

end GlobalTheory.Core.Rk.IP

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section OfTower

variable (W : GlobalTheory.Core.Rk.Tower D)

def comOf : Com D := ⟨W.θ, W.ψ, W.toLevCh.mu (), W.eta, W.Pg, W.triv, W.chi⟩

def stageY (j : ℕ) : PiLocalization₂ D :=
  ⟨Yc D j, parB (Ptw D) (min j D.R.m), W.MY j, W.ΛY j, W.βY j, W.datYt () j W.triv, W.νY j, W.fdY j⟩

def stageX : PiLocalization₂ D := ⟨D.sp.X', parB (Ptw D) D.R.m, W.MX, W.ΛX, W.βX, W.datXt (), W.νX, W.fdX⟩

def stepY (k : ℕ) : Step (comOf W) (stageY W k) (stageY W (k + 1)) := ⟨W.ωY k, W.vY k, W.ItY k, W.ioY k⟩

def stepX : Step (comOf W) (stageY W (D.R.m - 1)) (stageX W) := ⟨W.ωX, W.vX, W.ItX, W.ioX⟩

def TowerIsChain : Prop :=
  (comOf W).Is ∧ (∀ j < D.R.m, (stageY W j).Is (comOf W) j) ∧ (stageX W).Is (comOf W) D.R.m ∧
    (∀ k, k + 1 < D.R.m → (stepY W k).Is (k + 1)) ∧ (stepX W).Is D.R.m

end OfTower

def PiLocalization₂.InFlag (s : PiLocalization₂ D) (κ : GA D s.V) : Prop :=
  κ ∈ GfC s.V ∧ Lev.finE s.V κ ∈ Formalism.L2.DIV.parLev D.sp.cm s.V.gram s.β s.L

def PiLocalization₂.ch (s : PiLocalization₂ D) (κ : GA D s.V) : ℂ := Lev.levChi s.V s.β (Lev.flagL s.L) κ

def Moved {c : Com D} {s : PiLocalization₂ D} (κ : GA D s.V) (y y' : s.CC c) : Prop :=
  ∀ w g, PiLocalization₂.val y' w g = (s.ch κ)⁻¹ * PiLocalization₂.val y w (g * κ)

def SameBlock (s s' : PiLocalization₂ D) (κ : GA D s.V) (κ' : GA D s'.V) : Prop :=
  HEq (Formalism.L2.DIV.rTup s.β s.L (Lev.finE s.V κ)) (Formalism.L2.DIV.rTup s'.β s'.L (Lev.finE s'.V κ'))

def PairLaw (D : D7) : Prop := ForStep D fun c _ s s' p => c.P.H = ⊥ → ∀ κ κ', s.InFlag κ → s'.InFlag κ' → SameBlock s s' κ κ' →
  ∀ φ, p.ω (κ, κ') (p.pt φ) = (s.ch κ * (s'.ch κ')⁻¹) • p.pt φ

def StepEqv (D : D7) : Prop := ForStep D fun c _ s s' p => c.P.H = ⊥ → ∀ κ κ', s.InFlag κ → s'.InFlag κ' → SameBlock s s' κ κ' →
  ∀ y y' : s'.CC c, Moved κ' y y' → Moved κ (p.io y) (p.io y')

def ActCC (D : D7) : Prop := ForStage D fun c _ s => c.P.H = ⊥ →
  (∀ κ, s.InFlag κ → ∀ y : s.CC c, ∃ y', Moved κ y y') ∧ Lev.LiftsExist s.V s.β s.L

example (s : PiLocalization₂ D) (κ : GA D s.V) : SameBlock s s κ κ := HEq.rfl

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.FinZeta (Gv embV VacFin)
open GlobalTheory.AdelicU (frameLat)

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TransferOn (D : D7) (C : HeightOneSpectrum (𝓞 D.host.F) → Prop) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t →
  ∀ v, C v → (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χS w' ∧ GlobalTheory.LFun.UnrAt χT w') →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (U : Submodule ℂ (WO S T → ℂ))
    (hU : ∀ a a', ∀ u ∈ U, om (embV S v a, embV T v a') u ∈ U) (f : U), VacFin ψ S T v f →
  ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gv S v) X) (x : X) (B : Multiset ℂˣ),
    GlobalTheory.LFun.IsParamVec D.sp.cm.sig S.gram (frameLat S) h ρ x B →
  ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (Gv T v) X') (b : U →ₗ[ℂ] X →ₗ[ℂ] X'),
    (∀ a a' (u : U) y, b ⟨om (embV S v a, embV T v a') u, hU a a' u u.2⟩ (ρ a y) = ρ' a' (b u y)) → b f x ≠ 0 →
    GlobalTheory.LFun.IsParamVec D.sp.cm.sig T.gram (frameLat T) h ρ' (b f x) (stepPar χS χT t (fun _ => B) w)

def CosetSym {G : Type} [Group G] (K : Subgroup G) : Prop :=
  ∀ g : G, Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * g : G) : G ⧸ K)} = Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * g⁻¹ : G) : G ⧸ K)}

theorem TransferOn.mono {D : D7} {C C' : HeightOneSpectrum (𝓞 D.host.F) → Prop} (h : TransferOn D C) (hC : ∀ v, C' v → C v) :
    TransferOn D C' := fun ψ S T χS χT om hW t ht v hv => h ψ S T χS χT om hW t ht v (hC v hv)

example {G : Type} [Group G] : CosetSym (⊤ : Subgroup G) := fun g => by
  have e : ∀ g : G, Nat.card {c : G ⧸ (⊤ : Subgroup G) // ∃ k ∈ (⊤ : Subgroup G), c = ((k * g : G) : G ⧸ (⊤ : Subgroup G))} = 1 := fun g => by
    haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
    exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨⟨_, 1, trivial, rfl⟩⟩⟩
  rw [e, e]

end GlobalTheory.ChainOnto

end
end

