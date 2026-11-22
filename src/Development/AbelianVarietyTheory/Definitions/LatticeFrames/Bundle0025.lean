import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
section
noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2
namespace GlobalTheory.Core.Diag

def RowNGEq : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ C4 : ℝ, 0 ≤ C4 ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.MainNotions.S.Cnt.Stand D u u → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).RowNG (epsNG D large₂ C4) (ddC X Y u u)

def RowMainEq : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, 0 < cb → 0 < cT → ∃ CB : ℝ, 0 ≤ CB ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).RowMain (gamB D large₂ CB) (ddC X Y u u)

def RowLoopEq : Prop :=
  ∀ Cg cb Cw cT CT C0 A CG : ℝ, 0 < cb → 0 < cT → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (_ : SIso D.s (sOf hF)) (u : D.what₂.Word),
      Formalism.BasicNotions.Ties D → Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D → large₂.CGam = CG →
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).RowBig (epsL D) (ddC X Y u u) ∧ (Y.tO u u).RowNotScalar (epsL D) (ddC X Y u u)

def RowKppEq : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv →
      Summable ((Y.tO u u).degSet.indicator (fun t => ‖(Y.tO u u).op t‖)) ∧
      Formalism.L2.SG.RowsOther.KppDiag (Y.tO u u) (duC X Y u) D.R.k D.R.f

def RowDiagEq : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, 0 < cb → 0 < cT → ∃ CG₀ : ℝ, ∀ CG : ℝ, CG₀ ≤ CG →
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (_ : SIso D.s (sOf hF)) (u : D.what₂.Word),
      Formalism.BasicNotions.Ties D → Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D →
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoParameterConditions D large₂ Cl Cg CT →
      ConcTie X Y → (Y.tO u u).AbsConv → large₂.CGam = CG →
      Formalism.L2.SG.RowsOther.DiagRow (Y.tO u u) (oneC X Y u) (D.mem u).A.GamP (ddC X Y u u)

def TrueS (D : D7) : Prop :=
  Formalism.BasicNotions.Ties D ∧ Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D ∧ Formalism.L2.SG.Pf.LocCP.LocTied D ∧ Nonempty (Formalism.L2.SG.SpectralTiesReal.STies D)

def TFrameP : Prop :=
  ∀ Cg cb Cu cT CT C0 CG : ℝ, 0 < cb → 0 < cT → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), Formalism.BasicNotions.Ties D → Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D → large₂.CGam = CG →
      Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1 → AdmissibleBoundsFromSource.hyp D large₂ C0 C' Cl Cg cb Cu cT CT → TFrameAt D

def e0 (D : D7) (C0 : ℝ) : ℝ := 2 * C0 / AdmissibleBoundsFromSource.Gam D + 2 * AdmissibleBoundsFromSource.xK D

def AtLed (Q : D7 → ℝ → Prop) : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CG₀ : ℝ, ∀ CG : ℝ, CG₀ ≤ CG →
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), TrueS D → TFrameAt D → large₂.CGam = CG → AdmissibleBoundsFromSource.hyp D large₂ C0 C' Cl Cg cb Cu cT CT → Q D C0

def ClausesLed : Prop := AtLed fun D _ => Formalism.L2.SG.ThmSOwn.ClKppDiag D ∧ Formalism.L2.SG.ThmSOwn.ClDiag D

def DiagLed : Prop := AtLed fun D C0 => ∀ u, GlobalTheory.Core.Rk.DiagS D u (e0 D C0)

def HasLed (D : D7) (L CG : ℝ) : Prop := ∃ large₂ : SizeData₂ D, large₂.sc.L = L ∧ large₂.CGam = CG

def DiagAtScale : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, 0 < cb → 0 < cT → 1 ≤ C0 → ∃ CG₀ : ℝ, ∀ CG : ℝ, CG₀ ≤ CG →
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ), TrueS D → TFrameAt D → HasLed D L CG → GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT → StandingNumericalData D C0 →
      ∀ u, GlobalTheory.Core.Rk.DiagS D u (e0 D C0)

def HD (D : D7) (L C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT ∧ GlobalTheory.Core.Deg.DataNW D ∧ TFrameAt D

def gamL (D : D7) (L C : ℝ) : ℝ := Real.exp (C * (D.R.m : ℝ) ^ 5 * D.R.f * L)

def SDiagAt (D : D7) (u : D.what₂.Word) (Γ c : ℝ) : Prop :=
  GlobalTheory.Core.Rk.hsDev D u ≤
    4 * ((Γ + 1) * (D.duS u : ℝ) ^ 2 / D.what₂.Dstar + (D.duS u : ℝ) * Real.exp (-(c * D.R.k * D.R.f * Real.log D.R.k))) +
      2 * (D.duS u : ℝ) * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))

def SDiag (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ), TrueS D → HD D L C' Cl Cg cb Cu cT CT → ∀ u, SDiagAt D u (gamL D L CD) c

def SDiagLed (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), TrueS D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → GlobalTheory.Core.Deg.DataNW D → TFrameAt D →
      ∀ u, SDiagAt D u (gamL D large₂.sc.L CD) c

def SDiagWin (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), TrueS D → Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → TFrameAt D →
      ∀ u, SDiagAt D u (gamL D large₂.sc.L CD) c

def SDiagHas (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ), TrueS D → (∃ large₂ : SizeData₂ D, large₂.sc.L = L) → 8 * Real.log (AdmissibleBoundsFromSource.Gam D) ≤ D.R.k →
      HD D L C' Cl Cg cb Cu cT CT → ∀ u, SDiagAt D u (gamL D L CD) c

def OneLed (gen : Bool) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C : ℝ, 0 ≤ C ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → GlobalTheory.Core.Deg.DataNW D → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).pairSum ((Y.tO u u).one (if gen then (Y.tO u u).genSet else (Y.tO u u).ngSet)) ≤
        gamL D large₂.sc.L C * ddC X Y u u
end GlobalTheory.Core.Diag
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod.PinModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nonempty_frame (k : Type) [Field k] {N : ℕ} (Y : Type) [Fintype Y] [DecidableEq Y] (h : Fintype.card Y = N) :
    Nonempty (GlobalTheory.LocMod.Frame k N Y) :=
  let e := Fintype.equivFinOfCardEq h
  ⟨⟨(1 : Matrix (Fin N) (Fin N) k).submatrix id e, (1 : Matrix (Fin N) (Fin N) k).submatrix e id,
    by rw [submatrix_mul_equiv]; simp, by rw [← submatrix_mul (he₂ := Function.bijective_id)]; simp⟩⟩

theorem exists_dbl (p : Place D k) {σ : ℕ} (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (n₀ n₁ n₂ : Type)
    [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] {s : k} (hs : s ≠ 0)
    (F₀ : GlobalTheory.LocMod.Frame k B.A.rank n₀) (F₁ : GlobalTheory.LocMod.Frame k J.W₀.rank n₁) (F₂ : GlobalTheory.LocMod.Frame k B'.A.rank n₂) :
    ∃ F : Dbl p B J B' n₀ n₁ n₂ (2 * σ), F.s = s ∧ F.F₀ = F₀ ∧ F.F₁ = F₁ ∧ F.F₂ = F₂ := by
  obtain ⟨G₀, h₀⟩ := Witness.exists_bes p B hs F₀
  obtain ⟨G₁, h₁⟩ := Witness.exists_jac p J hs (Witness.hz_ne p B) F₁
  obtain ⟨G₂, h₂⟩ := Witness.exists_bes p B' (mul_ne_zero hs (Witness.xi_ne p)) F₂
  exact ⟨⟨s, hs, F₀, F₁, F₂, G₀, G₁, G₂, h₀, h₁, h₂⟩, rfl, rfl, rfl, rfl⟩

theorem Dbl_c (p : Place D k) {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} {n₀ n₁ n₂ : Type}
    [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] {c : ℕ}
    (F : Dbl p B J B' n₀ n₁ n₂ c) : c = 2 * σ := by have := F.bes'.1; omega

theorem exists_dbl_closed (D : D7) : ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k)
    (_ : IsNonarchimedeanLocalField k) (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (B : BesLev D 1) (J : JacLev D 1) (B' : BesLev D 0),
    Nonempty (StepBF ψ B J) ∧ Nonempty (StepFB (σ := 0) ψ J B') ∧ Nonempty (Link B B'.L B'.ζ) ∧
      Nonempty (Dbl (σ := 0) p B J B' Unit Unit Unit 0) := by
  obtain ⟨v, ⟨p⟩⟩ := Witness.nonempty_place D
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  obtain ⟨ψ, hψ⟩ := (Inhab.exists_chain D).1
  let B : BesLev D 1 := Inhab.besPlane (GlobalTheory.RegSW.Model.hypFour D) (Inhab.cmHost_imaginaryGenerator_ne_zero D)
  let J : JacLev D 1 := Inhab.jacLine (hypDecThree D)
  let B' : BesLev D 0 := Inhab.besPlane (Inhab.hypRefl (Inhab.plane D)) one_ne_zero
  have e : D.host.xi0⁻¹ • B.ζ = B'.ζ := funext fun _ => inv_mul_cancel₀ (Inhab.cmHost_imaginaryGenerator_ne_zero D)
  have l : Link B B.L B'.ζ := e ▸ Inhab.selfLink B
  obtain ⟨F⟩ := nonempty_frame (v.adicCompletion D.host.F) (N := 1) Unit (by simp)
  obtain ⟨G, -⟩ := exists_dbl (σ := 0) p B J B' Unit Unit Unit one_ne_zero F F F
  exact ⟨_, _, _, _, _, p, ψ, B, J, B', Inhab.nonempty_stepBF hψ B J, Inhab.nonempty_stepFB hψ J B', ⟨l⟩, ⟨G⟩⟩

variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem exists_isOne : ∃ Φ : SB (Matrix Y Y' k), IsOne Φ ∧ Φ.1 0 = 1 := by
  refine ⟨⟨Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1, mem_SB_of_periodic (fun x hx => ?_) fun x y hy => ?_⟩, rfl, ?_⟩
  · exact (Set.mem_of_indicator_ne_zero hx)
  · have : (∀ r q, (x + y) r q ∈ 𝒪[k]) ↔ ∀ r q, x r q ∈ 𝒪[k] :=
      ⟨fun h r q => by simpa using sub_mem (h r q) (hy.intM r q), fun h r q => add_mem (h r q) (hy.intM r q)⟩
    by_cases hx : ∀ r q, x r q ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (by exact this.2 hx), Set.indicator_of_mem (by exact hx)]
    · rw [Set.indicator_of_notMem (by exact fun h => hx (this.1 h)), Set.indicator_of_notMem (by exact hx)]
  · simp

theorem isCombAt_one (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (FS : GlobalTheory.LocMod.Frame k S.rank Y')
    (FT : GlobalTheory.LocMod.Frame k T.rank Y) :
    p.IsCombAt ψ FS FT (Finsupp.single 0 1) (Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) := by
  refine ⟨fun u hu => ?_, fun Tm _ Φ₀ Φ h₀ h => ?_⟩
  · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
    subst hu; intro i j; simp
  · obtain rfl : Φ = Φ₀ := Subtype.ext (h.trans h₀.symm)
    funext w
    simp [comb, Finsupp.support_single_ne_zero, heisO, symplOH, symplO, hO]

theorem toEAf_surj (D : D7) : Function.Surjective (toEAf D) := by
  refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
  exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id

theorem pi_congr (p : Place D k) {a b : Formalism.L2.Theta.AE D} (h : toEAf D a = toEAf D b) : p.π a = p.π b := by
  have h1 : finPart D a = finPart D b := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h
  have h2 : p.e * a = p.e * b := GlobalTheory.SplitScalar.adele_ext (by rw [map_mul, map_mul, GlobalTheory.SplitScalar.infPart_splitIdem p.split, zero_mul, zero_mul])
    (by rw [map_mul, map_mul, h1])
  rw [← p.π_ι (p.π a), p.ι_π, h2, ← p.ι_π, p.π_ι]

theorem exists_movedTo (p : Place D k) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {M M' : Matrix (Fin V.rank) (Fin V.rank) k}
    (hM : M * M' = 1) : ∃ g, SuppAt p.e V g ∧ MovedTo p V g β M := by
  choose f hf using toEAf_surj D
  have key : ∀ b : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D), b.map (toEAf D) = β.val →
      ((β⁻¹).val.map f).map p.π * b.map p.π = 1 := fun b hb => by
    have e : ((β⁻¹).val.map f * b).map (toEAf D) = (1 : Matrix _ _ (Formalism.L2.Theta.AE D)).map (toEAf D) := by
      rw [Matrix.map_mul, hb, show ((β⁻¹).val.map f).map (toEAf D) = (β⁻¹).val from by ext i j; exact hf _, Units.inv_mul,
        Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← Matrix.map_mul, ← Matrix.map_one p.π (map_zero _) (map_one _)]
    ext i j
    exact pi_congr p (congrFun (congrFun e i) j)
  have k0 := key (β.val.map f) (by ext i j; exact hf _)
  have h1 : M * ((β⁻¹).val.map f).map p.π * ((β.val.map f).map p.π * M') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ M', k0, Matrix.one_mul, hM]
  obtain ⟨g, hg, hg'⟩ := Witness.exists_isLoc p (S := V) (Frame.ofGL 1) ⟨_, _, h1, mul_eq_one_comm.1 h1⟩
  refine ⟨g, hg, fun b hb => ?_⟩
  rw [Matrix.map_mul, hg']
  simp only [Frame.ofGL, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mul_assoc, key b hb, Matrix.mul_one]

theorem movedTo_unique (p : Place D k) (V : HSp D) (g : GA D V) (β : GL (Fin V.rank) (Lev.EAf D))
    {M M' : Matrix (Fin V.rank) (Fin V.rank) k} (h : MovedTo p V g β M) (h' : MovedTo p V g β M') : M = M' := by
  choose f hf using toEAf_surj D
  have e : (β.val.map f).map (toEAf D) = β.val := by ext i j; exact hf _
  exact (h _ e).symm.trans (h' _ e)

theorem exists_ord (κ l τ j N : ℕ) (h : Fintype.card (Ix (Fin κ ⊕ Fin l) (Fin τ) j) = N) :
    ∃ e : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin N, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e := by
  have h' : κ + l + j * τ = N := by simpa using h
  refine ⟨((finSumFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv).trans (finCongr h'), ?_⟩
  rintro ((i | i) | ⟨a, b⟩) <;> simp [GlobalTheory.SymBridge.zPos]
  ring

variable {u : D.what₂.Word}

theorem exists_gAt (d : Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E)
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (unitVol : IsUnitVol ν) (q : GlobalTheory.FinPl.SplitPt D k)
    (idem : Formalism.L2.NTheta.IsIdemAt q.e PP) (unit : q.UnitAA) (s : ℕ) (hs : s + 1 + 1 = D.R.m) (S : SymData k s D.R.k)
    (char : (ofSplit q).IsChar d.c.ψ S.ψ) (mu : ∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit q).IsComp (d.c.chS j)⁻¹ (S.μ j))
    (FX : ∀ j, j ≤ s + 1 → GlobalTheory.LocMod.Frame k (D.sp.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j))
    (FT : GlobalTheory.LocMod.Frame k D.sp.X'.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2)))
    (FM : GlobalTheory.LocMod.Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit))
    (c : k) (hc : valuation k c = 1) (hxi : valuation k (ofSplit q).xi = 1)
    (hz_unit : ∀ j ρ h, valuation k ((ofSplit q).hz (d.B j ρ h)) = 1) (z₀ : Fin d.Lz.rank → k)
    (last : FM.β = fromCols ((d.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
      (Matrix.of fun r _ => ((d.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r))
    (tau : ∀ h, (τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * c)) • fun i => (ofSplit q).pr ((d.bes s 0 h).ζ i))
    (latX : ∀ j hj (y : XIx (Fin D.R.k) (Fin D.R.t) j → k), (∀ i, y i ∈ 𝒪[k]) ↔
      (fun i => q.sec (((FX j hj).β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X j) (d.x j).L (· = q.v))
    (latM : ∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k, (∀ i, y i ∈ 𝒪[k]) ↔
      (fun i => q.sec ((FM.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X (s + 1 + 1)) (d.x (s + 1 + 1)).L (· = q.v))
    (frameTop : ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin D.sp.X'.rank,
      GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) D.sp.X' 1 d.top.β (FT.β.submatrix id e.symm))
    (cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ)
    (cg_mid : ∀ j c (H : j + 1 + c = s), (ofSplit q).IsCombAt d.c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j)
      ((S.T (Fin D.R.t)).entry S.ψ ν j c H 1 1))
    (cg_pen : (ofSplit q).IsCombAt d.c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s)
      fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t)))
    (cg_top : (ofSplit q).IsCombAt d.c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1))
      ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))) :
    ∃ t' : ∀ j, GA D (d.st j).V, (∀ j, SuppAt q.e _ (t' j)) ∧ Nonempty (GAt { d with t := t' } τ PP) := by
  set p := ofSplit q with hp
  have hx : p.xi ≠ 0 := Witness.xi_ne p
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  let sc : ℕ → k := fun j => c * p.xi ^ (j / 2) / p.xi ^ (s / 2)
  have sc0 : ∀ j, sc j ≠ 0 := fun j => div_ne_zero (mul_ne_zero hc0 (pow_ne_zero _ hx)) (pow_ne_zero _ hx)
  have hodd := S.odd
  let Q : ∀ j c, j + c = s + 1 → GlobalTheory.LocMod.Frame k (d.st j).V.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) → Prop := fun j =>
    match j with
    | 0 => fun _ _ _ => True
    | j + 1 => fun c hc F => ∀ ρ h, p.IsJacFrame ((d.jac j ρ h).lev (d.x (j + 1)).vol) (sc j) (p.hz (d.B j ρ h)) (FX (j + 1) (by omega)) F
  have hFY : ∀ j c (hc : j + c = s + 1), ∃ F : GlobalTheory.LocMod.Frame k (d.st j).V.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c),
      (∀ ρ h, p.IsBesFrame (d.B j ρ h) (sc j) (FX j (by omega)) F) ∧ Q j c hc F := by
    intro j c hc
    by_cases hj : j % 2 = 0
    · obtain ⟨ρ, rfl⟩ : ∃ ρ, c = 2 * ρ + 1 := ⟨c / 2, by omega⟩
      have h : j + 2 * ρ + 2 = D.R.m := by omega
      obtain ⟨F, hF⟩ := Witness.exists_bes p (d.B j ρ h) (sc0 j) (FX j (by omega))
      refine ⟨F, fun ρ' h' => ?_, ?_⟩
      · obtain rfl : ρ' = ρ := by omega
        exact hF
      · cases j with
        | zero => trivial
        | succ j => intro ρ' h'; omega
    · obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      obtain ⟨ρ, rfl⟩ : ∃ ρ, c = 2 * ρ := ⟨c / 2, by omega⟩
      have h : j + 2 * ρ + 2 = D.R.m := by omega
      obtain ⟨F, hF⟩ := Witness.exists_jac p ((d.jac j ρ h).lev (d.x (j + 1)).vol) (sc0 j) (Witness.hz_ne p (d.B j ρ h))
        (FX (j + 1) (by omega))
      refine ⟨F, fun ρ' h' => by omega, fun ρ' h' => ?_⟩
      obtain rfl : ρ' = ρ := by omega
      exact hF
  choose FY hB hJ using hFY
  have ht : ∀ j, ∃ g : GA D (d.st j).V, SuppAt q.e _ g ∧ ∀ c (hc : j + c = s + 1),
      ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) j ≃ Fin (d.st j).V.rank,
      GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo p (d.st j).V g (d.st j).β
        (((FY j c hc).β * ((S.T (Fin D.R.t)).bas j c hc).val).submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
    intro j
    by_cases hj : j ≤ s + 1
    · obtain ⟨c, hc⟩ : ∃ c, j + c = s + 1 := ⟨s + 1 - j, by omega⟩
      obtain ⟨e, he⟩ := exists_ord D.R.k (s + 1) D.R.t j (d.st j).V.rank
        ((Fintype.card_congr (stdOrd _ _ j c hc)).trans (Witness.card_frame (FY j c hc)).symm)
      obtain ⟨g, hg, hg'⟩ := exists_movedTo p (d.st j).V (d.st j).β
        (M := ((FY j c hc).β * ((S.T (Fin D.R.t)).bas j c hc).val).submatrix id (e.symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) j c hc)))
        (M' := ((((S.T (Fin D.R.t)).bas j c hc)⁻¹).val * (FY j c hc).γ).submatrix (e.symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) j c hc)) id)
        (by rw [submatrix_mul_equiv, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (FY j c hc).γ, Units.mul_inv, Matrix.one_mul, (FY j c hc).βγ]; rfl)
      refine ⟨g, hg, fun c' hc' => ?_⟩
      obtain rfl : c' = c := by omega
      exact ⟨e, he, hg'⟩
    · exact ⟨1, fun i j => by simp [Formalism.L2.Theta.mt], fun c hc => by omega⟩
  choose t' ht1 ht2 using ht
  refine ⟨t', ht1, ⟨⟨k, ν, unitVol, q, idem, unit, s, hs, S, char, mu, FX, FT, FM, FY, sc, fun j => ?_, fun j => ?_, hz_unit,
    fun j ρ h c hc => hB j c hc ρ h, fun j ρ h c hc => hJ (j + 1) c hc ρ h, z₀, last, fun h => ?_, latX, latM, ht2, frameTop, cg,
    cg_mid, cg_pen, cg_top⟩⟩⟩
  · simp [sc, hc, hxi]
  · simp only [sc]
    rw [show (j + 1 + 1) / 2 = j / 2 + 1 by omega, pow_succ, ← hp]
    ring
  · have : sc s = c := by simp only [sc]; field_simp
    rw [this]; exact tau h

end GlobalTheory.LocMod.PinModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsSumFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.DblInh

variable {D : D7}

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def conjHom {R : Type} [CommRing R] (x : Matrix n m R) (y : Matrix m n R) (hx : x * y = 1) (hy : y * x = 1) :
    Matrix m m R →* Matrix n n R where
  toFun g := x * g * y
  map_one' := by rw [Matrix.mul_one, hx]
  map_mul' g h := by
    rw [Matrix.mul_assoc (x * g), ← Matrix.mul_assoc y, ← Matrix.mul_assoc y, hy, Matrix.one_mul]
    simp only [Matrix.mul_assoc]

def rebase {S : HSp D} (β : Frame p S n) (b : Matrix (Fin S.rank) m k) (b' : Matrix m (Fin S.rank) k) (h : b * b' = 1)
    (h' : b' * b = 1) : Frame p S m where
  b := b
  b' := b'
  bb' := h
  b'b := h'
  gl := β.gl.comp (Units.map (conjHom (β.b' * b) (b' * β.b)
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc b, h, Matrix.one_mul, β.b'b])
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, h'])))
  gl_supp g := β.gl_supp _
  gl_mat g := by
    refine (β.gl_mat _).trans ?_
    change β.b * (β.b' * b * g.val * (b' * β.b)) * β.b' = _
    simp only [← Matrix.mul_assoc, β.bb', Matrix.one_mul]
    rw [Matrix.mul_assoc _ β.b, β.bb', Matrix.mul_one]

theorem exists_sumFrame {S A L : HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ)
    (β : Frame p A (Fin A.rank)) (γ : Frame p S n) : ∃ β₀ : Frame p S (Fin A.rank ⊕ Fin 1), IsSumFrame o ζ β β₀ := by
  let f : D.host.E →+* k := p.pr.comp (incA D)
  let w : Fin L.rank → D.host.E := (star ζ ⬝ᵥ L.gram *ᵥ ζ)⁻¹ • (star ζ ᵥ* L.gram)
  have hw : w ⬝ᵥ ζ = 1 := by
    rw [smul_dotProduct, ← dotProduct_mulVec, smul_eq_mul, inv_mul_cancel₀ hζ.2]
  let M : Matrix (Fin S.rank) (Fin A.rank ⊕ Fin 1) D.host.E := fromCols o.iA (replicateCol (Fin 1) (vecB o ζ))
  let N : Matrix (Fin A.rank ⊕ Fin 1) (Fin S.rank) D.host.E := fromRows o.qA (replicateRow (Fin 1) (w ᵥ* o.qB))
  have hNM : N * M = 1 := by
    rw [fromRows_mul_fromCols, o.qA_iA, ← replicateCol_mulVec, vecB, mulVec_mulVec, o.qA_iB, zero_mulVec,
      ← replicateRow_vecMul, vecMul_vecMul, o.qB_iA, vecMul_zero, replicateRow_mul_replicateCol, dotProduct_mulVec,
      vecMul_vecMul, o.qB_iB, vecMul_one, hw, replicateCol_zero, replicateRow_zero, ← fromBlocks_one]
    congr 1
    ext i j
    rw [Subsingleton.elim i j, one_apply_eq, of_apply]
  let X : Matrix (Fin A.rank ⊕ Fin 1) (Fin A.rank ⊕ Fin 1) k := fromBlocks β.b 0 0 1
  let X' : Matrix (Fin A.rank ⊕ Fin 1) (Fin A.rank ⊕ Fin 1) k := fromBlocks β.b' 0 0 1
  have h1 : (X' * N.map f) * (M.map f * X) = (1 : Matrix (Fin A.rank ⊕ Fin 1) (Fin A.rank ⊕ Fin 1) k) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (N.map f), ← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.one_mul, fromBlocks_multiply]
    simp [β.b'b]
  have h2 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [← o.rank_add, hζ.1])).1 h1
  refine ⟨rebase γ _ _ h2 h1, ?_⟩
  change M.map f * X = _
  rw [fromCols_map, fromCols_mul_fromBlocks, Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
  rfl

end Frames

attribute [local instance] GlobalTheory.FinPl.Model.relAt GlobalTheory.FinPl.Model.locAt

theorem exists_pairDat {v : Pl D} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) {S A L : HSp D} (o : OrthDec S A L)
    {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) (hA : 0 < A.rank) :
    ∃ a : PairDat (fun _ : Unit => Model.splitPt τ) A S (Fin A.rank), IsSumFrame o ζ (a.α ()) (a.α₀ ()) :=
  let ⟨β₀, h⟩ := exists_sumFrame o hζ (Model.frame τ A 1) (Model.frame τ S 1)
  ⟨⟨fun _ => Model.frame τ A 1, fun _ => β₀, fun _ => stdPair _ ⟨0, hA⟩⟩, h⟩

def midDat {v : Pl D} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (S : HSp D) (hS : 0 < S.rank) :
    MidDat (fun _ : Unit => Model.splitPt τ) S (Fin S.rank) :=
  ⟨fun _ => Model.frame τ S 1, fun _ => stdPair _ ⟨0, hS⟩⟩

def stdLat {σ : ℕ} (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) : DblLat B J B' :=
  ⟨PlaceModel.latFrame _, PlaceModel.latFrame _, PlaceModel.latFrame _, PlaceModel.latFrame _, PlaceModel.latFrame _,
    PlaceModel.latFrame _⟩

theorem exists_data {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ (v : Pl D) (p : Unit → SplitPt D (Fv D.host.F v)) (B : BesLev D 1) (J : JacLev D 1) (B' : BesLev D 0)
      (_ : StepBF ψ B J) (_ : StepFB ψ J B') (_ : Link B B'.L B'.ζ) (Λ : DblLat B J B')
      (a : PairDat p B.A B.V₀ (Fin B.A.rank)) (_ : MidDat p J.W₀ (Fin J.W₀.rank)) (a' : PairDat p B'.A B'.V₀ (Fin B'.A.rank)),
      0 < B.A.rank ∧ 0 < J.W₀.rank ∧ 0 < B'.A.rank ∧ IsSelfDualC _ Λ.L₀ ∧ IsSelfDualC _ Λ.M₀ ∧ IsSelfDualC _ Λ.L₁ ∧
      IsSelfDualC _ Λ.M₁ ∧ IsSelfDualC _ Λ.L₂ ∧ IsSelfDualC _ Λ.M₂ ∧ IsSumFrame B.o B.ζ (a.α ()) (a.α₀ ()) ∧
      IsSumFrame B'.o B'.ζ (a'.α ()) (a'.α₀ ()) := by
  obtain ⟨T, B, c, hB, -, hc, -⟩ := GlobalTheory.Unf.Inhab.exists_chain_of_isStdChar hψ
  obtain ⟨v, ⟨τ⟩⟩ := GlobalTheory.AdelicU.exists_split_place (GlobalTheory.AdelicU.isCMExt_host D)
  cases c with
  | step J B' s₁ s₂ l vL c =>
    obtain ⟨a, ha⟩ := exists_pairDat τ B.o B.line hB
    obtain ⟨a', ha'⟩ := exists_pairDat τ B'.o B'.line hc.2.1
    have h := fun S : HSp D => PlaceModel.isSelfDualC_latFrame S
    exact ⟨v, _, B, J, B', s₁, s₂, l, stdLat B J B', a, midDat τ _ hc.1, a', hB, hc.1, hc.2.1, h _, h _, h _, h _, h _, h _,
      ha, ha'⟩

theorem collapse_hyp (A B : Type) [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup A]
    [IsTopologicalGroup B] [T2Space A] [T2Space B] [CompactSpace B] (R₁ : Subgroup A) (R₂ : Subgroup B)
    (h₁ : IsClosed (R₁ : Set A)) (h₂ : IsClosed (R₂ : Set B)) :
    let G₁ : Subgroup (A × B) := (⊤ : Subgroup A).prod ⊥
    let G₂ : Subgroup (A × B) := (⊥ : Subgroup A).prod ⊤
    IsClosed (G₁ : Set (A × B)) ∧ IsClosed (G₂ : Set (A × B)) ∧ IsClosed (R₁.prod R₂ : Set (A × B)) ∧
      (∀ x ∈ G₁, ∀ y ∈ G₂, x * y = y * x) ∧ IsHomeomorph (fun x : G₁ × G₂ => (x.1 : A × B) * x.2) ∧
      (∀ r ∈ R₁.prod R₂, ∃ x ∈ R₁.prod R₂ ⊓ G₁, ∃ y ∈ R₁.prod R₂ ⊓ G₂, r = x * y) ∧ IsCompact (G₂ : Set (A × B)) ∧
      IsOpen ((G₂.subgroupOf G₂ : Subgroup G₂) : Set G₂) := by
  intro G₁ G₂
  have h1 : ∀ x ∈ G₁, x.2 = 1 := fun x hx => hx.2
  have h2 : ∀ x ∈ G₂, x.1 = 1 := fun x hx => hx.1
  refine ⟨isClosed_univ.prod isClosed_singleton, isClosed_singleton.prod isClosed_univ, h₁.prod h₂, fun x hx y hy => ?_, ?_,
    fun r hr => ⟨(r.1, 1), ⟨⟨hr.1, one_mem _⟩, trivial, rfl⟩, (1, r.2), ⟨⟨one_mem _, hr.2⟩, rfl, trivial⟩, by simp⟩,
    isCompact_singleton.prod isCompact_univ, by simp⟩
  · ext
    · simp [h2 y hy]
    · simp [h1 x hx]
  · refine isHomeomorph_iff_exists_inverse.2 ⟨by fun_prop,
      fun g => (⟨(g.1, 1), ⟨trivial, rfl⟩⟩, ⟨(1, g.2), ⟨rfl, trivial⟩⟩), ?_, ?_, ?_⟩
    · rintro ⟨x, y⟩
      ext <;> simp [h1 x x.2, h2 y y.2]
    · intro g
      simp
    · fun_prop

end GlobalTheory.FinPl.DblInh

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioParts
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

open GlobalTheory.Fam (UnitRatio)

variable {D : D7} {c : Comm D} (v : VCom c) {𝒯 : Type} (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)) (F : ∀ s, GlobalTheory.QPl.QFam v (t s))

structure RatioParts (S : 𝒯 → ℕ → Prop) (s₀ : 𝒯) : Prop where
  base : (F s₀).r = 0
  sc : ∀ s j, j < D.R.m → UnitRatio (S s) ((w s).sc j) ((w s₀).sc j)
  cT : ∀ s j ρ, j + 2 * ρ + 2 = D.R.m → UnitRatio (S s) ((w s).cT j) ((w s₀).cT j)
  cI : ∀ s j, j < D.R.m → (t s).cI j * ∏ i, (((F s).Q i).idx (j + 1) : ℂ) = (t s₀).cI j
  cK : ∀ s j, j < D.R.m → UnitRatio (S s) ((t s).cK j) ((t s₀).cK j)
  cP : ∀ s, UnitRatio (S s) (t s).cP (t s₀).cP

end GlobalTheory.SeeSaw

end
end

