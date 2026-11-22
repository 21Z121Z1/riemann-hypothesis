import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherFaceStatementsIndependentOfError
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def reFaceErr (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) : type_of% R.err0 :=
  fun w _ => errOf ((R.toCx3 F).data (reFace F Dc Sp Zsc).cr false) ((reFace F Dc Sp Zsc).fc (R.toCx3 F).zs).Z.F0 w

set_option maxHeartbeats 4000000 in

theorem reFace_errEq (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) :
    ErrEq (R.withErr (reFaceErr R F Dc Sp Zsc)) (reFace F Dc Sp Zsc) := fun _ _ => rfl

set_option maxHeartbeats 4000000 in

theorem reFace_keep (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (h : Keep (A3 := A3) R.toRealDat F.lv2 cG) :
    Keep (A3 := A3) (R.withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 cG :=
  ⟨h.std, h.signs, h.frames, h.beta, h.prX, h.grp, h.psi, h.guard, h.valKs, h.frameKs, h.levKs⟩

set_option maxHeartbeats 4000000 in

theorem reFace_keep_back (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0)
    (h : Keep (A3 := A3) (R.withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 cG) : Keep (A3 := A3) R.toRealDat F.lv2 cG :=
  ⟨h.std, h.signs, h.frames, h.beta, h.prX, h.grp, h.psi, h.guard, h.valKs, h.frameKs, h.levKs⟩

set_option maxHeartbeats 4000000 in

theorem reFace_scal (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (hl6 : ∀ i, (Zsc (R.toCx3 F).zs).l6m i = (F.Zsc (R.toCx3 F).zs).l6m i ∨
      ((∀ p, R.Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → R.PartAt F i p v))
    (hs : R.IsScal F) : R.IsScal (reFace F Dc Sp Zsc) := by
  refine ⟨hs.lam0, hs.kap, hs.off, fun i t p hp => ?_, fun i p v hv hp => ?_, hs.tup⟩
  · refine (hs.abs0 i t p hp).trans ?_
    rcases hl6 i with h | h
    · exact congrArg Real.exp h.symm
    · exact absurd hp (h.1 p)
  · refine (hs.abs i p v hv hp).trans ?_
    rcases hl6 i with h | h
    · exact congrArg Real.exp h.symm
    · exact absurd (h.2 p v hv) hp

set_option maxHeartbeats 4000000 in

theorem reFace_pins (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0)
    (hl6 : ∀ i, (Zsc (R.toCx3 F).zs).l6m i = (F.Zsc (R.toCx3 F).zs).l6m i ∨
      ((∀ p, R.Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → R.PartAt F i p v))
    (hP : Pins R F cG) : Pins (R.withErr e) (reFace F Dc Sp Zsc) cG := by
  have h := RealDat3.weak_characterisation_with_error hP.char e
  have hl6' : ∀ i, (Zsc ((R.withErr e).toCx3 F).zs).l6m i = (F.Zsc ((R.withErr e).toCx3 F).zs).l6m i ∨
      ((∀ p, (R.withErr e).Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → (R.withErr e).PartAt F i p v) := fun i => by
    rw [RealDat3.zs_withErr]
    exact (hl6 i).imp id fun h => ⟨h.1, fun p v hv => (RealDat3.partAt_withErr e i p v).2 (h.2 p v hv)⟩
  exact ⟨⟨h.base, h.inert, h.fullY, h.fullX, h.fullP, reFace_scal (R.withErr e) F Dc Sp Zsc hl6' h.scal, h.tup, h.phase, h.allPl⟩,
    reFace_keep R F cG Dc Sp Zsc e hP.keep, hP.phs, hP.trSem⟩

set_option maxHeartbeats 4000000 in

theorem further_face_statements_independent_of_error (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (h : UnusedChoiceStatements R F) :
    UnusedChoiceStatements (R.withErr e) (reFace F Dc Sp Zsc) :=
  ⟨⟨h.ex.ItY, h.ex.ItX, h.ex.ioY, h.ex.ioX, h.ex.Th, h.ex.ioP, h.ex.thF, h.ex.thG⟩, h.conj, h.levelW, h.integral⟩

set_option maxHeartbeats 4000000 in

def reFaceRead (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) : Read (A3 := A3) (R.withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 X0 :=
  { Y with
    mj := ⟨Y.mj.eW, Y.mj.eW_range, Y.mj.eW_norm, Y.mj.eW_lat⟩
    cen0 := fun cG hK => Y.cen0 cG (reFace_keep_back R F cG Dc Sp Zsc e hK)
    cen1 := fun cG hK => Y.cen1 cG (reFace_keep_back R F cG Dc Sp Zsc e hK) }

set_option maxHeartbeats 4000000 in

def reFaceReadL (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) :
    ReadL (R.withErr e) (reFace F Dc Sp Zsc) X0 (reFaceRead R F Dc Sp Zsc e X0 Y) :=
  { Z with }

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfConstSmul
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

variable {D : D7}

def word (θ : InfF D) (V : HSp D) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (φ : GA D V → ℂ) :
    GA D V → ℂ := l.foldr (fun p f => Rder θ V p.1 p.2 f) φ

def IsMod (θ : InfF D) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  φ ∈ SmFun θ V ∧ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ ∀ l, (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
    Continuous (word θ V l φ) ∧ ∃ (N : ℕ) (C : ℝ), ∀ g, ‖word θ V l φ g‖ ≤ C * (height θ V g : ℝ) ^ N

private theorem word_mem_smFun {θ : InfF D} {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : word θ V l φ ∈ SmFun θ V := by
  induction l with
  | nil => exact hφ
  | cons p l ih =>
    exact Rder_mem (ih fun q hq => hl q (List.mem_cons_of_mem _ hq)) (hl p (by simp))

theorem word_add {θ : InfF D} {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) {φ ψ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hψ : ψ ∈ SmFun θ V) :
    word θ V l (φ + ψ) = word θ V l φ + word θ V l ψ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    show Rder θ V p.1 p.2 (word θ V l (φ + ψ)) =
      Rder θ V p.1 p.2 (word θ V l φ) + Rder θ V p.1 p.2 (word θ V l ψ)
    rw [ih hl', Rder_add (word_mem_smFun hl' hφ) (word_mem_smFun hl' hψ) (hl p (by simp))]

theorem word_smul {θ : InfF D} {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (c : ℂ) (φ : GA D V → ℂ) : word θ V l (c • φ) = c • word θ V l φ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    show Rder θ V p.1 p.2 (word θ V l (c • φ)) = c • Rder θ V p.1 p.2 (word θ V l φ)
    rw [ih fun q hq => hl q (List.mem_cons_of_mem _ hq), Rder_smul]

theorem word_Rder {θ : InfF D} {V : HSp D} (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    word θ V l (Rder θ V τ X φ) = word θ V (l ++ [(τ, X)]) φ := by
  unfold word
  rw [List.foldr_append]
  rfl

def Decay (θ : InfF D) (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | φ ∈ SmFun θ V ∧ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ ∀ l, (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
    Continuous (word θ V l φ) ∧ IsRapidDecay θ V (word θ V l φ)}
  add_mem' := by
    rintro φ ψ ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨add_mem a1 b1, fun γ hγ g => by simp only [Pi.add_apply, a2 γ hγ, b2 γ hγ], fun l hl => ?_⟩
    rw [word_add hl a1 b1]
    refine ⟨(a3 l hl).1.add (b3 l hl).1, fun N => ?_⟩
    obtain ⟨C, hC⟩ := (a3 l hl).2 N
    obtain ⟨C', hC'⟩ := (b3 l hl).2 N
    refine ⟨C + C', fun g => le_trans ?_ (add_le_add (hC g) (hC' g))⟩
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  zero_mem' := by
    refine ⟨zero_mem _, fun _ _ _ => rfl, fun l hl => ?_⟩
    have := word_smul (θ := θ) hl 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]
    exact ⟨continuous_const, fun N => ⟨0, fun g => by simp⟩⟩
  smul_mem' := by
    rintro c φ ⟨a1, a2, a3⟩
    refine ⟨Submodule.smul_mem _ c a1, fun γ hγ g => by simp only [Pi.smul_apply, a2 γ hγ], fun l hl => ?_⟩
    rw [word_smul hl]
    refine ⟨(a3 l hl).1.const_smul c, fun N => ?_⟩
    obtain ⟨C, hC⟩ := (a3 l hl).2 N
    refine ⟨‖c‖ * C, fun g => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg c)

theorem Rder_left {θ : InfF D} {V : HSp D} {φ : GA D V → ℂ} {γ : GA D V} (h : ∀ g, φ (γ * g) = φ g)
    (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V) :
    Rder θ V τ X φ (γ * g) = Rder θ V τ X φ g := by
  show deriv (fun t : ℝ => φ (γ * g * oneP θ V τ X t)) 0 = deriv (fun t : ℝ => φ (g * oneP θ V τ X t)) 0
  simp only [mul_assoc, h]

theorem append_mem_lie {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    ∀ p ∈ l ++ [(τ, X)], p.2 ∈ lieAt V p.1 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hl p hp
  · rw [List.mem_singleton] at hp
    subst hp
    exact hX

theorem Rder_mem_Decay {θ : InfF D} {V : HSp D} {φ : GA D V → ℂ} (h : φ ∈ Decay θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : Rder θ V τ X φ ∈ Decay θ V := by
  obtain ⟨h1, h2, h3⟩ := h
  refine (show _ ∧ _ ∧ _ from ⟨Rder_mem h1 hX, fun γ hγ g => Rder_left (h2 γ hγ) τ X g, fun l hl => ?_⟩)
  rw [word_Rder]
  exact h3 _ (append_mem_lie hl hX)

theorem IsMod.rder {θ : InfF D} {V : HSp D} {φ : GA D V → ℂ} (h : IsMod θ V φ) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : IsMod θ V (Rder θ V τ X φ) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold IsMod
  refine ⟨Rder_mem h1 hX, fun γ hγ g => Rder_left (h2 γ hγ) τ X g, fun l hl => ?_⟩
  rw [word_Rder]
  exact h3 _ (append_mem_lie hl hX)

private theorem word_const_eq_const_norm_le {θ : InfF D} {V : HSp D} (c : ℂ)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) :
    ∃ d : ℂ, word θ V l (fun _ => c) = (fun _ => d) ∧ ‖d‖ ≤ ‖c‖ := by
  induction l with
  | nil => exact ⟨c, rfl, le_rfl⟩
  | cons p l ih =>
    obtain ⟨d, hd, -⟩ := ih
    refine ⟨0, ?_, by simp⟩
    show Rder θ V p.1 p.2 (word θ V l fun _ => c) = _
    rw [hd]
    funext g
    simp [Rder]

theorem isMod_const (θ : InfF D) (V : HSp D) (c : ℂ) : IsMod θ V fun _ => c := by
  unfold IsMod
  refine ⟨?_, fun _ _ _ => rfl, fun l _ => ?_⟩
  · intro k τs Xs _ g
    exact contDiff_const
  · obtain ⟨d, hd, hdc⟩ := word_const_eq_const_norm_le (θ := θ) (V := V) c l
    rw [hd]
    exact ⟨continuous_const, 0, ‖c‖, fun _ => by rw [pow_zero, mul_one]; exact hdc⟩

structure IsKerSys (θ : InfF D) (V W : HSp D) {M : Type} [AddCommGroup M] [Module ℂ M]
    (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)) : Prop where
  cont : ∀ f, Continuous fun p : GA D V × GA D W => κ f p.1 p.2
  left : ∀ f, ∀ γ ∈ GQ V, ∀ δ ∈ GQ W, ∀ g h, κ f (γ * g) (δ * h) = κ f g h
  level : ∀ f, ∃ (U : Subgroup (GA D V)) (U' : Subgroup (GA D W)), IsOpen (U : Set (GA D V)) ∧
    IsOpen (U' : Set (GA D W)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ k' ∈ U', k' ∈ GfC W → ∀ g h, κ f (g * k) (h * k') = κ f g h
  growth : ∃ N : ℕ, ∀ f, ∃ C : ℝ, ∀ g h, ‖κ f g h‖ ≤ C * ((height θ V g : ℝ) * (height θ W h : ℝ)) ^ N
  derV : ∀ τ, ∀ X ∈ lieAt V τ, ∀ f, ∃ f', ∀ g h,
    HasDerivAt (fun t : ℝ => κ f (g * oneP θ V τ X t) h) (κ f' g h) 0
  derW : ∀ τ, ∀ X ∈ lieAt W τ, ∀ f, ∃ f', ∀ g h,
    HasDerivAt (fun t : ℝ => κ f g (h * oneP θ W τ X t)) (κ f' g h) 0
  cap : ∀ τ, ∃ a b : ℕ → Module.End ℂ M, (∀ k f h, gelf θ V τ k (fun g => κ f g h) = fun g => κ (a k f) g h) ∧
    (∀ k f g, gelf θ W τ k (κ f g) = κ (b k f) g) ∧ Algebra.adjoin ℂ (Set.range a) = Algebra.adjoin ℂ (Set.range b)

def swapKer {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)) :
    M →ₗ[ℂ] (GA D W → GA D V → ℂ) where
  toFun f h g := κ f g h
  map_add' f f' := by rw [map_add]; rfl
  map_smul' c f := by rw [map_smul]; rfl

theorem IsKerSys.swap {θ : InfF D} {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M]
    {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)} (h : IsKerSys θ V W κ) : IsKerSys θ W V (swapKer κ) where
  cont f := (h.cont f).comp continuous_swap
  left f γ hγ δ hδ g g' := h.left f δ hδ γ hγ g' g
  level f := by
    obtain ⟨U, U', hU, hU', hk⟩ := h.level f
    exact ⟨U', U, hU', hU, fun k hk1 hk2 k' hk1' hk2' g g' => hk k' hk1' hk2' k hk1 hk2 g' g⟩
  growth := by
    obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun f => ?_⟩
    obtain ⟨C, hC⟩ := hN f
    refine ⟨C, fun g g' => ?_⟩
    have hb := hC g' g
    rw [mul_comm (height θ V g' : ℝ)] at hb
    exact hb
  derV τ X hX f := by
    obtain ⟨f', hf'⟩ := h.derW τ X hX f
    exact ⟨f', fun g g' => hf' g' g⟩
  derW τ X hX f := by
    obtain ⟨f', hf'⟩ := h.derV τ X hX f
    exact ⟨f', fun g g' => hf' g' g⟩
  cap τ := by
    obtain ⟨a, b, ha, hb, hab⟩ := h.cap τ
    exact ⟨b, a, fun k f g' => hb k f g', fun k f g => ha k f g, hab.symm⟩

def constKer (V W : HSp D) : ℂ →ₗ[ℂ] (GA D V → GA D W → ℂ) where
  toFun c _ _ := c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def OmCont (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → ∀ w, Continuous fun p : GA D S × GA D T => om p f w

def thKer (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) :
    GlobalTheory.RealWeil.thetaSub ψ S T →ₗ[ℂ] (GA D S → GA D T → ℂ) where
  toFun f g h := om (g, h) f.1 0
  map_add' f f' := by funext g h; simp
  map_smul' c f := by funext g h; simp

end GlobalTheory.Mem.Lift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantActionCommuteUnitaryRepSmooth
section
open Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmVec Matrix

noncomputable section
namespace GlobalTheory.SmVecGelfComm

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def RealLin (G : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  (∀ X ∈ lieG G, ∀ Y ∈ lieG G, dRep π (X + Y) w = dRep π X w + dRep π Y w) ∧
    ∀ (a : ℝ), ∀ X ∈ lieG G, dRep π (a • X) w = (a : ℂ) • dRep π X w

theorem lie_smul (a : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) : a • X ∈ lieG G := by
  have h : Xᴴ * G + G * X = 0 := hX
  show _ + _ = 0
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, star_trivial, ← smul_add, h, smul_zero]

theorem conjG_add (Z W : Matrix (Fin n) (Fin n) ℂ) : conjG G (Z + W) = conjG G Z + conjG G W := by
  simp only [conjG, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, neg_add]

theorem conjG_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) : conjG G (c • Z) = star c • conjG G Z := by
  simp only [conjG, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem dRepC_add_left (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    dRepC G π (Z + W) w = dRepC G π Z w + dRepC G π W w := by
  have e1 : (1 / 2 : ℂ) • (Z + W + conjG G (Z + W)) =
      (1 / 2 : ℂ) • (Z + conjG G Z) + (1 / 2 : ℂ) • (W + conjG G W) := by rw [conjG_add]; module
  have e2 : (1 / (2 * Complex.I)) • (Z + W - conjG G (Z + W)) =
      (1 / (2 * Complex.I)) • (Z - conjG G Z) + (1 / (2 * Complex.I)) • (W - conjG G W) := by
    rw [conjG_add]; module
  unfold dRepC
  rw [e1, e2, hl.1 _ (parts_mem hG hh Z).1 _ (parts_mem hG hh W).1,
    hl.1 _ (parts_mem hG hh Z).2 _ (parts_mem hG hh W).2]
  module

theorem dRepC_smul_left (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) (c : ℂ)
    (Z : Matrix (Fin n) (Fin n) ℂ) : dRepC G π (c • Z) w = c • dRepC G π Z w := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, c = a + b * Complex.I := ⟨c.re, c.im, (Complex.re_add_im c).symm⟩
  have hs : star ((a : ℂ) + b * Complex.I) = a - b * Complex.I := by simp [sub_eq_add_neg]
  have hi : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    field_simp
    simp
  have hI := Complex.I_mul_I
  obtain ⟨h1, h2⟩ := parts_mem hG hh Z
  have e1 : (1 / 2 : ℂ) • (((a : ℂ) + b * Complex.I) • Z + conjG G (((a : ℂ) + b * Complex.I) • Z)) =
      a • (1 / 2 : ℂ) • (Z + conjG G Z) + (-b) • (1 / (2 * Complex.I)) • (Z - conjG G Z) := by
    rw [conjG_smul, hs, hi, ← Complex.coe_smul, ← Complex.coe_smul]
    push_cast
    module
  have e2 : (1 / (2 * Complex.I)) • (((a : ℂ) + b * Complex.I) • Z - conjG G (((a : ℂ) + b * Complex.I) • Z)) =
      b • (1 / 2 : ℂ) • (Z + conjG G Z) + a • (1 / (2 * Complex.I)) • (Z - conjG G Z) := by
    rw [conjG_smul, hs, hi, ← Complex.coe_smul, ← Complex.coe_smul]
    match_scalars
    · linear_combination (-(b : ℂ) / 2) * hI
    · linear_combination (-(b : ℂ) / 2) * hI
  unfold dRepC
  rw [e1, e2, hl.1 _ (lie_smul _ h1) _ (lie_smul _ h2), hl.1 _ (lie_smul _ h1) _ (lie_smul _ h2),
    hl.2 _ _ h1, hl.2 _ _ h1, hl.2 _ _ h2, hl.2 _ _ h2]
  push_cast
  match_scalars
  · ring
  · linear_combination (-(b : ℂ)) * hI

def dLin (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] H where
  toFun Z := dRepC G π Z w
  map_add' := dRepC_add_left hG hh hl
  map_smul' := dRepC_smul_left hG hh hl

theorem dRepC_eq_sum (hG : IsUnit G) (hh : Gᴴ = G) {w : H} (hl : RealLin G π w) (Z : Matrix (Fin n) (Fin n) ℂ) :
    dRepC G π Z w = ∑ c, ∑ d, Z c d • dRepC G π (Matrix.single c d 1) w := by
  have e : Z = ∑ c, ∑ d, Z c d • Matrix.single c d (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    simp
  show dLin hG hh hl Z = _
  conv_lhs => rw [e]
  simp only [map_sum, map_smul]
  rfl

theorem conjG_conj (hG : IsUnit G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (Z : Matrix (Fin n) (Fin n) ℂ) : conjG G (g⁻¹ * Z * g) = g⁻¹ * conjG G Z * g := by
  have h : gᴴ * G * g = G := hg
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (isUnit_of_mem_UH hG hg)
  have hD := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have h1 : G * g⁻¹ = gᴴ * G := by
    conv_lhs => rw [← h]
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (g⁻¹)ᴴ * G = G * g := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hd]; simp
  have h3 : G⁻¹ * gᴴ = g⁻¹ * G⁻¹ := by
    calc G⁻¹ * gᴴ = G⁻¹ * (gᴴ * G) * G⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hD, Matrix.mul_one]
      _ = _ := by rw [← h1, ← Matrix.mul_assoc, nonsing_inv_mul _ hD, Matrix.one_mul]
  calc conjG G (g⁻¹ * Z * g) = -((G⁻¹ * gᴴ) * Zᴴ * ((g⁻¹)ᴴ * G)) := by
        simp only [conjG, conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h3, h2]; simp only [conjG, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]

theorem dRepC_rep (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {w : H} (hw : w ∈ smSub G π)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) (Z : Matrix (Fin n) (Fin n) ℂ) :
    dRepC G π Z (π g w) = π g (dRepC G π (g⁻¹ * Z * g) w) := by
  unfold dRepC
  rw [dRep_rep hG hπ hw hg (parts_mem hG hh Z).1, dRep_rep hG hπ hw hg (parts_mem hG hh Z).2, conjG_conj hG hg,
    map_add, map_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]

def dEnd (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Module.End ℂ (smSub G π) where
  toFun w := ⟨dRepC G π Z w, dRepC_mem hG hh hπ Z w.2⟩
  map_add' v w := Subtype.ext <| by
    show dRepC G π Z (v + w) = dRepC G π Z v + dRepC G π Z w
    unfold dRepC
    rw [dRep_add v.2 w.2 (parts_mem hG hh Z).1, dRep_add v.2 w.2 (parts_mem hG hh Z).2]
    module
  map_smul' c w := Subtype.ext <| by
    show dRepC G π Z (c • w) = c • dRepC G π Z w
    unfold dRepC
    rw [dRep_smul c w.2 (parts_mem hG hh Z).1, dRep_smul c w.2 (parts_mem hG hh Z).2]
    module

def gEnd (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) : Module.End ℂ (smSub G π) :=
  (π g : H →ₗ[ℂ] H).restrict fun _ hw => rep_mem hG hπ hw hg

theorem gEnd_coe (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) (w : smSub G π) : ((gEnd hG hπ hg w : smSub G π) : H) = π g w := rfl

theorem foldr_dEnd (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (w : smSub G π) :
    (((l.map (dEnd hG hh hπ)).prod w : smSub G π) : H) = (l.map (dRepC G π)).foldr (fun f acc => f acc) (w : H) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_cons, List.foldr_cons, ← ih]
    rfl

theorem gelfH_eq (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) (k : ℕ) (w : smSub G π) :
    gelfH G π k w =
      ((∑ c, (Matrix.of (fun a b => dEnd hG hh hπ (Matrix.single a b 1)) ^ (k + 1)) c c) w : smSub G π) := by
  rw [← GlobalTheory.SmoothForms.gelfA_eq_sum_pow, GlobalTheory.SmoothForms.gelfA, LinearMap.sum_apply, Submodule.coe_sum, gelfH]
  refine Finset.sum_congr rfl fun idx _ => ?_
  have := foldr_dEnd hG hh hπ (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) w
  rw [List.map_ofFn, List.map_ofFn] at this
  exact this.symm

theorem gelfH_rep_of (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    (hl : ∀ w ∈ smSub G π, RealLin G π w) (k : ℕ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    {w : H} (hw : w ∈ smSub G π) : gelfH G π k (π g w) = π g (gelfH G π k w) := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (isUnit_of_mem_UH hG hg)
  have hQP : gᵀ * (g⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, nonsing_inv_mul _ hd, Matrix.transpose_one]
  have h := GlobalTheory.Dec.GelfAd.trace_pow_comm (fun a b => dEnd hG hh hπ (Matrix.single a b 1)) (gEnd hG hπ hg) _ _ hQP
    (fun a b => by
      refine LinearMap.ext fun v => Subtype.ext ?_
      rw [Module.End.mul_apply, Module.End.mul_apply]
      refine (dRepC_rep hG hh hπ v.2 hg _).trans ?_
      rw [gEnd_coe]
      congr 1
      rw [dRepC_eq_sum hG hh (hl v v.2)]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      congr 1
      simp [Matrix.mul_apply, Matrix.single, ite_and]) (k + 1)
  have h2 := congrArg (fun T : Module.End ℂ (smSub G π) => ((T ⟨w, hw⟩ : smSub G π) : H)) h
  simp only [Module.End.mul_apply] at h2
  rw [← gelfH_eq] at h2
  refine h2.trans ?_
  rw [gEnd_coe, ← gelfH_eq]

theorem gelfH_rep : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P →
    Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (k : ℕ), ∀ g ∈ Formalism.QuantumDeterminants.UH G,
    ∀ w ∈ smSub G (trRep σ P),
    gelfH G (trRep σ P) k ((trRep σ P) g w) = (trRep σ P) g (gelfH G (trRep σ P) k w) :=
  fun n ε H _ _ _ σ P G hP h hσ k _ hg _ hw =>
    gelfH_rep_of (gram_unit hP h) (gram_herm h) (isURepOn_trRep hP h hσ) (GlobalTheory.T.derived_action_smooth_vector_real_linear n ε H σ P G hP h hσ) k hg hw

end GlobalTheory.SmVecGelfComm
end
end

