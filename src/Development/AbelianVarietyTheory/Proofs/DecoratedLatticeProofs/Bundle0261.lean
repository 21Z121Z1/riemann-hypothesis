import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.DoubledUnramifiedFrames
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WittIndexAddOfIsWittLower
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRealSSmulTwoSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

noncomputable section

open MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Scale

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w₀ (c • f) = c • heisO ψ S T w₀ f := by
  funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem comb_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : WO S T →₀ ℂ) (c : ℂ) (f : WO S T → ℂ) :
    comb ψ S T a (c • f) = c • comb ψ S T a f := by
  simp only [comb, heisO_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_comm]

theorem biComb_smul (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (a : WO A S →₀ ℂ) (a' : WO S A' →₀ ℂ) (c : ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' a a' (c • C) = c • biComb ψ A S A' a a' C := by
  funext u v
  simp only [biComb]
  have h1 : (fun u' => comb ψ S A' a' ((c • C) u') v) = c • fun u' => comb ψ S A' a' (C u') v := by
    funext u'
    show comb ψ S A' a' (c • C u') v = c * comb ψ S A' a' (C u') v
    rw [comb_smul]; rfl
  rw [h1, comb_smul]; rfl

theorem isThetaFunO_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) where
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    exact ⟨U, hUo, fun u hu hi => by rw [heisO_smul, hU u hu hi]⟩
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := contDiff_const.mul (hf.smooth k L hL hfin w)

theorem isLatVac_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {Λ : AddSubgroup (WO S T)} {f : WO S T → ℂ}
    (hf : IsLatVac (heisO ψ S T) Λ f) : IsLatVac (heisO ψ S T) Λ (c • f) :=
  ⟨fun u hu => by rw [heisO_smul, hf.1 u hu], fun e' he u hu hh => by rw [heisO_smul, hf.2 e' he u hu hh]⟩

theorem isBiVac_smul {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {LA : Set (Fin A.rank → D.host.E)}
    {LS : Set (Fin S.rank → D.host.E)} {LA' : Set (Fin A'.rank → D.host.E)} (c : ℂ) {C : WO A S → WO S A' → ℂ}
    (h : IsBiVac ψ A S A' LA LS LA' C) : IsBiVac ψ A S A' LA LS LA' (c • C) where
  cont := continuous_const.mul h.cont
  left v := by
    have e : (fun u => (c • C) u v) = c • fun u => C u v := rfl
    rw [e]; exact ⟨isThetaFunO_smul c (h.left v).1, isLatVac_smul c (h.left v).2⟩
  right u := by
    have e : (c • C) u = c • C u := rfl
    rw [e]; exact ⟨isThetaFunO_smul c (h.right u).1, isLatVac_smul c (h.right u).2⟩

theorem isBiSmooth_smul {A S A' : HSp D} (c : ℂ) {C : WO A S → WO S A' → ℂ} (h : IsBiSmooth C) :
    IsBiSmooth (c • C) :=
  fun n L L' hL hL' h0 h0' u v => by
    show ContDiff ℝ _ fun t => c * C (u + L t) (v + L' t)
    exact ContDiff.mul contDiff_const (h n L L' hL hL' h0 h0' u v)

end GlobalTheory.SeeSaw.Scale

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsStepVecOfIff
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.StepData (XIx Ix latOf box LatFrame)
open GlobalTheory.LocMod (GAt PinGBy ofSplit MovedTo)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastPair lastKer)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedLocalFrameSequences (IsFockOver StepsAll vec atW IsMoved InAt InvOnUnits IsBesFrame IsJacFrame FrameMapsPrefix jacLat ptBF ptFB)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RouteCompare

variable {D : D7}

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def toFin (p : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank n) : Frame p S n :=
  ⟨F.β, F.γ, F.βγ, F.γβ, (GlobalTheory.LocGrp.exists_hom (ofSplit p) F).choose,
    fun g => ((GlobalTheory.LocGrp.exists_hom (ofSplit p) F).choose_spec g).1,
    fun g => ((GlobalTheory.LocGrp.exists_hom (ofSplit p) F).choose_spec g).2⟩

def move {p : SplitPt D k} {S : HSp D} (β : Frame p S n) (g : GA D S) : Frame p S n :=
  toFin p S ⟨(mt S g).map p.pr * β.b, β.b' * (mt S g⁻¹).map p.pr,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, ← Matrix.map_mul]; simp [Formalism.L2.Theta.mt],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ β.b, ← Matrix.map_mul]; simp [Formalism.L2.Theta.mt, β.b'b]⟩

theorem isMoved_move {p : SplitPt D k} {S : HSp D} (β : Frame p S n) (g : GA D S) : IsMoved g β (move β g) := rfl

theorem isMoved_back {p : SplitPt D k} {S : HSp D} (β : Frame p S n) (g : GA D S) : IsMoved g (move β g⁻¹) β := by
  change β.b = (mt S g).map p.pr * ((mt S g⁻¹).map p.pr * β.b)
  rw [← Matrix.mul_assoc, ← Matrix.map_mul]
  simp [Formalism.L2.Theta.mt]

def IsCharBy (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle) (θ : k) : Prop :=
  ∀ a, (χ a : ℂ) = psiE ψ (p.sec (θ * a))

def BesCols {p : SplitPt D k} {ρ : ℕ} (B : BesLev D ρ) (θ s : k) (α : Frame p B.A n) (β : Frame p B.V (n ⊕ Fin c)) : Prop :=
  c = 2 * ρ + 1 ∧ (∀ r a, β.b r (Sum.inl a) = ((B.d.i₀ * B.o.iA).map (ofSplit p).pr * α.b) r a) ∧
    (∀ (i : Fin ρ) (j : Fin c), j.val = i.val → ∀ r, β.b r (Sum.inr j) = s * θ ^ (ρ - i.val) * (ofSplit p).pr (B.d.e r i)) ∧
    (∀ j : Fin c, j.val = ρ → ∀ r, β.b r (Sum.inr j) = s * (ofSplit p).pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r)) ∧
    ∀ (i : Fin ρ) (j : Fin c), j.val + i.val = 2 * ρ → ∀ r,
      β.b r (Sum.inr j) = s * (-(ofSplit p).hz B / θ) * (-1 / θ) ^ (ρ - 1 - i.val) * (ofSplit p).pr (B.d.e' r i)

def JacCols {p : SplitPt D k} {ρ : ℕ} (J : JacLev D ρ) (θ s a : k) (α : Frame p J.W₀ n) (β : Frame p J.W (n ⊕ Fin c)) : Prop :=
  c = 2 * ρ ∧ (∀ r b, β.b r (Sum.inl b) = (J.d.i₀.map (ofSplit p).pr * α.b) r b) ∧
    (∀ (i : Fin ρ) (j : Fin c), j.val = i.val → ∀ r, β.b r (Sum.inr j) = s * θ ^ (ρ - i.val) * (ofSplit p).pr (J.d.e r i)) ∧
    ∀ (i : Fin ρ) (j : Fin c), j.val + i.val + 1 = 2 * ρ → ∀ r,
      β.b r (Sum.inr j) = s * a * (-1 / θ) ^ (ρ - 1 - i.val) * (ofSplit p).pr (J.d.e' r i)

theorem besCols_toFin {p : SplitPt D k} {ρ : ℕ} (B : BesLev D ρ) (s : k) (α : GlobalTheory.LocMod.Frame k B.A.rank n)
    (β : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin c)) :
    BesCols B (ofSplit p).xi s (toFin p _ α) (toFin p _ β) ↔ (ofSplit p).IsBesFrame B s α β := Iff.rfl

theorem jacCols_toFin {p : SplitPt D k} {ρ : ℕ} (J : JacLev D ρ) (s h : k) (α : GlobalTheory.LocMod.Frame k J.W₀.rank n)
    (β : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin c)) :
    JacCols J (ofSplit p).xi s (h / (ofSplit p).xi) (toFin p _ α) (toFin p _ β) ↔ (ofSplit p).IsJacFrame J s h α β := Iff.rfl

open GlobalTheory.LocMod.Witness in

theorem exists_jacCols {p : SplitPt D k} {ρ : ℕ} (J : JacLev D ρ) {θ s a : k} (hθ : θ ≠ 0) (hs : s ≠ 0) (ha : a ≠ 0)
    (α : Frame p J.W₀ n) (hc : c = 2 * ρ) : ∃ β : Frame p J.W (n ⊕ Fin c), JacCols J θ s a α β := by
  subst hc
  obtain ⟨G, hG⟩ := exists_witt (ofSplit p) J.d (GlobalTheory.LocMod.Frame.ofFinPl α)
  obtain ⟨F, hF⟩ := exists_scaled' G
    (Sum.map id (Sum.elim (fun i : Fin ρ => (⟨i.val, by omega⟩ : Fin (2 * ρ))) fun i : Fin ρ => ⟨2 * ρ - 1 - i.val, by omega⟩))
    (by
      rintro (a | a | a) (b | b | b) h <;> simp [Fin.ext_iff] at h ⊢ <;> first | exact h | omega)
    (by simp; ring)
    (Sum.elim (fun _ => 1) (Sum.elim (fun i => s * θ ^ (ρ - i.val)) fun i => s * a * (-1 / θ) ^ (ρ - 1 - i.val)))
    (by rintro (a | a | a) <;> simp [hs, ha, hθ])
  rw [hG] at hF
  refine ⟨toFin p _ F, rfl, fun r a => (hF r (Sum.inl a)).trans (one_mul _), fun i j h r => ?_, fun i j h r => ?_⟩
  · rw [show j = ⟨i.val, by omega⟩ from Fin.ext h]
    exact hF r (Sum.inr (Sum.inl i))
  · rw [show j = ⟨2 * ρ - 1 - i.val, by omega⟩ from Fin.ext (by simp only; omega)]
    exact hF r (Sum.inr (Sum.inr i))

open GlobalTheory.LocMod.Witness in

theorem exists_besCols {p : SplitPt D k} {ρ : ℕ} (B : BesLev D ρ) {θ s : k} (hθ : θ ≠ 0) (hs : s ≠ 0)
    (α : Frame p B.A n) (hc : c = 2 * ρ + 1) : ∃ β : Frame p B.V (n ⊕ Fin c), BesCols B θ s α β := by
  subst hc
  obtain ⟨F₀, h₀⟩ := exists_core (ofSplit p) B one_ne_zero (GlobalTheory.LocMod.Frame.ofFinPl α)
  obtain ⟨G, hG⟩ := exists_witt (ofSplit p) B.d F₀
  have hz := hz_ne (ofSplit p) B
  obtain ⟨F, hF⟩ := exists_scaled' G
    (Sum.elim (Sum.map id fun _ => (⟨ρ, by omega⟩ : Fin (2 * ρ + 1)))
      (Sum.elim (fun i : Fin ρ => Sum.inr (⟨i.val, by omega⟩ : Fin (2 * ρ + 1)))
        fun i : Fin ρ => Sum.inr ⟨2 * ρ - i.val, by omega⟩))
    (by
      rintro ((a | a) | a | a) ((b | b) | b | b) h <;> simp [Fin.ext_iff] at h ⊢ <;> first | exact h | omega)
    (by simp; ring)
    (Sum.elim (Sum.elim (fun _ => 1) fun _ => s)
      (Sum.elim (fun i => s * θ ^ (ρ - i.val)) fun i => s * (-(ofSplit p).hz B / θ) * (-1 / θ) ^ (ρ - 1 - i.val)))
    (by rintro ((a | a) | a | a) <;> simp [hs, hz, hθ])
  rw [hG] at hF
  refine ⟨toFin p _ F, rfl, fun r a => ((hF r (Sum.inl (Sum.inl a))).trans (one_mul _)).trans ?_, fun i j h r => ?_,
    fun j h r => ?_, fun i j h r => ?_⟩
  · change (B.d.i₀.map (prH (ofSplit p)) * F₀.β) r (Sum.inl a) = ((B.d.i₀ * B.o.iA).map (prH (ofSplit p)) * α.b) r a
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun u _ => by rw [h₀.1]; rfl
  · rw [show j = ⟨i.val, by omega⟩ from Fin.ext h]
    exact hF r (Sum.inr (Sum.inl i))
  · rw [show j = ⟨ρ, by omega⟩ from Fin.ext h]
    refine (hF r (Sum.inl (Sum.inr ()))).trans (congrArg (s * ·) ?_)
    change (B.d.i₀.map (prH (ofSplit p)) * F₀.β) r (Sum.inr ()) = prH (ofSplit p) (∑ u, B.d.i₀ r u * vecB B.o B.ζ u)
    rw [Matrix.mul_apply, map_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [h₀.2, one_mul, map_mul]; rfl
  · rw [show j = ⟨2 * ρ - i.val, by omega⟩ from Fin.ext (by simp only; omega)]
    exact hF r (Sum.inr (Sum.inr i))

end Local

def PrimCol {S : HSp D} {ρ : ℕ} (L : Lat S) (v : Pl D) (x : Mx D S.rank ρ) (i : Fin ρ) : Prop :=
  ∀ a ∈ idAt D (· = v), colMul x i a ∈ latV S L (· = v) ↔ a ∈ intAt D (· = v)

def AgreeSplit (χ χ' : (AE D)ˣ →* Circle) : Prop :=
  ∀ e, IsSplitIdem D e → ∀ u x : (AE D)ˣ, (x : AE D) = e * u + (1 - e) → χ x = χ' x

def FockMap (ψ : AddChar (AF D.host.F) ℂ) {S T S' T' : HSp D} (LS : Lat S) (LT : Lat T) (LS' : Lat S') (LT' : Lat T')
    (𝔉 : (WO S T → ℂ) → WO S' T' → ℂ) : Prop :=
  ∀ (θ : InfFam D) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) →
    ∃ (sS' BS' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ)
      (sT' BT' : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ),
      (∀ τ, IsCartanInv (gramAt D S' τ) (sS' τ)) ∧ (∀ τ, IsCartanInv (gramAt D T' τ) (sT' τ)) ∧
      (∀ τ, IsONBasis (gramAt D S' τ) (sS' τ) (BS' τ) (pS τ)) ∧ (∀ τ, IsONBasis (gramAt D T' τ) (sT' τ) (BT' τ) (pT τ)) ∧
      (∀ f₀, IsVacO ψ θ S T sS sT (LS : Set _) (LT : Set _) f₀ → IsVacO ψ θ S' T' sS' sT' (LS' : Set _) (LT' : Set _) (𝔉 f₀)) ∧
      ∀ P, ∃ P', ∀ f, IsThetaFunO ψ S T f →
        𝔉 (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S' T' sS' sT' BS' BT' (𝔉 f) P'

open Classical in

def stepDat (c : GlobalTheory.ChainOnto.Com D) (s s' : GlobalTheory.ChainOnto.PiLocalization₂ D) (j : ℕ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (e : AE D) (x : WO s.V s'.V) : ℂ :=
  if IsHalf e x ∧ IsIntM (frMapO s.V s'.V s.β s'.β x) then
    omegaG s.L (c.chi (j + 1)) (fun PP => redM PP (frMapO s.V s'.V s.β s'.β x)) *
      omegaQ ∅ s.L.r ξ 1 (fun PP => redM PP (frMapO s.V s'.V s.β s'.β x))
  else 0

open Classical in
theorem isStepVecOf_iff (c : GlobalTheory.ChainOnto.Com D) (s s' : GlobalTheory.ChainOnto.PiLocalization₂ D) (j : ℕ) (ξ f₀ f) :
    IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (j + 1)) ∅ ξ f₀ f ↔
      IsVacO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ f₀ ∧ ∃ e : AE D, IsIdemSum e (s.L.Pg ∪ ∅) ∧
        IsThetaAt c.ψ (symplO s.V s'.V) (heisO c.ψ s.V s'.V) e (latO s.V s'.V s.Λ s'.Λ fun _ => True) 1 f₀
          (stepDat c s s' j ξ e) f := Iff.rfl

variable {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}
  {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP)

def FrAt (s : GlobalTheory.ChainOnto.PiLocalization₂ D) (j : ℕ) {Y : Type} [Fintype Y] [DecidableEq Y] (γ : Frame G.q s.V Y)
    (L : LatFrame G.k (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j) Y) : Prop :=
  ∃ e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j ≃ Fin s.V.rank, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧
    MovedTo (ofSplit G.q) s.V 1 s.β ((γ.b * L.bas.val).submatrix id fun i => L.ord (e.symm i))

def locLev (j : ℕ) {Y : Type} [Fintype Y] [DecidableEq Y] (L : LatFrame G.k (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j) Y) :
    Subgroup (GL Y G.k) :=
  ((G.S.P.iter (Fin D.R.t) G.S.μ G.S.tame j).toLevel.map L.conj).J

def locPhi (j : ℕ) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (L : LatFrame G.k (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j) Y)
    (L' : LatFrame G.k (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (j + 1)) Y') : Matrix Y' Y G.k → ℂ :=
  L'.transport L (G.S.P.iterPhi (Fin D.R.t) G.S.μ G.S.tame j)

def LevLoc (s : GlobalTheory.ChainOnto.PiLocalization₂ D) (j : ℕ) (A : GA D s.V → Prop) : Prop :=
  ∃ (Y : Type) (_ : Fintype Y) (_ : DecidableEq Y) (γ : Frame G.q s.V Y) (L : LatFrame G.k _ Y),
    FrAt G s j γ L ∧ ∀ g, A g ↔ InAt γ (locLev G j L) g

def StepLoc (s s' : GlobalTheory.ChainOnto.PiLocalization₂ D) (j : ℕ) (R : (WO s.V s'.V → ℂ) → (WO s.V s'.V → ℂ) → Prop) : Prop :=
  ∃ (Y Y' : Type) (_ : Fintype Y) (_ : DecidableEq Y) (_ : Fintype Y') (_ : DecidableEq Y') (γ : Frame G.q s.V Y)
    (γ' : Frame G.q s'.V Y') (L : LatFrame G.k _ Y) (L' : LatFrame G.k _ Y'), FrAt G s j γ L ∧ FrAt G s' (j + 1) γ' L' ∧
      ∀ f₀ f, R f₀ f ↔ Over d.c.ψ γ γ' s.Λ s'.Λ f₀ (locPhi G j L L') f

example (j c : ℕ) (h : j + c = G.s + 1) : ((G.S.T (Fin D.R.t)).lev j c h).J =
    locLev G j (GlobalTheory.StepData.typeFrame G.S.ϖ (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) j c h)) := rfl

example (j c : ℕ) (h : j + c = G.s) : (G.S.T (Fin D.R.t)).Phi j c h =
    locPhi G j (GlobalTheory.StepData.typeFrame G.S.ϖ (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) j (c + 1) (by omega)))
      (GlobalTheory.StepData.typeFrame G.S.ϖ (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) (j + 1) c (by omega))) := rfl

example (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (LS : Lat S) (LT : Lat T) : FockMap ψ LS LT LS LT id :=
  fun _ sS BS sT BT _ _ _ a b c e => ⟨sS, BS, sT, BT, a, b, c, e, fun _ h => h, fun P => ⟨P, fun _ _ => rfl⟩⟩

end GlobalTheory.RouteCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatSchwartzAddSmul
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatAdd

variable {D : D7}

theorem mixS_add {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (T : HSp D) {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)} (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕)
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (x : Mx D T.rank ρ) :
    d.mixS T ψ μ 𝓕 (f + g) x = d.mixS T ψ μ 𝓕 f x + d.mixS T ψ μ 𝓕 g x := by
  funext w₀
  have h1 := d.integrableOn_mixS hψ hμ hf x w₀
  have h2 := d.integrableOn_mixS hψ hμ hg x w₀
  simp only [HypDec.integrandS_eq] at h1 h2
  simp only [HypDec.mixS, Pi.add_apply, HypDec.integrandS_eq]
  rw [← integral_add h1 h2]
  congr 1; funext a; ring

theorem continuous_mixS {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (T : HSp D) {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)} (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : Mx D T.rank ρ) : Continuous (d.mixS T ψ μ 𝓕 f x) := by
  have cY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  have c0 : Continuous (d.ext0 T) := continuous_id.matrix_mul continuous_const
  refine GlobalTheory.MixCont.continuous_covolOne_integral hμ
    (fun (w : WO S₀ T) a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0) ?_
    (fun w γ hγ a => d.integrandS_periodic hf x w γ hγ a)
  have e : Function.uncurry (fun (w : WO S₀ T) a =>
      heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0) =
      fun z => ψ (symplOH S T (d.extY T z.2) (d.extX T x)) * f (d.extY T z.2 + d.extX T x + d.ext0 T z.1) := by
    funext z; exact d.integrandS_eq _ _ _ _
  rw [e]
  exact (hψ.comp (GlobalTheory.OrientedHeis.continuous_symplOH (cY.comp continuous_snd) continuous_const)).mul
    (hf.cont.comp (((cY.comp continuous_snd).add continuous_const).add (c0.comp continuous_fst)))

theorem integrableOn_mixT_of_quasi {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {T T₀ : HSp D} {ρ : ℕ}
    (d : HypDec T T₀ ρ) (S : HSp D) {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) {f : WO S T → ℂ} (hc : Continuous f)
    (hq : ∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w) (y : Mx D S.rank ρ) (w₀ : WO S T₀) :
    IntegrableOn
      (fun ξ => heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0) 𝓕 μ := by
  refine covolOne_integrableOn hμ _ ?_ (GlobalTheory.MixCont.integrandT_periodic_of_quasi d hq y w₀)
  have cX : Continuous (d.incX S) := continuous_const.matrix_mul continuous_id
  simp only [HypDec.integrandT_eq]
  exact (hψ.comp (GlobalTheory.OrientedHeis.continuous_symplOH cX continuous_const)).mul
    (hc.comp ((cX.add continuous_const).add continuous_const))

theorem evalAt_add {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {V V₀ W W₀ : HSp D} {ρ σ : ℕ}
    (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank)
    {f g : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (hg : IsThetaFunO ψ V W g) (x : Mx D W.rank ρ)
    (y : Mx D V₀.rank σ) :
    evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (f + g) x y =
      evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 f x y + evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 g x y := by
  funext w₀
  have h1 := integrableOn_mixT_of_quasi hψ dW V₀ vT.covol (continuous_mixS hψ dV W vS.covol hf x)
    (fun δ w => GlobalTheory.MixModel.Check.mixS_quasi dV vS.μ vS.𝓕 hf x δ w) y w₀
  have h2 := integrableOn_mixT_of_quasi hψ dW V₀ vT.covol (continuous_mixS hψ dV W vS.covol hg x)
    (fun δ w => GlobalTheory.MixModel.Check.mixS_quasi dV vS.μ vS.𝓕 hg x δ w) y w₀
  simp only [HypDec.integrandT_eq] at h1 h2
  simp only [evalAt, mixS_add hψ dV W vS.covol hf hg x, HypDec.mixT, Pi.add_apply, HypDec.integrandT_eq]
  rw [← integral_add h1 h2]
  congr 1; funext a; ring

theorem flatFB_add_smul : ∀ (D : D7), FlatLaw D → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (f g : WO J.W B.V → ℂ),
    IsThetaFunO ψ J.W B.V f → IsThetaFunO ψ J.W B.V g →
    flatFB st (f + g) = flatFB st f + flatFB st g ∧ ∀ a : ℂ, flatFB st (a • f) = a • flatFB st f := by
  intro D hF ψ hψ σ J B st f g hf hg
  refine ⟨?_, fun a => GlobalTheory.HandHom.flatFB_smul st a f⟩
  have hif := (hF ψ hψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d st.vS st.vT st.vU (GlobalTheory.Unf.FlatTheta.lastQ B)
    (GlobalTheory.Unf.FlatTheta.lastQ_indep B) 0 f hf).1
  have hig := (hF ψ hψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d st.vS st.vT st.vU (GlobalTheory.Unf.FlatTheta.lastQ B)
    (GlobalTheory.Unf.FlatTheta.lastQ_indep B) 0 g hg).1
  rw [GlobalTheory.Unf.FlatTheta.rat_lastQ] at hif hig
  funext w
  simp only [flatFB, flatLast, flatAt, Pi.add_apply]
  rw [← integral_add (hif w) (hig w)]
  congr 1; funext u
  simp only [flatFun, evalAt_add hψ.1.1 J.d B.d st.vS st.vT hf hg, Pi.add_apply, mul_add]

end GlobalTheory.FlatAdd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KeepLatticeHyperbolicEmbedding
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RegSch.EmbLevel

open Formalism.UG

section Ring

variable {A B : Type} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {φ : A →+* B}

theorem cT_map (hφ : ∀ x, φ (σ x) = τ (φ x)) {m p : Type} (M : Matrix m p A) :
    (cT σ M).map φ = cT τ (M.map φ) := by
  funext i j
  exact hφ (M j i)

theorem conj_mem_iff {n : ℕ} (b g : GL (Fin n) B) :
    b⁻¹ * g * b ∈ UJ τ (1 : Matrix (Fin n) (Fin n) B) ↔
      cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1 = cT τ (b⁻¹).1 * (b⁻¹).1 := by
  have h1 : b.1 * (b⁻¹).1 = 1 := b.mul_inv
  have h2 : (b⁻¹).1 * b.1 = 1 := b.inv_mul
  have h3 : cT τ (b⁻¹).1 * cT τ b.1 = 1 := by rw [← cT_mul, h1, cT_one]
  have h4 : cT τ b.1 * cT τ (b⁻¹).1 = 1 := by rw [← cT_mul, h2, cT_one]
  change cT τ ((b⁻¹).1 * g.1 * b.1) * 1 * ((b⁻¹).1 * g.1 * b.1) = 1 ↔ _
  have e : cT τ ((b⁻¹).1 * g.1 * b.1) * 1 * ((b⁻¹).1 * g.1 * b.1) =
      cT τ b.1 * (cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1) * b.1 := by
    simp only [cT_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e]
  generalize cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1 = X
  constructor
  · intro h
    calc X = (cT τ (b⁻¹).1 * cT τ b.1) * X * (b.1 * (b⁻¹).1) := by rw [h1, h3, Matrix.one_mul, Matrix.mul_one]
      _ = cT τ (b⁻¹).1 * (cT τ b.1 * X * b.1) * (b⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]
  · rintro rfl
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul, h2]

theorem conj_bc_mem_iff (hφ : ∀ x, φ (σ x) = τ (φ x)) {n : ℕ} (c g : GL (Fin n) A) :
    (bc φ c)⁻¹ * bc φ g * bc φ c ∈ UJ τ (1 : Matrix (Fin n) (Fin n) B) ↔
      (cT σ g.1 * (cT σ (c⁻¹).1 * (c⁻¹).1) * g.1).map φ = (cT σ (c⁻¹).1 * (c⁻¹).1).map φ := by
  rw [conj_mem_iff, ← map_inv]
  simp only [Matrix.map_mul, cT_map hφ]
  rfl

end Ring

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem compInf_sigR (σ : E →ₐ[F] E) (w : InfinitePlace F) (x : AF F ⊗[F] E) :
    compInf F E w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compInf F E w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

omit [NumberField E] in
theorem mem_levelAll_iff (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (c : GL (Fin n) (AF F ⊗[F] E)) (g : GAd σ J) : g ∈ levelAll σ J L c ↔
    (∀ v y, y ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J g).1.map (compFin F E v) *ᵥ y ∈ latLoc F L v) ∧
      ∀ w, (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (GlobalTheory.AdelicU.matHom _ σ J g).1 *
          (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (c⁻¹).1 * (c⁻¹).1) * (GlobalTheory.AdelicU.matHom _ σ J g).1).map (compInf F E w) =
        (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (c⁻¹).1 * (c⁻¹).1).map (compInf F E w) := by
  refine mem_levelAll.trans (and_congr Iff.rfl (forall_congr' fun w => ?_))
  rw [mem_stabArch, matHom_projArch]
  exact conj_bc_mem_iff (compInf_sigR σ w) c _

end Lattice

variable {D : D7}

end GlobalTheory.RegSch.EmbLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LastSeeSaw

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']

def BiForm (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (FA : GlobalTheory.LocMod.Frame k A.rank n')
    (FS : GlobalTheory.LocMod.Frame k S.rank n) (FA' : GlobalTheory.LocMod.Frame k A'.rank n'') (Ξ : SB (Matrix n n' k × Matrix n'' n k))
    (C : WO A S → WO S A' → ℂ) : Prop :=
  ∃ Λ, p.IsBiModel ψ FA FS FA' Λ ∧ C = Λ Ξ

def BiOne (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (FA : GlobalTheory.LocMod.Frame k A.rank n')
    (FS : GlobalTheory.LocMod.Frame k S.rank n) (FA' : GlobalTheory.LocMod.Frame k A'.rank n'') (C : WO A S → WO S A' → ℂ) : Prop :=
  ∃ Λ, p.IsBiModel ψ FA FS FA' Λ ∧ ∃ (O₁ : SB (Matrix n n' k)) (O₂ : SB (Matrix n'' n k))
    (O : SB (Matrix n n' k × Matrix n'' n k)), GlobalTheory.LocMod.IsOne O₁ ∧ GlobalTheory.LocMod.IsOne O₂ ∧
      (∀ q, O.1 q = O₁.1 q.1 * O₂.1 q.2) ∧ C = Λ O

def lastDat {u : D.what₂.Word} (d : Dat D u) {ι : Type} (o : OffDat d k ι) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m)
    (P₁ : Formalism.IndefR.Links.PolF D (d.st (j + 1)).V.rank (d.st j).V.rank)
    (P₂ : Formalism.IndefR.Links.PolF D d.top.st.V.rank (d.st (j + 1)).V.rank) :
    WO (D.sp.X j) (D.sp.X (j + 1)) → WO (D.sp.X (j + 1)) (D.sp.X (j + 1 + 1)) → ℂ :=
  lastBi (d.bes j 0 h).o (d.oT (j + 1 + 1) h) (o.τ j h) (xiBF d j 0 h P₁ 1) (xiTop d j h P₂)

end GlobalTheory.LastSeeSaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelSourceSupportFiniteComponentInBoxStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelSource_support_finiteComponentInBox : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ x w, d.mixS T ψ v.μ v.𝓕 f x w ≠ 0 → InBox K x := by
  first | exact @GlobalTheory.Unf.mixS_support_inBox | exact GlobalTheory.Unf.mixS_support_inBox | (intros; apply GlobalTheory.Unf.mixS_support_inBox <;> assumption)
end

