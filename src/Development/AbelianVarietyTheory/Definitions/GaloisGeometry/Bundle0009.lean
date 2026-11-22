import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
section
noncomputable section

namespace GlobalTheory.ThStr

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField Classical

variable {l : ℕ} [Fact l.Prime]

def laS (l : ℕ) [Fact l.Prime] (d : ℕ) (s : ZMod d) : MvPowerSeries (ZMod d) ℂ_[l] :=
  fun n => ∑ e ∈ Finset.range ((n.sum fun _ k => k) + 1),
    if n = Finsupp.single (s - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e)) then ((l : ℂ_[l]) ^ e)⁻¹ else 0

def laAt {d : ℕ} {κ : Type} (ι : ZMod d → κ) (s : ZMod d) : MvPowerSeries κ ℂ_[l] :=
  MvPowerSeries.subst (fun r : ZMod d => (MvPowerSeries.X (ι r) : MvPowerSeries κ ℂ_[l])) (laS l d s)

def parDeg {d : ℕ} (par : Bool) (n : ZMod d →₀ ℕ) : ℕ :=
  n.sum fun s k => if decide (Even s.val) = par then k else 0

def cobdry {d : ℕ} (par : Bool) (be : MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (Bool × ZMod d) ℂ_[l] :=
  MvPowerSeries.subst (fun s : ZMod d => if decide (Even s.val) = par then
      (laAt (fun r => (false, r)) s + laAt (fun r => (true, r)) s : MvPowerSeries (Bool × ZMod d) ℂ_[l])
      else laAt (fun r => (false, r)) s) be -
    MvPowerSeries.subst (fun s : ZMod d => (laAt (fun r => (false, r)) s : MvPowerSeries (Bool × ZMod d) ℂ_[l])) be -
    MvPowerSeries.subst (fun s : ZMod d => if decide (Even s.val) = par then
      (laAt (fun r => (true, r)) s : MvPowerSeries (Bool × ZMod d) ℂ_[l]) else laAt (fun r => (false, r)) s) be

structure IsBe (d : ℕ) (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop where
  coef : CoefWf be
  inv : ∀ u : ℂ_[l], u ^ (l ^ d - 1) = 1 →
    MvPowerSeries.rescale (fun s : ZMod d => if Even s.val then u ^ (l ^ s.val) else (u ^ (l ^ s.val))⁻¹) be = be
  bideg : ∀ n, MvPowerSeries.coeff n be ≠ 0 →
    parDeg true n ≠ 0 ∧ parDeg false n ≠ 0 ∧ ¬ (parDeg true n = 1 ∧ parDeg false n = 1)
  cob : ∀ par, IntegralW (expMv (cobdry par be))

def FormA {d : ℕ} {V A B : Type} [Fintype V] [Fintype A] [Fintype B] (be : V → MvPowerSeries (ZMod d) ℂ_[l])
    (Th : MvPowerSeries (ZMod d × (V × A × B)) ℂ_[l]) : Prop :=
  IntegralMv (MvPowerSeries.subst
    (fun k : ZMod d × (V × A × B) => (laAt (fun r => (r, k.2)) k.1 : MvPowerSeries (ZMod d × (V × A × B)) ℂ_[l]))
    (Th * expMv (∑ x : V × A × B, MvPowerSeries.subst
      (fun s : ZMod d => (MvPowerSeries.X (s, x) : MvPowerSeries (ZMod d × (V × A × B)) ℂ_[l])) (be x.1))))

def FormB {κ : Type} [Fintype κ] (be : MvPowerSeries (ZMod 2) ℂ_[l]) (Th : MvPowerSeries κ ℂ_[l]) : Prop :=
  IntegralMv (MvPowerSeries.subst
    (fun k : κ => (PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries κ ℂ_[l]) (logF l) : MvPowerSeries κ ℂ_[l]))
    (Th * expMv (MvPowerSeries.C (1 / 2 : ℂ_[l]) * ∑ k : κ, MvPowerSeries.subst
      (fun _ : ZMod 2 => (MvPowerSeries.X k : MvPowerSeries κ ℂ_[l])) be)))

def JetInt {κ : Type} (F : MvPowerSeries κ ℂ_[l]) : Prop :=
  ∀ n : κ →₀ ℕ, ‖(n.prod fun _ k => (k.factorial : ℂ_[l])) * MvPowerSeries.coeff n F‖ ≤ 1

def StrA (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → InertK D p → AllSplit D p →
    ∃ ep : ℂ_[p], ep ∈ Wp p ∧ ‖ep‖ = 1 ∧ ∀ (d : ℕ) [NeZero d] (Po : Pos D p d),
      ∃ be : {v // v ∈ Po.V} → MvPowerSeries (ZMod d) ℂ_[p], (∀ v, IsBe d (be v)) ∧
        ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
          (P : {v // v ∈ Po.V} → Matrix (Fin N) (Fin N) D.host.E) (P' : {v // v ∈ Po.V} → Matrix (Fin N') (Fin N') D.host.E),
          admitted D N N' L L' → (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L (P v)) →
          (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L' (P' v)) →
          ∀ F, IsComb D T e lam L L' F →
            FormA be (atLin (fun k j => ep * chg D lam Po P P' k j) (fun j => MvPowerSeries.X j) F)

def StrB (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → InertK D p → IsFrobC D p →
    ∃ ep : ℂ_[p], ep ∈ Wp p ∧ ‖ep‖ = 1 ∧ ∃ be : MvPowerSeries (ZMod 2) ℂ_[p], IsBe 2 be ∧
      ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
        (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E),
        admitted D N N' L L' → (∀ τ, OrthoBasisW D (tauEmb D lam τ) L (P τ)) → (∀ τ, OrthoBasisW D (tauEmb D lam τ) L' (P' τ)) →
        ∀ F, IsComb D T e lam L L' F →
          FormB be (atLin (fun k j => ep * chgB D lam P P' k j) (fun j => MvPowerSeries.X j) F)

def beTil {d : ℕ} [NeZero d] {ρ : Type} [Fintype ρ] (b0 : MvPowerSeries (Fin 2) ℂ_[l]) (Ni Ni' : ρ → ZMod d → ℂ_[l]) :
    MvPowerSeries (ZMod d) ℂ_[l] :=
  ∑ r : ρ, MvPowerSeries.subst (fun i : Fin 2 => ∑ s : ZMod d,
    (MvPowerSeries.C (if i = 0 then (if Even s.val then Ni r s else 0) else (if Even s.val then 0 else Ni' r s)) *
      MvPowerSeries.X s : MvPowerSeries (ZMod d) ℂ_[l])) b0

def avgT {d : ℕ} (b : MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (ZMod d) ℂ_[l] :=
  MvPowerSeries.C (((l ^ d - 1 : ℕ) : ℂ_[l])⁻¹) * ∑ u ∈ Polynomial.nthRootsFinset (l ^ d - 1) (1 : ℂ_[l]),
    MvPowerSeries.rescale (fun s : ZMod d => if Even s.val then u ^ (l ^ s.val) else (u ^ (l ^ s.val))⁻¹) b

def inT {d : ℕ} (b : MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (ZMod d) ℂ_[l] :=
  MvPowerSeries.subst (fun s : ZMod d => laS l d s) b

end GlobalTheory.ThStr
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
section
noncomputable section

namespace GlobalTheory.ThBe0

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable {l : ℕ} [Fact l.Prime]

def lg {κ : Type} (k : κ) : MvPowerSeries κ ℂ_[l] :=
  PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries κ ℂ_[l]) (logF l)

structure IsFrob (σ : ℂ_[l] →+* ℂ_[l]) : Prop where
  norm_eq : ∀ x, ‖σ x‖ = ‖x‖
  lift : ∀ x ∈ Wp l, ∃ y ∈ Wp l, σ x = x ^ l + (l : ℂ_[l]) * y

def at2 {κ : Type} (b0 : MvPowerSeries (Fin 2) ℂ_[l]) (x y : MvPowerSeries κ ℂ_[l]) : MvPowerSeries κ ℂ_[l] :=
  MvPowerSeries.subst (fun i : Fin 2 => if i = 0 then x else y) b0

structure IsBe0 (σ : ℂ_[l] →+* ℂ_[l]) (b0 : MvPowerSeries (Fin 2) ℂ_[l]) : Prop where
  coef : CoefWf b0
  axes : ∀ n, MvPowerSeries.coeff n b0 ≠ 0 → n 0 ≠ 0 ∧ n 1 ≠ 0
  add₁ : SimeqW (at2 b0 (lg 0 + lg 1) (lg 2) : MvPowerSeries (Fin 3) ℂ_[l]) (at2 b0 (lg 0) (lg 2) + at2 b0 (lg 1) (lg 2))
  add₂ : SimeqW (at2 b0 (lg 0) (lg 1 + lg 2) : MvPowerSeries (Fin 3) ℂ_[l]) (at2 b0 (lg 0) (lg 1) + at2 b0 (lg 0) (lg 2))
  conj : ∀ α ∈ Wp l, σ (σ α) = α →
    SimeqW (at2 b0 (MvPowerSeries.C α * lg 0) (lg 1) : MvPowerSeries (Fin 2) ℂ_[l]) (at2 b0 (lg 0) (MvPowerSeries.C (σ α) * lg 1))

structure DualOm (σ : ℂ_[l] →+* ℂ_[l]) (d : ℕ) {ρ : Type} [Fintype ρ] [DecidableEq ρ] (om om' : ρ → ℂ_[l]) : Prop where
  card : 2 * Fintype.card ρ = d
  mem : ∀ r, om r ∈ Wp l ∧ om' r ∈ Wp l
  fix : ∀ r, (σ ^ d) (om r) = om r ∧ (σ ^ d) (om' r) = om' r
  dual : ∀ r r', ∑ i ∈ Finset.range (d / 2), (σ ^ (2 * i)) (om r * om' r') = if r = r' then 1 else 0

def zOm (σ : ℂ_[l] →+* ℂ_[l]) {d : ℕ} {ρ : Type} [Fintype ρ] (om om' : ρ → ℂ_[l]) (s : ZMod d) : MvPowerSeries (ρ ⊕ ρ) ℂ_[l] :=
  if Even s.val then ∑ r, MvPowerSeries.C ((σ ^ s.val) (om r)) * lg (Sum.inl r)
  else ∑ r, MvPowerSeries.C ((σ ^ s.val) (om' r)) * lg (Sum.inr r)

end GlobalTheory.ThBe0
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MtType
section
noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions NumberField

def MtType {D : D7} (u : D.what₂.Word) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  letI := D.host.cmStar
  ∀ (i : ℕ) (h : i < D.R.m), (∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ mt (i + 1) k ^ n = 1) ∧
    ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hcW u τ).e ⟨i, h⟩) ∧
      ∀ z : unitary D.host.E, ((mt (i + 1) (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ

def MtIs {D : D7} {C : Formalism.L2.Host.CharFrame D} (Dt : Formalism.L2.Host.DtTied D C) {nch : NChoice D}
    (Tp : Formalism.L2.Host.TupTied D C nch) (μ : D.what₂.Tup) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  ∀ (j : Fin D.R.m) a, Formalism.L2.Host.IsFinIdele a → mt (j.1 + 1) (Dt.eDt a) = (Tp.tup μ j).1 a

end GlobalTheory.KerJ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical

namespace GlobalTheory.KerStd

def StdBases (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  (∀ τ, LocBasisW D (tauEmb D lam τ) L (P τ)) ∧
  ((IsResidueClassZero D p ∨ IsSg D p) → ∀ z : Bool × HH D,
    ((P (tauPl D (posPl D p z 1))).map D.host.conj).transpose * P (tauPl D z) = 1) ∧
  (p = D.host.d → DualB D P)

def stdSer (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ} (κ : D.what₂.Tau → ℂ_[p])
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : MvPowerSeries ((Bool × HH D) × Fin N × Fin N') ℂ_[p] :=
  atLin (fun k (j : (Bool × HH D) × Fin N × Fin N') =>
    κ k.1 * chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) (fun j => MvPowerSeries.X j) F

def StdScal (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (s : D.what₂.Tau → ℂ) (κ : D.what₂.Tau → ℂ_[p]) : Prop :=
  (∀ τ, ‖κ τ‖ = ‖lamC lam (s τ)‖) ∧ ((IsResidueClassZero D p ∨ IsSg D p) → ∀ τ, κ τ = 1)

abbrev ThFam (D : D7) : Type :=
  ∀ u μ (w : D.what₂.places.Pl) (i : ℕ), (D.chTw u μ).cls i → (D.chTw u μ).cls (i + 1) →
    MvPowerSeries ((Bool × HH D) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w]

def ThStd {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw)
    (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (Th : ThFam D) : Prop :=
  ∀ u μ w, LevFree Dx u μ w →
    ∃ (P : ∀ i, (D.chTw u μ).cls i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)
      (κ : D.what₂.Tau → ℂ_[D.what₂.places.resChar w]),
      (∀ i, i ≤ D.R.m → ∀ c, StdBases D (E.lam w) ((O u μ).lat i c).1 (P i c)) ∧
      StdScal D (E.lam w) (O u μ).dgen κ ∧
      ∀ i, i < D.R.m → ∀ c c', Th u μ w i c c' =
        stdSer D (E.lam w) κ (P i c) (P (i + 1) c') (pSer D (E.lam w) ((O u μ).Th i c c'))

end GlobalTheory.KerStd
end
end

