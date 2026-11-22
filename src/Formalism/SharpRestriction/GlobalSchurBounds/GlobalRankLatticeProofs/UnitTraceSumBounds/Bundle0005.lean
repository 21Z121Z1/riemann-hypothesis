import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0002
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0002
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0011

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AddPtW
section
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions

namespace Formalism.MainNotions.Ext

def PtW {p : ℕ} [Fact p.Prime] {σ : Type} (a : MvPowerSeries σ ℂ_[p]) : Prop :=
  IntegralW a ∧ MvPowerSeries.constantCoeff a = 0

def AddPtW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∀ (σ : Type) (a b : MvPowerSeries σ ℂ_[p]), PtW a → PtW b → PtW (g.add a b)

def MulPtW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → ∀ c : ℂ_[p], IntegralW (g.mulBy c (Xv ()) : MvPowerSeries Unit ℂ_[p]) →
    ∀ (σ : Type) (a : MvPowerSeries σ ℂ_[p]), PtW a → PtW (g.mulBy c a)

def LinPtW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∀ (ι : Type) [Fintype ι] (c : ι → ℂ_[p]), (∀ j, IntegralW (g.mulBy (c j) (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    ∀ (σ : Type) (a : ι → MvPowerSeries σ ℂ_[p]), (∀ j, PtW (a j)) → PtW (g.lin c a)

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CubeIdentityFromAdditionFormula
section
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext.CutA

def UnitTraceSumSecondBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∃ n : MvPowerSeries (Fin 2) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      (Xv 0) ^ 2 * (PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ -
          (Xv 1) ^ 2 * (PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ =
        g.add (Xv 0) (Xv 1) * g.sub (Xv 0) (Xv 1) * n

def CubeIdentityFromAdditionFormula : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 →
    g.add (Xv 0) (Xv 1) * g.sub (Xv 0) (Xv 1) *
        PowerSeries.subst (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) *
        PowerSeries.subst (g.sub (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) =
      ((Xv 0) ^ 2 * (PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ -
          (Xv 1) ^ 2 * (PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹) *
        PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 2 *
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 2 →
    (∃ n : MvPowerSeries (Fin 2) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      (Xv 0) ^ 2 * (PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ -
          (Xv 1) ^ 2 * (PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) g.wq)⁻¹ =
        g.add (Xv 0) (Xv 1) * g.sub (Xv 0) (Xv 1) * n) →
    Simeq (g.phAt (g.add (Xv 0) (Xv 1)) + g.phAt (g.sub (Xv 0) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (2 * g.phAt (Xv 0) + 2 * g.phAt (Xv 1))

end Formalism.MainNotions.Ext.CutA
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CubeOfTwoIdentities
section
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext.CutA

def CubeOfTwoIdentities : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    Simeq (g.phAt (g.add (Xv 0) (Xv 1)) + g.phAt (g.sub (Xv 0) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (2 * g.phAt (Xv 0) + 2 * g.phAt (Xv 1)) →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) + g.phAt (g.sub (Xv 0) (Xv 1)) +
        g.phAt (g.sub (Xv 1) (Xv 2)) + g.phAt (g.sub (Xv 2) (Xv 0)) : MvPowerSeries (Fin 3) ℂ_[p])
      (3 * (g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2))) →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) - g.phAt (g.add (Xv 0) (Xv 1)) -
        g.phAt (g.add (Xv 1) (Xv 2)) - g.phAt (g.add (Xv 2) (Xv 0)) +
        g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0

def PhGramG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok →
    (∀ α ∈ S, α.swap ∈ S) →
    (∀ α ∈ S, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))) →
    (∀ α ∈ S, Simeq (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))) →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) →
    ∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (g.PhOn A)
        (∑ j, MvPowerSeries.C (hP (A j) (A j)).1 * g.phAt (Xv j) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), g.be (g.mulBy (hP (A j) (A j')).1 (Xv j)) (Xv j'))

def GramUnitEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    ∀ (n : ℕ) (de : Fin n → Fin n → ℂ_[p] × ℂ_[p]), (∀ i j, hP (de i) (de j) = if i = j then 1 else 0) →
      (∑ j, MvPowerSeries.C (hP (de j) (de j)).1 * g.phAt (Xv j) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), g.be (g.mulBy (hP (de j) (de j')).1 (Xv j)) (Xv j') :
        MvPowerSeries (Fin n) ℂ_[p]) = ∑ j, g.phAt (Xv j)

def GramIsoEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    ∀ (κ : Type) [Fintype κ] (r : ℕ) (b : Fin r → κ → ℂ_[p] × ℂ_[p]), (∀ e e', hP (b e) (b e') = 0) →
      (∑ j, MvPowerSeries.C (hP (b j) (b j)).1 * g.phAt (Xv j) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), g.be (g.mulBy (hP (b j) (b j')).1 (Xv j)) (Xv j') :
        MvPowerSeries (Fin r) ℂ_[p]) = 0

def PhDualOfGram : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok →
    (∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (g.PhOn A)
        (∑ j, MvPowerSeries.C (hP (A j) (A j)).1 * g.phAt (Xv j) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), g.be (g.mulBy (hP (A j) (A j')).1 (Xv j)) (Xv j'))) →
    ∀ (κ ι : Type) [Fintype κ] [Fintype ι] (b b' : ι → κ → ℂ_[p] × ℂ_[p]), (∀ e k, b e k ∈ S) →
      (∀ e k, b' e k ∈ S) → DualIso b b' →
      Simeq (g.PhOn (Sum.elim b b')) (g.beSum ι)

def JetsHigh : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) - g.phAt (g.add (Xv 0) (Xv 1)) -
        g.phAt (g.add (Xv 1) (Xv 2)) - g.phAt (g.add (Xv 2) (Xv 0)) +
        g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0 →
    ∀ i : ℕ, i ≠ 1 → i ≠ 2 → IsIntP (g.jetPh i)

def JetsOne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → p ≠ 2 →
    Simeq (g.phAt (g.mulBy (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (g.phAt (Xv ())) →
    IsIntP (g.jetPh 1)

def JetsTwo : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (a b : ℂ_[p]), g.Ok →
    Simeq (g.be (g.mulBy a (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (g.be (Xv 0) (g.mulBy b (Xv 1))) →
    IsIntP ((a - b) * g.jetPh 2)

def BeDiagG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok →
    (∀ α ∈ S, α.swap ∈ S) →
    (∀ α ∈ S, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, ∃ n : ℤ_[p], α.1 + α.2 = zc n) →
    Simeq (g.phAt (g.mulBy 2 (Xv ())) : MvPowerSeries Unit ℂ_[p]) (MvPowerSeries.C (2 * 2) * g.phAt (Xv ())) →
    (∀ α ∈ S, Simeq (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))) →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) →
    (∀ γ ∈ S, Simeq (2 * g.be (Xv ()) (g.mulBy γ.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (γ.1 + γ.2) * g.be (Xv ()) (Xv ()))) ∧
    Simeq (g.be (Xv ()) (Xv ()) : MvPowerSeries Unit ℂ_[p]) (2 * g.phAt (Xv ()))

end Formalism.MainNotions.Ext.CutA
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EndIntWOf
section
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions

namespace Formalism.MainNotions.Ext

def CoefWfRing : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g : MvPowerSeries σ ℂ_[p]), CoefWf f → CoefWf g →
    CoefWf (f + g) ∧ CoefWf (f - g) ∧ CoefWf (f * g) ∧ ∀ c : ℂ_[p], InWf c → CoefWf (MvPowerSeries.C c * f)

def SubstWf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
    CoefWf f → IntegralW a → MvPowerSeries.constantCoeff a = 0 → CoefWf (PowerSeries.subst a f)

def LogWf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → ModelOverW g.lam g.abelian₂ g.C → CoefWf g.l ∧ CoefWf g.ex

def EndIntWG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → ModelOverW g.lam g.abelian₂ g.C → ∀ α ∈ W2pair p,
    IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]) →
    IntegralW (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])

theorem endIntW_of (H : EndIntWG) (D : D7) (hO : okpInert D) : StatementEndomorphismIntegralWitt D := by
  intro hE p _ cc δ g hA h5 hI hM α hα
  have hp2 : p ≠ 2 := by omega
  have hW : α ∈ W2pair p := by
    rw [← hO p g.lam hp2 hI]
    exact hα
  exact H p g hA.2.2.2.2 hM α hW (hE p cc δ g hA α hα)

def PhEvenG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → (∀ z, sgStar g.abelian₂ (-z) = -sgStar g.abelian₂ z) →
    g.W.a₁ = 0 → g.W.a₃ = 0 →
    (g.mulBy (-1) (Xv ()) : MvPowerSeries Unit ℂ_[p]) = -Xv () ∧
    (g.phAt (-Xv ()) : MvPowerSeries Unit ℂ_[p]) = g.phAt (Xv ())

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IopUnitaryOf
section
open Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions

namespace Formalism.MainNotions.Ext

section Th

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

noncomputable def alG (s A : ℝ) (x : T → I → J → ℂ) : ℂ := (-1 : ℂ) ^ (round (s * (HfG A x x).re))

def ThSpG (s A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)) : Set ((T → I → J → ℂ) → ℂ) :=
  {G | Differentiable ℂ G ∧ ∀ x ∈ La', ∀ z, alG s A x * UG A x G z = G z}

noncomputable def normSqG (A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)) (G : (T → I → J → ℂ) → ℂ) : ℝ :=
  let Fd : Set (T → I → J → ℂ) :=
    Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain La' Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (HfG A z z).re)

noncomputable def IopG (s A : ℝ) (La₁ La₂ : AddSubgroup (T → I → J → ℂ)) (G : (T → I → J → ℂ) → ℂ) :
    (T → I → J → ℂ) → ℂ :=
  fun z => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
    ∑ᶠ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      alG s A ((Quotient.out q : La₂) : T → I → J → ℂ) * UG A ((Quotient.out q : La₂) : T → I → J → ℂ) G z

def GoodLat (s A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)) : Prop :=
  (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ (T → I → J → ℂ)), La' = AddSubgroup.closure (Set.range b)) ∧
  (∀ x ∈ La', ∀ y ∈ La', ∃ n : ℤ, (HfG A x y).im = n) ∧
  (∀ v : T → I → J → ℂ, (∀ x ∈ La', ∃ n : ℤ, (HfG A v x).im = n) → v ∈ La') ∧
  ∀ x ∈ La', ∀ y ∈ La', ∀ n : ℤ, (HfG A x y).im = n → alG s A (x + y) = alG s A x * alG s A y * (-1 : ℂ) ^ n

end Th

def ThetaLineG : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La' : AddSubgroup (T → I → J → ℂ), GoodLat s A La' →
      ∃ G ∈ ThSpG s A La', G ≠ 0 ∧ ∀ F ∈ ThSpG s A La', ∃ c : ℂ, F = fun z => c * G z

def IopUnitaryG : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La₁ La₂ : AddSubgroup (T → I → J → ℂ), GoodLat s A La₁ → GoodLat s A La₂ →
      (La₁.addSubgroupOf La₂).index ≠ 0 → (La₂.addSubgroupOf La₁).index ≠ 0 →
      ∀ th ∈ ThSpG s A La₁,
        IopG s A La₁ La₂ th ∈ ThSpG s A La₂ ∧
        normSqG A La₂ (IopG s A La₁ La₂ th) = normSqG A La₁ th ∧
        IopG s A La₂ La₁ (IopG s A La₁ La₂ th) = th

def GoodLa (D : D7) : Prop :=
  ∀ (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    0 < area (lamOf D cc δ) ∧
    ∀ (N N' : ℕ) (L₁ L₂ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E))
      (L₁' L₂' : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N' → D.host.E)), admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
      GoodLat (Real.sqrt D.host.d / 2) (area (lamOf D cc δ)) (La D (tor0 D cc δ) L₁ L₁') ∧
      ((La D (tor0 D cc δ) L₁ L₁').addSubgroupOf (La D (tor0 D cc δ) L₂ L₂')).index ≠ 0

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ModelShortOf
section
open Formalism.MainNotions.FormalGroupJets

namespace Formalism.MainNotions.Ext

def FunEqAll : Prop := ∀ (l d : ℕ) [Fact l.Prime] [NeZero d], ExistsIntegralAdditionSeries l d

end Formalism.MainNotions.Ext

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions

namespace Formalism.MainNotions.Ext

def BiaddOfCube : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) - g.phAt (g.add (Xv 0) (Xv 1)) -
        g.phAt (g.add (Xv 1) (Xv 2)) - g.phAt (g.add (Xv 2) (Xv 0)) +
        g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0 →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) ∧
    Simeq (g.be (Xv 0) (g.add (Xv 1) (Xv 2)) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 1) + g.be (Xv 0) (Xv 2))

def AddIntG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ∧
    (ModelOverW g.lam g.abelian₂ g.C → IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))

end Formalism.MainNotions.Ext

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

def ShortModel : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ W : WeierstrassCurve ℂ_[p],
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → ‖W.Δ‖ = 1 →
    ∃ C : WeierstrassCurve.VariableChange ℂ_[p],
      (C • W).a₁ = 0 ∧ (C • W).a₂ = 0 ∧ (C • W).a₃ = 0 ∧ IsIntP (C • W).a₄ ∧ IsIntP (C • W).a₆ ∧ ‖(C • W).Δ‖ = 1 ∧
      (W.a₁ ∈ Wp p → W.a₂ ∈ Wp p → W.a₃ ∈ Wp p → W.a₄ ∈ Wp p → W.a₆ ∈ Wp p →
        (C • W).a₄ ∈ Wp p ∧ (C • W).a₆ ∈ Wp p)

def OkpInertG : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]),
    Module.finrank ℚ K = 2 → (∃ x, c x ≠ x) → p ≠ 2 → (Ideal.span {(p : 𝓞 K)}).IsPrime →
    closure (Set.range fun a : 𝓞 K => (τ (a : K), τ (c (a : K)))) = W2pair p

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhNormOfUnits
section
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext.CutA

def PhNormClosed : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (T : Set (ℂ_[p] × ℂ_[p])), g.Ok →
    (∀ α ∈ T, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    (∀ α ∈ T, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))) →
    ∀ α ∈ closure T, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))

def PhNormOfUnits : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok → p ≠ 2 →
    ((2 : ℂ_[p]), (2 : ℂ_[p])) ∈ S → (∀ α ∈ S, α.swap ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) →
    (∀ α ∈ S, ∀ β ∈ S, α * β ∈ S) →
    (∀ α ∈ S, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, ∃ n : ℤ_[p], α.1 + α.2 = zc n) → (∀ α ∈ S, ∃ n : ℤ_[p], α.1 * α.2 = zc n) →
    (∀ α ∈ S, ∃ β ∈ S, ∃ γ ∈ S, ‖β.1‖ = 1 ∧ ‖β.2‖ = 1 ∧ ‖γ.1‖ = 1 ∧ ‖γ.2‖ = 1 ∧ α = β + γ) →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) →
    (∀ α ∈ S, ‖α.1‖ = 1 → ‖α.2‖ = 1 → Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))) →
    ∀ α ∈ S, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))

end Formalism.MainNotions.Ext.CutA
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ReadWHolds
section
namespace Formalism.MainNotions.GL3Theta

theorem readW_holds : readW := expIntegralWitt

end Formalism.MainNotions.GL3Theta
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.SimeqLimit
section
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext.CutA

def SimeqGroup : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g : MvPowerSeries σ ℂ_[p]), Simeq f 0 → Simeq g 0 →
    Simeq (f + g) 0 ∧ Simeq (-f) 0

def SimeqZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : MvPowerSeries σ ℂ_[p]), Simeq f 0 →
    ∀ n : ℤ_[p], Simeq (MvPowerSeries.C (zc n) * f) 0

def SimeqSubst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Fintype σ] [Fintype τ] (f : MvPowerSeries σ ℂ_[p])
    (s : σ → MvPowerSeries τ ℂ_[p]), (∀ i, MvPowerSeries.constantCoeff (s i) = 0) → (∀ i, IntegralMv (s i)) →
    Simeq f 0 → Simeq (MvPowerSeries.subst s f) 0

def SimeqLimit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : ℕ → MvPowerSeries σ ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]),
    (∀ α, Filter.Tendsto (fun k => MvPowerSeries.coeff α (f k)) Filter.atTop (nhds (MvPowerSeries.coeff α F))) →
    (∀ k, Simeq (f k) 0) → Simeq F 0

def SimeqPd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) [DecidableEq σ] (f : MvPowerSeries σ ℂ_[p]), Simeq f 0 →
    ∀ k : σ, IntegralMv (pd k f)

def BiaddZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) →
    ∀ n : ℤ_[p], Simeq (g.be (g.mulBy (zc n) (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (MvPowerSeries.C (zc n) * g.be (Xv 0) (Xv 1))

end Formalism.MainNotions.Ext.CutA
end

