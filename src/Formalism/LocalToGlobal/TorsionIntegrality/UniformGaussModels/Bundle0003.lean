import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0002

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.PairsK
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer)
open Formalism.G (unitBall)

def pairsK (dK p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Set.range fun mn : ℤ × ℤ =>
    (ι ((mn.1 : ℂ) + (mn.2 : ℂ) * omegaK dK), ι ((mn.1 : ℂ) + (mn.2 : ℂ) * (1 - omegaK dK))))

def CalcP : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
    Formalism.L2.Th1.C.Frame (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) ∧
    Formalism.L2.Th1.C.F1 (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) ∧
    (∀ a b : ℂ_[p], (a, b) ∈ pairsK dK p ι →
      Formalism.L2.Th1.C.EndInt (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) a ∧
      Formalism.L2.Th1.C.PhNormAt (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) a b ∧
      Formalism.L2.Th1.C.AdjAt (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) a b) ∧
    (∀ a : ℂ_[p], (a, a) ∈ pairsK dK p ι → Formalism.L2.Th1.C.IsBinomScalar (unitBall ℂ_[p]) a)

end Formalism.L2.Th1.Top
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementC
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer)
open Formalism.L2.Th1.G (linSub sqSum betaPair)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair jetPairPoly minorProd)

def ShapeOrthD : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
  ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (n : Type) [Fintype n]
    (A : n → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]) (th : ℂ_[p])
    (Q2 : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p]),
    (∀ i x, ‖A i x‖ ≤ 1) → ‖th‖ ≤ ‖(dK : ℂ_[p])‖ ^ (1 / 2 : ℝ) →
    (∀ t, ‖u t‖ ≤ 1) → MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum (fun _ => (1 : ℂ_[p]))) =
      MvPowerSeries.C 2 * betaPair H N0 N1 u + MvPowerSeries.C th * Q2 →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[p]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ p ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    ‖Formalism.L2.Th1.C.jet (logSer (curveL p L ι)) (phC p L ι) 2‖ ≤ ‖(dK : ℂ_[p])‖ ^ (-(1 / 2 : ℝ)) ∧
    ∃ sg : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p], JetsIntegral sg ∧
      linSub A (thetaZ p L ι ω₀ r s) =
        Formalism.DworkPowerSeriesWeights.mvExp ((-(Formalism.L2.Th1.C.jet (logSer (curveL p L ι)) (phC p L ι) 2)) • betaPair H N0 N1 u) * sg

def ThmBOrth : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
  ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (n : Type) [Fintype n]
    (A : n → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]) (th : ℂ_[p])
    (Q2 : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p]),
    (∀ i x, ‖A i x‖ ≤ 1) → ‖th‖ ≤ ‖(dK : ℂ_[p])‖ ^ (1 / 2 : ℝ) →
    (∀ t, ‖u t‖ ≤ 1) → MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum (fun _ => (1 : ℂ_[p]))) =
      MvPowerSeries.C 2 * betaPair H N0 N1 u + MvPowerSeries.C th * Q2 →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[p]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ p ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    ∀ (x : Bool × H → Matrix (Fin N0) (Fin N0) ℂ_[p]), (∀ τ i a, ‖x τ i a‖ ≤ 1) →
      (∀ τ, ‖(x τ).det‖ = 1) →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (ht : ∀ τ, Fin (colN τ) → ℕ)
      (hht : ∀ τ c, ht τ c ≤ N0), (∀ τ c, 1 ≤ ht τ c) → ∀ (I : ∀ τ c, Fin (ht τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ ht τ c)).card) → (∀ τ, size τ = ∑ c, ht τ c) →
      ‖jetPair (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (∑ a, MvPolynomial.C (x τ i a) * MvPolynomial.X (τ, a, b) :
              MvPolynomial ((Bool × H) × Fin N0 × Fin N1) ℂ_[p])) (ht τ) (hht τ) (I τ))
          (linSub A (thetaZ p L ι ω₀ r s))‖ ≤
        ‖(dK : ℂ_[p])‖ ^ (-(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)))

def ThmBGaussOrth : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
  ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (n : Type) [Fintype n]
    (A : n → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]) (th : ℂ_[p])
    (Q2 : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p]),
    (∀ i x, ‖A i x‖ ≤ 1) → ‖th‖ ≤ ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ) →
    (∀ t, ‖u t‖ ≤ 1) → MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum (fun _ => (1 : ℂ_[p]))) =
      MvPowerSeries.C 2 * betaPair H N0 N1 u + MvPowerSeries.C th * Q2 →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[p]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ p ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (ht : ∀ τ, Fin (colN τ) → ℕ)
      (hht : ∀ τ c, ht τ c ≤ N0), (∀ τ c, 1 ≤ ht τ c) → ∀ (I : ∀ τ c, Fin (ht τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ ht τ c)).card) →
      (∀ τ, size τ = ∑ c, ht τ c) →
    ∀ nn : ((Bool × H) × Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff nn (jetPairPoly (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) =>
              (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (τ, i, a)) * MvPolynomial.X (τ, a, b) :
                MvPolynomial ((Bool × H) × Fin N0 × Fin N1)
                  (MvPolynomial ((Bool × H) × Fin N0 × Fin N0) ℂ_[p])))
            (ht τ) (hht τ) (I τ))
          (linSub A (thetaZ p L ι ω₀ r s)))‖ ≤
        ‖(p : ℂ_[p])‖ ^ (-(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)))

def IntOpOrth : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
  ∀ (n : Type) [Fintype n],
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
  ∀ (κ : Type) [Fintype κ] (r : κ → ℂ_[p]) (s : κ → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N →
    ¬ p ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    JetsIntegral (thetaZ p L ι ω₀ r s) ∧
    ∀ P : MvPolynomial n ℂ_[p], (∀ m, ‖MvPolynomial.coeff m P‖ ≤ 1) →
      ‖jetPair P (thetaZ p L ι ω₀ r s)‖ ≤ 1

end Formalism.L2.Th1.Top
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementM
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy)
open Formalism.L2.Th1.E (IntCurve curveL)

def GoodModelUniform : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → HasCMBy dK L →
    ∃ (c : ℂ) (hc : c ≠ 0), ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ι : ℂ ≃+* ℂ_[p],
      IntCurve (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι)

def ThetaZScale : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p]) (c : ℂ) (hc : c ≠ 0) (ω₀ : ℂ),
    ω₀ / 2 ∉ L.lattice →
  ∀ (κ n : Type) [Fintype κ] [Fintype n] (r : κ → ℂ_[p]) (s : κ → n → ℂ),
    MvPowerSeries.rescale (fun _ : n => ι c)
        (thetaZ p (Formalism.L2.Th1.F.scalePair L c hc) ι (c * ω₀) r (fun k i => c * s k i)) =
      thetaZ p L ι ω₀ r s

end Formalism.L2.Th1.Top
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelCondition
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def IsUnitaryK {K : Type} [NormedField K] (σ : K →+* K) {m : Type} [Fintype m] [DecidableEq m]
    (γ : Matrix m m K) : Prop :=
  (∀ a b, ‖γ a b‖ ≤ 1 ∧ σ (σ (γ a b)) = γ a b) ∧
  (∀ a b, ∑ k, σ (γ k a) * γ k b = if a = b then 1 else 0)

def phL (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) : PowerSeries ℂ_[l] :=
  PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)

def inHyp (l : ℕ) [Fact l.Prime] {E n : Type} [Fintype E] [Fintype n] (f f' : E → n → MaximalUnramifiedExtension l)
    (Θ : MvPowerSeries n ℂ_[l]) : MvPowerSeries (Bool × E) ℂ_[l] :=
  MvPowerSeries.subst
    (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[l] l) (expF ℂ_[l] l) (MaximalUnramifiedExtension l).subtype f f') Θ

def uniformGaussModelCondition (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {n : Type} [Fintype n]
    (Θ : MvPowerSeries n ℂ_[l]) (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) : Prop :=
  Formalism.L2.Th1.E.ThetaFourthTensorPowerProductShape (lgF ℂ_[l] l) (expF ℂ_[l] l) (phL l g2 g3 s2 ε) (MaximalUnramifiedExtension l).subtype Θ γ

def uniformGaussModelConditionReformulated : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l →
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (Θ : MvPowerSeries n ℂ_[l])
    (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)), IsUnitaryK σ γ → uniformGaussModelCondition l g2 g3 s2 ε Θ γ →
    Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) * Θ)

def HypShape : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l →
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) →
  ∀ (N0 N1 : ℕ) (ιr : Type) [Fintype ιr] [DecidableEq ιr] (n : Type) [Fintype n]
    (f f' : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ Θ : MvPowerSeries n ℂ_[l],
    Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) * Θ) →
    ∃ U0 Φ : MvPowerSeries (Bool × ιr × Fin N0 × Fin N1) ℂ_[l], Integral U0 ∧
      MvPowerSeries.constantCoeff Φ = 0 ∧
      Simeq Φ (sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l g2 g3 s2 ε)))) ∧
      inHyp l f f' Θ = Formalism.DworkPowerSeriesWeights.mvExp (-Φ) * U0

end Formalism.L2.Th1.Top
end
end

