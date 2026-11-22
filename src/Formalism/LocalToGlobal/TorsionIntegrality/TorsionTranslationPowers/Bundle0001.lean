import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementT
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0004
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0004
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementA
section
open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

section An

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])

def curveL : WeierstrassCurve ℂ_[l] := Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃)

open Classical in

def ptOf (t : ℂ) : (curveL l L ι).toAffine.Point :=
  if h : t ∉ L.lattice ∧
      (curveL l L ι).toAffine.Nonsingular (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2)
  then .some _ _ h.2 else 0

def phL : PowerSeries ℂ_[l] :=
  Formalism.L2.Th1.B.phO (ι (Formalism.L2.Th1.F.s2 L)) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.pSeries L))
    (Formalism.L2.Th1.A.logSer (curveL l L ι))

def inU (f : ℂ → ℂ) : PowerSeries ℂ_[l] :=
  (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0 f)).subst (Formalism.L2.Th1.A.logSer (curveL l L ι))

def gT (t : ℂ) : PowerSeries ℂ_[l] :=
  Formalism.L2.Th1.B.fExp (phL l L ι) * inU l L ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L))

def phPrime (t₀ : ℂ) : PowerSeries ℂ_[l] :=
  -Formalism.L2.Th1.B.fLog (inU l L ι (Formalism.L2.Th1.F.th0 L t₀))

end An

open Classical in

def PtOfAdd : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (s t : ℂ),
    ptOf l L ι (s + t) = ptOf l L ι s + ptOf l L ι t

def PtOfZero : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (t : ℂ), ptOf l L ι t = 0 ↔ t ∈ L.lattice

def TorsionIntegral : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K), IntCurve W →
    ∀ (P : W.toAffine.Point) (N : ℕ), ‖(N : K)‖ = 1 → N • P = 0 → P ≠ 0 → ‖px W P‖ ≤ 1 ∧ ‖py W P‖ ≤ 1

def WpBridge : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]),
    Formalism.L2.Th1.A.wpReg (curveL l L ι) = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.pSeries L)

def TransWpBridge : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (t : ℂ), t ∉ L.lattice →
    inU l L ι (fun z => L.weierstrassP (z + t)) = xT (curveL l L ι) (ptOf l L ι t)

open Classical in

def AnalyticSys : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (π : ℂ →+ (curveL l L ι).toAffine.Point), (∀ t, π t = ptOf l L ι t) →
    IsTransSys (curveL l L ι) π (gT l L ι)

def AnalyticTrans : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]), IntCurve (curveL l L ι) →
    ∀ (t : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
      ‖ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0)‖ = 1 ∧
      OneUnit (C (ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0))⁻¹ * gT l L ι t)

def OpUTh0Root : Prop :=
  ∀ (L : PeriodPair) (t t₀ : ℂ) (N : ℕ), 0 < N → (N : ℂ) * t ∈ L.lattice → (N : ℂ) * t₀ ∈ L.lattice →
    t₀ ∉ L.lattice → ∃ (ζ : ℂ) (m : ℕ), 0 < m ∧ ζ ^ m = 1 ∧
      Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.th0 L t₀) =
        fun z => ζ * (Formalism.L2.Th1.F.opU L t₀ (Formalism.L2.Th1.F.sgStar L) 0)⁻¹ *
          Formalism.L2.Th1.F.opU L (t + t₀) (Formalism.L2.Th1.F.sgStar L) z

def ThetaZeroAnalytic : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]), l ≠ 2 → IntCurve (curveL l L ι) →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
      Formalism.InvariantFactorPaths.G7.Simeq (ι := Unit) (phL l L ι) (phPrime l L ι (ω₀ / 2)) ∧
      ∀ (t : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * t ∈ L.lattice →
        GaussOne (Formalism.L2.Th1.B.fExp (phL l L ι) *
          inU l L ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))

def PtOfInt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]), IntCurve (curveL l L ι) →
    ∀ (t : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
      ‖px (curveL l L ι) (ptOf l L ι t)‖ ≤ 1 ∧ ‖py (curveL l L ι) (ptOf l L ι t)‖ ≤ 1

def KernelPtInt : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy d L →
    ∀ (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]), IntCurve (curveL l L ι) →
    ∀ (a b : ℤ) (t : ℂ), ((a : ℂ) + (b : ℂ) * Formalism.L2.Th1.CM.omegaK d) * t ∈ L.lattice →
      ¬ (l : ℤ) ∣ a ^ 2 + a * b + b ^ 2 * (((d : ℤ) + 1) / 4) → t ∉ L.lattice →
      ‖px (curveL l L ι) (ptOf l L ι t)‖ ≤ 1 ∧ ‖py (curveL l L ι) (ptOf l L ι t)‖ ≤ 1

end Formalism.L2.Th1.E
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementP
section
open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq cob IsLawOfLog lgF UnrOK)

section Prod

variable {K : Type} [Field K]

def phSum {n : Type} [Fintype n] (ph : PowerSeries K) : MvPowerSeries n K := ∑ i, at1 i ph

def thetaProd {κ n : Type} [Fintype κ] [Fintype n] (r : κ → K) (H : κ → n → PowerSeries K) :
    MvPowerSeries n K :=
  ∑ k, MvPowerSeries.C (r k) * ∏ i, at1 i (H k i)

def hypCoord {O ι n : Type} [Semiring O] [Fintype ι] (l linv : PowerSeries K) (τ : O →+* K) (f f' : ι → n → O) (i : n) :
    MvPowerSeries (Bool × ι) K :=
  Formalism.L2.Th1.C.flin l linv (Sum.elim (fun e => τ (f e i)) (fun e => τ (f' e i)))
    (Sum.elim (fun e => (MvPowerSeries.X (false, e) : MvPowerSeries (Bool × ι) K))
      (fun e => MvPowerSeries.X (true, e)))

def beSum {ι : Type} [Fintype ι] (l linv ph : PowerSeries K) : MvPowerSeries (Bool × ι) K :=
  ∑ e, Formalism.L2.Th1.C.be0 l linv ph (MvPowerSeries.X (false, e)) (MvPowerSeries.X (true, e))

end Prod

def ProdInt : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (κ n : Type) [Fintype κ] [Fintype n]
    (ph : PowerSeries K) (r : κ → K) (V : κ → n → PowerSeries K),
    constantCoeff ph = 0 → (∀ k, ‖r k‖ ≤ 1) → (∀ k i, IntS (V k i)) →
      thetaProd r (fun k i => (mvExp (-ph) : PowerSeries K) * V k i) =
          mvExp (-(phSum ph : MvPowerSeries n K)) * thetaProd r V ∧
        Integral (thetaProd r V)

def SubstExpInt : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (n m : Type) [Fintype n]
    (φ : n → MvPowerSeries m K), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → (∀ i, Integral (φ i)) →
    ∀ Φ U : MvPowerSeries n K, MvPowerSeries.constantCoeff Φ = 0 → Integral U →
      MvPowerSeries.subst φ (mvExp (-Φ) * U) =
          mvExp (-(MvPowerSeries.subst φ Φ)) * MvPowerSeries.subst φ U ∧
        Integral (MvPowerSeries.subst φ U) ∧ MvPowerSeries.constantCoeff (MvPowerSeries.subst φ Φ) = 0

def CongIffSimeq : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (R : Subring K),
    (∀ a, a ∈ R ↔ ‖a‖ ≤ 1) → ∀ (σ : Type) (f g : MvPowerSeries σ K),
      Formalism.L2.Th1.C.Cong R f g ↔ Simeq f g

def IntHyp : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (R : Subring K),
    (∀ a, a ∈ R ↔ ‖a‖ ≤ 1) → ∀ (l linv ph : PowerSeries K), Formalism.L2.Th1.C.Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, Formalism.L2.Th1.C.EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → Formalism.L2.Th1.C.IsBinomScalar R (τ z)) →
    Formalism.L2.Th1.C.F1 R l linv ph →
    (∀ α : O, Formalism.L2.Th1.C.PhNormAt R l linv ph (τ α) (τ (star α))) →
    (∀ α : O, Formalism.L2.Th1.C.AdjAt R l linv ph (τ α) (τ (star α))) →
    ∀ (n ι : Type) [Fintype n] [Fintype ι] [DecidableEq ι] (f f' : ι → n → O),
    (∀ e e', ∑ i, star (f e i) * f e' i = 0) → (∀ e e', ∑ i, star (f' e i) * f' e' i = 0) →
    (∀ e e', ∑ i, star (f e i) * f' e' i = if e = e' then 1 else 0) →
    ∀ (κ : Type) [Fintype κ] (r : κ → K) (V : κ → n → PowerSeries K),
      (∀ k, ‖r k‖ ≤ 1) → (∀ k i, IntS (V k i)) →
      ∃ U0 Φ : MvPowerSeries (Bool × ι) K, Integral U0 ∧ MvPowerSeries.constantCoeff Φ = 0 ∧
        Simeq Φ (beSum l linv ph) ∧
        MvPowerSeries.subst (hypCoord l linv τ f f')
            (thetaProd r (fun k i => (mvExp (-ph) : PowerSeries K) * V k i)) = mvExp (-Φ) * U0

def SumEBridge : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (l linv : PowerSeries K), Formalism.L2.Th1.C.IsLogPair l linv →
    ∀ F : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff F = 0 → cob F l = 0 →
    ∀ (ph : PowerSeries K) (ι : Type) [Fintype ι] (N0 N1 : ℕ),
      (Formalism.L2.Th1.D.sumE (cob F ph) : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K) =
        beSum l linv ph

def MapCob : Prop :=
  ∀ (K0 K : Type) [Field K0] [Field K] (j : K0 →+* K) (F : MvPowerSeries (Fin 2) K0) (f : PowerSeries K0),
    MvPowerSeries.constantCoeff F = 0 →
      MvPowerSeries.map j (cob F f) = cob (MvPowerSeries.map j F) (PowerSeries.map j f)

def IntThetaZ : Prop :=
  ∀ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [NormedField K]
    [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d] (σ : K0 →+* K0) (j : K0 →+* K),
    UnrOK K0 l σ → (∀ a, ‖j a‖ = ‖a‖) → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog l F → ∀ ph0 : PowerSeries K0, constantCoeff ph0 = 0 →
    Formalism.L2.Th1.D.F1 F (cob F ph0) → Formalism.L2.Th1.D.F2 l σ (cob F ph0) →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K0), Formalism.L2.Th1.D.OwOK d σ om oms →
      Formalism.L2.Th1.D.TrDual d σ om oms → ∀ ζ : K0, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ (R : Subring K), (∀ a, a ∈ R ↔ ‖a‖ ≤ 1) →
    Formalism.L2.Th1.C.Frame R (lgF K l) (Formalism.L2.Th1.D.expF K l) (PowerSeries.map j ph0) →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, Formalism.L2.Th1.C.EndInt R (lgF K l) (Formalism.L2.Th1.D.expF K l) (τ α)) →
    (∀ z : O, star z = z → Formalism.L2.Th1.C.IsBinomScalar R (τ z)) →
    Formalism.L2.Th1.C.F1 R (lgF K l) (Formalism.L2.Th1.D.expF K l) (PowerSeries.map j ph0) →
    (∀ α : O, Formalism.L2.Th1.C.PhNormAt R (lgF K l) (Formalism.L2.Th1.D.expF K l) (PowerSeries.map j ph0)
      (τ α) (τ (star α))) →
    (∀ α : O, Formalism.L2.Th1.C.AdjAt R (lgF K l) (Formalism.L2.Th1.D.expF K l) (PowerSeries.map j ph0)
      (τ α) (τ (star α))) →
    ∀ (n : Type) [Fintype n] (f f' : ι × Fin N0 × Fin N1 → n → O),
    (∀ e e', ∑ i, star (f e i) * f e' i = 0) → (∀ e e', ∑ i, star (f' e i) * f' e' i = 0) →
    (∀ e e', ∑ i, star (f e i) * f' e' i = if e = e' then 1 else 0) →
    ∀ (κ : Type) [Fintype κ] (r : κ → K) (V : κ → n → PowerSeries K),
      (∀ k, ‖r k‖ ≤ 1) → (∀ k i, IntS (V k i)) →
      ∃ U : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K, Integral U ∧
        ∀ g : Formalism.DworkPowerSeriesWeights.ZV d N0 N1 → MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K,
          (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
          (∀ y, MvPowerSeries.subst g (Formalism.DworkPowerSeriesWeights.entLog (K := K) l y) = MvPowerSeries.X y) →
          Formalism.L2.Th1.D.thetaInZ l j σ om oms
                    (MvPowerSeries.subst (hypCoord (lgF K l) (Formalism.L2.Th1.D.expF K l) τ f f')
                      (thetaProd r (fun k i => (mvExp (-(PowerSeries.map j ph0)) : PowerSeries K) * V k i))) =
            Formalism.DworkPowerSeriesWeights.thetaZ g U (-1) (MvPowerSeries.map j (Formalism.L2.Th1.D.beMean l σ (cob F ph0) om oms ζ))

end Formalism.L2.Th1.E
end
end

