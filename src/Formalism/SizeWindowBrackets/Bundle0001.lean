import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Lattice.Fold

-- bundled from Formalism.SizeWindowBrackets.ClaimGaFree
section
namespace Formalism.LFunctionChainParameters.UnitWeightPartition

open Finset

noncomputable section

variable {ι κ : Type*} [DecidableEq ι]

def sgw (J : Finset κ) (gain F E : κ → ι → ℝ) (w : ι) : ℝ :=
  ∑ j ∈ J, (gain j w + F j w - E j w)

def Ga (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain : κ → ι → ℝ) (tau : ι → ℝ) : ℝ :=
  2 * ∑ w ∈ W, l w * ((∑ j ∈ J, gain j w) - tau w)

def Fo (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (F : κ → ι → ℝ) : ℝ :=
  2 * ∑ j ∈ J, ∑ w ∈ W, l w * F j w

def Ee (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (E : κ → ι → ℝ) : ℝ :=
  2 * ∑ j ∈ J, ∑ w ∈ W, l w * E j w

def Sg (W : Finset ι) (l s tau : ι → ℝ) : ℝ :=
  ∑ w ∈ W, 2 * l w * (s w - tau w)

def Ta (W : Finset ι) (l tau : ι → ℝ) : ℝ :=
  2 * ∑ w ∈ W, l w * tau w

def IO (W : Finset ι) (l io : ι → ℝ) : ℝ :=
  ∑ w ∈ W, 2 * l w * io w

def be (du : ℝ) (len tau : ι → ℝ) (w : ι) : ℝ :=
  (len w - du * tau w) / du

def BeSum (W : Finset ι) (l : ι → ℝ) (du : ℝ) (len tau : ι → ℝ) : ℝ :=
  ∑ w ∈ W, 2 * l w * be du len tau w

def ClaimSg (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau : ι → ℝ) : Prop :=
  Sg W l (sgw J gain F E) tau = Ga W J l gain tau + Fo W J l F - Ee W J l E

def ClaimGaFree (W Z : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain1 gain2 : κ → ι → ℝ)
    (tau1 tau2 : ι → ℝ) : Prop :=
  (∀ w ∈ W, w ∉ Z → (∀ j ∈ J, gain1 j w = gain2 j w) ∧ tau1 w = tau2 w) →
  (∀ w ∈ W, w ∈ Z → (∀ j ∈ J, gain1 j w = 0 ∧ gain2 j w = 0) ∧ tau1 w = 0 ∧ tau2 w = 0) →
  Ga W J l gain1 tau1 = Ga W J l gain2 tau2

def ClaimUnit (W : Finset ι) (P : Finset ℕ) (pr : ι → ℕ) (l io : ι → ℝ) (iop : ℕ → ℝ) :
    Prop :=
  (∀ w ∈ W, pr w ∈ P) →
  (∀ p ∈ P, ∑ w ∈ W.filter (fun w => pr w = p), l w = Real.log (p : ℝ)) →
  (∀ w ∈ W, io w = iop (pr w)) →
  IO W l io = 2 * ∑ p ∈ P, Real.log (p : ℝ) * iop p

def ClaimDe (f : ℕ) (T dM du : ℝ) : Prop :=
  0 < dM → 2 < T → du = dM * (1 - 1 / (T - 1)) ^ f →
  du = (1 - (1 - du / dM)) * dM ∧ 0 ≤ 1 - du / dM ∧ 1 - du / dM < 1 ∧
    1 - du / dM ≤ 2 * (f : ℝ) / T

def ClaimT (WT : Finset ι) (l len : ι → ℝ) (dM du de lam T : ℝ) : Prop :=
  (∀ w ∈ WT, 0 ≤ l w) → 0 < dM → 0 ≤ de → de ≤ 1 / 2 → du = (1 - de) * dM → 0 ≤ lam →
  (∀ w ∈ WT, len w ≤ dM * lam) → ∑ w ∈ WT, l w = Real.log T →
  ∑ w ∈ WT, 2 * l w * len w / du ≤ 4 * lam * Real.log T

def HypLow (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ) : Prop :=
  (∀ w ∈ W, 0 ≤ l w) ∧ 0 < dM ∧ 0 ≤ de ∧ de < 1 ∧ du = (1 - de) * dM ∧ WT ⊆ W ∧
  (∀ w ∈ WT, tau w = 0) ∧ (∀ w ∈ W, 0 ≤ io w) ∧
  (∀ w ∈ W \ WT, len w ≤ dM * (tau w + io w)) ∧
  ∑ w ∈ WT, 2 * l w * len w / du ≤ PT ∧
  ∑ w ∈ W, 2 * l w * (sgw J gain F E w - sg' w) ≤ Rd ∧
  muN = muMu + Sg W l sg' tau - BeSum W l du len tau

def ClaimLow (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ) : Prop :=
  HypLow W WT J l gain F E tau io len sg' dM du de muMu muN PT Rd →
  muMu + Ga W J l gain tau + Fo W J l F - Ee W J l E - Rd - PT - IO W l io / (1 - de)
      - de / (1 - de) * Ta W l tau ≤ muN

def HypLow2 (W : Finset ι) (l tau io : ι → ℝ) (f T de b muM muMu IOp PT LT Rd RX : ℝ) :
    Prop :=
  muMu = muM - f * Real.log (T - 1) / (T - 2) ∧ de ≤ 2 * f / T ∧ 2 * f / T ≤ 1 / 2 ∧
  (∀ w ∈ W, 0 ≤ tau w) ∧ Ta W l tau ≤ b ^ 2 ∧
  4 * f / T * b ^ 2 + f * Real.log (T - 1) / (T - 2) ≤ 1 ∧
  IO W l io = 2 * IOp ∧ PT ≤ LT ∧ Rd ≤ RX

def ClaimLow2 (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ)
    (f T b muM IOp LT RX : ℝ) : Prop :=
  HypLow W WT J l gain F E tau io len sg' dM du de muMu muN PT Rd →
  HypLow2 W l tau io f T de b muM muMu IOp PT LT Rd RX →
  muM + Ga W J l gain tau + Fo W J l F - Ee W J l E - (4 * IOp + LT + RX + 1) ≤ muN

def HypHigh (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau sg' : ι → ℝ) (muMaxM muMaxMu muMaxN : ℝ) : Prop :=
  (∀ w ∈ W, 0 ≤ l w) ∧ (∀ w ∈ W, sg' w ≤ sgw J gain F E w) ∧
  muMaxN ≤ muMaxMu + Sg W l sg' tau ∧ muMaxMu ≤ muMaxM

def ClaimHigh (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau sg' : ι → ℝ) (muMaxM muMaxMu muMaxN : ℝ) : Prop :=
  HypHigh W J l gain F E tau sg' muMaxM muMaxMu muMaxN →
  muMaxN ≤ muMaxM + Ga W J l gain tau + Fo W J l F - Ee W J l E

end

end Formalism.LFunctionChainParameters.UnitWeightPartition
end

-- bundled from Formalism.SizeWindowBrackets.CutFailsForRSubmodule
section
namespace Formalism.LFunctionChainParameters.DiagonalSublatticeLength

open scoped Pointwise

section defs

variable {R K W : Type*} [CommRing R] [Field K] [Algebra R K] [AddCommGroup W] [Module K W] [Module R W]
  [IsScalarTower R K W]

def latV (M : Submodule R W) (V : Submodule K W) : Submodule R W :=
  M ⊓ V.restrictScalars R

def cutN (ϖ : R) (τ : ℕ) (M N : Submodule R W) (V : Submodule K W) : Submodule R W :=
  N ⊓ ϖ ^ τ • M ⊓ V.restrictScalars R

end defs

def LemmaC : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
  ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (W : Type) [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W] [FiniteDimensional K W]
    (d : ℕ) (M : Submodule R W) (b : Module.Basis (Fin d) R M), Submodule.span K (M : Set W) = ⊤ →
  ∀ (e : Fin d → ℕ) (N : Submodule R W), N = Submodule.span R (Set.range fun i => ϖ ^ e i • (b i : W)) →
  ∀ (τ : ℕ) (V : Submodule K W),
    cutN ϖ τ M N V ≤ ϖ ^ τ • latV M V ∧
    (ϖ ^ τ • M) ⊓ V.restrictScalars R = ϖ ^ τ • latV M V ∧
    Module.length R (latV M V ⧸ (cutN ϖ τ M N V).comap (latV M V).subtype) ≤
      ((Module.finrank R (latV M V) * τ + ∑ i, (e i - τ) : ℕ) : ℕ∞)

def ClaimC : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
  ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (W : Type) [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W] [FiniteDimensional K W]
    (d : ℕ) (M : Submodule R W) (b : Module.Basis (Fin d) R M), Submodule.span K (M : Set W) = ⊤ →
  ∀ (e : Fin d → ℕ) (N : Submodule R W), N = Submodule.span R (Set.range fun i => ϖ ^ e i • (b i : W)) →
  ∀ (τ : ℕ) (V : Submodule K W),
    Module.length R ((ϖ ^ τ • latV M V : Submodule R W) ⧸
        (cutN ϖ τ M N V).comap (ϖ ^ τ • latV M V : Submodule R W).subtype) ≤ ((∑ i, (e i - τ) : ℕ) : ℕ∞) ∧
    Module.length R (latV M V ⧸ (ϖ ^ τ • latV M V).comap (latV M V).subtype) =
      ((Module.finrank R (latV M V) * τ : ℕ) : ℕ∞)

def CutFailsForRSubmodule : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
  ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K],
    let M : Submodule R K := Submodule.span R {1}
    let V : Submodule R K := Submodule.span R {algebraMap R K ϖ}
    ϖ • M ⊓ V ≠ ϖ • (M ⊓ V)

end Formalism.LFunctionChainParameters.DiagonalSublatticeLength
end

-- bundled from Formalism.SizeWindowBrackets.RealSlopeBoundsSplit
section
namespace Formalism.LFunctionChainParameters.WeightedMeanLemmas

open Finset

noncomputable section

def wmean {ι : Type*} [Fintype ι] (d X : ι → ℝ) : ℝ :=
  (∑ u, d u * X u) / ∑ u, d u

def umax {ι : Type*} [Fintype ι] [Nonempty ι] (X : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty X

def sF {ι : Type*} [Fintype ι] (d muN h : ι → ℝ) : ℝ :=
  wmean d (fun u => muN u - h u)

def uF {ι : Type*} [Fintype ι] [Nonempty ι] (d muMaxN muN h : ι → ℝ) : ℝ :=
  umax (fun u => muMaxN u - h u) - sF d muN h

def Slopes2 {ι : Type*} (muMaxN muN muMaxM muM dr BE : ι → ℝ) (Sg0 : ℝ) : Prop :=
  (∀ u, muMaxN u ≤ muMaxM u + (Sg0 - dr u)) ∧ (∀ u, muN u = muM u + (Sg0 - dr u) - BE u)

def Slopes2ge {ι : Type*} (muMaxN muN muMaxM muM dr BE : ι → ℝ) (Sg0 : ℝ) : Prop :=
  (∀ u, muMaxN u ≤ muMaxM u + (Sg0 - dr u)) ∧ (∀ u, muM u + (Sg0 - dr u) - BE u ≤ muN u)

def rhsU {ι : Type*} [Fintype ι] [Nonempty ι] (d muMaxM muM h dr BE : ι → ℝ) : ℝ :=
  umax (fun u => muMaxM u - h u) - wmean d (fun u => muM u - h u) + wmean d (fun u => dr u + BE u)

def LemmaU (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE : ι → ℝ) (Sg0 : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2 muMaxN muN muMaxM muM dr BE Sg0 →
    uF d muMaxN muN h ≤ rhsU d muMaxM muM h dr BE

def LemmaUge (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE : ι → ℝ) (Sg0 : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 →
    uF d muMaxN muN h ≤ rhsU d muMaxM muM h dr BE

def LemmaUNeedsDr : Prop :=
  ¬ ∀ (d muMaxN muN muMaxM muM h dr BE : Unit → ℝ) (Sg0 : ℝ),
    (∀ u, 0 < d u) → Slopes2 muMaxN muN muMaxM muM dr BE Sg0 →
    uF d muMaxN muN h ≤ rhsU d muMaxM muM h dr BE

def LemmaUSharp : Prop :=
  ∃ (d muMaxN muN muMaxM muM h dr BE : Bool → ℝ) (Sg0 : ℝ),
    (∀ u, 0 < d u) ∧ (∀ u, 0 ≤ dr u) ∧ (∀ u, 0 < BE u) ∧ (∃ u, 0 < dr u) ∧
    Slopes2 muMaxN muN muMaxM muM dr BE Sg0 ∧
    uF d muMaxN muN h = rhsU d muMaxM muM h dr BE

def RealSlopeBounds (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE : ι → ℝ) (Sg0 A A' V : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 →
    (∀ u, muMaxM u ≤ A) → (∀ u, -A' ≤ muM u) → (∀ u u', |h u - h u'| ≤ V) →
    uF d muMaxN muN h ≤ A + A' + V + wmean d (fun u => dr u + BE u)

def RealSlopeBoundsSplit (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE lT : ι → ℝ) (Sg0 A A' sa V1 Lk : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 →
    (∀ u, muMaxM u ≤ A) → (∀ u, -A' ≤ muM u) →
    (∀ u u', |(h u + sa * lT u) - (h u' + sa * lT u')| ≤ V1) →
    (∀ u u', |lT u - lT u'| ≤ Lk) →
    uF d muMaxN muN h ≤ A + A' + (V1 + |sa| * Lk) + wmean d (fun u => dr u + BE u)

end

end Formalism.LFunctionChainParameters.WeightedMeanLemmas
end

-- bundled from Formalism.SizeWindowBrackets.TraceSquareAndDiagBounds
section
open Matrix
open scoped ComplexOrder

namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare

noncomputable section

def hsSq {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖ ^ 2

def hsNorm {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : ℝ :=
  Real.sqrt (hsSq M)

section Family

variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}

def Kp (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (u u' : ι) :
    Matrix (Fin (d u)) (Fin (d u')) ℂ :=
  ((Real.sqrt (ga u * ga u') : ℝ) : ℂ) • ((B u)ᴴ * B u')

def Kd (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (u : ι) :
    Matrix (Fin (d u)) (Fin (d u)) ℂ :=
  Kp B ga u u

def Qm (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ u, ((ga u : ℝ) : ℂ) • (B u * (B u)ᴴ)

def Rs (d : ι → ℕ) : ℝ := ∑ u, (d u : ℝ)

def F1 (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (η : ℝ) : Prop :=
  (Qm B ga * Qm B ga).trace.re ≤ (1 + η) * (Qm B ga).trace.re ^ 2 / (D : ℝ)

def F2 (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (e : ℝ) : Prop :=
  ∑ u, hsSq (Kd B ga u - 1) ≤ e * Rs d

def InputS (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (Dstar η0 η1 e0 : ℝ) : Prop :=
  (∀ u u', u ≠ u' → hsSq (Kp B ga u u') ≤ (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar) ∧
  (∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) ∧
  (D : ℝ) ≤ (1 + η1) * Dstar

def Isom {r : ι → ℕ} (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) : Prop :=
  ∀ u, (V u)ᴴ * V u = 1

def Bram {r : ι → ℕ} (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) : ∀ u, Matrix (Fin D) (Fin (r u)) ℂ :=
  fun u => B u * V u

end Family

def TraceIdentities : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ), (∀ u, 0 ≤ ga u) →
    (Qm B ga).trace = ∑ u, (Kd B ga u).trace ∧
    (Qm B ga).trace = (((∑ u, (Kd B ga u).trace.re : ℝ)) : ℂ) ∧
    (Qm B ga * Qm B ga).trace = (((∑ u, ∑ u', hsSq (Kp B ga u u') : ℝ)) : ℂ)

def TraceLower : Prop :=
  ∀ (n : ℕ) (K : Matrix (Fin n) (Fin n) ℂ),
    (n : ℝ) - Real.sqrt n * hsNorm (K - 1) ≤ K.trace.re

def CorBounds : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (Dstar η0 η1 e0 : ℝ),
    (∀ u, 0 ≤ ga u) → 0 < Dstar → -1 ≤ η0 → 0 ≤ e0 → InputS B ga Dstar η0 η1 e0 →
    (Qm B ga * Qm B ga).trace.re
        ≤ (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * Rs d ∧
    (1 - Real.sqrt e0) * Rs d ≤ (Qm B ga).trace.re

def TraceSquareAndDiagBounds : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (ga : ι → ℝ) (Dstar sg η0 η1 e0 : ℝ),
    (∀ u, 0 ≤ ga u) → 0 < Dstar → 0 < sg → sg ≤ 1 / 4 → Dstar / sg ≤ Rs d →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    InputS B ga Dstar η0 η1 e0 →
    F1 B ga (5 * sg) ∧ F2 B ga e0 ∧ e0 ≤ 1 / 4

def RamCompress : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d r : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ),
    Isom V → ∀ u,
    Kd (Bram B V) ga u = (V u)ᴴ * Kd B ga u * V u ∧
    hsNorm (Kd (Bram B V) ga u - 1) ≤ hsNorm (Kd B ga u - 1)

def RamLoewner : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d r : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ),
    Isom V → (∀ u, 0 ≤ ga u) →
    (Qm (Bram B V) ga).PosSemidef ∧ (Qm B ga - Qm (Bram B V) ga).PosSemidef

def RamTrace : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d r : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ) (de e0 : ℝ),
    Isom V → (∀ u, 0 ≤ ga u) → 0 ≤ de → 0 ≤ e0 →
    (∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) →
    ∑ u, ((d u : ℝ) - (r u : ℝ)) ≤ de * Rs d →
    (Qm B ga).trace.re - (de + Real.sqrt (de * e0)) * Rs d ≤ (Qm (Bram B V) ga).trace.re

def CompressDiagDefectBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d r : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ) (de e0 : ℝ),
    Isom V → de ≤ 1 / 2 → 0 ≤ e0 →
    (∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) →
    ∑ u, ((d u : ℝ) - (r u : ℝ)) ≤ de * Rs d →
    (1 - de) * Rs d ≤ Rs r ∧ F2 (Bram B V) ga (2 * e0)

def CompressTraceSquareBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (D : ℕ) (d r : ι → ℕ) (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ)
    (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ) (ga : ι → ℝ) (Dstar sg η0 η1 e0 de : ℝ),
    Isom V → (∀ u, 0 ≤ ga u) → 0 < Dstar → 0 < sg → sg ≤ 1 / 20 → Dstar / sg ≤ Rs d →
    -1 ≤ η0 → η0 ≤ sg / 2 → η1 ≤ sg / 2 → 0 ≤ e0 → Real.sqrt e0 ≤ sg / 2 →
    0 ≤ de → de ≤ 1 / 4 → ∑ u, ((d u : ℝ) - (r u : ℝ)) ≤ de * Rs d →
    InputS B ga Dstar η0 η1 e0 →
    F1 (Bram B V) ga (5 * sg + 3 * Real.sqrt de)

end

end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
end

