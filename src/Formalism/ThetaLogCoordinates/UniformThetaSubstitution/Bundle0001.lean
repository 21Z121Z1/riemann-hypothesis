import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementC
import Formalism.GaussJetBounds.Statement

-- bundled from Formalism.ThetaLogCoordinates.UniformThetaSubstitution.EdgeExponent
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

def EdgeExponent : Prop :=
  ∀ (ι : Type) (Ev Od : Finset ι) (lam : ι → ℕ → ℤ) (wj X : ι → ℤ) (i : ℕ),
    NprimeZ Ev Od lam wj i + ∑ s ∈ Ev, ((i : ℤ) * wj s - X s) + ∑ s ∈ Od, (X s - (i : ℤ) * wj s) =
      ∑ s ∈ Od, X s + ∑ s ∈ Ev, (∑ a ∈ Icc 1 i, (lam s a + wj s) - X s)

def EdgeNonneg : Prop :=
  ∀ (μ : YoungDiagram) (B : Type) [DecidableEq B] (I : ℕ → Finset B) (J : Finset B),
    (∀ c, (I c).card = μ.colLen c) →
    ∑ c ∈ range (μ.rowLen 0), (I c ∩ J).card ≤ ∑ a ∈ range J.card, μ.rowLen a

end Formalism.InvariantFactorPaths.G7
end
end

-- bundled from Formalism.ThetaLogCoordinates.UniformThetaSubstitution.HeckeOneLift
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

def HeckeOneLift : Prop :=
  ∀ (K X X' Fn V V' : Type) [Field K] [AddCommGroup Fn] [Module K Fn] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (Q N g : ℕ) (up dn : ℕ → X → Finset X)
    (dn' : ℕ → X' → Finset X') (kk : X → X' → Fn) (sv : X → X' → K) (abelian₂ : Fn →ₗ[K] (V →ₗ[K] V'))
    (ε : X → K) (ε' : X' → K) (a b : K) (cs : (X → V') →ₗ[K] V') (Forms : Set (X → V)),
    (Q : K) ≠ 0 → b ≠ 0 →
    (∀ L L' j, ∑ L1 ∈ dn' j L', kk L L1 = ∑ l ∈ range (j + 1),
      (((Q ^ 2) ^ ((j - l) * (g - l)) * Formalism.G0.gaussBinom (Q ^ 2) g l : ℕ) : K) •
        ∑ L1 ∈ up (j - l) L, kk L1 L') →
    (∀ L L' j, ∀ L1 ∈ dn' j L', sv L L1 = (Q : K) ^ (j * N) * sv L L' ∧ ε' L1 = a ^ j * ε' L') →
    (∀ L L' i, ∀ L1 ∈ up i L, sv L1 L' = (Q : K) ^ (i * (N + g)) * sv L L' ∧ ε L1 = b ^ i * ε L) →
    (∀ i L', ∀ F ∈ Forms,
      cs (fun L => ∑ L1 ∈ up i L, (ε L1 * ε' L' * sv L1 L') • abelian₂ (kk L1 L') (F L)) =
        cs (fun L1 => (ε L1 * ε' L' * sv L1 L') • abelian₂ (kk L1 L') (∑ L ∈ dn i L1, F L))) →
    ∀ F ∈ Forms, ∀ (i : ℕ) (L' : X'),
      ((Q : K) ^ (-((i : ℤ) * ((N : ℤ) + g - i)))) •
          ∑ L1 ∈ dn' i L', cs (fun L => (ε L * ε' L1 * sv L L1) • abelian₂ (kk L L1) (F L)) =
        (a / b) ^ i • ∑ l ∈ range (i + 1), eF (fun x => b * beFam (Q : K) g x) l •
          cs (fun L => (ε L * ε' L' * sv L L') • abelian₂ (kk L L')
            (((Q : K) ^ (-(((i - l : ℕ) : ℤ) * ((N : ℤ) - (i - l : ℕ))))) • ∑ L0 ∈ dn (i - l) L, F L0))

def ThmCiUnits : Prop :=
  ∀ (K ι : Type) [Field K] (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (Kk : ∀ i, M i →ₗ[K] M (i + 1)) (Tm : ∀ j, ℕ → Module.End K (M j)) (pp : K) (ν k t r j : ℕ)
    (Ev Od : Finset ι) (lam : ι → ℕ → ℤ) (w : ℕ → ι → ℤ) (m u : ℕ → K),
    pp ≠ 0 → r ≤ k → (∀ a, u a ≠ 0) →
    (∀ a, a < j → ∀ i : ℕ,
      (((pp ^ ν) ^ (-((i : ℤ) * ((NN k t (a + 1) : ℤ) - i)))) • Tm (a + 1) i).comp (Kk a) =
        (u (a + 1) ^ i) • (Kk a).comp
          (∑ l ∈ range (i + 1), eF (fun x => m (a + 1) * beFam (pp ^ ν) (t + 1) x) l •
            (((pp ^ ν) ^ (-(((i - l : ℕ) : ℤ) * ((NN k t a : ℤ) - (i - l : ℕ))))) • Tm a (i - l)))) →
    (Zop pp ν Ev Od lam w (fun l => (∏ a ∈ Icc 1 (l - 1), u a)⁻¹ * m l) k t r j
        (fun i => ((∏ a ∈ Icc 1 j, u a) ^ i)⁻¹ • Tm j i)).comp (Kc Kk j) =
      pp ^ (PrZ Od lam (w j) k r j t ν) • (Kc Kk j).comp (pp ^ (ArZ Ev Od lam k r) • Tm 0 r)

def ThmCiiiMulti : Prop :=
  ∀ (K Pl H V : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq Pl] [CommRing H]
    [Algebra K H] [SeminormedAddCommGroup V] [IsUltrametricDist V] [NormedSpace K V] [Module H V]
    [IsScalarTower K H V] (p : ℝ) (B : Finset Pl) (r : Pl → ℕ) (cc : Pl → ℕ → K)
    (Tt : Pl → ℕ → H) (g A : Pl → ℝ) (rest : ℝ) (x : V),
    1 < p → (∀ v ∈ B, ∀ l, l ≤ r v → ‖cc v l‖ ≤ 1) → (∀ v ∈ B, ‖cc v (r v)‖ ≤ p ^ (-(A v))) →
    (∀ L : Pl → ℕ, (∀ v ∈ B, L v ≤ r v) →
      ‖(∏ v ∈ B, Tt v (r v - L v)) • x‖ ≤
        p ^ (-(∑ v ∈ B, (if L v = r v then g v - A v else g v) + rest))) →
    ‖(∏ v ∈ B, ∑ l ∈ range (r v + 1), ((-1 : K) ^ l * cc v l) • Tt v (r v - l)) • x‖ ≤
      p ^ (-(∑ v ∈ B, g v + rest))

def ScaleHomog : Prop :=
  ∀ (K V V' : Type) [NormedField K] [SeminormedAddCommGroup V] [NormedSpace K V]
    [SeminormedAddCommGroup V'] [NormedSpace K V'] (T : V →ₗ[K] V') (ρ : ℝ),
    (∃ c : K, 1 < ‖c‖) → (∀ G : V, ∃ c : K, ‖c‖ = ‖G‖) → (∀ G : V, ‖G‖ ≤ 1 → ‖T G‖ ≤ ρ) →
    ∀ G : V, ‖T G‖ ≤ ρ * ‖G‖

end Formalism.InvariantFactorPaths.G7
end
end

-- bundled from Formalism.ThetaLogCoordinates.UniformThetaSubstitution.OddLogRelation
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

def lgF (K : Type) [Field K] (p : ℕ) : PowerSeries K :=
  PowerSeries.mk fun n => ∑ j ∈ range (n + 1), if n = (p ^ 2) ^ j then ((p : K) ^ j)⁻¹ else 0

def g0F (K : Type) [Field K] (p : ℕ) : PowerSeries K :=
  PowerSeries.mk fun n =>
    ∑ j ∈ range (n + 1), if n = p * (p ^ 2) ^ j then ((p : K) ^ (j + 1))⁻¹ else 0

def Aser (K : Type) [Field K] (p : ℕ) : MvPowerSeries (Fin 2) K :=
  fun n => ∑ i ∈ range (n 0 + 1), ∑ j ∈ range (n 1 + 1),
    if i ≤ j ∧ n 0 = (p ^ 2) ^ i ∧ n 1 = p * (p ^ 2) ^ j then ((p : K) ^ (i + j + 1))⁻¹ else 0

def Aser' (K : Type) [Field K] (p : ℕ) : MvPowerSeries (Fin 2) K :=
  fun n => ∑ i ∈ range (n 1 + 1), ∑ j ∈ range (n 0 + 1),
    if i ≤ j ∧ n 1 = (p ^ 2) ^ i ∧ n 0 = p * (p ^ 2) ^ j then ((p : K) ^ (i + j + 1))⁻¹ else 0

def Gser {K : Type} [Field K] (p : ℕ) (c c' : K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.C c * Aser K p - MvPowerSeries.C c' * Aser' K p

def at1 {K ι : Type} [Field K] (x : ι) (f : PowerSeries K) : MvPowerSeries ι K :=
  PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries ι K) f

def frobVar {K ι : Type} [Field K] (p : ℕ) (f : MvPowerSeries ι K) : MvPowerSeries ι K :=
  MvPowerSeries.subst (fun i => (MvPowerSeries.X i : MvPowerSeries ι K) ^ p) f

def OddLogRelation : Prop :=
  ∀ (K : Type) [Field K] (p : ℕ), 2 ≤ p → (p : K) ≠ 0 →
    g0F K p = PowerSeries.C ((p : K)⁻¹) *
        (PowerSeries.subst (PowerSeries.X ^ p : PowerSeries K) (lgF K p) : PowerSeries K) ∧
      (PowerSeries.subst (PowerSeries.X ^ p : PowerSeries K) (g0F K p) : PowerSeries K) =
        lgF K p - PowerSeries.X

def IdentityB : Prop :=
  ∀ (K : Type) [Field K] (p : ℕ), 2 ≤ p → (p : K) ≠ 0 →
    frobVar p (Aser K p) =
        MvPowerSeries.C (p : K) * (at1 0 (g0F K p) * at1 1 (lgF K p) - Aser' K p) ∧
      frobVar p (Aser' K p) =
        MvPowerSeries.C (p : K) * (at1 0 (lgF K p) * at1 1 (g0F K p) - Aser K p)

def FrobExprG : Prop :=
  ∀ (K : Type) [Field K] (p : ℕ) (c c' : K), 2 ≤ p → (p : K) ≠ 0 →
    frobVar p (Gser p c' c) - MvPowerSeries.C (p : K) * Gser p c c' =
      MvPowerSeries.C (p : K) *
        (MvPowerSeries.C c' * (at1 0 (g0F K p) * at1 1 (lgF K p)) -
          MvPowerSeries.C c * (at1 0 (lgF K p) * at1 1 (g0F K p)))

def ValTable : Prop :=
  ∀ (p i j : ℕ), 2 ≤ p → i ≤ j →
    (j = 0 → (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ j) / ((p : ℝ) ^ 2 - 1) - (i + j + 1) =
      1 / ((p : ℝ) - 1) - 1) ∧
    (1 ≤ j → 1 / ((p : ℝ) - 1) + p - 2 ≤
      (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ j) / ((p : ℝ) ^ 2 - 1) - (i + j + 1))

def PiFactorial : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (p : ℕ) (ϖ : K), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) →
    ∀ i : ℕ, ‖ϖ ^ ((p + 1) * i) / (i.factorial : K)‖ ≤ 1

def ExpIntegral : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ →
    ∀ f : MvPowerSeries ι K, MvPowerSeries.constantCoeff f = 0 →
      (∀ n, ‖MvPowerSeries.coeff n f‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))) → Integral (mvExp f)

def InClass {K ι : Type} [NormedField K] (pp : K) (hh F : MvPowerSeries ι K) : Prop :=
  ∃ U : ℕ → MvPowerSeries ι K, (∀ i, Integral (U i)) ∧
    ∀ n : ι →₀ ℕ, MvPowerSeries.coeff n F =
      ∑ i ∈ range (n.degree + 1), (pp ^ i)⁻¹ * MvPowerSeries.coeff n (hh ^ i * U i)

def ClassChange : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] (pp : K), pp ≠ 0 → ‖pp‖ ≤ 1 →
    ∀ hh Y F : MvPowerSeries ι K, MvPowerSeries.constantCoeff hh = 0 →
      MvPowerSeries.constantCoeff Y = 0 → Integral Y →
      InClass pp hh F → InClass pp (hh + MvPowerSeries.C pp * Y) F

def ClassMul : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] (pp : K)
    (hh F V : MvPowerSeries ι K), MvPowerSeries.constantCoeff hh = 0 → Integral V →
    InClass pp hh F → InClass pp hh (F * V)

def ClassSubst : Prop :=
  ∀ (K ι κ : Type) [Finite ι] [NormedField K] [IsUltrametricDist K] (pp : K)
    (hh F : MvPowerSeries ι K) (φ : ι → MvPowerSeries κ K),
    MvPowerSeries.constantCoeff hh = 0 →
    (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → (∀ i, Integral (φ i)) →
    InClass pp hh F → InClass pp (MvPowerSeries.subst φ hh) (MvPowerSeries.subst φ F)

def ClassExp : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p : ℕ) (ϖ : K), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) →
    ∀ hh : MvPowerSeries ι K, MvPowerSeries.constantCoeff hh = 0 →
      InClass (p : K) hh (mvExp (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hh)))

def Gtot {K E : Type} [Field K] [Fintype E] (p : ℕ) (c c' ϖ : K) : MvPowerSeries (Bool × E) K :=
  ∑ e : E, MvPowerSeries.subst
    (fun a : Fin 2 => MvPowerSeries.C ϖ *
      (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) : MvPowerSeries (Bool × E) K))
    (Gser p c c')

def hh1 {K E : Type} [Field K] [Fintype E] (p : ℕ) (c c' : K) : MvPowerSeries (Bool × E) K :=
  ∑ e : E, (MvPowerSeries.C c * MvPowerSeries.X (false, e) * MvPowerSeries.X (true, e) ^ p -
    MvPowerSeries.C c' * MvPowerSeries.X (false, e) ^ p * MvPowerSeries.X (true, e))

def RescaleExact : Prop :=
  ∀ (K E : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [Fintype E] (p : ℕ)
    (c c' ϖ : K), p.Prime → ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) →
    ‖c‖ ≤ 1 → ‖c'‖ ≤ 1 →
    ∃ V : MvPowerSeries (Bool × E) K, Integral V ∧
      mvExp (-(Gtot (E := E) p c c' ϖ)) =
        mvExp (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hh1 (E := E) p c c')) * V

def RescaleCore : Prop :=
  ∀ (K E : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [Fintype E] (p : ℕ)
    (c c' ϖ : K), p.Prime → ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) →
    ‖c‖ ≤ 1 → ‖c'‖ ≤ 1 →
    InClass (p : K) (hh1 (E := E) p c c') (mvExp (-(Gtot (E := E) p c c' ϖ)))

end Formalism.InvariantFactorPaths.G7
end
end

