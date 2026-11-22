import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.AutomorphicBallCount
section
open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount

open Formalism.MainNotions.S GlobalTheory.Count

def ballSet (I : AutInst) (x : I.GA) (r : InfinitePlace I.F → ℝ) : Set I.GA :=
  {γ | γ ∈ I.GFset ∧ (x⁻¹ * γ * x).2 ∈ I.Kset ∧ ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ r v}

def bigA (I : AutInst) (x : I.GA) : ℝ :=
  (3 * Real.sqrt (I.n : ℝ) / (tau1 I x) ^ 2) ^ (2 * (I.n ^ 2 * I.f))

def AutBallCount : Prop :=
  ∀ (I : AutInst), 1 ≤ I.n → ∀ (x : I.GA) (r : InfinitePlace I.F → ℝ), (∀ v, 0 ≤ r v) →
    (ballSet I x r).Finite ∧
      ((ballSet I x r).ncard : ℝ) ≤ bigA I x * Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v)

end GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
section
open NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets

open Formalism.MainNotions.S GlobalTheory.Count

section Lie

variable {A : Type} [CommRing A] {n : ℕ}

def perpSet (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A)) : Set (Fin n → A) :=
  {y | ∀ w ∈ W, Formalism.UG.hform s J w y = 0}

def IsSkew (s : A →+* A) (J Y : Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ u u' : Fin n → A, Formalism.UG.hform s J (Y *ᵥ u) u' + Formalism.UG.hform s J u (Y *ᵥ u') = 0

def InNil (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A))
    (Y : Matrix (Fin n) (Fin n) A) : Prop :=
  IsSkew s J Y ∧ (∀ u, Y *ᵥ u ∈ perpSet s J W) ∧ (∀ u ∈ perpSet s J W, Y *ᵥ u ∈ W) ∧ ∀ u ∈ W, Y *ᵥ u = 0

def InCen (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A))
    (Y : Matrix (Fin n) (Fin n) A) : Prop :=
  InNil s J W Y ∧ ∀ u ∈ perpSet s J W, Y *ᵥ u = 0

theorem inCen_zero (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A)) :
    InCen s J W 0 := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [IsSkew, perpSet, Formalism.UG.hform]

end Lie

variable (I : AutInst)

def spanAt (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (v : InfinitePlace I.F) : Submodule ℂ (Fin I.n → ℂ) :=
  Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (R : Set _))

def nilReal (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
  {Y | ∀ v, InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) (Y v)}

def cenReal (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
  {Y | ∀ v, InCen (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) (Y v)}

def nilInt (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {Y | InNil (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y ∧
    ∀ u ∈ lamX I x, Y *ᵥ u ∈ lamX I x}

def cenInt (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {Y | InCen (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y ∧
    ∀ u ∈ lamX I x, Y *ᵥ u ∈ lamX I x}

def diagEmb (Y : Matrix (Fin I.n) (Fin I.n) I.E) : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ :=
  fun v => Y.map (I.φ v)

def normAt (x : I.GA) (Y : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) : ℝ :=
  Real.sqrt (∑ v, Formalism.REAL.hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * Y v * I.P v * uMat (x.1 v)))

theorem normAt_zero (x : I.GA) : normAt I x 0 = 0 := by
  simp [normAt, Formalism.REAL.hs]

def nextSize {a : ℕ} (τ : Fin a → ℝ) (i : Fin a) : ℝ :=
  if h : (i : ℕ) + 1 < a then τ ⟨(i : ℕ) + 1, h⟩ else 1 / 2

example : nextSize ![(1 : ℝ) / 8, 1 / 4] 0 = 1 / 4 ∧ nextSize ![(1 : ℝ) / 8, 1 / 4] 1 = 1 / 2 := by
  constructor <;> simp [nextSize]

def CoveringRadii : Prop :=
  ∀ (I : AutInst) (x : I.GA) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ),
    HasFlag I x S τ → ∀ (i : Fin a) (ρ : ℝ), 0 < ρ → τ i ≤ ρ * nextSize τ i → τ i ^ 2 ≤ ρ / 4 →
      (∀ Y ∈ nilReal I (S i.succ), ∃ Y₀ ∈ nilInt I x (S i.succ), ∃ Z ∈ cenReal I (S i.succ),
        normAt I x (Y - diagEmb I Y₀ - Z) ≤
          ((I.n : ℝ) ^ 2 * I.f) / 8 * I.rd * ρ / Real.sqrt (2 * I.f)) ∧
      (∀ Z ∈ cenReal I (S i.succ), ∃ Z₀ ∈ cenInt I x (S i.succ),
        normAt I x (Z - diagEmb I Z₀) ≤ ((I.n : ℝ) ^ 2 * I.f) * I.rd * ρ / (16 * Real.sqrt I.f))

end GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CoveringRadii
section
open NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NilpotentCenteredRadii

open Formalism.MainNotions.S GlobalTheory.Count

section Lie

variable {A : Type} [CommRing A] {n : ℕ}

def InNil (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A))
    (Y : Matrix (Fin n) (Fin n) A) : Prop :=
  Formalism.UG.cT s Y * J + J * Y = 0 ∧
    (∀ y, ∀ w ∈ W, Formalism.UG.hform s J w (Y *ᵥ y) = 0) ∧
    (∀ y, (∀ w ∈ W, Formalism.UG.hform s J w y = 0) → Y *ᵥ y ∈ W) ∧
    ∀ w ∈ W, Y *ᵥ w = 0

def InCen (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A))
    (Y : Matrix (Fin n) (Fin n) A) : Prop :=
  InNil s J W Y ∧ ∀ y, (∀ w ∈ W, Formalism.UG.hform s J w y = 0) → Y *ᵥ y = 0

example (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (W : Submodule A (Fin n → A)) :
    InCen s J W 0 := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have : Formalism.UG.cT s (0 : Matrix (Fin n) (Fin n) A) = 0 := by
      ext i j; simp [Formalism.UG.cT]
    simp [this]
  · intro y w _; simp [Formalism.UG.hform]
  · intro y _; simp
  · intro w _; simp
  · intro y _; simp

end Lie

variable (I : AutInst)

def spanE (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Submodule I.E (Fin I.n → I.E) :=
  Submodule.span I.E (R : Set (Fin I.n → I.E))

def spanAt (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (v : InfinitePlace I.F) : Submodule ℂ (Fin I.n → ℂ) :=
  Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (R : Set (Fin I.n → I.E)))

def nilR (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Set (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
  {Y | ∀ v, InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) (Y v)}

def cenR (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Set (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
  {Y | ∀ v, InCen (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) (Y v)}

def nilO (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {Y | InNil (starRingEnd I.E) I.J (spanE I R) Y ∧ ∀ y ∈ lamX I x, Y *ᵥ y ∈ lamX I x}

def cenO (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Matrix (Fin I.n) (Fin I.n) I.E) :=
  {Y | InCen (starRingEnd I.E) I.J (spanE I R) Y ∧ ∀ y ∈ lamX I x, Y *ᵥ y ∈ lamX I x}

def diagR (Y : Matrix (Fin I.n) (Fin I.n) I.E) : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ :=
  fun v => Y.map (I.φ v)

def normX (x : I.GA) (Y : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) : ℝ :=
  Real.sqrt (∑ v, Formalism.REAL.hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * Y v * I.P v * uMat (x.1 v)))

def nextSize {a : ℕ} (τ : Fin a → ℝ) (i : Fin a) : ℝ :=
  if h : (i : ℕ) + 1 < a then τ ⟨(i : ℕ) + 1, h⟩ else 1 / 2

example (τ : Fin 1 → ℝ) : nextSize τ 0 = 1 / 2 := by simp [nextSize]

example (τ : Fin 2 → ℝ) : nextSize τ 0 = τ 1 := by simp [nextSize]

def CoveringRadii : Prop :=
  ∀ (I : AutInst) (x : I.GA) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ),
    HasFlag I x S τ → ∀ (i : Fin a) (ρ : ℝ), 0 < ρ → τ i ≤ ρ * nextSize τ i → τ i ^ 2 ≤ ρ / 4 →
      (∀ Y ∈ nilR I (S i.succ), ∃ Y₀ ∈ nilO I x (S i.succ), ∃ Z ∈ cenR I (S i.succ),
        normX I x (Y - diagR I Y₀ - Z) ≤
          ((I.n : ℝ) ^ 2 * I.f) / 8 * I.rd * ρ / Real.sqrt (2 * I.f)) ∧
      (∀ Z ∈ cenR I (S i.succ), ∃ Z₀ ∈ cenO I x (S i.succ),
        normX I x (Z - diagR I Z₀) ≤
          ((I.n : ℝ) ^ 2 * I.f) * I.rd * ρ / (16 * Real.sqrt I.f))

end GlobalTheory.IndefiniteRowSideFullHecke.NilpotentCenteredRadii
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CuspidalFrames
section
open MeasureTheory NumberField
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames

open Formalism.MainNotions.S GlobalTheory.Count

def IsCuspidalFrame (B : RowsAut) (Rφ : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
    (T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) : Prop :=
  (∀ i, T i ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧
    (∀ i, T i ∈ B.I.HomS B.σs B.μf B.fund B.R) ∧
    (∀ i u, ‖T i u‖ = ‖u‖) ∧
    (∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0) ∧
    Submodule.span ℂ (Set.range T) = B.I.eHom B.σs B.μf B.fund B.R B.Re ∧
    (∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) ∧
    (∀ i u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T i u) = T i u) ∧
    Orthonormal ℂ (fun i => T i (B.tens B.w)) ∧
    Submodule.span ℂ (Set.range fun i => T i (B.tens B.w)) = LinearMap.range Rφ.toLinearMap

def CuspidalIntertwiners : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (h : ℝ),
    IsDSData B d → SigIs B p q → 1 ≤ min p q → 1 ≤ B.g → GapGe B h →
    40 * (B.I.n : ℝ) ^ 2 * Real.sqrt ((min p q : ℕ) : ℝ) ≤ h →
    16 * (B.I.n : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) < h →
    ∃ Rφ : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund,
      B.I.IsRConv B.μf B.fund B.R (phe B d) Rφ ∧
        ∃ T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), IsCuspidalFrame B Rφ T

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepKernelBound
section
open MeasureTheory NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound

open Formalism.MainNotions.S GlobalTheory.Count

def dimN (B : RowsAut) : ℕ := B.I.n ^ 2 * B.I.f

def stepBe (n : ℕ) (b : ℝ) (P : ℕ) : ℝ :=
  Real.sqrt n * b ^ 2 + 3 / 2 * ((n : ℝ) * Real.sqrt n) + 3 * (P : ℝ)

def radRh (B : RowsAut) (q : ℕ) (τ : ℝ) : ℝ :=
  (B.I.n : ℝ) ^ 2 * Real.sqrt B.I.f * B.g * B.I.rd * (2 * τ) ^ ((1 : ℝ) / q) / 4

def DeepKernelBound : Prop :=
  ∀ (Cg : ℝ) (n₀ : ℕ) (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ)
    (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA),
    0 ≤ Cg → 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b →
    (∀ v, IsGauge (B.I.ε v) (c v)) →
    least B.I x < tauStar B q b →
    (kern B.I (phe B d) x x).re ≤
      (2 * radRh B q (least B.I x) * Real.sqrt B.I.f *
            stepBe B.I.n b (8 * q * dimN B + dimN B)) ^ (16 * q * dimN B) *
        (6 * stepBe B.I.n b (8 * q * dimN B + dimN B)) ^ dimN B *
        Real.exp B.I.f *
        (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * dimN B) *
        (B.D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal

example (n : ℕ) (b : ℝ) {P P' : ℕ} (h : P ≤ P') : stepBe n b P ≤ stepBe n b P' := by
  unfold stepBe
  have : (P : ℝ) ≤ P' := by exact_mod_cast h
  linarith

example : stepBe 4 1 2 = 20 := by
  have : Real.sqrt (4 : ℕ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  unfold stepBe
  rw [this]; norm_num

end GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepSetBound
section
open MeasureTheory NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeepSet

open Formalism.MainNotions.S GlobalTheory.Count

def deepSet (B : RowsAut) (q : ℕ) (b : ℝ) : Set B.I.GA :=
  {x | x ∈ B.fund ∧ least B.I x < tauStar B q b}

def DeepBound : Prop :=
  ∀ Cg : ℝ, 0 ≤ Cg → ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    1 ≤ q → CountHyp B Cg n₀ d p q b →
      ∫⁻ x in deepSet B q b, ENNReal.ofReal (kern B.I (phe B d) x x).re ∂(B.I.muA B.μf) ≤
        ENNReal.ofReal ((B.D : ℝ) * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))))

example (B : RowsAut) (q : ℕ) (b : ℝ) : deepSet B q b ⊆ B.fund := fun _ h => h.1

example (B : RowsAut) (q : ℕ) (b : ℝ) : tauStar B q b = (bigX B b ^ (11 * q))⁻¹ := by
  simp [tauStar]

end GlobalTheory.IndefiniteRowSideFullHecke.DeepSet
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DefiniteFiniteCount
section
open NumberField MeasureTheory

namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount

open Formalism.MainNotions.S GlobalTheory.Count

def DefiniteHyp (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ) : Prop :=
  IsDSData B d ∧ SigIs B p 0 ∧ 1 ≤ p ∧ 1 ≤ B.g ∧ B.g₀.Prime ∧ 4 * B.I.n < B.g₀ ∧
    (Ideal.primesOver (Ideal.span {(B.g₀ : ℤ)}) (𝓞 B.I.E)).ncard = Module.finrank ℚ B.I.E

def DefiniteCount : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ), DefiniteHyp B d p →
    (B.D : ℝ) = mainTerm B d

def DefiniteCountFin : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ), DefiniteHyp B d p →
    FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧
      B.I.muA B.μf B.fund ≠ ⊤ ∧ (B.D : ℝ) = mainTerm B d

theorem DefiniteHyp.rank_eq {B : RowsAut} {d : InfinitePlace B.I.F → ℝ} {p : ℕ}
    (h : DefiniteHyp B d p) : B.I.n = p := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
  obtain ⟨hp, hq⟩ := h.2.1 v
  unfold AutInst.pAt at hp
  unfold AutInst.qAt at hq
  have hall : ∀ a, B.I.ε v a = true := by
    intro a
    by_contra ha
    have hm : a ∈ (Finset.univ.filter fun a => B.I.ε v a = false) := by
      simpa using ha
    rw [Finset.card_eq_zero.mp hq] at hm
    simp at hm
  rw [← hp, Finset.filter_true_of_mem fun a _ => hall a]
  simp

end GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermSum
section
open MeasureTheory NumberField
open scoped ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate

open Formalism.MainNotions.S GlobalTheory.Count

variable (B : RowsAut)

def farSet (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : Set B.I.GA :=
  {γ | γ ∈ B.I.GFset ∧ ¬ IsNear B d (epN B) x γ}

def farSum (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : ℝ≥0∞ :=
  ∑' γ : farSet B d x, ‖phe B d (x⁻¹ * γ.1 * x)‖ₑ

def moderate (q : ℕ) (b : ℝ) : Set B.I.GA :=
  {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x}

def FarModerate : Prop :=
  ∀ Cg : ℝ, 0 ≤ Cg → ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    1 ≤ q → CountHyp B Cg n₀ d p q b →
      ∫⁻ x in moderate B q b, farSum B d x ∂(B.I.muA B.μf) ≤
        ENNReal.ofReal (Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * mainTerm B d)

example (d : InfinitePlace B.I.F → ℝ) (x γ : B.I.GA) (h : γ ∈ farSet B d x)
    (h0 : phe B d (x⁻¹ * γ * x) ≠ 0) : ∃ v, epN B < dHS (uMat ((x⁻¹ * γ * x).1 v)) := by
  by_contra hc
  push Not at hc
  exact h.2 ⟨h.1, h0, hc⟩

example (q : ℕ) (b : ℝ) : moderate B q b ⊆ B.fund := fun _ hx => hx.1

end GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermsLatticeBound
section
open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound

open Formalism.MainNotions.S GlobalTheory.Count

def farSet (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (ep : ℝ) (x : B.I.GA) : Set B.I.GA :=
  {γ | γ ∈ B.I.GFset ∧ ¬ IsNear B d ep x γ}

def latFactor (I : AutInst) (x : I.GA) : ℝ :=
  (3 * Real.sqrt (I.n : ℝ) / tau1 I x ^ 2) ^ (2 * (I.n ^ 2 * I.f))

def FarTermsBound : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (h ep : ℝ),
    IsDSData B d → SigIs B p q → q = min p q → 1 ≤ q → 1 ≤ B.g → GapGe B h →
    0 < ep → ep ≤ 1 / Real.sqrt (2 * (q : ℝ)) → 2 * (B.I.n : ℝ) ^ 2 * ep ≤ Real.log 2 →
    64 * (B.I.n : ℝ) ^ 2 ≤ h * ep → 1 ≤ h * ep ^ 2 / 16 → 8 * (B.I.n : ℝ) * (q : ℝ) < h →
    ∀ x : B.I.GA,
      Summable (fun γ : farSet B d ep x => ‖phe B d (x⁻¹ * γ.1 * x)‖) ∧
      ∑' γ : farSet B d ep x, ‖phe B d (x⁻¹ * γ.1 * x)‖ ≤
        (∏ v, d v) * (B.e 1).re * latFactor B.I x *
          (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * ep ^ 2 / 16)))

example (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (ep : ℝ) (x γ : B.I.GA) (hγ : γ ∈ B.I.GFset) :
    γ ∈ farSet B d ep x ↔
      (phe B d (x⁻¹ * γ * x) = 0 ∨ ∃ v, ep < dHS (uMat ((x⁻¹ * γ * x).1 v))) := by
  simp only [farSet, IsNear, Set.mem_setOf_eq, hγ, true_and, not_and_or, not_not, not_forall, not_le, ne_eq, not_true, false_or]

example : ∃ h ep : ℝ, 0 < ep ∧ ep ≤ 1 / Real.sqrt (2 * ((1 : ℕ) : ℝ)) ∧
    2 * ((2 : ℕ) : ℝ) ^ 2 * ep ≤ Real.log 2 ∧ 64 * ((2 : ℕ) : ℝ) ^ 2 ≤ h * ep ∧ 1 ≤ h * ep ^ 2 / 16 ∧
    8 * ((2 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) < h := by
  refine ⟨10000, 1 / 16, by norm_num, ?_, ?_, by norm_num, by norm_num, by norm_num⟩
  · have h1 : Real.sqrt (2 * ((1 : ℕ) : ℝ)) ≤ 16 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have h2 : 0 < Real.sqrt (2 * ((1 : ℕ) : ℝ)) := Real.sqrt_pos.mpr (by norm_num)
    exact one_div_le_one_div_of_le h2 h1
  · have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith

end GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.LatticeCountingTheorem
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem

open NumberField Formalism.MainNotions.S

def CountingTheorem : Prop :=
  ∀ Cg : ℝ, ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    GlobalTheory.Count.CountHyp B Cg n₀ d p q b →
      FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧
        |(B.D : ℝ) - GlobalTheory.Count.mainTerm B d| ≤
          Real.exp (-(1 / 16 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) *
            GlobalTheory.Count.mainTerm B d

example (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ)
    (h : GlobalTheory.Count.CountHyp B Cg n₀ d p q b) : 0 ≤ Cg := by
  obtain ⟨-, -, -, -, -, -, hb, -, -, hg, hgb, -⟩ := h
  by_contra hC
  have hC' : Cg < 0 := not_le.mp hC
  have h1 : b ^ Cg < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) hC'
  have h2 : (1 : ℝ) ≤ (B.g : ℝ) := by exact_mod_cast hg
  linarith

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.NearNonzeroTerms
section
open MeasureTheory NumberField
open scoped ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms

open Formalism.MainNotions.S GlobalTheory.Count

variable (B : RowsAut)

def moderate (q : ℕ) (b : ℝ) : Set B.I.GA := {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x}

def nearNe (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : Set B.I.GA :=
  {γ | IsNear B d (epN B) x γ ∧ γ ≠ 1}

def nearAbs (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : ℝ≥0∞ :=
  ∑' γ : nearNe B d x, ‖phe B d (x⁻¹ * γ.1 * x)‖ₑ

def nearBound (d : InfinitePlace B.I.F → ℝ) : ℝ :=
  Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) * mainTerm B d

def NearModerate : Prop :=
  ∀ Cg : ℝ, 0 ≤ Cg → ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    1 ≤ q → CountHyp B Cg n₀ d p q b →
      ∫⁻ x in moderate B q b, nearAbs B d x ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (nearBound B d)

theorem nearAbs_eq_zero (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA)
    (h : ∀ γ, IsNear B d (epN B) x γ → γ = 1) : nearAbs B d x = 0 := by
  haveI : IsEmpty (nearNe B d x) := ⟨fun γ => γ.2.2 (h γ.1 γ.2.1)⟩
  simp [nearAbs]

end GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms
end
end

