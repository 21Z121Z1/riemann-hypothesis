import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Formalism.ThetaSupremumBounds.StatementE

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
section
open Matrix Complex Filter Topology
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram

open GlobalTheory.HermFrame

variable {n a g : ℕ}

def polydisc (n : ℕ) (ρ : ℝ) : Set (Fin n → ℂ) := {z | ∀ k, ‖z k‖ < ρ}

def punctured (ha : a ≤ n) (ρ : ℝ) : Set (Fin n → ℂ) :=
  {z | z ∈ polydisc n ρ ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0}

def tlog (w : ℂ) : ℝ := -Real.log ‖w‖ / (2 * Real.pi)

structure IsPeriodChart (rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) : Prop where

  rk_le : rk ≤ g

  holo : ∀ j k, DifferentiableOn ℂ (fun z => τ₀ z j k) (polydisc n 1)

  symm : ∀ z ∈ polydisc n 1, (τ₀ z).IsSymm

  psd : ∀ i, ((B i).map (Int.cast : ℤ → ℝ)).PosSemidef

  supp : ∀ i (j k : Fin g), (rk ≤ j.val ∨ rk ≤ k.val) → B i j k = 0

  toric : (((∑ i, B i).map (Int.cast : ℤ → ℝ)).submatrix
    (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef

  abelian : ∀ z ∈ polydisc n 1, (((τ₀ z).map Complex.im).submatrix
    (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef

def period (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (z : Fin n → ℂ) (L : Fin a → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  τ₀ z + ∑ i, (L i / (2 * Real.pi * I)) • (B i).map (Int.cast : ℤ → ℂ)

def imPeriod (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  (τ₀ z).map Complex.im + ∑ i, tlog (z (Fin.castLE ha i)) • (B i).map (Int.cast : ℤ → ℝ)

def hodgeGram (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (imPeriod ha τ₀ B z).map Complex.ofReal

def poincareGram (a : ℕ) (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun k =>
    ((if k.val < a then 1 / (2 * (‖z k‖ ^ 2 * tlog (z k) ^ 2)) else 1 / 2 : ℝ) : ℂ)

def BoundsOn (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ρ c C : ℝ) : Prop :=
  (∀ z ∈ punctured ha ρ, (imPeriod ha τ₀ B z - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) ∧
  (∀ z ∈ punctured ha ρ,
    ((C * (1 + ∑ i : Fin a, tlog (z (Fin.castLE ha i)))) • (1 : Matrix (Fin g) (Fin g) ℝ)
      - imPeriod ha τ₀ B z).PosSemidef) ∧
  OneFormBound (punctured ha ρ) (fun _ => 1) (poincareGram a) (conn (hodgeGram ha τ₀ B)) C ∧
  TwoFormBound (punctured ha ρ) (hodgeGram ha τ₀ B) (poincareGram a) (curv (hodgeGram ha τ₀ B)) C

def HodgeChartBounds : Prop :=
  ∀ (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ), IsPeriodChart rk τ₀ B →
    ∃ ρ c C : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ 0 < c ∧ BoundsOn ha τ₀ B ρ c C

open Matrix Complex Filter Topology in
open scoped ComplexOrder in
variable {n a g : ℕ} in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog_pos {w : ℂ} (h0 : w ≠ 0) (h1 : ‖w‖ < 1) : 0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog w :=
  div_pos (neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr h0) h1)) (by positivity)

open Matrix Complex Filter Topology in
open scoped ComplexOrder in
variable {n a g : ℕ} in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.im_period (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) (L : Fin a → ℂ)
    (hL : ∀ i, exp (L i) = z (Fin.castLE ha i)) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period τ₀ B z L).map Complex.im = _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod ha τ₀ B z := by
  ext j k
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period, _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod, Matrix.map_apply, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply, Complex.add_im, Complex.im_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hL i, _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog, Complex.norm_exp, Real.log_exp]
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [Complex.mul_im, Complex.div_re, Complex.div_im]
  simp [Complex.normSq_apply]
  field_simp

open Matrix Complex Filter Topology in
open scoped ComplexOrder in
variable {n a g : ℕ} in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.conn_hodgeGram {rk : ℕ} (ha : a ≤ n) {τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    {B : Fin a → Matrix (Fin g) (Fin g) ℤ} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B) {z : Fin n → ℂ}
    (hz : z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1) (ξ : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.conn (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B) z ξ =
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B z)⁻¹ * _root_.GlobalTheory.HermFrame.mdel (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B) z ξ := by
  apply _root_.GlobalTheory.HermFrame.conn_eq_of_isSymm
  have hnear : ∀ᶠ x in 𝓝 z, x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1 :=
    Filter.eventually_all.2 fun k =>
      (continuous_apply k).norm.continuousAt.eventually_lt continuousAt_const (hz k)
  filter_upwards [hnear] with x hx
  have hB : ∀ i, ((B i).map (Int.cast : ℤ → ℝ))ᵀ = (B i).map (Int.cast : ℤ → ℝ) := fun i => by
    have := (h.psd i).isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hτ : ((τ₀ x).map Complex.im)ᵀ = (τ₀ x).map Complex.im := by
    rw [← Matrix.transpose_map, (h.symm x hx).eq]
  have hI : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod ha τ₀ B x).IsSymm := by
    unfold Matrix.IsSymm _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod
    rw [Matrix.transpose_add, Matrix.transpose_sum, hτ]
    simp only [Matrix.transpose_smul, hB]
  exact hI.map _

end GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
section
open Matrix Filter Topology
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic

def IsPshE {D : ℕ} (U : Set (Fin D → ℂ)) (v : (Fin D → ℂ) → EReal) : Prop :=
  (∀ z ∈ U, v z ≠ ⊤) ∧ UpperSemicontinuousOn v U ∧ U ⊆ closure {z ∈ U | v z ≠ ⊥} ∧
    ∀ κ : ℝ, ReciprocityTheory.AnForm.A.IsPsh U fun z => (max (v z) ((-κ : ℝ) : EReal)).toReal

section Manifold

variable {D : ℕ} {Y : Type} [TopologicalSpace Y]

def chartPart (A : FinHolAtlas D Y) (j : Fin A.n) (S : Set Y) : Set (Fin D → ℂ) :=
  (A.chart j).target ∩ (A.chart j).symm ⁻¹' S

def IsQuasiPsh (A : FinHolAtlas D Y) (Θ : LocPot Y) (v : Y → EReal) : Prop :=
  ∀ x j, IsPshE (chartPart A j (Θ.U x)) fun z =>
    ((2 * Θ.φ x ((A.chart j).symm z) : ℝ) : EReal) + v ((A.chart j).symm z)

def leviSum (A : FinHolAtlas D Y) (Θ : LocPot Y) (u : Y → ℝ) (x : Y) (j : Fin A.n)
    (z w : Fin D → ℂ) : ℝ :=
  levi (fun z' => 2 * Θ.φ x ((A.chart j).symm z') + u ((A.chart j).symm z')) z w

def SumNonnegOn (A : FinHolAtlas D Y) (Θ : LocPot Y) (u : Y → ℝ) (S : Set Y) : Prop :=
  ∀ x j, ∀ z ∈ chartPart A j (Θ.U x ∩ S), ∀ w, 0 ≤ leviSum A Θ u x j z w

def SumZeroOn (A : FinHolAtlas D Y) (Θ : LocPot Y) (u : Y → ℝ) (S : Set Y) : Prop :=
  ∀ x j, ∀ z ∈ chartPart A j (Θ.U x ∩ S), ∀ w, leviSum A Θ u x j z w = 0

def IsBoundary (A : FinHolAtlas D Y) (L : LocPot Y) (s : Y → Y → ℂ) {m : ℕ}
    (W : Fin m → Set Y) : Prop :=
  IsPotential A L ∧ IsSection A L s ∧ IsSNC A L s (fun _ => 1) W ∧
    ∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1

def opn (s : Y → Y → ℂ) : Set Y := {y | s y y ≠ 0}

def rad (L : LocPot Y) (s : Y → Y → ℂ) (y : Y) : ℝ := Real.exp 1 - 2 * logNormSec L s y

def limsupExt (S : Set Y) (u : Y → ℝ) (y : Y) : EReal :=
  limsup (fun y' => (u y' : EReal)) (𝓝[S] y)

def tnorm (A : FinHolAtlas D Y) (Ω : LocPot Y) (j : Fin A.n) (z ξ : Fin D → ℂ) : ℝ :=
  √(levi (Ω.φ ((A.chart j).symm z) ∘ (A.chart j).symm) z ξ / Real.pi)

def IsFlagBundle (A : FinHolAtlas D Y) {n : ℕ} (U : Y → Set Y)
    (g : Y → Y → Y → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ x, IsOpen (U x) ∧ x ∈ U x) ∧
  (∀ x x' a b, A.HoloOn (U x ∩ U x') fun y => g x x' y a b) ∧
  (∀ x x', ∀ y ∈ U x ∩ U x', ∀ a b, b < a → g x x' y a b = 0) ∧
  (∀ x, ∀ y ∈ U x, g x x y = 1) ∧
  ∀ x x' x'', ∀ y ∈ U x ∩ U x' ∩ U x'', g x x' y * g x' x'' y = g x x'' y

def IsMetricOn (A : FinHolAtlas D Y) (S : Set Y) {n : ℕ} (U : Y → Set Y)
    (g : Y → Y → Y → Matrix (Fin n) (Fin n) ℂ) (H : Y → Y → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ x j, IsPosFrame (chartPart A j (U x ∩ S)) fun z => H x ((A.chart j).symm z)) ∧
  ∀ x x', ∀ y ∈ U x ∩ U x' ∩ S, H x' y = (g x x' y)ᵀ * H x y * (g x x' y)ᴴᵀ

def IsLogPair (A : FinHolAtlas D Y) (Ω L : LocPot Y) (s : Y → Y → ℂ) (μ C : ℝ) {n : ℕ}
    (U : Y → Set Y) (g : Y → Y → Y → Matrix (Fin n) (Fin n) ℂ)
    (H₀ H : Y → Y → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsFlagBundle A U g ∧ IsMetricOn A Set.univ U g H₀ ∧ IsMetricOn A (opn s) U g H ∧
  (∀ x, ∀ y ∈ U x ∩ opn s, ∀ v,
    rad L s y ^ (-μ) * (form (H₀ x y) v v).re ≤ (form (H x y) v v).re ∧
      (form (H x y) v v).re ≤ rad L s y ^ μ * (form (H₀ x y) v v).re) ∧
  ∀ x j, ∀ z ∈ chartPart A j (U x ∩ opn s), ∀ ξ v,
    gnorm (H₀ x ((A.chart j).symm z))
        ((conn (fun z' => H x ((A.chart j).symm z')) z ξ -
          conn (fun z' => H₀ x ((A.chart j).symm z')) z ξ) *ᵥ v) ≤
      C * Real.exp (rad L s ((A.chart j).symm z) / 2) * tnorm A Ω j z ξ *
        gnorm (H₀ x ((A.chart j).symm z)) v

end Manifold

def stepLog {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) : ℝ :=
  Real.log (H.submatrix (Subtype.val : {a : Fin n // a.val < i} → Fin n) Subtype.val).det.re

def fundLog {j k : ℕ} (HW : Matrix (Fin j) (Fin j) ℂ) (Hω : Matrix (Fin k) (Fin k) ℂ) (i : ℕ) : ℝ :=
  if i ≤ j then stepLog HW i else stepLog HW j + stepLog Hω (i - j)

def coeff {N : ℕ} (lam : Fin N → ℝ) (i : Fin N) : ℝ :=
  if h : i.val + 1 < N then lam i - lam ⟨i.val + 1, h⟩ else lam i

def weightDiff {Y Ψ : Type} [Fintype Ψ] {N : ℕ} {j k : Ψ → ℕ}
    (HW₀ HW : ∀ τ, Y → Y → Matrix (Fin (j τ)) (Fin (j τ)) ℂ)
    (Hω₀ Hω : ∀ τ, Y → Y → Matrix (Fin (k τ)) (Fin (k τ)) ℂ)
    (lam : Ψ → Fin N → ℝ) (y : Y) : ℝ :=
  ∑ τ, ∑ i : Fin N, coeff (lam τ) i *
    (fundLog (HW τ y y) (Hω τ y y) (i.val + 1) - fundLog (HW₀ τ y y) (Hω₀ τ y y) (i.val + 1))

def Extension : Prop :=
  ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] (A : FinHolAtlas D Y)
    (L : LocPot Y) (s : Y → Y → ℂ) (m : ℕ) (W : Fin m → Set Y), IsBoundary A L s W →
    ∀ (Θ : LocPot Y) (u : Y → ℝ) (C₁ : ℝ), IsPotential A Θ → A.SmoothOn (opn s) u →
      SumNonnegOn A Θ u (opn s) → (∀ y ∈ opn s, u y ≤ C₁ * Real.log (rad L s y)) →
      (∃ M : ℝ, ∀ y ∈ opn s, u y ≤ M) ∧ (∀ y ∈ opn s, limsupExt (opn s) u y = u y) ∧
        IsQuasiPsh A Θ (limsupExt (opn s) u)

def FlatExtension : Prop :=
  ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] (A : FinHolAtlas D Y)
    (L : LocPot Y) (s : Y → Y → ℂ) (m : ℕ) (W : Fin m → Set Y), IsBoundary A L s W →
    ∀ (Θ : LocPot Y) (u : Y → ℝ) (C₁ : ℝ), IsPotential A Θ → A.SmoothOn (opn s) u →
      SumZeroOn A Θ u (opn s) → (∀ y ∈ opn s, |u y| ≤ C₁ * Real.log (rad L s y)) →
      ∃ u' : Y → ℝ, A.Smooth u' ∧ (∀ y ∈ opn s, u' y = u y) ∧ SumZeroOn A Θ u' Set.univ

def GradientBound : Prop :=
  ∀ (D : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] (A : FinHolAtlas D Y)
    (L : LocPot Y) (s : Y → Y → ℂ) (m : ℕ) (W : Fin m → Set Y), IsBoundary A L s W →
    ∀ (Ω : LocPot Y), IsPotential A Ω → IsPosPot A Ω →
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (j k : Ψ → ℕ), (∀ τ, j τ + k τ = N) →
    ∀ (μ C₂ : ℝ) (UW Uω : Ψ → Y → Set Y)
      (gW : ∀ τ, Y → Y → Y → Matrix (Fin (j τ)) (Fin (j τ)) ℂ)
      (gω : ∀ τ, Y → Y → Y → Matrix (Fin (k τ)) (Fin (k τ)) ℂ)
      (HW₀ HW : ∀ τ, Y → Y → Matrix (Fin (j τ)) (Fin (j τ)) ℂ)
      (Hω₀ Hω : ∀ τ, Y → Y → Matrix (Fin (k τ)) (Fin (k τ)) ℂ),
      (∀ τ, IsLogPair A Ω L s μ C₂ (UW τ) (gW τ) (HW₀ τ) (HW τ)) →
      (∀ τ, IsLogPair A Ω L s μ C₂ (Uω τ) (gω τ) (Hω₀ τ) (Hω τ)) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : Ψ → Fin N → ℝ,
        A.SmoothOn (opn s) (weightDiff HW₀ HW Hω₀ Hω lam) ∧
        ∀ c, ∀ z ∈ chartPart A c (opn s), ∀ ξ : Fin D → ℂ,
          |fderiv ℝ (weightDiff HW₀ HW Hω₀ Hω lam ∘ (A.chart c).symm) z ξ| ≤
            C * (∑ τ, ∑ i, |lam τ i|) * rad L s ((A.chart c).symm z) ^ ((N : ℝ) * μ) *
              Real.exp (rad L s ((A.chart c).symm z) / 2) * tnorm A Ω c z ξ

def Statement : Prop := Extension ∧ FlatExtension ∧ GradientBound

example (lam : Fin 2 → ℝ) : coeff lam 0 + coeff lam 1 = lam 0 ∧ coeff lam 1 = lam 1 := by
  simp [coeff]

theorem exp_one_le_rad {D : ℕ} {Y : Type} [TopologicalSpace Y] {A : FinHolAtlas D Y}
    {L : LocPot Y} {s : Y → Y → ℂ} {m : ℕ} {W : Fin m → Set Y} (h : IsBoundary A L s W) (y : Y) :
    Real.exp 1 ≤ rad L s y := by
  have := Real.log_nonpos (by positivity) (h.2.2.2 y)
  unfold rad logNormSec
  linarith

example {D : ℕ} : ¬ IsPshE (Set.univ : Set (Fin D → ℂ)) fun _ => ⊥ := fun h => by
  simpa using h.2.2.1 (Set.mem_univ 0)

end GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TaylorCoefficientForms
section
open Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms

open Formalism.DimensionVariation (mono mfact nsq liftBlock)

section Calculus

variable {E κ W : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype κ]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

def dirDeriv (v : E) (F : E → ℂ) : E → ℂ := fun z => fderiv ℂ F z v

def monoDeriv (v : κ → E) (e : κ → ℕ) (F : E → ℂ) : E → ℂ :=
  (univ : Finset κ).toList.foldr (fun x G => (dirDeriv (v x))^[e x] G) F

def polyJet (v : κ → E) (Rc : (κ → ℕ) →₀ W) (F : E → ℂ) : W :=
  Rc.sum fun e A => monoDeriv v e F 0 • A

open Classical in

def coordVec (x : κ) : κ → ℂ := Pi.single x 1

def taylorCoeff (F : (κ → ℂ) → ℂ) (e : κ → ℕ) : ℂ :=
  monoDeriv coordVec e F 0 / (mfact e : ℂ)

end Calculus

def lineForm (ξ D D' : ℂ) : ℂ := 2 * (‖ξ‖ : ℂ) * (D * conj D')

def period (ξ D : ℂ) : ℝ := 1 / (π * (lineForm ξ D D).re)

def unitScale (ξ : ℂ) : ℝ := Real.sqrt (2 * π * ‖ξ‖)

section OnePlace

variable {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B] {n₀ n₁ : ℕ}

def homForm (x x' : A →L[ℂ] B) : ℂ :=
  LinearMap.trace ℂ A (LinearMap.adjoint (x' : A →ₗ[ℂ] B) ∘ₗ (x : A →ₗ[ℂ] B))

def matUnit (b₀ : OrthonormalBasis (Fin n₀) ℂ A) (b₁ : OrthonormalBasis (Fin n₁) ℂ B)
    (p : Fin n₁ × Fin n₀) : A →L[ℂ] B :=
  (innerSL ℂ (b₀ p.2)).smulRight (b₁ p.1)

def matEntry (b₀ : OrthonormalBasis (Fin n₀) ℂ A) (b₁ : OrthonormalBasis (Fin n₁) ℂ B)
    (x : A →L[ℂ] B) (p : Fin n₁ × Fin n₀) : ℂ :=
  b₁.repr (x (b₀ p.2)) p.1

end OnePlace

section AllPlaces

variable {Pl : Type} [Fintype Pl] {X₀ X₁ : Pl → Type}
  [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
  [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
  {n₀ n₁ : ℕ}

def bigForm (ξ : Pl → ℂ) (z z' : ∀ τ, X₀ τ →L[ℂ] X₁ τ) : ℂ :=
  2 * ∑ τ, (‖ξ τ‖ : ℂ) * homForm (z τ) (z' τ)

open Classical in

def letterTensor (τ : Pl) (D : ℂ) (x : X₀ τ →L[ℂ] X₁ τ) : ∀ σ, X₀ σ →L[ℂ] X₁ σ :=
  Pi.single (M := fun σ => X₀ σ →L[ℂ] X₁ σ) τ (D • x)

def letterUnit (D : Pl → ℂ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
    (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)) (x : Pl × (Fin n₁ × Fin n₀)) :
    ∀ σ, X₀ σ →L[ℂ] X₁ σ :=
  letterTensor x.1 (D x.1) (matUnit (b₀ x.1) (b₁ x.1) x.2)

def unitCoord (ξ : Pl → ℂ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
    (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)) (z : ∀ τ, X₀ τ →L[ℂ] X₁ τ) :
    Pl × (Fin n₁ × Fin n₀) → ℂ :=
  fun x => (unitScale (ξ x.1) : ℂ) * matEntry (b₀ x.1) (b₁ x.1) (z x.1) x.2

def ofUnitCoord (ξ : Pl → ℂ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
    (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)) (u : Pl × (Fin n₁ × Fin n₀) → ℂ) :
    ∀ τ, X₀ τ →L[ℂ] X₁ τ :=
  fun τ => ∑ p, (u (τ, p) / (unitScale (ξ τ) : ℂ)) • matUnit (b₀ τ) (b₁ τ) p

end AllPlaces

def JetFrame : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (ξ D : Pl → ℂ), (∀ τ, ξ τ ≠ 0) → (∀ τ, D τ ≠ 0) →
    (∀ τ, 0 < period (ξ τ) (D τ)) ∧
    ∃ lam : Pl → ℂ, (∀ τ, ‖lam τ‖ ^ 2 = (period (ξ τ) (D τ))⁻¹) ∧
      ∀ (X₀ X₁ : Pl → Type)
        [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)]
        [∀ τ, FiniteDimensional ℂ (X₀ τ)]
        [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)]
        [∀ τ, FiniteDimensional ℂ (X₁ τ)]
        (n₀ n₁ : ℕ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
        (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)),
        (∀ z, ofUnitCoord ξ b₀ b₁ (unitCoord ξ b₀ b₁ z) = z) ∧
        (∀ u, unitCoord ξ b₀ b₁ (ofUnitCoord ξ b₀ b₁ u) = u) ∧
        (∀ z, (nsq (unitCoord ξ b₀ b₁ z) : ℂ) = π * bigForm ξ z z) ∧
        (∀ (τ : Pl) (d d' : ℂ) (x x' : X₀ τ →L[ℂ] X₁ τ),
          bigForm ξ (letterTensor τ d x) (letterTensor τ d' x') = lineForm (ξ τ) d d' * homForm x x') ∧
        ∀ Θ : (∀ τ, X₀ τ →L[ℂ] X₁ τ) → ℂ, Differentiable ℂ Θ →
          (∀ (x : Pl × (Fin n₁ × Fin n₀)) (z : ∀ τ, X₀ τ →L[ℂ] X₁ τ),
            dirDeriv (letterUnit D b₀ b₁ x) Θ z =
              lam x.1 * dirDeriv (coordVec x) (Θ ∘ ofUnitCoord ξ b₀ b₁) (unitCoord ξ b₀ b₁ z)) ∧
          (∀ u, HasSum (fun e => taylorCoeff (Θ ∘ ofUnitCoord ξ b₀ b₁) e * mono u e)
            (Θ (ofUnitCoord ξ b₀ b₁ u))) ∧
          ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] (n : Pl → ℕ)
            (Rc : (Pl × (Fin n₁ × Fin n₀) → ℕ) →₀ W),
            (∀ e ∈ Rc.support, ∀ τ, ∑ p, e (τ, p) = n τ) →
            polyJet (letterUnit D b₀ b₁) Rc Θ =
                (∏ τ, lam τ ^ n τ) • polyJet coordVec Rc (Θ ∘ ofUnitCoord ξ b₀ b₁) ∧
              polyJet (letterUnit D b₀ b₁) Rc Θ =
                liftBlock (taylorCoeff (Θ ∘ ofUnitCoord ξ b₀ b₁)) Rc lam ∧
              ∀ c : (Pl × (Fin n₁ × Fin n₀) → ℕ) → ℂ,
                (∀ u, HasSum (fun e => c e * mono u e) (Θ (ofUnitCoord ξ b₀ b₁ u))) →
                polyJet (letterUnit D b₀ b₁) Rc Θ = liftBlock c Rc lam

example (ξ D : ℂ) : period ξ D = 1 / (π * (2 * ‖ξ‖ * ‖D‖ ^ 2)) := by
  have : lineForm ξ D D = ((2 * ‖ξ‖ * ‖D‖ ^ 2 : ℝ) : ℂ) := by
    simp [lineForm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [period, this, Complex.ofReal_re]

example {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype κ] (v : κ → E) (F : E → ℂ) :
    monoDeriv v 0 F = F := by
  unfold monoDeriv
  induction (univ : Finset κ).toList with
  | nil => rfl
  | cons a l ih => simpa using ih

end GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms
end
end

