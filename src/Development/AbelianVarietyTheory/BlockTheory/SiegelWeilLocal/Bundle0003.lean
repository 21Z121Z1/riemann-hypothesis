import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
section
open Matrix Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

open Formalism.MainNotions.S

section Defs

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def orbit (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : ℝ → H :=
  fun t => σ (NormedSpace.exp ((t : ℂ) • X)) v

def dAct (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : H :=
  deriv (orbit σ X v) 0

def IsDiffVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∀ X, Formalism.REAL.inG ε X → DifferentiableAt ℝ (orbit σ X v) 0

def dWord (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (l : List (Matrix (Fin n) (Fin n) ℂ)) (v : H) : H :=
  l.foldr (dAct σ) v

def stepSpace (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P : ℕ) :
    Submodule ℂ H :=
  Submodule.span ℂ {v | ∃ (l : List (Matrix (Fin n) (Fin n) ℂ)) (u : H), l.length ≤ P ∧
    (∀ X ∈ l, Formalism.REAL.inG ε X) ∧ u ∈ lowKSub ε lam σ ∧ v = dWord σ l u}

def IsONFamily (ε : Fin n → Bool) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i, Formalism.REAL.inG ε (E i)) ∧ ∀ i j, (Matrix.trace (E i * (E j)ᴴ)).re = if i = j then 1 else 0

def stepConst (n : ℕ) (b : ℝ) (P : ℕ) : ℝ :=
  (n : ℝ) ^ (1 / 2 : ℝ) * b ^ 2 + 3 / 2 * (n : ℝ) ^ (3 / 2 : ℝ) + 3 * (P : ℝ)

theorem stepSpace_zero (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    stepSpace ε lam σ 0 = lowKSub ε lam σ := by
  have : {v | ∃ (l : List (Matrix (Fin n) (Fin n) ℂ)) (u : H), l.length ≤ 0 ∧
      (∀ X ∈ l, Formalism.REAL.inG ε X) ∧ u ∈ lowKSub ε lam σ ∧ v = dWord σ l u} = (lowKSub ε lam σ : Set H) := by
    ext v
    constructor
    · rintro ⟨l, u, hl, -, hu, rfl⟩
      have : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
      subst this
      exact hu
    · intro hv
      exact ⟨[], v, le_rfl, by simp, hv, rfl⟩
  rw [stepSpace, this, Submodule.span_eq]

theorem stepSpace_mono (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Monotone (stepSpace ε lam σ) := by
  intro P Q h
  refine Submodule.span_mono ?_
  rintro v ⟨l, u, hl, h1, h2, h3⟩
  exact ⟨l, u, hl.trans h, h1, h2, h3⟩

end Defs

example (ε : Fin 1 → Bool) : IsONFamily ε (fun _ => Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  refine ⟨fun _ => ?_, fun i j => ?_⟩
  · simp [Formalism.REAL.inG, Matrix.conjTranspose_smul]
  · have : i = j := Subsingleton.elim (α := Fin 1) i j
    simp [this, Matrix.conjTranspose_smul, smul_smul]

def StepBound : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (b : ℝ) (P : ℕ),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → (∀ a, |lam a| ≤ b ^ 2) →
      FiniteDimensional ℂ (stepSpace ε lam σ P) ∧
      (∀ w ∈ stepSpace ε lam σ P, IsDiffVec ε σ w) ∧
      (∀ E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ, IsONFamily ε E → ∀ w ∈ stepSpace ε lam σ P,
        ∑ i, ‖dAct σ (E i) w‖ ^ 2 ≤ stepConst n b P ^ 2 * ‖w‖ ^ 2) ∧
      ∀ E, Formalism.REAL.inG ε E → ∀ w ∈ stepSpace ε lam σ P,
        ‖dAct σ E w‖ ≤ Real.sqrt (Formalism.REAL.hs E) * stepConst n b P * ‖w‖

end GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
section
open NumberField Matrix

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

open Formalism.MainNotions.S

def gLie {n : ℕ} (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Formalism.REAL.inG ε X}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Formalism.REAL.inG] at *
    rw [conjTranspose_add, add_mul, mul_add]
    calc _ = (aᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * a) + (bᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * b) := by abel
      _ = 0 := by rw [ha, hb, add_zero]
  zero_mem' := by simp [Formalism.REAL.inG]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, Formalism.REAL.inG] at *
    rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, ha, smul_zero]

def expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : Formalism.REAL.UJ ε :=
  ⟨(Matrix.isUnit_exp (X : Matrix (Fin n) (Fin n) ℂ)).unit, Formalism.REAL.f1alg_exp_inUJ ε X.1 X.2⟩

@[simp] theorem uMat_expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) :
    uMat (expU X) = NormedSpace.exp (X : Matrix (Fin n) (Fin n) ℂ) := rfl

def IsONBasis {n m : ℕ} {ε : Fin n → Bool} (E : Fin m → gLie ε) : Prop :=
  (∀ i j, (((E i : Matrix (Fin n) (Fin n) ℂ) * (E j : Matrix (Fin n) (Fin n) ℂ)ᴴ).trace).re =
      if i = j then 1 else 0) ∧
    Submodule.span ℝ (Set.range E) = ⊤

variable (B : RowsAut)

abbrev gInf : Type := ∀ v : InfinitePlace B.I.F, gLie (B.I.ε v)

open Classical in

def atPlace (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v)) : gInf B := Pi.single v X

def orbit (E : gInf B) (w : B.Hs) (t : ℝ) : B.Hs := B.σs (fun v => expU (t • E v)) w

def dAct (E : gInf B) (w : B.Hs) : B.Hs := deriv (orbit B E w) 0

def wordAct (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (w : B.Hs) : B.Hs :=
  l.foldr (fun X y => dAct B (atPlace B X.1 X.2) y) w

def VP (P : ℕ) : Submodule ℂ B.Hs :=
  Submodule.span ℂ {y | ∃ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (u : ∀ v, B.H v),
    l.length ≤ P ∧ (∀ v, u v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v)) ∧ y = wordAct B l (B.tens u)}

def beP (n : ℕ) (b : ℝ) (P : ℕ) : ℝ :=
  Real.sqrt n * b ^ 2 + 3 / 2 * ((n : ℝ) * Real.sqrt n) + 3 * (P : ℝ)

def StepBoundAt (b : ℝ) (P : ℕ) : Prop :=
  FiniteDimensional ℂ (VP B P) ∧
  (∀ k : B.I.Ginf, (∀ v, uMat (k v) ∈ Formalism.REAL.Kset (B.I.ε v)) → ∀ w ∈ VP B P, B.σs k w ∈ VP B P) ∧
  (∀ (E : gInf B), ∀ w ∈ VP B P, DifferentiableAt ℝ (orbit B E w) 0) ∧
  (∀ (v : InfinitePlace B.I.F) (m : ℕ) (E : Fin m → gLie (B.I.ε v)), IsONBasis E → ∀ w ∈ VP B P,
    ∑ i, ‖dAct B (atPlace B v (E i)) w‖ ^ 2 ≤ beP B.I.n b P ^ 2 * ‖w‖ ^ 2) ∧
  (∀ (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v)), ∀ w ∈ VP B P,
    ‖dAct B (atPlace B v X) w‖ ≤ Real.sqrt (Formalism.REAL.hs X.1) * beP B.I.n b P * ‖w‖) ∧
  (∀ (E : gInf B), ∀ w ∈ VP B P,
    ‖dAct B E w‖ ≤ Real.sqrt B.I.f * Real.sqrt (∑ v, Formalism.REAL.hs (E v).1) * beP B.I.n b P * ‖w‖) ∧
  ∀ (E : gInf B), ∀ w ∈ VP B P, dAct B E w ∈ VP B (P + 1)

def StepBound : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (b : ℝ), GlobalTheory.Count.IsDSData B d →
    (∀ v a, |B.lam v a| ≤ b ^ 2) → ∀ P : ℕ, StepBoundAt B b P

open NumberField Matrix in
variable (B : _root_.Formalism.MainNotions.S.RowsAut) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.stepSpan_mono {P Q : ℕ} (h : P ≤ Q) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.VP B P ≤ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.VP B Q :=
  Submodule.span_mono fun _ ⟨l, u, hl, hu, hy⟩ => ⟨l, u, hl.trans h, hu, hy⟩

open NumberField Matrix in
variable (B : _root_.Formalism.MainNotions.S.RowsAut) in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem {d : InfinitePlace B.I.F → ℝ}
    (h : _root_.GlobalTheory.Count.IsDSData B d) (P : ℕ) :
    B.tens B.w ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.VP B P ∧ ‖B.tens B.w‖ = 1 := by
  have hd := h
  unfold _root_.GlobalTheory.Count.IsDSData at hd
  have hunit : ∀ v, ‖B.w v‖ = 1 ∧ B.w v ∈ _root_.Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v) := fun v => by
    have hv := (hd v).2.2.1
    unfold _root_.Formalism.MainNotions.S.IsLowUnit at hv
    exact hv
  refine ⟨Submodule.subset_span ⟨[], B.w, Nat.zero_le _, fun v => (hunit v).2, rfl⟩, ?_⟩
  have hs := B.tens_spec
  unfold _root_.Formalism.MainNotions.S.AutInst.IsHilbTensor at hs
  have hinner : inner ℂ (B.tens B.w) (B.tens B.w) = 1 := by
    rw [hs.1]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [inner_self_eq_norm_sq_to_K, (hunit v).1]
    simp
  have hsq : ‖B.tens B.w‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hinner, RCLike.one_re]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq

example (ε : Fin 1 → Bool) : ∃ E : Fin 1 → gLie ε, IsONBasis E := by
  have hm : ∀ t : ℝ, Formalism.REAL.inG ε (!![(t : ℂ) * Complex.I]) := by
    intro t
    ext i j
    fin_cases i; fin_cases j
    by_cases h : ε 0 = true <;> simp [Formalism.REAL.Jm, Matrix.mul_apply, h]
  refine ⟨fun _ => ⟨!![((1 : ℝ) : ℂ) * Complex.I], hm 1⟩, ?_, ?_⟩
  · intro i j
    fin_cases i; fin_cases j
    simp [Matrix.trace, Matrix.vecMul, dotProduct]
  · rw [eq_top_iff]
    rintro ⟨X, hX⟩ -
    have h0 : (X 0 0).re = 0 := by
      have := congrArg Complex.re (congrFun (congrFun hX 0) 0)
      by_cases h : ε 0 = true <;> simp [Formalism.REAL.Jm, Matrix.mul_apply, h] at this <;> linarith
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun _ => (X 0 0).im, ?_⟩
    ext i j
    fin_cases i; fin_cases j
    simp [Complex.ext_iff, h0]

end GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.PointwiseKernelBound
section
open NumberField Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound

open Formalism.MainNotions.S GlobalTheory.Count

def decHS (q : ℕ) (h t : ℝ) : ℝ := Real.exp (-(h / 8) * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))))

def PointwiseBound : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (h : ℝ),
    IsDSData B d → SigIs B p q → GapGe B h → 8 * (B.I.n : ℝ) * ((min p q : ℕ) : ℝ) < h →
      (1 ≤ min p q → ∀ y : B.I.GA,
          ‖phe B d y‖ ≤ (∏ v, d v) * (B.e 1).re * ∏ v, decHS (min p q) h (dHS (uMat (y.1 v)))) ∧
      (∀ y : B.I.GA, ‖phe B d y‖ ≤ (∏ v, d v) * (B.e 1).re) ∧
      phe B d 1 = ((∏ v, d v : ℝ) : ℂ) * B.e 1 ∧
      (B.e 1).im = 0 ∧ 0 ≤ (B.e 1).re ∧
      (∀ x : B.I.Gf, ‖B.e x‖ ≤ (B.e 1).re) ∧
      ∀ y : B.I.GA, phe B d y ≠ 0 → y.2 ∈ B.I.Kset

example (q : ℕ) (h : ℝ) : decHS q h 0 = 1 := by simp [decHS]

example (q : ℕ) (h t : ℝ) (hh : 0 ≤ h) (ht : 0 ≤ t) : decHS q h t ≤ 1 := by
  unfold decHS
  rw [Real.exp_le_one_iff]
  have : 0 ≤ min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) := le_min (by positivity) (by positivity)
  nlinarith [mul_nonneg hh this]

end GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.RareFlags
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RareFlags

open Formalism.MainNotions.S GlobalTheory.Count

def FlagRare : Prop :=
  ∃ n₀ : ℕ, ∀ (B : RowsAut) (p q : ℕ), SigIs B p q → n₀ ≤ B.I.n → q ^ 2 ≤ B.I.n →
    Real.log B.I.rd ≤ Real.exp B.I.n → Real.log B.I.f ≤ Real.sqrt B.I.n →
    prob B {x | least B.I x < 1 / 2} ≤
      Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n))

example (q n : ℕ) : q ^ 2 ≤ n ↔ (q : ℝ) ≤ Real.sqrt n := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  exact_mod_cast Iff.rfl

example (I : AutInst) (x : I.GA) : least I x < 1 / 2 ↔ tau1 I x < 1 / 2 := by
  simp [tau1]

end GlobalTheory.IndefiniteRowSideFullHecke.RareFlags
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.SaturatedDuality
section
open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SaturatedLatticeDuality

open Formalism.MainNotions.S GlobalTheory.Count

def SatIn (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S

def StepDuality : Prop :=
  ∀ (I : AutInst) (x : I.GA),
    Formalism.HN.ht (bas I) (frm I x) (lamX I x) = 1 ∧
    (1 ≤ I.n → Formalism.HN.largestSize (bas I) (frm I x) (lamX I x) * least I x = 1) ∧
    (∀ t : ℝ, 0 < t →
      perpIn I x (stepLe I x t) = stepLt I x (1 / t) ∧
      perpIn I x (stepLt I x t) = stepLe I x (1 / t)) ∧
    (∀ S : Submodule (𝓞 I.E) (Fin I.n → I.E), SatIn I x S →
      SatIn I x (perpIn I x S) ∧
      Formalism.HN.rkK (perpIn I x S) + Formalism.HN.rkK S = I.n ∧
      perpIn I x (perpIn I x S) = S) ∧
    ∀ S S' : Submodule (𝓞 I.E) (Fin I.n → I.E), SatIn I x S → SatIn I x S' → S ≤ S' →
      Formalism.HN.htQ (bas I) (frm I x) (perpIn I x S) (perpIn I x S') *
        Formalism.HN.htQ (bas I) (frm I x) S' S = 1

example (I : AutInst) (x : I.GA) : perpIn I x ⊥ = lamX I x := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun y hy => hy.1
  · intro y hy
    refine Submodule.subset_span ⟨hy, fun s hs => ?_⟩
    rw [(Submodule.mem_bot _).1 hs]
    simp [Formalism.UG.hform]

example (I : AutInst) (x : I.GA) (S S' : Submodule (𝓞 I.E) (Fin I.n → I.E)) (h : S ≤ S') :
    perpIn I x S' ≤ perpIn I x S :=
  Submodule.span_mono fun _ hy => ⟨hy.1, fun s hs => hy.2 s (h hs)⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SaturatedLatticeDuality
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.SaturatedPerpDuality
section
open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality

open Formalism.MainNotions.S GlobalTheory.Count

def SatIn (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S

def StepDuality : Prop :=
  ∀ (I : AutInst) (x : I.GA),
    Formalism.HN.ht (bas I) (frm I x) (lamX I x) = 1 ∧
    (1 ≤ I.n → Formalism.HN.largestSize (bas I) (frm I x) (lamX I x) = 1 / least I x) ∧
    (∀ t : ℝ, 0 < t →
      perpIn I x (stepLe I x t) = stepLt I x (1 / t) ∧
      perpIn I x (stepLt I x t) = stepLe I x (1 / t)) ∧
    (∀ S : Submodule (𝓞 I.E) (Fin I.n → I.E), SatIn I x S →
      SatIn I x (perpIn I x S) ∧
      Formalism.HN.rkK (perpIn I x S) + Formalism.HN.rkK S = I.n ∧
      perpIn I x (perpIn I x S) = S) ∧
    (∀ S S' : Submodule (𝓞 I.E) (Fin I.n → I.E), SatIn I x S → SatIn I x S' → S ≤ S' →
      Formalism.HN.htQ (bas I) (frm I x) (perpIn I x S) (perpIn I x S') =
        1 / Formalism.HN.htQ (bas I) (frm I x) S' S)

theorem perpIn_bot (I : AutInst) (x : I.GA) : perpIn I x ⊥ = lamX I x := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun _ hy => hy.1
  · intro y hy
    refine Submodule.subset_span ⟨hy, fun s hs => ?_⟩
    rw [Submodule.mem_bot] at hs
    subst hs
    simp [Formalism.UG.hform]

end GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality
end
end

