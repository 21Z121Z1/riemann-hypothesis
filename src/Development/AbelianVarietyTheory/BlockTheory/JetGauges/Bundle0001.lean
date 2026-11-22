import Mathlib

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.BalancedHermitianSpace
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace

open NumberField NumberField.IsCMField TensorProduct

abbrev Bil (Y : Type) [AddCommGroup Y] : Type := Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ

section Forms

variable {Y : Type} [AddCommGroup Y]

def quad (β : Bil Y) (x : Y) : ℝ := β x x / 2

def IsPsd (β : Bil Y) : Prop := ∀ a, 0 ≤ β a a

def IsPosDefReal (β : Bil Y) : Prop :=
  ∀ (k : ℕ) (a : Fin k → Y), LinearIndependent ℤ a → (Matrix.of fun i j => β (a i) (a j)).PosDef

def IsIntegralFn (S : Submodule ℝ (Bil Y)) (l : S →ₗ[ℝ] ℝ) : Prop :=
  ∀ β : S, (∀ a c, ∃ z : ℤ, (β : Bil Y) a c = z) → ∃ z : ℤ, l β = z

def IsPositiveFn (S : Submodule ℝ (Bil Y)) (l : S →ₗ[ℝ] ℝ) : Prop :=
  ∀ β : S, (∀ a, 0 ≤ (β : Bil Y) a a) → β ≠ 0 → 0 < l β

def IsAdmissible (S : Submodule ℝ (Bil Y)) (l : S →ₗ[ℝ] ℝ) : Prop :=
  IsIntegralFn S l ∧ IsPositiveFn S l

def leastExponent (S : Submodule ℝ (Bil Y)) (b : S) : ℝ :=
  sInf {x | ∃ l : S →ₗ[ℝ] ℝ, IsIntegralFn S l ∧ IsPositiveFn S l ∧ x = l b}

def evalSum (S : Submodule ℝ (Bil Y)) {k : ℕ} (x x' : Fin k → Y) : S →ₗ[ℝ] ℝ where
  toFun β := ∑ i, (β : Bil Y) (x i) (x' i)
  map_add' β γ := by simp [Finset.sum_add_distrib]
  map_smul' r β := by simp [Finset.mul_sum]

def HasShortFrame (β : Bil Y) (r : ℝ) : Prop :=
  ∃ v : Fin (Module.finrank ℤ Y) → Y, LinearIndependent ℤ v ∧ ∀ i, quad β (v i) ≤ r

end Forms

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

def HasTraceOne : Prop := ∃ w : 𝓞 E, w + ringOfIntegersComplexConj E w = 1

def upperConst : ℝ :=
  (|(discr E : ℝ)| ^ ((1 : ℝ) / (2 * (Module.finrank ℚ (maximalRealSubfield E) : ℝ)))) ^ 2 /
    (4 * (Module.finrank ℚ (maximalRealSubfield E) : ℝ))

variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

def IsBalanced (β : Bil Y) : Prop :=
  (∀ x y, β x y = β y x) ∧
    ∀ (a : 𝓞 E) (x y : Y), β (a • x) y = β x (ringOfIntegersComplexConj E a • y)

def IsBalancedSpace (S : Submodule ℝ (Bil Y)) : Prop := ∀ β, β ∈ S ↔ IsBalanced E β

def balancedSpace (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] : Submodule ℝ (Bil Y) where
  carrier := {β | IsBalanced E β}
  add_mem' hβ hγ := ⟨fun x y => by simp [hβ.1 x y, hγ.1 x y], fun a x y => by simp [hβ.2 a x y, hγ.2 a x y]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  smul_mem' r β hβ := ⟨fun x y => by simp [hβ.1 x y], fun a x y => by simp [hβ.2 a x y]⟩

theorem IsBalancedSpace.eq {S : Submodule ℝ (Bil Y)} (h : IsBalancedSpace E S) : S = balancedSpace E Y :=
  Submodule.ext h

def SpansOverField {k : ℕ} (x : Fin k → Y) : Prop :=
  Submodule.span E (Set.range fun b => ((1 : E) ⊗ₜ[𝓞 E] x b : E ⊗[𝓞 E] Y)) = ⊤

def LowerBound (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ β : S, IsPsd (β : Bil Y) → ∀ (k : ℕ) (x : Fin k → Y), SpansOverField E x →
    leastExponent S β ≤ ∑ b, quad (β : Bil Y) (x b)

def UpperBound (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ β : S, IsPosDefReal (β : Bil Y) →
    HasShortFrame (β : Bil Y) (upperConst E * (Module.finrank ℤ Y : ℝ) ^ 2 * leastExponent S β)

def UpperBoundSemidef (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ β : S, IsPsd (β : Bil Y) → ∀ r : ℝ,
    upperConst E * (Module.finrank ℤ Y : ℝ) ^ 2 * leastExponent S β < r → HasShortFrame (β : Bil Y) r

def ReducedBasis (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ β : S, IsPosDefReal (β : Bil Y) →
    ∃ b : Module.Basis (Fin (Module.finrank ℤ Y)) ℤ Y,
      (∀ R : ℝ, upperConst E ≤ R → ∀ j,
        quad (β : Bil Y) (b j) ≤ R * (Module.finrank ℤ Y : ℝ) ^ 3 * leastExponent S β) ∧
      ∀ j z, |(β : Bil Y) (b j) z| ≤ 2 * Real.sqrt (Module.finrank ℤ Y : ℝ) * quad (β : Bil Y) z

omit [NumberField E] [IsCMField E] in

def AdmissibleAreSums (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ l : S →ₗ[ℝ] ℝ, IsAdmissible S l ↔
    IsPositiveFn S l ∧ ∃ (k : ℕ) (x x' : Fin k → Y), l = evalSum S x x'

def pairForm {k : ℕ} (x x' : Fin k → Y) (y y' : Module.Dual (𝓞 E) Y) : 𝓞 E :=
  ∑ i, (y (x i) * ringOfIntegersComplexConj E (y' (x' i)) +
    y (x' i) * ringOfIntegersComplexConj E (y' (x i)))

def IsHermOnDual (h : Module.Dual (𝓞 E) Y → Module.Dual (𝓞 E) Y → 𝓞 E) : Prop :=
  (∀ y₁ y₂ y', h (y₁ + y₂) y' = h y₁ y' + h y₂ y') ∧
  (∀ (a : 𝓞 E) y y', h (a • y) y' = a * h y y') ∧
  ∀ y y', h y' y = ringOfIntegersComplexConj E (h y y')

def IsPosDefOnDual (h : Module.Dual (𝓞 E) Y → Module.Dual (𝓞 E) Y → 𝓞 E) : Prop :=
  ∀ (σ : E →+* ℂ) (y : Module.Dual (𝓞 E) Y), y ≠ 0 → 0 < (σ (h y y : E)).re

def HermitianDictionary (S : Submodule ℝ (Bil Y)) : Prop :=
  (∀ h : Module.Dual (𝓞 E) Y → Module.Dual (𝓞 E) Y → 𝓞 E,
    IsHermOnDual E h ↔ ∃ (k : ℕ) (x x' : Fin k → Y), h = pairForm E x x') ∧
  (∀ (k m : ℕ) (x x' : Fin k → Y) (z z' : Fin m → Y),
    pairForm E x x' = pairForm E z z' ↔ evalSum S x x' = evalSum S z z') ∧
  ∀ (k : ℕ) (x x' : Fin k → Y), IsPosDefOnDual E (pairForm E x x') ↔ IsPositiveFn S (evalSum S x x')

def BoundsAt (S : Submodule ℝ (Bil Y)) : Prop :=
  LowerBound E S ∧ UpperBound E S ∧ UpperBoundSemidef E S ∧ ReducedBasis E S ∧
    AdmissibleAreSums S ∧ HermitianDictionary E S

def LeastExponentBounds : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], HasTraceOne E →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
      (S : Submodule ℝ (Bil Y)), IsBalancedSpace E S → BoundsAt E S

open NumberField NumberField.IsCMField TensorProduct in
variable (E : Type) [Field E] [NumberField E] [IsCMField E] in
variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y] in
omit [NumberField E] [IsCMField E] [Module (𝓞 E) Y] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.isIntegralFn_evalSum (S : Submodule ℝ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.Bil Y))
    {k : ℕ} (x x' : Fin k → Y) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.IsIntegralFn S (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.evalSum S x x') := by
  intro β hβ
  choose f hf using hβ
  refine ⟨∑ i, f (x i) (x' i), ?_⟩
  show ∑ i, (β : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.Bil Y) (x i) (x' i) = _
  push_cast
  exact Finset.sum_congr rfl fun i _ => hf _ _

end GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.DecreasingNodeGaps
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps

theorem card_eq (r k : ℕ) (hk : 1 ≤ k) : 2 * r + k + 1 = (k - 1) + (2 * r + 2) := by omega

def param (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) :
    Fin (2 * r + k + 1) → ℝ :=
  fun s => Fin.append v (fun i => -b i) (Fin.cast (card_eq r k hk) s)

def cloudIdx (r k : ℕ) (j : Fin (k - 1)) : Fin (2 * r + k + 1) := ⟨j.val, by omega⟩

def nodeIdx (r k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * r + 2)) : Fin (2 * r + k + 1) :=
  ⟨k - 1 + i.val, by omega⟩

def IsDecreasing (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  StrictAnti (param r k hk v b)

def sign (r k : ℕ) (hk : 1 ≤ k) : Fin (2 * r + k + 1) → Bool :=
  fun s => Fin.append (fun _ : Fin (k - 1) => true)
    (fun i : Fin (2 * r + 2) => decide (Even i.val)) (Fin.cast (card_eq r k hk) s)

def Interlaces (r k : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : Fin k → ℝ) : Prop :=
  (∀ i : Fin k, lam ⟨i.val, by omega⟩ < u i) ∧
    ∀ (i : ℕ) (hi : i + 1 < k), u ⟨i + 1, hi⟩ < lam ⟨i, by omega⟩

def Parity (r k : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : Fin k → ℝ) : Prop :=
  ∀ (s : Fin (2 * r + k + 1)) (i : Fin k), ∃ z : ℤ, lam s - u i = (z : ℝ) + 1 / 2

def IsShiftedIntegral {d : ℕ} (x : Fin d → ℝ) : Prop :=
  ∀ s : Fin d, ∃ z : ℤ, x s = (z : ℝ) + ((d : ℝ) - 1) / 2

def NodeGapGe (r : ℕ) (b : Fin (2 * r + 2) → ℝ) (h : ℝ) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < 2 * r + 2), h ≤ (-b ⟨i, by omega⟩) - (-b ⟨i + 1, hi⟩)

def NoncompactGapGe (r k : ℕ) (hk : 1 ≤ k) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) : Prop :=
  ∀ s t : Fin (2 * r + k + 1), sign r k hk s ≠ sign r k hk t → h ≤ |lam s - lam t|

@[simp] theorem param_cloud (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (j : Fin (k - 1)) : param r k hk v b (cloudIdx r k j) = v j := by
  have : Fin.cast (card_eq r k hk) (cloudIdx r k j) = Fin.castAdd (2 * r + 2) j := rfl
  simp only [param, this, Fin.append_left]

@[simp] theorem param_node (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (i : Fin (2 * r + 2)) :
    param r k hk v b (nodeIdx r k hk i) = -b i := by
  have : Fin.cast (card_eq r k hk) (nodeIdx r k hk i) = Fin.natAdd (k - 1) i := rfl
  simp only [param, this, Fin.append_right]

@[simp] theorem sign_cloud (r k : ℕ) (hk : 1 ≤ k) (j : Fin (k - 1)) :
    sign r k hk (cloudIdx r k j) = true := by
  have : Fin.cast (card_eq r k hk) (cloudIdx r k j) = Fin.castAdd (2 * r + 2) j := rfl
  simp only [sign, this, Fin.append_left]

@[simp] theorem sign_node (r k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * r + 2)) :
    sign r k hk (nodeIdx r k hk i) = decide (Even i.val) := by
  have : Fin.cast (card_eq r k hk) (nodeIdx r k hk i) = Fin.natAdd (k - 1) i := rfl
  simp only [sign, this, Fin.append_right]

theorem parity_of_isShiftedIntegral (r k : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : Fin k → ℝ)
    (hl : IsShiftedIntegral lam) (hu : IsShiftedIntegral u) : Parity r k lam u := by
  intro s i
  obtain ⟨a, ha⟩ := hl s
  obtain ⟨c, hc⟩ := hu i
  refine ⟨a - c + r, ?_⟩
  rw [ha, hc]
  push_cast
  ring

theorem nodeGapGe_of_noncompactGapGe (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (hd : IsDecreasing r k hk v b)
    (hg : NoncompactGapGe r k hk (param r k hk v b) h) : NodeGapGe r b h := by
  intro i hi
  have hlt : nodeIdx r k hk ⟨i, by omega⟩ < nodeIdx r k hk ⟨i + 1, hi⟩ := by
    simp [nodeIdx, Fin.lt_def]
  have h1 := hd hlt
  have h2 := hg (nodeIdx r k hk ⟨i, by omega⟩) (nodeIdx r k hk ⟨i + 1, hi⟩) (by
    simp only [sign_node, Nat.even_add_one]
    by_cases he : Even i <;> simp [he])
  simp only [param_node] at h1 h2
  rwa [abs_of_pos (by linarith)] at h2

example : List.ofFn (sign 1 2 (by norm_num)) = [true, true, false, true, false] := by decide

example :
    IsDecreasing 0 2 (by norm_num) ![1] ![8, 10] ∧
    Interlaces 0 2 (param 0 2 (by norm_num) ![1] ![8, 10]) ![5 / 2, -1 / 2] ∧
    Parity 0 2 (param 0 2 (by norm_num) ![1] ![8, 10]) ![5 / 2, -1 / 2] ∧
    NodeGapGe 0 ![8, 10] 2 := by
  have hp : param 0 2 (by norm_num) ![1] ![8, 10] = ![1, -8, -10] := by
    funext s
    fin_cases s <;> rfl
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold IsDecreasing
    rw [hp]
    intro s t hst
    fin_cases s <;> fin_cases t <;> simp_all <;> norm_num
  · rw [hp]
    intro i
    fin_cases i <;> simp <;> norm_num
  · rw [hp]
    intro i hi
    obtain rfl : i = 0 := by omega
    simp
    norm_num
  · apply parity_of_isShiftedIntegral
    · rw [hp]
      intro s
      fin_cases s
      · exact ⟨0, by simp; norm_num⟩
      · exact ⟨-9, by simp; norm_num⟩
      · exact ⟨-11, by simp; norm_num⟩
    · intro s
      fin_cases s
      · exact ⟨2, by simp; norm_num⟩
      · exact ⟨-1, by simp; norm_num⟩
  · intro i hi
    obtain rfl : i = 0 := by omega
    simp
    norm_num

end GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.HarishChandraParameters
section
open scoped BigOperators
open Matrix

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData

variable {n : ℕ}

def formJ (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun c => if ε c then 1 else -1

def grpG (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {g | gᴴ * formJ ε * g = formJ ε}

def grpK (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {k | k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ ∀ a b, ε a ≠ ε b → k a b = 0}

def root (a b : Fin n) : Fin n → ℝ := Pi.single a 1 - Pi.single b 1

def posPairs (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter fun x => x.1 < x.2

def cptPairs (ε : Fin n → Bool) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun x => x.1 < x.2 ∧ ε x.1 = ε x.2

def ncPairs (ε : Fin n → Bool) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun x => x.1 < x.2 ∧ ε x.1 ≠ ε x.2

def rho (n : ℕ) : Fin n → ℝ := (1 / 2 : ℝ) • ∑ x ∈ posPairs n, root x.1 x.2

def rhoC (ε : Fin n → Bool) : Fin n → ℝ := (1 / 2 : ℝ) • ∑ x ∈ cptPairs ε, root x.1 x.2

def rhoNC (ε : Fin n → Bool) : Fin n → ℝ := (1 / 2 : ℝ) • ∑ x ∈ ncPairs ε, root x.1 x.2

def IsHCParam (μ : Fin n → ℝ) : Prop :=
  StrictAnti μ ∧ ∀ i, ∃ m : ℤ, μ i = (m : ℝ) + ((n : ℝ) - 1) / 2

def lowestWeight (ε : Fin n → Bool) (μ : Fin n → ℝ) : Fin n → ℝ := μ + rhoNC ε - rhoC ε

def torus (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => Complex.exp (Complex.I * (θ a : ℂ))

def wtChar (ω θ : Fin n → ℝ) : ℂ := Complex.exp (Complex.I * ((∑ a, ω a * θ a : ℝ) : ℂ))

def CptLE (ε : Fin n → Bool) (ω Λ : Fin n → ℝ) : Prop :=
  ∃ c : Fin n × Fin n → ℕ, Λ - ω = ∑ x ∈ cptPairs ε, (c x : ℝ) • root x.1 x.2

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure IsUnitaryRepOn (Γ : Set (Matrix (Fin n) (Fin n) ℂ))
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) : Prop where
  map_one : σ 1 = 1
  map_mul : ∀ g ∈ Γ, ∀ g' ∈ Γ, σ (g * g') = σ g * σ g'
  norm_map : ∀ g ∈ Γ, ∀ v, ‖σ g v‖ = ‖v‖
  cont : ∀ v, ContinuousOn (fun g => σ g v) Γ

def weightSpace (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (ω : Fin n → ℝ) :
    Submodule ℂ H where
  carrier := {v | ∀ θ : Fin n → ℝ, σ (torus θ) v = wtChar ω θ • v}
  add_mem' := by
    intro a b ha hb θ
    rw [map_add, ha θ, hb θ, smul_add]
  zero_mem' := by intro θ; simp
  smul_mem' := by
    intro c v hv θ
    rw [map_smul, hv θ, smul_comm]

def IsWeightVector (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (ω : Fin n → ℝ) (v : H) : Prop :=
  v ≠ 0 ∧ v ∈ weightSpace σ ω

def KStable (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (S : Submodule ℂ H) : Prop :=
  ∀ k ∈ grpK ε, ∀ v ∈ S, σ k v ∈ S

structure IsKType (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (S : Submodule ℂ H) (Λ : Fin n → ℝ) : Prop where
  finDim : FiniteDimensional ℂ S
  stable : KStable ε σ S
  irred : ∀ S' : Submodule ℂ H, S' ≤ S → KStable ε σ S' → S' = ⊥ ∨ S' = S
  exists_highest : ∃ v ∈ S, IsWeightVector σ Λ v
  le_highest : ∀ ω : Fin n → ℝ, ∀ v ∈ S, IsWeightVector σ ω v → CptLE ε ω Λ

def isotypic (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (ν : Fin n → ℝ) : Submodule ℂ H :=
  sSup {S : Submodule ℂ H | IsKType ε σ S ν}

def isotypicWeight (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (ν ω : Fin n → ℝ) : Submodule ℂ H :=
  isotypic ε σ ν ⊓ weightSpace σ ω

def lowestIsotypic (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (μ : Fin n → ℝ) : Submodule ℂ H :=
  isotypic ε σ (lowestWeight ε μ)

def IsLowestTypeUnit (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (μ : Fin n → ℝ) (w : H) : Prop :=
  w ∈ lowestIsotypic ε σ μ ∧ ‖w‖ = 1

def IsLowestVector (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (μ : Fin n → ℝ) (w : H) : Prop :=
  w ∈ isotypicWeight ε σ (lowestWeight ε μ) (lowestWeight ε μ) ∧ ‖w‖ = 1

end Rep

def rhoU (k : ℕ) : Fin k → ℝ := fun i => ((k : ℝ) - 1) / 2 - (i : ℕ)

structure IsCompactIrrep {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin k) (Fin k) ℂ → H →L[ℂ] H) (u : Fin k → ℝ) : Prop where
  param : IsHCParam u
  rep : IsUnitaryRepOn (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) π
  type : IsKType (fun _ => true) π ⊤ (u - rhoU k)

theorem grpK_const (k : ℕ) : grpK (fun _ : Fin k => true) =
    (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) := by
  ext g
  simp [grpK]

def detRep (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ →L[ℂ] ℂ := g.det • (1 : ℂ →L[ℂ] ℂ)

end GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData
end
end

