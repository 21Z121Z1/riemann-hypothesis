import Mathlib

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.CobOn
section
noncomputable section

namespace GlobalTheory.KEdge

variable {Γ : Type*} [Group Γ] {N : ℕ}

def edge (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ h : Γ) : ZMod N :=
  η (σ * h * σ⁻¹) - η h - (x h).toAdd * (y σ).toAdd + (x σ).toAdd * (y h).toAdd

def CobOn (Δ : Subgroup Γ) (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) : Prop :=
  ∀ g ∈ Δ, ∀ h ∈ Δ, (x g).toAdd * (y h).toAdd = η h - η (g * h) + η g

end GlobalTheory.KEdge
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
section
noncomputable section

namespace GlobalTheory.AlmostEt

open scoped NNReal

variable {L : Type*} [Field L]

def ApproxRoot (p : ℕ) (v : Valuation L ℝ≥0) (F : Subfield L) : Prop :=
  ∃ θ : ℝ≥0, θ < 1 ∧ ∀ u ∈ F, ∃ w ∈ F, v (u - w ^ p) ≤ θ * v u

variable {G : Type*} [Group G] [MulSemiringAction G L]

abbrev Fix (L : Type*) [Field L] {G : Type*} [Group G] [MulSemiringAction G L] (N : Subgroup G) :
    Subfield L := FixedPoints.subfield N L

def Moves (v : Valuation L ℝ≥0) (F : Subfield L) (σ : G) : Prop :=
  ∀ r : ℝ≥0, r < 1 → ∃ x ∈ F, v x ≤ 1 ∧ r < v (σ • x - x)

structure IsSep (v : Valuation L ℝ≥0) (N : Subgroup G) {n : ℕ} (a b : Fin n → L) (c : L) : Prop where
  a_mem : ∀ i, a i ∈ Fix L N
  b_mem : ∀ i, b i ∈ Fix L N
  c_mem : c ∈ Fix L N
  a_le : ∀ i, v (a i) ≤ 1
  b_le : ∀ i, v (b i) ≤ 1
  c_le : v c ≤ 1
  sum_in : ∀ σ : G, σ ∈ N → ∑ i, a i * σ • b i = c
  sum_out : ∀ σ : G, σ ∉ N → ∑ i, a i * σ • b i = 0

def AlmostSep (v : Valuation L ℝ≥0) (N : Subgroup G) : Prop :=
  ∀ r : ℝ≥0, r < 1 → ∃ (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c ∧ r < v c

def cosetTrace (N : Subgroup G) [Fintype (G ⧸ N)] (x : L) : L := ∑ q : G ⧸ N, q.out • x

end GlobalTheory.AlmostEt
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.CthFac
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.Sieg

def ee (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * z)

def cthFac (c : ℕ) (q t : ℂ) (m : ℕ) : ℂ :=
  (1 - q ^ m * t) ^ (c ^ 2) * (1 - q ^ m * t⁻¹) ^ (c ^ 2) / ((1 - q ^ m * t ^ c) * (1 - q ^ m * (t ^ c)⁻¹))

def cth (c : ℕ) (q t : ℂ) : ℂ :=
  q ^ ((c ^ 2 - 1) / 12) * (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (1 - t) ^ (c ^ 2) / (1 - t ^ c) *
    ∏' m : ℕ, cthFac c q t (m + 1)

def pt (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := (x 0 : ℂ) * (τ : ℂ) + (x 1 : ℂ)

def sg (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := cth c (ee τ) (ee (pt x τ))

open Classical in

def f0 (j : ℕ) (x : Fin 2 → ℚ) : ℂ :=
  if j = 1 then (if Int.fract (x 0) = 0 then (1 / 2) * (1 + ee (x 1)) / (1 - ee (x 1)) else 1 / 2 - ((Int.fract (x 0) : ℚ) : ℂ))
  else -((((Polynomial.bernoulli j).eval (Int.fract (x 0)) : ℚ)) : ℂ) / j

open Classical in

def fTerm (j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) (p : ℤ × ℤ) : ℂ :=
  if 0 < (x 0 + p.1) * p.2 then
    (Int.sign p.2 : ℂ) * ((x 0 + p.1 : ℚ) : ℂ) ^ (j - 1) * ee (((x 0 + p.1 : ℚ) : ℂ) * p.2 * (τ : ℂ)) * ee ((x 1 : ℂ) * p.2)
  else 0

def F (j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := f0 j x + ∑' p : ℤ × ℤ, fTerm j x τ p

def cF (c j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := (c : ℂ) ^ 2 * F j x τ - (c : ℂ) ^ (2 - (j : ℤ)) * F j (c • x) τ

def admitted (c : ℕ) (x : Fin 2 → ℚ) : Prop :=
  1 < c ∧ Nat.Coprime c 6 ∧ ¬ ((c : ℚ) * x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c : ℚ) * x 1 ∈ Set.range ((↑) : ℤ → ℚ))

end GlobalTheory.Sieg
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
section
noncomputable section

namespace GlobalTheory.SgAlg

variable {E : Type} [CommRing E]

def IsQA (σ : E →+* E) : Prop :=
  (∀ x, σ (σ x) = x) ∧ (∃ x, σ x ≠ x) ∧ IsReduced E ∧ IsUnit (2 : E) ∧
    ∀ x, σ x = x → x ≠ 0 → IsUnit x

def cT (σ : E →+* E) {a b : Type} (A : Matrix a b E) : Matrix b a E := (A.map σ).transpose

def IsHermU (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Prop := cT σ J = J ∧ IsUnit J.det

def form (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  dotProduct (fun i => σ (y i)) (J.mulVec x)

def pairM (σ : E →+* E) {n : ℕ} {a b : Type} (J : Matrix (Fin n) (Fin n) E)
    (P' : Matrix (Fin n) b E) (P : Matrix (Fin n) a E) : Matrix a b E := cT σ P * J * P'

def IsUn (σ : E →+* E) {n : ℕ} (J g : Matrix (Fin n) (Fin n) E) : Prop := cT σ g * J * g = J

def Free {n : ℕ} {a : Type} [Fintype a] [DecidableEq a] (P : Matrix (Fin n) a E) : Prop :=
  ∃ L : Matrix a (Fin n) E, L * P = 1

def IsUp {m : ℕ} (u : Matrix (Fin m) (Fin m) E) : Prop :=
  ∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1)

def IsLo {m : ℕ} (u : Matrix (Fin m) (Fin m) E) : Prop :=
  ∀ i j, (i < j → u i j = 0) ∧ (i = j → u i j = 1)

def lead {m : ℕ} (Z : Matrix (Fin m) (Fin m) E) (l : ℕ) (hl : l ≤ m) : E :=
  (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def TF (r : ℕ) (T : E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.diagonal fun a => if a = Fin.last r then -T else 0

def Gq (σ : E →+* E) {r : ℕ} (T T' : E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E :=
  Z.det * σ Z.det - T * T' * (lead Z r (Nat.le_succ r) * σ (lead Z r (Nat.le_succ r)))

def IsFrame (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T : E)
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Prop := Free P ∧ pairM σ J P P = TF r T

def eOf {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Matrix (Fin n) (Fin r) E :=
  P.submatrix id Fin.castSucc

def IsDual (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E) : Prop :=
  pairM σ J f P = (Matrix.of fun a b => if a = Fin.castSucc b then 1 else 0) ∧ pairM σ J f f = 0

def InS (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (g : Matrix (Fin n) (Fin n) E) : Prop := IsUn σ J g ∧ ∃ ν, IsUp ν ∧ g * P = P * ν

def InFrameStabilizer (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (g : Matrix (Fin n) (Fin n) E) : Prop := IsUn σ J g ∧ g * P = P

def InN (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (g : Matrix (Fin n) (Fin n) E) : Prop :=
  IsUn σ J g ∧ (∃ ν, IsUp ν ∧ g * eOf P = eOf P * ν) ∧
    ∀ v : Fin n → E, (cT σ (eOf P) * J).mulVec v = 0 → ∃ c, g.mulVec v - v = (eOf P).mulVec c

def InH (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (f : Matrix (Fin n) (Fin r) E) (g : Matrix (Fin n) (Fin n) E) : Prop :=
  IsUn σ J g ∧ g * P = P ∧ g * f = f

def Zhat (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P P' : Matrix (Fin n) (Fin (r + 1)) E) (γ : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) E := pairM σ J (γ * P') P

def XZ (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T T' : E)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Set (Matrix (Fin n) (Fin (r + 1)) E × Matrix (Fin n) (Fin (r + 1)) E) :=
  {p | IsFrame σ J T p.1 ∧ IsFrame σ J T' p.2 ∧ pairM σ J p.2 p.1 = Z}

def PosOnPerp {n : ℕ} {a : Type} [Fintype a] (J : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n) a ℂ) : Prop :=
  ∀ w : Fin n → ℂ, (cT (starRingEnd ℂ) A * J).mulVec w = 0 → w ≠ 0 →
    0 < (form (starRingEnd ℂ) J w w).re

end GlobalTheory.SgAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.Integral
section
noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

def frc (M : ℕ) (a : ℤ) : ℚ := ((a % (M : ℤ) : ℤ) : ℚ) / M

def const0 (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) : K :=
  if j = 1 then
    (if (M : ℤ) ∣ a₁ then (1 / 2 : K) * (1 + ζ ^ a₂) / (1 - ζ ^ a₂) else ((1 / 2 - frc M a₁ : ℚ) : K))
  else -(((Polynomial.bernoulli j).eval (frc M a₁) / j : ℚ) : K)

def coefPos (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) : K :=
  ∑ d ∈ n.divisors,
    ((if ((n / d : ℕ) : ℤ) ≡ a₁ [ZMOD M] then (((n / d : ℕ) : K) / M) ^ (j - 1) * ζ ^ (a₂ * d) else 0) -
     (if (-((n / d : ℕ) : ℤ)) ≡ a₁ [ZMOD M] then (-(((n / d : ℕ) : K) / M)) ^ (j - 1) * ζ ^ (-(a₂ * d)) else 0))

def eisF (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) : K :=
  if n = 0 then const0 j M ζ a₁ a₂ else coefPos j M ζ a₁ a₂ n

def smF (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) : K :=
  (c : K) ^ 2 * eisF j M ζ a₁ a₂ n - (c : K) ^ ((2 : ℤ) - j) * eisF j M ζ (c * a₁) (c * a₂) n

def cmul (f g : ℕ → K) (n : ℕ) : K := ∑ i ∈ range (n + 1), f i * g (n - i)

def up (p : ℕ) (f : ℕ → K) (n : ℕ) : K := f (p * n)

def vp (p : ℕ) (f : ℕ → K) (n : ℕ) : K := if p ∣ n then f (n / p) else 0

def rowIdx (N p n : ℕ) (γ : GL (Fin 2) (ZMod (p ^ n))) (i : Fin 2) (y : ℤ) : ℤ × ℤ :=
  ((N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 0).val,
   (N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 1).val + (p : ℤ) ^ n * y)

def piece (N p n m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (c d x t : ℤ) (ζ : K)
    (X : Finset (GL (Fin 2) (ZMod (p ^ n)))) (r : ℕ) : K :=
  -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
    ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ n) ζ (rowIdx N p n γ 0 (x * t)).1 (rowIdx N p n γ 0 (x * t)).2)
           (smF d 1 (N * p ^ n) ζ (rowIdx N p n γ 1 t).1 (rowIdx N p n γ 1 t).2) r

def unitSet (p n : ℕ) [NeZero p] : Finset (GL (Fin 2) (ZMod (p ^ n))) :=
  Finset.univ.filter fun γ => ¬ (p : ℕ) ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧
    ¬ (p : ℕ) ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val

def gaussS (p m : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (ζm : K) : K :=
  ∑ a : ZMod (p ^ m), ψ a * ζm ^ a.val

def ffPos (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) (full : Bool) (n : ℕ) : K :=
  ∑ d ∈ n.divisors, if (full || ¬ p ∣ d) && ¬ p ∣ (n / d) then
    (ψ ((n / d : ℕ) : ZMod (p ^ m)) * ((n / d : ℕ) : K) ^ (k - 2) * (ζ ^ (p ^ m)) ^ (x * t * d) -
     ψ (-((n / d : ℕ) : ZMod (p ^ m))) * (-((n / d : ℕ) : K)) ^ (k - 2) * (ζ ^ (p ^ m)) ^ (-(x * t * d)))
    else 0

def eePos (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K) (full : Bool) (n : ℕ) : K :=
  ∑ d ∈ n.divisors, if (full || ¬ p ∣ (n / d)) && ¬ p ∣ d then
    (ψ⁻¹ ((d : ℕ) : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (t * d) -
     ψ⁻¹ (-((d : ℕ) : ZMod (p ^ m))) * (ζ ^ (p ^ m)) ^ (-(t * d)))
    else 0

def lval (p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) : K :=
  ((p : K) ^ m) ^ (k - 2) * ∑ u ∈ range (p ^ m), ψ (u : ZMod (p ^ m)) *
    (-(((Polynomial.bernoulli (k - 1)).eval ((u : ℚ) / (p ^ m : ℕ)) / (k - 1 : ℕ) : ℚ) : K))

def eeConst (N p m : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K) : K :=
  (gaussS p m ψ (ζ ^ N))⁻¹ * ∑ v ∈ range (p ^ m), ψ (v : ZMod (p ^ m)) *
    ((1 / 2 : K) * (1 + ζ ^ ((N : ℤ) * v + (p : ℤ) ^ m * t)) / (1 - ζ ^ ((N : ℤ) * v + (p : ℤ) ^ m * t)))

def ffSer (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) (n : ℕ) : K :=
  if n = 0 then lval p m k ψ else ffPos N p m k ψ x t ζ true n

def eeSer (N p m : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K) (n : ℕ) : K :=
  if n = 0 then eeConst N p m ψ t ζ else eePos N p m ψ t ζ true n

def xSer (N p m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) : ℕ → K :=
  cmul (ffSer N p m k ψ x t ζ) (eeSer N p m ψ t ζ)

def coPt (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) : ℕ → K :=
  cmul (fun n => if n = 0 then 0 else ffPos N p m k ψ x t ζ false n)
       (fun n => if n = 0 then 0 else eePos N p m ψ t ζ false n)

def toQ (M : ℕ) (f : ℕ → K) (n : ℕ) : K := f (M * n)

def Integral (M : ℕ) (f : ℕ → K) : Prop := ∀ n, ¬ M ∣ n → f n = 0

end GlobalTheory.KummerEisensteinGalois
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
section
noncomputable section

open Polynomial Matrix
open scoped MatrixGroups

namespace GlobalTheory.HeckeFamilyMatrices

abbrev mat (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ)

def slP (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] →ₗ[ℂ] ℂ[X] :=
  ∑ i ∈ Finset.range (w + 1),
    (LinearMap.toSpanSingleton ℂ ℂ[X]
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i))).comp (lcoeff ℂ i)

def Z1 (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : Submodule ℂ (Γ → ℂ[X]) where
  carrier := {z | (∀ γ, z γ ∈ degreeLT ℂ (w + 1)) ∧
    ∀ γ δ : Γ, z (γ * δ) = slP w (mat δ) (z γ) + z δ}
  add_mem' := by
    rintro z z' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun γ => Submodule.add_mem _ (h1 γ) (h1' γ), fun γ δ => ?_⟩
    simp only [Pi.add_apply, h2, h2', map_add]
    abel
  zero_mem' := ⟨fun _ => Submodule.zero_mem _, fun _ _ => by simp⟩
  smul_mem' := by
    rintro c z ⟨h1, h2⟩
    refine ⟨fun γ => Submodule.smul_mem _ c (h1 γ), fun γ δ => ?_⟩
    simp only [Pi.smul_apply, h2, map_smul, smul_add]

def B1 (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : Submodule ℂ (Γ → ℂ[X]) :=
  LinearMap.range ((LinearMap.pi fun γ : Γ => slP w (mat γ) - LinearMap.id).comp (degreeLT ℂ (w + 1)).subtype)

def IsDCReps (Γ : Subgroup SL(2, ℤ)) (α : Matrix (Fin 2) (Fin 2) ℤ) {ι : Type} (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) :
    Prop :=
  (∀ i, ∃ γ₁ γ₂ : Γ, δ i = mat γ₁ * α * mat γ₂) ∧
    ∀ γ₁ γ₂ : Γ, ∃! i, ∃ γ : Γ, mat γ₁ * α * mat γ₂ = mat γ * δ i

open Classical in

def hk (Γ : Subgroup SL(2, ℤ)) (w : ℕ) {ι : Type} [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) :
    (Γ → ℂ[X]) →ₗ[ℂ] (Γ → ℂ[X]) :=
  LinearMap.pi fun γ : Γ =>
    if h : ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i) then
      ∑ i, (slP w (δ (h.choose i))).comp (LinearMap.proj (h.choose_spec i).choose)
    else 0

def dg (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![a, 0; 0, b]

def Lev (N l : ℕ) : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l

def IsDiam (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)) : Prop :=
  σ ∈ CongruenceSubgroup.Gamma0 (N * l) ∧ ((mat σ 1 1 : ℤ) : ZMod N) = d

def tqFam (q : ℕ) (σ : SL(2, ℤ)) : Fin (q + 1) → Matrix (Fin 2) (Fin 2) ℤ := fun i =>
  if (i : ℕ) < q then !![1, (i : ℤ); 0, (q : ℤ)] else mat σ * dg q 1

def ulFam (l : ℕ) : Fin l → Matrix (Fin 2) (Fin 2) ℤ := fun j => !![1, (j : ℤ); 0, (l : ℤ)]

def TqZ (Γ : Subgroup SL(2, ℤ)) (w q : ℕ) (σ : SL(2, ℤ)) : Module.End ℂ (Γ → ℂ[X]) := hk Γ w (tqFam q σ)

def UlZ (Γ : Subgroup SL(2, ℤ)) (w l : ℕ) : Module.End ℂ (Γ → ℂ[X]) := hk Γ w (ulFam l)

def DdZ (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (σ : SL(2, ℤ)) : Module.End ℂ (Γ → ℂ[X]) :=
  hk Γ w (fun _ : Unit => mat σ)

def toGL (g : Matrix (Fin 2) (Fin 2) ℤ) : GL (Fin 2) ℝ :=
  if h : g.det = 0 then 1 else
    Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℝ).mapMatrix g)
      (by rw [← RingHom.map_det]; simpa using h)

open scoped ModularForm in

def hkF (k : ℤ) {ι : Type} [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) (f : UpperHalfPlane → ℂ) :
    UpperHalfPlane → ℂ :=
  ∑ i, f ∣[k] toGL (δ i)

def TqF (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ := hkF k (tqFam q σ) f

def UlF (k : ℤ) (l : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ := hkF k (ulFam l) f

def DdF (k : ℤ) (σ : SL(2, ℤ)) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  hkF k (fun _ : Unit => mat σ) f

def eichler (w : ℕ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : ℂ[X] :=
  ∑ j ∈ Finset.range (w + 1),
    C ((w.choose j : ℂ) * ∫ t in (0 : ℝ)..1,
      (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) * X ^ j

def per (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (f : UpperHalfPlane → ℂ) : Γ → ℂ[X] := fun γ =>
  slP w (mat γ) (eichler w f ((γ : SL(2, ℤ)) • UpperHalfPlane.I))

def cj {Γ : Type} (z : Γ → ℂ[X]) : Γ → ℂ[X] := fun γ => (z γ).map (starRingEnd ℂ)

end GlobalTheory.HeckeFamilyMatrices
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
section
noncomputable section

open Polynomial

namespace GlobalTheory.NeedB

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

def kum {N : ℕ} (ζ θ : Ω) (g : Ω ≃ₐ[K] Ω) : ZMod N :=
  open Classical in
  if h : ∃ i : ZMod N, g θ = ζ ^ i.val * θ then h.choose else 0

def Inert (B : ValuationSubring Ω) (g : Ω ≃ₐ[K] Ω) : Prop :=
  ∀ x : Ω, B.valuation x ≤ 1 → B.valuation (g x - x) < 1

def Over (R : Subring K) (B : ValuationSubring Ω) : Prop :=
  ∀ x ∈ R, algebraMap K Ω x ∈ B

def RY (R : Subring K) : Subgroup (Ω ≃ₐ[K] Ω) :=
  (Subgroup.normalClosure {g | ∃ B : ValuationSubring Ω, Over R B ∧ Inert B g}).topologicalClosure

def ThmA : Prop :=
  ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 →
      a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ α (g * h) = kum ζ α g + kum ζ α h) ∧
      IsLocallyConstant (kum (K := K) (N := N) ζ α) ∧
      (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ β (g * h) = kum ζ β g + kum ζ β h) ∧
      IsLocallyConstant (kum (K := K) (N := N) ζ β) ∧
      ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧
        (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) ∧
        ∀ B : ValuationSubring Ω, Over (FunctionField.ringOfIntegers k K).toSubring B → ∀ g, Inert B g → η g = 0

def ThmB : Prop :=
  ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 →
      a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η →
        (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) →
        (∀ B : ValuationSubring Ω, Over (FunctionField.ringOfIntegers k K).toSubring B → ∀ g, Inert B g → η g = 0) →
        ∀ r ∈ RY (Ω := Ω) (FunctionField.ringOfIntegers k K).toSubring,
          η r = 0 ∧ kum (N := N) ζ α r = 0 ∧ kum (N := N) ζ β r = 0 ∧ ∀ g, η (g * r) = η g ∧ η (r * g) = η g

def IsFirstChernClassOfLineBundle (K : Type*) [Field K] : Prop :=
  ∀ (n d : ℕ) (f : MvPolynomial (Fin n) K), f.IsHomogeneous d → 0 < d → d < n →
    ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0

def Tsen : Prop :=
  ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra (RatFunc k) K] [FiniteDimensional (RatFunc k) K], IsFirstChernClassOfLineBundle K

def TsenCochain : Prop :=
  ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra (RatFunc k) K]
    [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ), 0 < N →
    ∀ z : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω) → ZMod N,
      IsLocallyConstant (fun p : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) => z p.1 p.2) →
      (∀ g h l, z h l - z (g * h) l + z g (h * l) - z g h = 0) →
      ∃ y : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant y ∧ ∀ g h, z g h = y h - y (g * h) + y g

def ClDiv : Prop :=
  ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] (N : ℕ), 0 < N →
    ∀ c : ClassGroup (FunctionField.ringOfIntegers k K), ∃ d, c = d ^ N

def PropC : Prop :=
  ∀ (k K Ω F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field F] [Algebra F K] [Algebra F Ω] [IsScalarTower F K Ω] [Normal F K]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ r ∈ (Subgroup.normalClosure {g : Ω ≃ₐ[F] Ω | (∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x) ∧
        ∃ B : ValuationSubring Ω, Over (FunctionField.ringOfIntegers k K).toSubring B ∧
          ∀ x : Ω, B.valuation x ≤ 1 → B.valuation (g x - x) < 1}).topologicalClosure,
      (∀ x : K, r (algebraMap K Ω x) = algebraMap K Ω x) ∧ r ζ = ζ ∧
      ∀ (γ : Ω) (c : F), c ≠ 0 → γ ^ N = algebraMap F Ω c → algebraMap F K c ∈ FunctionField.ringOfIntegers k K →
        (algebraMap F K c)⁻¹ ∈ FunctionField.ringOfIntegers k K → r γ = γ

theorem kum_choose_spec {N : ℕ} {ζ θ : Ω} {g : Ω ≃ₐ[K] Ω} (h : ∃ i : ZMod N, g θ = ζ ^ i.val * θ) :
    g θ = ζ ^ (kum (N := N) ζ θ g).val * θ := by
  classical
  unfold kum
  rw [dif_pos h]
  exact h.choose_spec

theorem kum_eq_of {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0) {g : Ω ≃ₐ[K] Ω}
    (i : ZMod N) (hi : g θ = ζ ^ i.val * θ) : kum (N := N) ζ θ g = i := by
  have hs := kum_choose_spec (N := N) ⟨i, hi⟩
  rw [hi] at hs
  have h2 : ζ ^ i.val = ζ ^ (kum (N := N) ζ θ g).val := mul_right_cancel₀ hθ hs
  exact (ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2)).symm

theorem kum_one {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0) :
    kum (N := N) ζ θ (1 : Ω ≃ₐ[K] Ω) = 0 :=
  kum_eq_of hζ hθ 0 (by simp)

theorem inert_one (B : ValuationSubring Ω) : Inert B (1 : Ω ≃ₐ[K] Ω) := by
  intro x _
  simp

theorem mem_RY_of_inert (R : Subring K) {B : ValuationSubring Ω} (hB : Over R B) {g : Ω ≃ₐ[K] Ω} (hg : Inert B g) :
    g ∈ RY R :=
  Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨B, hB, hg⟩)

theorem over_top (R : Subring K) : Over R (⊤ : ValuationSubring Ω) := fun _ _ => trivial

example : Over (⊤ : Subring ℚ) (⊤ : ValuationSubring ℂ) := over_top _

example : (1 : ℂ ≃ₐ[ℚ] ℂ) ∈ RY (⊤ : Subring ℚ) := mem_RY_of_inert _ (over_top _) (inert_one _)

example : kum (N := 2) (-1 : ℂ) 1 (1 : ℂ ≃ₐ[ℚ] ℂ) = 0 :=
  kum_one (IsPrimitiveRoot.neg_one 0 (by norm_num)) one_ne_zero

end GlobalTheory.NeedB
end
end

