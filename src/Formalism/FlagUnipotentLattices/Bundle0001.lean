import Mathlib
import Formalism.HyperbolicPlaceProducts.Bundle0001
import Formalism.FlagUnipotentLattices.DetIndexProductHyperbolicInequality
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

-- bundled from Formalism.FlagUnipotentLattices.DetIndexProductPlacesInequalitySq
section
open Module NumberField nonZeroDivisors

noncomputable section

namespace Formalism.HermitianLatticeCounting.LocalIntegralStructure

abbrev FreeQuotCard : Prop := Formalism.SLP.FreeQuotCard

abbrev GInj : Prop := Formalism.SLP.GInj

def EmbedGB : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [AddCommGroup B] [Finite B] (g : ℕ) (φ : A →+ B),
    Function.Injective φ → (∀ x, φ x ∈ (nsmulAddMonoidHom g : B →+ B).range) →
    Nat.card A ≤ Nat.card (nsmulAddMonoidHom g : B →+ B).range

def GramDetGen : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (t t' : R),
    (Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -t else 0) W Z
        (Matrix.diagonal fun i => if i = Fin.last r then -t' else 0)).det =
      (-1) ^ (r + 1) *
        (Z.det * W.det - t * t' * (Z.submatrix Fin.castSucc Fin.castSucc).det *
          (W.submatrix Fin.castSucc Fin.castSucc).det)

def GramDet : Prop :=
  ∀ (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (T T' : ℝ),
    (Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then (-(T : ℂ)) else 0)
        Z.conjTranspose Z
        (Matrix.diagonal fun i => if i = Fin.last r then (-(T' : ℂ)) else 0)).det =
      (-1) ^ (r + 1) *
        ((‖Z.det‖ ^ 2 - T * T' * ‖(Z.submatrix Fin.castSucc Fin.castSucc).det‖ ^ 2 : ℝ) : ℂ)

def GramNondeg : Prop :=
  ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (σ : K →+* K) (B : V →ₗ[K] V →ₛₗ[σ] K) (v : ι → V),
    (Matrix.of fun i j => B (v i) (v j)).det ≠ 0 →
    LinearIndependent K v ∧
      finrank K (Submodule.span K (Set.range v)) = Fintype.card ι ∧
      (∀ x ∈ Submodule.span K (Set.range v),
        (∀ y ∈ Submodule.span K (Set.range v), B y x = 0) → x = 0) ∧
      (∀ x ∈ Submodule.span K (Set.range v),
        (∀ y ∈ Submodule.span K (Set.range v), B x y = 0) → x = 0)

def QuadToJ : Prop :=
  ∀ (M : Matrix (Fin 2) (Fin 2) ℂ),
    (∀ u v : ℂ, ‖M 0 0 * u + M 0 1 * v‖ ^ 2 - ‖M 1 0 * u + M 1 1 * v‖ ^ 2 = ‖u‖ ^ 2 - ‖v‖ ^ 2) →
    M.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J * M = Formalism.SLP.GlobalBoundRefinements.J

def IsoBij : Prop :=
  ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), M.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J * M = Formalism.SLP.GlobalBoundRefinements.J →
    ‖M.det‖ = 1 ∧ Function.Bijective M.mulVec

def DenomNormFrac : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (α : E) (J : FractionalIdeal (𝓞 E)⁰ E),
    α ≠ 0 → J ≠ 0 → (∀ x ∈ J, IsInt (α * x)) →
    1 ≤ |Algebra.norm ℚ α| * FractionalIdeal.absNorm J

def DetIndexProductInequalitySq : Prop :=
  ∀ (detM dLa₁ dLa₂ dPs₁ dPs₂ i₁ i₂ G0₁ G0₂ g : ℝ) (e f : ℕ),
    0 < dPs₁ → 0 < dPs₂ → 0 < g → 0 ≤ i₁ → 0 ≤ i₂ → 0 ≤ dLa₁ → 0 ≤ dLa₂ →
    detM ^ 2 = dLa₁ * dLa₂ / (dPs₁ * dPs₂) →
    dLa₁ * i₁ ^ 2 ≤ G0₁ → dLa₂ * i₂ ^ 2 ≤ G0₂ →
    g ^ (2 * f * e) ≤ 4 ^ (e * f) * dPs₁ * dPs₂ →
    detM * i₁ * i₂ ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂)

def DetIndexProductPlacesInequalitySq : Prop :=
  ∀ (detM dLa₁ dLa₂ dPs₁ dPs₂ P₁ P₂ dQ₁ dQ₂ i₁ i₂ G0₁ G0₂ g NT K₁ K₂ Nr₁ Nr₂ : ℝ) (e f : ℕ),
    0 < P₁ → 0 < P₂ → 0 < dQ₁ → 0 < dQ₂ → 0 < g → 0 ≤ i₁ → 0 ≤ i₂ → 0 ≤ dLa₁ → 0 ≤ dLa₂ →
    0 < NT → 0 < K₁ → 0 < K₂ → 0 < Nr₁ → 0 < Nr₂ →
    detM ^ 2 = dLa₁ * dLa₂ / (dPs₁ * dPs₂) → dPs₁ = P₁ * dQ₁ → dPs₂ = P₂ * dQ₂ →
    dLa₁ * i₁ ^ 2 ≤ G0₁ / Nr₁ → dLa₂ * i₂ ^ 2 ≤ G0₂ / Nr₂ →
    NT / (Nr₂ * K₂ ^ 2) ≤ P₁ → NT / (Nr₁ * K₁ ^ 2) ≤ P₂ →
    g ^ (2 * f * e) ≤ 4 ^ (e * f) * dQ₁ * dQ₂ →
    detM * i₁ * i₂ ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT

def FormCoeffEq : Prop :=
  ∀ (a b c d : ℂ) (T T' : ℝ), 0 < T → 0 < T' →
    (∀ u v : ℂ, T * ‖a * u + b * v‖ ^ 2 - T' * ‖c * u + d * v‖ ^ 2 = T * ‖u‖ ^ 2 - T' * ‖v‖ ^ 2) →
    T' * ‖c‖ ^ 2 / T = T * ‖b‖ ^ 2 / T' ∧ ‖a‖ = ‖d‖

def DivGlob : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (e : E) (N : ℕ), 0 < N → IsInt e →
    (∀ P : Ideal (𝓞 E), P.IsPrime → (N : 𝓞 E) ∈ P → LocIn P e N) →
    ∃ β : 𝓞 E, e = (N : E) * (β : E)

end Formalism.HermitianLatticeCounting.LocalIntegralStructure
end
end

-- bundled from Formalism.FlagUnipotentLattices.LiftUnitaryFixesBase
section
noncomputable section

open scoped BigOperators
open Matrix

namespace Formalism.HermitianLatticeCounting.S6

def StrictUpper {R : Type} [Zero R] {j : ℕ} (A : Matrix (Fin j) (Fin j) R) : Prop :=
  ∀ b a : Fin j, a ≤ b → A b a = 0

def superSum {R : Type} [AddCommMonoid R] {j : ℕ} (A : Matrix (Fin j) (Fin j) R) : R :=
  ∑ a : Fin j, if h : a.val + 1 < j then A a ⟨a.val + 1, h⟩ else 0

def Zj {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V] {H : HermSpace K V}
    {r : ℕ} (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) : Matrix (Fin j) (Fin j) K :=
  (Zhat F F').submatrix (Fin.castLE (hj.trans (Nat.le_succ r))) (Fin.castLE (hj.trans (Nat.le_succ r)))

def CellExt : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (A A' : Matrix (Fin j) (Fin j) K),
    F.X = F.Xa j ⊔ II F F' → F'.X = F'.Xa j ⊔ II F F' →
    Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0 →
    StrictUpper A → StrictUpper A' → Aᵀ * Zj F F' j hj + Zj F F' j hj * A'.map star = 0 →
      ∃ Y : V →ₗ[K] V, F.LieN Y ∧ F'.LieN Y ∧
        (∀ a : Fin j, Y (F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a)) =
          ∑ b, A b a • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) ∧
        (∀ a : Fin j, Y (F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) a)) =
          ∑ b, A' b a • F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) ∧
        (∀ w : V, (∀ x ∈ F.Xa j ⊔ F'.Xa j, H.B x w = 0) → Y w = 0) ∧
        F.DPsi Y (superSum A) ∧ F'.DPsi Y (superSum A')

def CellRelevant : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (A A' : Matrix (Fin j) (Fin j) K),
    F.X = F.Xa j ⊔ II F F' → F'.X = F'.Xa j ⊔ II F F' →
    Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0 → Relevant F F' →
    StrictUpper A → StrictUpper A' → Aᵀ * Zj F F' j hj + Zj F F' j hj * A'.map star = 0 →
      superSum A + star (superSum A) = superSum A' + star (superSum A')

def CellRelevantE : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (A A' : Matrix (Fin j) (Fin j) K),
    (∃ μ : K, μ + star μ ≠ 0) → F.X = F.Xa j ⊔ II F F' → F'.X = F'.Xa j ⊔ II F F' →
    Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0 → Relevant F F' →
    StrictUpper A → StrictUpper A' → Aᵀ * Zj F F' j hj + Zj F F' j hj * A'.map star = 0 →
      superSum A = star (superSum A')

def CellRelevantAsm : Prop := CellExt → CellRelevant

def CellRelevantEAsm : Prop := CellRelevant → CellRelevantE

def InULift {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
    (H : HermSpace K V) (Wt : Submodule K V) (g : V →ₗ[K] V) : Prop :=
  (∀ x y : V, H.B (g x) (g y) = H.B x y) ∧ ∀ y : V, (∀ w ∈ Wt, H.B y w = 0) → g y = y

def LiftUnitaryFixesBase : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (Wt : Submodule K V) (g : V →ₗ[K] V), IsLift F F' Wt → InULift H Wt g →
      (∀ y ∈ V0 F F', g y = y) ∧ (∀ a : Fin (r + 1), g (F.e a) = F.e a) ∧
      (∀ a : Fin (r + 1), g (F'.e a) = F'.e a)

def LiftAniso : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (Wt : Submodule K V), F.Aniso → F'.Aniso → IsLift F F' Wt →
      ∀ w ∈ Wt, H.B w w = 0 → w = 0

def LiftDecomp : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r) (Wt : Submodule K V),
    F.Aniso → F'.Aniso → IsLift F F' Wt →
      ∀ y : V, ∃! w : V, w ∈ Wt ∧ ∀ w' ∈ Wt, H.B (y - w) w' = 0

def LiftUnitary : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r) (Wt : Submodule K V) (h : Wt →ₗ[K] Wt),
    F.Aniso → F'.Aniso → IsLift F F' Wt → (∀ x y : Wt, H.B (h x : V) (h y : V) = H.B (x : V) (y : V)) →
      ∃! g : V →ₗ[K] V, InULift H Wt g ∧ Function.Bijective g ∧ ∀ w : Wt, g (w : V) = (h w : V)

def LiftIsoW : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K) (Wt : Submodule K V),
    NFFull F F' j hj c → IsLift F F' Wt →
      (∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃! wt : V, wt ∈ Wt ∧ w - wt ∈ F.X) ∧
      (∀ w : V, (∀ a : Fin (r + 1), H.B (F'.e a) w = 0) → ∃! wt : V, wt ∈ Wt ∧ w - wt ∈ F'.X)

def ProdLeXi : Prop :=
  ∀ (l : ℕ) (la la' : Fin l → ℝ) (Xi Xi' : ℝ), (∀ a, 0 ≤ la a) → (∀ a, 0 ≤ la' a) →
    (∀ a, la a ≤ Xi) → (∀ a, la' a ≤ Xi') → ∏ a, la a * la' a ≤ (Xi * Xi') ^ l

def SgXi : Prop :=
  ∀ l Xi : ℝ, 0 < l → max 1 (max l (1 / l)) ≤ Xi → 1 ≤ Xi ∧ 1 / Xi ≤ l ∧ l ≤ Xi

def RelIndexInter : Prop :=
  ∀ (G : Type) [AddCommGroup G] (Lam₁ M W La : AddSubgroup G), La ≤ M ⊓ W →
    (Lam₁ ⊓ W).relIndex La ∣ Lam₁.relIndex M

def IndexChain : Prop :=
  ∀ (G : Type) [AddCommGroup G] (Lam₁ L W La : AddSubgroup G), Lam₁ ⊓ W ≤ La → La ≤ L ⊓ W →
    Lam₁.relIndex L ≠ 0 →
      La.relIndex (L ⊓ W) * (Lam₁ ⊓ W).relIndex La = (Lam₁ ⊓ W).relIndex (L ⊓ W) ∧
      (Lam₁ ⊓ W).relIndex (L ⊓ W) ≤ Lam₁.relIndex L

def BInGO : Prop :=
  ∀ (K U : Type) [Field K] [StarRing K] [AddCommGroup U] [Module K U] (h : U →ₗ[K] U →ₗ⋆[K] K)
    (O : Subring K) (g : K) (L₀ L₀' : Set U) (ι' : U → U) (η : U →ₗ[K] U),
    g ∈ O → star g = g → (∀ x ∈ L₀, ∀ y ∈ L₀, h x y ∈ O) →
    (∀ x ∈ L₀', ∀ y ∈ L₀', ∃ t ∈ O, h (ι' x) (ι' y) - h x y = g * t) →
    ∀ x' x'' : U, x' ∈ L₀ → x' ∈ L₀' → x'' ∈ L₀ → η x'' ∈ L₀' →
      (∃ l ∈ L₀, ι' x' - x' = g • l) → (∃ l ∈ L₀, ι' (η x'') - x'' = g • l) →
        ∃ t ∈ O, bEta h η x' x'' = g * t

def DetInPow : Prop :=
  ∀ (R : Type) [CommRing R] (J : Ideal R) (s : ℕ) (M : Matrix (Fin s) (Fin s) R),
    (∀ a b, M a b ∈ J) → M.det ∈ J ^ s

def DetBNorm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (g s f : ℕ) (I : Ideal (NumberField.RingOfIntegers E)),
    Module.finrank ℚ E = 2 * f → I ≠ ⊥ →
    I ≤ Ideal.span {(g : NumberField.RingOfIntegers E)} ^ s → g ^ (2 * s * f) ≤ Ideal.absNorm I

def DetBNormAsm : Prop := Formalism.SLP.IdealNormBound → DetBNorm

def mI (f : ℕ) (v dF : ℝ) (Lv : ℕ → ℝ) (i : ℕ) : ℝ :=
  (((i - 1).factorial : ℝ) * (v / Real.pi) ^ i) ^ f * (Real.sqrt dF)⁻¹ * Lv i

def MassRatio : Prop :=
  ∀ (f k s i : ℕ) (v dF Z : ℝ) (Lv : ℕ → ℝ), 1 ≤ v → 0 < dF → 1 ≤ Z →
    (∀ j, 3 ≤ j → (Z ^ f)⁻¹ ≤ Lv j ∧ Lv j ≤ Z ^ f) → s ≤ k → 3 ≤ i →
      (Real.pi ^ ((k - s) * f))⁻¹ * ((Z ^ 2) ^ f)⁻¹ ≤ mI f v dF Lv (k - s + i) / mI f v dF Lv i

def InvMI : Prop :=
  ∀ (f i : ℕ) (v dF Z : ℝ) (Lv : ℕ → ℝ), 1 ≤ v → 0 < dF → 1 ≤ Z → 3 ≤ i → (Z ^ f)⁻¹ ≤ Lv i →
    (mI f v dF Lv i)⁻¹ ≤ Real.pi ^ (i * f) * Z ^ f * Real.sqrt dF

def XiSBound : Prop :=
  ∀ (f k s : ℕ) (v dF Z Hh : ℝ) (Lv mass : ℕ → ℝ), 1 ≤ v → 0 < dF → 1 ≤ Z → 1 ≤ Hh →
    (∀ j, 3 ≤ j → (Z ^ f)⁻¹ ≤ Lv j ∧ Lv j ≤ Z ^ f) →
    (∀ j, 3 ≤ j → mass j = mI f v dF Lv j * mass (j - 1)) →
    0 < mass 1 → 0 < mass 2 → mass 1 ≤ Hh → mass 2 ≤ Hh → dF ≤ Hh → 3 ≤ k → 1 ≤ s → s < k →
      mass s * mass (k - s) / mass k ≤ Hh ^ 2 * (Real.pi * Z ^ 2) ^ (s * k * f)

def IsoTorsor : Prop :=
  ∀ (R K A B : Type) [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (qA : A → A → K) (qB : B → B → K),
    Finite {φ : B ≃ₗ[R] B // ∀ x y, qB (φ x) (φ y) = qB x y} →
      Finite {φ : A ≃ₗ[R] B // ∀ x y, qB (φ x) (φ y) = qA x y} ∧
      Nat.card {φ : A ≃ₗ[R] B // ∀ x y, qB (φ x) (φ y) = qA x y} ≤
        Nat.card {φ : B ≃ₗ[R] B // ∀ x y, qB (φ x) (φ y) = qB x y}

def PairsLoss : Prop :=
  ∀ (C s k : ℕ) (D' D'' NT Hh S' S'' : ℝ), s ≤ k → 1 ≤ Hh → 1 ≤ S' → 1 ≤ S'' → 0 ≤ D' → 0 ≤ D'' →
    0 ≤ NT → D' ≤ Hh * S' ^ 2 → D'' ≤ Hh * S'' ^ 2 → NT ≤ Hh →
      (D' * D'' * NT) ^ (C * s) ≤ Hh ^ (3 * C * s) * (S' * S'') ^ (2 * C * k)

def RatioSum : Prop :=
  ∀ (C k f : ℕ) (g Hh : ℝ), 0 < g → 1 ≤ Hh →
    ((C : ℝ) / g) ^ (k * f) * Hh ^ C * ((C * k * f : ℕ) : ℝ) ^ (4 * f) ≤ 1 / 2 →
      ∑ s ∈ Finset.Icc 1 (k - 1),
        ((C : ℝ) / g) ^ (s * k * f) * Hh ^ (C * s) * ((C * s * f : ℕ) : ℝ) ^ (4 * s * f) ≤ 1

def RatioBound : Prop :=
  ∀ C : ℕ, 1 ≤ C → ∃ C₀ : ℕ, ∀ (k r f : ℕ) (b g : ℝ), 2 ≤ b → 1 ≤ f → Real.log f ≤ (r : ℝ) ^ 2 →
    C₀ * (2 * r + 2) ^ 2 ≤ k → ((k : ℝ) * b) ^ 8 ≤ g →
      ((C : ℝ) / g) ^ (k * f) * (b ^ (C * (2 * r + 2) ^ 2 * f)) ^ C * ((C * k * f : ℕ) : ℝ) ^ (4 * f) ≤ 1 / 2

def SEqKCount : Prop :=
  ∀ (k f : ℕ) (g' g'' Hh S' S'' : ℝ), 1 ≤ k → 1 ≤ f → Real.log f ≤ k → 1 ≤ Hh → 1 ≤ S' → 1 ≤ S'' →
    0 ≤ g' → 0 ≤ g'' → g' ≤ Hh * S' ^ 2 → g'' ≤ Hh * S'' ^ 2 →
      (g' * g'') ^ ((k : ℝ) + (1 + Real.logb 2 (2 * f))) ≤ Hh ^ (10 * k) * (S' * S'') ^ (10 * k)

def SEqKClose : Prop :=
  ∀ (C k f : ℕ) (g Hh NT : ℝ), 4 ≤ C → 0 < g → 1 ≤ Hh → 0 ≤ NT → NT ≤ Hh →
    ((C : ℝ) / g) ^ (k * f) * Hh ^ C * ((C * k * f : ℕ) : ℝ) ^ (4 * f) ≤ 1 / 2 →
      (2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * NT ^ k * Hh ^ ((C - 1) * k) ≤ 1

end Formalism.HermitianLatticeCounting.S6
end
end

