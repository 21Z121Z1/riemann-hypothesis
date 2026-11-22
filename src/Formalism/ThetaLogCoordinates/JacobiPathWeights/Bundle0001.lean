import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.DefsCol
import Formalism.ThetaLogCoordinates.JacobiPathWeights.DetLetters

-- bundled from Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementB
section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def HStrip {n : ℕ} (ν μ : Fin n → ℤ) (b : ℕ) : Prop :=
  (∀ m, μ m ≤ ν m) ∧ (∀ m m' : Fin n, m.val + 1 = m'.val → ν m' ≤ μ m) ∧ ∑ m, ν m - ∑ m, μ m = (b : ℤ)

def IsPath (n : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ) (N : ℕ) : Prop :=
  μ 0 = 0 ∧ (∀ i ≤ N, Antitone (μ i)) ∧
    ∀ i < N, if isVec i then HStrip (μ (i + 1)) (μ i) (B i) else HStrip (μ i) (μ (i + 1)) (B i)

def CondC {r K : ℕ} (isVec : ℕ → Bool) (ν : ℕ → Fin r → ℤ) (κ : ℕ → Fin K → ℤ) (i : ℕ) : Prop :=
  ∀ (a : Fin r) (b : Fin K), a.val + 1 = r → b.val = 0 →
    if isVec i then κ (i + 1) b ≤ ν i a else κ i b ≤ ν (i + 1) a

def StripPathSplitting : Prop :=
  ∀ (r K N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ), 1 ≤ r → 1 ≤ K →
    (∀ μ : ℕ → Fin (r + K) → ℤ,
      IsPath (r + K) isVec B μ N ↔
        ∃ b' b'' : ℕ → ℕ, (∀ i < N, b' i + b'' i = B i) ∧
          IsPath r isVec b' (fun i a => μ i (Fin.castAdd K a)) N ∧
          IsPath K isVec b'' (fun i b => μ i (Fin.natAdd r b)) N ∧
          ∀ i < N, CondC isVec (fun i a => μ i (Fin.castAdd K a)) (fun i b => μ i (Fin.natAdd r b)) i) ∧
    (∀ (ν : ℕ → Fin r → ℤ) (κ : ℕ → Fin K → ℤ),
      (fun i a => (Fin.append (ν i) (κ i)) (Fin.castAdd K a)) = ν ∧
      (fun i b => (Fin.append (ν i) (κ i)) (Fin.natAdd r b)) = κ)

def colHeight {n : ℕ} (μ : Fin n → ℤ) (c : ℤ) : ℕ := (univ.filter fun m => c ≤ μ m).card

def PathColumns : Prop :=
  ∀ (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ), IsPath n isVec B μ N →
    (∀ i ≤ N, ∀ c (m : Fin n), c ≤ μ i m ↔ m.val < colHeight (μ i) c) ∧
    (∀ c : ℤ, colHeight (μ 0) c = if 1 ≤ c then 0 else n) ∧
    (∀ i < N, ∀ c : ℤ,
      if isVec i then
        colHeight (μ (i + 1)) c = colHeight (μ i) c ∨ colHeight (μ (i + 1)) c = colHeight (μ i) c + 1
      else
        colHeight (μ (i + 1)) c = colHeight (μ i) c ∨ colHeight (μ (i + 1)) c + 1 = colHeight (μ i) c) ∧
    (∀ i < N, {c : ℤ | colHeight (μ (i + 1)) c ≠ colHeight (μ i) c}.ncard = B i)

variable {ι : Type*}

def ordW (r K : ℕ) (isVec : ι → Bool) (om : ι → ℝ) : ι × Fin (r + K) → ℝ :=
  fun x => if (isVec x.1 = true ↔ r ≤ x.2.val) then om x.1 else 0

def OrdGe {σ R : Type*} [CommRing R] (w : σ → ℝ) (f : MvPolynomial σ R) (o : ℝ) : Prop :=
  ∀ e ∈ f.support, o ≤ Finsupp.weight w e

def colOrd (r : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (om : ι → ℝ) (l : ℕ) : ℝ :=
  ∑ m ∈ (range l).filter (fun m => colCostly r primal isVec lt m), om (lt m)

def rowX (R : Type*) [CommRing R] (r K : ℕ) (i : ι) : Fin (r + K) → MvPolynomial (ι × Fin (r + K)) R :=
  fun a => X (i, a)

def rowPl (R : Type*) [CommRing R] (r K : ℕ) (i : ι) : Fin r → MvPolynomial (ι × Fin (r + K)) R :=
  fun a => X (i, Fin.castAdd K a)

def rowNm (R : Type*) [CommRing R] (r K : ℕ) (i : ι) : Fin K → MvPolynomial (ι × Fin (r + K)) R :=
  fun b => X (i, Fin.natAdd r b)

def LowestPart (R : Type*) [CommRing R] (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (om : ι → ℝ) (L : ℕ) : Prop :=
  ∀ l ≤ L, ∀ I : Finset (Fin (r + K)),
    OrdGe (ordW r K isVec om) (colWord primal isVec lt (rowX R r K) l I) (colOrd r primal isVec lt om l) ∧
    weightedHomogeneousComponent (ordW r K isVec om) (colOrd r primal isVec lt om l)
        (colWord primal isVec lt (rowX R r K) l I) =
      joinF (colPl primal isVec lt (rowPl R r K) l) (colTan r primal isVec lt (rowNm R r K) l) I

def LowestComponent : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (om : ι → ℝ) (L : ℕ), 1 ≤ r → 1 ≤ K → ColValid r K primal isVec lt L →
    Set.InjOn lt (Set.Iio L) → (∀ l < L, 0 < om (lt l)) →
    (∀ l, l + 1 < L → om (lt (l + 1)) < om (lt l)) →
    LowestPart R r K primal isVec lt om L

def LemmaB2plus : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (om : ι → ℝ) (L : ℕ), 1 ≤ r → 1 ≤ K → ColValid r K primal isVec lt L →
    Set.InjOn lt (Set.Iio L) → (∀ l < L, 0 < om (lt l)) →
    (∀ l, l + 1 < L → om (lt (l + 1)) < om (lt l)) →
    ∀ l < L, ∀ I : Finset (Fin (r + K)),
      (if primal then ((planePart I).card : ℤ) < min (colDeg primal isVec lt (l + 1)) (r : ℤ)
        else (planePart I).Nonempty) →
      OrdGe (ordW r K isVec om) (colWord primal isVec lt (rowX R r K) (l + 1) I)
        (colOrd r primal isVec lt om (l + 1) + om (lt l))

def LemmaB2tie : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (om : ι → ℝ) (L : ℕ), 1 ≤ r → 1 ≤ K → ColValid r K primal isVec lt L →
    Set.InjOn lt (Set.Iio L) → (∀ l < L, 0 < om (lt l)) →
    (∀ l, l + 1 < L → om (lt (l + 1)) ≤ om (lt l)) →
    (∀ l, l + 1 < L → colCostly r primal isVec lt (l + 1) → om (lt (l + 1)) < om (lt l)) →
    LowestPart R r K primal isVec lt om L

def LemmaB2necessity : Prop :=
  ¬ LowestPart ℤ 1 1 true (fun i : Fin 2 => decide (i = 0)) (fun l => if l = 0 then 0 else 1)
      (fun _ => 1) 2

def FirstStepFree : Prop :=
  ∀ (ι : Type) (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (L : ℕ), 1 ≤ r → 1 ≤ L →
    ColValid r K primal isVec lt L → ¬ colCostly r primal isVec lt 0

def SymbolWordSupport : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) [DecidableEq ι] (r K : ℕ) (primal : Bool) (isVec : ι → Bool)
    (lt : ℕ → ι) (L : ℕ), 1 ≤ r → 1 ≤ K → ColValid r K primal isVec lt L → Set.InjOn lt (Set.Iio L) →
    ∀ l ≤ L, ∀ I : Finset (Fin (r + K)),
      (symWord primal isVec lt (rowPl R r K) (rowNm R r K) l I ≠ 0 →
        Nominal primal I ∧ (I.card : ℤ) = colDeg primal isVec lt l) ∧
      ∀ i : ι, IsWeightedHomogeneous (fun x : ι × Fin (r + K) => if x.1 = i then 1 else 0)
        (symWord primal isVec lt (rowPl R r K) (rowNm R r K) l I)
        (if ∃ m < l, lt m = i then 1 else 0)

def SymbolWordJoin : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) (r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι)
    (pl : ι → Fin r → R) (nm : ι → Fin K → R) (L : ℕ), 1 ≤ r → 1 ≤ K → ColValid r K primal isVec lt L →
    ∀ l ≤ L, symWord primal isVec lt pl nm l =
      joinF (colPl primal isVec lt pl l) (colTan r primal isVec lt nm l)

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

-- bundled from Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementE
section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def ValTop : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k),
    (valS isVec S G = ⊤ ↔ G = 0) ∧ (lam1S isVec S G = ⊥ ↔ G = 0)

def PropVa : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G H : MvPolynomial (LVar ι ζ n) k),
    valS isVec S (G * H) = valS isVec S G + valS isVec S H ∧
    min (valS isVec S G) (valS isVec S H) ≤ valS isVec S (G + H) ∧
    lam1S isVec S (G * H) = lam1S isVec S G + lam1S isVec S H ∧
    lam1S isVec S (G + H) ≤ max (lam1S isVec S G) (lam1S isVec S H)

def PropVe : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)],
    (2 ≤ n → ∀ (i : ι) (a : Fin n), i ∈ S →
      (isVec i = true →
        valS isVec S (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) k) = 0 ∧
        lam1S isVec S (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) k) = 1) ∧
      (isVec i = false →
        valS isVec S (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) k) = ((-1 : ℤ) : WithTop ℤ) ∧
        lam1S isVec S (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) k) = 0)) ∧
    (∀ (i : ι) (a : Fin n), i ∉ S →
      valS isVec S (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) k) = 0 ∧
      lam1S isVec S (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) k) = 0) ∧
    (∀ z : ζ,
      valS isVec S (X (Sum.inr z) : MvPolynomial (LVar ι ζ n) k) = 0 ∧
      lam1S isVec S (X (Sum.inr z) : MvPolynomial (LVar ι ζ n) k) = 0) ∧
    (∀ c : k, c ≠ 0 →
      valS isVec S (C c : MvPolynomial (LVar ι ζ n) k) = 0 ∧
      lam1S isVec S (C c : MvPolynomial (LVar ι ζ n) k) = 0) ∧
    (1 ≤ n → ∀ A : Fin n → ι, Function.Injective A → (∀ l, A l ∈ S ∧ isVec (A l) = true) →
      valS isVec S (detLetters (ζ := ζ) k A) = 1 ∧ lam1S isVec S (detLetters (ζ := ζ) k A) = 1)

def PropVdSub : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (θ : WithTop ℤ) (M : WithBot ℤ) (c : k) (G H : MvPolynomial (LVar ι ζ n) k),
    (θ ≤ valS isVec S G → θ ≤ valS isVec S H → θ ≤ valS isVec S (c • G + H)) ∧
    (lam1S isVec S G ≤ M → lam1S isVec S H ≤ M → lam1S isVec S (c • G + H) ≤ M)

def CornerValSpecialize : Prop :=
  ∀ (k k₁ : Type) [Field k] [Field k₁] (φ : k →+* k₁) (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι)
    [DecidablePred (· ∈ S)] (G : MvPolynomial (LVar ι ζ n) k) (θ : ℤ) (g₀ : (Matrix (Fin n) (Fin n) k₁)ˣ),
    (θ : WithTop ℤ) ≤ valS isVec S G →
    ∀ j ∈ (conjAct φ isVec S (↑g₀ : Matrix _ _ k₁) (↑g₀⁻¹ : Matrix _ _ k₁) true G).coeff.support, θ ≤ j

def sharpHom {k₁ ι ζ : Type*} [CommRing k₁] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (g gi : Matrix (Fin n) (Fin n) k₁) :
    MvPolynomial (LVar ι ζ n) k₁ →ₐ[k₁] MvPolynomial (LVar ι ζ n) k₁ :=
  aeval fun x =>
    match x with
    | Sum.inl (i, a) =>
      if i ∈ S then
        (if isVec i then Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C) a
        else Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C).transpose a)
      else X (Sum.inl (i, a))
    | Sum.inr z => X (Sum.inr z)

def lastExp {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (e : LVar ι ζ n →₀ ℕ) : ℤ :=
  e.sum fun x d => match x with
    | Sum.inl (i, a) => if i ∈ S ∧ a.val + 1 = n then (if isVec i then (d : ℤ) else -(d : ℤ)) else 0
    | Sum.inr _ => 0

def CoordChangeCoeff : Prop :=
  ∀ (k₁ : Type) [Field k₁] (ι ζ : Type) (n : ℕ) (isVec : ι → Bool) (S : Set ι)
    [DecidablePred (· ∈ S)] (g₀ : (Matrix (Fin n) (Fin n) k₁)ˣ) (H : MvPolynomial (LVar ι ζ n) k₁),
    (∀ j : ℤ,
      (conjAct (RingHom.id k₁) isVec S (↑g₀ : Matrix _ _ k₁) (↑g₀⁻¹ : Matrix _ _ k₁) true
          (sharpHom isVec S (↑g₀ : Matrix _ _ k₁) (↑g₀⁻¹ : Matrix _ _ k₁) H)).coeff j =
        sharpHom isVec S (↑g₀ : Matrix _ _ k₁) (↑g₀⁻¹ : Matrix _ _ k₁)
          (∑ e ∈ H.support.filter (fun e => lastExp isVec S e = j), monomial e (coeff e H))) ∧
    Function.Bijective (sharpHom (ζ := ζ) (n := n) isVec S (↑g₀ : Matrix (Fin n) (Fin n) k₁)
      (↑g₀⁻¹ : Matrix (Fin n) (Fin n) k₁))

def LetterDetIrreducible : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (r : ℕ) (A : Fin r → ι), 1 ≤ r → Function.Injective A →
    Irreducible (detLetters (ζ := ζ) k A)

def PowDvdOfFractionField : Prop :=
  ∀ (R₀ Q₀ : Type) [CommRing R₀] [IsDomain R₀] [UniqueFactorizationMonoid R₀] [Field Q₀] [Algebra R₀ Q₀]
    [IsFractionRing R₀ Q₀] (Z : Type) (D G : MvPolynomial Z R₀) (m : ℕ),
    Irreducible D → (∀ c : R₀, D ≠ C c) →
    (map (algebraMap R₀ Q₀) D) ^ m ∣ map (algebraMap R₀ Q₀) G → D ^ m ∣ G

def LemmaEa : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (r : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (U : Set ι) [DecidablePred (· ∈ U)] (A : Fin r → ι) (G : MvPolynomial (LVar ι ζ r) k) (B' : ℕ) (θ : ℤ),
    1 ≤ r → Function.Injective A → (∀ l, A l ∈ S ∧ isVec (A l) = true) →
    (∀ i, i ∈ U ↔ i ∈ S ∧ isVec i = true ∧ ∀ l, A l ≠ i) →
    G ≠ 0 → (∀ e ∈ G.support, degIn U e ≤ B') → (θ : WithTop ℤ) ≤ valS isVec S G → (B' : ℤ) < θ →
    (detLetters k A) ^ (θ - B').toNat ∣ G

def PropEb : Prop :=
  ∀ (k : Type) [Field k] (ι ζ : Type) (r : ℕ) (isVec : ι → Bool) (S' : Set ι) [DecidablePred (· ∈ S')]
    (A : Fin r → ι), 1 ≤ r → Function.Injective A → (∀ l, isVec (A l) = true) →
    ((∀ l, A l ∈ S') → valS isVec S' (detLetters (ζ := ζ) k A) = 1) ∧
    ((∃ l, A l ∉ S') → valS isVec S' (detLetters (ζ := ζ) k A) = 0) ∧
    ∀ (H : MvPolynomial (LVar ι ζ r) k) (m : ℕ),
      valS isVec S' ((detLetters k A) ^ m * H) = valS isVec S' H + m • valS isVec S' (detLetters (ζ := ζ) k A) ∧
      valS isVec S' ((detLetters k A) ^ m * H) ≤ valS isVec S' H + (m : WithTop ℤ)

def LemmaEint : Prop :=
  ∀ (O Kf : Type) [CommRing O] [IsDomain O] [UniqueFactorizationMonoid O] [Field Kf] [Algebra O Kf]
    [IsFractionRing O Kf] (ι ζ : Type) (r : ℕ) (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (U : Set ι) [DecidablePred (· ∈ U)] (A : Fin r → ι) (G : MvPolynomial (LVar ι ζ r) O) (B' : ℕ) (θ : ℤ),
    1 ≤ r → Function.Injective A → (∀ l, A l ∈ S ∧ isVec (A l) = true) →
    (∀ i, i ∈ U ↔ i ∈ S ∧ isVec i = true ∧ ∀ l, A l ≠ i) →
    G ≠ 0 → (∀ e ∈ G.support, degIn U e ≤ B') →
    (θ : WithTop ℤ) ≤ valS isVec S (map (algebraMap O Kf) G) → (B' : ℤ) < θ →
    (detLetters O A) ^ (θ - B').toNat ∣ G

def PropEsharp : Prop :=
  ∀ (k : Type) [Field k],
    valS (ζ := Empty) (fun _ : Fin 3 => true) Set.univ
      (detLetters k (fun l : Fin 2 => (Fin.castSucc l : Fin 3)) *
        detLetters k (fun l : Fin 2 => if l = 0 then (0 : Fin 3) else 2)) = 2 ∧
    ¬ (detLetters (ζ := Empty) k (fun l : Fin 2 => (Fin.castSucc l : Fin 3))) ^ 2 ∣
      (detLetters k (fun l : Fin 2 => (Fin.castSucc l : Fin 3)) *
        detLetters k (fun l : Fin 2 => if l = 0 then (0 : Fin 3) else 2))

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

