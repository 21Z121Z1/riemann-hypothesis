import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.LiftWord
import Formalism.ThetaLogCoordinates.JacobiPathWeights.Bundle0001

-- bundled from Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementA
section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def nthElt {n : ℕ} (J : Finset (Fin n)) (a : ℕ) : ℕ := ((J.sort (· ≤ ·)).map Fin.val).getD a n

def SemiStd {n C : ℕ} (T : Fin C → Finset (Fin n)) : Prop :=
  ∀ c c' : Fin C, c.val + 1 = c'.val → ∀ a < (T c').card, nthElt (T c) a ≤ nthElt (T c') a

def initSeg (n h : ℕ) : Finset (Fin n) := univ.filter fun m => m.val < h

def genX (k : Type*) [CommRing k] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k) :=
  Matrix.of fun a b => X (a, b)

def tabMinors (k : Type*) [CommRing k] {n C : ℕ} (T : Fin C → Finset (Fin n)) :
    MvPolynomial (Fin n × Fin n) k :=
  ∏ c, minorF (genX k n) (initSeg n (T c).card) (T c)

def tabDiag {n C : ℕ} (T : Fin C → Finset (Fin n)) : Fin n × Fin n →₀ ℕ :=
  ∑ c, ∑ b ∈ T c, ∑ a : Fin n,
    if a.val = ((T c).filter (· < b)).card then Finsupp.single (a, b) 1 else 0

def LeadingMinors : Prop :=
  ∀ (k : Type) [CommRing k] (n C : ℕ) (T : Fin C → Finset (Fin n)),
    coeff (tabDiag T) (tabMinors k T) = 1 ∧
    (∀ e ∈ (tabMinors k T).support, e ≠ tabDiag T →
      ∃ x : Fin n × Fin n, e x < tabDiag T x ∧
        ∀ y : Fin n × Fin n, (y.1 < x.1 ∨ (y.1 = x.1 ∧ y.2 < x.2)) → e y = tabDiag T y) ∧
    (∀ T' : Fin C → Finset (Fin n), SemiStd T → SemiStd T' → tabDiag T = tabDiag T' → T = T')

def LemmaA : Prop :=
  ∀ (k : Type) [Field k] (n C : ℕ),
    LinearIndependent k (fun T : {T : Fin C → Finset (Fin n) // SemiStd T} => tabMinors k T.1)

def pathWord {R : Type*} [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (Xr : ℕ → Fin n → R) : ℕ → Form R n
  | 0 => oneF
  | i + 1 =>
    if colHeight (μ (i + 1)) c = colHeight (μ i) c then pathWord isVec μ c Xr i
    else stepF (isVec i == decide (1 ≤ c)) (pathWord isVec μ c Xr i) (Xr i)

def canIdx {n : ℕ} (μN : Fin n → ℤ) (c : ℤ) : Finset (Fin n) :=
  if 1 ≤ c then univ.filter fun m => m.val < colHeight μN c
  else univ.filter fun m => colHeight μN c ≤ m.val

def psiPath (R : Type*) [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (N : ℕ)
    (I : ℤ → Finset (Fin n)) : MvPolynomial (ℕ × Fin n) R :=
  ∏ᶠ c : ℤ, pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c)

def IsIndex {n : ℕ} (μN : Fin n → ℤ) (I : ℤ → Finset (Fin n)) : Prop :=
  ∀ c : ℤ, (I c).card = if 1 ≤ c then colHeight μN c else n - colHeight μN c

def PathWordIsColWord : Prop :=
  ∀ (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ) (c : ℤ), IsPath n isVec B μ N →
    ∃ (L : ℕ) (lt : ℕ → ℕ), StrictMono lt ∧ (∀ l < L, lt l < N) ∧
      (∀ i < N, colHeight (μ (i + 1)) c ≠ colHeight (μ i) c ↔ ∃ l < L, lt l = i) ∧
      (∀ l ≤ L, 0 ≤ colDeg (decide (1 ≤ c)) isVec lt l ∧ colDeg (decide (1 ≤ c)) isVec lt l ≤ (n : ℤ)) ∧
      (∀ l < L, colDeg (decide (1 ≤ c)) isVec lt l =
        if 1 ≤ c then (colHeight (μ (lt l)) c : ℤ) else (n : ℤ) - colHeight (μ (lt l)) c) ∧
      (colDeg (decide (1 ≤ c)) isVec lt L =
        if 1 ≤ c then (colHeight (μ N) c : ℤ) else (n : ℤ) - colHeight (μ N) c) ∧
      ∀ (R : Type) [CommRing R] (Xr : ℕ → Fin n → R),
        pathWord isVec μ c Xr N = colWord (decide (1 ≤ c)) isVec lt Xr L

def PsiDegrees : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ)
    (I : ℤ → Finset (Fin n)), IsPath n isVec B μ N → IsIndex (μ N) I →
    (Function.mulSupport fun c : ℤ =>
      pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c)).Finite ∧
    ∀ i : ℕ, IsWeightedHomogeneous (fun x : ℕ × Fin n => if x.1 = i then 1 else 0)
      (psiPath R isVec μ N I) (if i < N then B i else 0)

def expE (R : Type*) [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (a b : Fin n) :
    MvPolynomial (ℕ × Fin n) R →ₐ[R] Polynomial (MvPolynomial (ℕ × Fin n) R) :=
  aeval fun x =>
    if isVec x.1 then
      (if x.2 = b then Polynomial.C (X x) + Polynomial.X * Polynomial.C (X (x.1, a)) else Polynomial.C (X x))
    else
      (if x.2 = a then Polynomial.C (X x) - Polynomial.X * Polynomial.C (X (x.1, b)) else Polynomial.C (X x))

def LemmaA1hw : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ),
    IsPath n isVec B μ N →
    (∀ m : Fin n, IsWeightedHomogeneous
      (fun x : ℕ × Fin n => if x.2 = m then (if isVec x.1 then (1 : ℤ) else -1) else 0)
      (psiPath R isVec μ N (canIdx (μ N))) (μ N m)) ∧
    ∀ a b : Fin n, a < b →
      expE R isVec a b (psiPath R isVec μ N (canIdx (μ N))) =
        Polynomial.C (psiPath R isVec μ N (canIdx (μ N)))

def PathProductLinearIndependent : Prop :=
  ∀ (k : Type) [Field k] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (ν : Fin n → ℤ),
    LinearIndependent k
      (fun P : {μ : ℕ → Fin n → ℤ // IsPath n isVec B μ N ∧ μ N = ν ∧ ∀ i, N < i → μ i = 0} =>
        psiPath k isVec P.1 N (canIdx ν))

def LemmaA1lead : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ),
    IsPath n isVec B μ (N + 1) →
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ e : ℕ × Fin n →₀ ℕ, (∀ x ∈ e.support, x.1 < N) →
        coeff (e + ∑ m : Fin n, Finsupp.single (N, m) (|μ (N + 1) m - μ N m|).toNat)
            (psiPath R isVec μ (N + 1) (canIdx (μ (N + 1)))) =
          (ε : R) * coeff e (psiPath R isVec μ N (canIdx (μ N)))

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

-- bundled from Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementC
section
noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def FrobLift (p : ℕ) {W : Type*} [CommRing W] (σ : RingAut W) : Prop := ∀ a : W, (p : W) ∣ σ a - a ^ p

def PlaneEq : Prop :=
  ∀ (W : Type) [CommRing W] (p r K : ℕ) (g h : (Matrix (Fin (r + K)) (Fin (r + K)) W)ˣ),
    (∀ ξ : Fin (r + K) → W,
      (∀ b : Fin K, (p : W) ∣ Matrix.vecMul ξ (↑g : Matrix _ _ W) (Fin.natAdd r b)) ↔
      (∀ b : Fin K, (p : W) ∣ Matrix.vecMul ξ (↑(g * h) : Matrix _ _ W) (Fin.natAdd r b))) ↔
    ∀ (a : Fin r) (b : Fin K), (p : W) ∣ (↑h : Matrix _ _ W) (Fin.castAdd K a) (Fin.natAdd r b)

def planeGens {ι W O : Type*} [CommRing W] [CommRing O] [Algebra W O] (r K : ℕ) (isVec : ι → Bool) (w : O)
    (σ : RingAut W) (s : ι → ℤ) (h : (Matrix (Fin (r + K)) (Fin (r + K)) W)ˣ) :
    Set (MvPolynomial (ι × Fin (r + K)) (Localization.Away w)) :=
  Set.range fun x : ι × Fin (r + K) =>
    (if heavy r K isVec x then C (IsLocalization.Away.invSelf w) else 1) *
      (if isVec x.1 then
        Matrix.vecMul (fun a => (X (x.1, a) : MvPolynomial (ι × Fin (r + K)) (Localization.Away w)))
          ((↑h : Matrix _ _ W).map fun c =>
            C (algebraMap O (Localization.Away w) (algebraMap W O ((σ ^ s x.1) c)))) x.2
      else
        Matrix.vecMul (fun a => (X (x.1, a) : MvPolynomial (ι × Fin (r + K)) (Localization.Away w)))
          ((↑h⁻¹ : Matrix _ _ W).map fun c =>
            C (algebraMap O (Localization.Away w) (algebraMap W O ((σ ^ s x.1) c)))).transpose x.2)

def PlaneAlgebraInvariant : Prop :=
  ∀ (ι W O : Type) [CommRing W] [CommRing O] [Algebra W O] (p r K : ℕ) (isVec : ι → Bool) (w : O)
    (σ : RingAut W) (s : ι → ℤ) (h : (Matrix (Fin (r + K)) (Fin (r + K)) W)ˣ),
    w ^ 2 = (p : O) →
    (∀ (a : Fin r) (b : Fin K), (p : W) ∣ (↑h : Matrix _ _ W) (Fin.castAdd K a) (Fin.natAdd r b)) →
    Algebra.adjoin O (planeGens r K isVec w σ s h) = Algebra.adjoin O (planeGens r K isVec w σ s 1)

def ScaleHeavyCoeff : Prop :=
  ∀ (ι O : Type) [CommRing O] (r K : ℕ) (isVec : ι → Bool) (w : O)
    (f : MvPolynomial (ι × Fin (r + K)) O),
    (∀ m, coeff m (planeEmb r K isVec w f) = w ^ heavyDeg r K isVec m * coeff m f) ∧
    ∀ j : ℕ, (C w) ^ j ∣ planeEmb r K isVec w f ↔ ∀ m, w ^ j ∣ w ^ heavyDeg r K isVec m * coeff m f

def PlaneRingFacts : Prop :=
  ∀ (ι O : Type) [CommRing O] [IsDomain O] (r K : ℕ) (isVec : ι → Bool) (w : O), w ≠ 0 →
    Function.Injective (planeEmb (ι := ι) r K isVec w) ∧
    (Prime w → Prime (C w : MvPolynomial (ι × Fin (r + K)) O))

def FactX2mul : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (K : Form R n) (m m' : Matrix (Fin n) (Fin n) R),
    actF K 1 = K ∧ actF (actF K m) m' = actF K (m * m')

def FactX2wedge : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (K : Form R n) (X : Fin n → R) (m : Matrix (Fin n) (Fin n) R),
    actF (wedgeF K X) m = wedgeF (actF K m) (Matrix.vecMul X m)

def FactX2contr : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (K : Form R n) (Y : Fin n → R) (m : (Matrix (Fin n) (Fin n) R)ˣ),
    actF (contrF K Y) (↑m : Matrix _ _ R) =
      contrF (actF K (↑m : Matrix _ _ R)) (Matrix.vecMul Y (↑m⁻¹ : Matrix _ _ R).transpose)

def MinorMap : Prop :=
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (n : ℕ) (m : Matrix (Fin n) (Fin n) R)
    (I J : Finset (Fin n)), φ (minorF m I J) = minorF (m.map φ) I J

def ContractWedge : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (K : Form R n) (X Y : Fin n → R),
    contrF (wedgeF K X) Y = (fun I => (∑ a, X a * Y a) * K I) - wedgeF (contrF K Y) X

def SumPowCongr : Prop :=
  ∀ (R : Type) [CommRing R] (p e : ℕ) (κ : Type) (t : Finset κ) (a : κ → R), p.Prime →
    (p : R) ∣ (∑ x ∈ t, a x) ^ (p ^ e) - ∑ x ∈ t, a x ^ (p ^ e)

def FrobeniusPowCongr : Prop :=
  ∀ (W : Type) [CommRing W] (p e : ℕ) (σ : RingAut W) (b : W), p.Prime → FrobLift p σ →
    (p : W) ∣ b ^ (p ^ e) - (σ ^ e) b

def AevalPowCongr : Prop :=
  ∀ (R : Type) [CommRing R] (p e : ℕ) (τ : Type) (f : MvPolynomial τ ℤ) (z : τ → R), p.Prime →
    (p : R) ∣ (aeval z f) ^ (p ^ e) - aeval (fun x => z x ^ (p ^ e)) f

def LiftedWordIntegral : Prop :=
  ∀ (ι : Type) [DecidableEq ι] (p n : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (s : ι → ℤ)
    (z : ℤ) (L : ℕ), p.Prime → Set.InjOn lt (Set.Iio L) →
    (∀ l, l + 1 < L → s (lt l) ≤ s (lt (l + 1))) → (∀ l < L, s (lt l) ≤ z) →
    (∀ (R : Type) [CommRing R] (Xr : ι → Fin n → R) (l : ℕ) (I : Finset (Fin n)),
      liftWord p primal isVec lt s Xr l I =
        aeval (fun x : ι × Fin n => Xr x.1 x.2)
          (liftWord p primal isVec lt s (fun i a => (X (i, a) : MvPolynomial (ι × Fin n) ℤ)) l I)) ∧
    (∀ l, 1 ≤ l → l ≤ L → ∀ (I : Finset (Fin n)) (i : ι),
      IsWeightedHomogeneous (fun x : ι × Fin n => if x.1 = i then 1 else 0)
        (liftWord p primal isVec lt s (fun i a => (X (i, a) : MvPolynomial (ι × Fin n) ℤ)) l I)
        (if ∃ m < l, lt m = i then p ^ (s (lt (l - 1)) - s i).toNat else 0)) ∧
    (∀ (I : Finset (Fin n)) (i : ι),
      IsWeightedHomogeneous (fun x : ι × Fin n => if x.1 = i then 1 else 0)
        (liftCol p primal isVec lt s z (fun i a => (X (i, a) : MvPolynomial (ι × Fin n) ℤ)) L I)
        (if ∃ m < L, lt m = i then levP p s z i else 0))

def LiftedWordNominal : Prop :=
  ∀ (ι W O : Type) [CommRing W] [CommRing O] [Algebra W O] (p r K : ℕ) (primal : Bool) (isVec : ι → Bool)
    (lt : ℕ → ι) (s : ι → ℤ) (z : ℤ) (L : ℕ) (w : O) (σ : RingAut W)
    (h : (Matrix (Fin (r + K)) (Fin (r + K)) W)ˣ),
    p.Prime → 1 ≤ r → 1 ≤ K → w ^ 2 = (p : O) → FrobLift p σ → ColValid r K primal isVec lt L →
    PosHyp r primal isVec lt s z L →
    ∀ l ≤ L, ∃ Sg T : Form (MvPolynomial (ι × Fin (r + K)) O) (r + K),
      (∀ J, actF (liftWord p primal isVec lt s (frameRow r K isVec w σ s h) l)
          (frameM r K primal lt σ s h l) J =
        (C w) ^ nomOrd p r primal isVec lt s l * (Sg J + C w * T J)) ∧
      ∀ J, Sg J ≠ 0 → Nominal primal J

def LiftedColumnDivisible : Prop :=
  ∀ (ι W O : Type) [CommRing W] [CommRing O] [Algebra W O] (p r K : ℕ) (primal : Bool) (isVec : ι → Bool)
    (lt : ℕ → ι) (s : ι → ℤ) (z : ℤ) (L : ℕ) (w : O) (σ : RingAut W)
    (h : (Matrix (Fin (r + K)) (Fin (r + K)) W)ˣ),
    p.Prime → 1 ≤ r → 1 ≤ K → w ^ 2 = (p : O) → FrobLift p σ → ColValid r K primal isVec lt L →
    PosHyp r primal isVec lt s z L →
    ∀ I, (C w) ^ nomOrdC p r primal isVec lt s z L ∣
      liftCol p primal isVec lt s z (frameRow r K isVec w σ s h) L I

def LiftedColumnSymbol : Prop :=
  ∀ (ι O : Type) [CommRing O] (p r K : ℕ) (primal : Bool) (isVec : ι → Bool)
    (lt : ℕ → ι) (s : ι → ℤ) (z : ℤ) (L : ℕ) (w : O),
    p.Prime → 1 ≤ r → 1 ≤ K → w ^ 2 = (p : O) → ColValid r K primal isVec lt L →
    PosHyp r primal isVec lt s z L →
    ∀ I, (C w) ^ (nomOrdC p r primal isVec lt s z L + 1) ∣
      liftCol p primal isVec lt s z (planeRow r K isVec w) L I -
        (C w) ^ nomOrdC p r primal isVec lt s z L *
          symWord primal isVec lt
            (fun i a => (X (i, Fin.castAdd K a) : MvPolynomial (ι × Fin (r + K)) O) ^ levP p s z i)
            (fun i b => (X (i, Fin.natAdd r b) : MvPolynomial (ι × Fin (r + K)) O) ^ levP p s z i) L I

def NominalOrderSum : Prop :=
  ∀ (ι : Type) (p r K : ℕ) (primal : Bool) (isVec : ι → Bool) (lt : ℕ → ι) (s : ι → ℤ) (z : ℤ) (L : ℕ),
    p.Prime → 1 ≤ r → 1 ≤ L → ColValid r K primal isVec lt L → PosHyp r primal isVec lt s z L →
    nomOrdC p r primal isVec lt s z L =
      ∑ m ∈ (range L).filter (fun m => colCostly r primal isVec lt m), levP p s z (lt m) ∧
    nomOrdC p r primal isVec lt s z L * (p - 1) < levP p s z (lt 0)

def SymbolWordScaling : Prop :=
  ∀ (ι O : Type) [CommRing O] (p r K : ℕ) (primal : Bool) (isVec : ι → Bool)
    (lt : ℕ → ι) (s : ι → ℤ) (z : ℤ) (L : ℕ) (w : O),
    p.Prime → 1 ≤ r → 1 ≤ K → w ^ 2 = (p : O) → ColValid r K primal isVec lt L →
    Set.InjOn lt (Set.Iio L) → PosHyp r primal isVec lt s z L →
    ∀ I,
      (∀ e ∈ (symWord primal isVec lt
            (fun i a => (X (i, Fin.castAdd K a) : MvPolynomial (ι × Fin (r + K)) O) ^ levP p s z i)
            (fun i b => (X (i, Fin.natAdd r b) : MvPolynomial (ι × Fin (r + K)) O) ^ levP p s z i) L I).support,
          heavyDeg r K isVec e = nomOrdC p r primal isVec lt s z L) ∧
      planeEmb r K isVec w (symWord primal isVec lt
            (fun i a => (X (i, Fin.castAdd K a) : MvPolynomial (ι × Fin (r + K)) O) ^ levP p s z i)
            (fun i b => (X (i, Fin.natAdd r b) : MvPolynomial (ι × Fin (r + K)) O) ^ levP p s z i) L I) =
        (C w) ^ nomOrdC p r primal isVec lt s z L *
          symWord primal isVec lt
            (fun i a => (X (i, Fin.castAdd K a) : MvPolynomial (ι × Fin (r + K)) O) ^ levP p s z i)
            (fun i b => (X (i, Fin.natAdd r b) : MvPolynomial (ι × Fin (r + K)) O) ^ levP p s z i) L I ∧
      (C w) ^ (nomOrdC p r primal isVec lt s z L + 1) ∣
        planeEmb r K isVec w
          (liftCol p primal isVec lt s z (fun i a => (X (i, a) : MvPolynomial (ι × Fin (r + K)) O)) L I -
            symWord primal isVec lt
              (fun i a => (X (i, Fin.castAdd K a) : MvPolynomial (ι × Fin (r + K)) O) ^ levP p s z i)
              (fun i b => (X (i, Fin.natAdd r b) : MvPolynomial (ι × Fin (r + K)) O) ^ levP p s z i) L I) ∧
      (¬ Nominal primal I →
        symWord primal isVec lt
            (fun i a => (X (i, Fin.castAdd K a) : MvPolynomial (ι × Fin (r + K)) O) ^ levP p s z i)
            (fun i b => (X (i, Fin.natAdd r b) : MvPolynomial (ι × Fin (r + K)) O) ^ levP p s z i) L I = 0)

def LiftedProductCongr : Prop :=
  ∀ (ι W O : Type) [CommRing W] [CommRing O] [Algebra W O] (p r K : ℕ) (isVec : ι → Bool)
    (s : ι → ℤ) (z : ℤ) (w : O) (σ : RingAut W) (h : (Matrix (Fin (r + K)) (Fin (r + K)) W)ˣ)
    (γ : Type) (cols : Finset γ) (primal : γ → Bool) (lt : γ → ℕ → ι) (L : γ → ℕ)
    (I : γ → Finset (Fin (r + K))),
    p.Prime → 1 ≤ r → 1 ≤ K → w ^ 2 = (p : O) → FrobLift p σ →
    (∀ c ∈ cols, ColValid r K (primal c) isVec (lt c) (L c)) →
    (∀ c ∈ cols, PosHyp r (primal c) isVec (lt c) s z (L c)) →
    (C w) ^ (∑ c ∈ cols, nomOrdC p r (primal c) isVec (lt c) s z (L c)) ∣
      ∏ c ∈ cols, liftCol p (primal c) isVec (lt c) s z (frameRow r K isVec w σ s h) (L c) (I c) ∧
    (C w) ^ ((∑ c ∈ cols, nomOrdC p r (primal c) isVec (lt c) s z (L c)) + 1) ∣
      ∏ c ∈ cols, liftCol p (primal c) isVec (lt c) s z (planeRow r K isVec w) (L c) (I c) -
        (C w) ^ (∑ c ∈ cols, nomOrdC p r (primal c) isVec (lt c) s z (L c)) *
          ∏ c ∈ cols, symWord (primal c) isVec (lt c)
            (fun i a => (X (i, Fin.castAdd K a) : MvPolynomial (ι × Fin (r + K)) O) ^ levP p s z i)
            (fun i b => (X (i, Fin.natAdd r b) : MvPolynomial (ι × Fin (r + K)) O) ^ levP p s z i) (L c) (I c)

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

