import Mathlib

-- bundled from Formalism.SubspaceCounting.Statement
section
noncomputable section

open scoped BigOperators

namespace Formalism.G0

def AllButLE {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (π : R)
    (M P : Submodule R X) (g E : ℕ) : Prop :=
  ∃ C : Finset X, (↑C : Set X) ⊆ M ∧ C.card ≤ g ∧
    ∀ x ∈ M, π ^ E • x ∈ P ⊔ Submodule.span R (↑C : Set X)

def GoodRank {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] (π : R) (f : A →ₗ[R] B) (n D : ℕ) : Prop :=
  ∃ (u : (Fin n → R) →ₗ[R] A) (v : B →ₗ[R] (Fin n → R)),
    v ∘ₗ f ∘ₗ u = (π ^ D) • LinearMap.id

inductive Slot
  | base
  | ball
  | dual
  deriving DecidableEq

def vertexLabel {V : ℕ} (B : Finset (Fin V)) : Fin V → Slot :=
  fun v => if v ∈ B then Slot.dual else Slot.base

def monoOp {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ} (π : R)
    (y : Fin V → Module.End R X) (m : ℕ) (S : Fin V → ℕ) (e : Fin V → Bool) :
    Module.End R X :=
  ((List.finRange V).map fun v => if e v then y v ^ m else (π ^ S v) • (1 : Module.End R X)).prod

def prodIdealMap {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ} (π : R)
    (y : Fin V → Module.End R X) (m : ℕ) (S : Fin V → ℕ) (M : Submodule R X) :
    Submodule R X :=
  ⨆ e : Fin V → Bool, M.map (monoOp π y m S e)

def WalkSharp : Prop :=
  ∀ {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (V : ℕ) (π : R)
    (L : (Fin V → Slot) → Submodule R X) (y : Fin V → Module.End R X)
    (m β c₀ S : ℕ) (a b c Sv : Fin V → ℕ) (g : Finset (Fin V) → ℕ)
    (G : Finset (Fin V) → Finset X),
    1 ≤ m →
    (∀ v w, Commute (y v) (y w)) →
    (∀ σ v, L (Function.update σ v Slot.base) ≤ L (Function.update σ v Slot.ball)) →
    (∀ σ v, L (Function.update σ v Slot.dual) ≤ L (Function.update σ v Slot.base)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      π ^ a v • x ∈ L (Function.update σ v Slot.base)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.base),
      π ^ b v • x ∈ L (Function.update σ v Slot.dual)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      π ^ c v • x ∈ L (Function.update σ v Slot.dual)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      y v x ∈ L (Function.update σ v Slot.dual)) →
    (∀ B : Finset (Fin V), B.card = β + 1 →
      (↑(G B) : Set X) ⊆ L (vertexLabel B) ∧ (G B).card ≤ g B ∧
      ∀ x ∈ L (vertexLabel B), π ^ c₀ • x ∈
        (⨆ v ∈ B, (L (Function.update (vertexLabel B) v Slot.ball)).map (y v)) ⊔
          Submodule.span R (↑(G B) : Set X)) →
    (∀ v, Sv v ≤ S) →
    AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base))
        (∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1), m ^ (β + 1) * g B)
        (∑ v, (a v + b v + (m - 1) * c v + m * c₀) + β * S) ∧
      AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base)) 0
        (∑ v, Sv v)

def LengthLayers : Prop :=
  ∀ {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
    (π : O), Irreducible π →
    ∀ (P : Submodule O M) (τ S Stop β₀ : ℕ) (g : ℕ → ℕ),
    (∀ β ≤ β₀, AllButLE π ⊤ P (g β) (τ + β * S)) →
    AllButLE π ⊤ P 0 (τ + Stop) →
    Module.length O (M ⧸ (P ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule O M))) ≤
      ((Module.finrank O M * τ + S * ∑ β ∈ Finset.range β₀, g β + Stop * g β₀ : ℕ) : ℕ∞)

def SaturatedMember : Prop :=
  ∀ {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    (π : O), π ≠ 0 →
    ∀ (M' P : Submodule O M) (τ : ℕ),
    (∀ (r : O) (x : M), r ≠ 0 → r • x ∈ M' → x ∈ M') →
    P ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule O M) ⊓ M' ≤ (Ideal.span {π ^ τ}) • M' ∧
    Module.length O (M' ⧸ (Submodule.comap M'.subtype
        (P ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule O M)))) ≤
      Module.length O (M ⧸ (P ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule O M)))

end Formalism.G0
end
end

-- bundled from Formalism.SubspaceCounting.StatementB
section
noncomputable section

open scoped BigOperators

namespace Formalism.G0

def window (n i L : ℕ) : Finset ℕ :=
  (Finset.range L).image fun j => (i + j) % n

def CondA (n : ℕ) (T : Finset ℕ) (L₂ K : ℕ) : Prop :=
  ∀ i < n, (T ∩ window n i L₂).card ≤ K

def GoodRun (n : ℕ) (T : Finset ℕ) (L₂ R i e : ℕ) : Prop :=
  ∃ u : Fin R → ℕ, StrictMono u ∧ (∀ l, u l ≤ e) ∧
    (∀ l, (i + u l) % n ∈ T) ∧ (∀ l, Even ((i + u l) % n)) ∧
    (∀ (l : Fin R) (h : l.val + 1 < R),
      L₂ < 2 * (u ⟨l.val + 1, h⟩ - u l) ∧
      ∀ d, u l < d → d < u ⟨l.val + 1, h⟩ → (i + d) % n ∉ T)

def CondB (n : ℕ) (T : Finset ℕ) (L₂ r N₁ : ℕ) : Prop :=
  ∀ i e : ℕ, i < n → e < n →
    N₁ ≤ ((Finset.range (e + 1)).filter fun d => (i + d) % n ∈ T).card →
    GoodRun n T L₂ (3 * r) i e

def CondC (n : ℕ) (T : Finset ℕ) (G : ℕ) : Prop :=
  ∀ i ∈ T, ∃ d : ℕ, 1 ≤ d ∧ d ≤ G ∧ (i + d) % n ∈ T

def GoodOrbit (n : ℕ) (T : Finset ℕ) (L₂ K r N₁ G : ℕ) : Prop :=
  CondA n T L₂ K ∧ CondB n T L₂ r N₁ ∧ CondC n T G ∧ N₁ ≤ T.card

def probNotGood (n : ℕ) (δ : ℝ) (L₂ K r N₁ G : ℕ) : ℝ := by
  classical
  exact ∑ T ∈ (Finset.range n).powerset,
    if 0 ∈ T ∧ ¬ GoodOrbit n T L₂ K r N₁ G then
      δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) else 0

def binLower (n : ℕ) (δ : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, (n.choose j : ℝ) * δ ^ j * (1 - δ) ^ (n - j)

def ChoiceOfTops : Prop :=
  ∀ (n : ℕ) (δ : ℝ) (L₂ K r N₁ G : ℕ), 2 ≤ n → Even n → 0 ≤ δ → 1 ≤ L₂ →
    (L₂ : ℝ) * δ ≤ 1 → 1 ≤ r → 3 * r ≤ N₁ →
    probNotGood n δ L₂ K r N₁ G ≤
      n * (L₂.choose K : ℝ) * δ ^ K +
      n * (1 - (1 / 2 : ℝ) ^ (3 * r) * (1 - L₂ * δ) ^ (3 * r)) ^ (N₁ / (3 * r) - 1) +
      n * (1 - δ) ^ G + binLower n δ N₁

def fTail (k' y : ℕ) : ℝ := Real.log ((y + k').choose k')

def tailSum {N : ℕ} (x : Fin N → ℕ) (u : ℕ) : ℕ :=
  ∑ l : Fin N, if u ≤ l.val then x l else 0

def TailConcavity : Prop :=
  ∀ (N k' X u₀ : ℕ) (α B : Fin N → ℕ) (hu : u₀ < N),
    (∀ l, k' ≤ B l) →
    (∀ (l : Fin N) (h : l.val + 1 < N), 4 * B ⟨l.val + 1, h⟩ ≤ B l) →
    (∀ u, tailSum α u ≤ tailSum B u) →
    tailSum α u₀ + X ≤ tailSum B u₀ →
    ∑ l, fTail k' (α l) ≤ ∑ l, fTail k' (B l) - (X : ℝ) * k' / (4 * B ⟨u₀, hu⟩)

def gaussBinom (q : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1)

def countAbove {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]
    (A : Submodule F W) (j : ℕ) : ℕ :=
  Nat.card {U : Submodule F W // A ≤ U ∧ Module.finrank F U = j}

def countBelow {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]
    (A : Submodule F W) (j : ℕ) : ℕ :=
  Nat.card {U : Submodule F W // U ≤ A ∧ Module.finrank F U = j}

def SubspaceCount : Prop :=
  ∀ {F W : Type} [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Finite W] (k : ℕ),
    countBelow (⊤ : Submodule F W) k = gaussBinom (Fintype.card F) (Module.finrank F W) k

def QVandermonde : Prop :=
  ∀ q m g n : ℕ,
    gaussBinom q (m + g) n =
      ∑ l ∈ Finset.range (n + 1), q ^ (l * (m + l - n)) * gaussBinom q m (n - l) * gaussBinom q g l ∧
    gaussBinom q (m + g) n =
      ∑ l ∈ Finset.range (n + 1), q ^ ((n - l) * (g - l)) * gaussBinom q m (n - l) * gaussBinom q g l

def TypeIIUp : Prop :=
  ∀ {F P Q : Type} [Field F] [Fintype F] [AddCommGroup P] [Module F P] [Finite P]
    [AddCommGroup Q] [Module F Q] [Finite Q] (f : P →ₗ[F] Q) (N g j : ℕ),
    Module.finrank F P = N → Module.finrank F Q = N + g →
    (countAbove (LinearMap.range f) j : ℤ) =
      ∑ l ∈ Finset.range (j + 1),
        (Fintype.card F : ℤ) ^ (l * (N + l - j)) * gaussBinom (Fintype.card F) g l *
          Nat.card {U : Submodule F P // U ≤ LinearMap.ker f ∧
            Module.finrank F U + (j - l) = N}

def TypeIIDown : Prop :=
  ∀ {F P Q : Type} [Field F] [Fintype F] [AddCommGroup P] [Module F P] [Finite P]
    [AddCommGroup Q] [Module F Q] [Finite Q] (f : P →ₗ[F] Q) (N g j : ℕ),
    Module.finrank F P = N → Module.finrank F Q = N + g →
    (Nat.card {U : Submodule F Q // LinearMap.range f ≤ U ∧ Module.finrank F U + j = N + g} : ℤ) =
      ∑ l ∈ Finset.range (j + 1),
        (Fintype.card F : ℤ) ^ ((j - l) * (g - l)) * gaussBinom (Fintype.card F) g l *
          countBelow (LinearMap.ker f) (j - l)

end Formalism.G0
end
end

-- bundled from Formalism.SubspaceCounting.StatementW
section
noncomputable section

open scoped BigOperators

namespace Formalism.G0

open Polynomial in

def msMat {L : Type} [Field L] {r : ℕ} (g : GL (Fin r) L) : Matrix (Fin r) (Fin r) L[X] :=
  (g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then X else 1) *
    ((g⁻¹ : GL (Fin r) L).1.map C)

open Polynomial in

def msDualMat {L : Type} [Field L] {r : ℕ} (g : GL (Fin r) L) : Matrix (Fin r) (Fin r) L[X] :=
  ((g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) *
    ((g⁻¹ : GL (Fin r) L).1.map C)).transpose

def substS {K L ι : Type} [Field K] [Field L] [Algebra K L] [DecidableEq ι] {r : ℕ}
    (vec : ι → Bool) (S : Finset ι) (g : GL (Fin r) L) :
    MvPolynomial (ι × Fin r) K →ₐ[K] MvPolynomial (ι × Fin r) (Polynomial L) :=
  MvPolynomial.aeval fun p =>
    if p.1 ∈ S then
      (if vec p.1 then ∑ b, MvPolynomial.C ((msMat g) p.2 b) * MvPolynomial.X (p.1, b)
       else ∑ b, MvPolynomial.C ((msDualMat g) p.2 b) * MvPolynomial.X (p.1, b))
    else MvPolynomial.X p

def ValGE {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ} (vec : ι → Bool) (S : Finset ι) (d : ι → ℕ)
    (F : MvPolynomial (ι × Fin r) K) (th : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [Algebra K L] (g : GL (Fin r) L),
    MvPolynomial.C (Polynomial.X ^ (th + ∑ i ∈ S.filter (fun i => vec i = false), d i)) ∣
      substS (K := K) vec S g F

def MultiHom {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ} (F : MvPolynomial (ι × Fin r) K) (d : ι → ℕ) :
    Prop :=
  ∀ i, MvPolynomial.IsWeightedHomogeneous (fun p : ι × Fin r => if p.1 = i then 1 else 0) F (d i)

def detLetters {K ι : Type} [Field K] {r : ℕ} (A : Fin r → ι) : MvPolynomial (ι × Fin r) K :=
  Matrix.det (Matrix.of fun (l a : Fin r) => MvPolynomial.X (A l, a))

def DetDivides : Prop :=
  ∀ {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (r : ℕ) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (d : ι → ℕ) (G : MvPolynomial (ι × Fin r) K) (th : ℕ),
    Function.Injective A → (∀ l, A l ∈ S ∧ vec (A l) = true) → MultiHom G d →
    ValGE vec S d G th →
    (∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) < th →
    (detLetters (K := K) A) ^ (th - ∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) ∣ G

def DetVal : Prop :=
  ∀ {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (r : ℕ) (vec : ι → Bool)
    (S' : Finset ι) (A : Fin r → ι), 1 ≤ r → Function.Injective A →
    (∀ l, vec (A l) = true) →
    let dD : ι → ℕ := fun i => if i ∈ Set.range A then 1 else 0
    ((∀ l, A l ∈ S') → ValGE vec S' dD (detLetters (K := K) A) 1 ∧
        ¬ ValGE vec S' dD (detLetters (K := K) A) 2) ∧
      ((¬ ∀ l, A l ∈ S') → ¬ ValGE vec S' dD (detLetters (K := K) A) 1)

def CramerCofactor : Prop :=
  ∀ {R : Type} [CommRing R] (r : ℕ) (T : Matrix (Fin r) (Fin r) R) (σ : Fin r → R) (a : Fin r),
    σ a * T.det = ∑ l, (∑ b, T l b * σ b) * T.adjugate a l

end Formalism.G0
end
end

