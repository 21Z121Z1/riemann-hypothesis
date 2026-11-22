import Mathlib

-- bundled from Formalism.CyclotomicNorms.DiscardKernel
section
open Finset

noncomputable section

namespace Formalism.CyclotomicNorms

open scoped ComplexOrder

def SubstitutionAdaptive : Prop :=
  ∀ (k : Type) [CommRing k] (ℓ r s : ℕ) (F : Fin s → MvPowerSeries (Fin r) k) (B : List ℕ → ℕ),
    2 ≤ ℓ → (∀ i, F i ≠ 0) →
    ∃ e : Fin r → ℕ, StrictMono e ∧
      (∀ j : Fin r, B (List.ofFn fun i : Fin (j : ℕ) => e (Fin.castLE (Nat.le_of_lt j.isLt) i)) ≤ e j) ∧
      ∀ i, (MvPowerSeries.subst (fun j => (PowerSeries.X : PowerSeries k) ^ (ℓ ^ e j)) (F i) :
        PowerSeries k) ≠ 0

def LowPowerSeries : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (n m₀ : ℕ)
    (D g : PowerSeries O),
    Irreducible ϖ →
    (PowerSeries.map (IsLocalRing.residue O) D).order ≤ (m₀ : ℕ∞) →
    PowerSeries.constantCoeff g ∉ Ideal.span {ϖ ^ n} →
    D * g ∉ Ideal.span {PowerSeries.C (ϖ ^ n), (PowerSeries.X : PowerSeries O) ^ (n * m₀ + 1)}

def PermFixedSet : Prop :=
  ∀ N a : ℕ, 0 < a → a < N →
    8 * (univ.filter (fun σ : Equiv.Perm (Fin N) =>
      ∃ S : Finset (Fin N), S.card = a ∧ S.map σ.toEmbedding = S)).card ≤ 7 * N.factorial

def DiscardRatio : Prop :=
  ∀ (n : ℕ) (Q Pi : Matrix (Fin n) (Fin n) ℂ) (δ Dstar η s : ℝ),
    Q.PosSemidef → Pi.IsHermitian → Pi * Pi = Pi → 0 ≤ δ → 2 * δ < 1 → 0 < Dstar →
    (Pi.rank : ℝ) ≤ δ * Dstar → 0 ≤ s → (n : ℝ) ≤ (1 + s) * Dstar → 0 ≤ η → η ≤ 1 →
    (Q * Q).trace.re ≤ (1 + η) * (Q.trace.re) ^ 2 / Dstar →
    (((1 - Pi) * Q * (1 - Pi)) * ((1 - Pi) * Q * (1 - Pi))).trace.re *
        ((n : ℝ) - Pi.rank) * (1 - Real.sqrt (2 * δ)) ^ 2 ≤
      (1 + η) * (1 + s) * (((1 - Pi) * Q * (1 - Pi)).trace.re) ^ 2

def DiscardRatioDstar : Prop :=
  ∀ (n : ℕ) (Q Pi : Matrix (Fin n) (Fin n) ℂ) (δ Dstar η : ℝ),
    Q.PosSemidef → Pi.IsHermitian → Pi * Pi = Pi → 0 ≤ δ → 2 * δ < 1 → 0 < Dstar →
    (Pi.rank : ℝ) ≤ δ * Dstar → 0 ≤ η → η ≤ 1 →
    (Q * Q).trace.re ≤ (1 + η) * (Q.trace.re) ^ 2 / Dstar →
    (((1 - Pi) * Q * (1 - Pi)) * ((1 - Pi) * Q * (1 - Pi))).trace.re *
        Dstar * (1 - Real.sqrt (2 * δ)) ^ 2 ≤
      (1 + η) * (((1 - Pi) * Q * (1 - Pi)).trace.re) ^ 2

def DiscardKernel : Prop :=
  ∀ (m n : ℕ) (B : Matrix (Fin m) (Fin n) ℂ) (Pi : Matrix (Fin m) (Fin m) ℂ) (c : ℝ),
    Pi.IsHermitian → Pi * Pi = Pi → 0 ≤ c →
    ((c : ℂ) • (B.conjTranspose * B) - (c : ℂ) • (B.conjTranspose * (1 - Pi) * B)).PosSemidef

end Formalism.CyclotomicNorms
end
end

-- bundled from Formalism.CyclotomicNorms.StatementA
section
open Finset Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

abbrev wt (x : ℝ) : WithTop ℝ := (x : WithTop ℝ)

def Newton : Prop :=
  ∀ (L : Type) [Field L] (v : AddValuation L (WithTop ℝ)) (ℓ e : ℕ) (f : L[X]) (c : ℝ),
    ℓ.Prime → 0 < e → v (ℓ : L) = wt 1 →
    (∀ i, v (f.coeff i) = ⊤ ∨ ∃ n : ℕ, v (f.coeff i) = wt ((n : ℝ) / e)) →
    v (f.coeff 0) = wt c →
    ∃ X : Finset ℕ, (X.card : ℝ) ≤ e * c ∧
      ∀ j : ℕ, 1 ≤ j → j ∉ X → ∀ z : L, IsPrimitiveRoot z (ℓ ^ j) →
        v (f.eval (z - 1)) ≤ wt c

def GTPigeonhole : Prop :=
  ∀ (a : ℕ → ℝ) (V ε K₁ : ℝ) (X B : Finset ℕ) (k₀ N : ℕ),
    0 < ε → 1 ≤ k₀ → (∀ k, 0 ≤ a k) → B.card ≤ N → (∀ S : Finset ℕ, ∑ k ∈ S, a k ≤ V) →
    K₁ = (k₀ + X.card + N + 1) * Real.exp (2 * V / ε) + 1 →
    ∃ k : ℕ, k₀ ≤ k ∧ (k : ℝ) ≤ K₁ ∧ k ∉ X ∧ k ∉ B ∧ (k : ℝ) * a k ≤ ε / 2

def Substitution : Prop :=
  ∀ (k : Type) [CommRing k] (ℓ r s E : ℕ) (F : Fin s → MvPowerSeries (Fin r) k),
    2 ≤ ℓ → (∀ i, F i ≠ 0) →
    ∃ e : Fin r → ℕ, StrictMono e ∧ (∀ j, E ≤ e j) ∧
      ∀ i, (MvPowerSeries.subst (fun j => (PowerSeries.X : PowerSeries k) ^ (ℓ ^ e j)) (F i) :
        PowerSeries k) ≠ 0

def Evaluation : Prop :=
  ∀ (L : Type) [Field L] (v : AddValuation L (WithTop ℝ)) (ℓ e w j : ℕ) (F : L[X]) (z : L),
    ℓ.Prime → 0 < e → v (ℓ : L) = wt 1 →
    (∀ i, v (F.coeff i) = wt 0 ∨ wt (1 / e) ≤ v (F.coeff i)) →
    (∃ i ≤ w, v (F.coeff i) = wt 0) →
    IsPrimitiveRoot z (ℓ ^ j) → ((e * w : ℕ) : ℝ) < ((ℓ ^ j).totient : ℝ) →
    v (F.eval (z - 1)) ≤ wt ((w : ℝ) / ((ℓ ^ j).totient : ℝ))

abbrev TruncRing (O : Type) [CommRing O] (π : O) (n M : ℕ) : Type :=
  (O ⧸ Ideal.span {π ^ n})[X] ⧸ Ideal.span {(X : (O ⧸ Ideal.span {π ^ n})[X]) ^ (M + 1)}

abbrev truncMk (O : Type) [CommRing O] (π : O) (n M : ℕ) :
    (O ⧸ Ideal.span {π ^ n})[X] →+* TruncRing O π n M :=
  Ideal.Quotient.mk _

def Product : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (π : O) (n m m₀ M : ℕ),
    Irreducible π → 1 ≤ n → m ≤ m₀ → n * m₀ ≤ M →
    ∀ (U : (TruncRing O π n M)ˣ) (D' : TruncRing O π n M) (g : (O ⧸ Ideal.span {π ^ n})[X]),
      g.coeff 0 ≠ 0 →
      (truncMk O π n M (X ^ m) * (U : TruncRing O π n M) +
          truncMk O π n M (C (Ideal.Quotient.mk _ π)) * D') * truncMk O π n M g ≠ 0

def genericGram {k La La' : Type} [Field k] [AddCommGroup La] [Module k La] [AddCommGroup La']
    [Module k La'] {R d : ℕ} (B : Fin R → La →ₗ[k] La' →ₗ[k] k) {S : Submodule k La}
    {S' : Submodule k La'} (b : Module.Basis (Fin d) k S) (b' : Module.Basis (Fin d) k S') :
    Matrix (Fin d) (Fin d) (MvPolynomial (Fin R) k) :=
  Matrix.of fun p q => ∑ i, MvPolynomial.X i * MvPolynomial.C (B i (b p) (b' q))

def GenericPairing : Prop :=
  ∀ (k La La' : Type) [Field k] [AddCommGroup La] [Module k La] [FiniteDimensional k La]
    [AddCommGroup La'] [Module k La'] [FiniteDimensional k La'] (R d : ℕ)
    (B : Fin R → La →ₗ[k] La' →ₗ[k] k), Submodule.span k (Set.range B) = ⊤ →
    ∀ (S : Submodule k La) (S' : Submodule k La') (b : Module.Basis (Fin d) k S)
      (b' : Module.Basis (Fin d) k S'),
      ((genericGram B b b').map
        (algebraMap (MvPolynomial (Fin R) k) (FractionRing (MvPolynomial (Fin R) k)))).det ≠ 0

def GenericAltRank : Prop :=
  ∀ (k La : Type) [Field k] [AddCommGroup La] [Module k La] [FiniteDimensional k La] (R d : ℕ)
    (B : Fin R → La →ₗ[k] La →ₗ[k] k), (∀ i x, B i x x = 0) →
    (∀ ω : La →ₗ[k] La →ₗ[k] k, (∀ x, ω x x = 0) → ω ∈ Submodule.span k (Set.range B)) →
    ∀ (S S' : Submodule k La) (b : Module.Basis (Fin d) k S) (b' : Module.Basis (Fin d) k S'),
      d - 1 ≤ ((genericGram B b b').map
        (algebraMap (MvPolynomial (Fin R) k) (FractionRing (MvPolynomial (Fin R) k)))).rank

def evalAt (k : Type) {M W : Type} [CommRing k] [AddMonoid M] [AddCommGroup W] [Module k W]
    (x : M) : (M →+ W) →ₗ[k] W where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def evalImage {k G : Type} [Field k] [Group G] {a : ℕ} {W : Fin a → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] {H : Subgroup G}
    (La : ∀ i, Submodule k (Additive H →+ W i)) (h : H) : ∀ i, La i →ₗ[k] W i :=
  fun i => (evalAt k (Additive.ofMul h)).comp (La i).subtype

def SpanHyp {k G : Type} [Field k] [Group G] {a : ℕ} {W : Fin a → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] (ρ : ∀ i, Representation k G (W i))
    (H : Subgroup G) (La : ∀ i, Submodule k (Additive H →+ W i)) : Prop :=
  H.Normal ∧
  (∀ i, FiniteDimensional k (W i) ∧ Nontrivial (W i) ∧
    Submodule.span k (Set.range (ρ i)) = ⊤) ∧
  (∀ i j, i ≠ j → ¬ ∃ T : W i ≃ₗ[k] W j, ∀ g x, T (ρ i g x) = ρ j g (T x)) ∧
  (∀ i, FiniteDimensional k (La i)) ∧
  (∀ i, ∀ lam ∈ La i, ∀ (g : G) (h : H) (hh : g * (h : G) * g⁻¹ ∈ H),
    lam (Additive.ofMul ⟨g * h * g⁻¹, hh⟩) = ρ i g (lam (Additive.ofMul h)))

def SpanImage : Prop :=
  ∀ (G k : Type) [Group G] [Field k] (a : ℕ) (W : Fin a → Type) [∀ i, AddCommGroup (W i)]
    [∀ i, Module k (W i)] (ρ : ∀ i, Representation k G (W i)) (H : Subgroup G)
    (La : ∀ i, Submodule k (Additive H →+ W i)), SpanHyp ρ H La →
    Submodule.span k (Set.range (evalImage La)) = ⊤

def SpanQuad : Prop :=
  ∀ (G k : Type) [Group G] [Field k] (a : ℕ) (W : Fin a → Type) [∀ i, AddCommGroup (W i)]
    [∀ i, Module k (W i)] (ρ : ∀ i, Representation k G (W i)) (H : Subgroup G)
    (La : ∀ i, Submodule k (Additive H →+ W i)) (BB : Type) [AddCommGroup BB] [Module k BB]
    (q : (∀ i, La i →ₗ[k] W i) → BB)
    (b : (∀ i, La i →ₗ[k] W i) →ₗ[k] (∀ i, La i →ₗ[k] W i) →ₗ[k] BB), SpanHyp ρ H La →
    (∀ h h' : H, q (evalImage La (h * h')) - q (evalImage La h) - q (evalImage La h') =
      b (evalImage La h) (evalImage La h')) →
    ∀ x y, b x y ∈ Submodule.span k (Set.range fun h : H => q (evalImage La h))

def coboundary {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W]
    (ρ : Representation R G W) (n : ℕ) (f : (Fin n → G) → W) : (Fin (n + 1) → G) → W :=
  fun g => ρ (g 0) (f fun i => g i.succ) +
    ∑ j : Fin (n + 1), (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)

def CentralScalar : Prop :=
  ∀ (G R W : Type) [Group G] [TopologicalSpace G] [CommRing R] [AddCommGroup W] [Module R W]
    [TopologicalSpace W] [DiscreteTopology W] (ρ : Representation R G W) (z : G) (c : R),
    z ∈ Subgroup.center G → IsUnit (c - 1) → (∀ w, ρ z w = c • w) →
    (∀ w : W, (∀ g, ρ g w = w) → w = 0) ∧
    ∀ (n : ℕ) (f : (Fin (n + 1) → G) → W), Continuous f → coboundary ρ (n + 1) f = 0 →
      ∃ h : (Fin n → G) → W, Continuous h ∧ coboundary ρ n h = f

def Cycles : Prop :=
  ∀ (G k V P : Type) [Group G] [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [Fintype P] (ρ : Representation k G V) (N : ℕ) (D I : P → Subgroup G)
    (χ : P → Fin N → G → k) (flag : P → Fin (N + 1) → Submodule k V),
    Module.finrank k V = N →
    (∀ v, I v ≤ D v) → (∀ v, ∀ d ∈ D v, ∀ x ∈ I v, d * x * d⁻¹ ∈ I v) →

    (∀ v (i : Fin (N + 1)), Module.finrank k (flag v i) = i) →
    (∀ v (i : Fin N), flag v i.castSucc ≤ flag v i.succ) →
    (∀ v i, ∀ x ∈ flag v i, ∀ y ∈ I v, ρ y x ∈ flag v i) →

    (∀ v (i : Fin N), ∀ x ∈ flag v i.succ, ∀ y ∈ I v,
      ρ y x - χ v i y • x ∈ flag v i.castSucc) →

    (∀ v (i j : Fin N), i ≠ j → ∃ y ∈ I v, χ v i y ≠ χ v j y) →
    (∀ v (i : Fin N), ∀ d ∈ D v, ∃ j : Fin N, ∀ y ∈ I v, χ v j y = χ v i (d⁻¹ * y * d)) →

    (∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ ∃ S : Finset (Fin N), S.card = a ∧
      ∀ i ∈ S, ∀ d ∈ D v, ∃ j ∈ S, ∀ y ∈ I v, χ v j y = χ v i (d⁻¹ * y * d)) →
    ∀ W : Submodule k V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤

def CentralTwoStep : Prop :=
  ∀ (H G : Type) [Group H] [CommGroup G] [Finite G] (π : H →* G), Function.Surjective π →
    IsPGroup 2 G → Nat.card π.ker = 2 → π.ker ≤ Subgroup.center H →
    ∀ D : Subgroup H, D.map π = ⊤ →
    (Function.Injective (π.comp D.subtype) ∨ (D = ⊤ ∧ ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)) →
    ∀ x y : H, x * y = y * x

def ElemAbelianRank : Prop :=
  ∀ (P : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [T2Space P]
    (X : Subgroup P) (a b c d : P),
    X = (commutator P).topologicalClosure →
    (Subgroup.closure ({a, b, c, d} : Set P)).topologicalClosure = ⊤ → a * b = b * a →
    X ≤ Subgroup.center P → (∀ x ∈ X, x ^ 2 = 1) →
    Finite X ∧ Nat.card X ≤ 2 ^ 5

def LengthBound : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Type) [CommRing R] [Algebra ℤ_[ℓ] R] [Module.Free ℤ_[ℓ] R]
    [Module.Finite ℤ_[ℓ] R] (y : R) (g : ℕ) (Y : Type) [AddCommGroup Y] [Module ℤ_[ℓ] Y],
    LinearMap.det (LinearMap.mulLeft ℤ_[ℓ] y) ≠ 0 →
    ∀ q : (Fin g → R ⧸ Ideal.span {y}) →ₗ[ℤ_[ℓ]] Y, Function.Surjective q →
      Module.length ℤ_[ℓ] Y ≤
        ((g * (LinearMap.det (LinearMap.mulLeft ℤ_[ℓ] y)).valuation : ℕ) : ℕ∞)

end Formalism.CyclotomicNorms
end
end

-- bundled from Formalism.CyclotomicNorms.StatementI
section
open Finset Polynomial
open scoped ComplexOrder

noncomputable section

namespace Formalism.CyclotomicNorms

def Exc (g d ℓ : ℕ) : Prop := ℓ.Prime ∧ g ^ d < ℓ ^ (4 * padicValNat ℓ (g ^ d - 1))

def BB (N g : ℕ) : Set ℕ := {g} ∪ {ℓ | ∃ d, 1 ≤ d ∧ d ≤ N ∧ Exc g d ℓ}

def BBCount : Prop :=
  ∀ g : ℕ, 2 ≤ g →
    (∀ d : ℕ, 1 ≤ d → Set.Finite {ℓ | Exc g d ℓ} ∧ Set.ncard {ℓ | Exc g d ℓ} ≤ 3) ∧
    ∀ N : ℕ, Set.Finite (BB N g) ∧ Set.ncard (BB N g) ≤ 3 * N + 1

def RootsOfUnityCount : Prop :=
  ∀ ℓ w d : ℕ, ℓ.Prime → 1 ≤ w → 1 ≤ d →
    (ℓ ≠ 2 → Nat.card {x : ZMod (ℓ ^ w) // x ^ d = 1} ≤ d * ℓ ^ padicValNat ℓ d) ∧
    Nat.card {x : ZMod (ℓ ^ w) // x ^ d = 1} ≤ 2 * d

def ChoiceCount : Prop :=
  ∀ (Y : ℝ) (N g₁ : ℕ), 2 ≤ Y → 1 ≤ N → Y ≤ g₁ → (g₁ : ℝ) ≤ 2 * Y →
    ∀ S : Finset ℕ, (∀ g ∈ S, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y ∧ (BB N g ∩ BB N g₁).Nonempty) →
      (S.card : ℝ) ≤ (3 * N + 1) * (1 + 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1))

def BlocksCycle : Prop :=
  ∀ (G Ω : Type) [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω] (B : Finset (Finset Ω))
    (m p : ℕ) (g₀ : G),
    (∀ b ∈ B, b.card = m) → (∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → Disjoint b b') → (∀ x, ∃ b ∈ B, x ∈ b) →
    (∀ g : G, ∀ b ∈ B, b.image (fun x => g • x) ∈ B) →
    p.Prime → Fintype.card Ω < 2 * p →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).IsCycle →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).support.card = p →
    B.card = 1 ∨ B.card = Fintype.card Ω

def JordanTransitive : Prop :=
  ∀ (G Ω : Type) [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω] (p : ℕ) (g₀ : G),
    MulAction.IsPretransitive G Ω → p.Prime → Fintype.card Ω < 2 * p →
    p + 3 ≤ Fintype.card Ω →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).IsCycle →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).support.card = p →
    alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range ∧ ¬ Group.IsSolvable G

def Restriction : Prop :=
  ∀ (G k V : Type) [Group G] [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (N : ℕ) (H : Subgroup G) [H.Normal] (I : Subgroup G) (e : Module.Basis (Fin N) k V)
    (χ : Fin N → G → k) (φ : G) (π : Equiv.Perm (Fin N)) (p : ℕ),
    8 ≤ N → Finite (G ⧸ H) → Group.IsSolvable (G ⧸ H) → I ≤ H →
    (∀ W : Submodule k V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∀ i, ∀ y ∈ I, ρ y (e i) = χ i y • e i) →
    (∀ i j, i ≠ j → ∃ y ∈ I, χ i y ≠ χ j y) →
    (∀ y, y ∈ I ↔ φ * y * φ⁻¹ ∈ I) →
    (∀ i, ∀ y ∈ I, χ (π i) y = χ i (φ⁻¹ * y * φ)) →
    p.Prime → Fintype.card (Fin N) < 2 * p → p + 3 ≤ N → p ∈ π.cycleType →
    ∀ W : Submodule k V, (∀ h ∈ H, ∀ x ∈ W, ρ h x ∈ W) → W = ⊥ ∨ W = ⊤

def IdemHyp {O K A : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup A] [Module K A] [Module O A] [IsScalarTower O K A] (e : A →ₗ[K] A) (c : O)
    (M : Submodule O A) : Prop :=
  e ∘ₗ e = e ∧ c ≠ 0 ∧ ∀ x ∈ M, c • e x ∈ M

def IdempotentLattice : Prop :=
  ∀ (O K A : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup A] [Module K A] [Module O A] [IsScalarTower O K A] (e : A →ₗ[K] A) (c : O)
    (M : Submodule O A), IdemHyp e c M →
    (∀ x ∈ M, c • e x ∈ M ∧ c • e x ∈ LinearMap.range e) ∧
    (∀ y ∈ M, y ∈ LinearMap.range e → ∃ x ∈ M, e x = y) ∧
    (∀ x ∈ M, ∃ u ∈ M, ∃ w ∈ M, u ∈ LinearMap.range e ∧
      w ∈ LinearMap.range (LinearMap.id - e) ∧ c • x = u + w)

def IdempotentDrop : Prop :=
  ∀ (O K A : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup A] [Module K A] [Module O A] [IsScalarTower O K A] (e f Z : A →ₗ[K] A) (c : O)
    (M : Submodule O A), IdemHyp e c M →
    f ∘ₗ e = e ∘ₗ f → (∀ x ∈ M, f x ∈ M) → Z ∘ₗ Z = Z → Z ∘ₗ e = e ∘ₗ Z → Z ∘ₗ f = f ∘ₗ Z →
    (∀ x ∈ M, f (Z x) ∈ M ∧ f (Z x) ∈ LinearMap.range Z) →
    ∀ x ∈ M, c • f (e (Z x)) ∈ M ∧ c • f (e (Z x)) ∈ LinearMap.range (e ∘ₗ Z)

def Discard : Prop :=
  ∀ (n : ℕ) (Q Pi : Matrix (Fin n) (Fin n) ℂ) (δ Dstar η : ℝ),
    Q.PosSemidef → Pi.IsHermitian → Pi * Pi = Pi → 0 ≤ δ → 0 < Dstar →
    (Pi.rank : ℝ) ≤ δ * Dstar → 0 ≤ η → η ≤ 1 →
    (Q * Q).trace.re ≤ (1 + η) * (Q.trace.re) ^ 2 / Dstar →
    (Pi * Q).trace.re ≤ Real.sqrt (2 * δ) * Q.trace.re ∧
    (((1 - Pi) * Q * (1 - Pi)) * ((1 - Pi) * Q * (1 - Pi))).trace.re ≤ (Q * Q).trace.re ∧
    (1 - Real.sqrt (2 * δ)) * Q.trace.re ≤ ((1 - Pi) * Q * (1 - Pi)).trace.re

def monicOf {K : Type} [Field K] {N : ℕ} (a : Fin N → K) : K[X] :=
  X ^ N + ∑ i : Fin N, C (a i) * X ^ (i : ℕ)

open Classical in

def SquarefreeShare : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (N : ℕ),
    ((univ.filter (fun a : Fin N → K => (monicOf a).coeff 0 ≠ 0 ∧ ¬ Squarefree (monicOf a))).card : ℝ)
      * Fintype.card K ≤
      2 * (univ.filter (fun a : Fin N → K => (monicOf a).coeff 0 ≠ 0)).card

end Formalism.CyclotomicNorms
end
end

-- bundled from Formalism.CyclotomicNorms.StatementTW
section
open Finset Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

def vl {L : Type*} [NormedField L] (ℓ : ℕ) (x : L) : ℝ := -Real.logb ℓ ‖x‖

def GTLemma : Prop :=
  ∀ (K L : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
    [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [IsAlgClosed L]
    [Algebra.IsAlgebraic K L]
    (ℓ e J M k₀ : ℕ) (h : Fin J → K[X]) (w : Fin J → ℕ) (vv : Fin J → ℝ) (ε : ℝ)
    (X : Finset ℕ),
    ℓ.Prime → 0 < e → ‖(ℓ : K)‖ = (ℓ : ℝ)⁻¹ →
    (∀ x : K, x ≠ 0 → ∃ n : ℤ, vl ℓ x = n / e) →
    (∀ j i, ‖(h j).coeff i‖ ≤ 1) →
    (∀ j, w j ≤ M ∧ (h j).coeff (w j) ≠ 0 ∧ vl ℓ ((h j).coeff (w j)) ≤ vv j) →
    0 < ε → 1 ≤ k₀ → 2 * (J : ℝ) * M / ε ≤ ((ℓ ^ k₀).totient : ℝ) → (e : ℝ) * ε < k₀ →
    ∃ k : ℕ, k₀ ≤ k ∧
      (k : ℝ) ≤ (k₀ + X.card + J * M + 1) * Real.exp (2 * (∑ j, vv j) / ε) + 1 ∧ k ∉ X ∧
      (∀ ζ ∈ primitiveRoots (ℓ ^ k) L, ∀ j, ((h j).map (algebraMap K L)).eval (ζ - 1) ≠ 0) ∧
      (∑ ζ ∈ primitiveRoots (ℓ ^ k) L, ∑ j, vl ℓ (((h j).map (algebraMap K L)).eval (ζ - 1))) ≤
        ((ℓ ^ k).totient : ℝ) * ((∑ j, vv j) + ε) ∧
      ∃ ζ ∈ primitiveRoots (ℓ ^ k) L, ∃ εj : Fin J → ℝ, (∀ j, 0 ≤ εj j) ∧ ∑ j, εj j ≤ ε ∧
        ∀ j, vl ℓ (((h j).map (algebraMap K L)).eval (ζ - 1)) ≤ vv j + εj j

def lamIdeal (A σ : Type) [CommRing A] (ℓ M : ℕ) : Ideal (MvPolynomial σ A) :=
  Ideal.span (Set.range fun i : σ => (1 + MvPolynomial.X i) ^ (ℓ ^ M) - 1)

def varIdeal (A σ : Type) [CommRing A] : Ideal (MvPolynomial σ A) :=
  Ideal.span (Set.range MvPolynomial.X)

def redLam (O σ : Type) [CommRing O] [IsLocalRing O] (ℓ M : ℕ) :
    MvPolynomial σ O →+*
      MvPolynomial σ (IsLocalRing.ResidueField O) ⧸ lamIdeal (IsLocalRing.ResidueField O) σ ℓ M :=
  (Ideal.Quotient.mk _).comp (MvPolynomial.map (IsLocalRing.residue O))

def FewFactors {O σ : Type} [CommRing O] [IsLocalRing O] (ℓ M m : ℕ) (D : MvPolynomial σ O) :
    Prop :=
  ∃ (n : ℕ) (φ : Fin n →
      MvPolynomial σ (IsLocalRing.ResidueField O) ⧸ lamIdeal (IsLocalRing.ResidueField O) σ ℓ M),
    n ≤ m ∧ redLam O σ ℓ M D = ∏ a, φ a ∧
    ∀ a, IsUnit (φ a) ∨ ∃ (i : σ) (u : MvPolynomial σ (IsLocalRing.ResidueField O) ⧸
        lamIdeal (IsLocalRing.ResidueField O) σ ℓ M),
      IsUnit u ∧ φ a = Ideal.Quotient.mk _ (MvPolynomial.X i) * u

def evTw {L : Type} [Field L] {R' : ℕ} (ℓ : ℕ) (z : L) (e'' e' : Fin R' → ℕ) (a : ℤˣ) :
    Fin R' ⊕ Fin R' → L :=
  Sum.elim (fun i => z ^ ((a : ℤ) * ((ℓ ^ e'' i : ℕ) : ℤ)) - 1)
    (fun i => z ^ ((a : ℤ) * ((ℓ ^ e' i : ℕ) : ℤ)) - 1)

def TWAbs : Prop :=
  ∀ (K L : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
    [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [IsAlgClosed L]
    [Algebra.IsAlgebraic K L]
    (ℓ e e₀ R' D' m₁ t M₀ : ℕ) (O₀ O : Subring K) [IsDiscreteValuationRing O₀]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O₀)] (w₀ : O₀) (w : O)
    (Sig JJ : Type) [Fintype Sig] [Fintype JJ] (vv : JJ → ℝ)
    (F : ℕ → Sig → MvPolynomial (Fin R' ⊕ Fin R') O₀)
    (f : ℕ → JJ → MvPolynomial (Fin R' ⊕ Fin R') O) (D g : ℕ → JJ → MvPolynomial (Fin R') O),
    ℓ.Prime → 0 < e → 0 < e₀ → ‖(ℓ : K)‖ = (ℓ : ℝ)⁻¹ →
    (∀ x : K, x ≠ 0 → ∃ n : ℤ, vl ℓ x = n / e) →
    (∀ x : O₀, ‖(x : K)‖ ≤ 1) → (∀ x : O, ‖(x : K)‖ ≤ 1) →
    Irreducible w₀ → Irreducible w → vl ℓ (w₀ : K) = 1 / e₀ → vl ℓ (w : K) = 1 / e →
    (∀ j, ∃ n : ℕ, vv j = n / e) →

    (∀ M, M₀ ≤ M → ∀ s, F M s ∉
      Ideal.span {MvPolynomial.C ((ℓ : O₀) ^ (if ℓ = 2 then 1 else 0) * w₀)} +
        varIdeal O₀ (Fin R' ⊕ Fin R') ^ (D' + 1) + lamIdeal O₀ (Fin R' ⊕ Fin R') ℓ M) →

    (∀ M, M₀ ≤ M → ∀ j,
      MvPolynomial.bind₁ (Sum.elim MvPolynomial.X (fun _ => 0)) (f M j) - D M j * g M j ∈
        lamIdeal O (Fin R') ℓ M ∧
      ((MvPolynomial.constantCoeff (g M j) : O) : K) ≠ 0 ∧
      vl ℓ ((MvPolynomial.constantCoeff (g M j) : O) : K) = vv j ∧
      FewFactors ℓ M m₁ (D M j)) →
    ∀ ε : ℝ, 0 < ε → ∀ sg : Sig ⊕ JJ → ℤˣ,
      ∃ (M k : ℕ) (e'' e' : Fin R' → ℕ) (z : L), M₀ ≤ M ∧ k ≤ M ∧ (∀ i, e'' i < k ∧ e' i < k) ∧
        IsPrimitiveRoot z (ℓ ^ k) ∧
        (∀ s, MvPolynomial.eval₂ ((algebraMap K L).comp O₀.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inl s))) (F M s) ≠ 0) ∧
        (∀ j, MvPolynomial.eval₂ ((algebraMap K L).comp O.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inr j))) (f M j) ≠ 0) ∧
        ∑ s, vl ℓ (MvPolynomial.eval₂ ((algebraMap K L).comp O₀.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inl s))) (F M s)) ≤
          (if ℓ = 2 then 1 else 0) * (Fintype.card Sig : ℝ) + ε ∧
        (∃ εj : JJ → ℝ, (∀ j, 0 ≤ εj j) ∧ ∑ j, εj j ≤ ε ∧
          ∀ j, vl ℓ (MvPolynomial.eval₂ ((algebraMap K L).comp O.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inr j))) (f M j)) ≤ vv j + εj j) ∧
        2 * (t : ℝ) * ∑ i, (vl ℓ (z ^ (ℓ ^ e'' i) - 1) + vl ℓ (z ^ (ℓ ^ e' i) - 1)) ≤ ε

def genB {k : Type} [Field k] {m r d R : ℕ} (u : Matrix (Fin R × Bool × Fin r) (Fin m) k)
    (us : Matrix (Fin R × Bool × Fin r) (Fin d) k) (i : Fin R) (x : Fin m → k) (y : Fin d → k) :
    k :=
  ∑ b : Bool, ∑ ρ : Fin r, (u.mulVec x) (i, b, ρ) * (us.mulVec y) (i, b, ρ)

def RESCore : Prop :=
  ∀ (k K' : Type) [Field k] [Field K'] [Algebra k K'] (m r d R : ℕ)
    (u t : Matrix (Fin R × Bool × Fin r) (Fin m) k) (us : Matrix (Fin R × Bool × Fin r) (Fin d) k)
    (s : Fin R → K') (bSel : Module.Basis (Fin d) k (LinearMap.ker (Matrix.toLin' t))),
    AlgebraicIndependent k s →
    (∀ (x : Fin m → k) (y : Fin d → k), ∑ P, (t.mulVec x) P * (us.mulVec y) P = 0) →
    Module.finrank K' (LinearMap.ker (Matrix.toLin' (t.map (algebraMap k K') -
        Matrix.diagonal (fun P : Fin R × Bool × Fin r => s P.1) * u.map (algebraMap k K')))) +
      (Matrix.of fun p q : Fin d => ∑ i, s i * algebraMap k K'
        (genB u us i (bSel p : Fin m → k) (Pi.single q 1))).rank ≤ d

abbrev TruncK (K' : Type) [Field K'] (n : ℕ) : Type := K'[X] ⧸ Ideal.span {(X : K'[X]) ^ n}

def RESModule : Prop :=
  ∀ (K' : Type) [Field K'] (n a C : ℕ) (Φ : Matrix (Fin a) (Fin a) (TruncK K' n))
    (N : Submodule (TruncK K' n) (Fin a → TruncK K' n)),
    C < n → N ≤ LinearMap.ker (Matrix.toLin' Φ) →
    Module.finrank K' (LinearMap.ker (Matrix.toLin' Φ) ⧸ N.comap (LinearMap.ker (Matrix.toLin' Φ)).subtype)
      ≤ C →
    ((∀ x ∈ N, (Ideal.Quotient.mk _ X : TruncK K' n) • x = 0 → x = 0) →
      N = ⊥ ∧ Φ.det ∉ Ideal.span {(Ideal.Quotient.mk _ X : TruncK K' n) ^ (C + 1)}) ∧
    (1 ≤ a → Module.finrank K' ↥(N ⊓ LinearMap.ker
        ((Ideal.Quotient.mk _ X : TruncK K' n) • LinearMap.id :
          (Fin a → TruncK K' n) →ₗ[TruncK K' n] (Fin a → TruncK K' n))) ≤ 1 →
      (∃ x, N = Submodule.span (TruncK K' n) {x}) ∧
      ∃ i j : Fin a, ∃ a' : ℕ, ∃ h : a = a' + 1,
        (Matrix.submatrix Φ (fun p : Fin a' => Fin.cast h.symm (Fin.succAbove (Fin.cast h i) p))
          (fun q : Fin a' => Fin.cast h.symm (Fin.succAbove (Fin.cast h j) q))).det ∉
          Ideal.span {(Ideal.Quotient.mk _ X : TruncK K' n) ^ (C + 1)})

def gramB {k : Type} [Field k] {m r d R : ℕ} (u t : Matrix (Fin R × Bool × Fin r) (Fin m) k)
    (us : Matrix (Fin R × Bool × Fin r) (Fin d) k)
    (bSel : Module.Basis (Fin d) k (LinearMap.ker (Matrix.toLin' t))) (i : Fin R) :
    Matrix (Fin d) (Fin d) k :=
  Matrix.of fun p q => genB u us i (bSel p : Fin m → k) (Pi.single q 1)

def RESAbs : Prop :=
  ∀ (k K' : Type) [Field k] [Field K'] [Algebra k K'] (m r d R n a C : ℕ)
    (u t : Matrix (Fin R × Bool × Fin r) (Fin m) k) (us : Matrix (Fin R × Bool × Fin r) (Fin d) k)
    (s : Fin R → K') (bSel : Module.Basis (Fin d) k (LinearMap.ker (Matrix.toLin' t)))
    (Φ : Matrix (Fin a) (Fin a) (TruncK K' n)) (N : Submodule (TruncK K' n) (Fin a → TruncK K' n))
    (ι : ↥(N ⊓ LinearMap.ker ((Ideal.Quotient.mk _ X : TruncK K' n) • LinearMap.id :
          (Fin a → TruncK K' n) →ₗ[TruncK K' n] (Fin a → TruncK K' n))) →ₗ[K']
      ↥(LinearMap.ker (Matrix.toLin' (t.map (algebraMap k K') -
        Matrix.diagonal (fun P : Fin R × Bool × Fin r => s P.1) * u.map (algebraMap k K'))))),
    AlgebraicIndependent k s →
    (∀ (x : Fin m → k) (y : Fin d → k), ∑ P, (t.mulVec x) P * (us.mulVec y) P = 0) →
    C < n → N ≤ LinearMap.ker (Matrix.toLin' Φ) →
    Module.finrank K' (LinearMap.ker (Matrix.toLin' Φ) ⧸ N.comap (LinearMap.ker (Matrix.toLin' Φ)).subtype)
      ≤ C →
    Function.Injective ι →
    (Submodule.span k (Set.range (gramB u t us bSel)) = ⊤ →
      N = ⊥ ∧ Φ.det ∉ Ideal.span {(Ideal.Quotient.mk _ X : TruncK K' n) ^ (C + 1)}) ∧
    (1 ≤ a → d - 1 ≤ (∑ i, s i • (gramB u t us bSel i).map (algebraMap k K')).rank →
      (∃ x, N = Submodule.span (TruncK K' n) {x}) ∧
      ∃ i j : Fin a, ∃ a' : ℕ, ∃ h : a = a' + 1,
        (Matrix.submatrix Φ (fun p : Fin a' => Fin.cast h.symm (Fin.succAbove (Fin.cast h i) p))
          (fun q : Fin a' => Fin.cast h.symm (Fin.succAbove (Fin.cast h j) q))).det ∉
          Ideal.span {(Ideal.Quotient.mk _ X : TruncK K' n) ^ (C + 1)})

end Formalism.CyclotomicNorms
end
end

