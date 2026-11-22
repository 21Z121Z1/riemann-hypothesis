import Formalism.PadicSubsetSums.CentralIdempotents.WindowSums
import Formalism.PadicSubsetSums.CentralIdempotents.PrimitiveRootFifteenSubOneUnit

-- bundled from Formalism.PadicSubsetSums.CentralIdempotents.ArchimedeanComponents
section
noncomputable section

namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial

def SqrtNegInCyclotomic : Prop :=
  ∀ (l : ℕ), l.Prime → l % 4 = 3 → ∀ (F : Type) [Field F] (ζ : F), IsPrimitiveRoot ζ l →
    IsSquare (-(l : F))

def DictRing : Prop :=
  ∀ (A₁ G : Type) [CommRing A₁] [Group G] [Fintype G] [MulSemiringAction G A₁]
    (p q E w u : A₁) (φ γ : A₁ →+* A₁) (vv : G → A₁ˣ) (ε₀ : A₁ˣ),
    (∀ x y : A₁, p * x = p * y → x = y) →
    (∀ g : G, g • p = p * vv g) → φ p = p * q → q = ε₀ * E → γ p = p * w →
    (∀ (g : G) (x : A₁), φ (g • x) = g • φ x) → (∀ (g : G) (x : A₁), γ (g • x) = g • γ x) →
    (∀ g : G, g • u = u) → p ∣ w - u → (∀ x : A₁, p ∣ γ x - x) →
    (∀ x : A₁, (∀ g : G, g • x = x) → p ∣ x → (∏ g : G, g • p) ∣ x) →
    (∃ ε : A₁ˣ, (∏ g : G, g • p) = ε * p ^ Fintype.card G) ∧
    (∃ ε : A₁ˣ, φ (∏ g : G, g • p) = ε * (∏ g : G, g • p) * E ^ Fintype.card G) ∧
    ((∏ g : G, g • p) ^ 2 ∣ γ (∏ g : G, g • p) - u ^ Fintype.card G * (∏ g : G, g • p)) ∧
    (∀ (y : ℕ) (f : A₁), (∀ g : G, g • f = f) →
      (∏ g : G, g • p) ^ (y + 1) ∣
        γ ((∏ g : G, g • p) ^ y * f) - u ^ (Fintype.card G * y) * ((∏ g : G, g • p) ^ y * f))

def PhiFiltrationMem : Prop :=
  ∀ (l e s H a : ℕ), l.Prime → e * s = l - 1 → a = ⌈((e * H : ℕ) : ℝ) / ((l : ℝ) - 1)⌉₊ →
    ¬ l ∣ s ∧ H ≤ s * a

def HorizInj : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (γ ϖ : Module.End R V) (c : ℕ → R),
    Function.Injective ϖ →
    (∀ (i : ℕ) (x : V), ∃ y, γ ((ϖ ^ i) x) - c i • (ϖ ^ i) x = (ϖ ^ (i + 1)) y) →
    (∀ (i : ℕ), 1 ≤ i → ∀ x y : V, (c i - 1) • x = ϖ y → ∃ x', x = ϖ x') →
    ∀ (k : ℕ) (w r : V), γ (ϖ w) - ϖ w = (ϖ ^ k) r → ∃ r', ϖ w = (ϖ ^ k) r'

def LogShift : Prop :=
  ∀ (l h S : ℕ), 2 ≤ l → 1 ≤ h → Real.logb l ((h : ℝ) + S) ≤ Real.logb l h + S

def BracketA : Prop :=
  ∀ (l e h S η n r m e' : ℕ) (c ρ σ κ y : ℝ), 3 ≤ l → 1 ≤ e → 1 ≤ h → 0 ≤ c →
    ρ ≤ 9 * ((e * h : ℕ) : ℝ) / l + 3 → σ ≤ 9 * ((e * h : ℕ) : ℝ) / l + 3 →
    κ ≤ (e : ℝ) * ((S : ℝ) + (S : ℝ) / ((l : ℝ) - 1) + Real.logb l ((h : ℝ) + S)) →
    y ≤ c * (ρ + σ) + κ + η + 1 + Real.logb l h →
    y ≤ (18 * c + 3) *
      (((e * h : ℕ) : ℝ) / l + (e : ℝ) * S + (e : ℝ) * Real.logb l h + 1 + η) ∧
    ((n : ℝ) * e + 1) * r * y + (n : ℝ) * e * ((e : ℝ) + 1) * m * e' ≤
      (18 * c + 3) * (((n : ℝ) * e + 1) * r *
        (((e * h : ℕ) : ℝ) / l + (e : ℝ) * S + (e : ℝ) * Real.logb l h + 1 + η)) +
      (n : ℝ) * e * ((e : ℝ) + 1) * m * e'

def PDPowFrob : Prop :=
  (∀ (l i : ℕ), l.Prime → 1 ≤ i → (i.factorial ^ l * l) ∣ (l * i).factorial) ∧
  ∀ (l i : ℕ), l.Prime → 1 ≤ i → ∀ (A : Type) [CommRing A] [Algebra ℚ A] (S : Subring A) (x : A),
    (∀ k : ℕ, algebraMap ℚ A (1 / (k.factorial : ℚ)) * x ^ k ∈ S) →
    ∃ z ∈ S, (algebraMap ℚ A (1 / (i.factorial : ℚ)) * x ^ i) ^ l = (l : A) * z

def FrobDiffPD : Prop :=
  ∀ (l : ℕ), l.Prime → ∀ (A : Type) [CommRing A] [Algebra ℚ A] (S : Subring A) (u x : A),
    u ∈ S → x ∈ S → algebraMap ℚ A (1 / (l.factorial : ℚ)) * x ^ l ∈ S →
    ∃ Y ∈ S, (u + x) ^ l - u ^ l = (l : A) * Y

def FallingWeyl : Prop :=
  ∀ (B : Type) [Ring B] (u D : B), D * u = u * D + 1 →
    ∀ i : ℕ, u ^ i * D ^ i = aeval (u * D) (descPochhammer ℤ i)

def FallingN : Prop :=
  ∀ (R : Type) [CommRing R] (i : ℕ) (f : R[X]),
    aeval ((LinearMap.mulLeft R (X : R[X])) ∘ₗ (derivative : R[X] →ₗ[R] R[X]) : Module.End R R[X])
      (descPochhammer R i) f = X ^ i * (derivative^[i] f)

def EulerCoord : Prop :=
  ∀ (K : Type) [Field K] (l : K), l ≠ 0 → ∃ ω : (PowerSeries K)ˣ,
    (PowerSeries.X * (ω : PowerSeries K)) * (PowerSeries.C l - PowerSeries.X) =
      PowerSeries.C l * PowerSeries.X ∧
    ∀ j : ℕ, PowerSeries.X * (PowerSeries.X - PowerSeries.C l) *
        PowerSeries.derivative K ((PowerSeries.X * (ω : PowerSeries K)) ^ j) =
      -(PowerSeries.C l * (j : PowerSeries K)) * (PowerSeries.X * (ω : PowerSeries K)) ^ j

def CokerT : Prop :=
  ∀ (R V Vb : Type) [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup Vb] [Module R Vb]
    (𝓋 : Module.End R V) (pr : V →ₗ[R] Vb) (N : Module.End R Vb) (V' : Submodule R V)
    (P₁ P₂ : R[X]) (d : R) (A' l : ℕ),
    Function.Injective 𝓋 → Function.Surjective pr → LinearMap.ker pr = LinearMap.range (𝓋 ^ l) →
    2 * A' ≤ l → (∀ x ∈ V', 𝓋 x ∈ V') → (∀ x, (𝓋 ^ A') x ∈ V') →
    (∀ z ∈ (V'.map (𝓋 ^ A')).map pr, N z ∈ (V'.map (𝓋 ^ A')).map pr) →
    (∀ x ∈ V', aeval N P₁ (pr x) ∈ (V'.map (𝓋 ^ A')).map pr) →
    (∀ x, aeval N P₂ (pr ((𝓋 ^ A') x)) ∈ (LinearMap.range (𝓋 ^ (2 * A'))).map pr) →
    C d ∈ Ideal.span ({P₁, P₂} : Set R[X]) →
    ∀ x : V, d • x ∈ V'

def PDBinom : Prop :=
  (∀ (A : Type) [CommRing A] [Algebra ℚ A] (E p : A) (m : ℕ),
    (E - p) ^ m = (m.factorial : A) * ∑ i ∈ Finset.range (m + 1),
      (algebraMap ℚ A (1 / (i.factorial : ℚ)) * E ^ i) *
        (algebraMap ℚ A (1 / ((m - i).factorial : ℚ)) * (-p) ^ (m - i))) ∧
  ∀ (l k : ℕ), l.Prime → padicValNat l k.factorial ≤ k

def PDPowerMem : Prop :=
  ∀ (l : ℕ), l.Prime → ∀ (A : Type) [CommRing A] [Algebra ℚ A] (S : Subring A) (E : A),
    (∀ i : ℕ, algebraMap ℚ A (1 / (i.factorial : ℚ)) * E ^ i ∈ S) →
    (∀ a : ℚ, 0 ≤ padicValRat l a → algebraMap ℚ A a ∈ S) →
    ∀ m : ℕ, ∃ z ∈ S, (E - (l : A)) ^ m = (m.factorial : A) * z

def PhiFilExp : Prop :=
  (∀ (l j i : ℕ), l.Prime → j + 1 ≤ l → j ≤ i → j + padicValNat l i.factorial ≤ i) ∧
  ∀ (l i : ℕ), l.Prime → 1 ≤ i → 1 + padicValNat l i.factorial ≤ i

def PhiFilMem : Prop :=
  ∀ (l : ℕ), l.Prime → ∀ (A : Type) [CommRing A] [Algebra ℚ A] (S : Subring A) (c : A), c ∈ S →
    (∀ a : ℚ, 0 ≤ padicValRat l a → algebraMap ℚ A a ∈ S) →
    ∀ j i : ℕ, j + 1 ≤ l → j ≤ i →
      ∃ z ∈ S, algebraMap ℚ A (1 / (i.factorial : ℚ)) * ((l : A) * c) ^ i = (l : A) ^ j * z

def TailGlue : Prop :=
  (∀ (l H η : ℕ), η < H → (l : ℤ) - 14 * H ≤ (l : ℤ) - 10 * H - (H + η + 1) - η) ∧
  (∀ (l e c r' n : ℕ), 1 ≤ l → e ≤ c * (l ^ r' - 1) → r' ≤ n → e * l ^ (n - r') ≤ c * l ^ n) ∧
  ∀ (l i n : ℕ), 2 ≤ l → 2 ≤ i → 1 ≤ n → i ≤ (i - 1) * l ^ n

end Formalism.IrreducibleCountingLemmas.WindowSums
end
end

-- bundled from Formalism.PadicSubsetSums.CentralIdempotents.FactorOverLocalSubalgebraMonic
section
noncomputable section

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

def OpenSubgroupContinuous : Prop :=
  ∀ (A : Type) [Group A] [TopologicalSpace A] [IsTopologicalGroup A] (U : Subgroup A)
    (χ : A →* Circle), IsOpen (U : Set A) → Continuous (fun u : U => χ (u : A)) → Continuous χ

def CircleCharExtendsOpen : Prop :=
  ∀ (A : Type) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (U : Subgroup A)
    (χ : U →* Circle), IsOpen (U : Set A) → Continuous χ →
    ∃ χ' : A →* Circle, Continuous χ' ∧ ∀ u : U, χ' (u : A) = χ u

def RunJumps : Prop :=
  ∀ (n p t : ℕ) (a : Fin n → ℤ) (c : ℤ), Antitone a → 1 ≤ t → p + t ≤ n →
    (∀ i : Fin n, a i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    (∀ j : Fin n, ((p : ℤ) - c ≤ (j : ℤ) - a j ∧ (j : ℤ) - a j < (p : ℤ) - c + t) ↔
      (p ≤ (j : ℕ) ∧ (j : ℕ) < p + t)) ∧
    (∀ k : ℕ, k < t → ∃ j : Fin n, (j : ℤ) - a j = (p : ℤ) - c + k) ∧
    ∀ j : Fin n, (j : ℤ) - a j ≠ (p : ℤ) - c - 1 ∧ (j : ℤ) - a j ≠ (p : ℤ) - c + t

def BlockIsRun : Prop :=
  ∀ (n p t : ℕ) (a : Fin n → ℤ) (c w : ℤ), Antitone a → p + t ≤ n → n < 2 * t →
    (∀ i : Fin n, a i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    (∀ k : ℕ, k < t → ∃ j : Fin n, (j : ℤ) - a j = w + k) →
    w = (p : ℤ) - c ∧
    ∀ j : Fin n, (w ≤ (j : ℤ) - a j ∧ (j : ℤ) - a j < w + t) ↔ (p ≤ (j : ℕ) ∧ (j : ℕ) < p + t)

def ResidueCharpolyEq : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O)),
    IsLocalRing T → ∀ (G : Type) (n : ℕ) (r : X' → G → Matrix (Fin n) (Fin n) O),
    (∀ (g : G) (j : ℕ), (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T) →
    ∀ (x y : X') (g : G),
      Matrix.charpolyRev ((r x g).map (IsLocalRing.residue O)) =
        Matrix.charpolyRev ((r y g).map (IsLocalRing.residue O)) ∧
      ((r x g).map (IsLocalRing.residue O)).charpoly =
        ((r y g).map (IsLocalRing.residue O)).charpoly

def BrauerNesbittCharZero : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (G : Type) [Group G] (V W : Type) [AddCommGroup V]
    [Module k V] [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (τ : Representation k G W),
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) τ.asModule →
    (∀ g, (ρ g).charpoly = (τ g).charpoly) →
    ∃ e : V ≃ₗ[k] W, ∀ g, e.toLinearMap ∘ₗ ρ g = τ g ∘ₗ e.toLinearMap

def BrauerNesbittFinite : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (G : Type) [Group G] (V W : Type) [AddCommGroup V]
    [Module k V] [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (τ : Representation k G W),
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) τ.asModule →
    (∀ g, (ρ g).charpoly = (τ g).charpoly) →
    ∃ e : V ≃ₗ[k] W, ∀ g, e.toLinearMap ∘ₗ ρ g = τ g ∘ₗ e.toLinearMap

def RootCoefficient : Prop :=
  ∀ m i : ℤ, 2 * ((m - i) + (m - 1) - (i - 1)) + 2 + 2 = 4 * (m - i + 1)

def RootSumUnitary : Prop :=
  ∀ (m : ℕ) (i : Fin m),
    ((∑ a : Fin m, ∑ b : Fin m, if a < b then
        (2 : ℤ) • ((Pi.single a 1 : Fin m → ℤ) - Pi.single b 1) +
          (2 : ℤ) • ((Pi.single a 1 : Fin m → ℤ) + Pi.single b 1) else 0) +
      ∑ a : Fin m, ((2 : ℤ) • (Pi.single a 1 : Fin m → ℤ) +
        (1 : ℤ) • ((2 : ℤ) • (Pi.single a 1 : Fin m → ℤ)))) i = 4 * ((m : ℤ) - (i : ℤ))

def HullBoundSigned : Prop :=
  ∀ (r m : ℕ) (x : Fin m → ℝ), r = 2 * m + 1 →
    x ∈ convexHull ℝ (Set.range fun p : Equiv.Perm (Fin m) × (Fin m → ℤˣ) =>
      fun i : Fin m => (((p.2 i : ℤˣ) : ℤ) : ℝ) * ((m : ℝ) - ((p.1 i : ℕ) : ℝ))) →
    ∀ i, |x i| ≤ ((r : ℝ) - 1) / 2

def InertParameterBound : Prop :=
  ∀ (r m : ℕ) (q : ℝ) (x : Fin m → ℝ) (α : Fin m → ℂ), r = 2 * m + 1 → 1 < q →
    (∀ i, ‖α i‖ = q ^ (x i)) →
    x ∈ convexHull ℝ (Set.range fun p : Equiv.Perm (Fin m) × (Fin m → ℤˣ) =>
      fun i : Fin m => (((p.2 i : ℤˣ) : ℤ) : ℝ) * ((m : ℝ) - ((p.1 i : ℕ) : ℝ))) →
    ∀ β ∈ Multiset.map α Finset.univ.val + Multiset.map (fun i => (α i)⁻¹) Finset.univ.val + {1},
      ‖β‖ ≤ q ^ (((r : ℝ) - 1) / 2)

def SemisimpleQuotientSimple : Prop :=
  ∀ (R M Q : Type) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    [IsSemisimpleModule R Q] [Nontrivial Q] (π : M →ₗ[R] Q),
    (∀ N N' : Submodule R M, IsCoatom N → IsCoatom N' → N = N') → Function.Surjective π →
    IsSimpleModule R Q

def inertFactor (q : ℝ) (ch s : ℂ) : ℂ :=
  (1 - ((q ^ 2 : ℝ) : ℂ) ^ (-s)) / (1 - ch * ((q ^ 2 : ℝ) : ℂ) ^ (-s))

def InertEulerQuotient : Prop :=
  ∀ (ι : Type) (q : ι → ℝ) (ch : ι → ℂ) (s : ℂ), (∀ v, 2 ≤ q v) → (∀ v, ‖ch v‖ = 1) →
    1 / 2 < s.re → Summable (fun v => (q v) ^ (-2 * s.re)) →
    Summable (fun v => ‖inertFactor (q v) (ch v) s - 1‖) ∧
    Multipliable (fun v => inertFactor (q v) (ch v) s) ∧
    (∏' v, inertFactor (q v) (ch v) s) ≠ 0

def InertEulerHolomorphic : Prop :=
  ∀ (ι : Type) (q : ι → ℝ) (ch : ι → ℂ), (∀ v, 2 ≤ q v) → (∀ v, ‖ch v‖ = 1) →
    (∀ σ : ℝ, 1 / 2 < σ → Summable (fun v => (q v) ^ (-2 * σ))) →
    DifferentiableOn ℂ (fun s => ∏' v, inertFactor (q v) (ch v) s) {s : ℂ | 1 / 2 < s.re}

def PoleTransfer : Prop :=
  ∀ (L Z R : ℂ → ℂ), ContinuousAt R 1 → R 1 ≠ 0 → (∀ s : ℂ, 1 < s.re → L s = Z s * R s) →
    Filter.Tendsto (fun s => ‖Z s‖) (nhdsWithin 1 {s : ℂ | 1 < s.re}) Filter.atTop →
    Filter.Tendsto (fun s => ‖L s‖) (nhdsWithin 1 {s : ℂ | 1 < s.re}) Filter.atTop

def GoodCuspidalOne : Prop :=
  ∀ (k : Type) [Field k] (P : Type) [Nonempty P] (r : ℕ) (f : P → k[X]) (I : Type) [Fintype I]
    (n d : I → ℕ) (h : P → I → k[X]), 1 ≤ r →
    (∀ v, (f v).natDegree = r) → (∀ v, Squarefree (f v)) → (∀ v, f v = ∏ i, h v i ^ d i) →
    (∀ v i, (h v i).natDegree = n i) → (∀ i, 1 ≤ n i) → (∀ i, 1 ≤ d i) →
    (¬ ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ r ∧ ∀ v, ∃ g : k[X], g ∣ f v ∧ g.natDegree = a) →
    Fintype.card I = 1 ∧ ∀ i, d i = 1 ∧ n i = r

def CharpolyOverSubalgebra : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O))
    (n : ℕ) (M : X' → Matrix (Fin n) (Fin n) O),
    (∀ j : ℕ, (fun x => (Matrix.charpolyRev (M x)).coeff j) ∈ T) →
    ∃ F : T[X], F.Monic ∧ ∀ x, F.map (ev T x) = (M x).charpoly

def FactorOverLocalSubalgebraMonic : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O)),
    IsLocalRing T → ∀ (t : ℕ) (c : O) (F : T[X]) (s : X' → O[X]), F.Monic →
    (∀ x, F.map (ev T x) = s x * (X - C c) ^ t) → (∀ x, IsUnit ((s x).eval c)) →
    ∃ P : T[X], P.Monic ∧ F = P * (X - C (algebraMap O T c)) ^ t ∧
      IsUnit (P.eval (algebraMap O T c)) ∧ ∀ x, P.map (ev T x) = s x

def FactorAnnihilatorFamily : Prop :=
  ∀ (O K : Type) [CommRing O] [IsLocalRing O] [Field K] [Algebra O K],
    Function.Injective (algebraMap O K) →
    ∀ (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O)), IsLocalRing T →
    ∀ (V : X' → Type) [∀ x, AddCommGroup (V x)] [∀ x, Module K (V x)]
      [∀ x, FiniteDimensional K (V x)] (A B : ∀ x, Submodule K (V x))
      (γ₀ γ : ∀ x, Module.End K (V x)) (c cγ : O) (t : ℕ) (F : T[X]),
    (∀ x, (F.map (ev T x)).map (algebraMap O K) = (γ₀ x).charpoly) →
    (∀ x, IsCompl (A x) (B x)) → (∀ x, ∀ v ∈ A x, γ₀ x v ∈ A x) → (∀ x, ∀ v ∈ A x, γ x v ∈ A x) →
    (∀ x, ∀ v ∈ B x, γ₀ x v = algebraMap O K c • v) →
    (∀ x, ∀ v ∈ B x, γ x v = algebraMap O K cγ • v) →
    (∀ x, Module.finrank K (B x) = t) →
    (∀ x, ((F.map (ev T x)).map (IsLocalRing.residue O)).rootMultiplicity
      (IsLocalRing.residue O c) = t) →
    ∃ P : T[X], P.Monic ∧ F = P * (X - C (algebraMap O T c)) ^ t ∧
      IsUnit (P.eval (algebraMap O T c)) ∧
      ∀ x, (aeval (γ₀ x) ((P.map (ev T x)).map (algebraMap O K))) *
        (γ x - algebraMap K (Module.End K (V x)) (algebraMap O K cγ)) = 0

def CuspValueCount : Prop :=
  ∀ (n p t : ℕ) (lam : Fin n → ℤ) (c : ℤ), p + t ≤ n → n < 2 * t →
    (∀ i : Fin n, lam i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    ∀ c₀ : ℤ, (Finset.univ.filter fun j => lam j = c₀).card ≤ t

def CuspValueCountDual : Prop :=
  ∀ (n p t : ℕ) (lam : Fin n → ℤ) (c : ℤ), p + t ≤ n → n < 2 * t →
    (∀ i : Fin n, lam i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    ∀ c₀ : ℤ, (Finset.univ.filter fun j : Fin n => -lam (Fin.rev j) = c₀).card ≤ t

def CuspCountSym : Prop :=
  ∀ (n p t : ℕ) (lam : Fin n → ℤ) (c : ℤ), p + t ≤ n → n < 2 * t →
    (∀ i : Fin n, lam i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    ∀ (c₀ : ℤ) (i : ℕ), 1 ≤ i →
      ¬ ((Finset.univ.filter fun j => c₀ < lam j).card +
        (Finset.univ.filter fun j => lam j < c₀).card + 2 * i ≤ n - t)

def CuspCountDual : Prop :=
  ∀ (n p t : ℕ) (lam : Fin n → ℤ) (c : ℤ), p + t ≤ n → n < 2 * t →
    (∀ i : Fin n, lam i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    ∀ (c₀ : ℤ) (i : ℕ), 1 ≤ i →
      ¬ ((Finset.univ.filter fun j => c₀ < lam j).card + i ≤ n - p - t ∧
        (Finset.univ.filter fun j => lam j < c₀).card + i ≤ p)

def CuspCentre : Prop :=
  ∀ (n p t : ℕ) (lam : Fin n → ℤ) (c : ℤ), p + t ≤ n → n < 2 * t →
    (∀ i : Fin n, lam i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) →
    ∀ c₀ : ℤ, (Finset.univ.filter fun j => c₀ < lam j).card +
        (Finset.univ.filter fun j => lam j < c₀).card ≤ n - t → c₀ = c

def ZCountRange : Prop :=
  ∀ (K M N : Type) [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [FiniteDimensional K M] [FiniteDimensional K N] (I Zg : Type) [Fintype I] [Fintype Zg]
    (Ms : I → Submodule K M) (Nx : Zg → Submodule K N) (e : Zg ≃ I) (θ : M →ₗ[K] N),
    iSupIndep Ms → (⨆ s, Ms s) = ⊤ → iSupIndep Nx →
    (∀ x, Set.BijOn θ (Ms (e x) : Set M) (Nx x : Set N)) →
    Function.Injective θ ∧ (LinearMap.range θ = ⨆ x, Nx x) ∧
      Module.finrank K (LinearMap.range θ) = ∑ x, Module.finrank K (Nx x) ∧
      Module.finrank K (LinearMap.range θ) = Module.finrank K M

end Formalism.IrreducibleCountingLemmas.Z
end
end

