import Mathlib

-- bundled from Formalism.PeriodIntegrals.FinExtTop
section
noncomputable section

namespace PI.FinExtTop

structure PadicCoeff (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] : Prop where
  ring : IsTopologicalRing O
  compact : CompactSpace O
  t2 : T2Space O
  adic : IsAdic (IsLocalRing.maximalIdeal O)
  p_mem : (p : O) ∈ IsLocalRing.maximalIdeal O
  p_ne : (p : O) ≠ 0

structure FracTop (O : Type) [CommRing O] [IsDomain O] [TopologicalSpace O]
    [TopologicalSpace (FractionRing O)] : Prop where
  emb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))

structure IsFGTop (O M : Type) [CommRing O] [TopologicalSpace O] [AddCommGroup M] [Module O M]
    [TopologicalSpace M] : Prop where
  fg : Module.Finite O M
  t2 : T2Space M
  csmul : ContinuousSMul O M

end PI.FinExtTop

namespace PI

open PI.FinExtTop in

def FinExtTop : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Free O O']
    [Module.Finite O O'],
    PadicCoeff ℓ O →
    ∃ (_ : Algebra ℤ_[ℓ] O') (_ : IsScalarTower ℤ_[ℓ] O O') (_ : Module.Finite ℤ_[ℓ] O')
      (_ : TopologicalSpace O') (_ : IsModuleTopology O O')
      (_ : TopologicalSpace (FractionRing O')) (_ : IsTopologicalAddGroup (FractionRing O'))
      (_ : ContinuousSMul O' (FractionRing O')),
      Function.Injective (algebraMap ℤ_[ℓ] O') ∧ PadicCoeff ℓ O' ∧ FracTop O' ∧
      ∀ (X' d : Type) [Fintype d] [DecidableEq d]
        (R' : Subalgebra O' (X' → Matrix d d (FractionRing O'))), Module.Finite O' R' →
        ∃ (_ : TopologicalSpace R') (_ : IsModuleTopology O' R'),
          IsTopologicalAddGroup R' ∧ ContinuousConstSMul O' R' ∧ ContinuousMul R' ∧
          IsTopologicalRing R' ∧ IsFGTop O' R'

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.FinOrdRedOne
section
noncomputable section

namespace PI.FinOrdRedOne

open NumberField IsDedekindDomain Ideal

abbrev OP (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Type :=
  P.adicCompletionIntegers E

def red {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ}
    (M : Matrix (Fin N) (Fin N) (OP E P)) :
    Matrix (Fin N) (Fin N) (IsLocalRing.ResidueField (OP E P)) :=
  M.map (IsLocalRing.residue (OP E P))

def Unram (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})], Q.ramificationIdx ℤ = 1

end PI.FinOrdRedOne

namespace PI

open NumberField IsDedekindDomain Ideal PI.FinOrdRedOne

def FinOrdRedOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → 3 ≤ p → Unram E p →
  ∀ (P : HeightOneSpectrum (𝓞 E)), (p : 𝓞 E) ∈ P.asIdeal →
  ∀ (N : ℕ) (β : GL (Fin N) (OP E P)), IsOfFinOrder β →
    red (β : Matrix (Fin N) (Fin N) (OP E P)) = 1 → β = 1

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.FlagGramNonneg
section
noncomputable section

open Matrix NumberField

namespace PI.FlagGramNonneg

def cT {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

def Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)

def HasSignature {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n ℂ) (p q : ℕ) : Prop :=
  ∃ e : n ≃ Fin p ⊕ Fin q, ∃ P : GL (Fin p ⊕ Fin q) ℂ,
    cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * J.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q

def leadMinorE {E : Type} [Field E] {N : ℕ} (A : Matrix (Fin N) (Fin N) E) (l : ℕ) : E := by
  classical
  exact if h : l ≤ N then (A.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

def gram {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {N : ℕ} (b : Module.Basis (Fin N) E V) : Matrix (Fin N) (Fin N) E :=
  fun i j => hT (b i) (b j)

def IsFlag {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (T : E) (e : Fin r → V) (z : V) : Prop :=
  LinearIndependent E e ∧ (∀ a b, hT (e a) (e b) = 0) ∧ (∀ a, hT (e a) z = 0) ∧ hT z z = -T

def fvec {V : Type} {r : ℕ} (e : Fin r → V) (z : V) : Fin (r + 1) → V :=
  Fin.snoc (α := fun _ => V) e z

def zhat {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (f f' : Fin (r + 1) → V) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  fun a b => hT (f a) (f' b)

def gval {E : Type} [Field E] [StarRing E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : E :=
  leadMinorE Z (r + 1) * star (leadMinorE Z (r + 1)) - T * T' * (leadMinorE Z r * star (leadMinorE Z r))

end PI.FlagGramNonneg

namespace PI

open PI.FlagGramNonneg

def FlagGramNonneg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (hT : V →ₗ⋆[E] V →ₗ[E] E), hT.IsSymm → hT.Nondegenerate →
    ∀ (N : ℕ) (b : Module.Basis (Fin N) E V) (τ : E →+* ℂ),
    (∀ a, τ (star a) = starRingEnd ℂ (τ a)) →
    ∀ (p r T T' : ℕ), HasSignature ((gram hT b).map τ) p (r + 1) → 0 < T → 0 < T' →
    ∀ (e e' : Fin r → V) (z z' : V), IsFlag hT (T : E) e z → IsFlag hT (T' : E) e' z' →
      ∃ c : ℝ, 0 ≤ c ∧ τ (gval (zhat hT (fvec e z) (fvec e' z')) (T : E) (T' : E)) = c

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.FockRBlock
section
open MvPolynomial

noncomputable section

namespace PI.TO

def colW (r n : ℕ) : Fin r × Fin n → (Fin n → ℕ) := fun v => Pi.single v.2 1

def colAddGen (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun v => if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)

def dualWeyl (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  weightedHomogeneousSubmodule R (colW r n) ν ⊓
    ⨅ (l : Fin n) (j : Fin n) (_ : l < j),
      LinearMap.ker ((colAddGen R (r := r) l j).toLinearMap -
        (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).toLinearMap)

def genM (R : Type) [CommRing R] (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :=
  Matrix.of fun a s => X (a, s)

def Nv (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  if vec then X (c, 0) else (genM R m).adjugate (Fin.last m) c

def theta (R : Type) [CommRing R] (m : ℕ) (vec : Bool) :
    MvPolynomial (Fin (m + 1)) R →ₐ[R] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  aeval (Nv R m vec)

def Hd (R : Type) [CommRing R] (k d : ℕ) : Submodule R (MvPolynomial (Fin k) R) :=
  restrictSupport R {μ | ∑ c, μ c = d}

def fockR {σ R : Type*} [CommRing R] (f g : MvPolynomial σ R) : R :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R)

def word1 {K : Type} [CommRing K] {k : ℕ} (l : List (Fin k × Fin k)) (f : MvPolynomial (Fin k) K) : MvPolynomial (Fin k) K :=
  l.foldr (fun y f => X y.1 * pderiv y.2 f) f

def blockEmb (K : Type*) [CommRing K] {S : Type*} {k n : ℕ} (s : S) :
    MvPolynomial (Fin k × Fin n) K →ₐ[K] MvPolynomial (S × (Fin k × Fin n)) K :=
  rename fun v => (s, v)

def tensorLat (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S] {k n : ℕ}
    (M : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) : Submodule R (MvPolynomial (S × (Fin k × Fin n)) K) :=
  Submodule.span R {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ M s) ∧ P = ∏ s, blockEmb K s (F s)}

def multideg {ι : Type*} {n : ℕ} (m : ι × Fin n →₀ ℕ) (i : ι) : ℕ := ∑ c : Fin n, m (i, c)

def Pol (R : Type*) [CommSemiring R] {ι : Type*} (n : ℕ) (d : ι → ℕ) :
    Submodule R (MvPolynomial (ι × Fin n) R) :=
  MvPolynomial.restrictSupport R {m | ∀ i, multideg m i = d i}

section Multi

variable {S : Type} [Fintype S] [DecidableEq S]

def Th0 (R : Type) [CommRing R] (m : ℕ) (vec : S → Bool) :
    MvPolynomial (S × Fin (m + 1)) R →ₐ[R] MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) R :=
  aeval fun v => blockEmb R v.1 (Nv R m (vec v.1) v.2)

end Multi

def opWord {R : Type} [CommRing R] {n' k : ℕ} (l : List (Fin n' × (Fin k × Fin k))) (f : MvPolynomial (Fin n' × Fin k) R) :
    MvPolynomial (Fin n' × Fin k) R :=
  l.foldr (fun y f => X (y.1, y.2.1) * pderiv (y.1, y.2.2) f) f

def FockRBlock : Prop :=
  ∀ (K S : Type) [CommRing K] [Fintype S] (k n : ℕ) (F G : S → MvPolynomial (Fin k × Fin n) K),
    fockR (∏ s, blockEmb K s (F s)) (∏ s, blockEmb K s (G s)) = ∏ s, fockR (F s) (G s)

def OnePos : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (m : ℕ), 1 ≤ m → ∀ (vec : Bool) (d c : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν 0 ≤ c →
    ∀ β ∈ dualWeyl K (m + 1) (m + 1) ν, ∀ s ∈ dualWeyl K (m + 1) (m + 1) ν,
      ∃ (L : Finset (List (Fin (m + 1) × Fin (m + 1)))) (a : List (Fin (m + 1) × Fin (m + 1)) → K),
        (∀ l ∈ L, l.length ≤ c) ∧
        ∀ P ∈ Hd K (m + 1) d, ∀ Q ∈ Hd K (m + 1) d,
          fockR (theta K m vec P * s) (theta K m vec Q * β) =
            fockR (theta K m vec (∑ l ∈ L, a l • word1 l P)) (theta K m vec Q)

def TenOp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n' m : ℕ), 1 ≤ m → ∀ (vec : Fin n' → Bool) (TT : Finset (Fin n')) (d : Fin n' → ℕ)
    (c : ℕ) (ν : Fin n' → Fin (m + 1) → ℕ), (∀ t, Antitone (ν t)) → (∀ t ∈ TT, ν t 0 ≤ c) → (∀ t, t ∉ TT → ν t = 0) →
    ∀ β ∈ tensorLat K K (fun t => dualWeyl K (m + 1) (m + 1) (ν t)),
    ∀ s ∈ tensorLat K K (fun t => dualWeyl K (m + 1) (m + 1) (ν t)),
      ∃ (L : Finset (List (Fin n' × (Fin (m + 1) × Fin (m + 1))))) (a : List (Fin n' × (Fin (m + 1) × Fin (m + 1))) → K),
        (∀ l ∈ L, (∀ z ∈ l, z.1 ∈ TT) ∧ ∀ t, (l.filter fun z => z.1 = t).length ≤ c) ∧
        ∀ G ∈ Pol K (ι := Fin n') (m + 1) d, (∑ l ∈ L, a l • opWord l G) ∈ Pol K (ι := Fin n') (m + 1) d ∧
          ∀ H ∈ Pol K (ι := Fin n') (m + 1) d,
            fockR (Th0 K m vec G * s) (Th0 K m vec H * β) = fockR (Th0 K m vec (∑ l ∈ L, a l • opWord l G)) (Th0 K m vec H)

end PI.TO

namespace PI

def TenOp : Prop := PI.TO.FockRBlock → PI.TO.OnePos → PI.TO.TenOp

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.FunEqAll
section
noncomputable section

open Classical

namespace PI.FunEqAll

def JetTdeg {σ : Type*} (m : σ →₀ ℕ) : ℕ := m.sum (fun _ k => k)

def jetLogG (l d : ℕ) [Fact l.Prime] {β : Type*} (v : ZMod d × β) : MvPowerSeries (ZMod d × β) ℂ_[l] :=
  fun m => ∑ e ∈ Finset.range (JetTdeg m + 1),
    if m = Finsupp.single (v.1 - 2 * (e : ZMod d), v.2) ((l ^ 2) ^ e) then (((l : ℂ_[l]) ^ e)⁻¹) else 0

def NonzeroIndexPlace {l : ℕ} [Fact l.Prime] (c : ℂ_[l]) : Prop :=
  c ∈ closure {x : ℂ_[l] | ∃ m : ℕ, 0 < m ∧ Nat.Coprime m l ∧ ∃ (ζ : ℂ_[l]) (a : Fin m → ℚ_[l]),
    ζ ^ m = 1 ∧ x = ∑ k, algebraMap ℚ_[l] ℂ_[l] (a k) * ζ ^ (k : ℕ)}

def InW {l : ℕ} [Fact l.Prime] (c : ℂ_[l]) : Prop := NonzeroIndexPlace c ∧ ‖c‖ ≤ 1

def zL (l d : ℕ) [Fact l.Prime] (s : ZMod d) : MvPowerSeries (ZMod d × Unit) ℂ_[l] :=
  jetLogG l d (s, ())

def zC (l d : ℕ) [Fact l.Prime] (c : Fin 3) (s : ZMod d) : MvPowerSeries (Fin 3 × ZMod d) ℂ_[l] :=
  MvPowerSeries.subst (fun k : ZMod d × Unit => (MvPowerSeries.X (c, k.1) : MvPowerSeries (Fin 3 × ZMod d) ℂ_[l]))
    (zL l d s)

def ExistsIntegralAdditionSeries (l d : ℕ) [Fact l.Prime] : Prop :=
  ∃ Fg : ZMod d → MvPowerSeries (Fin 3 × ZMod d) ℂ_[l],
    (∀ s n, InW (MvPowerSeries.coeff n (Fg s))) ∧
    ∀ s, MvPowerSeries.subst (fun k : ZMod d × Unit => Fg k.1) (zL l d s) = zC l d 0 s + zC l d 1 s

def Target : Prop := ∀ (l d : ℕ) [Fact l.Prime] [NeZero d], ExistsIntegralAdditionSeries l d

end PI.FunEqAll
end
end

-- bundled from Formalism.PeriodIntegrals.GalTorsConj
section
noncomputable section

namespace PI.GalTorsConj

open Classical
open scoped Pointwise

def lat2 (w₁ w₂ : ℂ) : AddSubgroup ℂ := AddSubgroup.closure {w₁, w₂}

def eisG (Λ : AddSubgroup ℂ) (k : ℕ) : ℂ :=
  ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)

def g2 (Λ : AddSubgroup ℂ) : ℂ := 60 * eisG Λ 2

def g3 (Λ : AddSubgroup ℂ) : ℂ := 140 * eisG Λ 3

def liftM (M : IntermediateField ℚ ℂ) (x : ℂ) : M := if h : x ∈ M then ⟨x, h⟩ else 0

def lamConj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) : AddSubgroup ℂ :=
  Classical.epsilon (fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (liftM M (g2 Λ)) ∧ g3 Λ' = ρ (liftM M (g3 Λ)))

def cj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x : ℂ) : ℂ := ρ (liftM M x)

def wpF (Λ : AddSubgroup ℂ) (z : ℂ) : ℂ :=
  1 / z ^ 2 + ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, (1 / (z - (w : ℂ)) ^ 2 - 1 / (w : ℂ) ^ 2)

def wpD (Λ : AddSubgroup ℂ) (z : ℂ) : ℂ := -2 * ∑' w : Λ, 1 / (z - (w : ℂ)) ^ 3

def StarPt (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) (t t' : ℂ) : Prop :=
  (t ∈ Λ ∧ t' ∈ lamConj M ρ Λ) ∨
  (t ∉ Λ ∧ t' ∉ lamConj M ρ Λ ∧ wpF Λ t ∈ M ∧ wpD Λ t ∈ M ∧
    wpF (lamConj M ρ Λ) t' = cj M ρ (wpF Λ t) ∧ wpD (lamConj M ρ Λ) t' = cj M ρ (wpD Λ t))

def InRationalLattice (Λ : AddSubgroup ℂ) (x : ℂ) : Prop := ∃ m : ℕ, 0 < m ∧ (m : ℂ) * x ∈ Λ

def Clauses (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) : Prop :=
  (∀ t, InRationalLattice Λ t → (t ∈ Λ ∨ (wpF Λ t ∈ M ∧ wpD Λ t ∈ M)) → ∃ t', StarPt M ρ Λ t t') ∧
  (∀ t t₁ t₂, StarPt M ρ Λ t t₁ → (StarPt M ρ Λ t t₂ ↔ t₁ - t₂ ∈ lamConj M ρ Λ)) ∧
  (∀ t t' ω, StarPt M ρ Λ t t' → ω ∈ Λ → StarPt M ρ Λ (t + ω) t') ∧
  (∀ t t' u u', StarPt M ρ Λ t t' → StarPt M ρ Λ u u' → StarPt M ρ Λ (t + u) (t' + u')) ∧
  (∀ c : ℂ, (∀ t ∈ Λ, c * t ∈ Λ) → c ∈ M → cj M ρ c = c →
    ∀ t t', StarPt M ρ Λ t t' → StarPt M ρ Λ (c * t) (c * t')) ∧
  (∀ (n : ℕ) t t', StarPt M ρ Λ t t' → ((n : ℂ) * t ∈ Λ ↔ (n : ℂ) * t' ∈ lamConj M ρ Λ)) ∧
  (∀ n : ℕ, 0 < n →
    (∀ t, (n : ℂ) * t ∈ Λ → t ∉ Λ → wpF Λ t ∈ M ∧ wpD Λ t ∈ M) →
    ∀ t', (n : ℂ) * t' ∈ lamConj M ρ Λ → ∃ t, (n : ℂ) * t ∈ Λ ∧ StarPt M ρ Λ t t')

def Target : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ),
      g2 (lat2 w₁ w₂) ∈ M → g3 (lat2 w₁ w₂) ∈ M → Clauses M ρ (lat2 w₁ w₂)

end PI.GalTorsConj
end
end

-- bundled from Formalism.PeriodIntegrals.GaussIntegral
section
open ValuativeRel MeasureTheory

namespace PI

def GaussIntegral : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ (ψ : AddChar F ℂ), Continuous ψ → (∀ x : F, (∀ y ∈ 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) →
  ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) F), H.IsSymm → H.det ≠ 0 →
  ∀ (L : AddSubgroup (Fin d → F)), IsCompact (L : Set (Fin d → F)) → IsOpen (L : Set (Fin d → F)) →
  ∃ δ : ℝ, 0 < δ ∧ ∀ t : F, t ≠ 0 → (μ ((fun y => t * y) '' (𝒪[F] : Set F))).toReal < δ →
    ‖∫ x in (L : Set (Fin d → F)), ψ (dotProduct x (H.mulVec x) / (2 * t))
        ∂(Measure.pi fun _ : Fin d => μ)‖ =
      (μ ((fun y => (t⁻¹ • H).det * y) '' (𝒪[F] : Set F))).toReal ^ (-(1 / 2 : ℝ))

end PI
end

-- bundled from Formalism.PeriodIntegrals.HeisDefs
section
namespace PI

section Heis

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

noncomputable def HfG (A : ℝ) (z w : T → I → J → ℂ) : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (A : ℂ)

noncomputable def UG (A : ℝ) (x : T → I → J → ℂ) (G : (T → I → J → ℂ) → ℂ) : (T → I → J → ℂ) → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * HfG A z x - (Real.pi : ℂ) * HfG A x x / 2)

end Heis

end PI
end

-- bundled from Formalism.PeriodIntegrals.Hensel
section
open ValuativeRel

namespace PI

def HenselStrong : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (f : Polynomial 𝒪[F]) (a : 𝒪[F]),
    valuation F ((f.eval a : 𝒪[F]) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) : F) ^ 2 →
    ∃ b : 𝒪[F], f.eval b = 0 ∧
      valuation F (((b - a : 𝒪[F])) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) : F)

end PI
end

-- bundled from Formalism.PeriodIntegrals.HermLatFin
section
open NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace PI.HermLatFin

def herm {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

def IsLat {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin n → E)) = ⊤

def admitted {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  IsLat L ∧ (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (herm σ J x y)) ∧
    ∀ y : Fin n → E, (∀ x ∈ L, IsIntegral ℤ (herm σ J x y)) → (T : E) • y ∈ L

def IsUJ {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J g : Matrix (Fin n) (Fin n) E) : Prop :=
  (g.map σ)ᵀ * J * g = J

def HermLatFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ),
    (∀ τ : E →+* ℂ, ∀ a : E, τ (σ a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, (J.map τ).PosDef) →
    0 < T →
    ∃ S : Set (Submodule (𝓞 E) (Fin n → E)), S.Finite ∧
      ∀ L, admitted σ J T L → ∃ L' ∈ S, ∃ g : Matrix (Fin n) (Fin n) E, IsUJ σ J g ∧
        (fun x => g *ᵥ x) '' (L' : Set (Fin n → E)) = (L : Set (Fin n → E))

end PI.HermLatFin
end
end

-- bundled from Formalism.PeriodIntegrals.IndexUBound
section
namespace PI.IndexUBound

def IndexUBound : Prop :=
  ∀ (ι : Type) (S : Finset ι) (g : ι → ℕ) (r : ℕ) (y : ℝ),
    (∀ v ∈ S, 2 ≤ g v) → ∑ v ∈ S, 1 / ((g v : ℝ) - 1) ≤ y →
      (1 - y) * ∏ v ∈ S, (g v : ℝ) ^ (r * (r - 1) / 2) ≤
        ∏ v ∈ S, ∏ i ∈ Finset.Ico 1 r, ((g v : ℝ) ^ i - 1)

end PI.IndexUBound
end

-- bundled from Formalism.PeriodIntegrals.InertPrime
section
open NumberField

namespace PI

def InertPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (b : K) (d p : ℕ), b ^ 2 = -(d : K) → p.Prime →
    jacobiSym (-(d : ℤ)) p = -1 → (Ideal.span {(p : 𝓞 K)}).IsPrime

end PI
end

