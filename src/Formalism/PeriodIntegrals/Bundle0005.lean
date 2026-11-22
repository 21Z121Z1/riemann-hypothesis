import Mathlib

-- bundled from Formalism.PeriodIntegrals.InvIdealIdxPi
section
noncomputable section

namespace PI

open NumberField nonZeroDivisors

def InvIdealIdxPi : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] (J : ι → Ideal (𝓞 E)), (∀ i, J i ≠ ⊥) →
    (Submodule.pi Set.univ (fun _ : ι => (1 : Submodule (𝓞 E) E))).toAddSubgroup.relIndex
      (Submodule.pi Set.univ (fun i =>
        (((J i : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E))).toAddSubgroup =
      ∏ i, Ideal.absNorm (J i)

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.IsoDerivB
section
noncomputable section

namespace PI.IsoDerivB

def ColChoice {Lt : Type} (N1 : ℕ) (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))

def colsOf {k : Type} [Zero k] {N : ℕ} (Y : Matrix (Fin N) (Fin N) k) : Fin N → ℕ → k :=
  fun a j => if h : j < N then Y a ⟨j, h⟩ else 0

abbrev LaC {Lt : Type} (N : ℕ) (nu : Lt → YoungDiagram) : Type := ColChoice N nu → ℂ

def hvC {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) (x : Lt → Fin N → ℕ → ℂ) : LaC N nu :=
  fun J => minY N nu J x

def Vnu {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) : Submodule ℂ (LaC N nu) :=
  Submodule.span ℂ (Set.range (hvC N nu))

def l2 {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ : LaC N nu) : ℝ := ∑ᶠ J, ‖φ J‖ ^ 2

def prC {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ ψ : LaC N nu) : ℂ := ∑ᶠ J, φ J * ψ J

def VnuMap {Lt : Type} [Fintype Lt] {N N' : ℕ} (nu : Lt → YoungDiagram) (f : Lt → Matrix (Fin N') (Fin N) ℂ)
    (φ : LaC N nu) : LaC N' nu :=
  fun I => ∑ᶠ J : ColChoice N nu, (∏ s, ∏ c : Fin ((nu s).rowLen 0),
    Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (J s c k))) * φ J

def canC {Lt : Type} [Fintype Lt] {N : ℕ} {nu : Lt → YoungDiagram} (φ : LaC N nu) (y : Lt → Fin N → ℕ → ℂ) : ℂ :=
  prC φ (hvC N nu y)

abbrev Idx (T : Type) (N N' : ℕ) : Type := T × Fin N' × Fin N

abbrev FrV (T : Type) (N : ℕ) : Type := T × Fin N × Fin N

abbrev VC (T : Type) (N N' : ℕ) : Type := T → Fin N' → Fin N → ℂ

abbrev Mono (T : Type) (N N' : ℕ) : Type := (T × Fin N' × Fin N) →₀ ℕ

open Classical in

def coordV {T : Type} {N N' : ℕ} (k : T × Fin N' × Fin N) : VC T N N' :=
  fun τ i j => if τ = k.1 ∧ i = k.2.1 ∧ j = k.2.2 then 1 else 0

def taylor {T : Type} [Fintype T] {N N' : ℕ} (G : VC T N N' → ℂ) (α : Mono T N N') : ℂ :=
  iteratedFDeriv ℂ (Multiset.card α.toMultiset) G 0
      (fun i => coordV (α.toMultiset.toList.get ⟨i, by simpa using i.2⟩)) /
    (α.prod fun _ n => (n.factorial : ℂ))

def applyAt0 {T : Type} [Fintype T] {N N' : ℕ} (P : MvPolynomial (Idx T N N') ℂ) (G : VC T N N' → ℂ) : ℂ :=
  ∑ α ∈ P.support, MvPolynomial.coeff α P * (α.prod fun _ n => (n.factorial : ℂ)) * taylor G α

def evFr {T : Type} {N : ℕ} (Q : MvPolynomial (FrV T N) ℂ) (y : T → Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  MvPolynomial.eval (fun k : FrV T N => y k.1 k.2.1 k.2.2) Q

def polD {T : Type} {N N' : ℕ} (s : T → ℂ) (Q : MvPolynomial (FrV T N) ℂ)
    (y' : T → Matrix (Fin N') (Fin N') ℂ) : MvPolynomial (Idx T N N') ℂ :=
  MvPolynomial.aeval (fun k : FrV T N => ∑ b : Fin N',
    MvPolynomial.C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
      MvPolynomial.X ((k.1, b, k.2.1) : Idx T N N')) Q

def PIJ {Lt T : Type} [Fintype Lt] (tp : Lt → T) {N N' : ℕ} (nu : Lt → YoungDiagram) (s : T → ℂ) (I : ColChoice N' nu)
    (J : ColChoice N nu) : MvPolynomial (Idx T N N') ℂ :=
  ∏ z, ∏ c : Fin ((nu z).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu z).colLen c) =>
    MvPolynomial.C (s (tp z)) * MvPolynomial.X ((tp z, I z c i, J z c k) : Idx T N N'))

def AOp {Lt T : Type} [Fintype Lt] [Fintype T] (tp : Lt → T) {N N' : ℕ} (nu : Lt → YoungDiagram) (s : T → ℂ) (Θ : VC T N N' → ℂ)
    (φ : LaC N nu) : LaC N' nu :=
  fun I => ∑ᶠ J : ColChoice N nu, applyAt0 (PIJ tp nu s I J) Θ * φ J

abbrev frC {Lt T : Type} (tp : Lt → T) {N : ℕ} (y : T → Matrix (Fin N) (Fin N) ℂ) : Lt → Fin N → ℕ → ℂ :=
  fun z => colsOf (y (tp z))

def IsoDerivB : Prop :=
  ∀ (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (tp : Lt → T) (N N' : ℕ) (nu : Lt → YoungDiagram) (s : T → ℂ) (Θ : VC T N N' → ℂ) (φ : LaC N nu)
    (Q : MvPolynomial (FrV T N) ℂ), (∀ y, evFr Q y = canC φ (frC tp y)) →
    ∀ y' : T → Matrix (Fin N') (Fin N') ℂ,
      applyAt0 (polD s Q y') Θ = canC (AOp tp nu s Θ φ) (frC tp y')

end PI.IsoDerivB
end
end

-- bundled from Formalism.PeriodIntegrals.IsoDet
section
noncomputable section

open scoped Classical

namespace PI.IsoDetDefs

open NumberField IsDedekindDomain Module

section Defs

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def hdual (B : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Submodule R V :=
  ⨅ y ∈ L, (1 : Submodule R K).comap ((B y).restrictScalars R)

def locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R) (L : Submodule R W) :
    Submodule R W where
  carrier := {x | ∃ s ∈ S, s • x ∈ L}
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
  smul_mem' := by
    rintro r x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact L.smul_mem r hx

def localization₂ {W : Type*} [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime] (L : Submodule R W) :
    Submodule R W :=
  locS p.primeCompl L

def locLen (p : Ideal R) [p.IsPrime] (A B : Submodule R V) : ℕ :=
  (Module.length R ((localization₂ p A) ⧸ (localization₂ p B).comap (localization₂ p A).subtype)).toNat

def lidx (p : Ideal R) [p.IsPrime] (A B : Submodule R V) : ℤ :=
  (locLen p A (A ⊓ B) : ℤ) - locLen p B (A ⊓ B)

end Defs

variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def dualInH (h : V →ₗ⋆[E] V →ₗ[E] E) (M : Submodule (𝓞 E) V) : Submodule (𝓞 E) V :=
  hdual h M ⊓ (Submodule.span E (M : Set V)).restrictScalars (𝓞 E)

def genIdxH (A B : Submodule (𝓞 E) V) : ℝ :=
  ∏ᶠ P : HeightOneSpectrum (𝓞 E),
    ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (haveI := P.isPrime; lidx P.asIdeal A B)

def latDetH (h : V →ₗ⋆[E] V →ₗ[E] E) (M : Submodule (𝓞 E) V) : ℝ :=
  Real.sqrt (genIdxH (dualInH h M) M)

def pseudoSpan {ι : Type} [Fintype ι] (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : ι → V) :
    Submodule (𝓞 E) V :=
  ⨆ a, ((𝔞 a : Submodule (𝓞 E) E)).map ((LinearMap.toSpanSingleton E V (v a)).restrictScalars (𝓞 E))

end PI.IsoDetDefs

namespace PI

open NumberField PI.IsoDetDefs

def IsoDet : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E]
    (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E), h.IsSymm →
    ∀ (n : ℕ) (e e' : Fin n → V) (𝔞 : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
      (∀ a, 𝔞 a ≠ 0) →
      (∀ a b, h (e a) (e b) = 0) → (∀ a b, h (e' a) (e' b) = 0) →
      (Matrix.of fun a b => h (e a) (e' b)).det ≠ 0 →
      latDetH h (pseudoSpan 𝔞 e ⊔ pseudoSpan 𝔞 e') ≤
        |((Algebra.norm ℚ (Matrix.of fun a b => h (e a) (e' b)).det : ℚ) : ℝ)| *
          ∏ a, ((FractionalIdeal.absNorm (𝔞 a) : ℚ) : ℝ) ^ 2

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.IsoDualPair
section
noncomputable section

namespace PI.IsoDualPair

def ColChoice {Lt : Type} (N1 : ℕ) (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))

def colsOf {k : Type} [Zero k] {N : ℕ} (Y : Matrix (Fin N) (Fin N) k) : Fin N → ℕ → k :=
  fun a j => if h : j < N then Y a ⟨j, h⟩ else 0

abbrev LaC {Lt : Type} (N : ℕ) (nu : Lt → YoungDiagram) : Type := ColChoice N nu → ℂ

def hvC {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) (x : Lt → Fin N → ℕ → ℂ) : LaC N nu :=
  fun J => minY N nu J x

def Vnu {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) : Submodule ℂ (LaC N nu) :=
  Submodule.span ℂ (Set.range (hvC N nu))

def l2 {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ : LaC N nu) : ℝ := ∑ᶠ J, ‖φ J‖ ^ 2

def prC {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ ψ : LaC N nu) : ℂ := ∑ᶠ J, φ J * ψ J

def VnuMap {Lt : Type} [Fintype Lt] {N N' : ℕ} (nu : Lt → YoungDiagram) (f : Lt → Matrix (Fin N') (Fin N) ℂ)
    (φ : LaC N nu) : LaC N' nu :=
  fun I => ∑ᶠ J : ColChoice N nu, (∏ s, ∏ c : Fin ((nu s).rowLen 0),
    Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (J s c k))) * φ J

def IsoDualPair : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram),
    (∀ φ ∈ Vnu N nu, (∀ ψ ∈ Vnu N nu, ‖prC φ ψ‖ ^ 2 ≤ l2 φ * l2 ψ) ∧
      ∃ ψ ∈ Vnu N nu, l2 ψ = l2 φ ∧ prC φ ψ = (l2 φ : ℂ)) ∧
    ∀ Λ : Vnu N nu →ₗ[ℂ] ℂ, ∃ φ ∈ Vnu N nu, ∀ ψ : Vnu N nu, Λ ψ = prC φ (ψ : LaC N nu)

end PI.IsoDualPair
end
end

-- bundled from Formalism.PeriodIntegrals.IsoFunV
section
noncomputable section

namespace PI.IsoFunV

def ColChoice {Lt : Type} (N1 : ℕ) (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))

def colsOf {k : Type} [Zero k] {N : ℕ} (Y : Matrix (Fin N) (Fin N) k) : Fin N → ℕ → k :=
  fun a j => if h : j < N then Y a ⟨j, h⟩ else 0

abbrev LaC {Lt : Type} (N : ℕ) (nu : Lt → YoungDiagram) : Type := ColChoice N nu → ℂ

def hvC {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) (x : Lt → Fin N → ℕ → ℂ) : LaC N nu :=
  fun J => minY N nu J x

def Vnu {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) : Submodule ℂ (LaC N nu) :=
  Submodule.span ℂ (Set.range (hvC N nu))

def l2 {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ : LaC N nu) : ℝ := ∑ᶠ J, ‖φ J‖ ^ 2

def prC {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ ψ : LaC N nu) : ℂ := ∑ᶠ J, φ J * ψ J

def VnuMap {Lt : Type} [Fintype Lt] {N N' : ℕ} (nu : Lt → YoungDiagram) (f : Lt → Matrix (Fin N') (Fin N) ℂ)
    (φ : LaC N nu) : LaC N' nu :=
  fun I => ∑ᶠ J : ColChoice N nu, (∏ s, ∏ c : Fin ((nu s).rowLen 0),
    Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (J s c k))) * φ J

def canC {Lt : Type} [Fintype Lt] {N : ℕ} {nu : Lt → YoungDiagram} (φ : LaC N nu) (y : Lt → Fin N → ℕ → ℂ) : ℂ :=
  prC φ (hvC N nu y)

abbrev Idx (T : Type) (N N' : ℕ) : Type := T × Fin N' × Fin N

abbrev FrV (T : Type) (N : ℕ) : Type := T × Fin N × Fin N

abbrev VC (T : Type) (N N' : ℕ) : Type := T → Fin N' → Fin N → ℂ

abbrev Mono (T : Type) (N N' : ℕ) : Type := (T × Fin N' × Fin N) →₀ ℕ

open Classical in

def coordV {T : Type} {N N' : ℕ} (k : T × Fin N' × Fin N) : VC T N N' :=
  fun τ i j => if τ = k.1 ∧ i = k.2.1 ∧ j = k.2.2 then 1 else 0

def taylor {T : Type} [Fintype T] {N N' : ℕ} (G : VC T N N' → ℂ) (α : Mono T N N') : ℂ :=
  iteratedFDeriv ℂ (Multiset.card α.toMultiset) G 0
      (fun i => coordV (α.toMultiset.toList.get ⟨i, by simpa using i.2⟩)) /
    (α.prod fun _ n => (n.factorial : ℂ))

def applyAt0 {T : Type} [Fintype T] {N N' : ℕ} (P : MvPolynomial (Idx T N N') ℂ) (G : VC T N N' → ℂ) : ℂ :=
  ∑ α ∈ P.support, MvPolynomial.coeff α P * (α.prod fun _ n => (n.factorial : ℂ)) * taylor G α

def evFr {T : Type} {N : ℕ} (Q : MvPolynomial (FrV T N) ℂ) (y : T → Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  MvPolynomial.eval (fun k : FrV T N => y k.1 k.2.1 k.2.2) Q

def polD {T : Type} {N N' : ℕ} (s : T → ℂ) (Q : MvPolynomial (FrV T N) ℂ)
    (y' : T → Matrix (Fin N') (Fin N') ℂ) : MvPolynomial (Idx T N N') ℂ :=
  MvPolynomial.aeval (fun k : FrV T N => ∑ b : Fin N',
    MvPolynomial.C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
      MvPolynomial.X ((k.1, b, k.2.1) : Idx T N N')) Q

def PIJ {Lt T : Type} [Fintype Lt] (tp : Lt → T) {N N' : ℕ} (nu : Lt → YoungDiagram) (s : T → ℂ) (I : ColChoice N' nu)
    (J : ColChoice N nu) : MvPolynomial (Idx T N N') ℂ :=
  ∏ z, ∏ c : Fin ((nu z).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu z).colLen c) =>
    MvPolynomial.C (s (tp z)) * MvPolynomial.X ((tp z, I z c i, J z c k) : Idx T N N'))

def AOp {Lt T : Type} [Fintype Lt] [Fintype T] (tp : Lt → T) {N N' : ℕ} (nu : Lt → YoungDiagram) (s : T → ℂ) (Θ : VC T N N' → ℂ)
    (φ : LaC N nu) : LaC N' nu :=
  fun I => ∑ᶠ J : ColChoice N nu, applyAt0 (PIJ tp nu s I J) Θ * φ J

abbrev frC {Lt T : Type} (tp : Lt → T) {N : ℕ} (y : T → Matrix (Fin N) (Fin N) ℂ) : Lt → Fin N → ℕ → ℂ :=
  fun z => colsOf (y (tp z))

def IsoFunV : Prop :=
  ∀ (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (tp : Lt → T) (N N' : ℕ) (nu : Lt → YoungDiagram) (s : T → ℂ) (Θ : VC T N N' → ℂ),
    ∀ φ ∈ Vnu N nu, AOp tp nu s Θ φ ∈ Vnu N' nu

end PI.IsoFunV
end
end

-- bundled from Formalism.PeriodIntegrals.IsoInvMetric
section
noncomputable section

namespace PI.IsoInvMetric

def ColChoice {Lt : Type} (N1 : ℕ) (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))

def colsOf {k : Type} [Zero k] {N : ℕ} (Y : Matrix (Fin N) (Fin N) k) : Fin N → ℕ → k :=
  fun a j => if h : j < N then Y a ⟨j, h⟩ else 0

abbrev LaC {Lt : Type} (N : ℕ) (nu : Lt → YoungDiagram) : Type := ColChoice N nu → ℂ

def hvC {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) (x : Lt → Fin N → ℕ → ℂ) : LaC N nu :=
  fun J => minY N nu J x

def Vnu {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) : Submodule ℂ (LaC N nu) :=
  Submodule.span ℂ (Set.range (hvC N nu))

def l2 {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ : LaC N nu) : ℝ := ∑ᶠ J, ‖φ J‖ ^ 2

def prC {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ ψ : LaC N nu) : ℂ := ∑ᶠ J, φ J * ψ J

def VnuMap {Lt : Type} [Fintype Lt] {N N' : ℕ} (nu : Lt → YoungDiagram) (f : Lt → Matrix (Fin N') (Fin N) ℂ)
    (φ : LaC N nu) : LaC N' nu :=
  fun I => ∑ᶠ J : ColChoice N nu, (∏ s, ∏ c : Fin ((nu s).rowLen 0),
    Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (J s c k))) * φ J

def IsoInvMetric : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram),
    (∀ k : Lt → Matrix (Fin N) (Fin N) ℂ, (∀ z, k z ∈ Matrix.unitaryGroup (Fin N) ℂ) →
      (∀ φ ∈ Vnu N nu, VnuMap nu k φ ∈ Vnu N nu ∧ l2 (VnuMap nu k φ) = l2 φ) ∧
      ((∀ z, (nu z).colLen 0 ≤ N) → l2 (hvC N nu fun z => colsOf (k z)) = 1)) ∧
    ∀ ip : LaC N nu →ₗ⋆[ℂ] LaC N nu →ₗ[ℂ] ℂ,
      (∀ k : Lt → Matrix (Fin N) (Fin N) ℂ, (∀ z, k z ∈ Matrix.unitaryGroup (Fin N) ℂ) →
        (∀ φ ∈ Vnu N nu, ∀ ψ ∈ Vnu N nu, ip (VnuMap nu k φ) (VnuMap nu k ψ) = ip φ ψ) ∧
        ip (hvC N nu fun z => colsOf (k z)) (hvC N nu fun z => colsOf (k z)) = 1) →
      ∀ φ ∈ Vnu N nu, ip φ φ = (l2 φ : ℂ)

end PI.IsoInvMetric
end
end

-- bundled from Formalism.PeriodIntegrals.IsoScaleA
section
noncomputable section

namespace PI.IsoScaleA

def ColChoice {Lt : Type} (N1 : ℕ) (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))

def colsOf {k : Type} [Zero k] {N : ℕ} (Y : Matrix (Fin N) (Fin N) k) : Fin N → ℕ → k :=
  fun a j => if h : j < N then Y a ⟨j, h⟩ else 0

abbrev LaC {Lt : Type} (N : ℕ) (nu : Lt → YoungDiagram) : Type := ColChoice N nu → ℂ

def hvC {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) (x : Lt → Fin N → ℕ → ℂ) : LaC N nu :=
  fun J => minY N nu J x

def Vnu {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) : Submodule ℂ (LaC N nu) :=
  Submodule.span ℂ (Set.range (hvC N nu))

def l2 {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ : LaC N nu) : ℝ := ∑ᶠ J, ‖φ J‖ ^ 2

def prC {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ ψ : LaC N nu) : ℂ := ∑ᶠ J, φ J * ψ J

def VnuMap {Lt : Type} [Fintype Lt] {N N' : ℕ} (nu : Lt → YoungDiagram) (f : Lt → Matrix (Fin N') (Fin N) ℂ)
    (φ : LaC N nu) : LaC N' nu :=
  fun I => ∑ᶠ J : ColChoice N nu, (∏ s, ∏ c : Fin ((nu s).rowLen 0),
    Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (J s c k))) * φ J

def canC {Lt : Type} [Fintype Lt] {N : ℕ} {nu : Lt → YoungDiagram} (φ : LaC N nu) (y : Lt → Fin N → ℕ → ℂ) : ℂ :=
  prC φ (hvC N nu y)

abbrev Idx (T : Type) (N N' : ℕ) : Type := T × Fin N' × Fin N

abbrev FrV (T : Type) (N : ℕ) : Type := T × Fin N × Fin N

abbrev VC (T : Type) (N N' : ℕ) : Type := T → Fin N' → Fin N → ℂ

abbrev Mono (T : Type) (N N' : ℕ) : Type := (T × Fin N' × Fin N) →₀ ℕ

open Classical in

def coordV {T : Type} {N N' : ℕ} (k : T × Fin N' × Fin N) : VC T N N' :=
  fun τ i j => if τ = k.1 ∧ i = k.2.1 ∧ j = k.2.2 then 1 else 0

def taylor {T : Type} [Fintype T] {N N' : ℕ} (G : VC T N N' → ℂ) (α : Mono T N N') : ℂ :=
  iteratedFDeriv ℂ (Multiset.card α.toMultiset) G 0
      (fun i => coordV (α.toMultiset.toList.get ⟨i, by simpa using i.2⟩)) /
    (α.prod fun _ n => (n.factorial : ℂ))

def applyAt0 {T : Type} [Fintype T] {N N' : ℕ} (P : MvPolynomial (Idx T N N') ℂ) (G : VC T N N' → ℂ) : ℂ :=
  ∑ α ∈ P.support, MvPolynomial.coeff α P * (α.prod fun _ n => (n.factorial : ℂ)) * taylor G α

def evFr {T : Type} {N : ℕ} (Q : MvPolynomial (FrV T N) ℂ) (y : T → Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  MvPolynomial.eval (fun k : FrV T N => y k.1 k.2.1 k.2.2) Q

def polD {T : Type} {N N' : ℕ} (s : T → ℂ) (Q : MvPolynomial (FrV T N) ℂ)
    (y' : T → Matrix (Fin N') (Fin N') ℂ) : MvPolynomial (Idx T N N') ℂ :=
  MvPolynomial.aeval (fun k : FrV T N => ∑ b : Fin N',
    MvPolynomial.C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
      MvPolynomial.X ((k.1, b, k.2.1) : Idx T N N')) Q

def PIJ {Lt T : Type} [Fintype Lt] (tp : Lt → T) {N N' : ℕ} (nu : Lt → YoungDiagram) (s : T → ℂ) (I : ColChoice N' nu)
    (J : ColChoice N nu) : MvPolynomial (Idx T N N') ℂ :=
  ∏ z, ∏ c : Fin ((nu z).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu z).colLen c) =>
    MvPolynomial.C (s (tp z)) * MvPolynomial.X ((tp z, I z c i, J z c k) : Idx T N N'))

def AOp {Lt T : Type} [Fintype Lt] [Fintype T] (tp : Lt → T) {N N' : ℕ} (nu : Lt → YoungDiagram) (s : T → ℂ) (Θ : VC T N N' → ℂ)
    (φ : LaC N nu) : LaC N' nu :=
  fun I => ∑ᶠ J : ColChoice N nu, applyAt0 (PIJ tp nu s I J) Θ * φ J

abbrev frC {Lt T : Type} (tp : Lt → T) {N : ℕ} (y : T → Matrix (Fin N) (Fin N) ℂ) : Lt → Fin N → ℕ → ℂ :=
  fun z => colsOf (y (tp z))

def IsoScaleA : Prop :=
  ∀ (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (tp : Lt → T) (N N' : ℕ) (nu : Lt → YoungDiagram) (c s : T → ℂ) (Θ : VC T N N' → ℂ) (φ : LaC N nu),
    AOp tp nu (fun τ => c τ * s τ) Θ φ = (∏ z : Lt, c (tp z) ^ (nu z).card) • AOp tp nu s Θ φ

end PI.IsoScaleA
end
end

-- bundled from Formalism.PeriodIntegrals.KerLat
section
noncomputable section
open NumberField

namespace PI.KerLat

def PerPair : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Module.finrank ℚ K = 2 → (∃ k : K, (φ k).im ≠ 0) → cc ≠ ⊥ → δ ≠ 0 →
      ∃ L : PeriodPair, L.lattice.toAddSubgroup = AddSubgroup.closure {w : ℂ | ∃ c ∈ cc, w = δ * φ (c : K)}

def ExistsTwoTorsionOffKernels : Prop :=
  ∀ (L : PeriodPair) (d : ℕ), d % 8 = 7 →
    (∀ w ∈ L.lattice, ((1 + Complex.I * (Real.sqrt d : ℂ)) / 2) * w ∈ L.lattice) →
      ∃ t : ℂ, 2 * t ∈ L.lattice ∧ ((1 + Complex.I * (Real.sqrt d : ℂ)) / 2) * t ∉ L.lattice ∧
        ((1 - Complex.I * (Real.sqrt d : ℂ)) / 2) * t ∉ L.lattice

end PI.KerLat
end
end

-- bundled from Formalism.PeriodIntegrals.KoszulExact
section
noncomputable section

namespace PI.KoszulExact

def form {R : Type*} [CommRing R] {D : ℕ} (s : Fin D → R) : Module.Dual R (Fin D → R) :=
  ∑ i, s i • (LinearMap.proj i : (Fin D → R) →ₗ[R] R)

def dK {R : Type*} [CommRing R] {D : ℕ} (s : Fin D → R) :
    ExteriorAlgebra R (Fin D → R) →ₗ[R] ExteriorAlgebra R (Fin D → R) :=
  CliffordAlgebra.contractLeft (form s)

end PI.KoszulExact

namespace PI

def KoszulExact.{u} : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s) →
      (∀ (j : ℕ) (x : ExteriorAlgebra R (Fin D → R)), x ∈ ⋀[R]^(j + 1) (Fin D → R) →
          KoszulExact.dK s x = 0 → ∃ y ∈ ⋀[R]^(j + 2) (Fin D → R), KoszulExact.dK s y = x) ∧
      (∀ r : R, (∃ y ∈ ⋀[R]^1 (Fin D → R), KoszulExact.dK s y = algebraMap R _ r) ↔
          r ∈ Ideal.span (Set.range s))

end PI
end
end

