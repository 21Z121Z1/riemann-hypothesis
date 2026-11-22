import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub
import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DI

section Cochain

variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

def delta (c : Finset ι → E) : Finset ι → E :=
  fun t => ∑ i ∈ t, cubeSign t i • c (t.erase i)

def Dtot (d : E →+ E) (c : Finset ι → E) : Finset ι → E :=
  fun t => delta c t + (-1 : ℤ) ^ t.card • d (c t)

omit [LinearOrder ι] in

def InCech (N : Finset ι → AddSubgroup E) (m : ℕ) (c : Finset ι → E) : Prop :=
  c ∅ = 0 ∧ (∀ s, c s ∈ N s) ∧ ∀ s, s.card ≠ m → c s = 0

def CechZero (N : Finset ι → AddSubgroup E) (b : ℕ) : Prop :=
  ∀ c, InCech N (b + 1) c → delta c = 0 → ∃ y, InCech N b y ∧ delta y = c

omit [LinearOrder ι] in

def InTot (T : ℕ → Finset ι → AddSubgroup E) (m : ℕ) (c : Finset ι → E) : Prop :=
  c ∅ = 0 ∧ (∀ q s, q + s.card = m → c s ∈ T q s) ∧ ∀ s, m < s.card → c s = 0

def HypZero (d : E →+ E) (T : ℕ → Finset ι → AddSubgroup E) (n : ℕ) : Prop :=
  ∀ c, InTot T (n + 1) c → Dtot d c = 0 → ∃ y, InTot T n y ∧ Dtot d y = c

structure CartierAt (d : E →+ E) (γ : E → E) (N T : ℕ → AddSubgroup E) : Prop where
  inj_zero : ∀ x ∈ N 0, γ x = 0 → x = 0
  inj_succ : ∀ a, ∀ x ∈ N (a + 1), ∀ z ∈ T a, γ x = d z → x = 0
  surj_zero : ∀ y ∈ T 0, d y = 0 → ∃ x ∈ N 0, y = γ x
  surj_succ : ∀ a, ∀ y ∈ T (a + 1), d y = 0 → ∃ x ∈ N (a + 1), ∃ z ∈ T a, y = γ x + d z

def cup (Φ : E → Finset ι → E) (c : Finset ι → E) : Finset ι → E :=
  fun u => ∑ j ∈ u, Φ (c (u.filter (· ≤ j))) (u.filter (j ≤ ·))

end Cochain

section Forms

variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]

structure IsOddDer (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) : Prop where
  mul : ∀ x y, d (x * y) = d x * y + CliffordAlgebra.involute x * d y
  sq : ∀ x, d (d x) = 0

structure IsExtD (k K : Type) [CommRing k] [CommRing K] [Algebra k K]
    (d : ExteriorAlgebra K Ω[K⁄k] →+ ExteriorAlgebra K Ω[K⁄k]) : Prop extends IsOddDer d where
  alg : ∀ a : K, d (algebraMap K _ a) = ExteriorAlgebra.ι K (KaehlerDifferential.D k K a)

def forms (B : Set K) (L : Set V) (q : ℕ) : AddSubgroup (ExteriorAlgebra K V) :=
  AddSubgroup.closure {x | ∃ b ∈ B, ∃ v : Fin q → V, (∀ k, v k ∈ L) ∧ x = b • ExteriorAlgebra.ιMulti K q v}

variable {ι : Type} [LinearOrder ι]

omit [LinearOrder ι] in

structure IsDatum (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V)
    (h : ι → ι → V →+ K) : Prop where
  f_smul : ∀ i (c : K) v, f i (c • v) = c ^ p • f i v
  h_smul : ∀ i j (c : K) v, h i j (c • v) = c ^ p * h i j v
  closed : ∀ i v, d (ExteriorAlgebra.ι K (f i v)) = 0
  dh : ∀ i j v, d (algebraMap K _ (h i j v)) = ExteriorAlgebra.ι K (f j v) - ExteriorAlgebra.ι K (f i v)
  cocycle : ∀ i j l v, h i j v + h j l v = h i l v

def Lop (f : ι → V →+ V) (h : ι → ι → V →+ K) (v : V) (y : Finset ι → ExteriorAlgebra K V) :
    Finset ι → ExteriorAlgebra K V := fun t =>
  if ht : t.Nonempty then
    (-1 : ℤ) ^ t.card • (ExteriorAlgebra.ι K (f (t.min' ht) v) * y t) +
      (if h2 : (t.erase (t.min' ht)).Nonempty then
        h (t.min' ht) ((t.erase (t.min' ht)).min' h2) v • y (t.erase (t.min' ht)) else 0)
  else 0

omit [LinearOrder ι] in

def oneC : Finset ι → ExteriorAlgebra K V := fun t => if t.card = 1 then 1 else 0

def prodL (f : ι → V →+ V) (h : ι → ι → V →+ K) (vs : List V) : Finset ι → ExteriorAlgebra K V :=
  vs.foldr (Lop f h) oneC

def alt (f : ι → V →+ V) (h : ι → ι → V →+ K) (a : ℕ) (v : Fin a → V) : Finset ι → ExteriorAlgebra K V :=
  ∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • prodL f h (List.ofFn (v ∘ σ))

def IsPhi (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K)
    (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) : Prop :=
  ∀ (c : K) (a : ℕ) (v : Fin a → V), Φ (c • ExteriorAlgebra.ιMulti K a v) = c ^ p • alt f h a v

def IsGamma (p : ℕ) (f : V →+ V) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V) : Prop :=
  (∀ c : K, γ (algebraMap K _ c) = algebraMap K _ (c ^ p)) ∧
    ∀ v, γ (ExteriorAlgebra.ι K v) = ExteriorAlgebra.ι K (f v)

end Forms

section Lift

variable {K Kt : Type} [CommRing K] [CommRing Kt]

structure IsFlatLift (p : ℕ) (π : Kt →+* K) : Prop where
  surj : Function.Surjective π
  ker : ∀ z, π z = 0 ↔ ∃ w, z = p * w
  ann : ∀ w, (p : Kt) * w = 0 ↔ π w = 0

def IsFrob (p : ℕ) (π : Kt →+* K) (F : Kt →+* Kt) : Prop := ∀ z, π (F z) = π z ^ p

def IsF (p : ℕ) (π : Kt →+* K) (F : Kt →+* Kt) (f : Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) : Prop :=
  (∀ (c : K) v, f (c • v) = c ^ p • f v) ∧ ∀ z w : Kt, F z = z ^ p + p * w →
    f (KaehlerDifferential.D ℤ K (π z)) =
      π z ^ (p - 1) • KaehlerDifferential.D ℤ K (π z) + KaehlerDifferential.D ℤ K (π w)

def IsH (p : ℕ) (π : Kt →+* K) (F F' : Kt →+* Kt) (h : Ω[K⁄ℤ] →+ K) : Prop :=
  (∀ (c : K) v, h (c • v) = c ^ p * h v) ∧ ∀ z w : Kt, F' z = F z + p * w →
    h (KaehlerDifferential.D ℤ K (π z)) = π w

def LogLift {ι : Type} (p : ℕ) (π : Kt →+* K) (F : ι → Kt →+* Kt) (s : Finset ι) (A : Set K) (g : K) : Prop :=
  ∃ z, π z = g ∧ ∀ i ∈ s, ∃ w, π w ∈ A ∧ F i z = z ^ p * (1 + p * w)

end Lift

end GlobalTheory.DI
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
section
noncomputable section

namespace GlobalTheory.UCls

open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def IsUA (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  IsUnit g.det ∧ ∀ x y, hermA c G (g *ᵥ x) (g *ᵥ y) = hermA c G x y

def IsKM (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    (k : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  IsUA c G k ∧ (∀ x ∈ hat F L, ∃ y ∈ hat F L, k *ᵥ x - x = M • y) ∧ ∀ x ∈ hat F L, ∃ y ∈ hat F L, k *ᵥ y = x

def ratM (F : Type) [Field F] [NumberField F] [Algebra F E] (γ : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin n) (Fin n) (RA F E) :=
  γ.map fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ x

def UEquiv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    (g g' : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∃ γ : Matrix (Fin n) (Fin n) E, IsUA c G (ratM F γ) ∧ ∃ k, IsKM c G L M k ∧ g' = ratM F γ * g * k

def classNo (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) : ℕ∞ :=
  ENat.card (Quot fun a b : {g // IsUA c G g} => UEquiv c G L M a.1 b.1)

def IsTA (c : E ≃ₐ[F] E) (t : RA F E) : Prop := t * sg (FiniteAdeleRing (𝓞 F) F) c t = 1

def TEquiv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) (t t' : RA F E) : Prop :=
  ∃ u : E, u * c u = 1 ∧ ∃ k, IsKM c G L M k ∧ t' = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ u) * t * k.det

def torusNo (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) : ℕ∞ :=
  ENat.card (Quot fun a b : {t // IsTA c t} => TEquiv c G L M a.1 b.1)

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in

theorem _root_.GlobalTheory.UCls.isKM_one (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (L : Set (Fin n → E)) (M : ℕ) :
    _root_.GlobalTheory.UCls.IsKM c G L M 1 := by
  refine ⟨⟨by simp, fun x y => by simp only [one_mulVec]⟩, fun x _ => ⟨0, ?_, ?_⟩,
    fun x hx => ⟨x, hx, one_mulVec x⟩⟩
  · exact (_root_.GlobalTheory.AdLat.hat F L).zero_mem
  · simp

end GlobalTheory.UCls
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MemShaKernelIffLocallyTrivial
section
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LKTorus

section Functoriality

variable {k k' k'' : Type} [Field k] [Field k'] [Field k'']
  {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra k A] [Algebra k' A'] [Algebra k'' A'']

def fixMap (c : A →ₐ[k] A) (c' : A' →ₐ[k'] A') (φ : A →+* A') (hc : ∀ a, φ (c a) = c' (φ a)) :
    fixU k c →* fixU k' c' where
  toFun a := ⟨Units.map φ.toMonoidHom a, by
    have h : c (a : Aˣ) = ((a : Aˣ) : A) := a.2
    show c' (φ ((a : Aˣ) : A)) = φ ((a : Aˣ) : A)
    rw [← hc, h]⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

@[simp] theorem fixMap_apply (c : A →ₐ[k] A) (c' : A' →ₐ[k'] A') (φ : A →+* A') (hc : ∀ a, φ (c a) = c' (φ a))
    (a : fixU k c) : (((fixMap c c' φ hc a : fixU k' c') : A'ˣ) : A') = φ ((a : Aˣ) : A) := rfl

def H1map (c : A →ₐ[k] A) (c' : A' →ₐ[k'] A') (ι : k →+* k') (φ : A →+* A') (hc : ∀ a, φ (c a) = c' (φ a))
    (hι : ∀ t : k, φ (algebraMap k A t) = algebraMap k' A' (ι t)) : H1 k c →* H1 k' c' :=
  QuotientGroup.map _ _ (fixMap c c' φ hc) (by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro a ⟨t, x, hx⟩
    refine Subgroup.subset_closure ⟨Units.map ι.toMonoidHom t, Units.map φ.toMonoidHom x, ?_⟩
    show φ ((a : Aˣ) : A) = _
    rw [hx, map_mul, map_mul, hι, hc]
    rfl)

end Functoriality

section Localisation

def locInv (S : Type) [Field S] [CharZero S] {L : Type} [CommRing L] [Algebra ℚ L] (c : L →ₐ[ℚ] L) :
    (S ⊗[ℚ] L) →ₐ[S] (S ⊗[ℚ] L) :=
  Algebra.TensorProduct.map (AlgHom.id S S) c

@[simp] theorem locInv_tmul (S : Type) [Field S] [CharZero S] {L : Type} [CommRing L] [Algebra ℚ L]
    (c : L →ₐ[ℚ] L) (s : S) (x : L) : locInv S c (s ⊗ₜ x) = s ⊗ₜ c x := rfl

def CohomologyLocalisation (S : Type) [Field S] [CharZero S] {L : Type} [CommRing L] [Algebra ℚ L] (c : L →ₐ[ℚ] L) :
    H1 ℚ c →* H1 S (locInv S c) :=
  H1map c (locInv S c) (algebraMap ℚ S) (Algebra.TensorProduct.includeRight.toRingHom)
    (fun a => by simp [locInv])
    (fun t => by
      show (1 : S) ⊗ₜ[ℚ] algebraMap ℚ L t = algebraMap ℚ S t ⊗ₜ[ℚ] (1 : L)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])

def ker1 {L : Type} [CommRing L] [Algebra ℚ L] (c : L →ₐ[ℚ] L) : Subgroup (H1 ℚ c) :=
  (CohomologyLocalisation ℝ c).ker ⊓ ⨅ (ℓ : Nat.Primes), (haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩; (CohomologyLocalisation ℚ_[(ℓ : ℕ)] c).ker)

end Localisation

example : Subgroup (H1 ℚ (AlgHom.id ℚ (ℚ × ℚ))) := ker1 (AlgHom.id ℚ (ℚ × ℚ))

example {L : Type} [CommRing L] [Algebra ℚ L] (c : L →ₐ[ℚ] L) : (1 : H1 ℚ c) ∈ ker1 c := (ker1 c).one_mem

example (a : fixU ℚ (AlgHom.id ℚ ℚ)) :
    fixMap (AlgHom.id ℚ ℚ) (AlgHom.id ℚ ℚ) (RingHom.id ℚ) (fun _ => rfl) a = a := by
  ext; rfl

end GlobalTheory.LKTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
section
set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField

namespace GlobalTheory.ChowHt

structure IsChowForm {k : Type} [Field k] {N : ℕ} (I : Ideal (MvPolynomial (Fin N) k)) (D δ : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) k) : Prop where

  homog : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => δ) f

  irred : Irreducible (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f)

  zero_iff : ∀ u : Fin (D + 1) × Fin N → AlgebraicClosure k, MvPolynomial.aeval u f = 0 ↔
    ∃ y : Fin N → AlgebraicClosure k, y ≠ 0 ∧ (∀ g ∈ I, MvPolynomial.aeval y g = 0) ∧
      ∀ i, ∑ j, u (i, j) * y j = 0

def linSubst {R : Type} [CommRing R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (f : MvPolynomial (Fin B × Fin N) R) : MvPolynomial (Fin B × Fin n) R :=
  MvPolynomial.aeval (fun p : Fin B × Fin N => ∑ k, C (M p.2 k) * X (p.1, k)) f

def frameNorm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖(A⁻¹.mulVec x) i‖ ^ 2)

def formHeight {F : Type} [Field F] [NumberField F] {B N n : ℕ} (δ : ℕ)
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin B × Fin N) F) : ℝ :=
  ((∑ᶠ v : FinitePlace F, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v (linSubst w f))) +
    ∑ σ : F →+* ℂ, (ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ f)) +
      (B : ℝ) * δ * (harmonic (N - 1) : ℝ) / 2)) / (Module.finrank ℚ F : ℝ)

def pointHeight {F : Type} [Field F] [NumberField F] {N n : ℕ}
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    {K : Type} [Field K] [NumberField K] [Algebra F K] (y : Fin N → K) : ℝ :=
  ((∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (∑ j, algebraMap F K (w j k) * y j))) +
    ∑ τ : K →+* ℂ, Real.log (Real.sqrt
      (∑ i, ‖∑ j, A (τ.comp (algebraMap F K)) j i * τ (y j)‖ ^ 2))) / (Module.finrank ℚ K : ℝ)

def ConjCompat {F : Type} [Field F] {N : ℕ} (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ (σ : F →+* ℂ) (x : Fin N → ℂ),
    frameNorm (A ((starRingEnd ℂ).comp σ)) (fun j => (starRingEnd ℂ) (x j)) = frameNorm (A σ) x

end GlobalTheory.ChowHt
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SubsingletonComplex
section
noncomputable section

namespace GlobalTheory.LKTorus.Model

open Complex

def conjC : ℂ →ₐ[ℝ] ℂ := (Complex.conjAe : ℂ →ₐ[ℝ] ℂ)

def conjCC : (ℂ × ℂ) →ₐ[ℝ] (ℂ × ℂ) := AlgHom.prodMap conjC conjC

theorem conjC_apply (z : ℂ) : conjC z = (starRingEnd ℂ) z := rfl

theorem conjCC_apply (z : ℂ × ℂ) : conjCC z = ((starRingEnd ℂ) z.1, (starRingEnd ℂ) z.2) := rfl

theorem conjCC_invol (z : ℂ × ℂ) : conjCC (conjCC z) = z := by
  simp [conjCC_apply]

theorem mem_normSub_iff {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A] (c : A →ₐ[k] A)
    (a : fixU k c) :
    a ∈ normSub k c ↔ ∃ (t : kˣ) (x : Aˣ), ((a : Aˣ) : A) = algebraMap k A t * (x * c x) := by
  constructor
  · intro h
    induction h using Subgroup.closure_induction with
    | mem a ha => exact ha
    | one => exact ⟨1, 1, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨s, x, hs⟩ := ha
      obtain ⟨t, y, ht⟩ := hb
      refine ⟨s * t, x * y, ?_⟩
      simp only [Subgroup.coe_mul, Units.val_mul, map_mul, hs, ht]
      ring
    | inv a _ ha =>
      obtain ⟨s, x, hs⟩ := ha
      refine ⟨s⁻¹, x⁻¹, ?_⟩
      have h1 : ((a : Aˣ) : A) * (algebraMap k A ((s⁻¹ : kˣ) : k) * (((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A))) = 1 := by
        rw [hs]
        calc _ = (algebraMap k A (s : k) * algebraMap k A ((s⁻¹ : kˣ) : k)) * (((x : Aˣ) : A) * ((x⁻¹ : Aˣ) : A))
              * (c ((x : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A)) := by ring
          _ = 1 := by rw [← map_mul, ← map_mul]; simp
      rw [Subgroup.coe_inv]
      exact Units.inv_eq_of_mul_eq_one_right h1
  · intro h
    exact Subgroup.subset_closure h

theorem subsingleton_complex : Subsingleton (H1 ℝ conjC) := by
  have : normSub ℝ conjC = ⊤ := by
    rw [eq_top_iff]
    intro a _
    rw [mem_normSub_iff]
    have ha : (starRingEnd ℂ) ((a : ℂˣ) : ℂ) = ((a : ℂˣ) : ℂ) := a.2
    have hre : (((a : ℂˣ) : ℂ).re : ℂ) = ((a : ℂˣ) : ℂ) := Complex.conj_eq_iff_re.mp ha
    have hne : ((a : ℂˣ) : ℂ).re ≠ 0 := by
      intro h
      rw [h] at hre
      exact (a : ℂˣ).ne_zero (by simpa using hre.symm)
    exact ⟨Units.mk0 _ hne, 1, by simp [hre]⟩
  unfold H1
  rw [this]
  exact QuotientGroup.subsingleton_quotient_top

def u : (ℂ × ℂ)ˣ := ⟨(1, -1), (1, -1), by ext <;> simp, by ext <;> simp⟩

theorem u_mem : u ∈ fixU ℝ conjCC := by
  show conjCC ((1, -1) : ℂ × ℂ) = (1, -1)
  simp [conjCC_apply]

theorem u_not_mem : (⟨u, u_mem⟩ : fixU ℝ conjCC) ∉ normSub ℝ conjCC := by
  rw [mem_normSub_iff]
  rintro ⟨t, x, h⟩
  have h' : ((1, -1) : ℂ × ℂ) = algebraMap ℝ (ℂ × ℂ) t * (x * conjCC x) := h
  have h1 := congrArg (fun z : ℂ × ℂ => z.1.re) h'
  have h2 := congrArg (fun z : ℂ × ℂ => z.2.re) h'
  simp only [conjCC_apply, Prod.fst_mul, Prod.snd_mul, Complex.mul_conj, Prod.algebraMap_apply,
    Complex.coe_algebraMap, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.one_re, Complex.neg_re] at h1 h2
  have a := Complex.normSq_nonneg (x : ℂ × ℂ).1
  have b := Complex.normSq_nonneg (x : ℂ × ℂ).2
  rcases le_total 0 (t : ℝ) with ht | ht
  · nlinarith [mul_nonneg ht b]
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos ht (neg_nonpos.mpr a)]

theorem nontrivial_prod : Nontrivial (H1 ℝ conjCC) := by
  unfold H1
  exact ⟨⟨QuotientGroup.mk ⟨u, u_mem⟩, 1, fun h => u_not_mem ((QuotientGroup.eq_one_iff _).mp h)⟩⟩

theorem simT_ne_top : simT ℝ conjCC ≠ ⊤ := by
  intro h
  have hm : (⟨(1, 2), (1, 2⁻¹), by ext <;> simp, by ext <;> simp⟩ : (ℂ × ℂ)ˣ) ∈ simT ℝ conjCC := by
    rw [h]; trivial
  obtain ⟨t, ht⟩ := hm
  have h' : ((1, 2) : ℂ × ℂ) * conjCC (1, 2) = algebraMap ℝ (ℂ × ℂ) t := ht
  have h1 := congrArg (fun z : ℂ × ℂ => z.1.re) h'
  have h2 := congrArg (fun z : ℂ × ℂ => z.2.re) h'
  simp only [conjCC_apply, Prod.fst_mul, Prod.snd_mul, Complex.mul_conj, Prod.algebraMap_apply,
    Complex.coe_algebraMap, Complex.ofReal_re] at h1 h2
  simp [Complex.normSq_apply] at h1 h2
  linarith

end GlobalTheory.LKTorus.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix
open GlobalTheory.QFam

namespace GlobalTheory.WpFam

def pv (τ : ℍ) (x : Fin 2 → ℝ) : ℂ := (x 0 : ℂ) * τ + (x 1 : ℂ)

def eta (τ : ℍ) (x : Fin 2 → ℝ) : ℂ := EisensteinSeries.G2 τ * pv τ x - 2 * Real.pi * Complex.I * (x 0 : ℂ)

def G2s (τ : ℍ) : ℂ := EisensteinSeries.G2 τ - (Real.pi : ℂ) / (τ.im : ℂ)

def redR (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℝ := (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)

def redGL (N : ℕ) (γ : SL(2, ℤ)) : GL (Fin 2) (ZMod N) :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ)

def vmul {N : ℕ} (x : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)) : Fin 2 → ZMod N :=
  x ᵥ* (α : Matrix (Fin 2) (Fin 2) (ZMod N))

def vact (N : ℕ) (x : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : Fin 2 → ZMod N := vmul x (redGL N γ)

def gact (N : ℕ) (D : GL (Fin 2) (ZMod N)) (α : GL (Fin 2) (ZMod N)) (γ : SL(2, ℤ)) : GL (Fin 2) (ZMod N) :=
  α * (D * redGL N γ * D⁻¹)

def dg {N : ℕ} (a : (ZMod N)ˣ) : GL (Fin 2) (ZMod N) where
  val := !![1, 0; 0, (a : ZMod N)]
  inv := !![1, 0; 0, ((a⁻¹ : (ZMod N)ˣ) : ZMod N)]
  val_inv := by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp
  inv_val := by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp

def tors (N : ℕ) (τ : ℍ) (x : Fin 2 → ZMod N) : ℂ := (((x 0).val : ℂ) * τ + ((x 1).val : ℂ)) / N

def wp (N : ℕ) (x : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  (tauPair τ).weierstrassP (tors N τ x) / (2 * Real.pi * Complex.I) ^ 2

def wpd (N : ℕ) (x : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  (tauPair τ).derivWeierstrassP (tors N τ x) / (2 * Real.pi * Complex.I) ^ 3

def gN (τ : ℍ) : ℂ := EisensteinSeries.G2 τ / (2 * Real.pi * Complex.I) ^ 2

def wB (N : ℕ) (x : Fin 2 → ZMod N) (τ : ℍ) : ℂ := gN τ + wp N x τ

def ch (N : ℕ) (j : ZMod N) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / N)

def ZetaAct (g : ℂ ≃+* ℂ) (N : ℕ) (a : ZMod N) : Prop := ∀ j : ZMod N, g (ch N j) = ch N (a * j)

open Classical in

def cSum (N e : ℕ) (ε : ℂ) (x : Fin 2 → ZMod N) (k : ℕ) : ℂ :=
  ∑ m ∈ k.divisors, (m : ℂ) ^ e * ((if ((k / m : ℕ) : ZMod N) = x 0 then ch N ((m : ZMod N) * x 1) else 0) +
    ε * (if ((k / m : ℕ) : ZMod N) = -x 0 then ch N (-((m : ZMod N) * x 1)) else 0))

open Classical in

def cB (N : ℕ) (x : Fin 2 → ZMod N) (k : ℕ) : ℂ :=
  if k = 0 then (if x 0 = 0 then ch N (x 1) / (1 - ch N (x 1)) ^ 2 else 0) else cSum N 1 1 x k

open Classical in

def cD (N : ℕ) (x : Fin 2 → ZMod N) (k : ℕ) : ℂ :=
  if k = 0 then (if x 0 = 0 then ch N (x 1) * (1 + ch N (x 1)) / (1 - ch N (x 1)) ^ 3 else 0) else cSum N 2 (-1) x k

def cG (N : ℕ) (k : ℕ) : ℂ :=
  if k = 0 then -1 / 12 else if N ∣ k then 2 * (ArithmeticFunction.sigma 1 (k / N) : ℂ) else 0

open Classical in

def cP (N : ℕ) (x : Fin 2 → ZMod N) (k : ℕ) : ℂ := if x = 0 then 0 else cB N x k - cG N k

theorem wB_eq (N : ℕ) (x : Fin 2 → ZMod N) (τ : ℍ) :
    wB N x τ = (EisensteinSeries.G2 τ + (tauPair τ).weierstrassP (tors N τ x)) / (2 * Real.pi * Complex.I) ^ 2 := by
  rw [wB, gN, wp, add_div]

theorem gact_one (N : ℕ) (α : GL (Fin 2) (ZMod N)) (γ : SL(2, ℤ)) : gact N 1 α γ = α * redGL N γ := by
  simp [gact]

end GlobalTheory.WpFam
end
end

