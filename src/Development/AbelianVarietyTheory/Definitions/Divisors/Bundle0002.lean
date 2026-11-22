import Mathlib

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups ModularForm

namespace GlobalTheory.QFam

def HasQ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) (f τ)

def IsFam {ι : Type} (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ) : Prop :=
  ∀ (i : ι) (γ : SL(2, ℤ)), (f i) ∣[w] γ = f (act i γ)

def IsRAct {ι : Type} (act : ι → SL(2, ℤ) → ι) : Prop :=
  (∀ i, act i 1 = i) ∧ ∀ i γ δ, act (act i γ) δ = act i (γ * δ)

def ActBij {ι : Type} (act : ι → SL(2, ℤ) → ι) : Prop :=
  ∀ γ, Function.Bijective fun i => act i γ

def FamQ {ι : Type} (act : ι → SL(2, ℤ) → ι) (w : ℤ) (N : ℕ) (f : ι → ℍ → ℂ) (a : ι → ℕ → ℂ) : Prop :=
  IsFam act w f ∧ ∀ i, HasQ N (f i) (a i)

def conv (a b : ℕ → ℂ) (n : ℕ) : ℂ := ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2

def spread (M : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ := if M ∣ n then a (n / M) else 0

def QAll (p : ℂ → Prop) (N : ℕ) (f : ℍ → ℂ) : Prop := ∃ a, HasQ N f a ∧ ∀ n, p (a n)

def QConj (g : ℂ ≃+* ℂ) (N : ℕ) (f f' : ℍ → ℂ) : Prop := ∃ a, HasQ N f a ∧ HasQ N f' fun n => g (a n)

def tauPair (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    have hs : s = 0 := by
      have : s * τ.im = 0 := by simpa using him
      exact (mul_eq_zero.mp this).resolve_right τ.im_pos.ne'
    subst hs
    exact ⟨rfl, by simpa using hre⟩

theorem IsRAct.actBij {ι : Type} {act : ι → SL(2, ℤ) → ι} (h : IsRAct act) : ActBij act := by
  obtain ⟨hone, hmul⟩ := h
  intro γ
  refine Function.bijective_iff_has_inverse.mpr ⟨fun i => act i γ⁻¹, fun i => ?_, fun i => ?_⟩
  · show act (act i γ) γ⁻¹ = i
    rw [hmul, mul_inv_cancel, hone]
  · show act (act i γ⁻¹) γ = i
    rw [hmul, inv_mul_cancel, hone]

theorem hasQ_iff (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) :
    HasQ N f a ↔ ∀ τ : ℍ, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ n) (f τ) := by
  have key : ∀ (τ : ℍ) (n : ℕ), Complex.exp (2 * Real.pi * Complex.I * n * τ / N)
      = Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ n := by
    intro τ n
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  simp only [HasQ, key]

end GlobalTheory.QFam
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsSimplicial
section
set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.Shintani

def openCone {W : Type} [AddCommGroup W] [Module ℚ W] (s : Finset W) : Set W :=
  {x | ∃ t : W → ℚ, (∀ v ∈ s, 0 < t v) ∧ x = ∑ v ∈ s, t v • v}

def IsSimplicial {W : Type} [AddCommGroup W] [Module ℚ W] (P : Set W) (s : Finset W) : Prop :=
  s.Nonempty ∧ LinearIndepOn ℚ id (s : Set W) ∧ (s : Set W) ⊆ P

def coneFuns {W : Type} [AddCommGroup W] [Module ℚ W] (P : Set W) : Submodule ℚ (W → ℚ) :=
  Submodule.span ℚ {f | ∃ s : Finset W, IsSimplicial P s ∧ f = (openCone s).indicator 1}

def IsPosCone {W : Type} [AddCommGroup W] [Module ℚ W] (P : Set W) : Prop :=
  ∀ u ∈ P, ∀ v ∈ P, ∀ a b : ℚ, 0 < a → 0 < b → a • u + b • v ∈ P

def totPos (F : Type) [Field F] : Set F := {x | ∀ σ : F →+* ℝ, 0 < σ x}

def rayUnits {F : Type} [Field F] (𝔣 : Ideal (𝓞 F)) : Subgroup (𝓞 F)ˣ where
  carrier := {u | (u : 𝓞 F) - 1 ∈ 𝔣 ∧ ((u : 𝓞 F) : F) ∈ totPos F}
  one_mem' := ⟨by simp, fun σ => by simp⟩
  mul_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨?_, fun σ => ?_⟩
    · rw [show ((u * v : (𝓞 F)ˣ) : 𝓞 F) - 1 = (u : 𝓞 F) * ((v : 𝓞 F) - 1) + ((u : 𝓞 F) - 1) by push_cast; ring]
      exact 𝔣.add_mem (𝔣.mul_mem_left _ hv) hu
    · have e : (((u * v : (𝓞 F)ˣ) : 𝓞 F) : F) = ((u : 𝓞 F) : F) * ((v : 𝓞 F) : F) := rfl
      rw [e, map_mul]
      exact mul_pos (hu' σ) (hv' σ)
  inv_mem' := by
    rintro u ⟨hu, hu'⟩
    refine ⟨?_, fun σ => ?_⟩
    · rw [show ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) - 1 = -((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((u : 𝓞 F) - 1) by
        rw [neg_mul, mul_sub, Units.inv_mul]; ring]
      exact 𝔣.mul_mem_left _ hu
    · have e : (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((u : 𝓞 F) : F) = 1 := by
        have := congrArg (algebraMap (𝓞 F) F) (Units.inv_mul u)
        rwa [map_mul, map_one] at this
      have e' := congrArg σ e
      rw [map_mul, map_one] at e'
      exact (mul_pos_iff_of_pos_right (hu' σ)).1 (by rw [e']; exact one_pos)

def IsEntRat {ι : Type} (f N : ι → ℚ) : Prop :=
  ∃ A : ℂ → ℂ, Differentiable ℂ A ∧ (∀ s : ℂ, 1 < s.re → HasSum (fun i => (f i : ℂ) * (N i : ℂ) ^ (-s)) (A s)) ∧
    ∀ k : ℕ, ∃ r : ℚ, A (-(k : ℂ)) = (r : ℂ)

def IsBalanced {ι : Type} [DecidableEq ι] (l : ℕ) (φ : (ι → ℕ) → ℚ) : Prop :=
  (∀ i j, φ (Function.update j i (j i + l)) = φ j) ∧ ∀ i j, ∑ t ∈ Finset.range l, φ (Function.update j i t) = 0

open Classical in

def smooth {F : Type} [Field F] [NumberField F] (𝔠 : Ideal (𝓞 F)) (x : 𝓞 F) : ℚ :=
  1 - if x ∈ 𝔠 then (Ideal.absNorm 𝔠 : ℚ) else 0

open Classical in

def smoothIdeal {F : Type} [Field F] [NumberField F] (𝔠 I : Ideal (𝓞 F)) : ℚ :=
  1 - if 𝔠 ∣ I then (Ideal.absNorm 𝔠 : ℚ) else 0

example : IsEntRat (fun _ : Unit => 1) (fun _ => 1) :=
  ⟨fun _ => 1, differentiable_const _, fun s _ => by simpa using hasSum_fintype (fun _ : Unit => (1 : ℂ)), fun _ => ⟨1, by simp⟩⟩

example : IsSimplicial (Set.Ioi (0 : ℚ)) {1} :=
  ⟨by simp, by simp, by simp⟩

end GlobalTheory.Shintani
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.LandherrCSA
section
noncomputable section
namespace GlobalTheory.HermCSA
open NumberField
open scoped TensorProduct

def IsUInv (F C : Type) [Field F] [NumberField F] [IsCMField F] [Ring C] [Algebra F C] (s : C →+ C) : Prop :=
  (∀ x y, s (x * y) = s y * s x) ∧ (∀ x, s (s x) = x) ∧
    ∀ a : F, s (algebraMap F C a) = algebraMap F C (IsCMField.complexConj F a)

def ext (C K : Type) [Ring C] [CommRing K] (s : C →+ C) : K ⊗[ℤ] C →ₗ[ℤ] K ⊗[ℤ] C :=
  LinearMap.lTensor K s.toIntLinearMap

def LandherrCSA : Prop :=
  ∀ (F C : Type) [Field F] [NumberField F] [IsCMField F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C] (s : C →+ C), IsUInv F C s →
    ∀ A A' : C, IsUnit A → IsUnit A' → s A = A → s A' = A' →
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (g : (ℚ_[ℓ] ⊗[ℤ] C)ˣ) (ν : ℚ_[ℓ]), ν ≠ 0 ∧
      (1 : ℚ_[ℓ]) ⊗ₜ A' = ν • (ext C ℚ_[ℓ] s (g : ℚ_[ℓ] ⊗[ℤ] C) * ((1 : ℚ_[ℓ]) ⊗ₜ A) * (g : ℚ_[ℓ] ⊗[ℤ] C))) →
    (∃ g : (ℝ ⊗[ℤ] C)ˣ, (1 : ℝ) ⊗ₜ A' = ext C ℝ s (g : ℝ ⊗[ℤ] C) * ((1 : ℝ) ⊗ₜ A) * (g : ℝ ⊗[ℤ] C)) →
    ∃ (g : Cˣ) (c : F), IsCMField.complexConj F c = c ∧ (∀ τ : F →+* ℂ, 0 < (τ c).re) ∧
      A' = algebraMap F C c * (s (g : C) * A * g)

end GlobalTheory.HermCSA
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PerFactor
section
noncomputable section
namespace GlobalTheory.PolDeg.Taut
variable (W : Type) [CommRing W] [IsDomain W]

def coordT (m N : ℕ) (k : Fin N) : MvPowerSeries (Fin N) W :=
  if (k : ℕ) < m then MvPowerSeries.X k else 1 + MvPowerSeries.X k

def params {m N : ℕ} (h : m ≤ N) : Fin m → MvPowerSeries (Fin N) W := fun i => MvPowerSeries.X (Fin.castLE h i)

def perFactor (m N n r : ℕ) (ε : Fin N → LinearMap.BilinForm ℤ (Fin r → ℤ)) (a b : Fin r → ℤ) : FractionRing (MvPowerSeries (Fin N) W) :=
  ∏ k, (algebraMap (MvPowerSeries (Fin N) W) (FractionRing (MvPowerSeries (Fin N) W)) (coordT W m N k)) ^ ((n : ℤ) * ε k a b)
example : perFactor W 0 0 3 0 (fun k => k.elim0) 0 0 = 1 := by simp [perFactor]
end GlobalTheory.PolDeg.Taut
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
section
noncomputable section

open MvPolynomial
open scoped ContDiff

namespace GlobalTheory.PsCo.Pc1

abbrev Mat (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

abbrev Poly (n : ℕ) : Type := MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ

variable {n : ℕ}

def ev (g : Mat n) : Poly n →+* ℂ :=
  MvPolynomial.eval (Sum.elim (fun x : Fin n × Fin n => g x.1 x.2) (fun x => star (g x.1 x.2)))

abbrev Mode (ε : Fin n → Bool) : Type := {x : Fin n × Fin n // ε x.1 = true ∧ ε x.2 = false}

def nMode (ε : Fin n → Bool) : ℕ := Fintype.card (Mode ε)

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

def barM (ε : Fin n → Bool) (Z : Mat n) : Mat n := fun a b => -(sg ε a * sg ε b * Z b a)

def LieU (ε : Fin n → Bool) (Z : Mat n) : Prop := ∀ a b, (starRingEnd ℂ) (Z a b) = barM ε Z a b

def dZ (ε : Fin n → Bool) (Z : Mat n) : Derivation ℂ (Poly n) (Poly n) :=
  mkDerivation ℂ (Sum.elim
    (fun x : Fin n × Fin n => ∑ c, (X (Sum.inl (x.1, c)) * C (Z c x.2) - C (Z x.1 c) * X (Sum.inl (c, x.2))))
    (fun x : Fin n × Fin n =>
      ∑ c, (X (Sum.inr (x.1, c)) * C (barM ε Z c x.2) - C (barM ε Z x.1 c) * X (Sum.inr (c, x.2)))))

def dM (ε : Fin n → Bool) (x : Mode ε) : Derivation ℂ (Poly n) (Poly n) := dZ ε (Matrix.single x.1.2 x.1.1 1)

def rM (ε : Fin n → Bool) (g : Mat n) : ℝ := ∑ x : Mode ε, ‖g x.1.1 x.1.2‖ ^ 2

def rP (ε : Fin n → Bool) : Poly n := ∑ x : Mode ε, X (Sum.inl x.1) * X (Sum.inr x.1)

def OmP (ε : Fin n → Bool) : Matrix (Mode ε) (Mode ε) (Poly n) := fun x y => dM ε x (X (Sum.inr y.1))

def detbP (n : ℕ) : Poly n := (Matrix.of fun a b : Fin n => (X (Sum.inr (a, b)) : Poly n)).det

def blockAlg (ε : Fin n → Bool) : Subalgebra ℂ (Poly n) :=
  Algebra.adjoin ℂ {P | ∃ a b, ε a = ε b ∧ P = X (Sum.inl (a, b))}

def topP (ε : Fin n → Bool) (M : ℕ) (P : Poly n) : Poly n := detbP n ^ M * P * (OmP ε).det

def prev (q : ℕ → Poly n) : ℕ → Poly n
  | 0 => 0
  | k + 1 => q k

def IsKoszul (ε : Fin n → Bool) (p : ℕ → Poly n) (q : Mode ε → ℕ → Poly n) : Prop :=
  (∀ k : ℕ, ((k : Poly n) + 1) * p (k + 1) + rP ε * p k = ∑ x, (dM ε x (q x k) + dM ε x (rP ε) * prev (q x) k)) ∧
    (∀ k, nMode ε < k → p k = 0) ∧ ∀ x k, nMode ε ≤ k → q x k = 0

def IsCutFn (H : ℝ → ℝ) : Prop := ContDiff ℝ ∞ H ∧ ∃ R : ℝ, ∀ x, R ≤ x → H x = 0

def bas (ε : Fin n → Bool) (H : ℝ → ℝ) (P : Poly n) : Mat n → ℂ := fun g => (H (rM ε g) : ℂ) * ev g P

def adBas (ε : Fin n → Bool) (Z : Mat n) (H : ℝ → ℝ) (P : Poly n) : Mat n → ℂ := fun g =>
  bas ε (deriv H) (dZ ε Z (rP ε) * P) g + bas ε H (dZ ε Z P) g

def ShapeM (ε : Fin n → Bool) (d : ℕ) : Submodule ℂ (Mat n → ℂ) :=
  Submodule.span ℂ {φ | ∃ (H : ℝ → ℝ) (P : Poly n), IsCutFn H ∧ P.totalDegree ≤ d ∧ φ = bas ε H P}

def AdSpanM (ε : Fin n → Bool) : Submodule ℂ (Mat n → ℂ) :=
  Submodule.span ℂ {φ | ∃ (Z : Mat n) (H : ℝ → ℝ) (P : Poly n), LieU ε Z ∧ IsCutFn H ∧ φ = adBas ε Z H P}

def IsProfile (N : ℕ) (G : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ G ∧ (∀ x, 1 ≤ x → G x = 0) ∧ (∀ x, 0 ≤ iteratedDeriv N G x) ∧ 0 < iteratedDeriv N G 0

def famF (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → Poly n) (t : ℝ) : Mat n → ℂ := fun g =>
  ∑ k ∈ Finset.range (nMode ε + 1), bas ε (iteratedDeriv k fun x => G (t * x)) (p k) g

def dMode (ε : Fin n → Bool) (θ : Fin n → ℝ) : ℝ :=
  ∏ x : Mode ε, ‖Complex.exp (θ x.1.1 * Complex.I) - Complex.exp (θ x.1.2 * Complex.I)‖ ^ 2

def StAlg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (M : ℕ) (P : Poly n), P ∈ blockAlg ε →
    ∃ (p : ℕ → Poly n) (q : Mode ε → ℕ → Poly n), IsKoszul ε p q ∧ p (nMode ε) = topP ε M P

def StProfile : Prop := ∀ N : ℕ, ∃ G : ℝ → ℝ, IsProfile N G

def StFam : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → Poly n), IsProfile (nMode ε) G →
    ∃ d : ℕ, (∀ k, k ≤ nMode ε → (p k).totalDegree ≤ d) ∧
      ∀ t : ℝ, 0 < t → famF ε G p t ∈ ShapeM ε d ∧ ∀ g : Mat n, 1 < t * rM ε g → famF ε G p t g = 0

def StHomot : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → Poly n) (q : Mode ε → ℕ → Poly n), IsProfile (nMode ε) G →
    IsKoszul ε p q → ∀ t : ℝ, 1 ≤ t → famF ε G p 1 - famF ε G p t ∈ AdSpanM ε

def StBasDeriv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Mat n) (H : ℝ → ℝ) (P : Poly n), LieU ε Z → IsCutFn H →
    adBas ε Z H P ∈ ShapeM ε (P.totalDegree + 2) ∧ ∀ (g : Mat n) (s : ℝ),
      HasDerivAt (fun u : ℝ => bas ε H P (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)))
        (adBas ε Z H P (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z))) s

end GlobalTheory.PsCo.Pc1

end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.PsCo.Pc1.A

abbrev EntIdx (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

abbrev PolyL (n L : ℕ) := MvPolynomial (Fin L ⊕ EntIdx n) ℂ

abbrev PolyM (n L : ℕ) := MvPolynomial (Option (Fin L ⊕ EntIdx n)) ℂ

variable {n L : ℕ}

def inL (n L : ℕ) : Poly n →ₐ[ℂ] PolyL n L := rename Sum.inr

def inM (n L : ℕ) : PolyL n L →ₐ[ℂ] PolyM n L := rename some

def laL (n : ℕ) (i : Fin L) : PolyL n L := X (Sum.inl i)

def muM (n L : ℕ) : PolyM n L := X none

def dL (L : ℕ) (ε : Fin n → Bool) (x : Mode ε) : Derivation ℂ (PolyL n L) (PolyL n L) :=
  mkDerivation ℂ (Sum.elim (fun _ => 0) (fun v => inL n L (dM ε x (X v))))

def dMu (L : ℕ) (ε : Fin n → Bool) (x : Mode ε) : Derivation ℂ (PolyM n L) (PolyM n L) :=
  mkDerivation ℂ (fun w => match w with
    | none => 0
    | some v => inM n L (dL L ε x (X v)))

def coefM (n L : ℕ) (k : ℕ) : PolyM n L →ₗ[ℂ] PolyL n L :=
  ((Polynomial.lcoeff (PolyL n L) k).restrictScalars ℂ).comp (optionEquivLeft ℂ (Fin L ⊕ EntIdx n)).toLinearMap

def allOnes (L : ℕ) : Fin L →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1

def exL (n L : ℕ) : PolyL n L →ₗ[ℂ] Poly n :=
  ((MvPolynomial.lcoeff (Poly n) (allOnes L)).restrictScalars ℂ).comp (sumAlgEquiv ℂ (Fin L) (EntIdx n)).toLinearMap

def ex (n L : ℕ) (k : ℕ) : PolyM n L →ₗ[ℂ] Poly n := (exL n L).comp (coefM n L k)

end GlobalTheory.PsCo.Pc1.A

end
end

section

noncomputable section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

def T_det_deriv : Prop := ∀ {A : Type} [CommRing A] [Algebra ℂ A] (D : Derivation ℂ A A) {I : Type} [Fintype I]
    [DecidableEq I] (Z : Matrix I I A), D Z.det = ∑ x, ∑ y, Z.adjugate y x * D (Z x y)

def T_piola : Prop := ∀ {A : Type} [CommRing A] [Algebra ℂ A] {I : Type} [Fintype I] [DecidableEq I]
    (D : I → Derivation ℂ A A) (Z : Matrix I I A), (∀ w x y, D w (Z x y) = D x (Z w y)) →
    ∀ y, ∑ x, D x (Z.adjugate y x) = 0

def CoreCondition : Prop := ∀ {A : Type} [CommRing A] [Algebra ℂ A] {I : Type} [Fintype I] [DecidableEq I]
    (D : I → Derivation ℂ A A) (dm : Derivation ℂ A A) (J : Ideal A) (Z : Matrix I I A) (u η : I → A) (E μ r : A),
    (∀ x y, dm (Z x y) = D x (u y)) → (∀ w x y, D w (Z x y) = D x (Z w y)) → dm E = 0 →
    (∀ x, D x E + μ * D x r * E - E * ∑ y, Z x y * η y ∈ J) → r = ∑ y, η y * u y →
    dm (E * Z.det) + r * (E * Z.det) -
      ∑ x, (D x (E * ∑ y, Z.adjugate y x * u y) + μ * D x r * (E * ∑ y, Z.adjugate y x * u y)) ∈ J

def T_dual_prod : Prop := ∀ {A : Type} [CommRing A] [Algebra ℂ A] (D : Derivation ℂ A A) {L : ℕ} (la m : Fin L → A)
    (J : Ideal A), (∀ i, D (la i) = 0) → (∀ i, la i ^ 2 ∈ J) →
    D (∏ i, (1 + la i * m i)) - (∏ i, (1 + la i * m i)) * ∑ i, la i * D (m i) ∈ J

def T_dM_comm : Prop := ∀ {n : ℕ} (ε : Fin n → Bool) (w x : Mode ε) (P : Poly n), dM ε w (dM ε x P) = dM ε x (dM ε w P)

def T_dM_eta : Prop := ∀ {n : ℕ} (ε : Fin n → Bool) (x y : Mode ε), dM ε x (X (Sum.inl y.1)) = 0

def BlockDeterminantCondition : Prop := ∀ {n : ℕ} (ε : Fin n → Bool) (a b : Fin n), ε a = ε b →
    ∃ c : Mode ε → Mode ε → ℂ, ∀ x, dM ε x (X (Sum.inl (a, b))) = ∑ y, C (c x y) * X (Sum.inl y.1)

def T_dM_detb : Prop := ∀ {n : ℕ} (ε : Fin n → Bool) (x : Mode ε), dM ε x (detbP n) = 0

def T_dM_rP : Prop := ∀ {n : ℕ} (ε : Fin n → Bool) (x : Mode ε),
    dM ε x (rP ε) = ∑ y, X (Sum.inl y.1) * OmP ε x y

def T_exL_dL : Prop := ∀ {n L : ℕ} (ε : Fin n → Bool) (x : Mode ε) (b : PolyL n L),
    exL n L (dL L ε x b) = dM ε x (exL n L b)

def T_exL_inL_mul : Prop := ∀ {n L : ℕ} (a : Poly n) (b : PolyL n L), exL n L (inL n L a * b) = a * exL n L b

def T_exL_mul_sq : Prop := ∀ {n L : ℕ} (b : PolyL n L) (i : Fin L), exL n L (b * laL n i ^ 2) = 0

def T_exL_dual : Prop := ∀ {n L : ℕ} (m : Fin L → Poly n) (a : Poly n),
    exL n L ((∏ i, (1 + laL n i * inL n L (m i))) * inL n L a) = (∏ i, m i) * a

def T_coefM_dMu : Prop := ∀ {n L : ℕ} (ε : Fin n → Bool) (x : Mode ε) (k : ℕ) (s : PolyM n L),
    coefM n L k (dMu L ε x s) = dL L ε x (coefM n L k s)

def T_coefM_pderiv : Prop := ∀ {n L : ℕ} (k : ℕ) (s : PolyM n L),
    coefM n L k (pderiv none s) = ((k : ℂ) + 1) • coefM n L (k + 1) s

def T_coefM_mu_mul : Prop := ∀ {n L : ℕ} (k : ℕ) (s : PolyM n L),
    coefM n L k (muM n L * s) = if k = 0 then 0 else coefM n L (k - 1) s

def T_coefM_inM_mul : Prop := ∀ {n L : ℕ} (k : ℕ) (b : PolyL n L) (s : PolyM n L),
    coefM n L k (inM n L b * s) = b * coefM n L k s

def T_coefM_pencil : Prop := ∀ {n L : ℕ} {I : Type} [Fintype I] [DecidableEq I] (A0 B0 : Matrix I I (PolyL n L)),
    let Z : Matrix I I (PolyM n L) := fun x y => muM n L * inM n L (A0 x y) + inM n L (B0 x y)
    (∀ k, Fintype.card I < k → coefM n L k Z.det = 0) ∧ coefM n L (Fintype.card I) Z.det = A0.det ∧
      ∀ k x y, Fintype.card I ≤ k → coefM n L k (Z.adjugate y x) = 0

def T_stMono : Prop := ∀ {n : ℕ} (ε : Fin n → Bool) (M L : ℕ) (β : Fin L → Fin n × Fin n), (∀ i, ε (β i).1 = ε (β i).2) →
    ∃ p q, IsKoszul ε p q ∧ p (nMode ε) = topP ε M (∏ i, X (Sum.inl (β i)))

end GlobalTheory.PsCo.Cw2a

end
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ZetaPair
section
noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HenQ

def eulerL (K : Type) [Field K] [NumberField K] (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∏' w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
    ((B w.1).map fun b => (1 - b * ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod

def eulerLd (K : Type) [Field K] [NumberField K] (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  eulerL K (fun w => (B w).map (·⁻¹)) S (1 - s)

def capPoly (m : Multiset ℂ) : ℂ[X] := (m.map fun z => (X + C z) * (X + C z + 1)).prod

def ZetaPair (L L' : ℂ → ℂ) (β : ℂ[X]) : Prop :=
  ∃ (Z W A B : ℂ → ℂ) (k : ℂ) (c : ℝ), Differentiable ℂ Z ∧ Differentiable ℂ W ∧ Z ≠ 0 ∧ W ≠ 0 ∧ k ≠ 0 ∧
    (∀ s : ℂ, c < s.re → Z s = L s * A s ∧ W s = L (s + 2) * β.eval s * A s) ∧
    (∀ s : ℂ, s.re < -c → Z s = L' s * B s ∧ W s = k * L' (s + 2) * B s)

end GlobalTheory.HenQ
end
end

