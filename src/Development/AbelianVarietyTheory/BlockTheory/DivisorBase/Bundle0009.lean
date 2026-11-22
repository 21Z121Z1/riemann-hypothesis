import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def archFactor (n : I → ℤ) (s : ℂ) : ℂ :=
  ∏ i, (2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)) * Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2))

def IsCompletedL (χ : HChar E) (n : I → ℤ) (Λ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Λ ∧ ∀ s : ℂ, 1 < s.re → ∃ L : ℂ, HasProd (eulerFactor χ s) L ∧ Λ s = archFactor n s * L

def BoundedInStrips (Λ : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a < b → ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Λ s‖ ≤ C

def CompletedLBoundedInStrips : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (χ : HChar E) (n : I → ℤ), IsUnitary χ → Formalism.L2.Host.HChar.HasInf χ φ n → (∃ i, n i ≠ 0) →
      ∃ Λ : ℂ → ℂ, IsCompletedL χ n Λ ∧ BoundedInStrips Λ

def CompletedLBoundedInStripsEven : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (χ : HChar E) (m : I → ℤ), IsUnitary χ → HasInfRatio χ φ m → (∃ i, m i ≠ 0) →
      ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
        (∀ s : ℂ, 1 < s.re → ∃ L : ℂ, HasProd (eulerFactor χ s) L ∧ Λ s = LInf m s * L) ∧ BoundedInStrips Λ

theorem IsCompletedL.unique {χ : HChar E} {n : I → ℤ} {f g : ℂ → ℂ} (hf : IsCompletedL χ n f) (hg : IsCompletedL χ n g) :
    f = g :=
  entire_eq_of_halfPlane hf.1 hg.1 1 fun s hs => by
    obtain ⟨L, h1, h2⟩ := hf.2 s hs
    obtain ⟨L', h1', h2'⟩ := hg.2 s hs
    rw [h2, h2', h1.unique h1']

theorem IsCompletedL.eq_mul {χ : HChar E} {n : I → ℤ} {Λ L : ℂ → ℂ} (h : IsCompletedL χ n Λ) (hL : IsHeckeL χ L)
    {s : ℂ} (hs : 1 < s.re) : Λ s = archFactor n s * L s := by
  obtain ⟨L', h1, h2⟩ := h.2 s hs
  rw [h2, h1.unique (hL.2 s hs)]

theorem archFactor_two_mul (m : I → ℤ) (s : ℂ) : archFactor (fun i => 2 * m i) s = LInf m s := by
  unfold archFactor LInf
  refine Finset.prod_congr rfl fun i _ => ?_
  have : (((|2 * m i| : ℤ) : ℂ)) / 2 = ((|m i| : ℤ) : ℂ) := by
    rw [abs_mul, abs_two]; push_cast; ring
  rw [this]

theorem CompletedLBoundedInStrips.forall (h : CompletedLBoundedInStrips) [IsTotallyComplex E] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {χ : HChar E} {n : I → ℤ} (hu : IsUnitary χ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (hn : ∃ i, n i ≠ 0)
    {Λ : ℂ → ℂ} (hΛ : IsCompletedL χ n Λ) : BoundedInStrips Λ := by
  obtain ⟨Λ', h1, h2⟩ := h E I φ hφ χ n hu hi hn
  rwa [hΛ.unique h1]

theorem CompletedLBoundedInStrips.even (h : CompletedLBoundedInStrips) : CompletedLBoundedInStripsEven := by
  intro E _ _ _ I _ φ hφ χ m hu hi ⟨i, hm⟩
  obtain ⟨Λ, h1, h2⟩ := h E I φ hφ χ (fun i => 2 * m i) hu hi ⟨i, mul_ne_zero two_ne_zero hm⟩
  refine ⟨Λ, h1.1, fun s hs => ?_, h2⟩
  simpa only [archFactor_two_mul] using h1.2 s hs

example : ¬ BoundedInStrips (fun s => s) := by
  intro h
  obtain ⟨C, hC⟩ := h 0 1 one_pos
  have := hC (((|C| + 1 : ℝ) : ℂ) * Complex.I) (by simp) (by simp)
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at this
  linarith [le_abs_self C]

example : archFactor (fun _ : Unit => (-2 : ℤ)) 0 = (Real.pi : ℂ)⁻¹ := by
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [archFactor, Complex.cpow_neg_one]
  field_simp

end GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
section
noncomputable section

open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal

namespace GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

section Val

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]

def ord_vw (x : K) : ℤ := -WithZero.log ((IsDiscreteValuationRing.maximalIdeal O).valuation K x)

open Classical in

def val_vp (l : ℕ) (x : K) : WithTop ℚ :=
  if x = 0 then ⊤ else (((ord_vw O x : ℚ) / (ord_vw O (l : K) : ℚ) : ℚ) : WithTop ℚ)

end Val

section Const

variable {E : Type} [Field E] [NumberField E]

def diffExp_vp (l : ℕ) (P : HeightOneSpectrum (𝓞 E)) : ℚ :=
  (multiplicity P.asIdeal (differentIdeal ℤ (𝓞 E)) : ℚ) / (multiplicity P.asIdeal (Ideal.span {(l : 𝓞 E)}) : ℚ)

def condExp (𝔣 : Ideal (OF E)) (l : ℕ) : ℕ :=
  sSup (expIn 𝔣 '' {v : HeightOneSpectrum (OF E) | (l : OF E) ∈ v.asIdeal})

open Classical in

def cNum_vp (𝔣 : Ideal (OF E)) (l : ℕ) (P : HeightOneSpectrum (𝓞 E)) : ℚ :=
  if ∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal then (condExp 𝔣 l : ℚ) else diffExp_vp l P

theorem condExp_bdd (𝔣 : Ideal (OF E)) {l : ℕ} (hl : l ≠ 0) :
    BddAbove (expIn 𝔣 '' {v : HeightOneSpectrum (OF E) | (l : OF E) ∈ v.asIdeal}) := by
  refine (Set.Finite.image _ ?_).bddAbove
  have h : Ideal.span {(l : OF E)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hl
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  simpa [Ideal.dvd_span_singleton] using hv

end Const

section Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]

def bar (σ : E →+* K) : E →+* K := σ.comp (IsCMField.complexConj E : E →+* E)

def IsCMTypeIn {I : Type} (φ : I → E →+* K) : Prop := ∀ σ : E →+* K, ∃! i, σ = φ i ∨ σ = bar (φ i)

def coordAt (O : Type) [CommRing O] [Algebra O K] (c : Ideal (OF E)) (σ : E →+* K) : orderC c ⊗[ℤ] O →ₐ[ℤ] K :=
  Algebra.TensorProduct.productMap (σ.comp (orderC c).subtype).toIntAlgHom (algebraMap O K).toIntAlgHom

open Classical in

def ClearsIdem (K : Type) [Field K] [Algebra O K] (c : Ideal (OF E)) (D : O) : Prop :=
  ∀ σ : E →+* K, ∃ t : orderC c ⊗[ℤ] O, ∀ σ' : E →+* K, coordAt O c σ' t = if σ' = σ then algebraMap O K D else 0

variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

def eigK (ρ : orderC c →+* Module.End O H) (σ : E →+* K) : Submodule K (K ⊗[O] H) :=
  ⨅ a : orderC c, Module.End.eigenspace ((ρ a).baseChange K) (σ a)

def inK (K : Type) [Field K] [Algebra O K] (H : Type) [AddCommGroup H] [Module O H] : H →ₗ[O] K ⊗[O] H :=
  TensorProduct.mk O K H 1

def eigLat (ρ : orderC c →+* Module.End O H) (σ : E →+* K) : Submodule O H :=
  ((eigK ρ σ).restrictScalars O).comap (inK K H)

def IsSat (M : Submodule O H) : Prop := ∀ (x : O) (h : H), x ≠ 0 → x • h ∈ M → h ∈ M

def ofF (c : Ideal (OF E)) (a : OF E) : orderC c := ⟨algebraMap (OF E) E a, algebraMap_mem_orderC c a⟩

def IsCMLattice {I : Type} (φ : I → E →+* K) (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H)
    (B : LinearMap.BilinForm O H) : Prop :=
  Module.Free O H ∧ Module.Finite O H ∧ Module.finrank O H = Module.finrank ℚ E ∧
  (∀ σ : E →+* K, Module.finrank K (eigK ρ σ) = 1) ∧
  IsSat Fil ∧ Fil.baseChange K = ⨆ i, eigK ρ (φ i) ∧
  Function.Bijective B ∧ B.IsAlt ∧
  ∀ a b : orderC c, (b : E) = IsCMField.complexConj E a → ∀ h h' : H, B (ρ a h) h' = B h (ρ b h')

def IsGens {I : Type} (φ : I → E →+* K) (ρ : orderC c →+* Module.End O H) (e f : I → H) : Prop :=
  ∀ i, eigLat ρ (φ i) = O ∙ e i ∧ eigLat ρ (bar (φ i)) = O ∙ f i

def IsLower (ρ : orderC c →+* Module.End O H) (τ : E →+* K) (e f : H) (N : Module.End K (K ⊗[O] H)) : Prop :=
  N (inK K H e) = inK K H f ∧ ∀ σ : E →+* K, σ ≠ τ → ∀ x ∈ eigK ρ σ, N x = 0

def IsScaledRestr (D : O) (N : Module.End K (K ⊗[O] H)) (M : Module.End O H) : Prop :=
  ∀ h : H, inK K H (M h) = algebraMap O K D • N (inK K H h)

end Lin

def lPrime (l : ℕ) : ℕ := if l = 2 then 4 else l

def lPrimeExp (l : ℕ) : ℕ := if l = 2 then 2 else 1

def nilPart {O : Type} [CommRing O] {H : Type} [AddCommGroup H] [Module O H] {I : Type} [Fintype I] (l : ℕ)
    (M : I → Module.End O H) (R : Type) [CommRing R] [Algebra O R] (t : I → R) : Module.End R (R ⊗[O] H) :=
  (lPrime l : R) • ∑ i, t i • (M i).baseChange R

def ElementD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
  ∀ (l : ℕ), l.Prime →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E →
    (∃ D : O, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal →
        val_vp O l (algebraMap O K D) = (cNum_vp 𝔣 l P : ℚ)) ∧ ClearsIdem K 𝔣 D) ∧
    ∀ Q : Finset (HeightOneSpectrum (OF E)), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
      ∀ D : O, ClearsIdem K (condQ 𝔣 Q) D ↔ ClearsIdem K 𝔣 D

section Steps

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)} {I : Type} [Fintype I]

open Classical in

def EigenClaims (φ : I → E →+* K) (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H)
    (D : O) : Prop :=
  DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ) ∧
  (∀ σ : E →+* K, IsSat (eigLat ρ σ) ∧ (∃ g : H, g ≠ 0 ∧ eigLat ρ σ = O ∙ g) ∧
    Module.Free O (eigLat ρ σ) ∧ Module.finrank O (eigLat ρ σ) = 1 ∧ ∃ C : Submodule O H, IsCompl (eigLat ρ σ) C) ∧
  (iSupIndep (fun σ : E →+* K => eigLat ρ σ) ∧ ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ) ∧
  (∀ i, Fil ⊓ eigLat ρ (φ i) = eigLat ρ (φ i)) ∧
  ∀ σ σ' : E →+* K, σ' ≠ bar σ → ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', B.baseChange K x y = 0

def LowerClaims (l : ℕ) (φ : I → E →+* K) (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) (D : O)
    (e f : I → H) : Prop :=
  (∀ i, ∃! N, IsLower ρ (φ i) (e i) (f i) N) ∧
  ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) →
    (∀ i, ∃! M : Module.End O H, IsScaledRestr D (N i) M) ∧
    (∀ i (a : OF E), Commute (N i) ((ρ (ofF c a)).baseChange K)) ∧
    (∀ i j, N i * N j = 0) ∧
    (∀ i x y, B.baseChange K (N i x) y + B.baseChange K x (N i y) = 0) ∧
    (∀ i j x y, B.baseChange K (N i x) (N j y) = 0) ∧
    ∀ M : I → Module.End O H, (∀ i, IsScaledRestr D (N i) (M i)) →
      ∀ (R : Type) [CommRing R] [Algebra O R] (t : I → R),
        (∀ x : R ⊗[O] H, ∃ y : R ⊗[O] H, (1 + nilPart l M R t) x = x + (lPrime l : R) • y) ∧
        ((1 + nilPart l M R t) * (1 - nilPart l M R t) = 1 ∧ (1 - nilPart l M R t) * (1 + nilPart l M R t) = 1) ∧
        (∀ a : OF E, Commute (1 + nilPart l M R t) ((ρ (ofF c a)).baseChange R)) ∧
        ∀ x y : R ⊗[O] H, B.baseChange R ((1 + nilPart l M R t) x) ((1 + nilPart l M R t) y) = B.baseChange R x y

def DetClaims (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] (l : ℕ) (Fil : Submodule O H) (D : O) (e : I → H) :
    Prop :=
  Module.Free O Fil ∧ Module.finrank O Fil = Fintype.card I ∧ (∀ i, e i ∈ Fil) ∧
  (∃ ω : ⋀[O]^(Fintype.card I) Fil, O ∙ ω = ⊤) ∧
  ∀ ω : ⋀[O]^(Fintype.card I) Fil, O ∙ ω = ⊤ → ∀ (s : Fin (Fintype.card I) ≃ I) (e' : I → Fil), (∀ i, (e' i : H) = e i) →
    ∃ u : O, exteriorPower.ιMulti O (Fintype.card I) (fun j => e' (s j)) = u • ω ∧
      0 ≤ val_vp O l (algebraMap O K u) ∧
      val_vp O l (algebraMap O K u) ≤ Fintype.card I • val_vp O l (algebraMap O K D)

def FormClaims (l : ℕ) (φ : I → E →+* K) (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) (D : O)
    (e f : I → H) : Prop :=
  (∃! ρE : E →+* Module.End K (K ⊗[O] H), ∀ a : orderC c, ρE a = (ρ a).baseChange K) ∧
  ∀ ρE : E →+* Module.End K (K ⊗[O] H), (∀ a : orderC c, ρE a = (ρ a).baseChange K) →
  ∀ (d : ℕ) (r ξ : E), d.Prime → r ^ 2 = -(d : E) → IsCMField.complexConj E ξ = -ξ → ξ ≠ 0 →
    (∀ σ : E →+* K, val_vp O l (σ ξ) ≤ 0) →
    (ξ * r ∈ maximalRealSubfield E ∧ ξ * r ≠ 0) ∧
    (∃! BF : LinearMap.BilinForm K (K ⊗[O] H), ∀ x y, B.baseChange K x y = BF x (ρE (ξ * r)⁻¹ y)) ∧
    ∀ BF : LinearMap.BilinForm K (K ⊗[O] H), (∀ x y, B.baseChange K x y = BF x (ρE (ξ * r)⁻¹ y)) → ∀ i,
      BF (inK K H (e i)) (inK K H (f i)) = φ i (ξ * r) * algebraMap O K (B (e i) (f i)) ∧
      BF (inK K H (e i)) (inK K H (f i)) ≠ 0 ∧
      val_vp O l (BF (inK K H (e i)) (inK K H (f i))) =
        val_vp O l (algebraMap O K (B (e i) (f i))) + val_vp O l (φ i ξ) + val_vp O l (φ i r) ∧
      val_vp O l (φ i r) = (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ) ∧
      val_vp O l (BF (inK K H (e i)) (inK K H (f i))) ≤
        val_vp O l (algebraMap O K D) + (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ)

end Steps

def LatticeClaims : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
  ∀ (l : ℕ), l.Prime →
  ∀ (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E →
  ∀ (D : O), D ≠ 0 → ClearsIdem K 𝔣 D →
  ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ →
  ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC (condQ 𝔣 Q) →+* Module.End O H) (Fil : Submodule O H)
    (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B →
    EigenClaims φ ρ Fil B D ∧
    ∀ e f : I → H, IsGens φ ρ e f →
      (∀ i, 0 ≤ val_vp O l (algebraMap O K (B (e i) (f i))) ∧
        val_vp O l (algebraMap O K (B (e i) (f i))) ≤ val_vp O l (algebraMap O K D)) ∧
      LowerClaims l φ ρ B D e f ∧ DetClaims K l Fil D e ∧ FormClaims l φ ρ B D e f

def DividedPowerClaims : Prop :=
  ∀ (l : ℕ), l.Prime →
  (∀ m : ℕ, (1 ≤ m → lPrimeExp l + padicValNat l m.factorial ≤ lPrimeExp l * m) ∧
    m + 2 * padicValNat l m.factorial ≤ 2 * (lPrimeExp l * m)) ∧
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O →
  ∀ (R : Type) [CommRing R] [Algebra O R], (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) →
    ∃ (γ : DividedPowers (Ideal.span {(lPrime l : R)})) (γ₀ : DividedPowers (Ideal.span {(l : R)})),
      (∀ m : ℕ, ∃ q : O, (m.factorial : O) * q = (lPrime l : O) ^ m ∧
        ∀ x : R, γ.dpow m ((lPrime l : R) * x) = algebraMap O R q * x ^ m) ∧
      (∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)}, (m.factorial : R) * γ₀.dpow m y = y ^ m) ∧
      (∀ (m : ℕ), ∀ y ∈ Ideal.span {(lPrime l : R)}, γ.dpow m y = γ₀.dpow m y) ∧
      ∀ n : ℕ, 1 ≤ n →
        γ.IsSubDPIdeal (Ideal.span {(lPrime l : R) ^ n}) ∧
        ∀ (r : ℕ) (m : Fin r → ℕ) (x : Fin r → R), (∀ i, x i ∈ Ideal.span {(lPrime l : R)}) →
          2 * n * lPrimeExp l ≤ ∑ i, m i → ∏ i, γ.dpow (m i) (x i) ∈ Ideal.span {(lPrime l : R) ^ n}

def Statement : Prop := ElementD ∧ LatticeClaims ∧ DividedPowerClaims

example : lPrime 2 = 2 ^ lPrimeExp 2 ∧ lPrime 7 = 7 ^ lPrimeExp 7 := by decide

example (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] {K : Type} [Field K] [Algebra O K]
    [IsFractionRing O K] (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) : val_vp O l (l : K) = 1 := by
  have h0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap O K)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (Nat.cast_ne_zero.2 hl)
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) < 1 := by
    rw [← map_natCast (algebraMap O K), HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact h
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) ≠ 0 := by simpa using h0
  have h3 : ord_vw O (l : K) ≠ 0 := by
    unfold ord_vw
    intro h4
    have := WithZero.exp_log h2
    rw [neg_eq_zero.1 h4, WithZero.exp_zero] at this
    exact h1.ne this.symm
  rw [val_vp, if_neg h0, div_self (by exact_mod_cast h3)]
  rfl

example {E : Type} [Field E] [NumberField E] {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] (c : Ideal (OF E))
    (σ : E →+* K) (a : orderC c) (x : O) : coordAt O c σ (a ⊗ₜ x) = σ a * algebraMap O K x := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] [DecidableEq I]

def cWt (E : Type) [Field E] [NumberField E] (k : ℕ) : ℝ :=
  ((k - 1).factorial : ℝ) ^ Module.finrank ℚ (maximalRealSubfield E) *
    |(discr (maximalRealSubfield E) : ℝ)| ^ (((k : ℝ) - 1) / 2)

def polydisc (I : Type) : Set (I → ℂ) := {z | ∀ i, ‖z i‖ < 1}

def defCoord (φ : I → E →+* ℂ) (z : I → ℂ) (x : E) (i : I) : ℂ := φ i x + z i * starRingEnd ℂ (φ i x)

def defTerm (φ : I → E →+* ℂ) (k : ℕ) (z : I → ℂ) (σ : ℂ) (x : E) : ℂ :=
  ∏ i, ((defCoord φ z x i)⁻¹ ^ k * ((‖defCoord φ z x i‖ : ℝ) : ℂ) ^ (-2 * σ))

def IsEisValue (φ : I → E →+* ℂ) (k : ℕ) (L : Set E) (z : I → ℂ) (G : ℂ) : Prop :=
  (k ≠ 2 → HasSum (fun q : modUnits L => ∏ i, (defCoord φ z q.1.out i)⁻¹ ^ k) G) ∧
  (k = 2 → ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {σ : ℂ | -1 / 2 < σ.re} ∧
    (∀ σ : ℂ, 0 < σ.re → HasSum (fun q : modUnits L => defTerm φ 2 z σ q.1.out) (H σ)) ∧ G = H 0)

def IsDefSum (φ : I → E →+* ℂ) (k : ℕ) (L : Set E) (g : (I → ℂ) → ℂ) : Prop :=
  ∀ z ∈ polydisc I, ∃ G : ℂ, IsEisValue φ k L z G ∧ g z = (cWt E k : ℂ) * G

def partialD (i : I) (g : (I → ℂ) → ℂ) : (I → ℂ) → ℂ := fun z => lineDeriv ℂ g z (Pi.single i 1)

def iterD (l : List I) (g : (I → ℂ) → ℂ) : (I → ℂ) → ℂ := l.foldr partialD g

def risingFactor (k : ℕ) (κ : I → ℕ) : ℂ := ∏ i, ((-1 : ℂ) ^ κ i * ∏ j ∈ Finset.range (κ i), ((k : ℂ) + j))

def DerivFormula (φ : I → E →+* ℂ) (k : ℕ) (L : Set E) : Prop :=
  (∃ g, IsDefSum φ k L g) ∧ ∀ g, IsDefSum φ k L g →
    DifferentiableOn ℂ g (polydisc I) ∧
    ∀ (κ : I → ℕ) (l : List I), (∀ i, l.count i = κ i) →
      (∀ S : ℂ → ℂ, IsLatSum φ k κ L S → iterD l g 0 = (cWt E k : ℂ) * risingFactor k κ * S 0) ∧
      (4 ≤ k → ∃ S₀ : ℂ,
        HasSum (fun q : modUnits L => ∏ i, ((φ i q.1.out)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i q.1.out)) ^ κ i)) S₀ ∧
        iterD l g 0 = (cWt E k : ℂ) * risingFactor k κ * S₀)

def lamInf (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (α : Eˣ) : ℂ :=
  ∏ i, ((φ i α) ^ (k + κ i) * (starRingEnd ℂ (φ i α))⁻¹ ^ κ i)

def Homothety (φ : I → E →+* ℂ) (k : ℕ) (L : Set E) : Prop :=
  ∀ (κ : I → ℕ) (α : Eˣ) (S : ℂ → ℂ), IsLatSum φ k κ L S →
    IsLatSum φ k κ ((fun x => (α : E) * x) '' L)
      (fun σ => (lamInf φ k κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) * S σ) ∧
    ∀ S' : ℂ → ℂ, IsLatSum φ k κ ((fun x => (α : E) * x) '' L) S' → S' 0 = (lamInf φ k κ α)⁻¹ * S 0

def lamFin (χ : HChar E) (s : ℕ) (y : (Af E)ˣ) : ℂ := (finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)

def ClassInvariance (φ : I → E →+* ℂ) (s : ℕ) : Prop :=
  ∀ (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (κ : I → ℕ) (χ : HChar E),
    IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ →
    ∀ (y y' : (Af E)ˣ) (S S' : ℂ → ℂ),
      (QuotientGroup.mk y : PicO (condQ 𝔣 Q)) = QuotientGroup.mk y' →
      IsLatSum φ (2 * s) κ (lattice (condQ 𝔣 Q) y) S → IsLatSum φ (2 * s) κ (lattice (condQ 𝔣 Q) y') S' →
      (lamFin χ s y)⁻¹ * S 0 = (lamFin χ s y')⁻¹ * S' 0

abbrev Coh (E : Type) [Field E] [NumberField E] : Type := E →ₗ[ℚ] ℂ

def eCl (φ : I → E →+* ℂ) (i : I) : Coh E := (φ i).toRatAlgHom.toLinearMap

def fCl (φ : I → E →+* ℂ) (i : I) : Coh E := (ComplexEmbedding.conjugate (φ i)).toRatAlgHom.toLinearMap

def plane (φ : I → E →+* ℂ) (i : I) : Submodule ℂ (Coh E) := Submodule.span ℂ {eCl φ i, fCl φ i}

variable [IsCMField E]

def riemann (ξ x y : E) : ℚ := Algebra.trace ℚ E (ξ * x * IsCMField.complexConj E y)

def riemannCl (ξ x : E) : Coh E where
  toFun y := (riemann ξ x y : ℂ)
  map_add' y y' := by simp [riemann, mul_add]
  map_smul' a y := by
    have h : IsCMField.complexConj E (a • y) = a • IsCMField.complexConj E y := map_rat_smul _ a y
    simp only [riemann, h, mul_smul_comm, map_smul, RingHom.id_apply]
    simp [Rat.smul_def]

def IsDualForm (ξ : E) (B : LinearMap.BilinForm ℂ (Coh E)) : Prop :=
  ∀ x y : E, B (riemannCl ξ x) (riemannCl ξ y) = (riemann ξ x y : ℂ)

def pairing (ε : ℤˣ) (B : LinearMap.BilinForm ℂ (Coh E)) (a b : Coh E) : ℂ :=
  ((ε : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * B a b

def DualFormValue (φ : I → E →+* ℂ) : Prop :=
  ∀ ξ : E, ξ ≠ 0 → IsCMField.complexConj E ξ = -ξ →
    (∃! B, IsDualForm ξ B) ∧ ∀ B, IsDualForm ξ B → ∀ ε : ℤˣ,
      (∀ i j, i ≠ j → ∀ a ∈ plane φ i, ∀ b ∈ plane φ j, pairing ε B a b = 0) ∧
      ∀ i, pairing ε B (eCl φ i) (fCl φ i) = ((ε : ℤ) : ℂ) * (φ i ξ)⁻¹ / (2 * (Real.pi : ℂ) * Complex.I)

def DualFormBase (φ : I → E →+* ℂ) : Prop :=
  ∀ (d : ℕ) (δ : E), 0 < d → δ ^ 2 = -(d : E) → (∀ i, φ i δ = Complex.I * (Real.sqrt d : ℂ)) → ∀ η : ℤˣ,
    (∃! B, IsDualForm (((η : ℤ) : E) * δ⁻¹) B) ∧ ∀ B, IsDualForm (((η : ℤ) : E) * δ⁻¹) B → ∀ ε : ℤˣ,
      (∀ i j, i ≠ j → ∀ a ∈ plane φ i, ∀ b ∈ plane φ j, pairing ε B a b = 0) ∧
      ∀ i, pairing ε B (eCl φ i) (fCl φ i) = ((ε * η : ℤˣ) : ℤ) * ((Real.sqrt d / (2 * Real.pi) : ℝ) : ℂ)

def Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ),
    2 ≤ Module.finrank ℚ (maximalRealSubfield E) → IsCMType φ →
    (∀ s : ℕ, 1 ≤ s →
      (∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
        DerivFormula φ (2 * s) (lattice c y) ∧ Homothety φ (2 * s) (lattice c y)) ∧
      ClassInvariance φ s) ∧
    DualFormValue φ ∧ DualFormBase φ

example (φ : I → E →+* ℂ) (k : ℕ) (σ : ℂ) (x : E) : defTerm φ k 0 σ x = term φ k (fun _ => 0) σ x := by
  simp [defTerm, term, defCoord]

example : risingFactor 2 (fun _ : Unit => 2) = 6 := by
  simp [risingFactor, Finset.prod_range_succ]; norm_num

example (φ : I → E →+* ℂ) (z : I → ℂ) (hz : z ∈ polydisc I) (x : E) (hx : x ≠ 0) (i : I) : defCoord φ z x i ≠ 0 := by
  intro h
  have h0 : φ i x ≠ 0 := by simpa using hx
  have h1 : φ i x = -(z i * starRingEnd ℂ (φ i x)) := eq_neg_of_add_eq_zero_left h
  have h2 : ‖φ i x‖ = ‖z i‖ * ‖φ i x‖ := by
    conv_lhs => rw [h1]
    simp
  have h3 : 0 < ‖φ i x‖ := norm_pos_iff.2 h0
  have h4 := hz i
  nlinarith

end GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates
end
end

