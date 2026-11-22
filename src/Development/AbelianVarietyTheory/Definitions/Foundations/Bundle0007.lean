import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.CoPtMu
section
noncomputable section

open Finset

namespace GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

def ffMu (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (a : ℤ) (s : ℕ) : K :=
  ∑ d ∈ s.divisors, if ¬ p ∣ d ∧ ¬ p ∣ (s / d) then
    ((if ((s / d : ℕ) : ℤ) ≡ a [ZMOD N] then ψ ((s / d : ℕ) : ZMod (p ^ m)) * ((s / d : ℕ) : K) ^ (k - 2) else 0) -
     (if (-((s / d : ℕ) : ℤ)) ≡ a [ZMOD N] then ψ (-((s / d : ℕ) : ZMod (p ^ m))) * (-((s / d : ℕ) : K)) ^ (k - 2) else 0))
    else 0

def eeMu (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (b : ℤ) (s : ℕ) : K :=
  ∑ d ∈ s.divisors, if ¬ p ∣ d ∧ ¬ p ∣ (s / d) then
    ((if ((s / d : ℕ) : ℤ) ≡ b [ZMOD N] then ψ⁻¹ ((d : ℕ) : ZMod (p ^ m)) else 0) -
     (if (-((s / d : ℕ) : ℤ)) ≡ b [ZMOD N] then ψ⁻¹ (-((d : ℕ) : ZMod (p ^ m))) else 0))
    else 0

def coPtMu (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (a b : ℤ) : ℕ → K :=
  cmul (ffMu N p m k ψ a) (eeMu N p m ψ b)

def coPtS (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d x : ℤ) (s : ℕ) : K :=
  (c : K) ^ 2 * (d : K) ^ 2 * coPtMu N p m k ψ x 1 s
    - (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) ^ 2 * coPtMu N p m k ψ (c * x) 1 s
    - (c : K) ^ 2 * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * coPtMu N p m k ψ x d s
    + (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * coPtMu N p m k ψ (c * x) d s

end GlobalTheory.KummerEisensteinGalois
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
section
noncomputable section

open scoped MatrixGroups
open Polynomial

namespace GlobalTheory.K4

open GlobalTheory.KZ

section Hahn

variable {Ω : Type} [Field Ω]

theorem hahn_pow_order_leadingCoeff (s : HahnSeries ℚ Ω) (hs : s ≠ 0) (n : ℕ) :
    (s ^ n).order = n • s.order ∧ (s ^ n).leadingCoeff = s.leadingCoeff ^ n := by
  refine ⟨HahnSeries.order_pow s n, ?_⟩
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, HahnSeries.leadingCoeff_mul, ih, pow_succ]

private theorem hahnSeries_algebraMap_mul_coeff (c : Ω) (x : HahnSeries ℚ Ω) (r : ℚ) :
    (algebraMap Ω (HahnSeries ℚ Ω) c * x).coeff r = c * x.coeff r := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem hahn_transcendental {s : HahnSeries ℚ Ω} (hs : s ≠ 0) (ho : s.order < 0) : Transcendental Ω s := by
  rintro ⟨P, hP, hPs⟩
  have hlead : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hP
  have hls : s.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.2 hs
  have key : (Polynomial.aeval s P).coeff (P.natDegree • s.order) =
      P.coeff P.natDegree * s.leadingCoeff ^ P.natDegree := by
    rw [Polynomial.aeval_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_range_succ, Finset.sum_eq_zero]
    · rw [zero_add]
      rw [Algebra.smul_def, hahnSeries_algebraMap_mul_coeff]
      rw [← (hahn_pow_order_leadingCoeff s hs P.natDegree).1,
        ← HahnSeries.leadingCoeff_eq, (hahn_pow_order_leadingCoeff s hs P.natDegree).2]
    · intro k hk
      rw [Algebra.smul_def, hahnSeries_algebraMap_mul_coeff]
      rw [HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
      rw [(hahn_pow_order_leadingCoeff s hs k).1, nsmul_eq_mul, nsmul_eq_mul]
      exact mul_lt_mul_of_neg_right (by exact_mod_cast Finset.mem_range.1 hk) ho
  rw [hPs] at key
  exact mul_ne_zero hlead (pow_ne_zero _ hls) (by simpa using key.symm)

end Hahn

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem mem_lev_iff (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (f : X.K) :
    f ∈ lev X Γ' ↔ ∀ γ ∈ Γ', X.sl (ofSL γ) f = f := by
  unfold lev
  simp only [Subfield.mem_iInf, RingHom.mem_eqLocusField]
  rfl

theorem algebraMap_mem_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (c : Ω) : algebraMap Ω X.K c ∈ lev X Γ' := (mem_lev_iff X Γ' _).2 fun γ _ => (X.sl (ofSL γ)).commutes c

theorem jK_mem_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : X.jK ∈ lev X Γ' := (mem_lev_iff X Γ' _).2 fun γ _ => X.j_inv γ

theorem mdl_le_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : mdl X Γ' S ≤ lev X Γ' := by
  unfold mdl
  exact inf_le_left

theorem jK_transcendental (X : Tower Ω ε) : Transcendental Ω X.jK := by
  have h1 : (X.exp X.jK).coeff (-1) ≠ 0 := by rw [X.j_exp.1]; exact one_ne_zero
  have hne : X.exp X.jK ≠ 0 := fun h => h1 (by rw [h]; rfl)
  have hord : (X.exp X.jK).order < 0 :=
    lt_of_le_of_lt (HahnSeries.order_le_of_coeff_ne_zero h1) (by norm_num)
  exact fun h => hahn_transcendental hne hord (h.algHom X.exp)

def levConst (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Ω →+* lev X Γ' :=
  (algebraMap Ω X.K).codRestrict (lev X Γ') (algebraMap_mem_lev X Γ')

def jPoly (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Polynomial Ω →+* lev X Γ' :=
  Polynomial.eval₂RingHom (levConst X Γ') ⟨X.jK, jK_mem_lev X Γ'⟩

theorem coe_jPoly (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (P : Polynomial Ω) :
    ((jPoly X Γ' P : lev X Γ') : X.K) = Polynomial.aeval X.jK P := by
  change (lev X Γ').subtype (Polynomial.eval₂ (levConst X Γ') ⟨X.jK, jK_mem_lev X Γ'⟩ P) = _
  rw [Polynomial.hom_eval₂, Polynomial.aeval_def]
  rfl

theorem jPoly_injective (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Function.Injective (jPoly X Γ') := by
  refine (injective_iff_map_eq_zero _).2 fun P hP => ?_
  have h : Polynomial.aeval X.jK P = 0 := by
    rw [← coe_jPoly, hP]; rfl
  by_contra hne
  exact jK_transcendental X ⟨P, hne, h⟩

def jRat (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : RatFunc Ω →+* lev X Γ' :=
  RatFunc.liftRingHom (jPoly X Γ') (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (jPoly_injective X Γ'))

theorem jRat_algebraMap (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (P : Polynomial Ω) :
    jRat X Γ' (algebraMap (Polynomial Ω) (RatFunc Ω) P) = jPoly X Γ' P := RatFunc.liftRingHom_algebraMap _ _ P

theorem exp_injective (X : Tower Ω ε) : Function.Injective X.exp := (X.exp : X.K →+* HahnSeries ℚ Ω).injective

theorem exp_algebraMap_coeff (X : Tower Ω ε) (c : Ω) (r : ℚ) :
    (X.exp (algebraMap Ω X.K c)).coeff r = if r = 0 then c else 0 := by
  rw [AlgHom.commutes, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HahnSeries.ofPowerSeries_C]
  change (HahnSeries.single (0 : ℚ) c).coeff r = _
  split_ifs with h
  · rw [h]
    exact HahnSeries.coeff_single_same _ _
  · exact HahnSeries.coeff_single_of_ne h

theorem gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply exp_injective X
  ext r
  rw [X.gal_exp, exp_algebraMap_coeff, exp_algebraMap_coeff]
  split_ifs <;> simp

theorem gal_jK (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply exp_injective X
  ext r
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [X.gal_exp, hn, map_intCast]

theorem mem_mdl_iff (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) (f : X.K) :
    f ∈ mdl X Γ' S ↔ f ∈ lev X Γ' ∧ ∀ s ∈ S, X.gal s f = f := by
  unfold mdl
  simp only [Subfield.mem_inf, Subfield.mem_iInf, RingHom.mem_eqLocusField]
  rfl

theorem algebraMap_mem_mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) (c : Ω)
    (hc : ∀ s ∈ S, s c = c) : algebraMap Ω X.K c ∈ mdl X Γ' S := (mem_mdl_iff X Γ' S _).2 ⟨algebraMap_mem_lev X Γ' c, fun s hs => by rw [gal_algebraMap, hc s hs]⟩

theorem jK_mem_mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : X.jK ∈ mdl X Γ' S := (mem_mdl_iff X Γ' S _).2 ⟨jK_mem_lev X Γ', fun s _ => gal_jK X s⟩

theorem coe_jRat_X (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : ((jRat X Γ' RatFunc.X : lev X Γ') : X.K) = X.jK := by
  rw [← RatFunc.algebraMap_X, jRat_algebraMap, coe_jPoly, Polynomial.aeval_X]

def algConst (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Algebra Ω (lev X Γ') := (levConst X Γ').toAlgebra

def algPoly (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Algebra (Polynomial Ω) (lev X Γ') := (jPoly X Γ').toAlgebra

def algRat (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Algebra (RatFunc Ω) (lev X Γ') := (jRat X Γ').toAlgebra

def algMdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : Algebra (mdl X Γ' S) (lev X Γ') :=
  (Subfield.inclusion (mdl_le_lev X Γ' S)).toAlgebra

section Instances

attribute [local instance] algConst algPoly algRat algMdl

theorem isScalarTower_poly_rat (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) :
    IsScalarTower (Polynomial Ω) (RatFunc Ω) (lev X Γ') := IsScalarTower.of_algebraMap_eq fun P => (jRat_algebraMap X Γ' P).symm

theorem isScalarTower_mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
    IsScalarTower (mdl X Γ' S) (lev X Γ') X.K := IsScalarTower.of_algebraMap_eq fun _ => rfl

example (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) :
    ((algebraMap (RatFunc Ω) (lev X Γ') RatFunc.X : lev X Γ') : X.K) = X.jK :=
  coe_jRat_X X Γ'

example (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (c : Ω) :
    ((algebraMap Ω (lev X Γ') c : lev X Γ') : X.K) = algebraMap Ω X.K c := rfl

example (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) :
    ((algebraMap (RatFunc Ω) (lev X Γ') RatFunc.X⁻¹ : lev X Γ') : X.K) = X.jK⁻¹ := by
  rw [map_inv₀, Subfield.coe_inv]
  show ((jRat X Γ' RatFunc.X : lev X Γ') : X.K)⁻¹ = _
  rw [coe_jRat_X]

example (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) (x : mdl X Γ' S) :
    ((algebraMap (mdl X Γ' S) (lev X Γ') x : lev X Γ') : X.K) = x := rfl

example (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) :
    algebraMap (Polynomial Ω) (lev X Γ') (Polynomial.X ^ 2 - Polynomial.C 1) ≠ 0 := by
  rw [← map_zero (algebraMap (Polynomial Ω) (lev X Γ'))]
  intro h
  have := jPoly_injective X Γ' h
  have h2 := congrArg (Polynomial.natDegree) this
  rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_zero] at h2
  exact absurd h2 (by norm_num)

end Instances

end GlobalTheory.K4
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
section
noncomputable section

namespace GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

def IntegralLocallyConstCochainModPow (k : ℕ) (H : Subgroup (Gal p Ω)) (w : Gal p Ω → Ω) : Prop :=
  (∀ g ∈ H, IsInt p (w g)) ∧ ∀ g ∈ H, ∃ S : Finset Ω, ∀ h ∈ H, (∀ x ∈ S, h x = g x) → Cong p k (w h) (w g)

def LocallyConstantTwoCochainOn (k : ℕ) (H : Subgroup (Gal p Ω)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  (∀ g ∈ H, ∀ h ∈ H, IsInt p (ξ g h)) ∧ ∀ g ∈ H, ∀ h ∈ H, ∃ S : Finset Ω, ∀ g' ∈ H, ∀ h' ∈ H,
    (∀ x ∈ S, g' x = g x ∧ h' x = h x) → Cong p k (ξ g' h') (ξ g h)

def IsTwistedOneCocycle (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (c : Gal p Ω → Ω) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, Cong p k (c (g * h)) (c g + ((χ g).val : Ω) ^ j * g (c h))

def IsTwistedOneCoboundary (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (c : Gal p Ω → Ω) : Prop :=
  ∃ x : Ω, IsInt p x ∧ ∀ g ∈ H, Cong p k (c g) (((χ g).val : Ω) ^ j * g x - x)

def IsTwistedTwoCocycle' (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, ∀ t ∈ H,
    Cong p k (((χ g).val : Ω) ^ j * g (ξ h t) + ξ g (h * t)) (ξ (g * h) t + ξ g h)

def IsTwistedTwoCoboundary' (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∃ w : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k H w ∧ ∀ g ∈ H, ∀ h ∈ H,
    Cong p k (ξ g h) (((χ g).val : Ω) ^ j * g (w h) - w (g * h) + w g)

variable (p) in

def plogQ (m k a : ℕ) : ZMod (p ^ k) :=
  ∑ i ∈ Finset.Icc 1 (2 * k + 2), (-1 : ZMod (p ^ k)) ^ (i + 1) *
    (p : ZMod (p ^ k)) ^ (m * (i - 1) - padicValNat p i) *
    ((i / p ^ padicValNat p i : ℕ) : ZMod (p ^ k))⁻¹ * (a : ZMod (p ^ k)) ^ i

def IsLam (T : Tower p Ω) (m k : ℕ) (H : Subgroup (Gal p Ω)) (lam : Gal p Ω → ZMod (p ^ k)) : Prop :=
  1 ≤ m ∧ ∃ a : Gal p Ω → ZMod (p ^ k), IsKum T k H (T.ζ (m + k)) a ∧ ∀ g ∈ H, lam g = plogQ p m k (a g).val

end GlobalTheory.K5
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise

namespace GlobalTheory.HL

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def hf (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  ∑ i, ∑ j, x i * Hm i j * L.cj (y j)

def cT (L : LocE F E) {m n : Type} (A : Matrix m n E) : Matrix n m E := fun i j => L.cj (A j i)

def IsHerm (L : LocE F E) {m : Type} (A : Matrix m m E) : Prop := cT L A = A

def IsHermND (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) : Prop :=
  IsHerm L Hm ∧ IsUnit Hm.det

def IsIntM (L : LocE F E) {m n : Type} (A : Matrix m n E) : Prop := ∀ i j, A i j ∈ L.O

def perp (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Y : Submodule E (Fin n → E)) :
    Submodule E (Fin n → E) where
  carrier := {x | ∀ y ∈ Y, hf L Hm x y = 0}
  zero_mem' := by intro y _; simp [hf]
  add_mem' := by
    intro a b ha hb y hy
    have h : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
      simp [hf, add_mul, Finset.sum_add_distrib]
    rw [h, ha y hy, hb y hy, add_zero]
  smul_mem' := by
    intro c a ha y hy
    have h : hf L Hm (c • a) y = c * hf L Hm a y := by
      simp [hf, Finset.mul_sum, mul_assoc]
    rw [h, ha y hy, mul_zero]

def IsLat (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) : Prop :=
  Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤

def IsSD (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Λ : Submodule L.O (Fin n → E)) : Prop :=
  IsLat L Λ ∧ ∀ y, (∀ x ∈ Λ, hf L Hm x y ∈ L.O) ↔ y ∈ Λ

def isomG (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) :
    Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) where
  carrier := {g | ∀ x y, hf L Hm (g x) (g y) = hf L Hm x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb x y
    exact (ha (b x) (b y)).trans (hb x y)
  inv_mem' := by
    intro a ha x y
    have h := ha (a.symm x) (a.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h.symm

def unipOn {n : ℕ} (A B : Submodule E (Fin n → E)) : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) where
  carrier := {g | (∀ v, g v ∈ A ↔ v ∈ A) ∧ ∀ v ∈ A, g v - v ∈ B}
  one_mem' := ⟨fun _ => Iff.rfl, fun v _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun v => (ha (b v)).trans (hb v), fun v hv => ?_⟩
    have h : (a * b) v - v = (a (b v) - b v) + (b v - v) := by simp
    rw [h]
    exact B.add_mem (ha' _ ((hb v).2 hv)) (hb' v hv)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ∀ v, a.symm v ∈ A ↔ v ∈ A := fun v => by
      have := ha (a.symm v)
      simp only [LinearEquiv.apply_symm_apply] at this
      exact this.symm
    refine ⟨h1, fun v hv => ?_⟩
    have h2 := ha' _ ((h1 v).2 hv)
    simp only [LinearEquiv.apply_symm_apply] at h2
    have h3 : a⁻¹ v - v = -(v - a.symm v) := by
      rw [neg_sub]; rfl
    rw [h3]
    exact B.neg_mem h2

def eich (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x u : Fin n → E) (s : E)
    (v : Fin n → E) : Fin n → E :=
  v + hf L Hm v u • x - hf L Hm v x • (u + s • x)

def invVol {G : Type*} [Group G] (K0 K : Subgroup G) : ℝ :=
  (K.relIndex K0 : ℝ) / (K0.relIndex K : ℝ)

def resQ (ϖ : 𝒪[F]) : ℕ := Nat.card (𝒪[F] ⧸ Ideal.span {ϖ})

def vE (L : LocE F E) (ϖ : 𝒪[F]) (c : E) : ℤ :=
  sSup {m : ℤ | ∃ y ∈ L.O, c = algebraMap F E ((ϖ : F) ^ m) * y}

def lead {N : ℕ} (Z : Matrix (Fin N) (Fin N) E) (l : Fin (N + 1)) : E :=
  (Z.submatrix (Fin.castLE (Nat.lt_succ_iff.mp l.2)) (Fin.castLE (Nat.lt_succ_iff.mp l.2))).det

end GlobalTheory.HL
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.RepL
section
noncomputable section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

abbrev M2 : Type := Matrix (Fin 2) (Fin 2) ℤ

def slz (k : ℕ) (δ : M2) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  ((δ.det : ℤ) : ℂ) ^ (k - 1) * ((((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹ *
    f (ofComplex ((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ))))

def LRep (L : ℕ) (Δ : Set M2) {ι : Type} (β : ι → M2) : Prop :=
  Set.BijOn (fun p : Gamma0 L × ι => ((p.1 : SL(2, ℤ)) : M2) * β p.2) Set.univ Δ

def RRep (L : ℕ) (Δ : Set M2) {κ : Type} (α : κ → M2) : Prop :=
  Set.BijOn (fun p : κ × Gamma0 L => α p.1 * ((p.2 : SL(2, ℤ)) : M2)) Set.univ Δ

def hsum (k : ℕ) (ε : ℤ → ℂ) {ι : Type} [Fintype ι] (β : ι → M2) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  ∑ i, ε (β i 0 0) * slz k (β i) f τ

def DT (L q : ℕ) : Set M2 := {δ | δ.det = q ∧ (L : ℤ) ∣ δ 1 0}

def DU (L l : ℕ) : Set M2 := {δ | δ.det = l ∧ (L : ℤ) ∣ δ 1 0 ∧ ¬ (l : ℤ) ∣ δ 0 0}

def repU (q : ℕ) (j : Fin q) : M2 := !![1, (j : ℕ); 0, q]

def repT (q : ℕ) : Option (Fin q) → M2
  | some j => repU q j
  | none => !![q, 0; 0, 1]

def repL (L q : ℕ) : Option (Fin q) → M2
  | some j => !![q, 0; L * (j : ℕ), 1]
  | none => !![1, 0; 0, q]

def Mod (F : ℍ → ℂ) : Prop := ∃ (C : ℝ) (A : ℕ), ∀ τ : ℍ, ‖F τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹)

def latF (L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) : ℤ × ℤ → ℂ := fun x => if (L : ℤ) ∣ x.1 then b (x.1 / L) * φ (x.2 : ZMod L) else 0

def Kills (L : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) : Prop := ∀ x, ∑ r ∈ Finset.range L, Φ (x - (r : ℤ) • v) = 0

def strip : Set ℍ := {τ | 0 ≤ τ.re ∧ τ.re < 1}

end GlobalTheory.EisM

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.SgC
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.KZ

def sgC (c : ℕ) (x : Fin 2 → ℚ) (z : ℂ) : ℂ := GlobalTheory.Sieg.sg c x (UpperHalfPlane.ofComplex z)

open Classical in

def siegel {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ) : T.K :=
  if h : ∃ f : T.K, T.an f = ((sgC c x : ℂ → ℂ) : Mero) then h.choose else 0

end GlobalTheory.KZ
end
end

