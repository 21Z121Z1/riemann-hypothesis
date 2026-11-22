import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0083
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Formalism.LocalToGlobal.Divisibility.RowSideTie
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0082
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjInertiaTameCharOtherPlace
section
open NumberField IsDedekindDomain

open Pointwise

namespace GlobalTheory.TameMove

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem val_smul_lt_one_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G E Ω) (y : Ω) :
    (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 := by
  have h1 : ∀ z : Ω, g z ∈ g • A ↔ z ∈ A := by
    intro z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', h1, ← map_inv₀, h1,
    map_eq_zero_iff _ g.injective]

theorem val_smul_le_one_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G E Ω) (y : Ω) :
    (g • A).valuation (g y) ≤ 1 ↔ A.valuation y ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem conj_mem_Ine_smul {A : ValuationSubring Ω} {g σ : Formalism.ConjugateSelfDual.G E Ω}
    (hσ : σ ∈ ReciprocityTheory.Gal.Ine (F := E) A) : g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) (g • A) := by
  refine ⟨?_, fun x hx => ?_⟩
  · show (g * σ * g⁻¹) • (g • A) = g • A
    have h : σ • A = A := hσ.1
    rw [← mul_smul, inv_mul_cancel_right, mul_smul, h]
  · have hy : A.valuation (g⁻¹ x) ≤ 1 := by
      rw [← val_smul_le_one_iff A g, ReciprocityTheory.Gal.mul_inv_apply]; exact hx
    have e : (g * σ * g⁻¹) x - x = g (σ (g⁻¹ x) - g⁻¹ x) := by
      rw [map_sub, ReciprocityTheory.Gal.mul_inv_apply]; rfl
    rw [e, val_smul_lt_one_iff]
    exact hσ.2 _ hy

theorem exists_mul_eq_of_not_mem_sq (P : HeightOneSpectrum (𝓞 E)) {ϖ ϖ₀ : 𝓞 E}
    (h₀ : ϖ₀ ∈ P.asIdeal) (h : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    ∃ s t : 𝓞 E, s ∉ P.asIdeal ∧ s * ϖ₀ = t * ϖ := by
  have hle : Ideal.span {ϖ} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr h
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr hle
  have hIP : ¬ I ≤ P.asIdeal := by
    intro hIP
    apply h2
    have : Ideal.span {ϖ} ≤ P.asIdeal ^ 2 := by
      rw [hI, pow_two]; exact Ideal.mul_mono_right hIP
    exact this (Ideal.mem_span_singleton_self ϖ)
  obtain ⟨s, hsI, hsP⟩ := Set.not_subset.mp hIP
  have hm : s * ϖ₀ ∈ Ideal.span {ϖ} := by
    rw [hI, mul_comm s]; exact Ideal.mul_mem_mul h₀ hsI
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
  exact ⟨s, t, hsP, ht.symm⟩

theorem val_le_one (A : ValuationSubring Ω) (t : 𝓞 E) : A.valuation (algebraMap E Ω (t : E)) ≤ 1 := by
  rw [A.valuation_le_one_iff]
  apply ReciprocityTheory.Gal.mem_of_isIntegral_int
  exact (NumberField.RingOfIntegers.isIntegral_coe t).map (algebraMap E Ω).toIntAlgHom

theorem val_eq_of_not_mem_sq (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E))
    (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P) {ϖ ϖ₀ : 𝓞 E} (h : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (h₀ : ϖ₀ ∈ P.asIdeal) (h02 : ϖ₀ ∉ P.asIdeal ^ 2) :
    A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation (algebraMap E Ω (ϖ₀ : E)) := by
  have key : ∀ a b : 𝓞 E, a ∈ P.asIdeal → b ∈ P.asIdeal → b ∉ P.asIdeal ^ 2 →
      A.valuation (algebraMap E Ω (a : E)) ≤ A.valuation (algebraMap E Ω (b : E)) := by
    intro a b ha hb hb2
    obtain ⟨s, t, hs, hst⟩ := exists_mul_eq_of_not_mem_sq P ha hb hb2
    have hvs : A.valuation (algebraMap E Ω (s : E)) = 1 :=
      le_antisymm (val_le_one A s) (not_lt.mp fun hlt => hs ((hA s).mp hlt))
    have e : algebraMap E Ω (s : E) * algebraMap E Ω (a : E) =
        algebraMap E Ω (t : E) * algebraMap E Ω (b : E) := by
      have := congrArg (fun z : 𝓞 E => algebraMap E Ω (z : E)) hst
      simpa using this
    have e2 := congrArg A.valuation e
    rw [Valuation.map_mul, Valuation.map_mul, hvs, one_mul] at e2
    rw [e2]
    calc A.valuation (algebraMap E Ω (t : E)) * A.valuation (algebraMap E Ω (b : E))
        ≤ 1 * A.valuation (algebraMap E Ω (b : E)) := mul_le_mul_left (val_le_one A t) _
      _ = _ := one_mul _
  exact le_antisymm (key _ _ h h₀ h02) (key _ _ h₀ h h2)

end GlobalTheory.TameMove

open Pointwise

namespace GlobalTheory.TameMove

theorem tameRep_move : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (A₀ : ValuationSubring Ω) (ϖ₀ : 𝓞 E) (π₀ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A₀ P → ϖ₀ ∈ P.asIdeal → ϖ₀ ∉ P.asIdeal ^ 2 →
    π₀ ^ (Formalism.ConjugateSelfDual.normV P - 1) = algebraMap E Ω (ϖ₀ : E) → Formalism.L2.NX.TameRep P e σ u →
    ∃ g : Formalism.ConjugateSelfDual.G E Ω, g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A₀ ∧
      A₀.valuation ((g * σ * g⁻¹) π₀ / π₀ - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  intro E Ω _ _ _ _ _ P e σ u A₀ ϖ₀ π₀ hA₀ h₀ h02 hπ₀ hT
  obtain ⟨A, hA, hσ, ϖ, π, h, h2, hπ, hv⟩ := hT
  obtain ⟨g, rfl⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_isPlaceOver hA hA₀
  have hσ'I : g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) (g • A) := conj_mem_Ine_smul hσ
  refine ⟨g, hσ'I, ?_⟩
  set B := g • A with hB
  set σ' := g * σ * g⁻¹ with hσ'
  set N := Formalism.ConjugateSelfDual.normV P - 1 with hN
  set U := (algebraMap E Ω (u : E)) ^ e with hU
  have hne : ∀ b : 𝓞 E, b ∉ P.asIdeal ^ 2 → algebraMap E Ω (b : E) ≠ 0 := by
    intro b hb hz
    apply hb
    have hb0 : b = 0 := by
      have : (b : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).mp hz
      exact_mod_cast this
    rw [hb0]; exact Ideal.zero_mem _
  have hw : algebraMap E Ω (ϖ : E) ≠ 0 := hne ϖ h2
  have hw₀ : algebraMap E Ω (ϖ₀ : E) ≠ 0 := hne ϖ₀ h02
  have hN0 : N ≠ 0 := by
    intro hz
    rw [hz, pow_zero] at hπ₀
    have := (hA₀ ϖ₀).mpr h₀
    rw [← hπ₀, map_one] at this
    exact lt_irrefl _ this
  have hπ₀0 : π₀ ≠ 0 := by
    rintro rfl; rw [zero_pow hN0] at hπ₀; exact hw₀ hπ₀.symm

  have hπ' : (g π) ^ N = algebraMap E Ω (ϖ : E) := by
    rw [← map_pow, hπ]; exact AlgEquiv.commutes g _
  have hπ'0 : g π ≠ 0 := by
    intro hz; rw [hz, zero_pow hN0] at hπ'; exact hw hπ'.symm
  have hgg : g⁻¹ (g π) = π := by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have ha : B.valuation (σ' (g π) / g π - U) < 1 := by
    have e1 : σ' (g π) / g π - U = g (σ π / π - U) := by
      have e2 : σ' (g π) = g (σ π) := by
        show g (σ (g⁻¹ (g π))) = g (σ π)
        rw [hgg]
      have e3 : g U = U := by
        rw [hU, map_zpow₀]; congr 1; exact AlgEquiv.commutes g _
      rw [map_sub, map_div₀, e2, e3]
    rw [e1, hB, val_smul_lt_one_iff]; exact hv

  set x := g π / π₀ with hx
  have hxπ : g π = x * π₀ := by rw [hx, div_mul_cancel₀ _ hπ₀0]
  have hx0 : x ≠ 0 := div_ne_zero hπ'0 hπ₀0
  have hvx : B.valuation x = 1 := by
    have hxN : x ^ N = algebraMap E Ω (ϖ : E) / algebraMap E Ω (ϖ₀ : E) := by
      rw [hx, div_pow, hπ', hπ₀]
    have hvN : B.valuation x ^ N = 1 := by
      rw [← Valuation.map_pow, hxN, map_div₀, val_eq_of_not_mem_sq B P hA₀ h h2 h₀ h02,
        div_self ((Valuation.ne_zero_iff _).mpr hw₀)]
    rcases lt_trichotomy (B.valuation x) 1 with h1 | h1 | h1
    · exact absurd hvN (pow_lt_one₀ zero_le h1 hN0).ne
    · exact h1
    · exact absurd hvN (one_lt_pow₀ h1 hN0).ne'
  have hc : B.valuation (σ' x / x - 1) < 1 := by
    have e : σ' x / x - 1 = (σ' x - x) / x := by field_simp
    rw [e, map_div₀, hvx, div_one]
    exact hσ'I.2 x hvx.le

  have hb : (σ' π₀ / π₀) ^ N = 1 := by
    rw [div_pow, ← map_pow, hπ₀, AlgEquiv.commutes, div_self hw₀]
  have hvb : B.valuation (σ' π₀ / π₀) = 1 := ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one B hN0 hb
  have hprod : σ' (g π) / g π = (σ' x / x) * (σ' π₀ / π₀) := by
    rw [hxπ, map_mul]; field_simp
  have e4 : σ' π₀ / π₀ - U = (σ' (g π) / g π - U) + -((σ' x / x - 1) * (σ' π₀ / π₀)) := by
    rw [hprod]; ring
  rw [e4]
  refine Valuation.map_add_lt _ ha ?_
  rw [Valuation.map_neg, Valuation.map_mul, hvb, mul_one]
  exact hc

end GlobalTheory.TameMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFormsTieOLatTie
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef
open scoped ComplexOrder

open scoped Matrix MatrixOrder

namespace GlobalTheory.Mem.CoordForms

theorem exists_sqrt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    ∃ S T : Matrix (Fin n) (Fin n) ℂ, Sᴴ * S = A ∧ S * T = 1 ∧ T * S = 1 := by
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose] at hS
  have hdet : IsUnit S.det := by
    have h := hA.det_pos.ne'
    rw [hS, Matrix.det_mul] at h
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h)
  exact ⟨S, S⁻¹, hS.symm, Matrix.mul_nonsing_inv S hdet, Matrix.nonsing_inv_mul S hdet⟩

variable {K : Type} [Field K] {n : ℕ}

noncomputable def emb (σ : K →+* ℂ) (S : Matrix (Fin n) (Fin n) ℂ) : (Fin n → K) →ₛₗ[σ] EuclideanSpace ℂ (Fin n) where
  toFun x := Matrix.toEuclideanLin S (WithLp.toLp 2 fun i => σ (x i))
  map_add' x y := by
    rw [← map_add]
    congr 1
    ext i
    simp
  map_smul' a x := by
    rw [← map_smul]
    congr 1
    ext i
    simp

theorem emb_ofLp (σ : K →+* ℂ) (S : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → K) :
    (emb σ S x).ofLp = S *ᵥ fun i => σ (x i) := rfl

noncomputable def act (σ : K →+* ℂ) (S T : Matrix (Fin n) (Fin n) ℂ) (h1 : S * T = 1) (h2 : T * S = 1) :
    Matrix (Fin n) (Fin n) K →+* Module.End ℂ (EuclideanSpace ℂ (Fin n)) where
  toFun E := Matrix.toEuclideanLin (S * E.map σ * T)
  map_one' := by
    ext1 v
    apply WithLp.ofLp_injective
    change (S * (1 : Matrix (Fin n) (Fin n) K).map σ * T) *ᵥ v.ofLp = v.ofLp
    rw [Matrix.map_one _ (map_zero σ) (map_one σ), mul_one, h1, Matrix.one_mulVec]
  map_mul' E F := by
    ext1 v
    apply WithLp.ofLp_injective
    change (S * (E * F).map σ * T) *ᵥ v.ofLp = (S * E.map σ * T) *ᵥ ((S * F.map σ * T) *ᵥ v.ofLp)
    rw [Matrix.mulVec_mulVec, Matrix.map_mul]
    congr 1
    calc S * (E.map σ * F.map σ) * T = S * E.map σ * (T * S) * F.map σ * T := by rw [h2]; simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]
  map_zero' := by simp
  map_add' E F := by
    rw [← map_add, Matrix.map_add _ (map_add σ), mul_add, add_mul]

theorem emb_single (σ : K →+* ℂ) (S : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    emb σ S (Pi.single i 1) = Matrix.toEuclideanLin S (EuclideanSpace.basisFun (Fin n) ℂ i) := by
  apply WithLp.ofLp_injective
  change S *ᵥ (fun k => σ ((Pi.single i (1 : K) : Fin n → K) k)) = S *ᵥ (EuclideanSpace.basisFun (Fin n) ℂ i).ofLp
  congr 1
  ext k
  rw [EuclideanSpace.basisFun_apply]
  by_cases h : k = i
  · subst h; simp
  · simp [h]

theorem bij (S T : Matrix (Fin n) (Fin n) ℂ) (h1 : S * T = 1) (h2 : T * S = 1) :
    Function.Bijective (Matrix.toEuclideanLin S) := by
  constructor
  · intro x y hxy
    have h := congrArg (fun v => (Matrix.toEuclideanLin T v).ofLp) hxy
    change T *ᵥ (S *ᵥ x.ofLp) = T *ᵥ (S *ᵥ y.ofLp) at h
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.one_mulVec] at h
    exact WithLp.ofLp_injective 2 h
  · intro y
    refine ⟨Matrix.toEuclideanLin T y, WithLp.ofLp_injective 2 ?_⟩
    change S *ᵥ (T *ᵥ y.ofLp) = y.ofLp
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem emb_injective (σ : K →+* ℂ) (S T : Matrix (Fin n) (Fin n) ℂ) (h1 : S * T = 1) (h2 : T * S = 1) :
    Function.Injective (emb σ S) := by
  intro x y hxy
  have h : (WithLp.toLp 2 fun i => σ (x i) : EuclideanSpace ℂ (Fin n)) = WithLp.toLp 2 fun i => σ (y i) :=
    (bij S T h1 h2).1 (show Matrix.toEuclideanLin S (WithLp.toLp 2 fun i => σ (x i)) =
      Matrix.toEuclideanLin S (WithLp.toLp 2 fun i => σ (y i)) from hxy)
  funext i
  exact σ.injective (congrFun (congrArg WithLp.ofLp h) i)

theorem emb_span (σ : K →+* ℂ) (S T : Matrix (Fin n) (Fin n) ℂ) (h1 : S * T = 1) (h2 : T * S = 1) :
    Submodule.span ℂ (Set.range fun i => emb σ S (Pi.single i 1)) = ⊤ := by
  have hs : (fun i => emb σ S (Pi.single i 1)) =
      (Matrix.toEuclideanLin S) ∘ (EuclideanSpace.basisFun (Fin n) ℂ) :=
    funext (emb_single σ S)
  rw [hs, Set.range_comp, Submodule.span_image, ← OrthonormalBasis.coe_toBasis, Module.Basis.span_eq,
    Submodule.map_top, LinearMap.range_eq_top]
  exact (bij S T h1 h2).2

theorem formsTie [NumberField K] [StarRing K] (σ : K →+* ℂ) (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x))
    (H : Matrix (Fin n) (Fin n) K) (S T : Matrix (Fin n) (Fin n) ℂ) (h0 : Sᴴ * S = H.map σ) (h1 : S * T = 1)
    (h2 : T * S = 1) (E : Matrix (Fin n) (Fin n) K) : FormsTie σ (emb σ S) H E (act σ S T h1 h2 E) where
  li := by
    rw [show (fun i => emb σ S (Pi.single i 1)) =
        (Matrix.toEuclideanLin S) ∘ (EuclideanSpace.basisFun (Fin n) ℂ) from funext (emb_single σ S)]
    exact (EuclideanSpace.basisFun (Fin n) ℂ).orthonormal.linearIndependent.map'
      _ (LinearMap.ker_eq_bot.mpr (bij S T h1 h2).1)
  span := emb_span σ S T h1 h2
  inner x y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, emb_ofLp, emb_ofLp, Matrix.star_mulVec, dotProduct_comm,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h0]
    simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, map_sum, map_mul, smul_eq_mul, dotProduct,
      Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Matrix.map_apply, RingHom.id_apply, starRingEnd_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [hσ, starRingEnd_apply]
    ring
  op_eq x := by
    apply WithLp.ofLp_injective
    change (S * E.map σ * T) *ᵥ (S *ᵥ fun i => σ (x i)) = S *ᵥ fun i => σ ((E *ᵥ x) i)
    rw [Matrix.mulVec_mulVec, mul_assoc (S * E.map σ), h2, mul_one, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    exact (RingHom.map_mulVec σ E x i).symm

theorem exists_lat [NumberField K] {O : Type} [CommRing O] (o : O →+* K) (σ : K →+* ℂ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (j : (Fin n → K) →ₛₗ[σ] W) (hj : Function.Injective j)
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤)
    (N : Submodule (𝓞 K) (Fin n → K)) (hN : Submodule.IsLattice K N) :
    ∃ M : Rows.OLat O (σ.comp o) W, OLatTie σ M j N ∧
      ((∀ y, IsIntegral ℤ (o y)) → (M.carrier : Set W) = j '' (N : Set (Fin n → K))) := by
  classical

  obtain ⟨G, hG⟩ := hN.fg.restrictScalars (R := ℤ)
  have hGN : ∀ g ∈ G, g ∈ N := fun g hg => by
    have : g ∈ Submodule.span ℤ (G : Set (Fin n → K)) := Submodule.subset_span hg
    rw [hG] at this
    exact this

  have hsum : ∀ φ : W → ℂ, ∑ v ∈ G.image j, φ v • v = ∑ g ∈ G, φ (j g) • j g := fun φ =>
    Finset.sum_image fun a _ b _ h => hj h

  have key : ∀ y ∈ Submodule.span K (G : Set (Fin n → K)),
      j y ∈ Submodule.span ℂ ((G.image j : Finset W) : Set W) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem j (Finset.mem_coe.mp hx)))
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  have hGK : Submodule.span K (G : Set (Fin n → K)) = ⊤ := by
    rw [eq_top_iff, ← hN.span_eq_top, Submodule.span_le]
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (G : Set (Fin n → K)) := by rw [hG]; exact hx
    exact Submodule.span_le_restrictScalars ℤ K _ hx'
  have hspan : Submodule.span ℂ ((G.image j : Finset W) : Set W) = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact key _ (hGK ▸ Submodule.mem_top)

  have hZ : ∀ x ∈ N, ∃ f : (Fin n → K) → ℤ, j x = ∑ g ∈ G, (f g : ℂ) • j g := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (G : Set (Fin n → K)) := by rw [hG]; exact hx
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hx'
    refine ⟨f, ?_⟩
    rw [← hf, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]

  have hcomb : ∀ a : (Fin n → K) → K, ∑ g ∈ G, σ (a g) • j g = j (∑ g ∈ G, a g • g) := fun a => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun g _ => (LinearMap.map_smulₛₗ j (a g) g).symm
  refine ⟨⟨G.image j, hspan⟩, ⟨fun v hv => ?_, fun x => ⟨fun hx => ?_, fun ⟨c, hc⟩ => ?_⟩⟩, fun hint => ?_⟩
  · obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨g, rfl⟩
  · obtain ⟨f, hf⟩ := hZ x hx
    refine ⟨fun w => (f (Function.invFun j w) : 𝓞 K), ?_⟩
    change j x = ∑ v ∈ G.image j, σ ((f (Function.invFun j v) : 𝓞 K) : K) • v
    rw [hsum, hf]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Function.leftInverse_invFun hj g]
    simp
  · change j x = ∑ v ∈ G.image j, σ (c v : K) • v at hc
    rw [hsum, hcomb] at hc
    rw [hj hc]
    refine Submodule.sum_mem _ fun g hg => ?_
    have hm := N.smul_mem (c (j g)) (hGN g hg)
    rwa [← algebraMap_smul K (c (j g)) g] at hm
  · ext w
    constructor
    · rintro ⟨c, rfl⟩
      let a : (Fin n → K) → 𝓞 K := fun g => ⟨o (c (j g)), hint _⟩
      refine ⟨∑ g ∈ G, (a g : K) • g, ?_, ?_⟩
      · refine Submodule.sum_mem _ fun g hg => ?_
        have hm := N.smul_mem (a g) (hGN g hg)
        rwa [← algebraMap_smul K (a g) g] at hm
      · change j (∑ g ∈ G, (a g : K) • g) = ∑ v ∈ G.image j, σ (o (c v)) • v
        rw [hsum, ← hcomb]
        rfl
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨f, hf⟩ := hZ x hx
      refine ⟨fun w => (f (Function.invFun j w) : O), ?_⟩
      change j x = ∑ v ∈ G.image j, σ (o (f (Function.invFun j v) : O)) • v
      rw [hsum, hf]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Function.leftInverse_invFun hj g]
      simp

theorem exists_formsTie_oLatTie : ∀ (K O : Type) [Field K] [NumberField K] [StarRing K] [CommRing O] (o : O →+* K) (σ : K →+* ℂ) (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (N : Submodule (𝓞 K) (Fin n → K)), (∀ x, σ (star x) = starRingEnd ℂ (σ x)) → (H.map σ).PosDef → Submodule.IsLattice K N → ∃ (j : (Fin n → K) →ₛₗ[σ] EuclideanSpace ℂ (Fin n)) (M : Rows.OLat O (σ.comp o) (EuclideanSpace ℂ (Fin n))) (ρ : Matrix (Fin n) (Fin n) K →+* Module.End ℂ (EuclideanSpace ℂ (Fin n))), (∀ E, FormsTie σ j H E (ρ E)) ∧ OLatTie σ M j N ∧ ((∀ y, IsIntegral ℤ (o y)) → (M.carrier : Set (EuclideanSpace ℂ (Fin n))) = j '' (N : Set (Fin n → K))) := by
  intro K O _ _ _ _ o σ n H N hσ hH hN
  obtain ⟨S, T, h0, h1, h2⟩ := exists_sqrt (H.map σ) hH
  obtain ⟨M, hM, hcar⟩ := exists_lat o σ (emb σ S) (emb_injective σ S T h1 h2) (emb_span σ S T h1 h2) N hN
  exact ⟨emb σ S, M, act σ S T h1 h2, fun E => formsTie σ hσ H S T h0 h1 h2 E, hM, hcar⟩

end GlobalTheory.Mem.CoordForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHcParamCodeWord
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

def hcParamOfCodeWord (R : Ranks) (G b₀ h : ℕ) (hG : 2 ≤ G) (hh : R.t + 3 ≤ h)
    (c : Fin R.k → Bool) : HCParam R where
  u i := if i.1 = 0 then (G : ℚ) * (R.k - 1) + 1 / 2 else if i.1 = R.k - 1 then (G : ℚ) - 1 / 2
    else if c i then (G : ℚ) * (R.k - i.1) - 1 / 2 else (G : ℚ) * (R.k - 1 - i.1) + 1 / 2
  v i := (G : ℚ) * (R.k - 1 - i.1)
  b j := b₀ + 2 * h * j.1
  e j := b₀ + 2 * h * j.1 + h
  u_gt_v i := by
    have hG' : (2 : ℚ) ≤ G := by exact_mod_cast hG
    have hi := i.2
    dsimp only
    split_ifs with h0 h1 h2
    · rw [h0]; push_cast; linarith
    · omega
    · linarith
    · linarith
  v_gt_u i := by
    have hG' : (2 : ℚ) ≤ G := by exact_mod_cast hG
    have hi := i.2
    dsimp only
    rw [if_neg (Nat.succ_ne_zero i.1)]
    split_ifs with h1 h2
    · have hk : (R.k : ℚ) = (i.1 : ℚ) + 2 := by
        have : R.k = i.1 + 2 := by omega
        exact_mod_cast this
      rw [hk]; linarith
    · push_cast; linarith
    · push_cast; linarith
  u_last_gt h0 h1 := by
    have hG' : (2 : ℚ) ≤ G := by exact_mod_cast hG
    have hb : (0 : ℚ) ≤ b₀ := by positivity
    have hk := R.m_add_three_le_k
    have hne : R.k - 1 ≠ 0 := by omega
    simp only [if_neg hne, if_true]
    push_cast
    linarith
  gap_be j := by
    have hh' : (R.t : ℚ) + 3 ≤ h := by exact_mod_cast hh
    have ht : (0 : ℚ) ≤ R.t := by positivity
    linarith
  gap_eb j hj := by
    have hh' : (R.t : ℚ) + 3 ≤ h := by exact_mod_cast hh
    have ht : (0 : ℚ) ≤ R.t := by positivity
    push_cast
    linarith
  e_int j := ⟨b₀ + 2 * h * j.1 + h, by push_cast; ring⟩
  u_half i := by
    split_ifs
    · exact ⟨G * (R.k - 1), by push_cast; ring⟩
    · exact ⟨G - 1, by push_cast; ring⟩
    · exact ⟨G * (R.k - i.1) - 1, by push_cast; ring⟩
    · exact ⟨G * (R.k - 1 - i.1), by push_cast; ring⟩
  v_int i := ⟨G * (R.k - 1 - i.1), by push_cast; ring⟩
  b_int j := ⟨b₀ + 2 * h * j.1, by push_cast; ring⟩

theorem exists_hcParam_codeWord : ∀ (R : Ranks) (G b₀ h : ℕ), 2 ≤ G → R.t + 3 ≤ h → ∃ P : (Fin R.k → Bool) → HCParam R, (∀ c i, (P c).v i = (G : ℚ) * (R.k - 1 - i.1)) ∧ (∀ c j, (P c).b j = b₀ + 2 * h * j.1) ∧ (∀ c j, (P c).e j = b₀ + 2 * h * j.1 + h) ∧ (∀ c (i : Fin R.k), (P c).u i = if i.1 = 0 then (G : ℚ) * (R.k - 1) + 1 / 2 else if i.1 = R.k - 1 then (G : ℚ) - 1 / 2 else if c i then (G : ℚ) * (R.k - i.1) - 1 / 2 else (G : ℚ) * (R.k - 1 - i.1) + 1 / 2) :=
  fun R G b₀ h hG hh =>
    ⟨hcParamOfCodeWord R G b₀ h hG hh, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsOfSemilinearStatement
section
open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_of_semilinear_alt : ∀ {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K'] {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type} (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (L : B.S.Forms →+ B'.S.Forms),
  (∀ (a : K) (f : B.S.Forms), L (a • f) = φ a • L f) →
  LinearIndependent K' (fun k => L (B.S.basis k)) → ⊤ ≤ Submodule.span K' (Set.range fun k => L (B.S.basis k)) →
  (∀ f g : B.S.Forms, B'.S.csum (L f : B'.S.Cl → B'.S.V) (L g) = φ (B.S.csum f g)) →
  (∀ (g : G) (f : B.S.Forms), B'.r (e g) (L f) = L (B.r g f)) →
  (∀ f' : B'.S.Forms, (∀ c, (f' : B'.S.Cl → B'.S.V) c ∈ B'.S.Nab c) ↔ f' ∈ Submodule.span (𝓞 K') (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c})) →
  Z' = Submodule.span K' (L '' (Z : Set B.S.Forms)) →
  ∃ C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K', Function.Bijective C.mulVec ∧
    Cᴴ * B'.S.H * C = B.S.H.map φ ∧
    (∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ) ∧
    B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) ∧
    B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K))) := by
  first | exact @GlobalTheory.Mem.R3.DefLatBC.forms_of_semilinear | exact GlobalTheory.Mem.R3.DefLatBC.forms_of_semilinear | (intros; apply GlobalTheory.Mem.R3.DefLatBC.forms_of_semilinear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConstituentHarishChandraRepIffPairingNeZeroStatement
section
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0) := by
  first | exact @GlobalTheory.GLq.ConstIff.constituent_hcRep_iff | exact GlobalTheory.GLq.ConstIff.constituent_hcRep_iff | (intros; apply GlobalTheory.GLq.ConstIff.constituent_hcRep_iff <;> assumption)
end

