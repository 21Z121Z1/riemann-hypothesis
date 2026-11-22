import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0083
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0053
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import GroundTheory.LocalFields.Bundle0002
import GroundTheory.AutomorphicForms.HermitianClassification
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0146
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0148
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0093
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0138
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarPartFinrankAddSenWeightsLeRank
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0080
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0149

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorLinearDescentPointOne
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

theorem eta_inv_eq {F : Type} [NormedField F] (x : F) : eta x⁻¹ = eta x := by
  have key : (∃ y : F, ‖x⁻¹‖ = ‖y‖ ^ 2) ↔ ∃ y : F, ‖x‖ = ‖y‖ ^ 2 := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y⁻¹, ?_⟩
      rw [norm_inv] at hy
      rw [norm_inv, inv_pow, ← hy, inv_inv]
    · rintro ⟨y, hy⟩
      exact ⟨y⁻¹, by rw [norm_inv, norm_inv, inv_pow, hy]⟩
  unfold eta
  by_cases h : ∃ y : F, ‖x‖ = ‖y‖ ^ 2
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (key.mp h')), if_neg h]

theorem eta_neg_one_pow {F : Type} [NormedField F] (r : ℕ) : eta ((-1 : F) ^ r) = 1 := by
  unfold eta
  rw [if_pos]
  exact ⟨1, by simp⟩

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem row_pow (hG : A.IsGen τ p) (c : A.K) (n : ℕ) :
    (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c)) ᵥ* (companion p) ^ n =
      fun j : Fin r => Algebra.trace F A.K (τ ^ (j : ℕ) * (τ ^ n * c)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.vecMul_vecMul, ih, ← leftMul_tau A hG, row_mul]
    funext j
    congr 2
    ring

theorem Cm_pt_one (hG : A.IsGen τ p) (lam : F) (a : A.K) :
    Cm (pt A hG lam 1 a) = Algebra.traceMatrix F (bas A hG) * Algebra.leftMulMatrix (bas A hG) a := by
  ext i j
  have h1 : Cm (pt A hG lam 1 a) i j = Algebra.trace F A.K (τ ^ (j : ℕ) * (τ ^ (i : ℕ) * a)) := by
    simp only [Cm, pt, Matrix.of_apply]
    rw [row_pow A hG]
  have h2 := congrFun (row_mul A hG a (τ ^ (i : ℕ))) j
  simp only [Matrix.vecMul, dotProduct] at h2
  rw [h1, Matrix.mul_apply]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, bas_apply]
  rw [mul_comm (τ ^ (i : ℕ)) a, ← h2]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm (τ ^ (i : ℕ))]

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc

theorem omega_pt_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F),
    ∃ κ₀ : ℂ, ∀ a : A.K, IsUnit a → ∀ g : GL (Fin r) F,
      omega (act g (LinDesc.pt A hG lam 1 a)) = κ₀ * eta ((g : Matrix (Fin r) (Fin r) F).det) * A.etaK a := by
  intro F E _ _ _ _ _ A r τ p hG lam
  obtain ⟨hmul, -, -, -⟩ := GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E
  have hnd := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  have hT : (Algebra.traceMatrix F (bas A hG)).det ≠ 0 := by
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (bas A hG)] at hnd
    convert hnd using 2
    ext i j
    rw [Algebra.traceForm_toMatrix, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  refine ⟨eta (Algebra.traceMatrix F (bas A hG)).det, fun a ha g => ?_⟩
  have hL := GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det F r
  have hdet : (g : Matrix (Fin r) (Fin r) F).det * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hg : (g : Matrix (Fin r) (Fin r) F).det ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hginv := eq_inv_of_mul_eq_one_right hdet
  have hna : Algebra.norm F a ≠ 0 := (ha.map (Algebra.norm F)).ne_zero
  have hr : (-1 : F) ^ r ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  unfold omega Et.etaK
  rw [hL.1, hL.2, Cm_pt_one, Matrix.det_mul, Matrix.det_mul, ← Algebra.norm_eq_matrix_det, hginv,
    hmul _ _ hr (mul_ne_zero (mul_ne_zero hT hna) (inv_ne_zero hg)),
    hmul _ _ (mul_ne_zero hT hna) (inv_ne_zero hg), hmul _ _ hT hna, eta_neg_one_pow, eta_inv_eq]
  ring

end GlobalTheory.JR.LinDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDivLocalEmbeddingCloseToOne
section
noncomputable section

open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory.NormCompat.RatioClose

theorem norm_one_tmul' {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [Module.Finite F E] (y : E) :
    Algebra.norm K ((1 : K) ⊗ₜ[F] y) = algebraMap F K (Algebra.norm F y) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem norm_div_close_to_one : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (σ : E' →+* w.adicCompletion E), (∀ x : E, σ (algebraMap E E' x) = algebraMap E _ x) → (∀ x : E', Valued.v (σ x) = w'.valuation E' x) → ∀ M : ℕ, ∃ M' : ℕ, ∀ z : E', z ≠ 0 → (∀ w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'), w''.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal → w'' ≠ w' → w''.valuation E' (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → Valued.v (algebraMap E (w.adicCompletion E) (Algebra.norm E z) / σ z - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  intro E E' _ _ _ _ _ w w' σ hσ hv M
  classical
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.NormCompat.NormCont.norm_close_to_one E E' w M
  refine ⟨M₁, fun z hz0 hz => ?_⟩
  set K := w.adicCompletion E
  let σA : E' →ₐ[E] K := { σ with commutes' := hσ }
  let ψ : K ⊗[E] E' →ₐ[K] K := Algebra.TensorProduct.lift (Algebra.ofId K K) σA (fun _ _ => Commute.all _ _)
  have hψ : ∀ x : E', ψ ((1 : K) ⊗ₜ x) = σ x := fun x => by
    simp [ψ, σA, Algebra.TensorProduct.lift_tmul]
  obtain ⟨e, he1, he⟩ := GlobalTheory.T.exists_tensor_idempotent_of_algHom_to_base E K E' ψ
  have hee : e * e = e := by rw [he, he1, map_one, one_mul]
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 E) E E'
  have hb' : ∀ i, IsIntegral ℤ (b i) := fun i => isIntegral_trans _ (hb i)
  have hvK : ∀ x : E, Valued.v (algebraMap E K x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  have hβ : ∀ x : E', x ≠ 0 → algebraMap E K (Algebra.norm E x) / σ x =
      Algebra.norm K (e + (1 - e) * ((1 : K) ⊗ₜ x)) := by
    intro x hx
    have h2 := GlobalTheory.T.norm_eq_mul_norm_idempotent_corner K (K ⊗[E] E') ψ e he1 he ((1 : K) ⊗ₜ x)
    rw [norm_one_tmul', hψ] at h2
    rw [h2, mul_div_cancel_left₀ _ ((map_ne_zero σ).2 hx)]
  let Z : K ⊗[E] E' := (1 : K) ⊗ₜ z
  set p : K ⊗[E] E' := e + (1 - e) * Z with hp
  set q : K ⊗[E] E' := (1 - e) * (1 - Z) with hq
  obtain ⟨K₀, hK₂, hK₁, hK₃⟩ : ∃ K₀ : ℕ, M ≤ K₀ ∧ M₁ ≤ K₀ ∧ 1 ≤ K₀ := ⟨M + M₁ + 1, by omega, by omega, by omega⟩
  set m : ℤ := (w'.valuation E' (z - 1)).log with hm
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, M ≤ n ∧ (K₀ : ℤ) + m ≤ n := ⟨M + K₀ + m.toNat, by omega, by omega⟩
  obtain ⟨ε, hε1, hε2, hε3⟩ := GlobalTheory.T.exists_global_element_near_idempotent_adicCompletion E E' w b ψ e hee he1 p q n
  set y : E' := ε + (1 - ε) * z with hy
  have hy1 : y - 1 = (1 - ε) * (z - 1) := by rw [hy]; ring
  have hw'ε : w'.valuation E' (ε - 1) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [← hv, map_sub, map_one, ← hψ]; exact hε2
  have hw'y : w'.valuation E' (y - 1) ≤ WithZero.exp (-(K₀ : ℤ)) := by
    rw [hy1, map_mul, Valuation.map_sub_swap]
    by_cases hz1 : w'.valuation E' (z - 1) = 0
    · rw [hz1, mul_zero]; exact zero_le'
    calc w'.valuation E' (ε - 1) * w'.valuation E' (z - 1)
        ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp m := by
          rw [hm, WithZero.exp_log hz1]; exact mul_le_mul' hw'ε le_rfl
      _ = WithZero.exp (-(n : ℤ) + m) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-(K₀ : ℤ)) := by
          rw [WithZero.exp_le_exp]; omega
  have hall : ∀ w'' : HeightOneSpectrum (𝓞 E'), w''.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = w.asIdeal →
      w''.valuation E' (y - 1) ≤ WithZero.exp (-(M₁ : ℤ)) := by
    intro w'' h1
    by_cases h2 : w'' = w'
    · subst h2
      exact hw'y.trans (WithZero.exp_le_exp.2 (by omega))
    rw [hy1, map_mul]
    have hi := GlobalTheory.T.valuation_le_one_of_sq_sub_self_integral_basis E E' b hb' w w'' h1 ε hε1
    have h1e : w''.valuation E' (1 - ε) ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (max_le (by simp) hi)
    calc w''.valuation E' (1 - ε) * w''.valuation E' (z - 1) ≤ 1 * WithZero.exp (-(M₁ : ℤ)) :=
          mul_le_mul' h1e (hz w'' h1 h2)
      _ = _ := one_mul _
  have hN := hM₁ y hall
  have hσy : Valued.v (σ y - 1) ≤ WithZero.exp (-(K₀ : ℤ)) := by
    rw [← map_one σ, ← map_sub, hv]; exact hw'y
  have hσy1 : Valued.v (σ y) = 1 := by
    have hlt : Valued.v (σ y - 1) < Valued.v (1 : K) := by
      rw [map_one]
      refine hσy.trans_lt ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    rw [Valuation.map_eq_of_sub_lt _ hlt, map_one]
  have hσy0 : σ y ≠ 0 := fun h => by rw [h, map_zero] at hσy1; exact zero_ne_one hσy1
  have hy0 : y ≠ 0 := fun h => hσy0 (by rw [h, map_zero])
  have hry : Valued.v (algebraMap E K (Algebra.norm E y) / σ y - 1) ≤ WithZero.exp (-(M : ℤ)) := by
    rw [div_sub_one hσy0, map_div₀, hσy1, div_one]
    have : algebraMap E K (Algebra.norm E y) - σ y =
        (algebraMap E K (Algebra.norm E y) - 1) - (σ y - 1) := by ring
    rw [this]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ (hσy.trans (WithZero.exp_le_exp.2 (by omega))))
    rw [← map_one (algebraMap E K), ← map_sub, hvK]; exact hN
  have hid : e + (1 - e) * ((1 : K) ⊗ₜ y) = p + q * ((1 : K) ⊗ₜ ε - e) := by
    have h1 : (1 : K) ⊗ₜ[E] y = (1 : K) ⊗ₜ ε + (1 - (1 : K) ⊗ₜ ε) * Z := by
      have := map_add (Algebra.TensorProduct.includeRight (R := E) (A := K) (B := E')) ε ((1 - ε) * z)
      simp only [Algebra.TensorProduct.includeRight_apply, map_mul, map_sub, map_one] at this
      rw [hy, this]
    rw [h1, hp, hq]
    linear_combination (Z - 1) * hee
  have hbz := hβ z hz0
  have hby : algebraMap E K (Algebra.norm E y) / σ y = Algebra.norm K (p + q * ((1 : K) ⊗ₜ ε - e)) := by
    rw [hβ y hy0, hid]
  rw [hbz]
  have : Algebra.norm K p - 1 = (Algebra.norm K (p + q * ((1 : K) ⊗ₜ ε - e)) - 1) -
      (Algebra.norm K (p + q * ((1 : K) ⊗ₜ ε - e)) - Algebra.norm K p) := by ring
  rw [this]
  refine (Valuation.map_sub _ _ _).trans (max_le (hby ▸ hry) (hε3.trans (WithZero.exp_le_exp.2 ?_)))
  omega

end GlobalTheory.NormCompat.RatioClose
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGroupSignMulAndNegOne
section
open scoped TensorProduct

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.NormSign

theorem exists_valuativeRel_of_normed : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F],
    ∃ _ : ValuativeRel F, IsNonarchimedeanLocalField F ∧ ∀ x y : F, x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  intro F _ _ _
  letI rel : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  have hc : (NormedField.valuation (K := F)).Compatible := Valuation.Compatible.ofValuation _
  refine ⟨rel, ?_, fun x y => Iff.rfl⟩
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := inferInstance, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := F))
      (fun {s} => (NormedField.toValued (K := F)).is_topological_valuation s)
  · rw [ValuativeRel.isNontrivial_iff_isNontrivial (NormedField.valuation (K := F))]
    infer_instance

theorem norm_one_tmul {R B L : Type} [Field R] [CommRing B] [Algebra R B] [Field L] [Algebra R L]
    [FiniteDimensional R L] (x : L) :
    Algebra.norm B ((1 : B) ⊗ₜ[R] x) = algebraMap R B (Algebra.norm R x) := by
  have h : Algebra.lmul B (B ⊗[R] L) ((1 : B) ⊗ₜ[R] x) = (Algebra.lmul R L x).baseChange B := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b z
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.norm_apply, h, LinearMap.det_baseChange, Algebra.norm_apply]

theorem norm_algebraMap_of_isPushout : ∀ (F E K L : Type) [Field F] [Field E] [Field K] [CommRing L] [Algebra F E] [Algebra F K] [Algebra F L]
    [Algebra K L] [Algebra E L] [IsScalarTower F K L] [IsScalarTower F E L] [FiniteDimensional F E],
    Algebra.IsPushout F E K L → ∀ z : E, Algebra.norm K (algebraMap E L z) = algebraMap F K (Algebra.norm F z) := by
  intro F E K L _ _ _ _ _ _ _ _ _ _ _ _ h z
  haveI := h.symm
  have he : Algebra.IsPushout.equiv F K E L ((1 : K) ⊗ₜ[F] z) = algebraMap E L z := by
    simp [Algebra.IsPushout.equiv_tmul]
  rw [← he, Algebra.norm_eq_of_algEquiv, norm_one_tmul]

theorem mul_norm_of_not_norm (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] [Field L] [Algebra K L] (h2 : Module.finrank K L = 2)
    (s t : Kˣ) (hs : ¬ ∃ y : L, Algebra.norm K y = s) (ht : ¬ ∃ y : L, Algebra.norm K y = t) :
    ∃ y : L, Algebra.norm K y = ((s * t : Kˣ) : K) := by
  haveI : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have hN := GroundTheory.Automorphic.natCard_quotient_range_normUnits_eq_two (F := K) (E := L)
  have ht' : t ∉ (GroundTheory.LocalField.normUnits K L).range := fun h =>
    ht ((GroundTheory.Automorphic.mem_range_normUnits_iff t).1 h)
  rcases GroundTheory.Automorphic.mem_or_mul_inv_mem_of_natCard_eq_two hN ht' s with h | h
  · exact absurd ((GroundTheory.Automorphic.mem_range_normUnits_iff s).1 h) hs
  · obtain ⟨z, hz⟩ := (GroundTheory.Automorphic.mem_range_normUnits_iff _).1 h
    refine ⟨z * algebraMap K L (t : K), ?_⟩
    rw [map_mul, hz, Algebra.norm_algebraMap, h2]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    have := t.ne_zero
    field_simp

theorem norms_of_isField {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) :
    A.NL 0 = 0 ∧
    (∀ s t : A.Kˣ, (¬ ∃ y, A.NL y = s) → (¬ ∃ y, A.NL y = t) → ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K)) ∧
      ∃ y, A.NL y = ((-1 : A.Kˣ) : A.K) := by
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  haveI := hU.ultraF
  haveI := hU.ultraE
  haveI := hU.lcF
  haveI := hU.lcE
  haveI := hU.charZero
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hU.finrank_eq
  have hKL : Module.finrank A.K A.L = 2 := by
    haveI := A.push.symm
    rw [← (Algebra.IsPushout.equiv F A.K E A.L).toLinearEquiv.finrank_eq, Module.finrank_baseChange,
      hU.finrank_eq]
  haveI : CharZero A.K := charZero_of_injective_algebraMap (algebraMap F A.K).injective
  obtain ⟨vF, hFloc, hFv⟩ := exists_valuativeRel_of_normed F
  refine ⟨?_, ?_⟩
  · haveI : FiniteDimensional A.K A.L := Module.finite_of_finrank_eq_succ hKL
    exact Algebra.norm_zero (R := A.K) (S := A.L)
  constructor
  · intro s t hs ht
    obtain ⟨vK, tK, hKloc, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension F A.K
    exact @mul_norm_of_not_norm A.K A.L _ vK tK hKloc _ _ _ hKL s t hs ht
  · obtain ⟨vE, hEloc, hEv⟩ := exists_valuativeRel_of_normed E
    haveI : ValuativeExtension F E := ⟨fun a b => by rw [hEv, hFv, norm_algebraMap', norm_algebraMap']⟩
    obtain ⟨z, hz⟩ := GlobalTheory.T.exists_norm_eq_neg_one_of_unramified_values F E (fun y => by
      obtain ⟨x, hx⟩ := hU.unram y
      exact ⟨x, by rw [hEv, norm_algebraMap', hx], by rw [hEv, norm_algebraMap', hx]⟩)
    refine ⟨algebraMap E A.L z, ?_⟩
    have := norm_algebraMap_of_isPushout F E A.K A.L A.push z
    simp only [Et.NL, this, hz, map_neg, map_one, Units.val_neg, Units.val_one]

theorem omega_mul_neg_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → (∀ s t : A.Kˣ, ω ((s * t : A.Kˣ) : A.K) = ω s * ω t) ∧ ω ((-1 : A.Kˣ) : A.K) = 1 := by
  classical
  intro F E _ _ _ _ _ A ψ x μ ω h
  obtain ⟨hK, hL, -, -, hω⟩ := h
  obtain ⟨hzero, hprod, hneg⟩ := norms_of_isField A hK hL
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  have hmul : ∀ s t : A.Kˣ, (∃ y, A.NL y = s) → (∃ y, A.NL y = t) → ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K) := by
    rintro s t ⟨y, hy⟩ ⟨y', hy'⟩
    exact ⟨y * y', by simp only [Et.NL] at hy hy' ⊢; rw [map_mul, hy, hy', Units.val_mul]⟩
  have hdiv : ∀ s t : A.Kˣ, (∃ y, A.NL y = s) → (∃ y, A.NL y = ((s * t : A.Kˣ) : A.K)) → ∃ y, A.NL y = t := by
    rintro s t ⟨y, hy⟩ ⟨y', hy'⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [hzero] at hy
      exact s.ne_zero hy.symm
    refine ⟨y' * y⁻¹, ?_⟩
    have h1 : A.NL y * A.NL y⁻¹ = 1 := by
      simp only [Et.NL]; rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
    simp only [Et.NL] at hy hy' h1 ⊢
    rw [map_mul, hy', Units.val_mul]
    rw [hy] at h1
    calc (s : A.K) * t * (Algebra.norm A.K) y⁻¹ = t * ((s : A.K) * (Algebra.norm A.K) y⁻¹) := by ring
      _ = t := by rw [h1, mul_one]
  have hval : ∀ s : A.Kˣ, ω s = if ∃ y, A.NL y = s then 1 else -1 := by
    intro s
    split_ifs with hs
    · exact (hω s).1 hs
    · exact (hω s).2 hs
  refine ⟨fun s t => ?_, by rw [hval, if_pos hneg]⟩
  rw [hval s, hval t, hval (s * t)]
  by_cases hs : ∃ y, A.NL y = s <;> by_cases ht : ∃ y, A.NL y = t
  · rw [if_pos hs, if_pos ht, if_pos (hmul s t hs ht)]; ring
  · rw [if_pos hs, if_neg ht, if_neg (fun h => ht (hdiv s t hs h))]; ring
  · have hst : ¬ ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K) := fun h => hs (hdiv t s ht (by rwa [mul_comm]))
    rw [if_neg hs, if_pos ht, if_neg hst]; ring
  · rw [if_neg hs, if_neg ht, if_pos (hprod s t hs ht)]; ring

end GlobalTheory.JR.WeilQuad.NormSign
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OntoOCAdditivePolyStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_root_additive_poly_eq_of_unit_coeff : ∀ (l : ℕ) [Fact l.Prime] (E N : ℕ) (a : ℕ → ℂ_[l]), N ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖a N‖ = 1 → ∀ b : ℂ_[l], ‖b‖ ≤ 1 → ∃ W : ℂ_[l], ‖W‖ ≤ 1 ∧ ∑ k ∈ Finset.range (E + 1), a k * W ^ l ^ k = b := by
  first | exact @GlobalTheory.onto_OC_additive_poly | exact GlobalTheory.onto_OC_additive_poly | (intros; apply GlobalTheory.onto_OC_additive_poly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierEtaleKProdLocallyConstantCompactSu
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.TildeTest

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (fun p : A.K × A.K => A.tilde μK ψ φ' p.1 p.2) := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ φ' hφ
  set T : A.K → A.K → ℂ := fun c u => A.tilde μK ψ φ' c u with hTdef
  have hslice : ∀ c, IsTest (fun u => T c u) := by
    intro c
    have hnd := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
    have h := (GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd).2 μK hμ
      (fun b => φ' (b, c)) (GlobalTheory.TestFn.slice_test φ' hφ c)
    convert h using 1
    funext u
    simp only [hTdef, Et.tilde, fourB, Algebra.traceForm_apply, Et.psiK]
    congr 1; funext b; rw [mul_comm u b]
  obtain ⟨V, hV, hVf⟩ := GlobalTheory.TestFn.unif_const (A.K × A.K) φ' hφ
  set V₂ : Set A.K := {v | ((0 : A.K), v) ∈ V} with hV₂def
  have hV₂ : V₂ ∈ 𝓝 (0 : A.K) := by
    have hc : Continuous (fun v : A.K => ((0 : A.K), v)) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by rw [show ((0 : A.K), (0 : A.K)) = (0 : A.K × A.K) from rfl]; exact hV)
  have hshift : ∀ c c', c' - c ∈ V₂ → ∀ u, T c' u = T c u := by
    intro c c' hcc u
    simp only [hTdef, Et.tilde]
    congr 1; funext b
    have := hVf (b, c) (0, c' - c) hcc
    simp only [Prod.mk_add_mk, add_zero, add_sub_cancel] at this
    rw [this]
  have hnbhd : ∀ c : A.K, {c' | c' - c ∈ V₂} ∈ 𝓝 c := by
    intro c
    have hc : Continuous (fun c' : A.K => c' - c) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV₂)
  have hlc : IsLocallyConstant (fun p : A.K × A.K => T p.1 p.2) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨c₀, u₀⟩
    have hu : {u | T c₀ u = T c₀ u₀} ∈ 𝓝 u₀ := ((hslice c₀).1.isOpen_fiber _).mem_nhds rfl
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod (hnbhd c₀) hu] with p hp
    rw [hshift c₀ p.1 hp.1 p.2]; exact hp.2
  refine ⟨hlc, ?_⟩
  have hC₂ : IsCompact (Prod.snd '' tsupport φ') := hφ.2.image continuous_snd
  obtain ⟨t, -, hcover⟩ := hC₂.elim_nhds_subcover (fun c => {c' | c' - c ∈ V₂}) (fun c _ => hnbhd c)
  have hK : IsCompact ((Prod.snd '' tsupport φ') ×ˢ ⋃ c ∈ t, tsupport (fun u => T c u)) :=
    hC₂.prod (t.isCompact_biUnion fun c _ => (hslice c).2)
  have hzero : ∀ c ∉ Prod.snd '' tsupport φ', ∀ u, T c u = 0 := by
    intro c hc u
    have h0 : ∀ b, φ' (b, c) = 0 := fun b => image_eq_zero_of_notMem_tsupport (fun h => hc ⟨(b, c), h, rfl⟩)
    simp [hTdef, Et.tilde, h0]
  have hsupp : Function.support (fun p : A.K × A.K => T p.1 p.2) ⊆
      (Prod.snd '' tsupport φ') ×ˢ ⋃ c ∈ t, tsupport (fun u => T c u) := by
    rintro ⟨c, u⟩ hp
    have hc : c ∈ Prod.snd '' tsupport φ' := by
      by_contra hc; exact hp (hzero c hc u)
    refine ⟨hc, ?_⟩
    obtain ⟨c', hc't, hcc'⟩ := Set.mem_iUnion₂.mp (hcover hc)
    refine Set.mem_iUnion₂.mpr ⟨c', hc't, subset_tsupport _ ?_⟩
    show T c' u ≠ 0
    rw [← hshift c' c hcc' u]; exact hp
  have hclosed : IsClosed (Function.support (fun p : A.K × A.K => T p.1 p.2)) := by
    have := (hlc.isOpen_fiber 0).isClosed_compl
    convert this using 1
    ext p; simp [Function.mem_support]
  have hts : tsupport (fun p : A.K × A.K => T p.1 p.2) = Function.support (fun p : A.K × A.K => T p.1 p.2) :=
    hclosed.closure_eq
  unfold HasCompactSupport
  rw [hts]
  exact hK.of_isClosed_subset hclosed hsupp

end GlobalTheory.JR.TildeTest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarPartFinrankAddSenWeightsLeRankStatement
section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarPart_finrank_add_senWeights_le_rank : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V), ∀ (ψ : ZMod n → V →ₗ[k] V) (ψ0 : k⸨X⸩ →ₗ[k] k⸨X⸩), (∀ i a x, ψ i (a • D.φ i x) = ψ0 a • x) → (∀ a b, ψ0 (R.φ a * b) = a * ψ0 b) → ψ0 1 = 1 → (∀ i x, ψ i (D.γ i x) = D.γ (i - 1) (ψ i x)) → (∀ a : ℤ, 2 - (l : ℤ) ≤ a → a ≤ 1 → ψ0 '' {x | ∃ b : k⟦X⟧, x = vv k ^ a * (b : k⸨X⸩)} = Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩))) → ∀ (i : ZMod n) (N₀ N : Submodule k⟦X⟧ V) (ws s : ℕ) (w : ℤ), IsLat N₀ → IsLat N → CondC (D.γ (i - 1)) N₀ → CondC (D.γ i) N → 1 ≤ ws → ws + 7 ≤ l → sh ws N ≤ pull (D.φ i) N₀ → pull (D.φ i) N₀ ≤ sh (-w) N → (ws : ℤ) + 2 ≤ l * (s + 3) - w → (∀ a : ℕ, a ≤ s + 1 → sen (D.γ (i - 1)) N₀ (a : k) = 0) → (∀ y ∈ sh (1 - ws) (pull (D.φ i) N₀), ψ i y = 0 → ∃ x ∈ sh (-ws) (pull (D.φ i) N₀), ψ i x = 0 ∧ D.γ i x - x = y) → (∀ x ∈ N, (∃ m : ℕ, ((nab (D.γ i)) ^ m) x ∈ sh (ws + 1) N) → nab (D.γ i) x ∈ sh (ws + 1) N) → ∀ Z : Submodule k V, (∀ x ∈ Z, x ∈ sh (-ws) (pull (D.φ i) N₀) ∧ D.γ i x - x ∈ sh (ws + 2) N) → Module.finrank k (↥Z ⧸ (N.restrictScalars k).submoduleOf Z) + ∑ a ∈ Finset.range (ws + 1), sen (D.γ i) N (a : k) ≤ Module.finrank k⸨X⸩ V := by
  first | exact @GlobalTheory.PhiGam.PolarCount.main | exact GlobalTheory.PhiGam.PolarCount.main | (intros; apply GlobalTheory.PhiGam.PolarCount.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemAdjoinGenStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_mem_adjoin_gen_of_separable : ∀ (K : UQ) (B : InvAlg K) (a : K.O), B.P.Separable → K.Small a → ∃ N : ℕ, ∀ r : B.A, IsIntegral K.O r → (al K a ^ N) • r ∈ Algebra.adjoin K.O {B.g} := by
  first | exact @GlobalTheory.UnitLemma.Desc.pow_smul_mem_adjoin_gen | exact GlobalTheory.UnitLemma.Desc.pow_smul_mem_adjoin_gen | (intros; apply GlobalTheory.UnitLemma.Desc.pow_smul_mem_adjoin_gen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledIntegersKAnnihilatorSmallNearZero
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.annihilator_small : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ U ∈ 𝓝 (0 : A.K), ∀ᶠ c in 𝓝[≠] (0 : F), ∀ b : A.K, (∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1) → b ∈ U := by
  intro F E _ _ _ _ hU A ψ hψ U hUmem
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  have hfacts := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hnd : (Algebra.traceForm F A.K).Nondegenerate := hfacts.2.2.1
  have hOKopen : IsOpen A.OK := hfacts.2.2.2.2.2.2.2.2.2.1
  obtain ⟨R, hR⟩ := hfacts.2.2.2.2.2.2.2.2.2.2.2
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  obtain ⟨-, hsmall⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ A.K (Algebra.traceForm F A.K)
    (Algebra.traceForm_isSymm F (S := A.K)) hnd
  obtain ⟨M, N, hMU, -, -, -, hNc, -, hM⟩ := hsmall U hUmem
  have hev : ∀ᶠ c in 𝓝 (0 : F), ∀ y ∈ (N : Set A.K), c • y ∈ A.OK := by
    refine hNc.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : ContinuousAt (fun p : F × A.K => p.1 • p.2) ((0 : F), y) := continuous_smul.continuousAt
    have : A.OK ∈ 𝓝 ((fun p : F × A.K => p.1 • p.2) ((0 : F), y)) := by
      simpa using hOKopen.mem_nhds h0
    exact hc this
  filter_upwards [nhdsWithin_le_nhds hev] with c hc b hb
  apply hMU
  rw [SetLike.mem_coe, hM]
  intro y hy
  have := hb y (hc y hy)
  simpa [Et.psiK, Algebra.traceForm_apply, mul_comm] using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → ∀ μ : Measure V, μ.IsAddHaarMeasure → (∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → (SelfDual μ (fun x y => ψ (β x y)) ↔ μ M * μ {y | ∀ x ∈ M, ψ (β x y) = 1} = 1) ∧ ∀ y, ∫ x in (M : Set V), ψ (β x y) ∂μ = Set.indicator {y | ∀ x ∈ M, ψ (β x y) = 1} (fun _ => ((μ M).toReal : ℂ)) y) ∧ (SelfDual μ (fun x y => ψ (β x y)) → ∀ f, IsTest f → ∫ y, ‖fourB μ (fun x y => ψ (β x y)) f y‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) := by
  first | exact @GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel | exact GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel | (intros; apply GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignedInvolutionStableLatticeSumMulFixedUnitStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signedInvolutionStableLatticeSum_mul_fixed_unit : ∀ (K : UQ) (B : InvAlg K) (ι : Type) (π : ι → B.A) (I I' : Finset ι) (u s y : B.A), B.LieReg → B.Plus y → HH B π I I' (y * u) s = K.eta (Algebra.norm K.E y) * HH B π I I' u (y * s) := by
  first | exact @GlobalTheory.UnitLemma.Move.HH_mul_unit | exact GlobalTheory.UnitLemma.Move.HH_mul_unit | (intros; apply GlobalTheory.UnitLemma.Move.HH_mul_unit <;> assumption)
end

