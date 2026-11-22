import Mathlib
import Formalism.LocalToGlobal.HermitianForms.Bundle0003
import Formalism.LocalToGlobal.Columns.RecLevelLocT
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0091
import Formalism.LocalRingCardinality.SpanPowerMembership.PlOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0124
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0118

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelActsTriviallyOnDiscriminantGroup
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigR_inclE_adic (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : E) :
    sigR σ (v.adicCompletion F) (inclE (F := F) (v.adicCompletion F) a) =
      inclE (F := F) (v.adicCompletion F) (σ a) := by
  simp [sigR, inclE]

theorem sigR_mem_intV_adic (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {s : E ⊗[F] v.adicCompletion F}
    (hs : s ∈ intV E v) : sigR σ (v.adicCompletion F) s ∈ intV E v := by
  have key : intV E v ≤ (intV E v).comap (sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, b, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · show sigR σ (v.adicCompletion F) (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E b)) ∈ intV E v
      rw [sigR_inclE_adic]
      have h : IsIntegral ℤ ((σ : E →+* E) (algebraMap (𝓞 E) E b)) :=
        (RingOfIntegers.isIntegral_coe b).map ((σ : E →+* E).toIntAlgHom)
      exact Formalism.UG.P.easyc_inclE_mem (F := F) (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring _
        ⟨IsIntegralClosure.mk' (𝓞 E) _ h, IsIntegralClosure.algebraMap_mk' _ _ _⟩
    · show sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] y) ∈ intV E v
      simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        map_one, AlgHom.coe_id, id_eq]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  exact key hs

theorem mul_eq_unit_mul_of_triple_product_one {A : Type} [CommRing A] (a b P Q T : A) (h : P * Q * T = 1) :
    a * b = T * ((a * P) * (b * Q)) := by linear_combination (-(a * b)) * h

theorem eq_one_add_mul_neg_of_add_mul_eq_one {A : Type} [CommRing A] (a T S : A) (h : a + T * S = 1) : a = 1 + T * (-S) := by
  linear_combination h

theorem mul_sub_eq_of_triple_product_one {A : Type} [CommRing A] (P Q T d e : A) (h : P * Q * T = 1) (hd : d = 1 + T * e) :
    P * (d * Q - Q) = e := by linear_combination (P * Q) * hd + e * h

end SlopeTestRemainingChoices

set_option maxHeartbeats 1000000 in

theorem uloc_acts_trivially_on_dual_quotient {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} [NeZero n] {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ (1 : Matrix (Fin n) (Fin n) E) T f bad) (p q : 𝓞 E) (hqp : (q : E) = σ (p : E))
    (hpq : (p : E) * (q : E) = (T : E)) (hT : T ≠ 0)
    (hLb : S.Lb = rll_dLat n ((p : E)⁻¹))
    (hdual : Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb) = rll_dLat n (q : E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (hH : ∀ m : S.fM v hv, m ≠ 0 → ∀ d c : intV E v, (d - 1) • m = 0 →
      sigR σ (v.adicCompletion F) (d : E ⊗[F] v.adicCompletion F) * (d : E ⊗[F] v.adicCompletion F) =
        1 + (T : E ⊗[F] v.adicCompletion F) * (c : E ⊗[F] v.adicCompletion F) →
      ∃ e : intV E v, (d : E ⊗[F] v.adicCompletion F) = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F))
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ S.Uloc v) :
    ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
  have hT' : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hp0 : (p : E) ≠ 0 := fun h => hT' (by rw [← hpq, h, zero_mul])
  have hq0 : (q : E) ≠ 0 := fun h => hT' (by rw [← hpq, h, mul_zero])
  have hΛ : ∀ z, z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ↔
      (∀ i, i ≠ lastIdx n → z i ∈ intV E v) ∧
        inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * z (lastIdx n) ∈ intV E v := by
    intro z; rw [hLb]; exact rll_mem_loc_dLat n v _ (inv_ne_zero hp0) z
  have hΛ' : ∀ z, z ∈ latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)) ↔
      (∀ i, i ≠ lastIdx n → z i ∈ intV E v) ∧
        inclE (F := F) (v.adicCompletion F) (q : E) * z (lastIdx n) ∈ intV E v := by
    intro z; rw [hdual]; exact rll_mem_loc_dLat n v _ hq0 z
  rw [S.UlocAlt v hv] at hx
  obtain ⟨⟨hU, hstL⟩, hstL', hfix⟩ := hx
  set ι := inclE (F := F) (E := E) (v.adicCompletion F) with hιdef
  set ℓ := lastIdx n with hℓ
  set X := (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) with hX
  have hQQ : ι (q : E) * ι ((q : E)⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
  have hPQi : ι ((p : E)⁻¹) * ι ((q : E)⁻¹) * (T : E ⊗[F] v.adicCompletion F) = 1 := by
    rw [← map_natCast ι T, ← map_mul, ← map_mul, ← hpq]
    rw [show (p : E)⁻¹ * (q : E)⁻¹ * ((p : E) * (q : E)) = 1 by field_simp, map_one]
  have hPQ : ι (p : E) * ι (q : E) = (T : E ⊗[F] v.adicCompletion F) := by
    rw [← map_mul, hpq, map_natCast]

  set w : Fin n → E ⊗[F] v.adicCompletion F := Pi.single ℓ (ι ((q : E)⁻¹)) with hwdef
  have hw : w ∈ (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))) := by
    refine (hΛ' w).2 ⟨fun i hi => ?_, ?_⟩
    · rw [hwdef, Pi.single_eq_of_ne hi]; exact zero_mem _
    · rw [hwdef, Pi.single_eq_same, hQQ]; exact one_mem _

  have hdec : ∀ z ∈ (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))), ∃ r : intV E v, (r : E ⊗[F] v.adicCompletion F) = ι (q : E) * z ℓ ∧
      z - (r : E ⊗[F] v.adicCompletion F) • w ∈ (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb) := by
    intro z hz
    refine ⟨⟨ι (q : E) * z ℓ, ((hΛ' z).1 hz).2⟩, rfl, (hΛ _).2 ⟨fun i hi => ?_, ?_⟩⟩
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hwdef, Pi.single_eq_of_ne hi, mul_zero, sub_zero]
      exact ((hΛ' z).1 hz).1 i hi
    · have h0 : z ℓ - (ι (q : E) * z ℓ) * ι ((q : E)⁻¹) = 0 := by linear_combination (-z ℓ) * hQQ
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hwdef, Pi.single_eq_same]
      rw [h0, mul_zero]; exact zero_mem _

  set m := S.fT v hv ⟨w, hw⟩ with hmdef
  have hf : ∀ z : (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))), ∃ r : intV E v, (r : E ⊗[F] v.adicCompletion F) = ι (q : E) * z.1 ℓ ∧ S.fT v hv z = r • m := by
    rintro ⟨z, hz⟩
    obtain ⟨r, hr, hu⟩ := hdec z hz
    refine ⟨r, hr, ?_⟩
    have h1 := S.fT_L v hv ((⟨z, hz⟩ : (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)))) - r • (⟨w, hw⟩ : (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))))) hu
    rw [map_sub] at h1
    rw [LinearMap.map_smul] at h1
    rw [sub_eq_zero] at h1
    exact h1
  have hm0 : m ≠ 0 := by
    intro h0
    apply S.fT_ne v hv
    refine LinearMap.ext fun z => ?_
    obtain ⟨r, -, hr⟩ := hf z
    rw [hr, h0, LinearMap.zero_apply]
    exact smul_zero r

  have hXw : X *ᵥ w = fun i => X i ℓ * ι ((q : E)⁻¹) := by
    funext i
    show (fun j => X i j) ⬝ᵥ Pi.single ℓ (ι ((q : E)⁻¹)) = _
    rw [dotProduct_single]
  have hxw : X *ᵥ w ∈ (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))) := (hstL' w).1 hw
  have hb : ∀ i, i ≠ ℓ → X i ℓ * ι ((q : E)⁻¹) ∈ intV E v := by
    intro i hi
    have h1 := ((hΛ' _).1 hxw).1 i hi
    rw [congrFun hXw i] at h1
    exact h1
  have hXwi : ∀ i, (X *ᵥ w) i = X i ℓ * ι ((q : E)⁻¹) := fun i => congrFun hXw i
  have hd : X ℓ ℓ ∈ intV E v := by
    have h1 := ((hΛ' _).1 hxw).2
    rw [hXwi ℓ, mul_left_comm, hQQ, mul_one] at h1
    exact h1
  have h2 : ((⟨X ℓ ℓ, hd⟩ : intV E v) - 1) • m = 0 := by
    obtain ⟨r, hr, hrm⟩ := hf ⟨X *ᵥ w, hxw⟩
    have hr' : r = ⟨X ℓ ℓ, hd⟩ := by
      apply Subtype.ext
      rw [hr]
      show ι (q : E) * (X *ᵥ w) ℓ = X ℓ ℓ
      rw [hXwi ℓ, mul_left_comm, hQQ, mul_one]
    have hfx := hfix ⟨w, hw⟩
    rw [sub_smul, one_smul, ← hr', ← hrm, sub_eq_zero]
    exact hfx
  have hU' : cT (sigR σ (v.adicCompletion F)) X * X = 1 := by
    have h1 : cT (sigR σ (v.adicCompletion F)) X * (1 : Matrix (Fin n) (Fin n) E).map ι * X =
        (1 : Matrix (Fin n) (Fin n) E).map ι := hU
    rwa [Matrix.map_one ι (map_zero ι) (map_one ι), Matrix.mul_one] at h1
  have hsum : ∑ j, sigR σ (v.adicCompletion F) (X j ℓ) * X j ℓ = 1 := by
    have h1 := congrFun (congrFun hU' ℓ) ℓ
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    simpa only [cT, Matrix.transpose_apply, Matrix.map_apply] using h1
  have hs : ∀ a : E, sigR σ (v.adicCompletion F) (ι a) = ι (σ a) := fun a => sigR_inclE_adic σ v a
  have hsq : σ (q : E) = p := by rw [hqp, hσ]
  have hsQi : sigR σ (v.adicCompletion F) (ι ((q : E)⁻¹)) = ι ((p : E)⁻¹) := by rw [hs, map_inv₀, hsq]
  have hc' : -∑ j ∈ Finset.univ.erase ℓ, sigR σ (v.adicCompletion F) (X j ℓ * ι ((q : E)⁻¹)) * (X j ℓ * ι ((q : E)⁻¹))
      ∈ intV E v :=
    neg_mem (sum_mem fun j hj => mul_mem (sigR_mem_intV_adic σ v (hb j (Finset.ne_of_mem_erase hj)))
      (hb j (Finset.ne_of_mem_erase hj)))
  have h3 : sigR σ (v.adicCompletion F) (X ℓ ℓ) * X ℓ ℓ = 1 + (T : E ⊗[F] v.adicCompletion F) *
      (-∑ j ∈ Finset.univ.erase ℓ, sigR σ (v.adicCompletion F) (X j ℓ * ι ((q : E)⁻¹)) * (X j ℓ * ι ((q : E)⁻¹))) := by
    apply eq_one_add_mul_neg_of_add_mul_eq_one
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ)] at hsum
    rw [Finset.mul_sum]
    convert hsum using 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hsQi]
    exact (mul_eq_unit_mul_of_triple_product_one _ _ _ _ _ hPQi).symm
  obtain ⟨e, he⟩ := hH m hm0 ⟨X ℓ ℓ, hd⟩ ⟨_, hc'⟩ h2 h3
  have he' : X ℓ ℓ = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F) := he
  have hwΛ : X *ᵥ w - w ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
    refine (hΛ _).2 ⟨fun i hi => ?_, ?_⟩
    · rw [Pi.sub_apply, hXwi i, hwdef, Pi.single_eq_of_ne hi, sub_zero]
      exact hb i hi
    · rw [Pi.sub_apply, hXwi ℓ, hwdef, Pi.single_eq_same, mul_sub_eq_of_triple_product_one _ _ _ _ _ hPQi he']
      exact e.2
  intro y hy
  obtain ⟨r, -, hu⟩ := hdec y hy
  have hsplit : X *ᵥ y - y = (X *ᵥ (y - (r : E ⊗[F] v.adicCompletion F) • w) - (y - (r : E ⊗[F] v.adicCompletion F) • w)) +
      (r : E ⊗[F] v.adicCompletion F) • (X *ᵥ w - w) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub]
    abel
  rw [hsplit]
  exact add_mem (sub_mem ((hstL _).1 hu) hu) (Submodule.smul_mem _ r hwΛ)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyResidueFieldUnitBallEquiv
section
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open IsLocalRing

theorem valuation_le_one_iff_of_lt_iff {K F : Type} [Field K] [NumberField K] [NormedField F]
    (v : HeightOneSpectrum (𝓞 K)) (a : K →+* F)
    (h : ∀ x : K, v.valuation K x < 1 ↔ ‖a x‖ < 1) (x : K) :
    v.valuation K x ≤ 1 ↔ ‖a x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h1 := h x⁻¹
  have hv : 0 < v.valuation K x := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx)
  have hn : 0 < ‖a x‖ := norm_pos_iff.mpr ((map_ne_zero a).mpr hx)
  rw [map_inv₀, map_inv₀, norm_inv, inv_lt_one₀ hv, inv_lt_one₀ hn] at h1
  rw [← not_lt, ← not_lt, h1]

theorem exists_embedding_inducing_place (K : Type) [Field K] [NumberField K] [IsGalois ℚ K]
    (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 K)) (hl : ((l : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ∃ a : K →+* PadicAlgCl l, ∀ x : K, v.valuation K x < 1 ↔ ‖a x‖ < 1 := by
  classical
  let a₀ : K →+* PadicAlgCl l := (IsAlgClosed.lift (R := ℚ) (S := K) (M := PadicAlgCl l)).toRingHom
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding K l a₀
  have hlw : ((l : ℕ) : 𝓞 K) ∈ w₀.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), hw₀]
    have hfin : ‖a₀ ((l : ℕ) : K)‖ < 1 := by
      rw [map_natCast]
      have h1 : ((l : ℕ) : PadicAlgCl l) = ((l : ℚ_[l]) : PadicAlgCl l) := by simp
      rw [h1, PadicAlgCl.norm_extends]
      exact Padic.norm_p_lt_one
    convert hfin using 3
    first | exact map_natCast _ _ | simp
  have := v.isPrime
  have := w₀.isPrime
  haveI := Formalism.BasicNotions.Examples₂.PlOver.liesOver_of_mem v.asIdeal hl
  haveI := Formalism.BasicNotions.Examples₂.PlOver.liesOver_of_mem w₀.asIdeal hlw
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(l : ℤ)}) v.asIdeal
    w₀.asIdeal (K ≃ₐ[ℚ] K)
  let a : K →+* PadicAlgCl l := a₀.comp (σ : K →+* K)
  obtain ⟨v', hv'⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding K l a
  have hvv : v' = v := by
    apply HeightOneSpectrum.ext
    ext y
    have h2 : (σ • y) ∈ w₀.asIdeal ↔ y ∈ v.asIdeal := by
      rw [← hσ]; exact Ideal.smul_mem_pointwise_smul_iff
    rw [← h2, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), hv',
      ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), hw₀]
    rfl
  subst hvv
  exact ⟨a, hv'⟩

theorem algebraMap_toZMod_eq {l : ℕ} [Fact l.Prime] {R : Type} [Field R] [Algebra (ZMod l) R]
    (f : ℤ_[l] →+* R) (hf : f (l : ℤ_[l]) = 0) (x : ℤ_[l]) :
    algebraMap (ZMod l) R (PadicInt.toZMod x) = f x := by
  first
  | exact @_root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq
  | exact _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq
  | (apply _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq ..)

theorem isAlgebraic_residueField {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [IsLocalRing B]
    [Algebra (ZMod l) (ResidueField B)] (c : ℤ_[l] →+* B)
    (hcl : c (l : ℤ_[l]) ∈ maximalIdeal B)
    (halg : ∀ b : B, ∃ p : ℤ_[l][X], p.IsPrimitive ∧ p.eval₂ c b = 0) :
    Algebra.IsAlgebraic (ZMod l) (ResidueField B) := by
  have hl : (residue B).comp c (l : ℤ_[l]) = 0 := (residue_eq_zero_iff _).mpr hcl
  have hcomp : (algebraMap (ZMod l) (ResidueField B)).comp PadicInt.toZMod = (residue B).comp c :=
    RingHom.ext fun x => algebraMap_toZMod_eq _ hl x
  refine ⟨fun y => ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective y
  obtain ⟨p, hp, hb⟩ := halg b
  refine ⟨p.map PadicInt.toZMod, fun h => ?_, ?_⟩
  · have hdvd : Polynomial.C (l : ℤ_[l]) ∣ p := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have h1 : PadicInt.toZMod (p.coeff i) = 0 := by
        have := congrArg (fun q => q.coeff i) h
        simpa using this
      have h2 : p.coeff i ∈ RingHom.ker (PadicInt.toZMod (p := l)) := h1
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p] at h2
      exact Ideal.mem_span_singleton.mp h2
    have hu := hp _ hdvd
    exact PadicInt.prime_p.not_unit hu
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hb, map_zero]

theorem exists_isPrimitive_eval₂_eq_zero {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) :
    ∃ p : ℤ_[l][X], p.IsPrimitive ∧
      p.eval₂ ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom) x = 0 := by
  classical
  have hmap : algebraMap ℤ_[l] (PadicAlgCl l) =
      (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom :=
    IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)
  haveI : FaithfulSMul ℤ_[l] (PadicAlgCl l) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      rw [hmap]
      exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp fun a b h => Subtype.ext h)
  letI : NormalizedGCDMonoid ℤ_[l] := Classical.arbitrary _
  have hx : IsAlgebraic ℤ_[l] x :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] (PadicAlgCl l)).mpr
      (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨p, hp0, hp⟩ := hx
  refine ⟨p.primPart, p.isPrimitive_primPart, ?_⟩
  rw [← hmap]
  exact Polynomial.aeval_primPart_eq_zero hp0 hp

def unitBall {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) : ValuationSubring ℂ :=
  (PadicAlgCl.valued l).v.valuationSubring.comap (ι.symm : ℂ →+* PadicAlgCl l)

theorem mem_unitBall_iff {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (z : ℂ) :
    z ∈ unitBall ι ↔ ‖ι.symm z‖ ≤ 1 := by
  rw [unitBall, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
    ← NNReal.coe_le_coe]
  rfl

theorem nonempty_residueField_unitBall_equiv {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) :
    Nonempty (ResidueField (unitBall ι) ≃+* Formalism.CyclotomicNorms.Fbar l) := by
  classical
  set B := unitBall ι with hB
  let inc : ℤ_[l] →+* PadicAlgCl l := (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom
  have hinc : ∀ x : ℤ_[l], ‖inc x‖ = ‖x‖ := fun x => by
    change ‖((x : ℚ_[l]) : PadicAlgCl l)‖ = ‖x‖
    rw [PadicAlgCl.norm_extends]; rfl
  let c : ℤ_[l] →+* B := (ι.toRingHom.comp inc).codRestrict B.toSubring fun x => by
    change ι (inc x) ∈ B
    rw [hB, mem_unitBall_iff, RingEquiv.symm_apply_apply, hinc]
    exact PadicInt.norm_le_one x
  have hcl : c (l : ℤ_[l]) ∈ maximalIdeal B := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨⟨y, hy⟩, hxy⟩ := hu.exists_right_inv
    have h1 : ι (inc (l : ℤ_[l])) * y = 1 := congrArg Subtype.val hxy
    have h2 : inc (l : ℤ_[l]) * ι.symm y = 1 := by
      apply ι.injective
      rw [map_mul, RingEquiv.apply_symm_apply, h1, map_one]
    have h3 := congrArg norm h2
    have h4 : ‖ι.symm y‖ ≤ 1 := (mem_unitBall_iff ι y).mp hy
    rw [norm_mul, hinc, norm_one] at h3
    have h5 : ‖(l : ℤ_[l])‖ < 1 := by
      rw [PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
    nlinarith [norm_nonneg (ι.symm y), norm_nonneg (l : ℤ_[l])]
  have halg : ∀ b : B, ∃ p : ℤ_[l][X], p.IsPrimitive ∧ p.eval₂ c b = 0 := by
    intro b
    obtain ⟨p, hp, h0⟩ := exists_isPrimitive_eval₂_eq_zero (ι.symm (b : ℂ))
    refine ⟨p, hp, Subtype.ext ?_⟩
    have h1 := Polynomial.hom_eval₂ p c B.subtype b
    have h2 := Polynomial.hom_eval₂ p inc ι.toRingHom (ι.symm (b : ℂ))
    have h3 : B.subtype.comp c = ι.toRingHom.comp inc := RingHom.ext fun _ => rfl
    have h4 : ι.toRingHom (ι.symm (b : ℂ)) = B.subtype b := ι.apply_symm_apply _
    rw [h3, ← h4, ← h2] at h1
    have h5 : p.eval₂ inc (ι.symm (b : ℂ)) = 0 := h0
    rw [h5, map_zero] at h1
    exact h1
  have hlR : ((l : ℕ) : ResidueField B) = 0 := by
    have := (residue_eq_zero_iff _).mpr hcl
    simpa using this
  haveI : CharP (ResidueField B) l := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hlR
  letI : Algebra (ZMod l) (ResidueField B) := ZMod.algebra _ l
  haveI : Algebra.IsAlgebraic (ZMod l) (ResidueField B) := isAlgebraic_residueField c hcl halg
  haveI : IsAlgClosed (ResidueField B) :=
    GlobalTheory.isAlgClosed_residueField_of_valuationRing_of_isAlgClosed B ℂ
  haveI : IsAlgClosure (ZMod l) (ResidueField B) := ⟨inferInstance, inferInstance⟩
  exact ⟨(IsAlgClosure.equiv (ZMod l) (ResidueField B) (AlgebraicClosure (ZMod l))).toRingEquiv⟩

theorem val_nonneg_iff (D : D7) (lam : D.what₂.places.Pl) (x : D.what₂.LL) :
    0 ≤ D.what₂.places.val lam x ↔ (D.plEq lam).valuation D.what₂.LL x ≤ 1 := by
  haveI := D.nfLL
  by_cases hx : x = 0
  · simp [hx]
  rw [D.val_eq lam x hx]
  have h0 : (D.plEq lam).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have h1 := WithZero.log_le_log (x := (D.plEq lam).valuation D.what₂.LL x) (y := 1) h0 one_ne_zero
  rw [WithZero.log_one] at h1
  rw [← h1]
  unfold vAdd
  norm_cast
  omega

theorem nonempty_plSide : ∀ D : D7, Nonempty (PlSide D) := by
  intro D
  haveI := D.nfLL
  haveI := D.galLL
  have key : ∀ lam : D.what₂.places.Pl, ∃ ι : Qbar (D.what₂.places.resChar lam) ≃+* ℂ,
      ∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val lam x ↔ ‖ι.symm (D.what₂.embLL x)‖ ≤ 1 := by
    intro lam
    obtain ⟨a, ha⟩ := exists_embedding_inducing_place D.what₂.LL (D.what₂.places.resChar lam)
      (D.plEq lam) (Formalism.BasicNotions.Examples₂.PlOver.resChar_mem D lam)
    obtain ⟨ι, hι⟩ := GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq
      (D.what₂.places.resChar lam) D.what₂.LL a D.what₂.embLL
    refine ⟨ι, fun x => ?_⟩
    have h1 : ι.symm (D.what₂.embLL x) = a x := by
      rw [← hι]; exact ι.symm_apply_apply _
    rw [h1, val_nonneg_iff, valuation_le_one_iff_of_lt_iff _ a ha]
  choose ι hι using key
  exact ⟨⟨ι, hι, fun lam => unitBall (ι lam), fun lam z => mem_unitBall_iff (ι lam) z,
    fun lam => Classical.choice (nonempty_residueField_unitBall_equiv (ι lam))⟩⟩

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareIsoCarriesSquareCubicalStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_iso_carries_square_cubical : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 G).left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t r z N ^ 2 =
        (∏ k : thK.{0}, gv wL (r ≫ thφ G (x3 G) k) z (fun _ => N (r ≫ thφ G (x3 G) k))
          (fun _ => N' (r ≫ thφ G (x3 G) k)) ^ thε k) *
        val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t r z N' ^ 2 := by
  first | exact @GlobalTheory.sq_iso_carries_sq_cube | exact GlobalTheory.sq_iso_carries_sq_cube | (intros; apply GlobalTheory.sq_iso_carries_sq_cube <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareIsoRespectsSymmetryPointwiseStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_iso_respects_symmetry_pointwise : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U.symG r z N ^ 2 =
        (∏ k : Fin 2, gv wL (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k) z
          (fun _ => N (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k))
          (fun _ => N' (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
        val (L := U'.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U'.symG r z N' ^ 2 := by
  first | exact @GlobalTheory.sq_iso_respects_symmetry_pointwise | exact GlobalTheory.sq_iso_respects_symmetry_pointwise | (intros; apply GlobalTheory.sq_iso_respects_symmetry_pointwise <;> assumption)
end

