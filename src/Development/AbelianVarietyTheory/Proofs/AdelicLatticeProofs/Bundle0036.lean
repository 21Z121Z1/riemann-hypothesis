import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormOneApproximationAtLevelPrimes
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0034

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexUnitsSquareUnderRingHomAdicCompletionLe
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sqIdx_hiUnits_anti {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) {m n : ℕ} (h : m ≤ n) :
    hiUnits w n ≤ hiUnits w m := by
  rintro x ⟨hx, hx'⟩
  refine ⟨hx, hx'.trans ?_⟩
  rw [WithZero.exp_le_exp]
  omega

theorem sqIdx_relIndex_hiUnits_add {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) (π : K)
    (R : Finset K) (hπ : w π = WithZero.exp (-1))
    (hR : ∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) (n k : ℕ) :
    (hiUnits w (n + k)).relIndex (hiUnits w n) ≠ 0 ∧
      (hiUnits w (n + k)).relIndex (hiUnits w n) ≤ R.card ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := GlobalTheory.T.relIndex_higherUnits_succ_le_card K w π R (n + k) hπ hR
    have := Subgroup.relIndex_mul_relIndex (hiUnits w (n + k + 1)) (hiUnits w (n + k))
      (hiUnits w n) (sqIdx_hiUnits_anti w (by omega)) (sqIdx_hiUnits_anti w (by omega))
    rw [← add_assoc, ← this]
    refine ⟨mul_ne_zero h1 ih.1, ?_⟩
    rw [pow_succ']
    exact Nat.mul_le_mul h2 ih.2

theorem sqIdx_sqSub_eq_comap {F L : Type} [Field F] [Field L] (φ : F →+* L) :
    sqSub φ = (sqs (⊤ : Subgroup Lˣ)).comap (Units.map (φ : F →* L)) := by
  ext x
  rw [mem_sqSub, Subgroup.mem_comap]
  constructor
  · rintro ⟨r, hr⟩
    have hx : φ (x : F) ≠ 0 := by simp
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hr)
    refine ⟨Units.mk0 r hr0, Subgroup.mem_top _, ?_⟩
    ext
    simp [hr, sq]
  · rintro ⟨r, -, hr⟩
    refine ⟨(r : L), ?_⟩
    have := congrArg (fun u : Lˣ => (u : L)) hr
    simpa [sq] using this.symm

theorem index_sqSub_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), v.valuation F 2 = WithZero.exp (-(e : ℤ)) → (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧ (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e := by
  intro F _ _ v e he
  obtain ⟨⟨π, -, hπ⟩, hval, -, R, hcard, -, hR⟩ := GlobalTheory.T.exists_global_uniformizer_residue_representatives F v
  have h2 : Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) := by
    rw [← he, ← hval, map_ofNat (algebraMap F (v.adicCompletion F))]
  have hsq := GlobalTheory.T.higherUnits_le_squares_higherUnits F v e h2
  set w : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v with hw
  have hA := sqIdx_relIndex_hiUnits_add w _ R hπ hR (e + 1) e
  have hB := sqIdx_relIndex_hiUnits_add w _ R hπ hR 0 (e + 1)
  rw [show e + 1 + e = 2 * e + 1 by ring] at hA
  rw [zero_add] at hB
  have hC0 : (sqs (hiUnits w (e + 1))).relIndex (hiUnits w (e + 1)) ≠ 0 :=
    fun h => hA.1 (Subgroup.relIndex_eq_zero_of_le_left hsq h)
  have hC : (sqs (hiUnits w (e + 1))).relIndex (hiUnits w (e + 1)) ≤ R.card ^ e :=
    (Subgroup.relIndex_le_of_le_left hsq hA.1).trans hA.2
  have hD := GlobalTheory.T.relIndex_squares_le_two_mul_of_subgroup (v.adicCompletion F)ˣ (hiUnits w 0) (hiUnits w (e + 1)) (-1)
    (sqIdx_hiUnits_anti w (by omega)) hB.1 (fun a ha => by
      have h : (a : v.adicCompletion F) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
      rcases sq_eq_one_iff.mp h with h | h
      · left; exact Units.ext h
      · right; exact Units.ext (by simpa using h)) hC0
  have hE := GlobalTheory.T.index_squares_le_two_mul_units_squares (v.adicCompletion F) w _ hπ hD.1
  rw [sqIdx_sqSub_eq_comap, Subgroup.index_comap]
  rw [← Subgroup.relIndex_top_right] at hE
  refine ⟨fun h => hE.1 (Subgroup.relIndex_eq_zero_of_le_right le_top h), ?_⟩
  refine (Subgroup.relIndex_le_of_le_right le_top hE.1).trans (hE.2.trans ?_)
  have hp : R.card ^ e ≤ Ideal.absNorm v.asIdeal ^ e := Nat.pow_le_pow_left hcard e
  have := hD.2
  omega

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNormFromBaseChangeOfPowFinrankCyclic
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm.LocStep

theorem iter_prod {A ι : Type} [CommMonoid A] (T : A →* A) (n : ℕ) (s : Finset ι) (f : ι → A) :
    T^[n] (∏ i ∈ s, f i) = ∏ i ∈ s, T^[n] (f i) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', ih, map_prod]

theorem prod_range_mul_iter {A : Type} [CommMonoid A] (T : A →* A) (d m : ℕ) (x : A) :
    ∏ i ∈ Finset.range (d * m), T^[i] x
      = ∏ k ∈ Finset.range m, (T^[d])^[k] (∏ j ∈ Finset.range d, T^[j] x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.prod_range_add, ih, Finset.prod_range_succ, ← Function.iterate_mul,
      iter_prod]
    congr 1
    exact Finset.prod_congr rfl fun j _ => Function.iterate_add_apply _ _ _ _

theorem prod_cyc {G A : Type} [Group G] [Fintype G] [CommMonoid A] (σ : G)
    (h : ∀ g, g ∈ Subgroup.zpowers σ) (f : G → A) :
    ∏ g, f g = ∏ i ∈ Finset.range (Nat.card G), f (σ ^ i) := by
  classical
  have ho : orderOf σ = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers h
  symm
  refine Finset.prod_bij (fun i _ => σ ^ i) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro i hi j hj hij
    rw [← ho] at hi hj
    exact pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij
  · intro g _
    have := (mem_zpowers_iff_mem_range_orderOf).1 (h g)
    rw [Finset.mem_image] at this
    obtain ⟨i, hi, e⟩ := this
    exact ⟨i, ho ▸ hi, e⟩

theorem telescope {A : Type} [CommMonoid A] (T : A →* A) (d : ℕ) (z : A) :
    (∏ j ∈ Finset.range d, T^[j] (T z)) * z = (∏ j ∈ Finset.range d, T^[j] z) * T^[d] z := by
  rw [← Finset.prod_range_succ, Finset.prod_range_succ']
  rfl

theorem core {A : Type} [CommMonoid A] (T : A →* A) (d m : ℕ) (x a b : A) (hab : a * b = 1)
    (hb : T b = b) (ha : T a = a) (hx : ∏ i ∈ Finset.range (d * m), T^[i] x = a ^ m)
    (h90 : ∀ u : A, ∏ k ∈ Finset.range m, (T^[d])^[k] u = 1 → ∃ z : Aˣ, u * T^[d] z = z) :
    ∃ x' : A, T^[d] x' = x' ∧ ∏ j ∈ Finset.range d, T^[j] x' = a := by
  set P : A → A := fun u => ∏ j ∈ Finset.range d, T^[j] u with hP
  have Pmul : ∀ u v, P (u * v) = P u * P v := fun u v => by
    simp only [hP, iterate_map_mul, Finset.prod_mul_distrib]
  have Pone : P 1 = 1 := by simp only [hP, iterate_map_one, Finset.prod_const_one]
  have hbk : ∀ k, T^[k] b = b := fun k => Function.IsFixedPt.iterate hb k
  obtain ⟨z, hz⟩ := h90 (P x * b) (by
    rw [prod_range_mul_iter] at hx
    have : ∀ k, (T^[d])^[k] (P x * b) = (T^[d])^[k] (P x) * b := fun k => by
      rw [← Function.iterate_mul, iterate_map_mul, hbk]
    simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [hx, ← mul_pow, hab, one_pow])
  have hzz : P z * P (z⁻¹ : Aˣ) = 1 := by rw [← Pmul, Units.mul_inv, Pone]
  have ht : ∀ u, P (T u) * u = P u * T^[d] u := fun u => telescope T d u
  have h1 : P (x * T z * (z⁻¹ : Aˣ)) = a := by
    rw [← Units.mul_left_inj z, Pmul, Pmul]
    calc P x * P (T z) * P (z⁻¹ : Aˣ) * z = P x * (P (T z) * z) * P (z⁻¹ : Aˣ) := by ac_rfl
      _ = P x * T^[d] z * (P z * P (z⁻¹ : Aˣ)) * (a * b) := by rw [ht, hab, mul_one]; ac_rfl
      _ = a * (P x * b * T^[d] z) := by rw [hzz, mul_one]; ac_rfl
      _ = a * z := by rw [hz]
  refine ⟨_, ?_, h1⟩
  generalize x * T z * (z⁻¹ : Aˣ) = w at h1
  have h2 : P (T w) = a := by
    rw [← ha, ← h1]
    simp only [hP, map_prod]
    exact Finset.prod_congr rfl fun j _ => Function.iterate_succ_apply' _ _ _
  have h3 := ht w
  rw [h1, h2] at h3
  calc T^[d] w = b * (a * T^[d] w) := by rw [← mul_assoc, mul_comm b, hab, one_mul]
    _ = w := by rw [← h3, ← mul_assoc, mul_comm b, hab, one_mul]

theorem map_pow_iter {F E K : Type} [Field F] [Field E] [Algebra F E] [CommRing K] [Algebra F K]
    (σ : E ≃ₐ[F] E) (i : ℕ) (y : K ⊗[F] E) :
    Algebra.TensorProduct.map (AlgHom.id K K) ((σ ^ i : E ≃ₐ[F] E) : E →ₐ[F] E) y
      = (Algebra.TensorProduct.map (AlgHom.id K K) (σ : E →ₐ[F] E))^[i] y := by
  induction i with
  | zero =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k e => simp
    | add u v hu hv => rw [map_add, hu, hv]; rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ← ih]
    clear ih
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k e => simp [pow_succ']
    | add u v hu hv => simp only [map_add, hu, hv]

theorem exists_pow_of_pow_eq_one {G : Type} [Group G] [Finite G] (σ : G) (d m : ℕ) (hm : m ≠ 0)
    (h : ∀ g, g ∈ Subgroup.zpowers σ) (ho : orderOf σ = d * m) (g : G) (hg : g ^ m = 1) :
    ∃ k : ℕ, g = σ ^ (d * k) := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (h g))
  rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, ho] at hg
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hm) hg
  exact ⟨k, rfl⟩

end GlobalTheory.CNorm.LocStep

namespace GlobalTheory.CNorm
open LocStep

theorem tnorm_of_tnorm_pow : ∀ (F M E K : Type) [Field F] [CharZero F] [Field M] [Field E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional F E] [IsGalois F E] [Field K] [Algebra F K], IsCyclic (E ≃ₐ[F] E) → ∀ a : F, a ≠ 0 → TNorm F E K (a ^ Module.finrank M E) → TNorm F M K a := by
  intro F M E K _ _ _ _ _ _ _ _ _ _ _ _ hc a ha ⟨x, hx⟩
  haveI : IsAbelianGalois F E := IsAbelianGalois.of_isCyclic F E
  haveI : IsGalois F M := (IsAbelianGalois.tower_bot F M E).toIsGalois
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite F M E
  haveI : FiniteDimensional F M := FiniteDimensional.left F M E
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
  set d := Module.finrank F M with hd
  set m := Module.finrank M E with hm
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have hm0 : m ≠ 0 := Module.finrank_pos.ne'
  have hcard : Nat.card (E ≃ₐ[F] E) = d * m := by
    rw [IsGalois.card_aut_eq_finrank, Module.finrank_mul_finrank]
  have ho : orderOf σ = d * m := (orderOf_eq_card_of_forall_mem_zpowers hσ).trans hcard
  have hτ : orderOf (σ ^ d) = m := by
    rw [orderOf_pow_of_dvd hd0 (ho ▸ dvd_mul_right d m), ho,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  set S := Algebra.TensorProduct.map (AlgHom.id K K) (σ : E →ₐ[F] E) with hS
  let T : K ⊗[F] E →* K ⊗[F] E := S
  have hT : (T : K ⊗[F] E → K ⊗[F] E) = S := rfl
  have hSd : (Algebra.TensorProduct.map (AlgHom.id K K) ((σ ^ d : E ≃ₐ[F] E) : E →ₐ[F] E) :
      K ⊗[F] E → K ⊗[F] E) = S^[d] := funext fun y => map_pow_iter σ d y
  have haK : algebraMap F K a ≠ 0 := (_root_.map_ne_zero _).2 ha
  obtain ⟨w, hw, hw'⟩ := core T d m x (algebraMap K _ (algebraMap F K a))
    (algebraMap K _ (algebraMap F K a)⁻¹) (by rw [← map_mul, mul_inv_cancel₀ haK, map_one])
    (S.commutes _) (S.commutes _)
    (by
      have := GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates F E K x
      rw [hx, prod_cyc σ hσ, hcard, map_pow, map_pow] at this
      rw [this]
      exact Finset.prod_congr rfl fun i _ => (map_pow_iter σ i x).symm)
    (by
      intro u hu
      have := GlobalTheory.T.hilbert90_baseChange' F E K (σ ^ d) m hτ u (by rw [hSd]; exact hu)
      rw [hSd] at this
      exact this)
  obtain ⟨z, rfl⟩ := GlobalTheory.T.exists_tensor_eq_of_fixed_by_algEquiv F M E K w (by
    intro h
    obtain ⟨k, hk⟩ := exists_pow_of_pow_eq_one σ d m hm0 hσ ho (h.restrictScalars F) (by
      have h1 : h ^ m = 1 := by
        rw [hm, ← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
      have := map_pow (AlgEquiv.restrictScalarsHom F (S := M) (A := E)) h m
      rw [h1, map_one] at this
      exact this.symm)
    rw [hk, map_pow_iter, Function.iterate_mul]
    exact Function.IsFixedPt.iterate hw k)
  set ι := Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) with hι
  have hinj : Function.Injective ι :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      (IsScalarTower.toAlgHom F M E).toLinearMap (algebraMap M E).injective
  let σ' : M ≃ₐ[F] M := AlgEquiv.restrictNormalHom M σ
  have hσ' : ∀ g, g ∈ Subgroup.zpowers σ' := by
    intro g
    obtain ⟨g', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := M) E g
    obtain ⟨k, rfl⟩ := hσ g'
    exact ⟨k, (map_zpow _ _ _).symm⟩
  have hcomm : ∀ u : K ⊗[F] M,
      ι (Algebra.TensorProduct.map (AlgHom.id K K) (σ' : M →ₐ[F] M) u) = S (ι u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul k e =>
      have : algebraMap M E (σ' e) = σ (algebraMap M E e) :=
        AlgEquiv.restrictNormal_commutes σ M e
      simp [hι, hS, this]
    | add u v hu hv => simp only [map_add, hu, hv]
  refine ⟨z, ?_⟩
  apply (algebraMap K (K ⊗[F] M)).injective
  apply hinj
  rw [GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates F M K z, prod_cyc σ' hσ', IsGalois.card_aut_eq_finrank, ι.commutes, ← hw',
    map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow_iter]
  exact Function.Semiconj.iterate_right hcomm i z

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MinNormTensorStabilizerConjTransposeInvariant
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma posDef_det_one_exists_unitary_exp_diagonal_sum_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (hP : P.PosDef) (hdet : P.det = 1) :
    ∃ (U : Matrix ι ι ℂ) (δ : ι → ℝ), U * Uᴴ = 1 ∧ ∑ i, δ i = 0 ∧
      P = (U * diagonal fun i => ((Real.exp (2 * δ i) : ℝ) : ℂ)) * Uᴴ := by
  refine ⟨(hP.1.eigenvectorUnitary : Matrix ι ι ℂ), fun i => Real.log (hP.1.eigenvalues i) / 2,
    ?_, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.mul_star_self_of_mem hP.1.eigenvectorUnitary.2
  · have h := hP.1.det_eq_prod_eigenvalues
    rw [hdet] at h
    have hprod' : ((∏ i, hP.1.eigenvalues i : ℝ) : ℂ) = 1 := by push_cast; exact h.symm
    have hprod : ∏ i, hP.1.eigenvalues i = 1 := by exact_mod_cast hprod'
    rw [← Finset.sum_div, ← Real.log_prod (fun i _ => (hP.eigenvalues_pos i).ne'), hprod,
      Real.log_one, zero_div]
  · conv_lhs => rw [hP.1.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    congr 3
    funext i
    simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id]
    rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log (hP.eigenvalues_pos i)]
    rfl

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma unitary_conj_exp_diagonal_conjTranspose {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (δ : ι → ℝ) (s : ℝ) :
    ((U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ)ᴴ =
      (U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ := by
  simp [conjTranspose_mul, Matrix.mul_assoc, diagonal_conjTranspose, -Complex.ofReal_exp, Pi.star_def]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma unitary_conj_exp_diagonal_mul_add_exponents {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U * Uᴴ = 1) (δ : ι → ℝ) (s t : ℝ) :
    ((U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ) *
        ((U * diagonal fun i => ((Real.exp (t * δ i) : ℝ) : ℂ)) * Uᴴ) =
      (U * diagonal fun i => ((Real.exp ((s + t) * δ i) : ℝ) : ℂ)) * Uᴴ := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU', Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _),
    diagonal_mul_diagonal]
  simp only [← Complex.ofReal_mul, ← Real.exp_add, ← add_mul]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma exists_unitary_exp_diagonal_fixing_of_nsq_eq {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (d : Fin m → ℕ) (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (hv : _root_.GlobalTheory.ClassFin.IsMinVec d v)
    (g : Matrix ι ι ℂ) (hg : g.det = 1)
    (hn : _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v g) = _root_.GlobalTheory.ClassFin.nsq v) :
    ∃ (U : Matrix ι ι ℂ) (δ : ι → ℝ), U * Uᴴ = 1 ∧ ∑ i, δ i = 0 ∧
      g * gᴴ = (U * diagonal fun i => ((Real.exp (2 * δ i) : ℝ) : ℂ)) * Uᴴ ∧
      ∀ s : ℝ, _root_.GlobalTheory.ClassFin.act d v
        ((U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ) = v := by
  have hdetP : (g * gᴴ).det = 1 := by simp [hg]
  have hP : (g * gᴴ).PosDef :=
    (posSemidef_self_mul_conjTranspose g).posDef_iff_isUnit.mpr
      ((isUnit_iff_isUnit_det _).mpr (by rw [hdetP]; exact isUnit_one))
  obtain ⟨U, δ, hU, hδ, hgP⟩ := posDef_det_one_exists_unitary_exp_diagonal_sum_zero _ hP hdetP
  refine ⟨U, δ, hU, hδ, hgP, ?_⟩
  obtain ⟨-, hactmul, -⟩ := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d v
  have hgu : IsUnit g.det := by rw [hg]; exact isUnit_one
  have hhh : ((U * diagonal fun i => ((Real.exp (1 * δ i) : ℝ) : ℂ)) * Uᴴ) *
      ((U * diagonal fun i => ((Real.exp (1 * δ i) : ℝ) : ℂ)) * Uᴴ)ᴴ = g * gᴴ := by
    rw [unitary_conj_exp_diagonal_conjTranspose, unitary_conj_exp_diagonal_mul_add_exponents hU, hgP]
    norm_num
  set h : Matrix ι ι ℂ := (U * diagonal fun i => ((Real.exp (1 * δ i) : ℝ) : ℂ)) * Uᴴ with hh
  have hk : (g⁻¹ * h) * (g⁻¹ * h)ᴴ = 1 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h, hhh, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, nonsing_inv_mul _ hgu, Matrix.one_mul, conjTranspose_nonsing_inv,
      mul_nonsing_inv _ (by simp [hg])]
  have hgk : h = g * (g⁻¹ * h) := by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hgu, Matrix.one_mul]
  have hnh : _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v h) = _root_.GlobalTheory.ClassFin.nsq v := by
    rw [hgk, hactmul, (_root_.GlobalTheory.ClassFin.ActNorm.act_norm_continuity ι m d).1 _ _ hk, hn]
  rw [hh] at hnh
  exact _root_.GlobalTheory.ClassFin.act_exp_eq_of_isMinVec ι m d v U δ hv hU hδ (by simpa only [one_mul] using hnh)

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in

theorem _root_.GlobalTheory.ClassFin.act_conjTranspose_of_isMinVec : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ)
    (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ), _root_.GlobalTheory.ClassFin.IsMinVec d v → ∀ g : Matrix ι ι ℂ, g.det = 1 →
      _root_.GlobalTheory.ClassFin.act d v g = v → _root_.GlobalTheory.ClassFin.act d v gᴴ = v := by
  intro ι _ _ m d v hv g hg hgv
  obtain ⟨U, δ, -, -, hgP, hfix⟩ := exists_unitary_exp_diagonal_fixing_of_nsq_eq d v hv g hg (by rw [hgv])
  obtain ⟨-, hactmul, -⟩ := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d v
  calc _root_.GlobalTheory.ClassFin.act d v gᴴ
      = _root_.GlobalTheory.ClassFin.act d (_root_.GlobalTheory.ClassFin.act d v g) gᴴ := by rw [hgv]
    _ = _root_.GlobalTheory.ClassFin.act d v (g * gᴴ) := (hactmul g gᴴ).symm
    _ = v := by rw [hgP]; exact hfix 2

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormOneApproximationAtLevelPrimesStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOne_approximation_at_level_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), (∀ x, c (c x) = x) → c ≠ 1 → ∀ (u : E) (N D : ℕ), u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ (∃ t : ℕ, t.Coprime N ∧ ∃ b : 𝓞 E, (t : E) * (u' / u - 1) = (D : E) * (b : E)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ (∃ b : 𝓞 E, (s : E) * (u' - 1) = (D : E) * (b : E)) ∧ ∃ b : 𝓞 E, (s : E) * (u'⁻¹ - 1) = (D : E) * (b : E) := by
  first | exact @GlobalTheory.UnRep.normOne_approx | exact GlobalTheory.UnRep.normOne_approx | (intros; apply GlobalTheory.UnRep.normOne_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OfIntermediateFieldTower
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem bijective_mul_out_inv {H G : Type} [Group H] [Group G] (φ : H →* G)
    (hφ : Function.Injective φ) :
    Function.Bijective (fun p : H × (G ⧸ φ.range) => φ p.1 * (p.2.out)⁻¹) := by
  constructor
  · rintro ⟨h, q⟩ ⟨h', q'⟩ e
    simp only at e
    have hq : q = q' := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
      refine ⟨h⁻¹ * h', ?_⟩
      rw [map_mul, map_inv]
      calc (φ h)⁻¹ * φ h' = (φ h)⁻¹ * (φ h' * (q'.out)⁻¹) * q'.out := by group
        _ = (φ h)⁻¹ * (φ h * (q.out)⁻¹) * q'.out := by rw [e]
        _ = _ := by group
    subst hq
    rw [hφ (mul_right_cancel e)]
  · intro g
    have : ((g⁻¹ : G) : G ⧸ φ.range).out⁻¹ * g⁻¹ ∈ φ.range := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    obtain ⟨h, hh⟩ := this
    refine ⟨(h⁻¹, ((g⁻¹ : G) : G ⧸ φ.range)), ?_⟩
    simp only [map_inv, hh]
    group

theorem TNorm.of_tower (F M E K : Type) [Field F] [Field M] [Field E] [Algebra F M] [Algebra M E]
    [Algebra F E] [IsScalarTower F M E] [FiniteDimensional F E] [IsGalois F E] [Field K]
    [Algebra F K] [Algebra M K] [IsScalarTower F M K] (x : F) (hx : TNorm F E K x) :
    TNorm M E K (algebraMap F M x) := by
  classical
  obtain ⟨y, hy⟩ := hx
  haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite F M E
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  let π : K ⊗[F] E →ₐ[K] K ⊗[M] E := Algebra.TensorProduct.mapOfCompatibleSMul M F K K E
  let φ : (E ≃ₐ[M] E) →* (E ≃ₐ[F] E) :=
    { toFun := fun h => h.restrictScalars F, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := AlgEquiv.restrictScalars_injective F
  haveI : Fintype ((E ≃ₐ[F] E) ⧸ φ.range) := Fintype.ofFinite _
  have key : ∀ (h : E ≃ₐ[M] E) (g : E ≃ₐ[F] E) (z : K ⊗[F] E),
      Algebra.TensorProduct.map (AlgHom.id K K) (h : E →ₐ[M] E)
        (π (Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) z)) =
      π (Algebra.TensorProduct.map (AlgHom.id K K) ((φ h * g : E ≃ₐ[F] E) : E →ₐ[F] E) z) := by
    intro h g z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  refine ⟨π (∏ q : (E ≃ₐ[F] E) ⧸ φ.range,
    Algebra.TensorProduct.map (AlgHom.id K K) (((q.out)⁻¹ : E ≃ₐ[F] E) : E →ₐ[F] E) y), ?_⟩
  apply (algebraMap K (K ⊗[M] E)).injective
  rw [GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates M E K, ← IsScalarTower.algebraMap_apply F M K x, ← hy, ← π.commutes,
    GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates F E K, map_prod π, map_prod π,
    ← (bijective_mul_out_inv φ hφ).prod_comp (fun g : E ≃ₐ[F] E =>
      π (Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y)), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun h _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun q _ => key h _ y

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.QuasiReflectionEqMulTransvectionsOfHyperbolicPlaStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiReflection_eq_mul_transvections_of_hyperbolicPlane : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → ∀ (x z : Fin n → E) (a u : E), hf σ G z z = 0 → hf σ G x z ≠ 0 → hf σ G x x ≠ 0 → hf σ G (x + a • z) (x + a • z) ≠ 0 → u * σ u = 1 → ∃ m ∈ TvGen σ G, tv σ G x ((u - 1) / hf σ G x x) = m * tv σ G (x + a • z) ((u - 1) / hf σ G (x + a • z) (x + a • z)) := by
  first | exact @GlobalTheory.UTrans.PlaneRefl.quasiRefl_eq_mul_of_plane | exact GlobalTheory.UTrans.PlaneRefl.quasiRefl_eq_mul_of_plane | (intros; apply GlobalTheory.UTrans.PlaneRefl.quasiRefl_eq_mul_of_plane <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulCardInfinitePlaceLeQuadraticStatement
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_card_infinitePlace_le_quadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → 2 * Fintype.card (InfinitePlace F) ≤ Fintype.card (InfinitePlace E) + tReal F δ := by
  first | exact @GlobalTheory.QNorm.two_mul_card_infinitePlace_le | exact GlobalTheory.QNorm.two_mul_card_infinitePlace_le | (intros; apply GlobalTheory.QNorm.two_mul_card_infinitePlace_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidAdjustIntegralAwayStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTransvectionSubmonoid_adjust_integral_away : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → IsHerm (c : E →+* E) G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ m ∈ TvGen (c : E →+* E) G, ∀ b : ℕ, 0 < b → ∀ N : ℕ, ∃ m' ∈ TvGen (c : E →+* E) G, ∃ k e : ℕ, k.Coprime b ∧ ∀ v ∈ L, (∃ w ∈ L, k • (m' *ᵥ v - m *ᵥ v) = b ^ N • w) ∧ b ^ e • (m' *ᵥ v) ∈ L ∧ b ^ e • (m'⁻¹ *ᵥ v) ∈ L := by
  first | exact @GlobalTheory.UTrans.tvGen_adjust | exact GlobalTheory.UTrans.tvGen_adjust | (intros; apply GlobalTheory.UTrans.tvGen_adjust <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidNormalDetOneStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTransvectionSubmonoid_normal_det_one : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∀ γ, IsU σ G γ → γ.det * σ γ.det = 1 ∧ IsU σ G γ⁻¹) ∧ (∀ m ∈ TvGen σ G, IsU σ G m ∧ m.det = 1 ∧ m⁻¹ ∈ TvGen σ G ∧ ∀ γ, IsU σ G γ → ∃ m' ∈ TvGen σ G, γ * m = m' * γ ∧ ∃ m'' ∈ TvGen σ G, m * γ = γ * m'') := by
  first | exact @GlobalTheory.UTrans.tvGen_normal | exact GlobalTheory.UTrans.tvGen_normal | (intros; apply GlobalTheory.UTrans.tvGen_normal <;> assumption)
end

