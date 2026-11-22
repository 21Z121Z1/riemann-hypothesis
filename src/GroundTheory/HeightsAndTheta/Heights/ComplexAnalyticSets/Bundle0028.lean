import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionsGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric

open MvPolynomial Matrix

noncomputable section

def entries {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : Fin a × Fin b → ℂ := fun ij => A ij.1 ij.2

def rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  bind₁ (fun ij : Fin d × Fin n => ∑ l, C (F (s ij.1) l) * X (l, ij.2)) p

theorem eval_rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) :
    eval (entries U) (rowsPoly F s p) = eval (entries ((F * U).submatrix s id)) p := by
  change eval₂Hom (RingHom.id ℂ) (entries U) (bind₁ _ p) = eval₂Hom (RingHom.id ℂ) _ p
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  simp [entries, Matrix.mul_apply]

theorem exists_rows_eq {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) (A : Matrix (Fin d) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, (F * U).submatrix s id = A := by
  refine ⟨star F * Matrix.of (Function.extend s (fun i => A i) 0), ?_⟩
  rw [← Matrix.mul_assoc, mem_unitaryGroup_iff.mp hF, Matrix.one_mul]
  ext i j
  simp [hs.extend_apply]

theorem rowsPoly_ne_zero {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) {p : MvPolynomial (Fin d × Fin n) ℂ}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : eval (entries A) p ≠ 0) : rowsPoly F s p ≠ 0 := by
  obtain ⟨U, hU⟩ := exists_rows_eq hF hs A
  intro h
  apply hA
  rw [← hU, ← eval_rowsPoly, h, map_zero]

theorem proof (hO : FiniteProjectionsContainOpen.Statement) (hU : UnitaryZariskiDense.Statement) :
    FiniteProjectionsGeneric.Statement := by
  classical
  intro n d J hJ hd
  obtain ⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hsub⟩ := hO n d J hJ hd
  have hA₀' := hA₀
  rw [hS] at hA₀'
  obtain ⟨p, hpS, hp⟩ := hA₀'
  have good : ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (entries A) p ≠ 0 → IsFiniteProjection J A :=
    fun A hA => hsub (by rw [hS]; exact ⟨p, hpS, hA⟩)
  have hdn : d ≤ n := by
    have h := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
    exact_mod_cast h
  refine ⟨⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hsub⟩, fun D hD hcl => ?_, fun m F => ?_⟩
  · obtain ⟨U, hUu, hUp⟩ := hU n (rowsPoly 1 (Fin.castLE hdn) p)
      (rowsPoly_ne_zero (one_mem _) (Fin.castLE_injective hdn) hp)
    have hUp' : eval (entries (U.submatrix (Fin.castLE hdn) id)) p ≠ 0 := by
      have := eval_rowsPoly 1 (Fin.castLE hdn) p U
      rw [Matrix.one_mul] at this
      exact this ▸ hUp
    have hAo : U.submatrix (Fin.castLE hdn) id ∈ orthoRows d n := by
      show _ * _ = _
      rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
        ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hUu,
        submatrix_one _ (Fin.castLE_injective hdn)]
    have hopen : IsOpen {B : Matrix (Fin d) (Fin n) ℂ | eval (entries B) p ≠ 0} :=
      isOpen_ne_fun ((MvPolynomial.continuous_eval p).comp
        (continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2)) continuous_const
    obtain ⟨B, hBp, hBD⟩ := mem_closure_iff.mp (hcl hAo) _ hopen hUp'
    exact ⟨B, hBD, good B hBp⟩
  · have hQ : (∏ ks : Fin m × (Fin d ↪ Fin n), rowsPoly (F ks.1 : Matrix (Fin n) (Fin n) ℂ) ks.2 p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun ks _ => rowsPoly_ne_zero (F ks.1).2 ks.2.injective hp
    obtain ⟨U, hUu, hUQ⟩ := hU n _ hQ
    refine ⟨U, hUu, fun k s => good _ ?_⟩
    rw [map_prod] at hUQ
    have := Finset.prod_ne_zero_iff.mp hUQ (k, s) (Finset.mem_univ _)
    change eval (entries U) (rowsPoly _ _ p) ≠ 0 at this
    rwa [eval_rowsPoly] at this

end

end GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFlatLocalRegularElement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing TensorProduct
open scoped Pointwise

section Flat

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

theorem lid_rTensor_subtype_mem_smul_top (I : Ideal A) (t : I ⊗[A] M) :
    TensorProduct.lid A M (I.subtype.rTensor M t) ∈ I • (⊤ : Submodule A M) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul i m => simpa using Submodule.smul_mem_smul i.2 Submodule.mem_top
  | add s t hs ht => rw [map_add, map_add]; exact add_mem hs ht

theorem exists_lid_rTensor_subtype_eq (I : Ideal A) {x : M} (hx : x ∈ I • (⊤ : Submodule A M)) :
    ∃ t : I ⊗[A] M, TensorProduct.lid A M (I.subtype.rTensor M t) = x := by
  refine Submodule.smul_induction_on hx (fun a ha m _ => ⟨⟨a, ha⟩ ⊗ₜ m, by simp⟩) ?_
  rintro x x' ⟨s, rfl⟩ ⟨s', rfl⟩
  exact ⟨s + s', by rw [map_add, map_add]⟩

theorem mem_colon_smul_top_of_flat [Module.Flat A M] (J : Ideal A) (a : A) {v : M}
    (hv : a • v ∈ J • (⊤ : Submodule A M)) :
    v ∈ LinearMap.ker (J.mkQ ∘ₗ LinearMap.mulRight A a) • (⊤ : Submodule A M) := by
  set g : A →ₗ[A] A ⧸ J := J.mkQ ∘ₗ LinearMap.mulRight A a
  have hex := Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map g)
  have h0 : g.rTensor M ((1 : A) ⊗ₜ v) = 0 := by
    apply (TensorProduct.quotTensorEquivQuotSMul M J).injective
    rw [map_zero, LinearMap.rTensor_tmul]
    have : g 1 = Ideal.Quotient.mk J a := by simp [g, Ideal.Quotient.mk_eq_mk]
    rw [this, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, Submodule.Quotient.mk_eq_zero]
    exact hv
  obtain ⟨t, ht⟩ := (hex ((1 : A) ⊗ₜ v)).mp h0
  have := lid_rTensor_subtype_mem_smul_top (LinearMap.ker g) t
  rwa [ht, TensorProduct.lid_tmul, one_smul] at this

end Flat

theorem exists_not_mem_forall_mul_mem {R : Type} [CommRing R] (m J : Ideal R) (hJ : J ≠ ⊤)
    (h : ∃ n, m ^ n ≤ J) : ∃ a ∉ J, ∀ r ∈ m, r * a ∈ J := by
  classical
  have hkJ : m ^ Nat.find h ≤ J := Nat.find_spec h
  have hk0 : Nat.find h ≠ 0 := by
    intro h0
    apply hJ
    rw [h0, pow_zero, Ideal.one_eq_top] at hkJ
    exact top_le_iff.mp hkJ
  obtain ⟨a, ha, haJ⟩ := SetLike.not_le_iff_exists.mp
    (Nat.find_min h (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos))
  refine ⟨a, haJ, fun r hr => hkJ ?_⟩
  have : r * a ∈ m ^ (1 + (Nat.find h - 1)) := by
    rw [pow_add, pow_one]
    exact Ideal.mul_mem_mul hr ha
  rwa [Nat.add_sub_cancel' (Nat.pos_of_ne_zero hk0)] at this

section Local

variable {A B M : Type} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

theorem mem_smul_top_iff_mem_map_smul_top (I : Ideal A) (x : M) :
    x ∈ I • (⊤ : Submodule A M) ↔ x ∈ I.map (algebraMap A B) • (⊤ : Submodule B M) := by
  rw [← Submodule.restrictScalars_mem A (I.map (algebraMap A B) • (⊤ : Submodule B M)) x,
    Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

theorem smul_mem_smul_top_of_mem (I : Ideal A) (y : B) {x : M}
    (hx : x ∈ I • (⊤ : Submodule A M)) : y • x ∈ I • (⊤ : Submodule A M) := by
  rw [mem_smul_top_iff_mem_map_smul_top (B := B)] at hx ⊢
  exact Submodule.smul_mem _ y hx

variable [IsNoetherianRing A] [IsLocalRing A] [Module.Flat A M]

theorem smul_regular_mod_of_pow_le (y : B)
    (h0 : ∀ u : M, y • u ∈ maximalIdeal A • (⊤ : Submodule A M) →
      u ∈ maximalIdeal A • (⊤ : Submodule A M)) (J : Ideal A) :
    (∃ n, maximalIdeal A ^ n ≤ J) →
      ∀ z : M, y • z ∈ J • (⊤ : Submodule A M) → z ∈ J • (⊤ : Submodule A M) := by
  induction J using WellFoundedGT.induction with
  | _ J ih =>
  intro hpow z hz
  by_cases hJ : J = ⊤
  · subst hJ
    rw [Submodule.top_smul]
    exact Submodule.mem_top
  obtain ⟨a, haJ, hma⟩ := exists_not_mem_forall_mul_mem (maximalIdeal A) J hJ hpow
  have hlt : J < J ⊔ Ideal.span {a} :=
    lt_of_le_of_ne le_sup_left fun h =>
      haJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))
  have hz' := ih _ hlt (hpow.imp fun n hn => hn.trans le_sup_left) z
    (Submodule.smul_mono_left le_sup_left hz)
  rw [Submodule.sup_smul, Submodule.mem_sup] at hz'
  obtain ⟨w, hw, v, hv, rfl⟩ := hz'
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hv
  obtain ⟨u, -, rfl⟩ := hv
  have hyw := smul_mem_smul_top_of_mem J y hw
  have hau : a • (y • u) ∈ J • (⊤ : Submodule A M) := by
    rw [smul_comm]
    have : y • (a • u) = y • (w + a • u) - y • w := by rw [smul_add]; abel
    rw [this]
    exact sub_mem hz hyw
  have hK : LinearMap.ker (J.mkQ ∘ₗ LinearMap.mulRight A a) ≤ maximalIdeal A := by
    intro r hr
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulRight_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hr
    by_contra hrm
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hrm
    obtain ⟨r', rfl⟩ := hrm
    apply haJ
    have := J.mul_mem_left (↑r'⁻¹ : A) hr
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this
  have hu := h0 u (Submodule.smul_mono_left hK (mem_colon_smul_top_of_flat J a hau))
  refine add_mem hw ?_
  refine Submodule.smul_induction_on hu (fun r hr m _ => ?_) (fun x x' hx hx' => ?_)
  · rw [smul_smul, mul_comm]
    exact Submodule.smul_mem_smul (hma r hr) Submodule.mem_top
  · rw [smul_add]
    exact add_mem hx hx'

variable [IsNoetherianRing B] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Module.Finite B M]

theorem smul_regular_mod_ideal (y : B)
    (h0 : ∀ u : M, y • u ∈ maximalIdeal A • (⊤ : Submodule A M) →
      u ∈ maximalIdeal A • (⊤ : Submodule A M)) (I : Ideal A) (z : M)
    (hz : y • z ∈ I • (⊤ : Submodule A M)) : z ∈ I • (⊤ : Submodule A M) := by
  set P : Submodule B M := I.map (algebraMap A B) • ⊤
  have hle : (maximalIdeal A).map (algebraMap A B) ≤ Ideal.jacobson ⊥ :=
    (IsLocalRing.map_maximalIdeal_le _).trans (IsLocalRing.maximalIdeal_le_jacobson _)
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M ⧸ P) _ hle
  rw [mem_smul_top_iff_mem_map_smul_top (B := B), ← Submodule.Quotient.mk_eq_zero P]
  have hmem : Submodule.Quotient.mk (p := P) z ∈
      (⨅ i : ℕ, ((maximalIdeal A).map (algebraMap A B)) ^ i • (⊤ : Submodule B (M ⧸ P))) := by
    rw [Submodule.mem_iInf]
    intro n
    have hn := smul_regular_mod_of_pow_le y h0 (I ⊔ maximalIdeal A ^ n) ⟨n, le_sup_right⟩ z
      (Submodule.smul_mono_left le_sup_left hz)
    rw [Submodule.sup_smul, Submodule.mem_sup] at hn
    obtain ⟨w, hw, v, hv, rfl⟩ := hn
    rw [mem_smul_top_iff_mem_map_smul_top (B := B)] at hw hv
    rw [Ideal.map_pow] at hv
    rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero P).mpr hw, zero_add]
    have hmap : (((maximalIdeal A).map (algebraMap A B)) ^ n • (⊤ : Submodule B M)).map P.mkQ ≤
        ((maximalIdeal A).map (algebraMap A B)) ^ n • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact hmap (Submodule.mem_map_of_mem hv)
  rw [hK] at hmem
  exact (Submodule.mem_bot B).mp hmem

end Local

theorem FlatLocalRegularElement.proof : FlatLocalRegularElement.Statement := by
  intro A B _ _ _ _ _ _ _ hloc M _ _ _ _ _ _ y _ hreg
  have h0 : ∀ u : M, y • u ∈ maximalIdeal A • (⊤ : Submodule A M) →
      u ∈ maximalIdeal A • (⊤ : Submodule A M) := by
    intro u hu
    rw [mem_smul_top_iff_mem_map_smul_top (B := B), ← Submodule.Quotient.mk_eq_zero] at hu ⊢
    refine hreg ?_
    show y • Submodule.Quotient.mk u = y • (0 : M ⧸ _)
    rw [smul_zero, ← Submodule.Quotient.mk_smul, hu]
  have hR := smul_regular_mod_ideal (B := B) y h0
  refine ⟨fun a b hab => ?_, ?_⟩
  · have hab' : y • a = y • b := hab
    have h := hR ⊥ (a - b) (by rw [Submodule.bot_smul, Submodule.mem_bot, smul_sub, hab', sub_self])
    rw [Submodule.bot_smul, Submodule.mem_bot] at h
    exact sub_eq_zero.mp h
  · rw [Module.Flat.iff_rTensor_injective']
    intro I
    let π : M →ₗ[A] QuotSMulTop y M := (Submodule.mkQ (y • (⊤ : Submodule B M))).restrictScalars A
    let Y : M →ₗ[A] M := (LinearMap.lsmul B M y).restrictScalars A
    let μM : I ⊗[A] M →ₗ[A] M := TensorProduct.lid A M ∘ₗ I.subtype.rTensor M
    let μN : I ⊗[A] QuotSMulTop y M →ₗ[A] QuotSMulTop y M :=
      TensorProduct.lid A (QuotSMulTop y M) ∘ₗ I.subtype.rTensor (QuotSMulTop y M)
    have hμM : Function.Injective μM :=
      (TensorProduct.lid A M).injective.comp
        (Module.Flat.rTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)
    have natπ : μN ∘ₗ π.lTensor I = π ∘ₗ μM :=
      TensorProduct.ext' fun i m => by simp [μN, μM, π]
    have natY : μM ∘ₗ Y.lTensor I = Y ∘ₗ μM :=
      TensorProduct.ext' fun i m => by simp [μM, Y, smul_comm (i : A) y m]
    have hπY : π ∘ₗ Y = 0 := LinearMap.ext fun m =>
      (Submodule.Quotient.mk_eq_zero _).mpr
        (Submodule.smul_mem_pointwise_smul m y ⊤ Submodule.mem_top)
    refine Function.Injective.of_comp (f := TensorProduct.lid A (QuotSMulTop y M)) ?_
    change Function.Injective μN
    rw [injective_iff_map_eq_zero]
    intro t ht
    have hπs : Function.Surjective π := Submodule.mkQ_surjective (y • (⊤ : Submodule B M))
    obtain ⟨s, rfl⟩ := LinearMap.lTensor_surjective I hπs t
    have h1 : π (μM s) = 0 := by
      rw [← LinearMap.comp_apply π μM, ← natπ, LinearMap.comp_apply]
      exact ht
    have h2 : μM s ∈ y • (⊤ : Submodule B M) := (Submodule.Quotient.mk_eq_zero _).mp h1
    obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h2
    have h3 : y • z ∈ I • (⊤ : Submodule A M) := hz ▸ lid_rTensor_subtype_mem_smul_top I s
    obtain ⟨s', hs'⟩ := exists_lid_rTensor_subtype_eq I (hR I z h3)
    have h4 : s = Y.lTensor I s' := by
      apply hμM
      rw [← LinearMap.comp_apply μM (Y.lTensor I), natY, LinearMap.comp_apply]
      change μM s = y • μM s'
      rw [show μM s' = z from hs', hz]
    rw [h4, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπY, LinearMap.lTensor_zero,
      LinearMap.zero_apply]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFlatLocalRegularSequence
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence Pointwise

def quotSMulTopQuotIdealSMulTopEquiv {B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
    (I : Ideal B) (y : B) :
    QuotSMulTop y (M ⧸ (I • ⊤ : Submodule B M)) ≃ₗ[B]
      (QuotSMulTop y M ⧸ (I • ⊤ : Submodule B (QuotSMulTop y M))) :=
  (Submodule.quotEquivOfEq ((y • (⊤ : Submodule B M)).map (I • (⊤ : Submodule B M)).mkQ) (y • ⊤)
      (by rw [Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ])).symm ≪≫ₗ
    Submodule.quotientQuotientEquivQuotientSup (I • ⊤) (y • ⊤) ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (sup_comm _ _) ≪≫ₗ
    (Submodule.quotientQuotientEquivQuotientSup (y • ⊤) (I • ⊤)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ])

theorem FlatLocalRegularElement.iterate (h : FlatLocalRegularElement.Statement)
    {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B) (hl : IsLocalHom (algebraMap A B))
    (ys : List B) (hys : ∀ y ∈ ys, y ∈ maximalIdeal B)
    (M : Type) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (hfin : Module.Finite B M) (hflat : Module.Flat A M)
    (hreg : IsWeaklyRegular (M ⧸ ((maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B M))) ys) :
    IsWeaklyRegular M ys ∧ Module.Flat A (M ⧸ (Ideal.ofList ys • (⊤ : Submodule B M))) := by
  induction ys generalizing M with
  | nil =>
    refine ⟨IsWeaklyRegular.nil B M, ?_⟩
    have e : (M ⧸ (Ideal.ofList ([] : List B) • (⊤ : Submodule B M))) ≃ₗ[B] M :=
      Submodule.quotEquivOfEqBot _ (by rw [Ideal.ofList_nil, Submodule.bot_smul])
    exact Module.Flat.of_linearEquiv (e.restrictScalars A)
  | cons y ys ih =>
    rw [isWeaklyRegular_cons_iff] at hreg
    obtain ⟨hyM, hflat'⟩ := h A B hA hB hl M hfin hflat y (hys y List.mem_cons_self) hreg.1
    have hfin' : Module.Finite B (QuotSMulTop y M) := inferInstance
    obtain ⟨h1, h2⟩ := ih (fun z hz => hys z (List.mem_cons_of_mem _ hz)) (QuotSMulTop y M) hfin' hflat'
      (((quotSMulTopQuotIdealSMulTopEquiv _ y).isWeaklyRegular_congr ys).mp hreg.2)
    refine ⟨(isWeaklyRegular_cons_iff M y ys).mpr ⟨hyM, h1⟩, ?_⟩
    have : Module.Flat A (QuotSMulTop y M ⧸ (Ideal.ofList ys • (⊤ : Submodule B (QuotSMulTop y M)))) := h2
    exact Module.Flat.of_linearEquiv
      ((Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M y ys).restrictScalars A)

theorem FlatLocalRegularSequence.proof (h : FlatLocalRegularElement.Statement) :
    FlatLocalRegularSequence.Statement := by
  intro A B _ _ _ _ _ hA hB hl hflat rs ys hrs hreg hys hfib
  set I := (maximalIdeal A).map (algebraMap A B) with hI
  have hfib' : IsWeaklyRegular (B ⧸ (I • ⊤ : Submodule B B)) ys := by
    have e : (B ⧸ I) ≃ₗ[B] (B ⧸ (I • ⊤ : Submodule B B)) :=
      Submodule.quotEquivOfEq _ _ (by rw [Ideal.smul_eq_mul, Ideal.mul_top])
    rw [← Ideal.Quotient.algebraMap_eq, isWeaklyRegular_map_algebraMap_iff] at hfib
    exact (e.isWeaklyRegular_congr ys).mp hfib
  obtain ⟨hysB, hflatQ⟩ :=
    FlatLocalRegularElement.iterate h hA hB hl ys hys B inferInstance hflat hfib'
  have hrsN : IsWeaklyRegular (B ⧸ (Ideal.ofList ys • (⊤ : Submodule B B))) rs :=
    ((TensorProduct.lid A _).isWeaklyRegular_congr rs).mp (hreg.isWeaklyRegular_rTensor)
  have happ : IsWeaklyRegular B (ys ++ rs.map (algebraMap A B)) :=
    (isWeaklyRegular_append_iff B ys _).mpr
      ⟨hysB, (isWeaklyRegular_map_algebraMap_iff B _ rs).mpr hrsN⟩
  have : IsNoetherian B B := hB
  refine IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal happ List.perm_append_comm ?_
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hys r hr
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => (IsLocalRing.mem_maximalIdeal a).mp (hrs a ha) (isUnit_of_map_unit _ _ hu)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericProjectionFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Matrix

noncomputable section

def entries {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : Fin a × Fin b → ℂ := fun ij => A ij.1 ij.2

def rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  bind₁ (fun ij : Fin d × Fin n => ∑ l, C (F (s ij.1) l) * X (l, ij.2)) p

theorem eval_rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) :
    eval (entries U) (rowsPoly F s p) = eval (entries ((F * U).submatrix s id)) p := by
  change eval₂Hom (RingHom.id ℂ) (entries U) (bind₁ _ p) = eval₂Hom (RingHom.id ℂ) _ p
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  simp [entries, Matrix.mul_apply]

theorem exists_rows_eq {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) (A : Matrix (Fin d) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, (F * U).submatrix s id = A := by
  refine ⟨star F * Matrix.of (Function.extend s (fun i => A i) 0), ?_⟩
  rw [← Matrix.mul_assoc, mem_unitaryGroup_iff.mp hF, Matrix.one_mul]
  ext i j
  simp [hs.extend_apply]

theorem rowsPoly_ne_zero {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) {p : MvPolynomial (Fin d × Fin n) ℂ}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : eval (entries A) p ≠ 0) : rowsPoly F s p ≠ 0 := by
  obtain ⟨U, hU⟩ := exists_rows_eq hF hs A
  intro h
  apply hA
  rw [← hU, ← eval_rowsPoly, h, map_zero]

theorem GenericProjectionFinite.proof (hO : FiniteProjectionsContainOpen.Statement)
    (hU : UnitaryZariskiDense.Statement) :
    GenericProjectionFinite.Statement := by
  classical
  intro n d J hJ hd
  obtain ⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hW⟩ := hO n d J hJ hd
  have good : ∀ A : Matrix (Fin d) (Fin n) ℂ, (∃ p ∈ S, eval (entries A) p ≠ 0) →
      IsFiniteProjection J A := fun A hA => hW (by rw [hS]; exact hA)
  have hA₀' := hA₀
  rw [hS] at hA₀'
  obtain ⟨p, hpS, hp⟩ := hA₀'
  have hdn : d ≤ n := by
    have h := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
    exact_mod_cast h
  refine ⟨⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, fun A hA => hW hA⟩, ⟨A₀, hW hA₀⟩, fun D hD hcl => ?_, fun m F => ?_⟩
  · obtain ⟨U, hUu, hUp⟩ := hU n (rowsPoly 1 (Fin.castLE hdn) p)
      (rowsPoly_ne_zero (one_mem _) (Fin.castLE_injective hdn) hp)
    have hUp' : eval (entries (U.submatrix (Fin.castLE hdn) id)) p ≠ 0 := by
      have := eval_rowsPoly 1 (Fin.castLE hdn) p U
      rw [Matrix.one_mul] at this
      exact this ▸ hUp
    have hAo : U.submatrix (Fin.castLE hdn) id ∈ orthoRows d n := by
      show _ * _ = _
      rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
        ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hUu,
        submatrix_one _ (Fin.castLE_injective hdn)]
    have hopen : IsOpen {B : Matrix (Fin d) (Fin n) ℂ | eval (entries B) p ≠ 0} :=
      isOpen_ne_fun ((MvPolynomial.continuous_eval p).comp
        (continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2)) continuous_const
    obtain ⟨B, hBp, hBD⟩ := mem_closure_iff.mp (hcl hAo) _ hopen hUp'
    exact ⟨B, hBD, good B ⟨p, hpS, hBp⟩⟩
  · have hQ : (∏ ks : Fin m × (Fin d ↪ Fin n), rowsPoly (F ks.1 : Matrix (Fin n) (Fin n) ℂ) ks.2 p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun ks _ => rowsPoly_ne_zero (F ks.1).2 ks.2.injective hp
    obtain ⟨U, hUu, hUQ⟩ := hU n _ hQ
    refine ⟨U, hUu, fun k s => good _ ⟨p, hpS, ?_⟩⟩
    rw [map_prod] at hUQ
    have := Finset.prod_ne_zero_iff.mp hUQ (k, s) (Finset.mem_univ _)
    change eval (entries U) (rowsPoly _ _ p) ≠ 0 at this
    rwa [eval_rowsPoly] at this

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalBoundedQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

theorem monic_eval_div_mul_pow {d : ℕ} (a : Fin d → ℂ) {F G : ℂ} (hG : G ≠ 0) :
    F ^ d + ∑ j : Fin d, a j * F ^ (j : ℕ) * G ^ (d - (j : ℕ)) =
      G ^ d * ((F / G) ^ d + ∑ j : Fin d, a j * (F / G) ^ (j : ℕ)) := by
  rw [mul_add, Finset.mul_sum, div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hG)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (j : ℕ) ≤ d := j.isLt.le
  have hGd : G ^ d = G ^ (j : ℕ) * G ^ (d - (j : ℕ)) := by rw [← pow_add, Nat.add_sub_cancel' hj]
  rw [hGd, div_pow]
  field_simp

theorem NormalBoundedQuotient.proof (hwi : WeaklyHolomorphicIntegral.Statement)
    (hic : NormalGermIntegrallyClosed.Statement) : NormalBoundedQuotient.Statement := by
  intro σ _ I w N F G hI hIc hw hN hwN hF hG hnv hb

  have hhol : HolomorphicOnSubset (fun z => F z / G z) ((zeroSetIn I ∩ N) \ {z | G z = 0}) := by
    intro z hz
    refine ⟨N ∩ G ⁻¹' {0}ᶜ, hG.continuousOn.isOpen_inter_preimage hN isOpen_compl_singleton,
      ⟨hz.1.2, hz.2⟩, fun z => F z / G z, ?_, fun _ _ => rfl⟩
    have hsub : N ∩ G ⁻¹' {0}ᶜ ⊆ N := Set.inter_subset_left
    simp only [div_eq_mul_inv]
    exact (hF.mono hsub).mul ((hG.mono hsub).inv fun y (hy : y ∈ N ∩ G ⁻¹' {0}ᶜ) => hy.2)
  obtain ⟨V, hVo, hwV, hVN, d, a, ha, heq⟩ :=
    hwi σ I w N G (fun z => F z / G z) hI hIc hw hN hwN hG hnv hhol hb
  refine hic σ I w V F G d a hI hIc hw hVo hwV (hF.mono hVN) (hG.mono hVN) ha hnv ?_
  intro z hz
  rw [monic_eval_div_mul_pow (fun j => a j z) (show G z ≠ 0 from hz.2), heq z hz, mul_zero]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

