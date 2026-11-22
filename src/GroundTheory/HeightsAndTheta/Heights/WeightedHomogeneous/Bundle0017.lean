import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIdealIndexPlaces
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace IdealIndexPlaces

theorem genIndex_comap {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G' →+ G)
    {A B : AddSubgroup G} (hA : A ≤ f.range) (hB : B ≤ f.range) :
    genIndex (A.comap f) (B.comap f) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_comap, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self hA,
    AddSubgroup.map_comap_eq_self hB]

theorem absNorm_eq_index {L : Type*} [Field L] [NumberField L] (A : Ideal (𝓞 L)) :
    A.absNorm = A.toAddSubgroup.index := rfl

theorem genIndex_ideal {L : Type*} [Field L] [NumberField L] {A B : Ideal (𝓞 L)} (hA : A ≠ ⊥)
    (hB : B ≠ ⊥) : genIndex A.toAddSubgroup B.toAddSubgroup = (B.absNorm : ℝ) / A.absNorm := by
  have hAB : A ⊓ B ≠ ⊥ := fun h ↦ (mul_ne_zero hA hB) (le_bot_iff.mp (h ▸ Ideal.mul_le_inf))
  have hn : (A ⊓ B).absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hAB
  have hAn : A.absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hA
  have hBn : B.absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hB
  have h1 : B.toAddSubgroup.relIndex A.toAddSubgroup * A.absNorm = (A ⊓ B).absNorm := by
    rw [← AddSubgroup.inf_relIndex_left A.toAddSubgroup B.toAddSubgroup, absNorm_eq_index,
      AddSubgroup.relIndex_mul_index inf_le_left, absNorm_eq_index]
    rfl
  have h2 : A.toAddSubgroup.relIndex B.toAddSubgroup * B.absNorm = (A ⊓ B).absNorm := by
    rw [← AddSubgroup.inf_relIndex_right A.toAddSubgroup B.toAddSubgroup, absNorm_eq_index,
      AddSubgroup.relIndex_mul_index inf_le_right, absNorm_eq_index]
    rfl
  have h1' : (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) = (A ⊓ B).absNorm / A.absNorm := by
    rw [← h1]; push_cast; field_simp
  have h2' : (A.toAddSubgroup.relIndex B.toAddSubgroup : ℝ) = (A ⊓ B).absNorm / B.absNorm := by
    rw [← h2]; push_cast; field_simp
  unfold genIndex
  rw [h1', h2']
  field_simp

end IdealIndexPlaces

open IdealIndexPlaces in

theorem IdealIndexPlaces.proof : IdealIndexPlaces.Statement := by
  intro L _ _ ι _ y hy
  obtain ⟨⟨b, hb⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 L)) y
  choose z hz using hint
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbL : (b : L) ≠ 0 := by rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  have hzy : ∀ i, ((z i : 𝓞 L) : L) = (b : L) * y i := fun i ↦ by
    have h := hz i
    simp only [Algebra.smul_def] at h
    exact h
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy
  replace hi0 : y i0 ≠ 0 := hi0
  set c : 𝓞 L := z i0 with hc
  have hcy : (c : L) = b * y i0 := hzy i0
  have hcL : (c : L) ≠ 0 := by rw [hcy]; exact mul_ne_zero hbL hi0
  have hc0 : c ≠ 0 := fun h ↦ hcL (by rw [h]; rfl)
  set M := multiplierIdeal y with hMdef
  let g : 𝓞 L →ₗ[𝓞 L] L :=
    (LinearMap.mulLeft (𝓞 L) ((c : L)⁻¹)).comp (Algebra.linearMap (𝓞 L) L)
  have hg : ∀ t, g t = (c : L)⁻¹ * t := fun t ↦ rfl
  set I : Ideal (𝓞 L) := M.comap g with hIdef
  set J : Ideal (𝓞 L) := Ideal.span (Set.range z) with hJdef
  have hI : ∀ t : 𝓞 L, t ∈ I ↔ ∀ i, t * z i ∈ Ideal.span {c * b} := by
    intro t
    change (∀ i, (c : L)⁻¹ * t * y i ∈ Set.range (algebraMap (𝓞 L) L)) ↔ _
    refine forall_congr' fun i ↦ ?_
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨e, he⟩
      refine ⟨e, RingOfIntegers.ext ?_⟩
      change (e : L) * ((c : L) * b) = t * z i
      change (e : L) = _ at he
      rw [he, hzy i]
      field_simp
    · rintro ⟨e, he⟩
      refine ⟨e, ?_⟩
      have he' : (e : L) * ((c : L) * b) = t * z i := congrArg (fun s : 𝓞 L ↦ (s : L)) he
      rw [hzy i] at he'
      have h3 : (e : L) * c = t * y i := mul_right_cancel₀ hbL (by linear_combination he')
      change (e : L) = _
      field_simp
      linear_combination h3

  have hIJ : I * J ≤ Ideal.span {c * b} := by
    refine Ideal.mul_le.mpr fun t ht s hs ↦ ?_
    have hle : J ≤ Submodule.comap (LinearMap.mulLeft (𝓞 L) t) (Ideal.span {c * b}) :=
      Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (hI t).mp ht i)
    exact hle hs
  have hcbJ : Ideal.span {c * b} ≤ J :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mul_mem_right b J (Ideal.subset_span ⟨i0, rfl⟩))
  have hcb0 : Ideal.span {c * b} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact mul_ne_zero hc0 hb0
  have hJ0 : J ≠ ⊥ := fun h ↦ hcb0 (le_bot_iff.mp (h ▸ hcbJ))
  obtain ⟨K, hK⟩ := Ideal.dvd_iff_le.mpr hcbJ
  have hKI : K ≤ I := fun t ht ↦ (hI t).mpr fun i ↦ by
    rw [hK, mul_comm t]; exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_range_self i)) ht
  have hIK : I ≤ K := by
    have h : J * K ∣ J * I := Ideal.dvd_iff_le.mpr (by rw [mul_comm J I, ← hK]; exact hIJ)
    exact Ideal.le_of_dvd ((mul_dvd_mul_iff_left hJ0).mp h)
  have hIeq : I = K := le_antisymm hIK hKI
  have hI0 : I ≠ ⊥ := by
    intro h; rw [hIeq] at h; rw [h, Ideal.mul_bot] at hK; exact hcb0 hK
  have hnorm : (I.absNorm : ℝ) * J.absNorm =
      |((Algebra.norm ℤ c : ℤ) : ℝ)| * |((Algebra.norm ℤ b : ℤ) : ℝ)| := by
    have h := congrArg (fun A ↦ (Ideal.absNorm A : ℝ)) hK
    simp only [map_mul, Ideal.absNorm_span_singleton, Int.natAbs_mul, Nat.cast_mul,
      Nat.cast_natAbs] at h
    rw [hIeq]
    push_cast at h
    linear_combination -1 * h

  set C : Ideal (𝓞 L) := (1 : Submodule (𝓞 L) L).comap g with hCdef
  have hC : C = Ideal.span {c} := by
    ext t
    rw [Ideal.mem_span_singleton']
    show g t ∈ (1 : Submodule (𝓞 L) L) ↔ _
    rw [Submodule.mem_one, hg]
    constructor
    · rintro ⟨e, he⟩
      refine ⟨e, RingOfIntegers.ext ?_⟩
      change (e : L) * c = t
      change (e : L) = _ at he
      rw [he]
      field_simp
    · rintro ⟨e, rfl⟩
      refine ⟨e, ?_⟩
      change (e : L) = (c : L)⁻¹ * ((e : L) * c)
      field_simp
  have hrange1 : M.toAddSubgroup ≤ g.toAddMonoidHom.range := by
    intro a ha
    have ha' : a ∈ M := ha
    obtain ⟨e, he⟩ := ha' i0
    refine ⟨b * e, ?_⟩
    change (c : L)⁻¹ * ((b : L) * e) = a
    change (e : L) = _ at he
    rw [he, hcy]
    field_simp
  have hrange2 : (1 : Submodule (𝓞 L) L).toAddSubgroup ≤ g.toAddMonoidHom.range := by
    intro a ha
    obtain ⟨e, rfl⟩ := Submodule.mem_one.mp ha
    refine ⟨c * e, ?_⟩
    change (c : L)⁻¹ * ((c : L) * e) = e
    field_simp
  have hC0 : C ≠ ⊥ := by rw [hC, Ne, Ideal.span_singleton_eq_bot]; exact hc0
  have hgen : genIndex M.toAddSubgroup (1 : Submodule (𝓞 L) L).toAddSubgroup =
      |((Algebra.norm ℤ c : ℤ) : ℝ)| / I.absNorm := by
    rw [← genIndex_comap g.toAddMonoidHom hrange1 hrange2]
    have e1 : M.toAddSubgroup.comap g.toAddMonoidHom = I.toAddSubgroup := rfl
    have e2 : (1 : Submodule (𝓞 L) L).toAddSubgroup.comap g.toAddMonoidHom = C.toAddSubgroup := rfl
    rw [e1, e2, genIndex_ideal hI0 hC0, hC, Ideal.absNorm_span_singleton, Nat.cast_natAbs]
    push_cast
    rfl

  have hz0 : z ≠ 0 := fun h ↦ hc0 (congrFun h i0)
  have hprodz := absNorm_mul_finprod_finitePlace_eq_one hz0
  have hsup : ∀ w : FinitePlace L, ⨆ i, w (z i : L) = w (b : L) * ⨆ i, w (y i) := by
    intro w
    simp_rw [hzy, map_mul]
    exact (Real.mul_iSup_of_nonneg (apply_nonneg w _) _).symm
  simp_rw [hsup] at hprodz
  rw [finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hbL) (hasFiniteMulSupport_iSup_place hy),
    FinitePlace.prod_eq_inv_abs_norm_int hb0] at hprodz
  rw [hgen]
  set P := ∏ᶠ w : FinitePlace L, ⨆ i, w (y i) with hPdef
  have hbn : |((Algebra.norm ℤ b : ℤ) : ℝ)| ≠ 0 := by
    rw [abs_ne_zero, Int.cast_ne_zero, Ne, Algebra.norm_eq_zero_iff]; exact hb0
  have hIn : (I.absNorm : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
  have hJn : (J.absNorm : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ0)
  have hinv := mul_inv_cancel₀ hbn
  have hP : (J.absNorm : ℝ) * P = |((Algebra.norm ℤ b : ℤ) : ℝ)| := by
    linear_combination |((Algebra.norm ℤ b : ℤ) : ℝ)| * hprodz - (J.absNorm : ℝ) * P * hinv
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq hIn]
  apply mul_left_cancel₀ hJn
  linear_combination |((Algebra.norm ℤ c : ℤ) : ℝ)| * hP - hnorm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PLatticeLineExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix
open scoped ComplexOrder ContDiff

noncomputable section

namespace LatticeLine

variable {K : Type} [Field K] [NumberField K] {r N : ℕ}

def recover (R : (K →+* ℂ) → Fin (r + 1) → Fin (N + 1) → ℂ) (σ : K →+* ℂ) (z : Fin (N + 1) → ℂ) :
    Fin (r + 1) → ℂ :=
  fun j ↦ ∑ b, R σ j b * z b

def remainder (φ : Fin (N + 1) → Fin (r + 1) → K) (R : (K →+* ℂ) → Fin (r + 1) → Fin (N + 1) → ℂ)
    (z : Fin (N + 1) → ℂ) : Fin (N + 1) → ℂ :=
  fun b ↦ z b - ∑ σ : K →+* ℂ, ∑ j, σ (φ b j) * recover R σ z j

def quad (F : HermLattice K (r + 1)) (φ : Fin (N + 1) → Fin (r + 1) → K)
    (R : (K →+* ℂ) → Fin (r + 1) → Fin (N + 1) → ℂ) (z : Fin (N + 1) → ℂ) : ℝ :=
  ∑ σ : K →+* ℂ, (star (recover R σ z) ⬝ᵥ (F.metric σ *ᵥ recover R σ z)).re +
    ∑ b, ‖remainder φ R z b‖ ^ 2

variable (F : HermLattice K (r + 1)) (φ : Fin (N + 1) → Fin (r + 1) → K)
  (R : (K →+* ℂ) → Fin (r + 1) → Fin (N + 1) → ℂ)

theorem herm_re_pos (σ : K →+* ℂ) {v : Fin (r + 1) → ℂ} (hv : v ≠ 0) :
    0 < (star v ⬝ᵥ (F.metric σ *ᵥ v)).re :=
  (Complex.pos_iff.mp ((F.posDef σ).dotProduct_mulVec_pos hv)).1

theorem herm_re_nonneg (σ : K →+* ℂ) (v : Fin (r + 1) → ℂ) :
    0 ≤ (star v ⬝ᵥ (F.metric σ *ᵥ v)).re := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (herm_re_pos F σ hv).le

theorem quad_nonneg (z : Fin (N + 1) → ℂ) : 0 ≤ quad F φ R z :=
  add_nonneg (Finset.sum_nonneg fun σ _ ↦ herm_re_nonneg F σ _)
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

theorem quad_pos {z : Fin (N + 1) → ℂ} (hz : z ≠ 0) : 0 < quad F φ R z := by
  by_cases h : ∀ σ, recover R σ z = 0
  · have hrem : remainder φ R z = z := by
      funext b
      simp [remainder, h]
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hz
    refine add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun σ _ ↦ herm_re_nonneg F σ _) ?_
    rw [hrem]
    exact Finset.sum_pos' (fun _ _ ↦ sq_nonneg _)
      ⟨b, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hb) 2⟩
  · obtain ⟨σ, hσ⟩ := not_forall.mp h
    exact add_pos_of_pos_of_nonneg
      (Finset.sum_pos' (fun τ _ ↦ herm_re_nonneg F τ _) ⟨σ, Finset.mem_univ _, herm_re_pos F σ hσ⟩)
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

omit [NumberField K] in
theorem recover_smul (σ : K →+* ℂ) (c : ℂ) (z : Fin (N + 1) → ℂ) :
    recover R σ (fun b ↦ c * z b) = c • recover R σ z := by
  funext j
  simp only [recover, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ ↦ by ring

theorem remainder_smul (c : ℂ) (z : Fin (N + 1) → ℂ) :
    remainder φ R (fun b ↦ c * z b) = c • remainder φ R z := by
  funext b
  simp only [remainder, recover_smul, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

theorem herm_smul (σ : K →+* ℂ) (c : ℂ) (v : Fin (r + 1) → ℂ) :
    (star (c • v) ⬝ᵥ (F.metric σ *ᵥ (c • v))).re = ‖c‖ ^ 2 * (star v ⬝ᵥ (F.metric σ *ᵥ v)).re := by
  rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem quad_smul (c : ℂ) (z : Fin (N + 1) → ℂ) :
    quad F φ R (fun b ↦ c * z b) = ‖c‖ ^ 2 * quad F φ R z := by
  simp only [quad, recover_smul, remainder_smul, herm_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
    mul_add, Finset.mul_sum]

theorem contDiff_quad : ContDiff ℝ ∞ (quad F φ R) := by
  have hrec : ∀ σ j, ContDiff ℝ ∞ (fun z : Fin (N + 1) → ℂ ↦ recover R σ z j) := fun σ j ↦
    ContDiff.sum fun b _ ↦ contDiff_const.mul (contDiff_apply ℝ ℂ b)
  have hconj : ContDiff ℝ ∞ (fun x : ℂ ↦ star x) := Complex.conjCLE.contDiff
  refine ContDiff.add (ContDiff.sum fun σ _ ↦ Complex.reCLM.contDiff.comp ?_)
    (ContDiff.sum fun b _ ↦ (contDiff_norm_sq ℝ).comp ?_)
  · simp only [dotProduct, mulVec, Pi.star_apply]
    exact ContDiff.sum fun i _ ↦ (hconj.comp (hrec σ i)).mul
      (ContDiff.sum fun j _ ↦ contDiff_const.mul (hrec σ j))
  · exact (contDiff_apply ℝ ℂ b).sub
      (ContDiff.sum fun σ _ ↦ ContDiff.sum fun j _ ↦ contDiff_const.mul (hrec σ j))

omit [NumberField K] in
open Classical in
theorem recover_point
    (hR : ∀ (σ : K →+* ℂ) (j₀ : Fin (r + 1)) (τ : K →+* ℂ) (j : Fin (r + 1)),
      ∑ b, R σ j₀ b * τ (φ b j) = if τ = σ ∧ j = j₀ then 1 else 0)
    (s t : K →+* ℂ) (w : Fin (r + 1) → ℂ) :
    recover R t (latticePoint φ s w ()) = if t = s then w else 0 := by
  funext j
  have h1 : ∀ i, ∑ b, R t j b * (s (φ b i) * w i) = (if s = t ∧ i = j then 1 else 0) * w i := by
    intro i
    rw [← hR t j s i, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ ↦ by ring
  simp only [recover, latticePoint, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [h1]
  by_cases hts : t = s
  · subst hts
    simp
  · simp [hts, Ne.symm hts]

open Classical in

theorem quad_point
    (hR : ∀ (σ : K →+* ℂ) (j₀ : Fin (r + 1)) (τ : K →+* ℂ) (j : Fin (r + 1)),
      ∑ b, R σ j₀ b * τ (φ b j) = if τ = σ ∧ j = j₀ then 1 else 0)
    (s : K →+* ℂ) (w : Fin (r + 1) → ℂ) :
    quad F φ R (latticePoint φ s w ()) = (star w ⬝ᵥ (F.metric s *ᵥ w)).re := by
  have hrem : remainder φ R (latticePoint φ s w ()) = 0 := by
    funext b
    simp only [remainder, recover_point φ R hR, Pi.zero_apply]
    rw [Finset.sum_eq_single s (fun σ _ hσ ↦ by simp [hσ]) (fun h ↦ absurd (Finset.mem_univ s) h)]
    simp [latticePoint]
  simp only [quad, hrem, recover_point φ R hR, Pi.zero_apply, norm_zero]
  rw [Finset.sum_eq_single s (fun σ _ hσ ↦ by simp [hσ]) (fun h ↦ absurd (Finset.mem_univ s) h)]
  simp

omit [NumberField K] in

theorem conj_point (s : K →+* ℂ) (w : Fin (r + 1) → ℂ) :
    (fun b ↦ starRingEnd ℂ (latticePoint φ s w () b)) =
      latticePoint φ (ComplexEmbedding.conjugate s) (fun j ↦ starRingEnd ℂ (w j)) () := by
  funext b
  simp [latticePoint, ComplexEmbedding.conjugate_coe_eq, map_sum, map_mul]

theorem herm_conj (s : K →+* ℂ) (w : Fin (r + 1) → ℂ) :
    (star (fun j ↦ starRingEnd ℂ (w j)) ⬝ᵥ
        (F.metric (ComplexEmbedding.conjugate s) *ᵥ fun j ↦ starRingEnd ℂ (w j))).re =
      (star w ⬝ᵥ (F.metric s *ᵥ w)).re := by
  rw [F.conj s]
  have h : star (fun j ↦ starRingEnd ℂ (w j)) ⬝ᵥ ((F.metric s).map (starRingEnd ℂ) *ᵥ
      fun j ↦ starRingEnd ℂ (w j)) = starRingEnd ℂ (star w ⬝ᵥ (F.metric s *ᵥ w)) := by
    simp [dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply]
  rw [h, Complex.conj_re]

def line : HermLine (fun _ : Unit ↦ N) where
  deg _ := 1
  metric z := Real.sqrt ((quad F φ R (z ()) + quad F φ R (fun b ↦ starRingEnd ℂ (z () b))) / 2)
  metric_pos z hz := by
    have h1 := quad_pos F φ R (hz ())
    have h2 := quad_nonneg F φ R (fun b ↦ starRingEnd ℂ (z () b))
    exact Real.sqrt_pos.mpr (by linarith)
  metric_smul c z _ _ := by
    have h2 : quad F φ R (fun b ↦ starRingEnd ℂ (c () * z () b)) =
        ‖c ()‖ ^ 2 * quad F φ R (fun b ↦ starRingEnd ℂ (z () b)) := by
      simp only [map_mul]
      rw [quad_smul, Complex.norm_conj]
    show Real.sqrt ((quad F φ R (fun b ↦ c () * z () b) +
      quad F φ R (fun b ↦ starRingEnd ℂ (c () * z () b))) / 2) = _
    rw [quad_smul, h2, ← mul_add, mul_div_assoc, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (norm_nonneg _)]
    simp
  metric_smooth := by
    have h0 : ContDiff ℝ ∞ (fun z : Cone (fun _ : Unit ↦ N) ℂ ↦ z ()) := contDiff_apply ℝ _ ()
    have h1 : ContDiff ℝ ∞ (fun z : Cone (fun _ : Unit ↦ N) ℂ ↦ fun b ↦ starRingEnd ℂ (z () b)) :=
      contDiff_pi.2 fun b ↦ Complex.conjCLE.contDiff.comp ((contDiff_apply ℝ ℂ b).comp h0)
    have hq := (((contDiff_quad F φ R).comp h0).add ((contDiff_quad F φ R).comp h1)).div_const 2
    refine hq.contDiffOn.sqrt fun z hz ↦ ne_of_gt ?_
    have h3 := quad_pos F φ R (hz ())
    have h4 := quad_nonneg F φ R (fun b ↦ starRingEnd ℂ (z () b))
    simp only [Function.comp_apply]
    linarith

end LatticeLine

theorem LatticeLineExists.proof (h : OneBlockPoints.Statement) : LatticeLineExists.Statement := by
  intro K _ _ r N F φ hφ
  obtain ⟨-, -, hrec⟩ := h K r N F φ hφ
  choose R hR using hrec
  refine ⟨LatticeLine.line F φ R, rfl, ?_, ?_⟩
  · intro s w _
    show Real.sqrt ((LatticeLine.quad F φ R (latticePoint φ s w ()) +
      LatticeLine.quad F φ R (fun b ↦ starRingEnd ℂ (latticePoint φ s w () b))) / 2) = _
    rw [LatticeLine.conj_point, LatticeLine.quad_point F φ R hR, LatticeLine.quad_point F φ R hR,
      LatticeLine.herm_conj]
    congr 1
    ring
  · intro z _
    show Real.sqrt ((LatticeLine.quad F φ R (fun b ↦ starRingEnd ℂ (z () b)) +
      LatticeLine.quad F φ R (fun b ↦ starRingEnd ℂ (starRingEnd ℂ (z () b)))) / 2) =
      Real.sqrt ((LatticeLine.quad F φ R (z ()) +
        LatticeLine.quad F φ R (fun b ↦ starRingEnd ℂ (z () b))) / 2)
    simp only [Complex.conj_conj]
    rw [add_comm]

end

end GroundTheory.Heights₂.Heights
end

