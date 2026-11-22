import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.LatticeBundleObjects
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ExistsSmulMemOfSpanEqTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights

noncomputable section

theorem genIndex_eq_div_of_le {M : Type*} [AddCommGroup M] {A B C : AddSubgroup M} (hCA : C ≤ A)
    (hCB : C ≤ B) (hC : C.relIndex B ≠ 0) :
    genIndex A B = (C.relIndex A : ℝ) / (C.relIndex B : ℝ) := by
  have h1 : C.relIndex (A ⊓ B) * B.relIndex A = C.relIndex A := by
    rw [← AddSubgroup.inf_relIndex_left A B]
    exact AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hCA hCB) inf_le_left
  have h2 : C.relIndex (A ⊓ B) * A.relIndex B = C.relIndex B := by
    rw [← AddSubgroup.inf_relIndex_right A B]
    exact AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hCA hCB) inf_le_right
  have h3 : (C.relIndex (A ⊓ B) : ℝ) ≠ 0 := by
    intro h
    apply hC
    rw [← h2, Nat.cast_eq_zero.mp h, zero_mul]
  unfold genIndex
  rw [← h1, ← h2]
  push_cast
  rw [mul_div_mul_left _ _ h3]

theorem exists_smul_mem_of_span_eq_top {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (Λ : Submodule (𝓞 K) (Fin n → K)) (hΛ : Submodule.span K (Λ : Set (Fin n → K)) = ⊤)
    (v : Fin n → K) : ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Λ :=
  _root_.GroundTheory.Variant₂.N1.exists_smul_mem_of_span_eq_top_alt Λ hΛ v

theorem gramAt_smul {K : Type*} [Field K] {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ)
    {ι : Type*} (u : ι → Fin n → K) (c : K) :
    gramAt h σ (fun a => c • u a) = ((‖σ c‖ ^ 2 : ℝ) : ℂ) • gramAt h σ u := by
  have he : ∀ v : Fin n → K, embVec σ (c • v) = σ c • embVec σ v := fun v => by
    funext k
    simp [embVec]
  ext a b
  simp only [gramAt, he, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, Complex.star_def, Complex.mul_conj']
  push_cast
  ring

theorem S6.CoordinateDegree.proof : S6.CoordinateDegree.Statement := by
  intro K _ _ E n H ψ hψ hspan hmet G ι _ _ u hu hG
  have hu' : LinearIndependent (𝓞 K) u := (LinearIndependent.iff_fractionRing (𝓞 K) K).mpr hu
  obtain ⟨t, ht0, htu⟩ : ∃ t : 𝓞 K, t ≠ 0 ∧ ∀ j, t • u j ∈ LinearMap.range ψ := by
    choose a ha hau using fun j => exists_smul_mem_of_span_eq_top (LinearMap.range ψ) hspan (u j)
    refine ⟨∏ j, a j, Finset.prod_ne_zero_iff.mpr fun j _ => ha j, fun j => ?_⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ j)
    rw [hc, mul_comm, mul_smul]
    exact (LinearMap.range ψ).smul_mem c (hau j)
  have htW : ∀ j, t • u j ∈ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K) := fun j =>
    (Submodule.span K (Set.range u)).smul_of_tower_mem t (Submodule.subset_span ⟨j, rfl⟩)
  have hmemG : ∀ j, t • u j ∈ G.map ψ := by
    intro j
    rw [hG]
    exact ⟨htu j, htW j⟩
  choose f0 hf0G hf0 using fun j => Submodule.mem_map.mp (hmemG j)
  let f : ι → G := fun j => ⟨f0 j, hf0G j⟩
  have htK : algebraMap (𝓞 K) K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ht0
  have htu_li : LinearIndependent (𝓞 K) (fun j => t • u j) := by
    refine (LinearIndependent.iff_fractionRing (𝓞 K) K).mpr ?_
    have h := hu.units_smul (fun _ : ι => Units.mk0 _ htK)
    have he : (fun j => t • u j) = (fun _ : ι => Units.mk0 _ htK) • u := by
      funext j
      simp only [Pi.smul_apply', Units.smul_def, Units.val_mk0, algebraMap_smul]
    rw [he]
    exact h
  have hf_li : LinearIndependent (𝓞 K) f := by
    refine LinearIndependent.of_comp (ψ ∘ₗ G.subtype) ?_
    have : (ψ ∘ₗ G.subtype) ∘ f = fun j => t • u j := funext hf0
    rw [this]
    exact htu_li

  have hcard : Fintype.card ι = Module.finrank (𝓞 K) G := by
    refine le_antisymm hf_li.fintype_card_le_finrank ?_
    obtain ⟨g, hg⟩ := HermitianBundle.exists_linearIndependent_rank E G
    have hgW : ∀ i, ψ (g i) ∈ Submodule.span K (Set.range u) := by
      intro i
      have hi : ψ (g i) ∈ G.map ψ := Submodule.mem_map_of_mem (g i).2
      rw [hG] at hi
      exact hi.2
    let v : Fin (HermitianBundle.rank E G) → Submodule.span K (Set.range u) :=
      fun i => ⟨ψ (g i), hgW i⟩
    have hv : LinearIndependent K v := by
      refine LinearIndependent.of_comp (Submodule.span K (Set.range u)).subtype ?_
      refine (LinearIndependent.iff_fractionRing (𝓞 K) K).mp ?_
      exact hg.map' (ψ ∘ₗ G.subtype) (LinearMap.ker_eq_bot.mpr (hψ.comp G.injective_subtype))
    have := hv.fintype_card_le_finrank
    rw [Fintype.card_fin, finrank_span_eq_card hu] at this
    exact this

  have hCA' : Submodule.span (𝓞 K) (Set.range fun j => t • u j) ≤
      LinearMap.range ψ ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K) :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => ⟨htu j, htW j⟩)
  have hCB' : Submodule.span (𝓞 K) (Set.range fun j => t • u j) ≤
      Submodule.span (𝓞 K) (Set.range u) :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j =>
      Submodule.smul_mem _ t (Submodule.subset_span ⟨j, rfl⟩))
  have hCA : (Submodule.span (𝓞 K) (Set.range fun j => t • u j)).toAddSubgroup ≤
      (LinearMap.range ψ ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K)).toAddSubgroup :=
    fun _ hx => hCA' hx
  have hCB : (Submodule.span (𝓞 K) (Set.range fun j => t • u j)).toAddSubgroup ≤
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup :=
    fun _ hx => hCB' hx
  have h1 : (Submodule.span (𝓞 K) (Set.range fun j => t • u j)).toAddSubgroup.relIndex
      (LinearMap.range ψ ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K)).toAddSubgroup =
      Nat.card (G ⧸ Submodule.span (𝓞 K) (Set.range f)) := by
    have hS : (Submodule.span (𝓞 K) (Set.range fun j => (f j : E.carrier))).map ψ =
        Submodule.span (𝓞 K) (Set.range fun j => t • u j) := by
      rw [Submodule.map_span, ← Set.range_comp]
      exact congrArg _ (congrArg Set.range (funext hf0))
    rw [← hG, ← hS, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
      AddSubgroup.relIndex_map_map_of_injective _ _ hψ]
    have hsp : Submodule.span (𝓞 K) (Set.range f) =
        (Submodule.span (𝓞 K) (Set.range fun j => (f j : E.carrier))).comap G.subtype := by
      rw [← Submodule.comap_map_eq_of_injective G.injective_subtype
        (Submodule.span (𝓞 K) (Set.range f)), Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hsp]
    rfl
  have h2 : (Submodule.span (𝓞 K) (Set.range fun j => t • u j)).toAddSubgroup.relIndex
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup =
      (Algebra.norm ℤ t).natAbs ^ Fintype.card ι := by
    have hΦ : Function.Injective (Fintype.linearCombination (𝓞 K) u) :=
      hu'.fintypeLinearCombination_injective
    let Dm : Matrix ι ι (𝓞 K) := Matrix.diagonal fun _ => t
    have hDet : Dm.det = t ^ Fintype.card ι := by
      simp [Dm, Matrix.det_diagonal]
    have hcomp : Fintype.linearCombination (𝓞 K) u ∘ₗ Dm.mulVecLin =
        Fintype.linearCombination (𝓞 K) (fun j => t • u j) := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Fintype.linearCombination_apply, Dm,
        Matrix.mulVec_diagonal]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, mul_smul, smul_comm]
    rw [← Fintype.range_linearCombination, ← Fintype.range_linearCombination, ← hcomp,
      LinearMap.range_comp, LinearMap.range_eq_map (Fintype.linearCombination (𝓞 K) u),
      Submodule.map_toAddSubgroup,
      Submodule.map_toAddSubgroup, AddSubgroup.relIndex_map_map_of_injective _ _ hΦ,
      Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right]
    change Nat.card ((ι → 𝓞 K) ⧸ LinearMap.range Dm.mulVecLin) = _
    rw [card_quotient_mulVecLin Dm (by rw [hDet]; exact pow_ne_zero _ ht0), hDet, map_pow,
      Int.natAbs_pow]
  have hM0 : (Algebra.norm ℤ t).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ht0)
  have hidx : genIndex
      (LinearMap.range ψ ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K)).toAddSubgroup
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup =
      (Nat.card (G ⧸ Submodule.span (𝓞 K) (Set.range f)) : ℝ) /
        ((Algebra.norm ℤ t).natAbs : ℝ) ^ Fintype.card ι := by
    rw [genIndex_eq_div_of_le hCA hCB (by rw [h2]; exact pow_ne_zero _ hM0), h1, h2]
    push_cast
    rfl

  have hgram : ∀ σ : K →+* ℂ,
      GroundTheory.Heights₂.Heights.gramDet (E.metric.comap G.subtype G.injective_subtype) σ f =
        (‖σ (algebraMap (𝓞 K) K t)‖ ^ 2) ^ Fintype.card ι * (gramAt (H σ) σ u).det.re := by
    intro σ
    have hM : (gram ℂ fun i => fibreVec (E.metric.comap G.subtype G.injective_subtype) σ (f i)) =
        ((‖σ (algebraMap (𝓞 K) K t)‖ ^ 2 : ℝ) : ℂ) • gramAt (H σ) σ u := by
      rw [← gramAt_smul]
      ext i j
      change (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (f i : E.carrier))
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (f j : E.carrier)) = _
      rw [hmet]
      simp only [gramAt, f, hf0, algebraMap_smul]
    simp only [GroundTheory.Heights₂.Heights.gramDet]
    rw [hM, Matrix.det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have hpos : ∀ σ : K →+* ℂ, 0 < ‖σ (algebraMap (𝓞 K) K t)‖ := fun σ =>
    norm_pos_iff.mpr ((map_ne_zero σ).mpr htK)
  have hD : ∀ σ : K →+* ℂ, 0 < (gramAt (H σ) σ u).det.re := by
    intro σ
    have h := gramDet_pos (E.metric.comap G.subtype G.injective_subtype) σ hf_li
    rw [hgram σ] at h
    exact pos_of_mul_pos_right h (by positivity)
  have hN : (0 : ℝ) < Nat.card (G ⧸ Submodule.span (𝓞 K) (Set.range f)) := by
    have := finite_quotient_span hf_li hcard
    exact_mod_cast Nat.card_pos
  have hMpos : (0 : ℝ) < ((Algebra.norm ℤ t).natAbs : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM0
  have hsum : ∑ σ : K →+* ℂ, Real.log ((‖σ (algebraMap (𝓞 K) K t)‖ ^ 2) ^ Fintype.card ι *
      (gramAt (H σ) σ u).det.re) = 2 * Fintype.card ι * Real.log ((Algebra.norm ℤ t).natAbs : ℝ) +
      ∑ σ : K →+* ℂ, Real.log (gramAt (H σ) σ u).det.re := by
    rw [← sum_log_norm_embedding t ht0, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Real.log_mul (pow_pos (pow_pos (hpos σ) 2) _).ne' (hD σ).ne', Real.log_pow, Real.log_pow,
      show algebraMap (𝓞 K) K t = (t : K) from rfl]
    push_cast
    ring

  rw [HermitianBundle.degree_eq_arithDegree, arithDegree_eq _ hf_li hcard, GroundTheory.Heights₂.Heights.degreeWith,
    subDegree, hidx]
  simp only [hgram]
  rw [hsum, Real.log_div hN.ne' (pow_pos hMpos _).ne', Real.log_pow]
  ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField
open scoped nonZeroDivisors

theorem S6.SaturatedSpan.proof : S6.SaturatedSpan.Statement := by
  intro K _ _ M _ _ _ n ψ hψ G hsat
  obtain ⟨S, hS, hli⟩ := exists_set_linearIndependent_of_isDomain (𝓞 K) G
  rw [← Module.finrank_eq_rank] at hS
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hS
  let f : Fin (Module.finrank (𝓞 K) G) → G := fun i ↦ (e.symm i : G)
  have hf : LinearIndependent (𝓞 K) f := hli.comp _ e.symm.injective
  let φ : G →ₗ[𝓞 K] (Fin n → K) := ψ ∘ₗ G.subtype
  have hφ : Function.Injective φ := hψ.comp Subtype.val_injective
  let b : Fin (Module.finrank (𝓞 K) G) → Fin n → K := φ ∘ f
  have hbO : LinearIndependent (𝓞 K) b := hf.map' φ (LinearMap.ker_eq_bot.mpr hφ)
  have hb : LinearIndependent K b := (LinearIndependent.iff_fractionRing (𝓞 K) K).mp hbO
  refine ⟨b, hb, ?_⟩
  have hspanO : ∀ c : Fin (Module.finrank (𝓞 K) G) → 𝓞 K,
      φ (∑ j, c j • f j) ∈ Submodule.span K (Set.range b) := by
    intro c
    rw [map_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [map_smul, ← algebraMap_smul K (c j)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self ψ x, ?_⟩
    have hnot : ¬ LinearIndependent (𝓞 K)
        (Fin.cons ⟨x, hx⟩ f : Fin (Module.finrank (𝓞 K) G + 1) → G) := by
      intro h
      have := h.fintype_card_le_finrank
      simp at this
    obtain ⟨s, hs0, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
    rw [Fin.sum_univ_succ] at hs0
    simp only [Fin.cons_zero, Fin.cons_succ] at hs0
    have ht : s 0 ≠ 0 := by
      intro h0
      rw [h0, zero_smul, zero_add] at hs0
      have hz := Fintype.linearIndependent_iff.mp hf (fun j ↦ s j.succ) hs0
      refine hi ?_
      cases i using Fin.cases with
      | zero => exact h0
      | succ j => exact hz j
    have key : s 0 • (⟨x, hx⟩ : G) = ∑ j, (-s j.succ) • f j := by
      simp only [neg_smul, Finset.sum_neg_distrib]
      exact eq_neg_of_add_eq_zero_left hs0
    have hmem := hspanO (fun j ↦ -s j.succ)
    rw [← key, map_smul] at hmem
    have hK : algebraMap (𝓞 K) K (s 0) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ht
    rw [← algebraMap_smul K (s 0)] at hmem
    have h2 := Submodule.smul_mem _ (algebraMap (𝓞 K) K (s 0))⁻¹ hmem
    rw [smul_smul, inv_mul_cancel₀ hK, one_smul] at h2
    exact h2
  · rintro y hy
    obtain ⟨⟨x, rfl⟩, hy⟩ := Submodule.mem_inf.mp hy
    have hy' : ψ x ∈ Submodule.span K (Set.range b) := hy
    obtain ⟨κ, hκ⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy'
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples (𝓞 K)⁰ Finset.univ κ
    choose a ha using fun j ↦ ht j (Finset.mem_univ j)
    have htx : (t : 𝓞 K) • x ∈ G := by
      have heq : ψ ((t : 𝓞 K) • x) = ψ (∑ j, a j • (f j : M)) := by
        rw [map_smul, ← hκ, map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [map_smul, ← algebraMap_smul K (a j), ha j, smul_assoc]
        rfl
      rw [hψ heq]
      exact Submodule.sum_mem _ fun j _ ↦ G.smul_mem _ (f j).2
    exact ⟨x, hsat _ x (nonZeroDivisors.coe_ne_zero t) htx, rfl⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

noncomputable section

def S6.QuotDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (d : (K →+* ℂ) → Fin n → ℝ), (∀ x, a x ≠ 0) → (∀ σ x, 0 < d σ x) →
    ∀ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)
      (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n),
      Submodule.span K (quotLattice a b c hli hmk : Set (Fin k → K)) = ⊤ ∧
        subDegree (quotLattice a b c hli hmk) (schurMetric d b c)
            (fun j : Fin k => (Pi.single j 1 : Fin k → K)) =
          quotDegree (idealLattice a) (diagMetric d) b c

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors ComplexOrder

noncomputable section

def S6.MatrixSubDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (M : Submodule (𝓞 K) (Fin N → K))
    [Module.Finite (𝓞 K) M] (H : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hH : ∀ σ, (H σ).PosDef)
    (hconj : ∀ σ, H (conjugate σ) = (H σ).map (starRingEnd ℂ)),
    Submodule.span K (M : Set (Fin N → K)) = ⊤ →
    ∀ (r : ℕ) (u : Fin r → Fin N → K), LinearIndependent K u →
      (matrixBundle M H hH hconj).rank (satSub M u) = r ∧
        (matrixBundle M H hH hconj).degree (satSub M u) = subDegree M H u

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

noncomputable section

def S6.QuotExtension.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (d : (K →+* ℂ) → Fin n → ℝ) (hd : ∀ σ x, 0 < d σ x) (hc : ∀ σ x, d (conjugate σ) x = d σ x),
    (∀ x, a x ≠ 0) →
    ∀ (m k : ℕ) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)
      (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n),
      ∃ X : HermitianExtension (subBundle a d hd hc b) (latticeBundle a d hd hc)
          (quotBundle a d hd hc b c hli hmk),
        X.incl = (subLattice a b).subtype ∧ X.proj = quotProj a b c hli hmk

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualGeomDegPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
open scoped ComplexOrder

noncomputable section

namespace DualGeometricDegreePositive

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

def stdLattice (F : HermLattice K i) : HermLattice K i where
  lattice := F.lattice
  fg := F.fg
  span_eq := F.span_eq
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

def oneLine : HermLine (dualBlocks T) :=
  HermLine.ofWeight (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)

omit [Fintype T] [DecidableEq T] in
theorem logNorm_oneLine : logNorm (oneLine (T := T)) 1 = fun _ => (1 : ℝ) := by
  funext z
  simp [logNorm, oneLine, HermLine.ofWeight]

omit [Fintype T] [DecidableEq T] in
theorem segre_apply (z : (Σ _ : Unit, T) → ℂ) (s : (k : Unit) → dualBlocks T k) :
    segre (ι := dualBlocks T) z s = z ⟨(), s ()⟩ := by
  simp [segre]

theorem isGoodProj (hOn : DualPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    IsGoodProj (dualIdeal b) (dualProj b hb) := by
  intro z hz h0
  obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
  have hne : dualRecover b hb (fun t => z ⟨(), t⟩) ≠ 0 := by
    intro h
    obtain ⟨t, ht⟩ := hz.1 ()
    exact ht (congrFun ((dualRecover b hb).map_eq_zero_iff.mp h) t)
  obtain ⟨⟨τ, j⟩, hτ⟩ := Function.ne_iff.mp hne
  have hτσ : τ = σ := by
    by_contra h
    exact hτ (hσ τ h j)
  subst hτσ
  have h1 := congrFun h0 j
  rw [dualProj_apply] at h1
  simp only [segre_apply] at h1
  rw [Finset.sum_eq_single τ (fun τ' _ h => hσ τ' h j) (fun h => absurd (Finset.mem_univ τ) h)] at h1
  exact hτ h1

end DualGeometricDegreePositive

open DualGeometricDegreePositive in

theorem DualGeomDegPos.proof (hDeg : DegreeStatement) (hInd : PtsIndepStatement)
    (hArith : DualArithVar.Statement) (hSemi : DualLineSemipositive.Statement)
    (hOn : DualPtsOnPlane.Statement) (hMass : DualStdMassAt.Statement) :
    DualGeomDegPos.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨D, rfl⟩ : ∃ D, i = D + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hV : IsArithVar (dualIdeal b) (D + 1) := hArith K (D + 1) F T b hi
  have hS1 : IsSmoothHerm (dualLine (stdLattice F) b hb) := (hSemi K (D + 1) (stdLattice F) T b hb).1
  have e0 := hDeg Unit (dualBlocks T) (dualIdeal b) D (fun _ => dualLine F b hb) 2 hV
    (fun _ => (hSemi K (D + 1) F T b hb).1) Nat.prime_two
  have e1 := hDeg Unit (dualBlocks T) (dualIdeal b) D (fun _ => dualLine (stdLattice F) b hb) 2 hV
    (fun _ => hS1) Nat.prime_two
  have hswap : geomDeg (dualIdeal b) (dualLine F b hb) D =
      geomDeg (dualIdeal b) (dualLine (stdLattice F) b hb) D := by
    change ptsIntegral (dualIdeal b) (pot fun _ => dualLine F b hb) (fun _ => 1) =
      ptsIntegral (dualIdeal b) (pot fun _ => dualLine (stdLattice F) b hb) (fun _ => 1)
    rw [e0, e1]
    rfl
  have hgood := isGoodProj hOn b hb
  have hΨ : ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (dualIdeal b) Ψ := ⟨_, hgood⟩
  have hsec : IsSectionOn (dualIdeal b) (oneLine (T := T)) 1 := by
    refine ⟨fun _ => 0, fun _ => rfl, ?_, ?_⟩
    · intro d hd k
      rw [support_one] at hd
      simp only [Finset.mem_singleton] at hd
      simp [hd]
    · exact (Ideal.ne_top_iff_one _).1 hV.2.1.1.ne_top
  have h := hInd Unit (dualBlocks T) (dualIdeal b) D hΨ.choose (dualProj b hb)
    (fun _ => dualLine (stdLattice F) b hb) oneLine 1 hV hΨ.choose_spec hgood (fun _ => hS1)
    contDiffOn_const hsec
  rw [logNorm_oneLine] at h
  have hm := hMass K D (stdLattice F) T b hb fun _ => rfl
  have hval : geomDeg (dualIdeal b) (dualLine (stdLattice F) b hb) D = Fintype.card (K →+* ℂ) := by
    unfold geomDeg ptsIntegral
    rw [dif_pos hΨ]
    exact h.trans hm
  rw [hswap, hval]
  exact_mod_cast Fintype.card_pos

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualEnergy
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

def DualMetricEnergy.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    ∑ k ∈ Finset.range i,
        ptsIntegral (dualIdeal b)
          (pot fun j : Fin (i - 1) =>
            if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
          (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
      1 / 2 * (∑ σ : K →+* ℂ, Real.log (F.metric σ).det.re) *
        geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

example : Σ' (b : Module.Basis Unit ℤ (dualLattice HermLattice.scaledExample)),
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)) ∧ 1 ≤ 1 ∧
      HermLattice.scaledExample.metric ≠ HermLattice.scaledExample.withStdMetric.metric :=
  ⟨dualBasisStandard, dualEmbMatrix_standard_bijective, le_rfl, fun h => by
    have h1 := congrFun (congrFun (congrFun h (Rat.castHom ℂ)) 0) 0
    simp [HermLattice.scaledExample, HermLattice.withStdMetric] at h1⟩

end

end GroundTheory.Heights₂.Heights
end

