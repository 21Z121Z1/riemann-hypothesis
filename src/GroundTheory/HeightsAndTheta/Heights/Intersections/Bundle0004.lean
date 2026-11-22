import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFIntZeroMixed
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Matrix Module ReciprocityTheory.ChartRestriction.G.Geo

variable {D : ℕ}

theorem sum_neg_one_pow_superset_eq_zero (p : Finset (Fin D) → Prop) [DecidablePred p] (a : Fin D)
    (hp : ∀ T, p (insert a T) ↔ p T) (X : ℂ) :
    ∑ T : Finset (Fin D), (-1 : ℂ) ^ (D - T.card) * (if p T then X else 0) = 0 := by
  rw [← Finset.powerset_univ, ← Finset.insert_erase (Finset.mem_univ a),
    Finset.sum_powerset_insert (Finset.notMem_erase a _), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun T hT => ?_
  have haT : a ∉ T := fun h => Finset.notMem_erase a _ (Finset.mem_powerset.mp hT h)
  have hlt : T.card < D := by
    have := Finset.card_le_card (Finset.mem_powerset.mp hT)
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin] at this
    have : 0 < D := Fin.pos a
    omega
  rw [Finset.card_insert_of_notMem haT]
  have hD : D - T.card = (D - (T.card + 1)) + 1 := by omega
  by_cases h : p T
  · rw [if_pos h, if_pos ((hp T).mpr h), hD, pow_succ]
    ring
  · rw [if_neg h, if_neg fun h' => h ((hp T).mp h')]
    ring

theorem mixedDisc_eq_zero_of_cols (B : Fin D → Matrix (Fin D) (Fin D) ℂ) (S C : Finset (Fin D))
    (hcard : D < C.card + S.card) (hB : ∀ k ∈ S, ∀ j ∈ C, ∀ i, B k i j = 0) : mixedDisc B = 0 := by
  classical
  unfold mixedDisc
  refine mul_eq_zero_of_right _ ?_
  have hdet : ∀ T : Finset (Fin D), (∑ k ∈ T, B k).det = ∑ σ : Equiv.Perm (Fin D), ∑ f : Fin D → Fin D,
      (if ∀ i, f i ∈ T then (Equiv.Perm.sign σ : ℂ) * ∏ i, B (f i) (σ i) i else 0) := by
    intro T
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.sum_apply]
    rw [Finset.prod_univ_sum, Units.smul_def, zsmul_eq_mul, Finset.mul_sum]
    have hpi : Fintype.piFinset (fun _ : Fin D => T) = Finset.univ.filter (fun f : Fin D → Fin D => ∀ i, f i ∈ T) := by
      ext f; simp [Fintype.mem_piFinset]
    rw [hpi, Finset.sum_filter]
  simp_rw [hdet, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun f _ => ?_
  by_cases hf : Function.Surjective f
  · have hbij : Function.Bijective f := ⟨Finite.injective_iff_surjective.mpr hf, hf⟩
    have hpre : (S.preimage f hbij.1.injOn).card = S.card := by
      rw [Finset.card_preimage]
      congr 1
      exact Finset.filter_true_of_mem fun x _ => hf x
    obtain ⟨i, hi⟩ := Finset.inter_nonempty_of_card_lt_card_add_card (Finset.subset_univ C)
      (Finset.subset_univ (S.preimage f hbij.1.injOn)) (by rw [hpre, Finset.card_univ, Fintype.card_fin]; exact hcard)
    rw [Finset.mem_inter, Finset.mem_preimage] at hi
    have h0 : ∏ i, B (f i) (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (hB _ hi.2 _ hi.1 _)
    refine Finset.sum_eq_zero fun T _ => ?_
    simp [h0]
  · obtain ⟨a, ha⟩ := not_forall.mp hf
    push Not at ha
    have := sum_neg_one_pow_superset_eq_zero (fun T => ∀ i, f i ∈ T) a
      (fun T => ⟨fun h i => (Finset.mem_insert.mp (h i)).resolve_left (ha i), fun h i => Finset.mem_insert_of_mem (h i)⟩)
      ((Equiv.Perm.sign σ : ℂ) * ∏ i, B (f i) (σ i) i)
    exact this

theorem mixedDisc_mul_right (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (P : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => A k * P) = mixedDisc A * P.det := by
  unfold mixedDisc
  simp_rw [← Finset.sum_mul, Matrix.det_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun T _ => by ring

theorem mixedDisc_map_star (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => (A k).map (starRingEnd ℂ)) = starRingEnd ℂ (mixedDisc A) := by
  unfold mixedDisc
  rw [map_mul, map_sum]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun T _ => ?_
    rw [map_mul, map_pow, map_neg, map_one, RingHom.map_det]
    congr 2
    ext i j
    simp [Matrix.sum_apply]

theorem mixedDisc_eq_zero_of_ker (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (V : Submodule ℂ (Fin D → ℂ))
    (S : Finset (Fin D)) (hdim : D < Module.finrank ℂ V + S.card) (hA : ∀ k ∈ S, ∀ x ∈ V, A k *ᵥ x = 0) :
    mixedDisc A = 0 := by
  classical
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl V
  set b0 := ((Module.finBasis ℂ V).prod (Module.finBasis ℂ U)).map (Submodule.prodEquivOfIsCompl V U hU) with hb0
  have hcardι : Fintype.card (Fin (Module.finrank ℂ V) ⊕ Fin (Module.finrank ℂ U)) = D := by
    rw [← Module.finrank_eq_card_basis b0, Module.finrank_fin_fun]
  set e := Fintype.equivFinOfCardEq hcardι
  set b := b0.reindex e
  have hbV : ∀ i, b (e (Sum.inl i)) ∈ V := by
    intro i
    simp [b, hb0, Basis.reindex_apply, Basis.map_apply, Basis.prod_apply]
  set P : Matrix (Fin D) (Fin D) ℂ := (Pi.basisFun ℂ (Fin D)).toMatrix b
  have hP : IsUnit P.det := by
    rw [← Basis.det_apply]
    exact (Pi.basisFun ℂ (Fin D)).isUnit_det b
  set C := Finset.univ.image fun i => e (Sum.inl i)
  have hC : C.card = Module.finrank ℂ V := by
    rw [Finset.card_image_of_injective (f := fun i => e (Sum.inl i)) _
      (fun x y h => Sum.inl_injective (e.injective h)), Finset.card_univ, Fintype.card_fin]
  have hcol : ∀ k ∈ S, ∀ j ∈ C, ∀ i, (A k * P) i j = 0 := by
    intro k hk j hj i
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hj
    have h := congrFun (hA k hk _ (hbV l)) i
    simpa [P, Matrix.mul_apply, Matrix.mulVec, dotProduct, Basis.toMatrix_apply] using h
  have h := mixedDisc_eq_zero_of_cols (fun k => A k * P) S C (by rw [hC]; exact hdim) hcol
  rw [mixedDisc_mul_right] at h
  exact (mul_eq_zero.mp h).resolve_right hP.ne_zero

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLinearQuotient
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial

theorem LinearQuotient.proof : LinearQuotient.Statement := by
  intro F _ σ _ S hS
  classical

  let ℓ : (σ → F) →ₗ[F] MvPolynomial σ F := Fintype.linearCombination F (fun s => (X s : MvPolynomial σ F))
  have hSrange : ∀ f ∈ S, f ∈ LinearMap.range ℓ := by
    intro f hf
    rw [Fintype.range_linearCombination, ← homogeneousSubmodule_one_eq_span_X]
    exact hS f hf
  let L : Submodule F (σ → F) := (Submodule.span F S).comap ℓ
  let b := Module.finBasis F ((σ → F) ⧸ L)
  let r := Module.finrank F ((σ → F) ⧸ L)
  let θ : (σ → F) →ₗ[F] MvPolynomial (Fin r) F :=
    Fintype.linearCombination F (fun i => (X i : MvPolynomial (Fin r) F)) ∘ₗ
      (b.equivFun.toLinearMap ∘ₗ L.mkQ)
  have hθ : ∀ v, θ v = ∑ i, b.equivFun (L.mkQ v) i • (X i : MvPolynomial (Fin r) F) := fun v => rfl
  let φ : MvPolynomial σ F →ₐ[F] MvPolynomial (Fin r) F := aeval (fun s => θ (Pi.single s 1))

  have key : ∀ c, φ (ℓ c) = θ c := by
    have : φ.toLinearMap ∘ₗ ℓ = θ := by
      refine LinearMap.pi_ext (fun s x => ?_)
      have hx : (Pi.single s x : σ → F) = x • Pi.single s (1 : F) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, ℓ,
        Fintype.linearCombination_apply_single, map_smul, φ, aeval_X]
      rw [hx, map_smul]
    exact fun c => LinearMap.congr_fun this c

  let lift : Fin r → (σ → F) := fun i => (L.mkQ_surjective (b i)).choose
  have hlift : ∀ i, L.mkQ (lift i) = b i := fun i => (L.mkQ_surjective (b i)).choose_spec
  let ψ : MvPolynomial (Fin r) F →ₐ[F] MvPolynomial σ F := aeval (fun i => ℓ (lift i))
  have hφψ : φ.comp ψ = AlgHom.id F _ := by
    refine MvPolynomial.algHom_ext (fun i => ?_)
    have he : b.equivFun (b i) = Pi.single i 1 := by
      funext j
      rw [Module.Basis.equivFun_self, Pi.single_apply]
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    simp only [AlgHom.comp_apply, ψ, aeval_X, key, AlgHom.id_apply]
    rw [show θ (lift i) = Fintype.linearCombination F (fun i => (X i : MvPolynomial (Fin r) F))
      (b.equivFun (L.mkQ (lift i))) from rfl, hlift, he, Fintype.linearCombination_apply_single, one_smul]
  have hψθ : ∀ v, ψ (θ v) = ℓ (∑ i, b.equivFun (L.mkQ v) i • lift i) := by
    intro v
    rw [hθ, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, map_smul, aeval_X]
  have hspan : Submodule.span F S ≤ (Ideal.span S).restrictScalars F :=
    Submodule.span_le.mpr (fun f hf => Ideal.subset_span hf)
  refine ⟨r, φ, fun p => ⟨ψ p, by simpa using AlgHom.congr_fun hφψ p⟩, ?_, fun s => ?_⟩
  · apply le_antisymm
    · have hmk : (Ideal.Quotient.mkₐ F (Ideal.span S)).comp (ψ.comp φ) = Ideal.Quotient.mkₐ F (Ideal.span S) := by
        refine MvPolynomial.algHom_ext (fun s => ?_)
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [Ideal.Quotient.eq]
        have h1 : φ (X s) = θ (Pi.single s 1) := aeval_X _ _
        rw [h1, hψθ]
        have hmem : (∑ i, b.equivFun (L.mkQ (Pi.single s 1)) i • lift i) - Pi.single s 1 ∈ L := by
          rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
          have : (Submodule.Quotient.mk (∑ i, b.equivFun (L.mkQ (Pi.single s 1)) i • lift i) : (σ → F) ⧸ L) =
              ∑ i, b.equivFun (L.mkQ (Pi.single s 1)) i • b i := by
            rw [← Submodule.mkQ_apply, map_sum]
            simp only [map_smul, hlift]
          rw [this, b.sum_equivFun, Submodule.mkQ_apply, sub_self]
        have h2 := hspan hmem
        rw [map_sub] at h2
        have h3 : ℓ (Pi.single s 1) = X s := by
          simp [ℓ]
        rwa [h3] at h2
      intro f hf
      rw [RingHom.mem_ker] at hf
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have := AlgHom.congr_fun hmk f
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
      rw [← this, hf, map_zero, map_zero]
    · refine Ideal.span_le.mpr (fun f hf => ?_)
      obtain ⟨c, rfl⟩ := hSrange f hf
      have hc : c ∈ L := Submodule.subset_span hf
      show φ (ℓ c) = 0
      rw [key, hθ, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero L).mpr hc]
      simp
  · rw [← mem_homogeneousSubmodule, homogeneousSubmodule_one_eq_span_X, ← Fintype.range_linearCombination]
    refine ⟨b.equivFun (L.mkQ (Pi.single s 1)), ?_⟩
    rw [show φ (X s) = θ (Pi.single s 1) from aeval_X _ _]
    rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PRankAdjoinFrac
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Module IntermediateField IntermediateField.algebraAdjoinAdjoin

namespace RankAdjoinFrac

theorem finrank_algebraAdjoin_eq_finrank_adjoin {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (T : Set Ω) :
    finrank K (Algebra.adjoin K T) = finrank K (IntermediateField.adjoin K T) := by
  by_cases hT : ∀ x ∈ T, IsAlgebraic K x
  · rw [← IntermediateField.finrank_eq_finrank_subalgebra, adjoin_toSubalgebra_of_isAlgebraic hT]
  · push Not at hT
    obtain ⟨x, hx, hnx⟩ := hT
    have h1 : finrank K (Algebra.adjoin K T) = 0 := by
      by_contra h0
      have := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h0)
      exact hnx ((Algebra.IsAlgebraic.isAlgebraic
        (⟨x, Algebra.subset_adjoin hx⟩ : Algebra.adjoin K T)).algHom (Algebra.adjoin K T).val)
    have h2 : finrank K (IntermediateField.adjoin K T) = 0 := by
      by_contra h0
      have := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h0)
      exact hnx ((Algebra.IsAlgebraic.isAlgebraic
        (⟨x, subset_adjoin K T hx⟩ : IntermediateField.adjoin K T)).algHom (IntermediateField.adjoin K T).val)
    rw [h1, h2]

theorem exists_mul_mem_of_mem {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω} (h : S ⊆ T) {y : Ω}
    (hy : y ∈ Algebra.adjoin (IntermediateField.adjoin F S) T) :
    ∃ a ∈ Algebra.adjoin F S, a ≠ 0 ∧ a * y ∈ Algebra.adjoin F T := by
  have hST := Algebra.adjoin_mono (R := F) h
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_mem _, one_ne_zero, by rw [one_mul]; exact Algebra.subset_adjoin hx⟩
  | algebraMap k =>
    obtain ⟨r, hr, s, hs, hk⟩ := mem_adjoin_iff_div.mp k.2
    by_cases hs0 : s = 0
    · refine ⟨1, one_mem _, one_ne_zero, ?_⟩
      have : (algebraMap (IntermediateField.adjoin F S) Ω k) = 0 := by
        change (k : Ω) = 0
        rw [hk, hs0, div_zero]
      rw [this, mul_zero]
      exact zero_mem _
    · refine ⟨s, hs, hs0, ?_⟩
      change s * (k : Ω) ∈ _
      rw [hk, mul_div_cancel₀ _ hs0]
      exact hST hr
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha0, hax⟩ := hx
    obtain ⟨b, hb, hb0, hby⟩ := hy
    refine ⟨a * b, mul_mem ha hb, mul_ne_zero ha0 hb0, ?_⟩
    have : a * b * (x + y) = b * (a * x) + a * (b * y) := by ring
    rw [this]
    exact add_mem (mul_mem (hST hb) hax) (mul_mem (hST ha) hby)
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, ha0, hax⟩ := hx
    obtain ⟨b, hb, hb0, hby⟩ := hy
    refine ⟨a * b, mul_mem ha hb, mul_ne_zero ha0 hb0, ?_⟩
    have : a * b * (x * y) = (a * x) * (b * y) := by ring
    rw [this]
    exact mul_mem hax hby

theorem finrank_eq_finrank_algebraAdjoin {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω}
    (h : S ⊆ T) :
    letI := adjoinInclAlgebra F h
    finrank (Algebra.adjoin F S) (Algebra.adjoin F T) =
      finrank (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) := by
  let _ := adjoinInclAlgebra F h
  let _ : Algebra (Algebra.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) :=
    ((algebraMap (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T)).comp
      (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S))).toAlgebra
  have : IsScalarTower (Algebra.adjoin F S) (IntermediateField.adjoin F S)
      (Algebra.adjoin (IntermediateField.adjoin F S) T) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hle : Algebra.adjoin F T ≤ (Algebra.adjoin (IntermediateField.adjoin F S) T).restrictScalars F :=
    Algebra.adjoin_le (Algebra.subset_adjoin (R := IntermediateField.adjoin F S))
  let f : Algebra.adjoin F T →ₗ[Algebra.adjoin F S] Algebra.adjoin (IntermediateField.adjoin F S) T :=
    { toFun := fun m => ⟨m.1, hle m.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        apply Subtype.ext
        simp only [Algebra.smul_def, RingHom.id_apply, Subalgebra.coe_mul, RingHom.algebraMap_toAlgebra,
          RingHom.comp_apply, Subalgebra.coe_algebraMap, IntermediateField.algebraMap_apply,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_inclusion] }
  have : IsLocalizedModule (nonZeroDivisors (Algebra.adjoin F S)) f := by
    refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} hx => ?_⟩
    · rw [Module.End.isUnit_iff]
      have hx0 : algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (Algebra.adjoin F S) (IntermediateField.adjoin F S))).mpr
          (nonZeroDivisors.coe_ne_zero x)
      refine ⟨fun u v huv => ?_, fun v => ?_⟩
      · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
          ← algebraMap_smul (IntermediateField.adjoin F S) (x : Algebra.adjoin F S) u,
          ← algebraMap_smul (IntermediateField.adjoin F S) (x : Algebra.adjoin F S) v] at huv
        calc u = (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x)⁻¹ •
              (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x • u) := by
                rw [smul_smul, inv_mul_cancel₀ hx0, one_smul]
          _ = v := by rw [huv, smul_smul, inv_mul_cancel₀ hx0, one_smul]
      · refine ⟨(algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x)⁻¹ • v, ?_⟩
        rw [Module.algebraMap_end_apply, ← algebraMap_smul (IntermediateField.adjoin F S), smul_smul,
          mul_inv_cancel₀ hx0, one_smul]
    · obtain ⟨a, ha, ha0, hay⟩ := exists_mul_mem_of_mem h y.2
      refine ⟨(⟨a * y, hay⟩, ⟨⟨a, ha⟩, mem_nonZeroDivisors_of_ne_zero ?_⟩), ?_⟩
      · exact fun h0 => ha0 (congrArg Subtype.val h0)
      · apply Subtype.ext
        simp only [Submonoid.smul_def, Algebra.smul_def, Subalgebra.coe_mul, RingHom.algebraMap_toAlgebra,
          RingHom.comp_apply, Subalgebra.coe_algebraMap, IntermediateField.algebraMap_apply]
        rfl
    · refine ⟨1, ?_⟩
      rw [one_smul, one_smul]
      exact Subtype.ext (congrArg (fun z : Algebra.adjoin (IntermediateField.adjoin F S) T => (z : Ω)) hx)
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (Algebra.adjoin F S)) f le_rfl,
    IsLocalization.finrank_eq (IntermediateField.adjoin F S) (nonZeroDivisors (Algebra.adjoin F S)) le_rfl]

theorem proof : RankAdjoinFrac.Statement := by
  intro F Ω _ _ _ S T h
  have hKL : IntermediateField.adjoin F S ≤ IntermediateField.adjoin F T := adjoin.mono F S T h
  have hE : extendScalars hKL = IntermediateField.adjoin (IntermediateField.adjoin F S) T :=
    restrictScalars_injective F (by
      rw [extendScalars_restrictScalars, adjoin_adjoin_left, Set.union_eq_self_of_subset_left h])
  have key : IntermediateField.relfinrank (IntermediateField.adjoin F S) (IntermediateField.adjoin F T) =
      finrank (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) := by
    rw [relfinrank_eq_finrank_of_le hKL, hE, finrank_algebraAdjoin_eq_finrank_adjoin]
  exact (finrank_eq_finrank_algebraAdjoin h).trans key.symm

end RankAdjoinFrac

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PRankFracDegree
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

theorem RankFracDegree.isFractionRing_of_closure {F Ω A : Type} [Field F] [Field Ω] [Algebra F Ω] [CommRing A]
    (K : IntermediateField F Ω) (f : A →+* Ω) (hf : Function.Injective f) (hK : ∀ a, f a ∈ K)
    (hcl : K.toSubfield ≤ Subfield.closure (Set.range f)) :
    let _ := (f.codRestrict K hK).toAlgebra
    IsFractionRing A K := by
  intro _
  have hmap : ∀ a, ((algebraMap A K a : K) : Ω) = f a := fun _ => rfl
  have hnz : ∀ a : A, a ∈ nonZeroDivisors A → f a ≠ 0 := by
    intro a ha h0
    have h10 : (1 : A) = 0 :=
      mem_nonZeroDivisors_iff_right.mp ha 1 (by rw [one_mul]; exact hf (by rw [h0, map_zero]))
    exact one_ne_zero (by simpa using congrArg f h10 : (1 : Ω) = 0)
  show IsLocalization (nonZeroDivisors A) K
  rw [isLocalization_iff]
  refine ⟨fun y => IsUnit.mk0 _ fun h => hnz y y.2 (by rw [← hmap, h]; rfl), fun z => ?_, fun {x y} h => ?_⟩
  · obtain ⟨y, hy, w, hw, hyw⟩ := Subfield.mem_closure_iff.mp (hcl z.2)
    rw [← RingHom.coe_range, Subring.closure_eq] at hy hw
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨a', rfl⟩ := hw
    by_cases h0 : f a' = 0
    · refine ⟨(0, 1), Subtype.ext ?_⟩
      simp only [OneMemClass.coe_one, map_zero, map_one, mul_one, ZeroMemClass.coe_zero]
      rw [← hyw, h0, div_zero]
    · have ha' : a' ∈ nonZeroDivisors A :=
        mem_nonZeroDivisors_of_injective hf (mem_nonZeroDivisors_of_ne_zero h0)
      refine ⟨(a, ⟨a', ha'⟩), Subtype.ext ?_⟩
      simp only [MulMemClass.coe_mul, hmap]
      rw [← hyw, div_mul_cancel₀ _ h0]
  · refine ⟨1, ?_⟩
    have hxy : x = y := hf (by rw [← hmap x, ← hmap y, h])
    rw [hxy]

theorem RankFracDegree.proof : RankFracDegree.Statement := by
  intro F Ω A B _ _ _ _ _ _ L₀ L f g hf hg hfg hfL₀ hgL hL₀ hL _
  have hle : L₀ ≤ L := by
    intro x hx
    have h1 : x ∈ Subfield.closure (Set.range g) := by
      refine Subfield.closure_mono ?_ (hL₀ hx)
      rintro _ ⟨a, rfl⟩
      exact ⟨algebraMap A B a, hfg a⟩
    exact (Subfield.closure_le (t := L.toSubfield)).mpr (by rintro _ ⟨b, rfl⟩; exact hgL b) h1
  let L' := IntermediateField.extendScalars hle
  let _ : Algebra A L₀ := (f.codRestrict L₀ hfL₀).toAlgebra
  let _ : Algebra B L' := (g.codRestrict L' hgL).toAlgebra
  let _ : Algebra A L' := ((algebraMap L₀ L').comp (algebraMap A L₀)).toAlgebra
  have _ : IsScalarTower A L₀ L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower A B L' := IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (hfg a).symm
  have _ : IsFractionRing A L₀ := RankFracDegree.isFractionRing_of_closure L₀ f hf hfL₀ hL₀
  have _ : IsFractionRing B L' := RankFracDegree.isFractionRing_of_closure L' g hg hgL hL
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  exact (IsFractionRing.finrank_eq A L₀ B L').symm

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PRelAlgClosureFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial IntermediateField.algebraAdjoinAdjoin

theorem RelAlgClosureFinite.linearIndependent_adjoin {K L : Type*} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) {σ : Type*} {x : σ → L} (hx : AlgebraicIndependent M x)
    {ι : Type*} {m : ι → M} (hm : LinearIndependent K m) :
    LinearIndependent (Algebra.adjoin K (Set.range x)) (fun i => (m i : L)) := by
  rw [linearIndependent_iff'] at hm ⊢
  intro s g hg i hi
  have hp : ∀ j, ∃ p : MvPolynomial σ K, aeval x p = (g j : L) := fun j => by
    have h : (g j : L) ∈ (aeval x : MvPolynomial σ K →ₐ[K] L).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact (g j).2
    exact (AlgHom.mem_range _).1 h
  choose p hp using hp
  have hP : (∑ j ∈ s, C (m j) * map (algebraMap K M) (p j) : MvPolynomial σ M) = 0 := by
    apply hx.eq_zero_of_aeval_eq_zero
    rw [← hg]
    simp only [map_sum, map_mul, aeval_C, aeval_map_algebraMap, hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul, mul_comm]
    rfl
  have hcoeff : ∀ d, ∀ j ∈ s, coeff d (p j) = 0 := fun d => by
    apply hm s (fun j => coeff d (p j))
    have := congrArg (coeff d) hP
    simp only [coeff_sum, coeff_C_mul, coeff_map, coeff_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have hpi : p i = 0 := MvPolynomial.ext _ _ fun d => by rw [hcoeff d i hi, coeff_zero]
  apply Subtype.ext
  rw [← hp i, hpi, map_zero]
  rfl

theorem RelAlgClosureFinite.proof : RelAlgClosureFinite.Statement := by
  intro K L _ _ _ S hS
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K L
  set M := algebraicClosure K L
  have hM : AlgebraicIndependent M ((↑) : t → L) := ht.1.algebraicClosure
  set E := IntermediateField.adjoin K (Set.range ((↑) : t → L))
  have halg : Algebra.IsAlgebraic E L := ht.isAlgebraic_field
  have htop : IntermediateField.adjoin E (S : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ IntermediateField.adjoin K (S : Set L) := hS ▸ IntermediateField.mem_top
    have hle : IntermediateField.adjoin K (S : Set L) ≤
        (IntermediateField.adjoin E (S : Set L)).restrictScalars K :=
      IntermediateField.adjoin_le_iff.2 fun y hy => IntermediateField.subset_adjoin E _ hy
    exact hle hz
  have hfin : FiniteDimensional E L := by
    have h := IntermediateField.finiteDimensional_adjoin (K := E) (S := (S : Set L))
      fun y _ => (halg.isAlgebraic y).isIntegral
    rw [htop] at h
    exact (IntermediateField.topEquiv (F := E) (E := L)).toLinearEquiv.finiteDimensional
  let b := Module.Basis.ofVectorSpace K M
  have hli : LinearIndependent E (fun i => ((b i : M) : L)) :=
    (LinearIndependent.iff_fractionRing (Algebra.adjoin K (Set.range ((↑) : t → L))) E).1
      (RelAlgClosureFinite.linearIndependent_adjoin M hM b.linearIndependent)
  have : Finite (Module.Basis.ofVectorSpaceIndex K M) := hli.finite
  exact Module.Finite.of_basis b

end GroundTheory.Heights₂.Heights.Inter
end
end

