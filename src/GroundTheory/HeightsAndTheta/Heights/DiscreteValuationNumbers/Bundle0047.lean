import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureBirational
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Lemmas

variable {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω]
  {O : Type*} [CommRing O] [Algebra O Ω] {Φ : Type*} [Field Φ] [Algebra Ω Φ] [Algebra O Φ]
  [IsScalarTower O Ω Φ]

theorem segreVec_algebraMap (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    segreVec (fun p => algebraMap Ω Φ (y p)) c = algebraMap Ω Φ (segreVec y c) := by
  simp [segreVec, map_prod]

theorem algebraMap_mem_chartRing_segre (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {z : Ω}
    (hz : z ∈ chartRing O (segreVec y) c) :
    algebraMap Ω Φ z ∈ chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c := by
  have hle : chartRing O (segreVec y) c ≤
      (chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c).comap
        (IsScalarTower.toAlgHom O Ω Φ) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_comap]
    show algebraMap Ω Φ (segreVec y j / segreVec y c) ∈
      chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c
    rw [map_div₀, ← segreVec_algebraMap, ← segreVec_algebraMap]
    exact div_mem_chartRing _ _ _
  exact hle hz

end Lemmas

theorem eq_repr_smul_basis_first {Ω : Type*} [Field Ω] {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (w : Module.Basis (Fin N) Ω E) (h0 : 0 < N) (v : E)
    (hv : ∀ j : Fin N, (⟨0, h0⟩ : Fin N) < j → w.repr v j = 0) :
    v = w.repr v ⟨0, h0⟩ • w ⟨0, h0⟩ := by
  conv_lhs => rw [← w.sum_repr v]
  refine Finset.sum_eq_single _ (fun j _ hj => ?_) (by simp)
  have hlt : (⟨0, h0⟩ : Fin N) < j := by
    rw [Fin.lt_def]
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    show 0 < (j : ℕ)
    omega
  rw [hv j hlt, zero_smul]

theorem SegreFlagClosureBirational.proof : SegreFlagClosureBirational.Statement := by
  intro O _ _ _ ϖ _ Ω _ _ K _ _ ι _ y d _ N E _ _ B B' _ w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t _ hN c hc c₁ c₂ hc₂
  set i0 : Fin N := ⟨0, hN⟩ with hi0
  have hcΩ : segreVec y c ≠ 0 := by
    intro h
    apply hc
    rw [segreVec_algebraMap, h, map_zero]
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hcΩ k (Finset.mem_univ k)
  have hpow : ∀ b : K → ℤ, ∏ k, y ⟨k, c k⟩ ^ b k ≠ 0 :=
    fun b => Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)

  have hmem : ∏ k, y ⟨k, c k⟩ ^ x i0 k ∈ degLat O y (x i0) c := ⟨1, one_mem _, (one_mul _).symm⟩
  rw [← hF.flag.graded c hcΩ i0] at hmem
  obtain ⟨v, hv, hvj, hv0⟩ := hmem
  have hmem' : ∏ k, y ⟨k, c k⟩ ^ x' i0 k ∈ degLat O y (x' i0) c := ⟨1, one_mem _, (one_mul _).symm⟩
  rw [← hF.flag'.graded c hcΩ i0] at hmem'
  obtain ⟨v', hv', hvj', hv0'⟩ := hmem'
  have hv_eq : v = (∏ k, y ⟨k, c k⟩ ^ x i0 k) • w i0 := by
    rw [← hv0]; exact eq_repr_smul_basis_first w hN v hvj
  have hv'_eq : v' = (∏ k, y ⟨k, c k⟩ ^ x' i0 k) • w' i0 := by
    rw [← hv0']; exact eq_repr_smul_basis_first w' hN v' hvj'
  have hw' : w' i0 = w.repr (w' i0) i0 • w i0 :=
    eq_repr_smul_basis_first w hN (w' i0) fun j hj => hF.sameFlag i0 j hj
  set u : Ω := w.repr (w' i0) i0 with hudef
  have hu : u ≠ 0 := by
    intro h
    apply w'.ne_zero i0
    rw [hw', h, zero_smul]

  choose α hα hαeq using fun l => hφ.sections c hcΩ l v hv
  choose β hβ hβeq using fun l => hφ'.sections c hcΩ l v' hv'
  set D : Ω := (∏ k, y ⟨k, c k⟩ ^ x i0 k) * ((∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u) with hDdef
  set G : Ω := (∏ k, y ⟨k, c k⟩ ^ a₀ k) * ∏ k, y ⟨k, c k⟩ ^ a₀' k with hGdef
  have hD : D ≠ 0 := mul_ne_zero (hpow _) (mul_ne_zero (hpow _) hu)
  have hprod : ∀ (l : Fin M) (m : Fin M'), D * (φ l (w i0) * φ' m (w i0)) = G * (α l * β m) := by
    intro l m
    have hA : (∏ k, y ⟨k, c k⟩ ^ x i0 k) * φ l (w i0) = α l * ∏ k, y ⟨k, c k⟩ ^ a₀ k := by
      rw [← hαeq l, hv_eq, map_smul, smul_eq_mul]
    have hB : (∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u * φ' m (w i0) =
        β m * ∏ k, y ⟨k, c k⟩ ^ a₀' k := by
      rw [← hβeq m, hv'_eq, hw', smul_smul, map_smul, smul_eq_mul]
    rw [hDdef, hGdef]
    linear_combination ((∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u * φ' m (w i0)) * hA +
      (α l * ∏ k, y ⟨k, c k⟩ ^ a₀ k) * hB
  have hprodΦ : ∀ (l : Fin M) (m : Fin M'),
      algebraMap Ω Φ D * (algebraMap Ω Φ (φ l (w i0)) * algebraMap Ω Φ (φ' m (w i0))) =
        algebraMap Ω Φ G * (algebraMap Ω Φ (α l) * algebraMap Ω Φ (β m)) := by
    intro l m
    have := congrArg (algebraMap Ω Φ) (hprod l m)
    simpa only [map_mul] using this

  set T : Φ := ∑ i, t i * algebraMap Ω Φ (w.repr (e i) i0) with hT
  have hfc : ∀ j : Fin N, j ≠ i0 → flagCoord w e t 1 j = 0 := by
    intro j hj
    have : ¬ ((j : ℕ) < 1) := by
      intro h
      apply hj
      ext
      simp only [hi0]
      omega
    simp [flagCoord, this]
  have hfc0 : flagCoord w e t 1 i0 = T := by simp [flagCoord, hi0, hT]
  have hsome : ∀ l : Fin M, flagLinePt w e φ φ' t 1 ⟨some (), l⟩ = T * algebraMap Ω Φ (φ l (w i0)) := by
    intro l
    show ∑ i, flagCoord w e t 1 i * algebraMap Ω Φ (φ l (w i)) = _
    rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [hfc j hj, zero_mul]) (by simp), hfc0]
  have hnone : ∀ l : Fin M', flagLinePt w e φ φ' t 1 ⟨none, l⟩ = T * algebraMap Ω Φ (φ' l (w i0)) := by
    intro l
    show ∑ i, flagCoord w e t 1 i * algebraMap Ω Φ (φ' l (w i)) = _
    rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [hfc j hj, zero_mul]) (by simp), hfc0]
  have hseg : ∀ c' : ∀ o, lineBlocks M M' o, segreVec (flagLinePt w e φ φ' t 1) c' =
      (T * algebraMap Ω Φ (φ' (c' none) (w i0))) * (T * algebraMap Ω Φ (φ (c' (some ())) (w i0))) := by
    intro c'
    rw [segreVec, Fintype.prod_option, Fintype.prod_unique]
    exact congrArg₂ (· * ·) (hnone (c' none)) (hsome (c' (some ())))

  refine ⟨algebraMap Ω Φ (α (c₁ (some ()))) * algebraMap Ω Φ (β (c₁ none)),
    mul_mem (algebraMap_mem_chartRing_segre y c (hα _)) (algebraMap_mem_chartRing_segre y c (hβ _)),
    algebraMap Ω Φ (α (c₂ (some ()))) * algebraMap Ω Φ (β (c₂ none)),
    mul_mem (algebraMap_mem_chartRing_segre y c (hα _)) (algebraMap_mem_chartRing_segre y c (hβ _)), ?_, ?_⟩
  · intro h0
    apply hc₂
    have hDΦ : algebraMap Ω Φ D ≠ 0 := (map_ne_zero _).2 hD
    apply (mul_right_injective₀ hDΦ)
    simp only [mul_zero]
    rw [hseg]
    have h2 := hprodΦ (c₂ (some ())) (c₂ none)
    linear_combination T ^ 2 * h2 + T ^ 2 * algebraMap Ω Φ G * h0
  · have hDΦ : algebraMap Ω Φ D ≠ 0 := (map_ne_zero _).2 hD
    apply (mul_right_injective₀ hDΦ)
    simp only
    rw [hseg, hseg]
    have h1 := hprodΦ (c₁ (some ())) (c₁ none)
    have h2 := hprodΦ (c₂ (some ())) (c₂ none)
    linear_combination T ^ 2 * (algebraMap Ω Φ (α (c₂ (some ()))) * algebraMap Ω Φ (β (c₂ none))) * h1 -
      T ^ 2 * (algebraMap Ω Φ (α (c₁ (some ()))) * algebraMap Ω Φ (β (c₁ none))) * h2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Blocks

variable (K : Type*)

def closureBlockEquiv : Option (Option K) ≃ K ⊕ Option Unit where
  toFun
    | none => Sum.inr none
    | some none => Sum.inr (some ())
    | some (some k) => Sum.inl k
  invFun
    | Sum.inl k => some (some k)
    | Sum.inr none => none
    | Sum.inr (some _) => some none
  left_inv := by rintro (_ | (_ | k)) <;> rfl
  right_inv := by rintro (k | (_ | ⟨⟩)) <;> rfl

variable {K} (ι : K → Type) (M M' : ℕ)

def closureVarEquiv :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) ≃ (Σ s, Sum.elim ι (lineBlocks M M') s) where
  toFun
    | ⟨none, l⟩ => ⟨Sum.inr none, l⟩
    | ⟨some none, l⟩ => ⟨Sum.inr (some ()), l⟩
    | ⟨some (some k), i⟩ => ⟨Sum.inl k, i⟩
  invFun
    | ⟨Sum.inl k, i⟩ => ⟨some (some k), i⟩
    | ⟨Sum.inr none, l⟩ => ⟨none, l⟩
    | ⟨Sum.inr (some _), l⟩ => ⟨some none, l⟩
  left_inv := by rintro ⟨_ | (_ | k), l⟩ <;> rfl
  right_inv := by rintro ⟨k | (_ | ⟨⟩), l⟩ <;> rfl

theorem closureVarEquiv_fst (v : Σ o, bundleIdx (bundleIdx ι M) M' o) :
    (closureVarEquiv ι M M' v).1 = closureBlockEquiv K v.1 := by
  rcases v with ⟨_ | (_ | k), l⟩ <;> rfl

theorem joinDeg_comp_closureBlockEquiv (L : K → ℤ) :
    joinDeg (K' := Option Unit) L ∘ closureBlockEquiv K = liftPairDeg L := by
  funext o
  rcases o with _ | (_ | k) <;> rfl

theorem rename_liftPairForm {R : Type*} [CommRing R] (F : MRing ι R) :
    rename (closureVarEquiv ι M M') (liftPairForm M M' F) = joinForm (ι' := lineBlocks M M') F := by
  rw [liftPairForm, rename_rename]
  rfl

end Blocks

section Data

variable {K : Type} {ι : K → Type} {m : ℕ}

def joinClosureDeg (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) : Fin (1 + m) → K ⊕ Option Unit → ℤ :=
  Fin.append (fun _ : Fin 1 => ζ ∘ (closureBlockEquiv K).symm) (fun j => joinDeg (L j))

def joinClosureForm {R : Type*} [CommRing R] (M M' : ℕ) (h : MRing (Sum.elim ι (lineBlocks M M')) R)
    (F : Fin m → MRing ι R) : Fin (1 + m) → MRing (Sum.elim ι (lineBlocks M M')) R :=
  Fin.append (fun _ : Fin 1 => h) (fun j => joinForm (F j))

theorem joinClosureDeg_comp (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) :
    (fun i => joinClosureDeg ζ L i ∘ closureBlockEquiv K) = closureDeg ζ L := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [joinClosureDeg, closureDeg, Fin.append_left]
    funext o
    simp
  · simp only [joinClosureDeg, closureDeg, Fin.append_right]
    exact joinDeg_comp_closureBlockEquiv _

theorem joinClosureDeg_natAdd (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) :
    joinClosureDeg ζ L ∘ Fin.natAdd 1 = fun j => joinDeg (L j) := by
  funext j
  simp [joinClosureDeg, Fin.append_right]

theorem rename_closureForm {R : Type*} [CommRing R] (M M' : ℕ) (h : MRing (bundleIdx (bundleIdx ι M) M') R)
    (F : Fin m → MRing ι R) :
    (fun i => rename (closureVarEquiv ι M M') (closureForm M M' h F i)) =
      joinClosureForm M M' (rename (closureVarEquiv ι M M') h) F := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [joinClosureForm, closureForm, Fin.append_left]
  · simp only [joinClosureForm, closureForm, Fin.append_right]
    exact rename_liftPairForm ι M M' _

theorem joinClosureForm_natAdd {R : Type*} [CommRing R] (M M' : ℕ) (h : MRing (Sum.elim ι (lineBlocks M M')) R)
    (F : Fin m → MRing ι R) : joinClosureForm M M' h F ∘ Fin.natAdd 1 = fun j => joinForm (F j) := by
  funext j
  simp [joinClosureForm, Fin.append_right]

end Data

section PointIdeal

theorem pointIdeal_map_rename {K₁ K₂ : Type*} {ι₁ : K₁ → Type*} {ι₂ : K₂ → Type*} {R Φ : Type*} [CommRing R]
    [Field Φ] [Algebra R Φ] (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1)
    (y : (Σ k, ι₂ k) → Φ) : (pointIdeal R (y ∘ σ)).map (rename σ) = pointIdeal R y := by
  have key : ∀ f, pointConeMap R y (rename σ f) = rename e (pointConeMap R (y ∘ σ) f) := by
    intro f
    have h : (pointConeMap R y).toRingHom.comp (rename σ).toRingHom =
        (rename e).toRingHom.comp (pointConeMap R (y ∘ σ)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [pointConeMap, MvPolynomial.algebraMap_eq]
      · intro v
        simp [pointConeMap, hσ]
    have := RingHom.congr_fun h f
    simpa using this
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap]
    simp only [pointIdeal, RingHom.mem_ker] at hf ⊢
    rw [key, hf, map_zero]
  · intro f hf
    have hf' : rename σ (rename σ.symm f) = f := by
      rw [rename_rename]
      simp
    rw [← hf']
    apply Ideal.mem_map_of_mem
    simp only [pointIdeal, RingHom.mem_ker] at hf ⊢
    apply rename_injective _ e.injective
    rw [map_zero, ← key, hf', hf]

theorem pointIdeal_algebraMap {K : Type*} {ι : K → Type*} {O Ω Φ : Type*} [CommRing O] [Field Ω] [Field Φ]
    [Algebra O Ω] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ] (y : (Σ k, ι k) → Ω) :
    pointIdeal O (fun p => algebraMap Ω Φ (y p)) = pointIdeal O y := by
  have key : ∀ f, pointConeMap O (fun p => algebraMap Ω Φ (y p)) f =
      MvPolynomial.map (algebraMap Ω Φ) (pointConeMap O y f) := by
    intro f
    have h : (pointConeMap O (fun p => algebraMap Ω Φ (y p))).toRingHom =
        (MvPolynomial.map (algebraMap Ω Φ)).comp (pointConeMap O y).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [pointConeMap, IsScalarTower.algebraMap_apply O Ω Φ]
      · intro v
        simp [pointConeMap]
    have := RingHom.congr_fun h f
    simpa using this
  ext f
  simp only [pointIdeal, RingHom.mem_ker, key]
  exact ⟨fun h => map_injective _ (algebraMap Ω Φ).injective (by rw [h, map_zero]),
    fun h => by rw [h, map_zero]⟩

end PointIdeal

theorem SegreFlagClosurePullback.proof (hPull : PairNumberPullback.Statement)
    (hExp : PairNumberExpansionIndependence.Statement) (hMod : SegreFlagClosureModel.Statement)
    (hRel : PairNumberRelabel.Statement) (hVJ : VerticalDivisorJoinPullback.Statement)
    (hBir : SegreFlagClosureBirational.Statement) : SegreFlagClosurePullback.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ'
    hφ hφ' Φ _ _ _ _ e t ht k hk1 hkN f₁ g₁ hD₁ _ n z z' fz gz hz r Bf hBf As Bs hAs hBs Q hQ
  classical
  letI : ∀ s, Fintype (Sum.elim ι (lineBlocks M M') s) := fun s =>
    match s with
    | Sum.inl k => inferInstanceAs (Fintype (ι k))
    | Sum.inr o => inferInstanceAs (Fintype (lineBlocks M M' o))

  have hpt : joinCoords (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t k) ∘ closureVarEquiv ι M M' =
      flagClosurePt y w e φ φ' t k := by
    funext p
    rcases p with ⟨_ | (_ | o), l⟩ <;> rfl
  have hPJ : (pointIdeal O (flagClosurePt y w e φ φ' t k)).map (rename (closureVarEquiv ι M M')) =
      pointIdeal O (joinCoords (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t k)) := by
    rw [← hpt]
    exact pointIdeal_map_rename (closureBlockEquiv K) _ (closureVarEquiv_fst ι M M') _
  have hPV : pointIdeal O (fun p => algebraMap Ω Φ (y p)) = pointIdeal O y := pointIdeal_algebraMap y
  obtain ⟨hRmod, hRvert, hRnum⟩ := hRel O ϖ (Option (Option K)) (bundleIdx (bundleIdx ι M) M')
    (K ⊕ Option Unit) (Sum.elim ι (lineBlocks M M')) (closureBlockEquiv K) (closureVarEquiv ι M M')
    (closureVarEquiv_fst ι M M') (pointIdeal O (flagClosurePt y w e φ φ' t k))
  rw [hPJ] at hRmod hRvert hRnum
  have hJmod : IsModelOver (pointIdeal O (joinCoords (fun p => algebraMap Ω Φ (y p))
      (flagLinePt w e φ φ' t k))) (d + (k - 1)) :=
    hRmod _ (hMod O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k
      hk1 hkN).1

  have hvert : ∀ i, IsVerticalDivisor (pointIdeal O (fun p => algebraMap Ω Φ (y p))) ϖ
      (Fin.append x z i - Fin.append x' z' i) (Fin.append f fz i) (Fin.append g gz i) := by
    rw [hPV]
    exact fun i => Fin.addCases (fun i => by simpa only [Fin.append_left] using hF.vertical i)
      (fun j => by simpa only [Fin.append_right] using hz j) i

  have hT := hRnum (1 + (N + n)) (joinClosureDeg (zetaFirst a₀) (Fin.append x z))
    (joinClosureDeg (zetaSecond a₀') (Fin.append x' z')) (closureForm M M' f₁ (Fin.append f fz))
    (closureForm M M' g₁ (Fin.append g gz)) As (Q.map joinDeg)
  have hQ' : (Q.map joinDeg).map (· ∘ closureBlockEquiv K) = Q.map liftPairDeg := by
    rw [List.map_map]
    exact List.map_congr_left fun L _ => joinDeg_comp_closureBlockEquiv L
  rw [rename_closureForm, rename_closureForm, joinClosureDeg_comp, joinClosureDeg_comp, hQ'] at hT
  rw [← hT]

  have hvJ : ∀ i, IsVerticalDivisor (pointIdeal O (joinCoords (fun p => algebraMap Ω Φ (y p))
      (flagLinePt w e φ φ' t k))) ϖ
      (joinClosureDeg (zetaFirst a₀) (Fin.append x z) i - joinClosureDeg (zetaSecond a₀') (Fin.append x' z') i)
      (joinClosureForm M M' (rename (closureVarEquiv ι M M') f₁) (Fin.append f fz) i)
      (joinClosureForm M M' (rename (closureVarEquiv ι M M') g₁) (Fin.append g gz) i) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [joinClosureDeg, joinClosureForm, Fin.append_left]
      apply hRvert
      have hζ : (zetaFirst a₀ ∘ (closureBlockEquiv K).symm - zetaSecond a₀' ∘ (closureBlockEquiv K).symm) ∘
          closureBlockEquiv K = zetaFirst a₀ - zetaSecond a₀' := by
        funext o
        simp
      rw [hζ]
      exact hD₁
    · simp only [joinClosureDeg, joinClosureForm, Fin.append_right]
      have hd : joinDeg (K' := Option Unit) (Fin.append x z j) - joinDeg (Fin.append x' z' j) =
          joinDeg (Fin.append x z j - Fin.append x' z' j) := by
        funext s
        rcases s with s | s <;> simp [joinDeg]
      rw [hd]
      exact hVJ O ϖ Φ K ι (Option Unit) (lineBlocks M M') _ _ _ _ _ (hvert j)

  rw [hExp O ϖ hϖ (K ⊕ Option Unit) (Sum.elim ι (lineBlocks M M')) _ (d + (k - 1)) hJmod (1 + (N + n)) _ _ _ _
    hvJ r (rename (Fin.natAdd 1) Bf) (hBf.rename_isHomogeneous) As (pushExpansion (Fin.natAdd 1) Bs) hAs
    (isPairExpansion_push _ hBs) (Q.map joinDeg) (by rw [List.length_map]; omega),
    pairNum_pushExpansion, joinClosureDeg_natAdd, joinClosureDeg_natAdd, joinClosureForm_natAdd,
    joinClosureForm_natAdd]

  have hPB := hPull O ϖ hϖ Φ K ι (Option Unit) (lineBlocks M M') (fun p => algebraMap Ω Φ (y p))
    (flagLinePt w e φ φ' t k) d (k - 1) (by rw [hPV]; exact hV) hJmod (N + n) (Fin.append x z)
    (Fin.append x' z') (Fin.append f fz) (Fin.append g gz) hvert r Bf hBf Bs hBs Q (by omega)
  split_ifs with hk
  · obtain rfl := hk
    rw [hPB.2 (hBir O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht hkN),
      hPV]
  · exact hPB.1 (by omega)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutForms
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagCutForms.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ) (hk : k < N) (S : Finset (Ideal (MRing (bundleIdx (bundleIdx ι M) M') O))),
      (∀ Q ∈ S, Q.IsPrime ∧ IsRelevant Q ∧ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ Q ∧
        (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ Q) →
      ∃ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs ∧ IsMultiHomog h ch ∧
        (fun o => (cs o : ℤ) - ch o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) ∧
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ∧ h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h ∧
        ∀ Q ∈ S, h ∉ Q

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutProjection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def secondFactorBlocks {K : Type*} : Option K ↪ Option (Option K) where
  toFun o := Option.elim o none fun k => some (some k)
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all

def SegreFlagCutProjection.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ) (hk : k < N),
      (∀ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs → IsMultiHomog h ch →
        (fun o => (cs o : ℤ) - ch o) = zetaFirst a₀ + liftPairDeg (x ⟨k, hk⟩) →
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
        ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W → ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
        FieldNumbers.relDim (FieldNumbers.contractPrime Function.Embedding.some (specialIdeal W)) <
          ((d + k : ℕ) : WithBot (WithTop ℤ))) ∧
      (∀ (cs ch : Option (Option K) → ℕ) (s h : MRing (bundleIdx (bundleIdx ι M) M') O),
        IsMultiHomog s cs → IsMultiHomog h ch →
        (fun o => (cs o : ℤ) - ch o) = zetaSecond a₀' + liftPairDeg (x' ⟨k, hk⟩) →
        s ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) → h ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) →
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s = flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
        ∀ W, (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∈ W → ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
        FieldNumbers.relDim (FieldNumbers.contractPrime secondFactorBlocks (specialIdeal W)) <
          ((d + k : ℕ) : WithBot (WithTop ℤ)))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

