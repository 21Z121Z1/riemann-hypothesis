import ReciprocityTheory.SemistableReduction.Bundle0020
import ReciprocityTheory.SemistableReduction.Bundle0021

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegCE
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField Matrix
open scoped nonZeroDivisors Pointwise

theorem prod_eq_span_prod {K : Type} [Field K] [NumberField K] {k : ℕ}
    (p : Fin k → Submodule (𝓞 K) K) :
    ∏ i, p i = Submodule.span (𝓞 K) (∏ i, (p i : Set K)) := by
  rw [← Submodule.prod_span]
  simp only [Submodule.span_eq]

theorem coe_prod_frac {K : Type} [Field K] [NumberField K] {k : ℕ}
    (F : Fin k → FractionalIdeal (𝓞 K)⁰ K) :
    ((∏ i, F i : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = ∏ i, (F i : Submodule (𝓞 K) K) :=
  map_prod (FractionalIdeal.coeSubmoduleHom (𝓞 K)⁰ K) F Finset.univ

def vecIdx {K : Type} [Field K] [NumberField K] {k : ℕ} (X : Submodule (𝓞 K) (Fin k → K)) : ℕ :=
  (intVec K k).toAddSubgroup.relIndex X.toAddSubgroup

theorem split_norm {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    (X : Submodule (𝓞 K) (Fin k → K)) (hfg : X.FG) (hstd : intVec K k ≤ X)
    (hint : IsIntegralOn S X) :
    ∃ J : FractionalIdeal (𝓞 K)⁰ K, J ≤ 1 ∧ (IsSelfDual S X → S.G.det ≠ 0 → 1 ≤ J) ∧
      FractionalIdeal.absNorm J * (vecIdx X : ℚ) ^ 2 = |Algebra.norm ℚ S.G.det| := by
  obtain ⟨C, z, hfgC, h1, htri, hdiag, hin, hdec, hidx⟩ := lattice_split K k X hfg hstd
  let CF : Fin k → FractionalIdeal (𝓞 K)⁰ K := fun i =>
    ⟨C i, FractionalIdeal.isFractional_of_fg (hfgC i)⟩
  let cF : Fin k → FractionalIdeal (𝓞 K)⁰ K := fun i =>
    ⟨cImage S.c (C i), FractionalIdeal.isFractional_of_fg (cImage_fg S.c S.c_invol (C i) (hfgC i))⟩
  let D : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanSingleton (𝓞 K)⁰ S.G.det
  have hcF0 : ∀ i, cF i ≠ 0 := by
    intro i h
    have : (1 : K) ∈ (cF i : Submodule (𝓞 K) K) :=
      one_le_cImage S.c (C i) (h1 i) (Submodule.mem_one.2 ⟨1, map_one _⟩)
    rw [h, FractionalIdeal.coe_zero] at this
    simp at this
  refine ⟨(∏ i, cF i) * D * ∏ i, CF i, ?_, ?_, ?_⟩
  · rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_one, FractionalIdeal.coe_mul,
      FractionalIdeal.coe_mul, coe_prod_frac, coe_prod_frac, FractionalIdeal.coe_spanSingleton]
    change (∏ i, cImage S.c (C i)) * Submodule.span (𝓞 K) {S.G.det} * (∏ i, C i) ≤ 1
    rw [prod_eq_span_prod, prod_eq_span_prod, Submodule.span_mul_span, Submodule.span_mul_span,
      Submodule.span_le]
    rintro x hx
    obtain ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_prod _ _).1 ha
    obtain ⟨t, ht, rfl⟩ := (Set.mem_fintype_prod _ _).1 hb
    exact split_integral S htri hdiag hin hint g t (fun i => hg i) ht
  · intro hsd hG
    have hCc : (∏ i, cF i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hcF0 i
    have hinv : (∏ i, cF i)⁻¹ ≤ D * ∏ i, CF i := by
      rw [← Finset.prod_inv_distrib, ← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul,
        coe_prod_frac, coe_prod_frac, FractionalIdeal.coe_spanSingleton, prod_eq_span_prod,
        Submodule.span_le]
      intro x hx
      obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_prod _ _).1 hx
      refine split_selfDual S htri hdiag hdec hsd hG g fun j w hw => ?_
      have := (FractionalIdeal.mem_inv_iff (hcF0 j)).1 (hg j) w hw
      obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 this
      exact Submodule.mem_one.2 ⟨a, ha⟩
    calc (1 : FractionalIdeal (𝓞 K)⁰ K) = (∏ i, cF i) * (∏ i, cF i)⁻¹ :=
          (mul_inv_cancel₀ hCc).symm
      _ ≤ (∏ i, cF i) * (D * ∏ i, CF i) := mul_le_mul_right hinv _
      _ = (∏ i, cF i) * D * ∏ i, CF i := by rw [mul_assoc]
  · let ι : Fin k → ℚ := fun i =>
      ((1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex (C i).toAddSubgroup : ℚ)
    have hCF : ∀ i, FractionalIdeal.absNorm (CF i) * ι i = 1 := fun i =>
      absNorm_mul_relIndex_one (C i) (hfgC i) (h1 i)
    have hcFn : ∀ i, FractionalIdeal.absNorm (cF i) * ι i = 1 := by
      intro i
      have := absNorm_mul_relIndex_one (cImage S.c (C i))
        (cImage_fg S.c S.c_invol (C i) (hfgC i)) (one_le_cImage S.c (C i) (h1 i))
      rwa [relIndex_cImage S.c S.c_invol] at this
    have hι0 : ∀ i, ι i ≠ 0 := fun i h => by simpa [h] using hCF i
    have hP0 : ∏ i, ι i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hι0 i
    have hA : FractionalIdeal.absNorm (∏ i, CF i) = (∏ i, ι i)⁻¹ := by
      rw [map_prod, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i _ => eq_inv_of_mul_eq_one_left (hCF i)
    have hC : FractionalIdeal.absNorm (∏ i, cF i) = (∏ i, ι i)⁻¹ := by
      rw [map_prod, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i _ => eq_inv_of_mul_eq_one_left (hcFn i)
    have hI : (vecIdx X : ℚ) = ∏ i, ι i := by
      simp only [vecIdx, hidx, Nat.cast_prod, ι]
    rw [map_mul, map_mul, hA, hC, FractionalIdeal.absNorm_span_singleton, hI]
    field_simp

theorem vec_integral_bound {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    (X : Submodule (𝓞 K) (Fin k → K)) (hfg : X.FG) (hstd : intVec K k ≤ X)
    (hint : IsIntegralOn S X) (hG : S.G.det ≠ 0) :
    (vecIdx X : ℚ) ^ 2 ≤ |Algebra.norm ℚ S.G.det| := by
  obtain ⟨J, hJ1, -, hJ⟩ := split_norm S X hfg hstd hint
  have hN : (0 : ℚ) < |Algebra.norm ℚ S.G.det| := abs_pos.2 (Algebra.norm_ne_zero_iff.2 hG)
  have hpos : (0 : ℚ) < FractionalIdeal.absNorm J * (vecIdx X : ℚ) ^ 2 := by
    rw [hJ]; exact hN
  obtain ⟨I, rfl⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ1
  rw [FractionalIdeal.coeIdeal_absNorm] at hJ hpos
  have hI : Ideal.absNorm I ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have h1 : (1 : ℚ) ≤ (Ideal.absNorm I : ℚ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hI
  have hv : (0 : ℚ) ≤ (vecIdx X : ℚ) ^ 2 := by positivity
  rw [← hJ]
  nlinarith

theorem vec_selfDual_bound {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    (X : Submodule (𝓞 K) (Fin k → K)) (hfg : X.FG) (hstd : intVec K k ≤ X)
    (hsd : IsSelfDual S X) : |Algebra.norm ℚ S.G.det| ≤ (vecIdx X : ℚ) ^ 2 := by
  by_cases hG : S.G.det = 0
  · rw [hG, Algebra.norm_zero, abs_zero]
    positivity
  obtain ⟨J, hJ1, hJsd, hJ⟩ := split_norm S X hfg hstd hsd.1
  have hJe : J = 1 := le_antisymm hJ1 (hJsd hsd hG)
  rw [hJe, map_one, one_mul] at hJ
  exact hJ.ge

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegD
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField
open scoped ComplexOrder

private theorem posDef_diagonal_ofReal_of_pos {r : ℕ} (d : Fin r → ℝ) (hd : ∀ l, 0 < d l) :
    (diagonal fun l => (d l : ℂ)).PosDef := by
  first
  | exact Matrix.posDef_diagonal_iff.mpr fun l => Complex.zero_lt_real.mpr (hd l)
  | exact Matrix.posDef_diagonal_iff.mpr fun l => by exact_mod_cast hd l

theorem sdd_gram_step {K : Type} [Field K] [NumberField K] {r e k₀ k₁ : ℕ} (σ : K →+* ℂ)
    (d : Fin r → ℝ) (hd : ∀ l, 0 < d l) (b₀ : Fin k₀ → Fin r → K) (c b₁ : Fin k₁ → Fin r → K)
    (hb₀cut : ∀ i, b₀ i ∈ cutSub K r e) (hb₀li : LinearIndependent K b₀)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) (hb₁li : LinearIndependent K b₁) :
    Real.log (gramC (diagonal fun l => (d l : ℂ)) σ b₁).det.re ≤
      Real.log (quotGramC (diagonal fun l => (d l : ℂ)) σ b₀ c).det.re := by

  have hcutz : ∀ i (l : Fin r), e ≤ (l : ℕ) → b₀ i l = 0 := by
    intro i l hl
    have h := hb₀cut i
    simp only [cutSub, UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub] at h
    exact h l hl
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal fun l => (d l : ℂ) with hDdef
  have hDpd : D.PosDef := posDef_diagonal_ofReal_of_pos d hd
  have hG0 : ((embM σ b₀)ᴴ * D * embM σ b₀).PosDef :=
    hDpd.conjTranspose_mul_mul_same (sdd_embM_inj σ b₀ hb₀li)
  have hG1 : ((embM σ b₁)ᴴ * D * embM σ b₁).PosDef :=
    hDpd.conjTranspose_mul_mul_same (sdd_embM_inj σ b₁ hb₁li)
  have hu : IsUnit ((embM σ b₀)ᴴ * D * embM σ b₀).det := by
    first
    | exact (Matrix.isUnit_iff_isUnit_det _).mp hG0.isUnit
    | exact hG0.det_pos.ne'.isUnit
  set E : Matrix (Fin r) (Fin k₁) ℂ := embM σ c - embM σ b₀ *
    (((embM σ b₀)ᴴ * D * embM σ b₀)⁻¹ * ((embM σ b₀)ᴴ * D * embM σ c)) with hE

  have hq : quotGramC D σ b₀ c = Eᴴ * D * E := by
    simp only [quotGramC, sdd_gramC_eq, sdd_gramX_eq]
    exact sdd_schur _ _ _ hDpd.1 hG0.1 hu

  have hB1 : ∀ (l : Fin r) (j : Fin k₁),
      embM σ b₁ l j = if e ≤ (l : ℕ) then E l j else 0 := by
    intro l j
    have hb1 : b₁ j l = if e ≤ (l : ℕ) then c j l else 0 := by
      rw [← hcb j]; rfl
    by_cases hl : e ≤ (l : ℕ)
    · have hz : ∀ i, b₀ i l = 0 := fun i => hcutz i l hl
      rw [if_pos hl, hE]
      simp [embM, Matrix.mul_apply, hb1, hl, hz]
    · rw [if_neg hl]
      simp [embM, hb1, hl]
  have hquad : ∀ v : Fin k₁ → ℂ, (star v ⬝ᵥ (((embM σ b₁)ᴴ * D * embM σ b₁) *ᵥ v)).re ≤
      (star v ⬝ᵥ ((Eᴴ * D * E) *ᵥ v)).re :=
    sdd_cut_quad d (fun l => (hd l).le) e E (embM σ b₁) hB1
  obtain ⟨hpos, hle⟩ := sdd_det_mono _ _ hG1 (Matrix.isHermitian_conjTranspose_mul_mul E hDpd.1) hquad
  rw [sdd_gramC_eq, hq]
  exact Real.log_le_log hpos hle

theorem gradedExt_holds (hB : LatDegBasisStatement) (hD : DegAddStatement) :
    GradedExtStatement := by
  unfold GradedExtStatement
  unfold LatDegBasisStatement at hB
  unfold DegAddStatement at hD
  intro K _ _ r e k k₀ k₁ δ B b b₀ b₁ hδ hFG hb hb₀ hb₁

  have hlift : ∀ j, ∃ y ∈ B, projGe K r e y = b₁ j := fun j => Submodule.mem_map.mp (hb₁.1 j)
  choose c hcB hcb using hlift
  have hb₀B : ∀ i, b₀ i ∈ B := fun i => (hb₀.1 i).1
  have hb₀cut : ∀ i, b₀ i ∈ cutSub K r e := fun i => (hb₀.1 i).2
  have hli : LinearIndependent K (Fin.append b₀ c) :=
    sdd_append_li b₀ c b₁ hb₀cut hb₀.2.1 hcb hb₁.2.1
  have hsp : ∀ x ∈ B, x ∈ Submodule.span K (Set.range (Fin.append b₀ c)) :=
    sdd_append_span B b₀ c b₁ hb₀ hcB hcb hb₁
  have hmem : ∀ i, Fin.append b₀ c i ∈ B := by
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [hb₀B, hcB]
  have hk : k = k₀ + k₁ := sdd_card_eq B b (Fin.append b₀ c) hb hmem hli hsp
  subst hk
  have hpd : ∀ σ, (diagMet δ σ).PosDef := fun σ => by
    simp only [diagMet]
    exact posDef_diagonal_ofReal_of_pos (δ σ) (hδ σ)
  have h1 : latDeg (diagMet δ) B b = latDeg (diagMet δ) B (Fin.append b₀ c) :=
    hB K r (k₀ + k₁) (diagMet δ) B b (Fin.append b₀ c) hpd hFG hb ⟨hmem, hli, hsp⟩
  have h2 := hD K r k₀ k₁ (diagMet δ) B b₀ c hpd hFG hb₀B hcB hli hsp
  have hsat : satSub B b₀ = B ⊓ cutSub K r e := sdd_satSub_eq B b₀ hb₀
  rw [hsat] at h2
  have h3 : quotDeg (diagMet δ) B b₀ c ≤ latDeg (diagMet δ) (B.map (projGe K r e)) b₁ := by
    unfold quotDeg latDeg
    rw [sdd_index B b₀ c b₁ hsat hcB hcb]
    have hs : ∑ σ : K →+* ℂ, Real.log (gramC (diagMet δ σ) σ b₁).det.re ≤
        ∑ σ : K →+* ℂ, Real.log (quotGramC (diagMet δ σ) σ b₀ c).det.re :=
      Finset.sum_le_sum fun σ _ =>
        sdd_gram_step σ (δ σ) (hδ σ) b₀ c b₁ hb₀cut hb₀.2.1 hcb hb₁.2.1
    linarith
  linarith [h1, h2, h3]

theorem absDet_holds : AbsDetStatement := by
  intro n A C hA hC h
  exact sdd_absDet A C hA hC h

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegF
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def wPart (r m : ℕ) (i : Fin r) : Fin r :=
  if (i : ℕ) < m ∨ r ≤ (i : ℕ) + m then Fin.rev i else i

def wVal {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i : Fin r) : K :=
  if (i : ℕ) < m ∨ r ≤ (i : ℕ) + m then 1 else g i

theorem wPart_wPart (r m : ℕ) (i : Fin r) : wPart r m (wPart r m i) = i := by
  have hi := i.isLt
  unfold wPart
  by_cases h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m
  · rw [if_pos h, if_pos (by simp only [Fin.val_rev]; omega), Fin.rev_rev]
  · rw [if_neg h, if_neg h]

theorem wPart_outer (r m : ℕ) (i : Fin r) (h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m) :
    wPart r m i = Fin.rev i := by
  unfold wPart
  rw [if_pos h]

theorem wPart_mid (r m : ℕ) (i : Fin r) (h : ¬ ((i : ℕ) < m ∨ r ≤ (i : ℕ) + m)) :
    wPart r m i = i := by
  unfold wPart
  rw [if_neg h]

theorem wVal_outer {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i : Fin r)
    (h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m) : wVal r m g i = 1 := by
  unfold wVal
  rw [if_pos h]

theorem wVal_mid {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i : Fin r)
    (h : ¬ ((i : ℕ) < m ∨ r ≤ (i : ℕ) + m)) : wVal r m g i = g i := by
  unfold wVal
  rw [if_neg h]

theorem wittMat_eq {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) :
    wittMat r m g = Matrix.of fun i j => if j = wPart r m i then wVal r m g i else 0 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [wittMat, Matrix.of_apply]
  by_cases h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m
  · rw [wPart_outer r m i h, wVal_outer r m g i h]
    by_cases hj' : j = Fin.rev i
    · subst hj'
      rw [if_pos rfl, if_pos (by simp only [Fin.val_rev]; omega)]
    · rw [if_neg hj']
      rw [if_neg (by rintro ⟨h1, -⟩; apply hj'; ext; simp only [Fin.val_rev]; omega),
        if_neg (by rintro ⟨rfl, h2, h3⟩; omega)]
  · rw [wPart_mid r m i h, wVal_mid r m g i h]
    by_cases hij : j = i
    · subst hij
      rw [if_pos rfl, if_neg (by rintro ⟨h1, h2⟩; omega), if_pos ⟨rfl, by omega, by omega⟩]
    · rw [if_neg hij, if_neg (by rintro ⟨h1, h2⟩; omega), if_neg (by rintro ⟨h1, -⟩; exact hij h1.symm)]

theorem wittMat_map_mul {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (σ : K →+* ℂ)
    (v : Fin r → ℂ) :
    (wittMat r m g).map σ * diagonal v * (wittMat r m g).map σ =
      diagonal fun i => σ (wVal r m g i) * v (wPart r m i) * σ (wVal r m g (wPart r m i)) := by
  rw [wittMat_eq]
  ext i k
  rw [Matrix.mul_apply, Finset.sum_eq_single (wPart r m i)]
  · simp only [Matrix.mul_diagonal, Matrix.map_apply, Matrix.of_apply, if_pos rfl, wPart_wPart,
      Matrix.diagonal_apply]
    by_cases hik : i = k
    · subst hik
      simp
    · rw [if_neg (Ne.symm hik), if_neg hik, map_zero, mul_zero]
  · intro j _ hj
    simp only [Matrix.mul_diagonal, Matrix.map_apply, Matrix.of_apply, if_neg hj, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

def adMet {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K) (dd : Fin r → ℝ) :
    (K →+* ℂ) → Fin r → ℝ :=
  fun σ i => if (i : ℕ) < m then dd i else if r ≤ (i : ℕ) + m then (dd (Fin.rev i))⁻¹
    else ‖σ (g i)‖

theorem adMet_pos {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K)
    (dd : Fin r → ℝ) (hdd : ∀ i, 0 < dd i)
    (hg : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0) (σ : K →+* ℂ) (i : Fin r) :
    0 < adMet r m g dd σ i := by
  have hi := i.isLt
  unfold adMet
  split_ifs with h1 h2
  · exact hdd i
  · exact inv_pos.mpr (hdd _)
  · exact norm_pos_iff.mpr ((map_ne_zero σ).mpr (hg i (by omega) (by omega)))

theorem adMet_conj {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K)
    (dd : Fin r → ℝ) (σ : K →+* ℂ) :
    adMet r m g dd ((starRingEnd ℂ).comp σ) = adMet r m g dd σ := by
  funext i
  unfold adMet
  simp only [RingHom.comp_apply, Complex.norm_conj]

theorem wVal_adMet {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K)
    (dd : Fin r → ℝ) (h2m : 2 * m ≤ r)
    (hg : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0) (σ : K →+* ℂ)
    (hreal : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → conj (σ (g i)) = σ (g i))
    (i : Fin r) :
    σ (wVal r m g i) * (((adMet r m g dd σ (wPart r m i) : ℝ) : ℂ))⁻¹ *
      σ (wVal r m g (wPart r m i)) = ((adMet r m g dd σ i : ℝ) : ℂ) := by
  have hi := i.isLt
  by_cases h1 : (i : ℕ) < m
  · have ho : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m := Or.inl h1
    rw [wPart_outer r m i ho, wVal_outer r m g i ho,
      wVal_outer r m g (Fin.rev i) (by simp only [Fin.val_rev]; omega)]
    unfold adMet
    simp only [Fin.val_rev, Fin.rev_rev]
    rw [if_neg (show ¬ (r - ((i : ℕ) + 1) < m) by omega), if_pos (show r ≤ r - ((i : ℕ) + 1) + m by omega),
      if_pos h1]
    simp
  · by_cases h2 : r ≤ (i : ℕ) + m
    · have ho : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m := Or.inr h2
      rw [wPart_outer r m i ho, wVal_outer r m g i ho,
        wVal_outer r m g (Fin.rev i) (by simp only [Fin.val_rev]; omega)]
      unfold adMet
      simp only [Fin.val_rev]
      rw [if_pos (show r - ((i : ℕ) + 1) < m by omega), if_neg h1, if_pos h2]
      simp
    · have hm : ¬ ((i : ℕ) < m ∨ r ≤ (i : ℕ) + m) := by omega
      rw [wPart_mid r m i hm, wVal_mid r m g i hm]
      unfold adMet
      rw [if_neg h1, if_neg h2]
      have hr := hreal i (by omega) (by omega)
      have hne : σ (g i) ≠ 0 := (map_ne_zero σ).mpr (hg i (by omega) (by omega))
      have hz : ((σ (g i)).re : ℂ) = σ (g i) := Complex.conj_eq_iff_re.mp hr
      rw [← hz, Complex.norm_real, Real.norm_eq_abs]
      have hx : (σ (g i)).re ≠ 0 := by
        intro h0
        apply hne
        rw [← hz, h0, Complex.ofReal_zero]
      have habs : ((|(σ (g i)).re| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hx
      have hsq : ((σ (g i)).re : ℂ) * (σ (g i)).re = ((|(σ (g i)).re| : ℝ) : ℂ) * |(σ (g i)).re| := by
        exact_mod_cast (abs_mul_abs_self (σ (g i)).re).symm
      calc ((σ (g i)).re : ℂ) * (↑|(σ (g i)).re|)⁻¹ * ((σ (g i)).re : ℂ)
          = (((σ (g i)).re : ℂ) * (σ (g i)).re) * (↑|(σ (g i)).re|)⁻¹ := by ring
        _ = (((|(σ (g i)).re| : ℝ) : ℂ) * |(σ (g i)).re|) * (↑|(σ (g i)).re|)⁻¹ := by rw [hsq]
        _ = ((|(σ (g i)).re| : ℝ) : ℂ) := by field_simp

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

