import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0062

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsFormDivOfMemChartRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver chartRingOver)

noncomputable section

theorem exists_form_div_of_mem_chartRing {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω]
    {x : Fin (N + 1) → Ω} {i : Fin (N + 1)} (hi : x i ≠ 0) {a : Ω}
    (ha : a ∈ Kleiman.chartRing k x (Kleiman.singleChart hi)) :
    ∃ (e : ℕ) (f : Kleiman.Poly k N), f.IsHomogeneous e ∧ a = aeval x f / x i ^ e := by
  obtain ⟨f, t, e, ht, hf, hte, rfl⟩ := ha
  have ht' : t ∈ Submonoid.closure {(X i : Kleiman.Poly k N)} := by
    have : ((fun l => (X l : Kleiman.Poly k N)) '' ((({i} : Finset (Fin (N + 1))) : Set (Fin (N + 1))))) =
        {X i} := by simp
    rw [← this]; exact ht
  obtain ⟨p, rfl⟩ := Submonoid.mem_closure_singleton.mp ht'
  have hpe : e = p := hte.inj_right (isHomogeneous_X_pow i p) (by
    rw [X_pow_eq_monomial, Ne, monomial_eq_zero]; exact one_ne_zero)
  subst hpe
  exact ⟨e, f, hf, by rw [map_pow, aeval_X]⟩

theorem exists_common_form_div {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω]
    {x : Fin (N + 1) → Ω} {ι : Type} [Fintype ι] {i : Fin (N + 1)} (hi : x i ≠ 0) (a : ι → Ω)
    (ha : ∀ t, a t ∈ Kleiman.chartRing k x (Kleiman.singleChart hi)) :
    ∃ (D : ℕ) (E : ι → Kleiman.Poly k N), (∀ t, (E t).IsHomogeneous D) ∧
      ∀ t, a t = aeval x (E t) / x i ^ D := by
  classical
  choose e f hf hfa using fun t => exists_form_div_of_mem_chartRing hi (ha t)
  have hle : ∀ t, e t ≤ ∑ t, e t := fun t =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  refine ⟨∑ t, e t, fun t => f t * X i ^ (∑ t, e t - e t), fun t => ?_, fun t => ?_⟩
  · have h := (hf t).mul (isHomogeneous_X_pow i (∑ t, e t - e t))
    rwa [Nat.add_sub_cancel' (hle t)] at h
  · have hD : x i ^ (∑ t, e t) = x i ^ e t * x i ^ (∑ t, e t - e t) := by
      rw [← pow_add, Nat.add_sub_cancel' (hle t)]
    rw [hfa t, map_mul, map_pow, aeval_X, hD, mul_div_mul_right _ _ (pow_ne_zero _ hi)]

theorem mConeMapOver_rename_base {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω]
    (x : Fin (N + 1) → Ω) {m : ℕ} (s : Fin m → Ω) {F : Kleiman.Poly k N} {D : ℕ} (hF : F.IsHomogeneous D) :
    mConeMapOver k (graphVec x s) (rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) F) =
      C (aeval x F) * X baseBlock ^ D := by
  have h := congrArg (fun φ => φ F) (mConeMapOver_graph_comp_base (S := k) x s)
  simp only [AlgHom.comp_apply] at h
  rw [h, Kleiman.cone_eq, Kleiman.coneGen_of_isHomogeneous x hF]
  simp only [AlgHom.restrictScalars_apply, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    MvPolynomial.algebraMap_eq]

theorem mConeMapOver_X' {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω] {m : ℕ}
    (y : (Σ c, graphIdx N m c) → Ω) (v : Σ c, graphIdx N m c) :
    mConeMapOver k y (X v) = C (y v) * X v.1 := by
  simp [mConeMapOver]

theorem SectionRatio.full : SectionRatio.Statement := by
  intro k _ N Ω _ _ x Q n m s hx hgen W hW hle j b hYj
  have hmem : ∀ P, mConeMapOver k (graphVec x s) P = 0 → P ∈ W := fun P hP => hle (RingHom.mem_ker.mpr hP)
  obtain ⟨i, hXi⟩ : ∃ i : Fin (N + 1), (X ⟨baseBlock, i⟩ : NumbersDVR.MRing (graphIdx N m) k) ∉ W :=
    hW.relevant baseBlock
  have hi : x i ≠ 0 := fun h0 => hXi (hmem _ (by
    rw [mConeMapOver_X', show graphVec x s ⟨baseBlock, i⟩ = 0 from h0, map_zero, zero_mul]))
  obtain ⟨w, hw, hsum⟩ := exists_graph_inverse Q n s hgen hi
  have hw' : ∀ p : Fin m × Fin m,
      x i ^ (-n) * s p.1 * w p.2 ∈ Kleiman.chartRing k x (Kleiman.singleChart hi) := fun p => by
    rw [← chartRingOver_oneBlock x (fun _ => i) hi]; exact hw p.1 p.2
  obtain ⟨D, E, hE, hEq⟩ := exists_common_form_div hi _ hw'
  have hval : ∀ a c, aeval x (E (a, c)) = x i ^ D * (x i ^ (-n) * s a * w c) := fun a c => by
    have h := hEq (a, c)
    dsimp only at h
    rw [h]; field_simp
  obtain ⟨b0, hb0⟩ : ∃ b0, rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, b0)) ∉ W := by
    by_contra h
    push Not at h
    have key : ∑ c, aeval x (E (j, c)) * s c = x i ^ D * s j := by
      simp only [hval]
      calc ∑ c, x i ^ D * (x i ^ (-n) * s j * w c) * s c
          = x i ^ D * s j * ∑ c, x i ^ (-n) * s c * w c := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
        _ = x i ^ D * s j := by rw [hsum, mul_one]
    have hrel : ∑ c, rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, c)) *
          X ⟨Sum.inr (), c⟩ -
        rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (X i ^ D) *
          X ⟨Sum.inr (), j⟩ ∈ W := by
      apply hmem
      rw [map_sub, map_sum, map_mul, mConeMapOver_rename_base x s (isHomogeneous_X_pow i D), mConeMapOver_X']
      have hc : ∀ c, mConeMapOver k (graphVec x s)
          (rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, c)) *
            X ⟨Sum.inr (), c⟩) = C (aeval x (E (j, c)) * s c) * (X baseBlock ^ D * X (Sum.inr ())) := fun c => by
        rw [map_mul, mConeMapOver_rename_base x s (hE _), mConeMapOver_X', graphVec_inr, map_mul]
        ring
      rw [Finset.sum_congr rfl fun c _ => hc c, ← Finset.sum_mul, ← map_sum, key, graphVec_inr]
      simp only [map_pow, aeval_X, map_mul]
      ring
    have hsumW : ∑ c, rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, c)) *
        X ⟨Sum.inr (), c⟩ ∈ W := W.sum_mem fun c _ => W.mul_mem_right _ (h c)
    have hXY := W.sub_mem hsumW hrel
    rw [sub_sub_cancel, map_pow, rename_X] at hXY
    rcases hW.isPrime.mem_or_mem hXY with h1 | h1
    · exact hXi (hW.isPrime.mem_of_pow_mem _ h1)
    · exact hYj h1
  refine ⟨D, E (b, b0), E (j, b0), hE _, hE _, hb0, hmem _ ?_⟩
  rw [map_sub, map_mul, map_mul, mConeMapOver_rename_base x s (hE _), mConeMapOver_rename_base x s (hE _),
    mConeMapOver_X', mConeMapOver_X', graphVec_inr, graphVec_inr, hval, hval]
  dsimp only
  simp only [map_mul]
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsFormOfMemChartRingOver
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Forms

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in

theorem RowSub.isMultiHomog_mul {f g : MRingOver S ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

omit [Fintype K] in

theorem RowSub.isMultiHomog_C (r : S) : IsMultiHomog (C r : MRingOver S ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
  split_ifs at hm with h
  · subst h; simp
  · exact absurd rfl hm

omit [Fintype K] in

theorem RowSub.isMultiHomog_X [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver S ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X'] at hm
  split_ifs at hm with h
  · subst h
    by_cases hk : k' = k
    · subst hk
      simp [Finsupp.single_apply]
    · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => hk (congrArg Sigma.fst e).symm
      simp [hk]
  · exact absurd rfl hm

omit [Fintype K] in

theorem RowSub.isMultiHomog_pow {f : MRingOver S ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using RowSub.isMultiHomog_C (ι := ι) (1 : S)
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact RowSub.isMultiHomog_mul ih hf

omit [Fintype K] in

theorem RowSub.isMultiHomog_prod {β : Type} (s : Finset β) (f : β → MRingOver S ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (f b) (a b)) : IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RowSub.isMultiHomog_C (ι := ι) (1 : S)
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact RowSub.isMultiHomog_mul (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

theorem RowSub.isMultiHomog_coordProd (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ d k) d := by
  classical
  have h := RowSub.isMultiHomog_prod (S := S) (ι := ι) Finset.univ (fun k => (X ⟨k, c k⟩ : MRingOver S ι) ^ d k)
    (fun k => d k • Pi.single k 1) fun k _ => RowSub.isMultiHomog_pow (RowSub.isMultiHomog_X k (c k)) _
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rwa [e] at h

variable {Ω : Type} [Field Ω] [Algebra S Ω]

theorem RowSub.exists_form_of_mem_chartRingOver (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {z : Ω} (hz : z ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.chartRingOver S y c) :
    ∃ (m : K → ℕ) (h : MRingOver S ι), IsMultiHomog h m ∧ z = aeval y h / ∏ k, y ⟨k, c k⟩ ^ m k := by
  classical
  have hP : ∀ m : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hPadd : ∀ m m' : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ (m + m') k) =
      (∏ k, y ⟨k, c k⟩ ^ m k) * ∏ k, y ⟨k, c k⟩ ^ m' k := fun m m' => by
    simp [pow_add, Finset.prod_mul_distrib]
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨Pi.single p.1 1, X p, RowSub.isMultiHomog_X p.1 p.2, ?_⟩
    rw [aeval_X]
    rw [Finset.prod_eq_single p.1 (fun k _ hk => by simp [hk]) (by simp)]
    simp
  | algebraMap r =>
    exact ⟨0, C r, RowSub.isMultiHomog_C r, by simp⟩
  | add x x' _ _ ih ih' =>
    obtain ⟨m, h, hh, rfl⟩ := ih
    obtain ⟨m', h', hh', rfl⟩ := ih'
    refine ⟨m + m', h * ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ m' k + h' * ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ m k,
      ?_, ?_⟩
    · have h1 := RowSub.isMultiHomog_mul hh (RowSub.isMultiHomog_coordProd (S := S) c m')
      have h2 := RowSub.isMultiHomog_mul hh' (RowSub.isMultiHomog_coordProd (S := S) c m)
      rw [add_comm m' m] at h2
      intro d hd k
      rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
      · exact h1 d hd k
      · exact h2 d hd k
    · rw [hPadd, div_add_div _ _ (hP m) (hP m')]
      simp only [map_add, map_mul, map_prod, map_pow, aeval_X]
      ring
  | mul x x' _ _ ih ih' =>
    obtain ⟨m, h, hh, rfl⟩ := ih
    obtain ⟨m', h', hh', rfl⟩ := ih'
    exact ⟨m + m', h * h', RowSub.isMultiHomog_mul hh hh', by rw [hPadd, map_mul, div_mul_div_comm]⟩

end Forms

theorem RowSub.proof : RowSub.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y k₀ N e γ J I hne hI t ht
  obtain ⟨n, hn⟩ := ht
  choose c hc using hne
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hI k (c k) (hc k)
  set δ : K → ℤ := γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ with hδ
  have h1 := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hn c) hyc
  rw [Submodule.mem_comap, LinearMap.mulRight_apply, Subalgebra.mem_toSubmodule] at h1
  obtain ⟨m, h, hh, heq⟩ := RowSub.exists_form_of_mem_chartRingOver y c hyc h1

  set p : K → ℕ := fun k => (-δ k).toNat with hp
  set q : K → ℕ := fun k => (δ k + p k).toNat with hq
  have hpk : ∀ k, -δ k ≤ (p k : ℤ) := fun k => Int.self_le_toNat _
  have hqk : ∀ k, (q k : ℤ) = δ k + p k := fun k => Int.toNat_of_nonneg (by have := hpk k; omega)

  set T : MRingOver S ι := (∏ j ∈ J.1, (X ⟨k₀, e.symm j⟩ : MRingOver S ι)) ^ n *
    ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ (m k + p k) with hT
  set G : MRingOver S ι := h * ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ q k with hG
  set a : K → ℕ := n • (∑ j ∈ J.1, (Pi.single k₀ 1 : K → ℕ)) + (m + p) with ha
  have hTa : IsMultiHomog T a := by
    refine RowSub.isMultiHomog_mul (RowSub.isMultiHomog_pow (RowSub.isMultiHomog_prod _ _ _ fun j _ =>
      RowSub.isMultiHomog_X k₀ (e.symm j)) n) ?_
    exact RowSub.isMultiHomog_coordProd c (m + p)
  have hak : ∀ k, γ k + (a k : ℤ) = δ k + p k + m k := by
    intro k
    simp only [ha, hδ, Pi.add_apply, Pi.smul_apply, Finset.sum_const, smul_eq_mul,
      IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
    by_cases hk : k = k₀
    · subst hk; simp; ring
    · simp [hk]; ring
  have hGa : IsMultiHomog G (fun k => (γ k + a k).toNat) := by
    have e' : (fun k => (γ k + (a k : ℤ)).toNat) = m + q := by
      funext k
      rw [hak k, Pi.add_apply]
      have := hqk k
      have := hpk k
      omega
    rw [e']
    exact RowSub.isMultiHomog_mul hh (RowSub.isMultiHomog_coordProd c q)
  have hXmem : ∀ k (i : ι k), i ∈ baseCell k₀ e J.1 I k →
      (X ⟨k, i⟩ : MRingOver S ι) ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) :=
    fun k i hi => Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  have hTmem : T ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) := by
    refine mul_mem (pow_mem (prod_mem fun j hj => hXmem k₀ (e.symm j) ?_) n)
      (prod_mem fun k _ => pow_mem (hXmem k (c k) ?_) _)
    · unfold baseCell
      rw [Function.update_self]
      exact Finset.mem_union_right _ (Finset.mem_map_of_mem _ hj)
    · unfold baseCell
      by_cases hk : k = k₀
      · subst hk; rw [Function.update_self]; exact Finset.mem_union_left _ (hc k)
      · rw [Function.update_of_ne hk]; exact hc k
  have hmeet : CellMeets y (baseCell k₀ e J.1 I) := by
    intro k i hi
    unfold baseCell at hi
    by_cases hk : k = k₀
    · subst hk
      rw [Function.update_self, Finset.mem_union] at hi
      rcases hi with hi | hi
      · exact hI k i hi
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact (Kleiman.mem_support _).mp (J.2.2 hj)
    · rw [Function.update_of_ne hk] at hi; exact hI k i hi

  have hx : Kleiman.xProd J ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => (Kleiman.mem_support _).mp (J.2.2 hj)
  have hPm : (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
  have hPp : (∏ k, y ⟨k, c k⟩ ^ (m k + p k)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
  have hTv : aeval y T = Kleiman.xProd J ^ n * ∏ k, y ⟨k, c k⟩ ^ (m k + p k) := by
    simp only [hT, map_mul, map_prod, map_pow, aeval_X]
    rfl
  have hGv : aeval y G = aeval y h * ∏ k, y ⟨k, c k⟩ ^ q k := by
    simp only [hG, map_mul, map_prod, map_pow, aeval_X]
  have hH : aeval y h = Kleiman.xProd J ^ n * t * (∏ k, y ⟨k, c k⟩ ^ (-δ k)) * ∏ k, y ⟨k, c k⟩ ^ m k := by
    rw [eq_div_iff hPm] at heq
    exact heq.symm
  have e1 : (∏ k, y ⟨k, c k⟩ ^ (m k + p k)) = (∏ k, y ⟨k, c k⟩ ^ m k) * ∏ k, y ⟨k, c k⟩ ^ p k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => pow_add _ _ _
  have e2 : (∏ k, y ⟨k, c k⟩ ^ (-δ k)) * ∏ k, y ⟨k, c k⟩ ^ q k = ∏ k, y ⟨k, c k⟩ ^ p k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), hqk k]
    congr 1
    ring
  have hval : t = aeval y G / aeval y T := by
    rw [hTv, hGv, eq_div_iff (mul_ne_zero (pow_ne_zero _ hx) hPp), hH, e1]
    linear_combination (-(Kleiman.xProd J ^ n * t * ∏ k, y ⟨k, c k⟩ ^ m k)) * e2
  show t ∈ cellSec S y γ (baseCell k₀ e J.1 I)
  unfold cellSec
  rw [if_pos hmeet]
  exact Submodule.subset_span ⟨G, T, a, hTmem, hTa, fun k => by rw [hak k]; have := hpk k; have := hqk k; omega,
    hGa, hval⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiHomogRename
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

namespace RowChartAct

variable {S : Type} [CommRing S] {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_mul {f g : MRingOver S ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf m₁ hm₁ k, hg m₂ hm₂ k, Pi.add_apply]

theorem isMultiHomog_rename [DecidableEq K] (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {f : MvPolynomial (Fin (N + 1)) S}
    {d : ℕ} (hf : f.IsHomogeneous d) :
    IsMultiHomog (rename (fun j => (⟨k₀, e.symm j⟩ : Σ k, ι k)) f) (Pi.single k₀ d) := by
  classical
  have hρ : Function.Injective (fun j => (⟨k₀, e.symm j⟩ : Σ k, ι k)) := fun j j' h =>
    e.symm.injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  intro m' hm' k
  rw [support_rename_of_injective hρ] at hm'
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
  have hd := hf (mem_support_iff.mp hm)
  by_cases hk : k = k₀
  · subst hk
    have hval : ∀ i, Finsupp.mapDomain (fun j => (⟨k, e.symm j⟩ : Σ k, ι k)) m ⟨k, i⟩ = m (e i) := fun i => by
      have hi : (⟨k, i⟩ : Σ k, ι k) = (fun j => (⟨k, e.symm j⟩ : Σ k, ι k)) (e i) := by simp
      rw [hi, Finsupp.mapDomain_apply hρ]
    simp_rw [hval]
    rw [Pi.single_eq_same, Equiv.sum_comp e (fun j => m j), ← hd]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Pi.single_eq_of_ne hk]
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨j, hj⟩
    exact hk (congrArg Sigma.fst hj).symm

end RowChartAct

theorem RowChartAct.proof : RowChartAct.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y k₀ N e γ J I r a hr ha
  obtain ⟨f, s, d, hs, hf, hsd, rfl⟩ := hr
  set ρ : Fin (N + 1) → Σ k, ι k := fun j => ⟨k₀, e.symm j⟩ with hρ
  have hsmem : rename ρ s ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) := by
    have hle : (Kleiman.monos (S := S) J.1).map (rename ρ : MvPolynomial _ S →ₐ[S] MRingOver S ι).toRingHom.toMonoidHom ≤
        ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) := by
      rw [Kleiman.monos, MonoidHom.map_mclosure]
      refine Submonoid.closure_le.mpr ?_
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      refine Submonoid.subset_closure ⟨k₀, e.symm j, ?_, by simp [ρ]⟩
      unfold baseCell
      rw [Function.update_self]
      exact Finset.mem_union_right _ (Finset.mem_map_of_mem _ hj)
    exact hle ⟨s, hs, rfl⟩
  unfold cellSec at ha ⊢
  split_ifs at ha ⊢ with hM
  · induction ha using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, t, b, ht, htb, hγ, hg, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨rename ρ f * g, rename ρ s * t, b + Pi.single k₀ d, mul_mem hsmem ht, ?_, ?_, ?_, ?_⟩
      · rw [add_comm b]
        exact RowChartAct.isMultiHomog_mul (RowChartAct.isMultiHomog_rename k₀ e hsd) htb
      · intro k
        have h1 := hγ k
        simp only [Pi.add_apply, Nat.cast_add]
        omega
      · have h2 := RowChartAct.isMultiHomog_mul (RowChartAct.isMultiHomog_rename k₀ e hf) hg
        have heq : (Pi.single k₀ d + fun k => (γ k + b k).toNat) =
            fun k => (γ k + ((b + Pi.single k₀ d : K → ℕ) k : ℕ)).toNat := funext fun k => by
          have h1 := hγ k
          simp only [Pi.add_apply, Nat.cast_add]
          omega
        rw [heq] at h2
        exact h2
      · simp only [map_mul, aeval_rename]
        rw [div_mul_div_comm]
        rfl
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | smul c u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu
  · rw [Submodule.mem_bot] at ha ⊢
    rw [ha, mul_zero]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

