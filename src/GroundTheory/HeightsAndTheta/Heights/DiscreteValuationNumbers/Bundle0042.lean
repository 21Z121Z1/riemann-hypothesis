import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinGradedFrameIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPairNum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0037

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairIff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)

universe u v w

namespace FlagPairCharacterisation

section Flags

variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

theorem finrank_flag (w : Module.Basis (Fin N) Ω E) (i : Fin (N + 1)) :
    Module.finrank Ω (Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i})) = i := by
  classical
  have hli : LinearIndependent Ω (fun x : {j : Fin N | (j : ℕ) < i} => w x) :=
    w.linearIndependent.comp _ Subtype.val_injective
  rw [Set.image_eq_range, finrank_span_eq_card hli]
  simp only [Fintype.card_subtype, Set.mem_ofPred_eq]
  rw [Fin.card_filter_val_lt]
  exact min_eq_right (Nat.lt_succ_iff.mp i.isLt)

theorem flag_eq (w : Module.Basis (Fin N) Ω E) {Vs : Fin (N + 1) → Submodule Ω E} (mono : Monotone Vs)
    (dim : ∀ i, Module.finrank Ω (Vs i) = (i : ℕ)) (hmem : ∀ j, w j ∈ Vs j.succ) (i : Fin (N + 1)) :
    Vs i = Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) := by
  have : FiniteDimensional Ω E := Module.Finite.of_basis w
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_flag, dim])
  rw [Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  exact mono (Fin.le_def.mpr (by simpa using hj)) (hmem j)

theorem flag_mono (w : Module.Basis (Fin N) Ω E) :
    Monotone fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) :=
  fun _ _ hij => Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk (Fin.le_def.mp hij))

theorem mem_flag_iff (w : Module.Basis (Fin N) Ω E) (n : ℕ) (x : E) :
    x ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < n}) ↔ ∀ j : Fin N, n ≤ (j : ℕ) → w.repr x j = 0 := by
  rw [Module.Basis.mem_span_image]
  constructor
  · intro h j hj
    by_contra hne
    exact absurd (h (Finsupp.mem_support_iff.mpr hne)) (by simpa using hj)
  · intro h j hj
    by_contra hne
    exact Finsupp.mem_support_iff.mp hj (h j (by simpa using hne))

theorem linearIndependent_of_not_mem {Vs : Fin (N + 1) → Submodule Ω E} (mono : Monotone Vs)
    {gen : Fin N → E} (hmem : ∀ i, gen i ∈ Vs i.succ) (hnot : ∀ i, gen i ∉ Vs i.castSucc) :
    LinearIndependent Ω gen := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  by_contra hne
  push Not at hne
  set S := Finset.univ.filter (fun q : Fin N => a q ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨q, hq⟩ := hne
    exact ⟨q, by simp [hS, hq]⟩
  set i := S.max' hSne
  have hi : a i ≠ 0 := by
    have := S.max'_mem hSne
    simpa [hS] using this
  have hrest : ∑ q ∈ Finset.univ.erase i, a q • gen q ∈ Vs i.castSucc := by
    refine Submodule.sum_mem _ fun q hq => ?_
    by_cases haq : a q = 0
    · rw [haq, zero_smul]
      exact Submodule.zero_mem _
    · have hle : q ≤ i := S.le_max' q (by simp [hS, haq])
      have hlt : q < i := lt_of_le_of_ne hle (Finset.ne_of_mem_erase hq)
      exact Submodule.smul_mem _ _ (mono (Fin.le_def.mpr (by simp; omega)) (hmem q))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at ha
  have hai : a i • gen i ∈ Vs i.castSucc := by
    rw [eq_neg_of_add_eq_zero_left ha]
    exact Submodule.neg_mem _ hrest
  apply hnot i
  have := Submodule.smul_mem _ (a i)⁻¹ hai
  rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at this

end Flags

section Frames

variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
  {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {N : ℕ} {E : Type*}
  [AddCommGroup E] [Module Ω E] {B : ChartBundle o (segreVec y) N E}

omit [∀ k, Fintype (ι k)] in

theorem linearIndependent_gen {Vs : Fin (N + 1) → Submodule Ω E} (mono : Monotone Vs)
    (dim : ∀ i, Module.finrank Ω (Vs i) = (i : ℕ)) {m : Fin N → K → ℤ} {gen : Fin N → E}
    (hmem : ∀ i, gen i ∈ Vs i.succ) (hfr : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsGradedFrame o y B Vs m gen)
    {c : ∀ k, ι k} (hc : segreVec y c ≠ 0) : LinearIndependent Ω gen := by
  classical
  obtain ⟨k, fs, cs, -, -, hsum, hl⟩ := hfr c hc
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      simp at hsum
    · exact h0
  obtain ⟨b, hli, hsp, -, hb⟩ := hl ⟨0, hk⟩
  have : FiniteDimensional Ω E := Module.Finite.of_basis (Module.Basis.mk hli hsp.ge)
  refine linearIndependent_of_not_mem mono hmem fun i hi => ?_
  have hbV : ∀ j : Fin N, j ≤ i → b j ∈ Vs i.castSucc := by
    intro j hj
    obtain ⟨u, -, hu⟩ := hb j
    have h1 : gen j ∈ Vs i.castSucc := by
      rcases hj.lt_or_eq with hlt | rfl
      · exact mono (Fin.le_def.mpr (by simp; omega)) (hmem j)
      · exact hi
    have h2 : Vs j.castSucc ≤ Vs i.castSucc := mono (Fin.le_def.mpr (by simpa using hj))
    have := Submodule.add_mem _ (h2 hu) (Submodule.smul_mem _ (u * IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (m j)) h1)
    simpa using this
  have hli' : LinearIndependent Ω
      (fun j : {j : Fin N // j ≤ i} => (⟨b j, hbV j j.2⟩ : Vs i.castSucc)) :=
    LinearIndependent.of_comp (Vs i.castSucc).subtype (hli.comp Subtype.val Subtype.val_injective)
  have hcard := hli'.fintype_card_le_finrank
  rw [dim] at hcard
  simp only [Fintype.card_subtype, Fin.val_castSucc] at hcard
  have hfl : (Finset.univ.filter fun j : Fin N => j ≤ i) =
      Finset.univ.filter fun j : Fin N => (j : ℕ) < (i : ℕ) + 1 := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
    omega
  rw [hfl, Fin.card_filter_val_lt, min_eq_right (Nat.succ_le_of_lt i.isLt)] at hcard
  omega

theorem eval_ne_zero {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
    [DecidableEq K] {b : K → ℤ} {f g : MRing ι O}
    (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (pointIdeal O y) b f g) : aeval y g ≠ 0 := by
  obtain ⟨⟨α, β, -, hβ, -⟩, -, hg, -⟩ := h
  intro h0
  apply hg
  rw [pointIdeal, RingHom.mem_ker, FlagTypings.pointConeMap_of_isMultiHomog y hβ, h0, map_zero,
    zero_mul]

end Frames

theorem proof : Statement.{u, v, w} := by
  intro O _ _ _ Ω _ _ K _ _ ι _ y N E _ _ B B' ϖ hϖ hP
  have hV : ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor (pointIdeal O y) ϖ b f g ↔
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O y) b f g :=
    fun b f g => (VerticalDivisorCharacterisation.proof O K ι (pointIdeal O y) ϖ b f g hϖ hP).symm
  have hG := fun (B₀ : ChartBundle O (segreVec y) N E) (w₀ : Module.Basis (Fin N) Ω E)
      (b : Fin N → K → ℤ) => GradedFrameCharacterisation.proof O Ω K ι y N E B₀ w₀ b
  refine ⟨fun w w' x x' f g => ⟨fun h => ?_, ?_⟩, fun hc F => ?_⟩
  · have hvert := fun i => (hV _ _ _).1 (h.vertical i)
    have hgy : ∀ i, aeval y (g i) ≠ 0 := fun i => eval_ne_zero (hvert i)
    have hflip := FlagTypings.triangular_flip w w' h.sameFlag
    have hspan : (fun i : Fin (N + 1) => Submodule.span Ω (w' '' {j : Fin N | (j : ℕ) < i})) =
        fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) := by
      funext i
      refine flag_eq w (flag_mono w') (finrank_flag w') (fun j => ?_) i
      rw [mem_flag_iff]
      intro q hq
      exact hflip.1 j q (Fin.lt_def.mpr (by simp at hq; omega))
    refine ⟨{ Vs := fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i})
              mono := flag_mono w
              dim := finrank_flag w
              top := ?_
              deg := x
              gen := w
              gen_mem := fun i => ?_
              frame := (hG B w x).1 h.flag
              deg' := x'
              gen' := w'
              gen'_mem := fun i => ?_
              frame' := ?_
              f := f
              g := g
              rel := fun i => ?_
              vert := hvert }, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · show Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (Fin.last N : ℕ)}) = ⊤
      have hu : {j : Fin N | (j : ℕ) < (Fin.last N : ℕ)} = Set.univ := by
        ext j
        simp
      rw [hu, Set.image_univ, w.span_eq]
    · show w i ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (i.succ : ℕ)})
      rw [mem_flag_iff]
      intro q hq
      rw [w.repr_self, Finsupp.single_apply, if_neg]
      rintro rfl
      simp at hq
    · show w' i ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (i.succ : ℕ)})
      rw [mem_flag_iff]
      intro q hq
      exact h.sameFlag i q (Fin.lt_def.mpr (by simp at hq; omega))
    · have := (hG B' w' x').1 h.flag'
      rwa [hspan] at this
    · show _ ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (i.castSucc : ℕ)})
      rw [mem_flag_iff]
      intro q hq
      rw [map_sub, map_smul, w.repr_self, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
        Finsupp.single_apply]
      by_cases hiq : i = q
      · subst hiq
        rw [if_pos rfl, mul_one, h.generic i, mul_div_cancel_right₀ _ (hgy i), sub_self]
      · rw [if_neg hiq, mul_zero, sub_zero]
        exact h.sameFlag i q (lt_of_le_of_ne (Fin.le_def.mpr (by simpa using hq)) hiq)
  · rintro ⟨F, hgen, hgen', rfl, rfl, rfl, rfl⟩
    have hVs : F.Vs = fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) :=
      funext (flag_eq w F.mono F.dim fun j => by rw [← hgen]; exact F.gen_mem j)
    have hVs' : F.Vs = fun i : Fin (N + 1) => Submodule.span Ω (w' '' {j : Fin N | (j : ℕ) < i}) :=
      funext (flag_eq w' F.mono F.dim fun j => by rw [← hgen']; exact F.gen'_mem j)
    refine ⟨(hG B w F.deg).2 ?_, (hG B' w' F.deg').2 ?_, fun i j hij => ?_,
      fun i => (hV _ _ _).2 (F.vert i), fun i => ?_⟩
    · have := F.frame
      rwa [hVs, hgen] at this
    · have := F.frame'
      rwa [hVs', hgen'] at this
    · have := F.gen'_mem i
      rw [hVs, hgen'] at this
      exact (mem_flag_iff w _ _).1 this j (by simp; omega)
    · have := F.rel i
      rw [hVs, hgen, hgen'] at this
      have h2 := (GradedFrameCharacterisation.repr_of_sub_mem w this).2
      rw [h2, div_mul_cancel₀ _ (eval_ne_zero (F.vert i))]
  · obtain ⟨c, hc⟩ := hc
    exact ⟨linearIndependent_gen F.mono F.dim F.gen_mem F.frame hc,
      linearIndependent_gen F.mono F.dim F.gen'_mem F.frame' hc⟩

end FlagPairCharacterisation

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPolyPairNum
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace plainPolynomialPairNumber

open plainPairNumber (term rename_divDiff_eq_sum)

theorem rename_divDiff_add {r : ℕ} (l : Fin r) (A B : MvPolynomial (Fin r) ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l (A + B)) =
      rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l A) +
        rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l B) := by
  classical
  rw [rename_divDiff_eq_sum l (A + B) support_add,
    rename_divDiff_eq_sum l A Finset.subset_union_left,
    rename_divDiff_eq_sum l B Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_add, map_add, add_mul]

theorem term_tail {N q : ℕ} (i : Fin N) (μ : Fin N →₀ ℕ) (t : Fin q →₀ ℕ) (ν : Fin (N + q) →₀ ℕ)
    (hc : ∀ j, ν (Fin.castAdd q j) = μ j) (hn : ∀ j, ν (Fin.natAdd N j) = t j) :
    term (Fin.castAdd q i) ν =
      rename (Sum.map (Fin.castAdd q) (Fin.castAdd q)) (term i μ) *
        ∏ j : Fin q, X (Sum.inl (Fin.natAdd N j)) ^ t j := by
  have hlt : ∀ j : Fin q, ¬ Fin.natAdd N j < Fin.castAdd q i := by
    intro j h
    rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at h
    omega
  have hgt : ∀ j : Fin q, Fin.castAdd q i < Fin.natAdd N j := by
    intro j
    rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]
    omega
  have hcc : ∀ j k : Fin N, (Fin.castAdd q j < Fin.castAdd q k ↔ j < k) := by
    intro j k
    simp only [Fin.lt_def, Fin.val_castAdd]
  have h1 : (∏ j ∈ Finset.univ.filter (fun j => j < Fin.castAdd q i),
      (X (Sum.inr j) : MvPolynomial (Fin (N + q) ⊕ Fin (N + q)) ℤ) ^ ν j) =
      ∏ j ∈ Finset.univ.filter (fun j => j < i), X (Sum.inr (Fin.castAdd q j)) ^ μ j := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_add]
    simp only [hlt, if_false, Finset.prod_const_one, mul_one, hcc, hc]
  have h3 : (∏ j ∈ Finset.univ.filter (fun j => Fin.castAdd q i < j),
      (X (Sum.inl j) : MvPolynomial (Fin (N + q) ⊕ Fin (N + q)) ℤ) ^ ν j) =
      (∏ j ∈ Finset.univ.filter (fun j => i < j), X (Sum.inl (Fin.castAdd q j)) ^ μ j) *
        ∏ j : Fin q, X (Sum.inl (Fin.natAdd N j)) ^ t j := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_add]
    simp only [hgt, if_true, hcc, hc, hn]
  unfold term
  rw [h1, h3, hc i]
  simp only [map_mul, map_prod, map_pow, map_sum, rename_X, Sum.map_inl, Sum.map_inr]
  ring

theorem rename_monomial_tail {N q : ℕ} (t : Fin q →₀ ℕ) (c : ℤ) :
    rename (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q))) (monomial t c) =
      C c * ∏ j : Fin q, X (Sum.inl (Fin.natAdd N j)) ^ t j := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_mul, map_prod, map_pow, rename_X, rename_C]

theorem rename_divDiff_castAdd_monomial {N q : ℕ} (i : Fin N) (G : MvPolynomial (Fin N) ℤ)
    (t : Fin q →₀ ℕ) (c : ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd q i)
        (rename (Fin.castAdd q) G * rename (Fin.natAdd N) (monomial t c))) =
      rename (Sum.map (Fin.castAdd q) (Fin.castAdd q))
          (rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff i G)) *
        rename (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q)))
          (monomial t c) := by
  classical
  set T : Fin (N + q) →₀ ℕ := t.mapDomain (Fin.natAdd N) with hT
  have hinj : Function.Injective
      (fun μ : Fin N →₀ ℕ => Finsupp.mapDomain (Fin.castAdd q) μ + T) :=
    fun a b h => Finsupp.mapDomain_injective (Fin.castAdd_injective _ _) (add_right_cancel h)
  have hsub : (rename (Fin.castAdd q) G * monomial T c).support ⊆
      G.support.image (fun μ => Finsupp.mapDomain (Fin.castAdd q) μ + T) := by
    intro ν hν
    rw [mem_support_iff, coeff_mul_monomial'] at hν
    split_ifs at hν with hle
    · have hmem : ν - T ∈ (rename (Fin.castAdd q) G).support :=
        mem_support_iff.mpr (left_ne_zero_of_mul hν)
      rw [support_rename_of_injective (Fin.castAdd_injective _ _), Finset.mem_image] at hmem
      obtain ⟨μ, hμ, he⟩ := hmem
      exact Finset.mem_image.mpr ⟨μ, hμ, by rw [he, tsub_add_cancel_of_le hle]⟩
    · exact absurd rfl hν
  rw [rename_monomial, ← hT, rename_divDiff_eq_sum (Fin.castAdd q i) _ hsub,
    Finset.sum_image fun a _ b _ h => hinj h, rename_divDiff_eq_sum i G subset_rfl, map_sum,
    Finset.sum_mul, rename_monomial_tail]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hc : ∀ j, (Finsupp.mapDomain (Fin.castAdd q) μ + T) (Fin.castAdd q j) = μ j := by
    intro j
    have hj : Fin.castAdd q j ∉ Set.range (Fin.natAdd N : Fin q → Fin (N + q)) := by
      rintro ⟨k, hk⟩
      have := congrArg Fin.val hk
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply (Fin.castAdd_injective _ _), hT,
      Finsupp.mapDomain_of_notMem_range _ _ hj, add_zero]
  have hn : ∀ j, (Finsupp.mapDomain (Fin.castAdd q) μ + T) (Fin.natAdd N j) = t j := by
    intro j
    have hj : Fin.natAdd N j ∉ Set.range (Fin.castAdd q : Fin N → Fin (N + q)) := by
      rintro ⟨k, hk⟩
      have := congrArg Fin.val hk
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _ hj, hT,
      Finsupp.mapDomain_apply (Fin.natAdd_injective _ _), zero_add]
  rw [coeff_mul_monomial, coeff_rename_mapDomain _ (Fin.castAdd_injective _ _),
    term_tail i μ t _ hc hn, C_mul]
  simp only [map_mul, rename_C]
  ring

theorem rename_divDiff_castAdd_mul {N q : ℕ} (i : Fin N) (G : MvPolynomial (Fin N) ℤ)
    (Q : MvPolynomial (Fin q) ℤ) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd q i)
        (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q)) =
      rename (Sum.map (Fin.castAdd q) (Fin.castAdd q))
          (rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff i G)) *
        rename (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q))) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial t c => exact rename_divDiff_castAdd_monomial i G t c
  | add A B hA hB => rw [map_add, mul_add, rename_divDiff_add, hA, hB, map_add, mul_add]

variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_mul_tail {σ : Type*} [DecidableEq σ] {q : ℕ} (cls : σ → K → ℤ)
    (L : Fin q → K → ℤ) (z : Fin q → σ) (hz : cls ∘ z = L) (A : MvPolynomial σ ℤ)
    (Q : MvPolynomial (Fin q) ℤ) (W : Ideal (MRing ι O)) :
    classNum cls (A * rename z Q) [] W = ∑ μ ∈ Q.support, Q.coeff μ * classNum cls A (classList L μ) W := by
  have hadd : ∀ H : MvPolynomial σ ℤ, classNum cls H [] W = classNumAddHom cls [] W H := fun _ => rfl
  conv_lhs => rw [Q.as_sum]
  rw [map_sum, Finset.mul_sum, hadd, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [rename_monomial, show monomial (μ.mapDomain z) (Q.coeff μ) =
      Q.coeff μ • monomial (μ.mapDomain z) (1 : ℤ) by rw [smul_monomial, smul_eq_mul, mul_one],
    mul_smul_comm, map_zsmul, smul_eq_mul, ← hadd, plainPairNumber.classNum_mul_monomial,
    classList_mapDomain, hz, List.append_nil]

theorem proof : plainPolynomialPairNumber.Statement := by
  intro O _ _ _ K _ _ ι _ P d N x x' f g m G hG hm q L Q hQ
  have hH : (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q :
      MvPolynomial (Fin (N + q)) ℤ).IsHomogeneous (d + 1) := by
    have h3 := (hG.rename_isHomogeneous (f := Fin.castAdd q)).mul
      (hQ.rename_isHomogeneous (f := Fin.natAdd N))
    rwa [show m + (d + 1 - m) = d + 1 by omega] at h3
  rw [BundleExamples.pairNum_eq P d _ _ _ _ hH]
  unfold pairNum
  have hr : ratDiv P 1 1 = fun _ => 0 := funext fun W => sub_self _
  have hz : ∀ n : Ideal (MRing ι O) → ℤ, cycEval n (fun _ => 0) = 0 := by
    intro n
    simp [cycEval]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, hr, hz, Finset.sum_const_zero, add_zero]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hZ := ratDiv_finite_support P (f i) (g i)
  simp only [cycEval_eq_sum hZ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun W _ => ?_
  have hcls : Sum.elim (Fin.append x L) (Fin.append x' L) ∘
      Sum.map (Fin.castAdd q) (Fin.castAdd q) = Sum.elim x x' := by
    funext p
    cases p <;> simp [Fin.append_left]
  have hL : Sum.elim (Fin.append x L) (Fin.append x' L) ∘
      (fun j : Fin q => (Sum.inl (Fin.natAdd N j) : Fin (N + q) ⊕ Fin (N + q))) = L := by
    funext j
    simp [Fin.append_right]
  rw [rename_divDiff_castAdd_mul, classNum_mul_tail _ L _ hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [plainPairNumber.classNum_rename _ (Sum.map_injective.mpr
      ⟨Fin.castAdd_injective _ _, Fin.castAdd_injective _ _⟩), hcls]
  ring

end plainPolynomialPairNumber

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosureTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagClosureTrdeg.Statement : Prop :=
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
    ∀ k : ℕ, 1 ≤ k → k ≤ N →
      Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸
          pointIdeal O (flagClosurePt y w e φ φ' t k)) =
        Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + ((k + 1 : ℕ) : Cardinal)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

