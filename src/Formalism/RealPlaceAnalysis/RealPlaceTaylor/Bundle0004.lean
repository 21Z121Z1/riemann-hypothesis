import Formalism.RealPlaceAnalysis.Bundle0002

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
section
open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

theorem mem_compactSpan_self {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) : x ∈ kSpan ε F x := by
  unfold kSpan
  rw [Submodule.mem_sInf]
  intro S hS
  exact hS.1

theorem compactSpan_le_of_mem {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) {x : V} {S : Submodule ℂ V} (hx : x ∈ S)
    (hS : KStable ε F S) : kSpan ε F x ≤ S :=
  sInf_le ⟨hx, hS⟩

theorem compactSpan_isCompactInvariant {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) : KStable ε F (kSpan ε F x) := by
  intro a b hab y hy
  unfold kSpan at *
  rw [Submodule.mem_sInf] at *
  intro S hS
  exact hS.2 a b hab y (hy S hS)

theorem inner_compactCasimir_self {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (hu : KUnit ε F) (y : V) :
    ⟪y, CasK ε F y⟫_ℂ = ((∑ a, ∑ b, if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) : ℂ) := by
  unfold CasK
  simp only [LinearMap.sum_apply, inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [Module.End.mul_apply, ← hu b a h.symm y (F b a y), inner_self_eq_norm_sq_to_K]
    push_cast; rfl
  · simp

theorem kWtBound_of (hc : KCasSpan) : KWtBound := by
  intro V _ _ n ε F μ ν x y hr hu hx hy hy0 hν
  have h1 := hc V n ε F μ x hr hx y hy
  have h2 := inner_compactCasimir_self ε F hu y
  rw [h1, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ckv ε μ * ‖y‖ ^ 2 = ∑ a, ∑ b, (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) := by
    apply Complex.ofReal_injective
    push_cast at h2 ⊢
    exact h2
  have h4 : nsq ν * ‖y‖ ^ 2 ≤ ∑ a, ∑ b, (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) := by
    unfold nsq dot
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    calc ν a * ν a * ‖y‖ ^ 2 = (if ε a = ε a then ‖F a a y‖ ^ 2 else 0 : ℝ) := by
          rw [if_pos rfl, hν a, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
          ring
      _ ≤ ∑ b, (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ) :=
          Finset.single_le_sum (f := fun b => (if ε a = ε b then ‖F b a y‖ ^ 2 else 0 : ℝ))
            (fun b _ => by split_ifs <;> positivity) (Finset.mem_univ a)
  have hpos : 0 < ‖y‖ ^ 2 := by positivity
  exact le_of_mul_le_mul_right (h4.trans h3.ge) hpos

theorem isCompactInvariant_orthogonal_inf {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (hu : KUnit ε F)
    {K S : Submodule ℂ V} (hK : KStable ε F K) (hS : KStable ε F S) : KStable ε F (Kᗮ ⊓ S) := by
  intro a b hab y hy
  rw [Submodule.mem_inf] at hy ⊢
  refine ⟨?_, hS a b hab y hy.2⟩
  rw [Submodule.mem_orthogonal]
  intro z hz
  rw [← hu b a hab.symm z y]
  exact (Submodule.mem_orthogonal K y).1 hy.1 _ (hK b a hab.symm z hz)

theorem compactDecomposition_of_finrank (he : KHiExist) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (n : ℕ) (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (hr : KRel ε F)
    (hu : KUnit ε F) :
    ∀ (d : ℕ) (S : Submodule ℂ V), Module.finrank ℂ S = d → FiniteDimensional ℂ S →
    KStable ε F S →
    ∃ (m : ℕ) (x : Fin m → V) (μ : Fin m → Fin n → ℝ),
      (∀ i, x i ∈ S ∧ x i ≠ 0 ∧ KHighest ε F (μ i) (x i)) ∧
      (∀ i i', i ≠ i' → ∀ y ∈ kSpan ε F (x i), ∀ z ∈ kSpan ε F (x i'), ⟪y, z⟫_ℂ = 0) ∧
      (⨆ i, kSpan ε F (x i)) = S := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro S hd hfin hS
  by_cases h0 : S = ⊥
  · refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    rw [h0]
    exact iSup_of_empty _
  obtain ⟨x, hxS, hx0, μ, hxμ⟩ := he V n ε F S hfin hr hu hS h0
  have hKS : kSpan ε F x ≤ S := compactSpan_le_of_mem ε F hxS hS
  have : FiniteDimensional ℂ (kSpan ε F x) := Submodule.finiteDimensional_of_le hKS
  have hS'S : (kSpan ε F x)ᗮ ⊓ S < S := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro heq
    have hx' : x ∈ (kSpan ε F x)ᗮ ⊓ S := by rw [heq]; exact hxS
    rw [Submodule.mem_inf] at hx'
    have h1 := (Submodule.mem_orthogonal (kSpan ε F x) x).1 hx'.1 x (mem_compactSpan_self ε F x)
    exact hx0 (inner_self_eq_zero.1 h1)
  have : FiniteDimensional ℂ ↥((kSpan ε F x)ᗮ ⊓ S) := Submodule.finiteDimensional_of_le hS'S.le
  have hlt : Module.finrank ℂ ↥((kSpan ε F x)ᗮ ⊓ S) < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hS'S
  obtain ⟨m, xs, μs, h1, h2, h3⟩ := ih _ hlt ((kSpan ε F x)ᗮ ⊓ S) rfl inferInstance
    (isCompactInvariant_orthogonal_inf ε F hu (compactSpan_isCompactInvariant ε F x) hS)
  have hle : ∀ j, kSpan ε F (xs j) ≤ (kSpan ε F x)ᗮ ⊓ S := fun j =>
    h3 ▸ le_iSup (fun i => kSpan ε F (xs i)) j
  refine ⟨m + 1, Fin.cons x xs, Fin.cons μ μs, ?_, ?_, ?_⟩
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · simp only [Fin.cons_zero]
      exact ⟨hxS, hx0, hxμ⟩
    · simp only [Fin.cons_succ]
      exact ⟨(h1 j).1.2, (h1 j).2⟩
  · intro i i' hii'
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ i' with rfl | ⟨j', rfl⟩
    · exact absurd rfl hii'
    · simp only [Fin.cons_zero, Fin.cons_succ]
      intro y hy z hz
      exact Submodule.inner_right_of_mem_orthogonal hy (hle j' hz).1
    · simp only [Fin.cons_zero, Fin.cons_succ]
      intro y hy z hz
      exact Submodule.inner_left_of_mem_orthogonal hz (hle j hy).1
    · simp only [Fin.cons_succ]
      exact h2 j j' (fun h => hii' (congrArg Fin.succ h))
  · apply le_antisymm
    · refine iSup_le fun i => ?_
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simpa using hKS
      · simp only [Fin.cons_succ]
        exact (hle j).trans inf_le_right
    · calc S = kSpan ε F x ⊔ (kSpan ε F x)ᗮ ⊓ S :=
            (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKS).symm
        _ ≤ _ := by
          refine sup_le ?_ ?_
          · exact le_iSup_of_le (0 : Fin (m + 1)) (by simp)
          · conv_lhs => rw [← h3]
            exact iSup_le fun j => le_iSup_of_le j.succ (by simp)

theorem kDecomp_of (he : KHiExist) (ho : KOrth) : KDecomp := by
  intro V _ _ n ε F S hfin hr hu hS
  exact compactDecomposition_of_finrank he V n ε F hr hu _ S rfl hfin hS

theorem compactSpan_le_isotypicPart {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Fin n → ℝ)) (S : Submodule ℂ V) {y : V}
    {μ : Fin n → ℝ} (hy : y ∈ S) (hμ : μ ∈ T) (hk : KHighest ε F μ y) :
    kSpan ε F y ≤ isoPart ε F T S := by
  unfold isoPart
  exact le_iSup₂_of_le (f := fun y (_ : y ∈ S ∧ ∃ μ ∈ T, KHighest ε F μ y) => kSpan ε F y)
    y ⟨hy, μ, hμ, hk⟩ le_rfl

theorem isotypicPart_le {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Fin n → ℝ)) (S : Submodule ℂ V)
    (hS : KStable ε F S) : isoPart ε F T S ≤ S := by
  unfold isoPart
  exact iSup₂_le fun y hy => compactSpan_le_of_mem ε F hy.1 hS

theorem kIsoSplit_of (hd : KDecomp) (ho : KOrth) : KIsoSplit := by
  intro V _ _ n ε F S T hfin hr hu hS
  constructor
  · have h : isoPart ε F T S ⟂ isoPart ε F Tᶜ S := by
      unfold isoPart
      rw [Submodule.isOrtho_iSup_left]; intro y
      rw [Submodule.isOrtho_iSup_left]; rintro ⟨_, μ, hμT, hyμ⟩
      rw [Submodule.isOrtho_iSup_right]; intro z
      rw [Submodule.isOrtho_iSup_right]; rintro ⟨_, ν, hνT, hzν⟩
      rw [Submodule.isOrtho_iff_inner_eq]
      exact ho V n ε F μ ν y z hr hu hyμ hzν (fun h => hνT (h ▸ hμT))
    exact Submodule.isOrtho_iff_inner_eq.1 h
  · obtain ⟨m, x, μ, h1, h2, h3⟩ := hd V n ε F S hfin hr hu hS
    apply le_antisymm
    · exact sup_le (isotypicPart_le ε F T S hS) (isotypicPart_le ε F Tᶜ S hS)
    · conv_lhs => rw [← h3]
      refine iSup_le fun i => ?_
      by_cases hi : μ i ∈ T
      · exact le_sup_of_le_left (compactSpan_le_isotypicPart ε F T S (h1 i).1 hi (h1 i).2.2)
      · exact le_sup_of_le_right (compactSpan_le_isotypicPart ε F Tᶜ S (h1 i).1 hi (h1 i).2.2)

theorem abs_compactHalfSum_le {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : |rhoC ε a| ≤ n := by
  unfold rhoC
  have c1 := Finset.card_filter_le (univ : Finset (Fin n)) (fun b => a < b ∧ ε b = ε a)
  have c2 := Finset.card_filter_le (univ : Finset (Fin n)) (fun b => b < a ∧ ε b = ε a)
  simp only [Finset.card_univ, Fintype.card_fin] at c1 c2
  have d1 : ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) ≤ n := by exact_mod_cast c1
  have d2 : ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) ≤ n := by exact_mod_cast c2
  have e1 : (0 : ℝ) ≤ ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  have e2 : (0 : ℝ) ≤ ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

theorem compactCasimirValue_le {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) (R : ℝ)
    (hμ : ∀ a, |μ a| ≤ R) : ckv ε μ ≤ n * (R + n) ^ 2 := by
  unfold ckv nsq dot
  have h0 : 0 ≤ ∑ a, rhoC ε a * rhoC ε a := Finset.sum_nonneg fun a _ => mul_self_nonneg _
  have h1 : ∑ a, (μ + rhoC ε) a * (μ + rhoC ε) a ≤ ∑ _a : Fin n, (R + n) ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    simp only [Pi.add_apply]
    have h3 : |μ a + rhoC ε a| ≤ R + n :=
      (abs_add_le (μ a) (rhoC ε a)).trans (add_le_add (hμ a) (abs_compactHalfSum_le ε a))
    rw [← sq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  linarith

theorem kCasBound_of (hd : KDecomp) (hc : KCasSpan) (ho : KOrth) : KCasBound := by
  intro V _ _ n ε F S R hfin hr hu hS hR hw y hy
  obtain ⟨m, x, μ, h1, h2, h3⟩ := hd V n ε F S hfin hr hu hS
  have hy' : y ∈ ⨆ i ∈ (univ : Finset (Fin m)), kSpan ε F (x i) := by simpa [h3] using hy
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ y).1 hy'
  have hC : CasK ε F y = ∑ i, ((ckv ε (μ i) : ℝ) : ℂ) • (v i : V) := by
    rw [← hv, map_sum]
    exact Finset.sum_congr rfl fun i _ => hc V n ε F (μ i) (x i) hr (h1 i).2.2 _ (v i).2
  have key : ∀ c : Fin m → ℂ,
      ⟪y, ∑ i, c i • (v i : V)⟫_ℂ = ∑ i, c i * ⟪(v i : V), (v i : V)⟫_ℂ := by
    intro c
    rw [← hv, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum, Finset.sum_eq_single j]
    · rw [inner_smul_right]
    · intro i _ hij
      rw [inner_smul_right, h2 j i (Ne.symm hij) _ (v j).2 _ (v i).2, mul_zero]
    · simp
  have hvv : ∀ i, ⟪(v i : V), (v i : V)⟫_ℂ = ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hn : ‖y‖ ^ 2 = ∑ i, ‖(v i : V)‖ ^ 2 := by
    have h := key (fun _ => 1)
    simp only [one_smul, one_mul, hv, inner_self_eq_norm_sq_to_K] at h
    apply Complex.ofReal_injective
    push_cast
    exact h
  have key2 := key (fun i => ((ckv ε (μ i) : ℝ) : ℂ))
  rw [hC, key2]
  simp only [hvv]
  have hre : (∑ i, ((ckv ε (μ i) : ℝ) : ℂ) * ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ)).re =
      ∑ i, ckv ε (μ i) * ‖(v i : V)‖ ^ 2 := by
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hre, hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact compactCasimirValue_le ε (μ i) R (hw (μ i) (x i) (h1 i).1 (h1 i).2.1 (h1 i).2.2.1)

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle
section
open MvPolynomial

noncomputable section

namespace Formalism.REAL

section general

variable {σ : Type*}

lemma fischerInner_eq_sum_of_subset (f g : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    fockF f g = ∑ m ∈ s, f.coeff m * star (g.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  apply Finset.sum_subset h
  intro m _ hm
  simp [MvPolynomial.notMem_support_iff.mp hm]

lemma fischerInner_add_left (f1 f2 g : MvPolynomial σ ℂ) :
    fockF (f1 + f2) g = fockF f1 g + fockF f2 g := by
  classical
  rw [fischerInner_eq_sum_of_subset _ _ (f1.support ∪ f2.support) MvPolynomial.support_add,
    fischerInner_eq_sum_of_subset f1 g (f1.support ∪ f2.support) Finset.subset_union_left,
    fischerInner_eq_sum_of_subset f2 g (f1.support ∪ f2.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [coeff_add]; ring

lemma fischerInner_add_right (f g1 g2 : MvPolynomial σ ℂ) :
    fockF f (g1 + g2) = fockF f g1 + fockF f g2 := by
  unfold fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [coeff_add, star_add]; ring

def fischerInnerLeftHom (g : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →+ ℂ :=
  AddMonoidHom.mk' (fun f => fockF f g) (fun a b => fischerInner_add_left a b g)

def fischerInnerRightHom (f : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →+ ℂ :=
  AddMonoidHom.mk' (fun g => fockF f g) (fun a b => fischerInner_add_right f a b)

lemma fischerInner_sum_left {ι : Type*} (s : Finset ι) (h : ι → MvPolynomial σ ℂ) (g : MvPolynomial σ ℂ) :
    fockF (∑ a ∈ s, h a) g = ∑ a ∈ s, fockF (h a) g :=
  map_sum (fischerInnerLeftHom g) h s

lemma fischerInner_sum_right {ι : Type*} (s : Finset ι) (f : MvPolynomial σ ℂ) (h : ι → MvPolynomial σ ℂ) :
    fockF f (∑ a ∈ s, h a) = ∑ a ∈ s, fockF f (h a) :=
  map_sum (fischerInnerRightHom f) h s

lemma fischerInner_neg_left (f g : MvPolynomial σ ℂ) : fockF (-f) g = -fockF f g :=
  map_neg (fischerInnerLeftHom g) f

lemma fischerInner_neg_right (f g : MvPolynomial σ ℂ) : fockF f (-g) = -fockF f g :=
  map_neg (fischerInnerRightHom f) g

lemma fischerInner_eq_star (f g : MvPolynomial σ ℂ) : fockF f g = star (fockF g f) := by
  classical
  rw [fischerInner_eq_sum_of_subset f g (f.support ∪ g.support) Finset.subset_union_left,
    fischerInner_eq_sum_of_subset g f (f.support ∪ g.support) Finset.subset_union_right, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', star_star, star_natCast]; ring

lemma fischerInner_monomial_left (u : σ →₀ ℕ) (c : ℂ) (g : MvPolynomial σ ℂ) :
    fockF (monomial u c) g = c * star (g.coeff u) * ((∏ k ∈ u.support, (u k).factorial : ℕ) : ℂ) := by
  classical
  rw [fischerInner_eq_sum_of_subset _ _ {u} support_monomial_subset, Finset.sum_singleton, coeff_monomial,
    if_pos rfl]

lemma prod_factorial_support_sub_single [DecidableEq σ] (u : σ →₀ ℕ) (v : σ) (hv : u v ≠ 0) :
    (∏ k ∈ u.support, (u k).factorial) =
      u v * ∏ k ∈ (u - Finsupp.single v 1 : σ →₀ ℕ).support, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial := by
  have hsub : (u - Finsupp.single v 1 : σ →₀ ℕ).support ⊆ u.support := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk ⊢
    intro h0; apply hk; simp [Finsupp.tsub_apply, h0]
  have e : ∏ k ∈ (u - Finsupp.single v 1 : σ →₀ ℕ).support, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial =
      ∏ k ∈ u.support, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial :=
    Finset.prod_subset hsub (fun k _ hk => by rw [Finsupp.notMem_support_iff.mp hk]; rfl)
  rw [e]
  have hmem : v ∈ u.support := Finsupp.mem_support_iff.mpr hv
  rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem]
  have h2 : ∏ k ∈ u.support.erase v, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial =
      ∏ k ∈ u.support.erase v, (u k).factorial := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : k ≠ v := Finset.ne_of_mem_erase hk
    simp [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm hk']
  rw [h2, ← mul_assoc]
  congr 1
  simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
  exact (Nat.mul_factorial_pred hv).symm

lemma fischerInner_pderiv_left [DecidableEq σ] (v : σ) (f g : MvPolynomial σ ℂ) :
    fockF (pderiv v f) g = fockF f (X v * g) := by
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [pderiv_monomial, fischerInner_monomial_left, fischerInner_monomial_left, coeff_X_mul']
    by_cases hv : u v = 0
    · have : v ∉ u.support := Finsupp.notMem_support_iff.mpr hv
      simp [hv, this]
    · have : v ∈ u.support := Finsupp.mem_support_iff.mpr hv
      rw [if_pos this, prod_factorial_support_sub_single u v hv]
      push_cast; ring
  | add p q hp hq => rw [map_add, fischerInner_add_left, fischerInner_add_left, hp, hq]

lemma fischerInner_X_mul_left [DecidableEq σ] (v : σ) (f g : MvPolynomial σ ℂ) :
    fockF (X v * f) g = fockF f (pderiv v g) := by
  rw [fischerInner_eq_star, ← fischerInner_pderiv_left, ← fischerInner_eq_star]

end general

variable {M n' : ℕ}

lemma fischerInner_oscillatorLower (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n')
    (f g : MvPolynomial (Fin M × Fin n') ℂ) :
    fockF (bop ε ε' i a f) g = (if sgnv ε ε' i a then 1 else -1) * fockF f (bpl ε ε' i a g) := by
  unfold bop bpl
  split_ifs with h
  · simp only [LinearMap.mulLeft_apply, Derivation.coeFn_coe, one_mul]
    exact fischerInner_pderiv_left _ f g
  · simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, fischerInner_neg_right]
    rw [fischerInner_X_mul_left]; ring

lemma fischerInner_oscillatorRaise (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n')
    (f g : MvPolynomial (Fin M × Fin n') ℂ) :
    fockF (bpl ε ε' i a f) g = (if sgnv ε ε' i a then 1 else -1) * fockF f (bop ε ε' i a g) := by
  unfold bop bpl
  split_ifs with h
  · simp only [LinearMap.mulLeft_apply, Derivation.coeFn_coe, one_mul]
    exact fischerInner_X_mul_left _ f g
  · simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, fischerInner_neg_left]
    rw [fischerInner_pderiv_left]; ring

lemma signMatch_mul_left (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i j : Fin M) (a : Fin n') :
    ((if sgnv ε ε' i a then 1 else -1 : ℂ) * (if sgnv ε ε' j a then 1 else -1)) =
      ((sgn ε i j : ℝ) : ℂ) := by
  unfold sgnv sgn
  generalize ε i = x; generalize ε j = y; generalize ε' a = z
  cases x <;> cases y <;> cases z <;> norm_num

lemma signMatch_mul_right (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a b : Fin n') :
    ((if sgnv ε ε' i b then 1 else -1 : ℂ) * (if sgnv ε ε' i a then 1 else -1)) =
      ((sgn ε' a b : ℝ) : ℂ) := by
  unfold sgnv sgn
  generalize ε i = x; generalize ε' a = y; generalize ε' b = z
  cases x <;> cases y <;> cases z <;> norm_num

theorem fischerAdjointness_holds : FockAdj := by
  intro M n' ε ε' f g
  refine ⟨fun i a => fischerInner_oscillatorLower ε ε' i a f g, fun i j => ?_, fun a b => ?_⟩
  · simp only [Eg, LinearMap.sum_apply, Module.End.mul_apply, fischerInner_sum_left,
      fischerInner_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [fischerInner_oscillatorRaise, fischerInner_oscillatorLower, ← mul_assoc, signMatch_mul_left]
  · simp only [Eg', LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply,
      fischerInner_neg_left, fischerInner_neg_right, fischerInner_sum_left, fischerInner_sum_right, mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fischerInner_oscillatorRaise, fischerInner_oscillatorLower, ← mul_assoc, signMatch_mul_right]

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.TrPowSumFilterZero
section
open Finset

noncomputable section

namespace Formalism.REAL

def TrPow_m {n : ℕ} (l : Fin n → ℂ) : ℕ → Fin n → ℂ
  | 0 => fun _ => 1
  | k + 1 => fun a => l a * TrPow_m l k a - ∑ b ∈ univ.filter (fun b => a < b), TrPow_m l k b

lemma TrPow_m_zero {n : ℕ} (l : Fin n → ℂ) (a : Fin n) : TrPow_m l 0 a = 1 := rfl

lemma TrPow_m_succ {n : ℕ} (l : Fin n → ℂ) (k : ℕ) (a : Fin n) :
    TrPow_m l (k + 1) a = l a * TrPow_m l k a - ∑ b ∈ univ.filter (fun b => a < b), TrPow_m l k b :=
  rfl

lemma TrPow_diag (h : HWDiag) {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (v : V) (hE : GlRel E)
    (hv : IsHW E ν v) : ∀ (k : ℕ) (a : Fin n), epow E k a a v = TrPow_m (lsh ν) k a • v := by
  intro k
  induction k with
  | zero => intro a; simp [epow, TrPow_m_zero]
  | succ k ih =>
    intro a
    rw [h V n E ν v hE hv k a, TrPow_m_succ, ih a]
    simp only [ih]
    rw [← Finset.sum_smul, sub_smul, mul_smul]

end Formalism.REAL
end
end

