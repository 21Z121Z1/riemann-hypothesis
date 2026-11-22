import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.YHom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.Bundle0001

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.AugmentationDegreeZero
section
noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial Finset

def wy (D : ℕ) : Fin D ⊕ Fin D → ℕ := Sum.elim 0 1

theorem KK {D : ℕ} (t u : Fin D → P D) (ω : W D) (J : Finset (Fin D)) :
    K t (K u ω) J = ∑ i ∈ Jᶜ, ∑ l ∈ Jᶜ, (if l = i then 0 else
      (sgn i J : P D) * (sgn l (insert i J) : P D) * (t i * u l) * ω (insert l (insert i J))) := by
  simp only [K]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.compl_insert, ← Finset.filter_ne', Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : l = i
  · simp [h]
  · simp only [h, if_false, ne_eq, not_false_eq_true, if_true]
    ring

end PI.EagonNorthcottZ
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.BasisZeroEqSingle
section
noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial

private def mon {D : ℕ} (α : Fin D → ℕ) : Fin D ⊕ Fin D →₀ ℕ := ∑ i, Finsupp.single (Sum.inr i) (α i)

private def yp {D : ℕ} (α : Fin D → ℕ) : P D := ∏ i, ys i ^ α i

private lemma mon_inr {D : ℕ} (α : Fin D → ℕ) (i : Fin D) : mon α (Sum.inr i) = α i := by
  classical
  simp [mon, Finsupp.finsetSum_apply, Finsupp.single_apply]

private lemma mon_inl {D : ℕ} (α : Fin D → ℕ) (i : Fin D) : mon α (Sum.inl i) = 0 := by
  classical
  simp [mon, Finsupp.finsetSum_apply]

private lemma yp_eq {D : ℕ} (α : Fin D → ℕ) : yp α = monomial (mon α) (1 : ℤ) := by
  rw [yp, mon, monomial_sum_one]
  simp [ys, X_pow_eq_monomial]

private lemma noX_iff {D : ℕ} (f : P D) : NoX f ↔ ∃ g, rename Sum.inr g = f := Iff.rfl

private lemma nox_zero {D : ℕ} : NoX (0 : P D) := (noX_iff _).2 ⟨0, map_zero _⟩

private lemma nox_add {D : ℕ} {f g : P D} (hf : NoX f) (hg : NoX g) : NoX (f + g) := by
  obtain ⟨u, rfl⟩ := (noX_iff _).1 hf
  obtain ⟨v, rfl⟩ := (noX_iff _).1 hg
  exact (noX_iff _).2 ⟨u + v, map_add _ _ _⟩

private lemma nox_smul {D : ℕ} (c : ℤ) {f : P D} (hf : NoX f) : NoX (c • f) := by
  obtain ⟨u, rfl⟩ := (noX_iff _).1 hf
  exact (noX_iff _).2 ⟨c • u, map_smul _ _ _⟩

private lemma noX_coeff {D : ℕ} {f : P D} (hf : NoX f) {m : Fin D ⊕ Fin D →₀ ℕ} (hm : m ∈ f.support)
    (i : Fin D) : m (Sum.inl i) = 0 := by
  classical
  by_contra h
  obtain ⟨g, rfl⟩ := (noX_iff _).1 hf
  have h1 : Sum.inl i ∈ (rename Sum.inr g).vars := (mem_vars_iff_mem_support _).2 ⟨m, hm, Finsupp.mem_support_iff.2 h⟩
  have h2 := vars_rename Sum.inr g h1
  simp at h2

private lemma yhom_zero {D a : ℕ} : YHom (D := D) a 0 := by
  intro m hm
  simp at hm

private lemma yhom_add {D a : ℕ} {f g : P D} (hf : YHom a f) (hg : YHom a g) : YHom a (f + g) := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (support_add hm) with h | h
  exacts [hf m h, hg m h]

private lemma yhom_smul {D a : ℕ} (c : ℤ) {f : P D} (hf : YHom a f) : YHom a (c • f) :=
  fun m hm => hf m (support_smul hm)

private lemma memA {D a : ℕ} {f : P D} (h1 : NoX f) (h2 : YHom a f) :
    f ∈ Submodule.span ℤ (yp '' {α : Fin D → ℕ | ∑ i, α i = a}) := by
  classical
  rw [f.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hmon : m = mon (fun i => m (Sum.inr i)) := by
    ext v
    rcases v with i | i
    · rw [mon_inl, noX_coeff h1 hm i]
    · rw [mon_inr]
  have hmem : monomial m (1 : ℤ) ∈ yp '' {α : Fin D → ℕ | ∑ i, α i = a} :=
    ⟨fun i => m (Sum.inr i), h2 m hm, by rw [yp_eq, ← hmon]⟩
  have : monomial m (coeff m f) = coeff m f • monomial m (1 : ℤ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

private lemma K_zero {D : ℕ} (t : Fin D → P D) : K t 0 = 0 := by
  funext J
  simp [K]

private lemma K_add {D : ℕ} (t : Fin D → P D) (ω η : W D) : K t (ω + η) = K t ω + K t η := by
  funext J
  simp [K, mul_add, Finset.sum_add_distrib]

private lemma K_smul {D : ℕ} (t : Fin D → P D) (c : ℤ) (ω : W D) : K t (c • ω) = c • K t ω := by
  funext J
  simp only [K, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm]

private lemma isZL_iff {D a j : ℕ} (ω : W D) : IsZL a j ω ↔
    (((∀ J, J.card ≠ j → ω J = 0) ∧ ∀ J, YHom a (ω J)) ∧ K ys ω = 0) ∧ ∀ J, NoX (ω J) := Iff.rfl

private def ZL (D a j : ℕ) : Submodule ℤ (W D) where
  carrier := {ω | IsZL a j ω}
  zero_mem' := (isZL_iff _).2 ⟨⟨⟨fun _ _ => rfl, fun _ => yhom_zero⟩, K_zero _⟩, fun _ => nox_zero⟩
  add_mem' := by
    intro ω η hω hη
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := (isZL_iff _).1 hω
    obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := (isZL_iff _).1 hη
    refine (isZL_iff _).2 ⟨⟨⟨fun J hJ => ?_, fun J => yhom_add (h2 J) (g2 J)⟩, ?_⟩,
      fun J => nox_add (h4 J) (g4 J)⟩
    · simp [h1 J hJ, g1 J hJ]
    · rw [K_add, h3, g3, add_zero]
  smul_mem' := by
    intro c ω hω
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := (isZL_iff _).1 hω
    refine (isZL_iff _).2 ⟨⟨⟨fun J hJ => ?_, fun J => yhom_smul c (h2 J)⟩, ?_⟩,
      fun J => nox_smul c (h4 J)⟩
    · simp [h1 J hJ]
    · rw [K_smul, h3, smul_zero]

private def G (D a : ℕ) : Set (W D) :=
  Set.range fun p : Finset (Fin D) × {α // α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) a} =>
    (Pi.single p.1 (yp p.2.1) : W D)

private lemma memB {D a : ℕ} {ω : W D} (h : ∀ J, NoX (ω J) ∧ YHom a (ω J)) :
    ω ∈ Submodule.span ℤ (G D a) := by
  classical
  rw [← Finset.univ_sum_single ω]
  refine Submodule.sum_mem _ fun J _ => ?_
  have h3 := Submodule.mem_map_of_mem (f := LinearMap.single ℤ (fun _ : Finset (Fin D) => P D) J)
    (memA (h J).1 (h J).2)
  rw [← Submodule.span_image] at h3
  refine Submodule.span_mono ?_ h3
  rintro _ ⟨_, ⟨α, hα, rfl⟩, rfl⟩
  exact ⟨(J, ⟨α, by simpa [Finset.mem_piAntidiag] using hα⟩), by simp⟩

end PI.EagonNorthcottZ
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.CardFilterLtInsert
section
noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial PI.EagonNorthcott

def nn (m : ℕ) (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => m
  | j + 1 => r (j + 1)

def BB {D m : ℕ} (e0 : Fin m → W D) (r : ℕ → ℕ) (b : ∀ j, Fin (r j) → W D) : ∀ j, Fin (nn m r j) → W D
  | 0 => e0
  | j + 1 => b (j + 1)

theorem ct_Phi {D r : ℕ} (b : Fin r → W D) (v : Fin r → S D) (i : Fin D) (J : Finset (Fin D)) :
    ct i (Phi b v) J = ∑ k, inx (v k) * ct i (b k) J := by
  simp only [ct, Phi]
  split_ifs
  · simp
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem inx_X {D : ℕ} (i : Fin D) : inx (X i : S D) = xs i := by simp [inx, xs]

theorem mu_inx {D : ℕ} (s : S D) : mu (inx s) = s := by
  simp only [mu, inx]
  rw [aeval_rename, Sum.elim_comp_inl, aeval_X_left_apply]

theorem mu_ys {D : ℕ} (i : Fin D) : mu (ys i : P D) = X i := by simp [mu, ys]

theorem frame_of (hE : LEnum) (hB0 : LBasis0) (hB : LBasis) (hV : LVan) (hI : LInj) (hR : LRan) (hC : LCt)
    (hX : LKx) : Frame := by
  intro D a
  obtain ⟨m, e, he, hae⟩ := hE D a
  choose r b hb using hB D a
  have hBB : ∀ j, IsZBasis a j (BB (b0 e) r b j) := by
    intro j
    cases j with
    | zero => exact hB0 D a m e he hae
    | succ j => exact hb (j + 1)
  have hmem : ∀ j (i : Fin D) (k : Fin (nn m r (j + 1))), ∃ c : Fin (nn m r j) → ℤ,
      ∑ p, c p • BB (b0 e) r b j p = ct i (BB (b0 e) r b (j + 1) k) := by
    intro j i k
    rw [← Submodule.mem_span_range_iff_exists_fun]
    exact ((hBB j).2 _).1 (hC D a j i _ (((hBB (j + 1)).2 _).2 (Submodule.subset_span ⟨k, rfl⟩)))
  choose c hc using hmem
  refine ⟨nn m r, e, fun j => Matrix.of fun p k i => c j i k p, fun j => Phi (BB (b0 e) r b j), ⟨?_, he, hae⟩,
    fun j => hI D a j _ _ (hBB j), fun j => ?_, fun j ω => hR D a j _ _ (hBB j) ω, fun j v => ?_, fun v => ?_⟩
  · intro j hj
    by_contra hne
    have k : Fin (nn m r j) := ⟨0, Nat.pos_of_ne_zero hne⟩
    exact (hBB j).1.ne_zero k (hV D a j hj _ (((hBB j).2 _).2 (Submodule.subset_span ⟨k, rfl⟩)))
  · funext J
    simp [Phi]
  · funext J
    have key : ∀ i k, ct i (BB (b0 e) r b (j + 1) k) J = ∑ p, (c j i k p : P D) * BB (b0 e) r b j p J := by
      intro i k
      rw [← hc j i k, Finset.sum_apply]
      simp [zsmul_eq_mul]
    rw [hX D]
    simp only [Phi, dmap, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply,
      lin, map_sum, map_mul, map_intCast, inx_X, ct_Phi, key, Finset.mul_sum, Finset.sum_mul]
    conv_lhs =>
      rw [Finset.sum_comm]
      arg 2
      ext k
      rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => by ring
  · simp only [aug, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
      Phi, BB, b0, if_true, map_sum, map_mul, mu_inx, map_prod, map_pow, mu_ys]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end PI.EagonNorthcottZ
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.DivisionLowersSecondDegree
section
noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial

variable {D : ℕ}

abbrev Cnd (ι : Fin D → Fin D ⊕ Fin D) (i : Fin D) (m : (Fin D ⊕ Fin D) →₀ ℕ) : Prop :=
  0 < m (ι i) ∧ ∀ l, l < i → m (ι l) = 0

end PI.EagonNorthcottZ
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.EagonNorthcottExactOf
section
noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial PI.EagonNorthcott

theorem main_of (hA : Anti) (hS : Sq) (hL : KLin) (hG : GrLin) (hGX : GrX) (hGY : GrY) (hX : ExX) (hY : ExY) (hYz : ExYz) :
    Main := by
  intro D a
  induction a with
  | zero =>
    intro j ω hω hy _
    have h0 := hYz D j ω hω hy
    refine ⟨0, ⟨fun _ _ => rfl, fun J m hm => by simp at hm⟩, ?_, ?_⟩
    · have := (hL D ys (0 : W D) 0).1; simpa using this
    · have := (hL D xs (0 : W D) 0).1; rw [h0]; simpa using this
  | succ a ih =>
    intro j ω hω hy hx
    obtain ⟨θ, hθ, hθω⟩ := hY D a j ω hω hy
    have h1 : K ys (K xs θ) = 0 := by rw [hA D ys xs θ, hθω, hx, neg_zero]
    obtain ⟨η', hη', hη'y, hη'x⟩ := ih j (K xs θ) (hGX D a (j + 1) θ hθ) h1 (hS D xs θ)
    have h2 : K xs (θ - η') = 0 := by rw [(hL D xs θ η').1, hη'x, sub_self]
    obtain ⟨ζ, hζ, hζx⟩ := hX D a (j + 1) (θ - η') (hG D a (j + 2) θ η' hθ hη').1 h2
    refine ⟨-K ys ζ, (hG D (a + 1) (j + 2) _ _ (hGY D a (j + 2) ζ hζ) (hGY D a (j + 2) ζ hζ)).2, ?_, ?_⟩
    · rw [(hL D ys (K ys ζ) 0).2, hS D ys ζ, neg_zero]
    · rw [(hL D xs (K ys ζ) 0).2, hA D xs ys ζ, neg_neg, hζx, (hL D ys θ η').1, hθω, hη'y, sub_zero]

end PI.EagonNorthcottZ
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.ExactSecondDegreeZeroOf
section
noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial

private theorem sgn_one {D : ℕ} (i : Fin D) (J : Finset (Fin D)) (h : ∀ l ∈ J, ¬ l < i) : sgn i J = 1 := by
  unfold sgn
  rw [Finset.filter_eq_empty_iff.mpr h]; simp

end PI.EagonNorthcottZ
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.LatticeInjective
section
noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial

abbrev Ex (D : ℕ) : P D ≃ₐ[ℤ] MvPolynomial (Fin D) (MvPolynomial (Fin D) ℤ) := sumAlgEquiv ℤ (Fin D) (Fin D)

def cmp {D : ℕ} (β : Fin D →₀ ℕ) (f : P D) : P D := rename Sum.inr (coeff β (Ex D f))

lemma Ex_inl {D : ℕ} (s : S D) :
    Ex D (rename Sum.inl s) = map (C : ℤ →+* MvPolynomial (Fin D) ℤ) s := by
  induction s using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

lemma Ex_inr {D : ℕ} (g : S D) : Ex D (rename Sum.inr g) = C g := by
  induction g using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

lemma cmp_zero {D : ℕ} (β : Fin D →₀ ℕ) : cmp β (0 : P D) = 0 := by simp [cmp]

lemma sum_cmp {D : ℕ} (f : P D) (B : Finset (Fin D →₀ ℕ)) (hB : (Ex D f).support ⊆ B) :
    ∑ β ∈ B, inx (monomial β 1) * cmp β f = f := by
  apply (Ex D).injective
  rw [map_sum]
  have h : ∀ β ∈ B, Ex D (inx (monomial β 1) * cmp β f) = monomial β (coeff β (Ex D f)) := by
    intro β _
    rw [map_mul, inx, cmp, Ex_inl, Ex_inr, map_monomial, map_one, mul_comm, C_mul_monomial, mul_one]
  rw [Finset.sum_congr rfl h]
  conv_rhs => rw [as_sum (Ex D f)]
  symm
  refine Finset.sum_subset hB fun β _ hβ => ?_
  rw [mem_support_iff, not_not] at hβ
  simp [hβ]

end PI.EagonNorthcottZ
end
end

