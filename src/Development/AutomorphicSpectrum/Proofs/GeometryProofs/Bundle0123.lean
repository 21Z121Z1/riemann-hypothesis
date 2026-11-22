import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0112
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MaximalTorusInFibre
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0023
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootHeightDifferenceBound
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.CloseHt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

section Places

variable {L : Type} [Field L] [NumberField L]

lemma log_sup_support {ι : Type} [Fintype ι] (x : ι → L) (hx : ∃ i, x i ≠ 0) :
    (Function.support fun v : FinitePlace L => Real.log (⨆ i, v (x i))).Finite := by
  classical
  obtain ⟨i₀, hi₀⟩ := hx
  haveI : Nonempty ι := ⟨i₀⟩
  have hS : (⋃ i ∈ Finset.univ.filter (fun i => x i ≠ 0),
      Function.mulSupport fun v : FinitePlace L => v (x i)).Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun i hi => ?_
    exact FinitePlace.mulSupport_finite (by simpa using hi)
  refine hS.subset fun v hv => ?_
  by_contra hn
  apply hv
  have h1 : ∀ i, x i ≠ 0 → v (x i) = 1 := by
    intro i hi
    by_contra h
    exact hn (Set.mem_biUnion (by simpa using hi) h)
  have h2 : ∀ i, v (x i) ≤ 1 := by
    intro i
    by_cases hi : x i = 0
    · simp [hi]
    · exact (h1 i hi).le
  have h3 : (⨆ i, v (x i)) = 1 := by
    have hle : (⨆ i, v (x i)) ≤ 1 := ciSup_le h2
    have hge : (1 : ℝ) ≤ ⨆ i, v (x i) := by
      have hb : BddAbove (Set.range fun i => v (x i)) := (Set.finite_range _).bddAbove
      calc (1 : ℝ) = v (x i₀) := (h1 i₀ hi₀).symm
        _ ≤ _ := le_ciSup hb i₀
    exact le_antisymm hle hge
  simp [h3]

lemma block_support {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (a : K → ℝ)
    (x : ∀ k, ι k → L) (hx : ∀ k, ∃ i, x k i ≠ 0) :
    (Function.support fun v : FinitePlace L => ∑ k, a k * Real.log (⨆ i, v (x k i))).Finite := by
  refine (Set.finite_iUnion fun k => log_sup_support (x k) (hx k)).subset fun v hv => ?_
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  exact Set.mem_iUnion.2 ⟨k, right_ne_zero_of_mul hk⟩

lemma avg_mem (S : (L →+* ℂ) → ℝ) {lo hi : ℝ} (h : ∀ σ, S σ ∈ Set.Icc lo hi) :
    (Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ, S σ ∈ Set.Icc lo hi := by
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hc : ∀ r : ℝ, ∑ _σ : L →+* ℂ, r = Module.finrank ℚ L * r := fun r => by
    simp [Finset.card_univ, Embeddings.card L ℂ]
  have h1 : Module.finrank ℚ L * lo ≤ ∑ σ, S σ := by
    rw [← hc]
    exact Finset.sum_le_sum fun σ _ => (h σ).1
  have h2 : ∑ σ, S σ ≤ Module.finrank ℚ L * hi := by
    rw [← hc]
    exact Finset.sum_le_sum fun σ _ => (h σ).2
  constructor
  · rw [inv_mul_eq_div, le_div_iff₀ hd]
    linarith
  · rw [inv_mul_eq_div, div_le_iff₀ hd]
    linarith

end Places

section Join

variable {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)]

lemma ptHt_sub_join (a₁ : K₁ → ℝ) (a₂ : K₂ → ℝ) (φ₁ : ((Σ k, ι₁ k) → ℂ) → ℝ) (φ₂ : ((Σ k, ι₂ k) → ℂ) → ℝ)
    (L : Type) [Field L] [NumberField L] (z : (Σ k, joinIdx ι₁ ι₂ k) → L) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ptHt a₁ φ₁ L (fun p => z (joinInl ι₁ ι₂ p)) - ptHt a₂ φ₂ L (fun p => z (joinInr ι₁ ι₂ p)) =
      ptHt (Sum.elim a₁ (-a₂))
        (fun Z => φ₁ (fun p => Z (joinInl ι₁ ι₂ p)) - φ₂ (fun p => Z (joinInr ι₁ ι₂ p))) L z := by
  unfold ptHt
  rw [← mul_sub]
  congr 1
  have s₁ := block_support (L := L) (ι := ι₁) a₁ (fun k i => z (joinInl ι₁ ι₂ ⟨k, i⟩))
    (fun k => hz (Sum.inl k))
  have s₂ := block_support (L := L) (ι := ι₂) a₂ (fun k i => z (joinInr ι₁ ι₂ ⟨k, i⟩))
    (fun k => hz (Sum.inr k))
  have e : (∑ᶠ v : FinitePlace L, ∑ k, Sum.elim a₁ (-a₂) k * Real.log (⨆ i, v (z ⟨k, i⟩))) =
      (∑ᶠ v : FinitePlace L, ∑ k, a₁ k * Real.log (⨆ i, v (z (joinInl ι₁ ι₂ ⟨k, i⟩)))) -
        ∑ᶠ v : FinitePlace L, ∑ k, a₂ k * Real.log (⨆ i, v (z (joinInr ι₁ ι₂ ⟨k, i⟩))) := by
    rw [← finsum_sub_distrib s₁ s₂]
    refine finsum_congr fun v => ?_
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rfl
  rw [e]
  simp only [Finset.sum_sub_distrib]
  simp only [joinInl, joinInr]
  ring

end Join

section Embed

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {L : Type} [Field L]

lemma aeval_emb (σ : L →+* ℂ) (z : (Σ k, ι k) → L) (f : MRing ι) :
    aeval (fun p => σ (z p)) f = σ (aeval z f) :=
  (comp_aeval_apply (R := ℤ) (f := z) σ.toIntAlgHom f).symm

lemma ptsOver_emb (σ : L →+* ℂ) {P : Ideal (MRing ι)} {z : (Σ k, ι k) → L} (hz : z ∈ ptsOver L P) :
    (fun p => σ (z p)) ∈ ptsOver ℂ P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, (map_ne_zero σ).2 hi⟩
  · rw [aeval_emb, hz.2 f hf, map_zero]

lemma hasVal_emb (σ : L →+* ℂ) {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} {z : (Σ k, ι k) → L} {w : L}
    (h : HasVal y a u z w) : HasVal y a u (fun p => σ (z p)) (σ w) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, h0, h1⟩ := h
  refine ⟨dg, dh, g, f, hg, hf, hd, hy, ?_, ?_⟩
  · rw [aeval_emb]
    exact (map_ne_zero σ).2 h0
  · rw [aeval_emb, aeval_emb, h1, map_mul]

end Embed

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

lemma line_a (M : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) : (M.line t j).a = (M.line 1 j).a := by
  cases j with
  | none => rfl
  | some r => simp [RootModel.line, M.x_deg]

lemma coef_eq {M R : RootModel Ψ N} (h : M.kA = R.kA) (lam : Wt Ψ N) (s : ℝ) (j : Option (Ψ × Fin N)) :
    M.coef lam s j = R.coef lam s j := by
  cases j with
  | none => simp [RootModel.coef, h]
  | some r => rfl

lemma sum_abs_coef (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ) :
    ∑ j, |M.coef lam s j| ≤ l1 lam + |s| := by
  rw [Fintype.sum_option, add_comm]
  have h1 : |M.coef lam s none| ≤ |s| := by
    have hk : (1 : ℝ) ≤ M.kA := by exact_mod_cast M.kA_pos
    simp only [RootModel.coef]
    rw [abs_div, Nat.abs_cast]
    exact div_le_self (abs_nonneg s) hk
  have h2 : ∑ r : Ψ × Fin N, |M.coef lam s (some r)| = l1 lam := by
    simp [RootModel.coef, l1, Fintype.sum_prod_type]
  linarith

def lineDefect (M R : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) :
    ((Σ k, joinIdx M.ι R.ι k) → ℂ) → ℝ := fun Z =>
  Real.log ((M.line t j).h fun p => Z (joinInl M.ι R.ι p)) -
    Real.log ((R.line 1 j).h fun p => Z (joinInr M.ι R.ι p))

lemma lineHt_sub (M R : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) (L : Type) [Field L] [NumberField L]
    (z : (Σ k, joinIdx M.ι R.ι k) → L) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    lineHt (M.line t j) L (fun p => z (joinInl M.ι R.ι p)) -
        lineHt (R.line 1 j) L (fun p => z (joinInr M.ι R.ι p)) =
      ptHt (fun k => (joinDeg M R j k : ℝ)) (lineDefect M R t j) L z := by
  unfold lineHt
  rw [ptHt_sub_join _ _ _ _ L z hz]
  have e : (Sum.elim (fun k => ((M.line t j).a k : ℝ)) (-fun k => ((R.line 1 j).a k : ℝ))) =
      fun k => (joinDeg M R j k : ℝ) := by
    funext k
    cases k with
    | inl k => simp [joinDeg, line_a M t j]
    | inr k => simp [joinDeg]
  rw [e]
  rfl

theorem close_ht (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω)
    (u : Option (Ψ × Fin N) → M.Ω) (c t s lo hi : ℝ) (lam : Wt Ψ N) (hC : Close M R i u c)
    (hA : ArchBetween M R i u t lam s lo hi) (L : Type) [Field L] [NumberField L]
    (z) (hz : z ∈ ptsOver L (mCoordIdeal (joinOf M R i))) :
    rootHt M t lam s L (fun p => z (joinInl M.ι R.ι p)) - rootHt R 1 lam s L (fun p => z (joinInr M.ι R.ι p)) ∈
      Set.Icc (lo - (l1 lam + |s|) * c) (hi + (l1 lam + |s|) * c) := by
  obtain ⟨harith, hbir, -, -⟩ := GlobalTheory.T.join_model_points_project Ψ N M R i
  choose val hval0 hval using fun j => hC.unit j L z hz
  have hc : 0 ≤ c := by
    obtain ⟨-, q, m, hq, -, hlog, -, -⟩ := hC.vert none
    have h0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    exact (mul_nonneg_iff_of_pos_left hq').1 (h0.trans hlog)

  let E : Option (Ψ × Fin N) → ℝ := fun j => (Module.finrank ℚ L : ℝ)⁻¹ *
    ∑ σ : L →+* ℂ, (lineDefect M R t j (fun p => σ (z p)) - Real.log ‖σ (val j)‖)
  let D : Option (Ψ × Fin N) → ℝ := fun j => lineHt (M.line t j) L (fun p => z (joinInl M.ι R.ι p)) -
    lineHt (R.line 1 j) L (fun p => z (joinInr M.ι R.ι p))
  have hD : ∀ j, |D j - E j| ≤ c := by
    intro j
    have := GlobalTheory.T.vertical_bound_height_compare (M.K ⊕ R.K) (joinIdx M.ι R.ι) M.Ω (joinOf M R i) (dimFl Ψ N + 1) harith hbir
      (joinDeg M R j) (u j) c (hC.vert j) (lineDefect M R t j) L z hz (val j) (hval0 j) (hval j)
    simp only [D, E]
    rw [lineHt_sub M R t j L z hz.1]
    exact this
  have hE : ∑ j, M.coef lam s j * E j ∈ Set.Icc lo hi := by
    have e : ∑ j, M.coef lam s j * E j = (Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ : L →+* ℂ, ∑ j, M.coef lam s j *
        (lineDefect M R t j (fun p => σ (z p)) - Real.log ‖σ (val j)‖) := by
      simp only [E]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      ring
    rw [e]
    refine avg_mem _ fun σ => ?_
    exact hA _ (ptsOver_emb σ hz) (fun j => σ (val j)) fun j => hasVal_emb σ (hval j)
  have hsplit : rootHt M t lam s L (fun p => z (joinInl M.ι R.ι p)) -
      rootHt R 1 lam s L (fun p => z (joinInr M.ι R.ι p)) =
      ∑ j, M.coef lam s j * E j + ∑ j, M.coef lam s j * (D j - E j) := by
    unfold rootHt
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← coef_eq hC.kA lam s j]
    simp only [D]
    ring
  have hb : |∑ j, M.coef lam s j * (D j - E j)| ≤ (l1 lam + |s|) * c := by
    calc |∑ j, M.coef lam s j * (D j - E j)| ≤ ∑ j, |M.coef lam s j * (D j - E j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |M.coef lam s j| * c := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hD j) (abs_nonneg _)
      _ = (∑ j, |M.coef lam s j|) * c := by rw [Finset.sum_mul]
      _ ≤ (l1 lam + |s|) * c := mul_le_mul_of_nonneg_right (sum_abs_coef M lam s) hc
  rw [hsplit]
  have := abs_le.1 hb
  exact ⟨by linarith [hE.1, this.1], by linarith [hE.2, this.2]⟩

end GlobalTheory.CompanionTheory.Ar.Ht.CloseHt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGroupRelDimGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

private theorem smoothOfRelativeDimension_restrict_of_le {A S : Scheme.{0}} (f : A ⟶ S) {n : ℕ} {V W : A.Opens} (h : V ≤ W)
    (hW : SmoothOfRelativeDimension n (W.ι ≫ f)) : SmoothOfRelativeDimension n (V.ι ≫ f) := by
  have := smoothOfRelativeDimension_comp 0 n (A.homOfLE h) (W.ι ≫ f)
  rw [zero_add, ← Category.assoc, Scheme.homOfLE_ι] at this
  exact this

private theorem relDim_eq_of_mem_of_mem {A S : Scheme.{0}} (f : A ⟶ S) {n m : ℕ} {V W : A.Opens}
    (hV : SmoothOfRelativeDimension n (V.ι ≫ f)) (hW : SmoothOfRelativeDimension m (W.ι ≫ f))
    {x : A} (hxV : x ∈ V) (hxW : x ∈ W) : n = m :=
  ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ (smoothOfRelativeDimension_restrict_of_le f inf_le_left hV) (smoothOfRelativeDimension_restrict_of_le f inf_le_right hW)
    ⟨x, hxV, hxW⟩

theorem reldim_eq_of_two_pullbacks {P A S : Scheme.{0}} {f : A ⟶ S} {b : A ⟶ S} {p : P ⟶ A} {a₁ a₂ : P ⟶ A}
    (h₁ : IsPullback a₁ p f b) (h₂ : IsPullback a₂ p f b) {n₁ n₂ : ℕ} {W₁ W₂ : A.Opens}
    (d₁ : SmoothOfRelativeDimension n₁ (W₁.ι ≫ f)) (d₂ : SmoothOfRelativeDimension n₂ (W₂.ι ≫ f))
    (z : P) (hz₁ : a₁ z ∈ W₁) (hz₂ : a₂ z ∈ W₂) : n₁ = n₂ := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange n₁
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange n₂
  have e₁ : SmoothOfRelativeDimension n₁ ((a₁ ⁻¹ᵁ W₁).ι ≫ p) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n₁)
      ((isPullback_morphismRestrict a₁ W₁).paste_vert h₁) d₁
  have e₂ : SmoothOfRelativeDimension n₂ ((a₂ ⁻¹ᵁ W₂).ι ≫ p) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n₂)
      ((isPullback_morphismRestrict a₂ W₂).paste_vert h₂) d₂
  exact relDim_eq_of_mem_of_mem p e₁ e₂ hz₁ hz₂

theorem isPullback_fst_snd {X : Scheme.{0}} (G : Over X) :
    IsPullback (fst G G) (snd G G) (toUnit G) (toUnit G) := by
  exact IsPullback.of_is_product (tensorProductIsBinaryProduct G G) isTerminalTensorUnit

theorem isPullback_mul_snd {X : Scheme.{0}} (G : Over X) [GrpObj G] :
    IsPullback (fst G G * snd G G) (snd G G) (toUnit G) (toUnit G) := by
  refine IsPullback.of_is_product (c := BinaryFan.mk (fst G G * snd G G) (snd G G)) ?_ isTerminalTensorUnit
  refine BinaryFan.IsLimit.mk _ (fun u v => lift (u * v⁻¹) v) ?_ ?_ ?_
  · intro T u v
    simp [comp_mul]
  · intro T u v
    simp
  · intro T u v m h₁ h₂
    simp only [BinaryFan.mk_fst, BinaryFan.mk_snd] at h₁ h₂
    have h₃ : m ≫ fst G G * v = u := by
      rw [← h₂]
      exact (comp_mul m (fst G G) (snd G G)).symm.trans h₁
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simpa using eq_mul_inv_of_mul_eq h₃
    · simpa using h₂

theorem toUnit_left {X : Scheme.{0}} (G : Over X) : (toUnit G).left = G.hom := by
  simpa using Over.w (toUnit G)

theorem reldim_eq_unit {X : Scheme.{0}} (G : Over X) [GrpObj G] {n m : ℕ} {W V : G.left.Opens}
    (dW : SmoothOfRelativeDimension n (W.ι ≫ G.hom)) (dV : SmoothOfRelativeDimension m (V.ι ≫ G.hom))
    (g : G.left) (hg : g ∈ W) (hV : eSec G (G.hom g) ∈ V) : n = m := by
  have h₁ := (isPullback_fst_snd G).map (Over.forget X)
  have h₂ := (isPullback_mul_snd G).map (Over.forget X)
  simp only [Over.forget_map, toUnit_left] at h₁ h₂
  have p₁ : (fst G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) = g := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
    simp
  have p₂ : (fst G G * snd G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) = (η[G]).left (G.hom g) := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, comp_mul, lift_fst, lift_snd, mul_inv_cancel,
      Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply, toUnit_left]
  refine reldim_eq_of_two_pullbacks h₁ h₂ dW dV ((lift (𝟙 G) (𝟙 G)⁻¹).left g) ?_ ?_
  · show (fst G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) ∈ W
    rw [p₁]
    exact hg
  · show (fst G G * snd G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) ∈ V
    rw [p₂]
    unfold eSec at hV
    exact hV

private theorem smoothOfRelativeDimension_of_local {A S : Scheme.{0}} (f : A ⟶ S) (n : ℕ)
    (h : ∀ x : A, ∃ W : A.Opens, x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ f)) :
    SmoothOfRelativeDimension n f := by
  rw [smoothOfRelativeDimension_iff]
  intro x
  obtain ⟨W, hxW, hW⟩ := h x
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := (smoothOfRelativeDimension_iff n (W.ι ≫ f)).1 hW ⟨x, hxW⟩
  have e₁ : W.ι ''ᵁ V ≤ f ⁻¹ᵁ U := by
    rintro _ ⟨v, hv, rfl⟩
    exact e hv
  have e₂ : V ≤ W.ι ⁻¹ᵁ (W.ι ''ᵁ V) := fun v hv => ⟨v, hv, rfl⟩
  have hcomp := Scheme.Hom.appLE_comp_appLE W.ι f U (W.ι ''ᵁ V) V e₁ e₂
  have hiso : W.ι.appLE (W.ι ''ᵁ V) V e₂ = (W.ι.appIso V).hom := (Scheme.Hom.appIso_hom' W.ι V).symm
  have key : f.appLE U (W.ι ''ᵁ V) e₁ = (W.ι ≫ f).appLE U V e ≫ (W.ι.appIso V).inv := by
    rw [← hcomp, hiso, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨U, hU, W.ι ''ᵁ V, hV.image_of_isOpenImmersion W.ι, ⟨⟨x, hxW⟩, hxV, rfl⟩, e₁, ?_⟩
  rw [key, CommRingCat.hom_comp]
  have h0 : RingHom.IsStandardSmoothOfRelativeDimension 0 (W.ι.appIso V).inv.hom :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv (W.ι.appIso V).symm.commRingCatIsoToRingEquiv
  have h1 := h0.comp hstd
  rwa [zero_add] at h1

theorem smoothGrp_relDim : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [Smooth G.hom],
    (∀ q : X, genPt ξ ⤳ q) → ∃ g : ℕ, SmoothOfRelativeDimension g G.hom := by
  intro X Ω _ ξ G _ _ hgen
  obtain ⟨n₀, W₀, hW₀, d₀⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom (eSec G (genPt ξ))
  refine ⟨n₀, smoothOfRelativeDimension_of_local G.hom n₀ fun g => ?_⟩
  obtain ⟨n, W, hgW, dW⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom g
  obtain ⟨m, V, hV, dV⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom (eSec G (G.hom g))
  have h₁ : n = m := reldim_eq_unit G dW dV g hgW hV
  have hsp : eSec G (genPt ξ) ⤳ eSec G (G.hom g) := (hgen (G.hom g)).map (eSec G).base.hom.continuous
  have h₂ : m = n₀ := relDim_eq_of_mem_of_mem G.hom dV d₀ (hsp.mem_open V.isOpen hV) hW₀
  rw [h₁, h₂] at dW
  exact ⟨W, hgW, dW⟩

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionRankBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.MaxTorus

theorem kernel_eq_of_rank_le : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (x : Sp k ⟶ S), (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ τ : TorusExtension Gk, (letI := τ.addCommGroup; Module.finrank ℤ τ.X ≤ Module.finrank ℤ X) → letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X, (t ≫ u).left = p.left ≫ ψ :=
  @PositivityTheory.Xgn.maximal_torus_in_fibre

end GlobalTheory.CompanionTheory.Ar.MaxTorus
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionSplitMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem torus_extension_generic : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z' : Scheme.{0}) [IsIntegral Z'] [AlgebraicGeometry.IsNoetherian Z'], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' → ∀ (G : Over Z') [GrpObj G], IsSemiAbelian G → ∀ (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ τ : TorusExtension ((Over.pullback j).obj G), letI := τ.addCommGroup; ∃ u : splitTorus Z' τ.X ⟶ G, IsMonHom u ∧ ∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' τ.X), t ≫ u = 1 → t = 1 :=
  @PositivityTheory.Xgn.exists_split_torus_extension

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTangentExact
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieExact

theorem ker_fst_isNilpotent {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra R (DualNumber A)] (π : DualNumber A →ₐ[R] A)
    (h : ∀ b, π b = TrivSqZeroExt.fst b) : IsNilpotent (RingHom.ker (π : DualNumber A →+* A)) := by
  refine ⟨2, ?_⟩
  rw [pow_two]
  refine le_bot_iff.mp (Ideal.mul_le.mpr fun a ha b hb => ?_)
  have ha' : TrivSqZeroExt.fst a = 0 := by rw [← h]; exact ha
  have hb' : TrivSqZeroExt.fst b = 0 := by rw [← h]; exact hb
  have : a * b = 0 := by
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, ha', hb']
  simp [this]

theorem exists_lift_dual {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f] (A : Type) [Field A]
    (s : Spec (CommRingCat.of (DualNumber A)) ⟶ S) (x₀ : Spec (CommRingCat.of A) ⟶ X)
    (h : x₀ ≫ f = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ s) :
    ∃ x : Spec (CommRingCat.of (DualNumber A)) ⟶ X,
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ x = x₀ ∧ x ≫ f = s := by
  let π : CommRingCat.of (DualNumber A) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom
  have hloc : IsLocalHom π.hom := ⟨fun b hb => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr hb⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    GlobalTheory.exists_isAffineOpen_pair f (x₀ (IsLocalRing.closedPoint (CommRingCat.of A))) (O := ⊤) trivial
  refine GlobalTheory.exists_lift_of_smooth_of_isAffineOpen f hU hV hVU π s x₀ h
    (GlobalTheory.range_subset_opens_of_isLocalRing s ?_) (GlobalTheory.range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · have e : f (x₀ (IsLocalRing.closedPoint (CommRingCat.of A))) =
        s (Spec.map π (IsLocalRing.closedPoint (CommRingCat.of A))) :=
      congr($h (IsLocalRing.closedPoint (CommRingCat.of A)))
    rw [← Spec_closedPoint (f := π), ← e]
    exact hVU hxV
  · intro R B _ _ _ _ _ _ π' hπ' φ
    have hsurj : Function.Surjective π' := fun a => ⟨TrivSqZeroExt.inl a, by rw [hπ']; rfl⟩
    have hnil := ker_fst_isNilpotent π' (fun b => by rw [hπ']; rfl)
    exact ⟨Algebra.FormallySmooth.liftOfSurjective φ π' hsurj hnil,
      Algebra.FormallySmooth.comp_liftOfSurjective φ π' hsurj hnil⟩

variable {S : Scheme.{0}}

theorem one_comp_hom {M N T : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : T ⟶ M) ≫ f = 1 := by
  simp [Hom.one_def, IsMonHom.one_hom]

noncomputable def zeroSec {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) : Over.mk x ⟶ epsAt x :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)) (by
    simp only [Over.mk_left, Over.mk_hom, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; rfl
    rw [this]; simp)

theorem isTanAt_iff {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (G : Over S) [GrpObj G]
    (v : epsAt x ⟶ G) : IsTanAt G x v ↔ zeroSec x ≫ v = 1 :=
  ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (fun t : Over.mk x ⟶ G => t.left) h⟩

end GlobalTheory.CompanionTheory.Ar.LieExact

open GlobalTheory.CompanionTheory.Ar.LieExact in

theorem GlobalTheory.CompanionTheory.Ar.LieExact.lie_exact_field : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] (τ : TorusExtension G), letI := τ.addCommGroup; letI := τ.grpB; ∀ (A : Type) [Field A] (c : K →+* A), (∀ v : epsAt (spMap c) ⟶ G, IsTanAt G _ v → (v ≫ τ.q = 1 ↔ ∃ w : epsAt (spMap c) ⟶ splitTorus (Sp K) τ.X, IsTanAt _ _ w ∧ w ≫ τ.i = v)) ∧ ∀ w : epsAt (spMap c) ⟶ τ.B, IsTanAt τ.B _ w → ∃ v : epsAt (spMap c) ⟶ G, IsTanAt G _ v ∧ v ≫ τ.q = w := by
  intro K _ G _ τ
  letI := τ.addCommGroup
  letI := τ.grpB
  intro A _ c
  have hq : IsMonHom τ.q := τ.q_hom
  have hi : IsMonHom τ.i := τ.i_hom
  refine ⟨fun v hv => ⟨fun h => ?_, ?_⟩, fun w hw => ?_⟩
  · have sq : v ≫ τ.q = toUnit _ ≫ η := h.trans Hom.one_def
    refine ⟨τ.isKernel.lift v (toUnit _) sq, ?_, τ.isKernel.lift_fst _ _ _⟩
    rw [isTanAt_iff]
    refine τ.isKernel.hom_ext ?_ (toUnit_unique _ _)
    rw [Category.assoc, τ.isKernel.lift_fst, one_comp_hom, (isTanAt_iff _ _ _).mp hv]
  · rintro ⟨w, -, rfl⟩
    rw [Category.assoc, τ.isKernel.w, ← Category.assoc, toUnit_unique (w ≫ toUnit _) (toUnit _),
      Hom.one_def]
  · obtain ⟨hs, -⟩ := GlobalTheory.torusExtension_smooth_geometricallyConnected G τ
    obtain ⟨x, hx1, hx2⟩ := exists_lift_dual τ.q.left A w.left
      (1 : Over.mk (spMap c) ⟶ G).left (by
        have h1 : ((1 : Over.mk (spMap c) ⟶ G) ≫ τ.q).left = (1 : Over.mk (spMap c) ⟶ τ.B).left := by
          rw [one_comp_hom]
        rw [Over.comp_left] at h1
        exact h1.trans hw.symm)
    refine ⟨Over.homMk x ?_, hx1, Over.OverMorphism.ext hx2⟩
    rw [← Over.w τ.q, ← Category.assoc, hx2, Over.w w]
end

