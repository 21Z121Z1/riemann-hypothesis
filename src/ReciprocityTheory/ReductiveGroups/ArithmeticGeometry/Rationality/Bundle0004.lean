import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0002
import ReciprocityTheory.SemistableReduction.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.RationalityHolds

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DiscPf
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

theorem disc_bound {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (K₀ : Subfield K) (hres : ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K)) (c : ℤ → K)
    (S : Set K)
    (hc : ∀ t ∈ S,
        Filter.Tendsto (fun n => ‖c n * t ^ n‖) Filter.cofinite (nhds 0) ∧
        ∀ τ ∈ K₀, ‖τ‖ = 1 → ‖∑' n, c n * (t * τ) ^ n‖ ≤ 1)
    (t : K) (htS : t ∈ S) (n : ℤ) : ‖c n‖ * ‖t‖ ^ n ≤ 1 := by
  obtain ⟨hlim, hbd⟩ := hc t htS
  let e := Equiv.funUnique (Fin 1) ℤ
  have key := ReciprocityTheory.MultiplicativeHeights.cauchy_inequality_on_torus K K₀ hres 1 (fun χ => c (χ 0) * t ^ (χ 0)) ?_ ?_ (fun _ => n)
  · simpa [norm_mul, norm_zpow] using key
  · exact (hlim.comp e.injective.tendsto_cofinite :)
  · intro τ hτ
    have h := hbd (τ 0) (hτ 0).1 (hτ 0).2
    unfold ReciprocityTheory.MultiplicativeHeights.torusSum
    have h2 : (fun χ : Fin 1 → ℤ => c (χ 0) * t ^ (χ 0) * ∏ i, τ i ^ χ i) =
        fun χ => (fun m : ℤ => c m * (t * τ 0) ^ m) (e χ) := by
      funext χ
      simp [e, Fin.prod_univ_one, mul_zpow, mul_assoc]
    rw [h2]
    convert h using 2
    exact e.tsum_eq (fun m : ℤ => c m * (t * τ 0) ^ m)

theorem disc_holds : DiscStatement := by
  intro K _ _ _ K₀ hres S hS hdense c b hb hc n
  have hbd : ∀ t ∈ S, ‖c n‖ * ‖t‖ ^ n ≤ 1 := fun t ht => disc_bound K₀ hres c S hc t ht n
  constructor
  · by_contra hlt
    push_neg at hlt
    have hcont : ContinuousAt (fun x : ℝ => ‖c n‖ * x ^ n) 1 :=
      continuousAt_const.mul (continuousAt_zpow₀ (1 : ℝ) n (Or.inl one_ne_zero))
    have hev : ∀ᶠ x in nhds (1 : ℝ), 1 < ‖c n‖ * x ^ n :=
      hcont.eventually (lt_mem_nhds (by simpa using hlt))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set r : ℝ := max (1 / 2) (1 - ε / 2) with hr
    have hr0 : 0 < r := lt_max_of_lt_left (by norm_num)
    have hr1 : r < 1 := max_lt (by norm_num) (by linarith)
    obtain ⟨t, htS, ht⟩ :=
      hdense r hr0 hr1 (min (ε / 2) (1 - r)) (lt_min (by linarith) (by linarith))
    have h1 := hbd t htS
    have h2 := (hS t htS).2
    have hdist : dist ‖t‖ 1 < ε := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith : (0 : ℝ) < 1 - ‖t‖)]
      have h4 := (abs_lt.1 ht).1
      have h5 : min (ε / 2) (1 - r) ≤ ε / 2 := min_le_left _ _
      have h3 : 1 - ε / 2 ≤ r := le_max_right _ _
      linarith
    exact absurd h1 (not_le.2 (hball hdist))
  · intro hn
    by_contra hne
    have hq : 0 < ‖c n‖ := norm_pos_iff.2 hne
    have hm : 0 < -n := by omega
    have hcont : ContinuousAt (fun x : ℝ => x ^ (-n)) 0 :=
      continuousAt_zpow₀ (0 : ℝ) (-n) (Or.inr hm.le)
    have h0 : (fun x : ℝ => x ^ (-n)) 0 = 0 := zero_zpow _ hm.ne'
    have hev : ∀ᶠ x in nhds (0 : ℝ), x ^ (-n) < ‖c n‖ :=
      hcont.eventually (gt_mem_nhds (by rw [h0]; exact hq))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set r : ℝ := min (1 / 2) (ε / 2) with hr
    have hr0 : 0 < r := lt_min (by norm_num) (by linarith)
    have hr1 : r < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    obtain ⟨t, htS, ht⟩ := hdense r hr0 hr1 r hr0
    have htpos := (hS t htS).1
    have hdist : dist ‖t‖ 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
      have h4 := (abs_lt.1 ht).2
      have h5 : r ≤ ε / 2 := min_le_right _ _
      linarith
    have h6 := hball hdist
    have h1 := hbd t htS
    have h7 : ‖t‖ ^ n * ‖t‖ ^ (-n) = 1 := by
      rw [← zpow_add₀ htpos.ne', add_neg_cancel, zpow_zero]
    have h9 : ‖c n‖ ≤ ‖t‖ ^ (-n) := by
      have h10 := mul_le_mul_of_nonneg_right h1 (zpow_pos htpos (-n)).le
      rw [mul_assoc, h7, mul_one, one_mul] at h10
      exact h10
    linarith

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FunKerPf
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

section SlopeTestRemainingChoices

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem galAct_tmul {K₂ : Type*} [Field K₂] [Algebra K K₂] (σ : K₂ ≃ₐ[K] K₂) (a : K₂) (v : V) :
    galAct σ (a ⊗ₜ[K] v) = σ a ⊗ₜ[K] v := rfl

theorem lTensor_mkQ_galAct {K₂ : Type*} [Field K₂] [Algebra K K₂] (U : Submodule K V)
    (σ : K₂ ≃ₐ[K] K₂) (x : K₂ ⊗[K] V) :
    LinearMap.lTensor K₂ U.mkQ (galAct σ x) =
      LinearMap.rTensor (V ⧸ U) σ.toLinearMap (LinearMap.lTensor K₂ U.mkQ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => rfl
  | add y z hy hz => simp only [map_add, hy, hz]

theorem galAct_mem_baseSpan {K₂ : Type*} [Field K₂] [Algebra K K₂] (U : Submodule K V)
    (σ : K₂ ≃ₐ[K] K₂) {x : K₂ ⊗[K] V} (hx : x ∈ baseSpan K₂ U) : galAct σ x ∈ baseSpan K₂ U := by
  rw [mem_baseSpan_iff] at hx ⊢
  rw [lTensor_mkQ_galAct, hx, map_zero]

theorem mem_of_one_tmul_mem_baseSpan (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) {v : V}
    (h : (1 : F) ⊗ₜ[K] v ∈ baseSpan F U) : v ∈ U := by
  rw [mem_baseSpan_iff] at h
  simp only [LinearMap.lTensor_tmul, Submodule.mkQ_apply] at h
  have hinj : Function.Injective (fun q : V ⧸ U => (1 : F) ⊗ₜ[K] q) := by
    have h1 : Function.Injective (LinearMap.rTensor (V ⧸ U) (Algebra.linearMap K F)) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K F).injective
    intro q q' hq
    have : LinearMap.rTensor (V ⧸ U) (Algebra.linearMap K F) ((1 : K) ⊗ₜ[K] q) =
        LinearMap.rTensor (V ⧸ U) (Algebra.linearMap K F) ((1 : K) ⊗ₜ[K] q') := by
      simpa using hq
    have := h1 this
    simpa using congrArg (TensorProduct.lid K (V ⧸ U)) this
  have : (Submodule.Quotient.mk v : V ⧸ U) = 0 := hinj (by simpa using h)
  exact (Submodule.Quotient.mk_eq_zero U).mp this

end SlopeTestRemainingChoices

theorem funKer_holds : FunKerStatement := by
  intro K Ω V _ _ _ _ _ _ _ U _ Wc FF hWle hdef hkill hdet hconj
  classical
  obtain ⟨K₁, hK₁, ρ, c, hc, hdesc, hspan, hfinW, hrank⟩ :=
    rationality_holds K Ω V U Wc FF hWle hdef hkill hdet
  have hK₁def : ∀ i, DefinedOver (c i) K₁ := fun i => (hc i).2
  have hckill : ∀ i, Wc ≤ LinearMap.ker (c i) := fun i => hkill _ (hc i).1
  choose φ hφ using fun i => exists_ratFun (hK₁def i)

  have hDfd : FiniteDimensional K₁ (baseSpan K₁ U) := finiteDimensional_baseSpan K₁ U
  have hEfd : FiniteDimensional Ω (baseSpan Ω U) := finiteDimensional_baseSpan Ω U
  set D := baseSpan K₁ U with hDdef
  set E := baseSpan Ω U with hEdef
  let Φ1 : D →ₗ[K₁] (Fin ρ → K₁) := LinearMap.pi fun i => φ i ∘ₗ D.subtype
  have hdescD : descend K₁ Wc ≤ D := by rw [hdesc]; exact inf_le_left
  have hker1 : LinearMap.ker Φ1 = (descend K₁ Wc).comap D.subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    rw [hdesc, Submodule.mem_inf, Submodule.mem_iInf]
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    constructor
    · intro h
      refine ⟨x.2, fun i => ?_⟩
      rw [← hφ i]
      have := congrFun h i
      simp only [Φ1, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        Pi.zero_apply] at this
      rw [this, map_zero]
    · rintro ⟨-, h⟩
      funext i
      simp only [Φ1, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        Pi.zero_apply]
      apply (algebraMap K₁ Ω).injective
      rw [hφ i, map_zero]; exact h i
  have hfinker : Module.finrank K₁ (LinearMap.ker Φ1) = Module.finrank K₁ (descend K₁ Wc) := by
    rw [hker1]; exact (Submodule.comapSubtypeEquivOfLe hdescD).finrank_eq
  have hsurj1 : LinearMap.range Φ1 = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ1
    rw [hfinker, finrank_baseSpan K₁ U] at h1
    rw [Module.finrank_fin_fun]
    omega
  have hd : ∀ j : Fin ρ, ∃ dj : D, Φ1 dj = Pi.single j 1 := fun j => by
    have : Pi.single j (1 : K₁) ∈ LinearMap.range Φ1 := hsurj1 ▸ Submodule.mem_top
    exact this
  choose d hd using hd
  let ΦΩ : E →ₗ[Ω] (Fin ρ → Ω) := LinearMap.pi fun i => c i ∘ₗ E.subtype
  have hdE : ∀ j, inclT K₁ V (d j : K₁ ⊗[K] V) ∈ E := fun j => inclT_mem_baseSpan K₁ U _ (d j).2
  have hΦd : ∀ j, ΦΩ ⟨_, hdE j⟩ = Pi.single j 1 := by
    intro j
    funext i
    have h := congrFun (hd j) i
    simp only [Φ1, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
    simp only [ΦΩ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [← hφ i, h]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hsurjΩ : LinearMap.range ΦΩ = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun Ω (Fin ρ)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply]
    exact ⟨_, hΦd j⟩
  have hWcE : Wc.comap E.subtype ≤ LinearMap.ker ΦΩ := by
    intro y hy
    rw [LinearMap.mem_ker]
    funext i
    simp only [ΦΩ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      Pi.zero_apply]
    exact hckill i hy
  have hkerΩ : Wc.comap E.subtype = LinearMap.ker ΦΩ := by
    apply Submodule.eq_of_le_of_finrank_eq hWcE
    have h1 := LinearMap.finrank_range_add_finrank_ker ΦΩ
    rw [hsurjΩ, finrank_top, Module.finrank_fin_fun, finrank_baseSpan Ω U] at h1
    rw [(Submodule.comapSubtypeEquivOfLe hWle).finrank_eq, ← hfinW]
    omega
  have hcut : ∀ y ∈ E, (∀ i, c i y = 0) → y ∈ Wc := by
    intro y hy h
    have : (⟨y, hy⟩ : E) ∈ LinearMap.ker ΦΩ := by
      rw [LinearMap.mem_ker]; funext i; exact h i
    rw [← hkerΩ] at this
    exact this

  have : FiniteDimensional K K₁ := hK₁

  let bK := Module.finBasis K K₁
  let q : Polynomial K := ∏ k, minpoly K ((bK k : K₁) : Ω)
  have hint : ∀ k, IsIntegral K ((bK k : K₁) : Ω) := fun k =>
    (IsIntegral.of_finite K (bK k)).map (IsScalarTower.toAlgHom K K₁ Ω)
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => minpoly.ne_zero (hint k)
  let K₂ : IntermediateField K Ω := IntermediateField.adjoin K (q.rootSet Ω)
  have hsplit : (q.map (algebraMap K Ω)).Splits := IsAlgClosed.splits _
  have : Polynomial.IsSplittingField K K₂ q :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have : FiniteDimensional K K₂ := Polynomial.IsSplittingField.finiteDimensional K₂ q
  have : Normal K K₂ := Normal.of_isSplittingField q
  have : Algebra.IsSeparable K K₂ := inferInstance
  have : IsGalois K K₂ := {}
  have hK12 : K₁ ≤ K₂ := by
    intro x hx
    have hxb := (bK.sum_repr ⟨x, hx⟩)
    have hx' : x = ∑ k, bK.repr ⟨x, hx⟩ k • ((bK k : K₁) : Ω) := by
      have := congrArg K₁.val.toLinearMap hxb
      rw [map_sum] at this
      simp only [map_smul] at this
      exact this.symm
    rw [hx']
    refine K₂.toSubalgebra.toSubmodule.sum_mem fun k _ => K₂.toSubalgebra.toSubmodule.smul_mem _ ?_
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    refine ⟨hq0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_finsetProd]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [← Polynomial.aeval_def]; exact minpoly.aeval K _)
  have hK₂def : ∀ i, DefinedOver (c i) K₂ := fun i => (hK₁def i).mono hK12
  have hstab : ∀ σ : K₂ ≃ₐ[K] K₂, ∀ x ∈ descend K₂ Wc, galAct σ x ∈ descend K₂ Wc := by
    intro σ x hx
    have hxW : inclT K₂ V x ∈ Wc := hx
    have hxU : x ∈ baseSpan K₂ U := mem_baseSpan_of_inclT K₂ U x (hWle hxW)
    show inclT K₂ V (galAct σ x) ∈ Wc
    refine hcut _ (inclT_mem_baseSpan K₂ U _ (galAct_mem_baseSpan U σ hxU)) fun i => ?_
    exact hconj (c i) (hc i).1 K₂ inferInstance inferInstance (hK₂def i) σ x hx
  have hGD := galoisDescent_holds K K₂ V (descend K₂ Wc) hstab
  set W := kPoints (descend K₂ Wc) with hWdef
  have hWU : W ≤ U := by
    intro v hv
    have h1 : (1 : K₂) ⊗ₜ[K] v ∈ descend K₂ Wc := hv
    have h2 : inclT K₂ V ((1 : K₂) ⊗ₜ[K] v) ∈ Wc := h1
    exact mem_of_one_tmul_mem_baseSpan K₂ U (mem_baseSpan_of_inclT K₂ U _ (hWle h2))

  let ι : K₁ ⊗[K] V →ₗ[K] K₂ ⊗[K] V :=
    LinearMap.rTensor V (IntermediateField.inclusion hK12).toLinearMap
  have hι : ∀ x, inclT K₂ V (ι x) = inclT K₁ V x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => rfl
    | add y z hy hz => simp only [map_add, hy, hz]
  have hK1W : ∀ x : K₁ ⊗[K] V, inclT K₁ V x ∈ Wc ↔ x ∈ baseSpan K₁ W := by
    intro x
    constructor
    · intro hx
      have h1 : ι x ∈ descend K₂ Wc := by show inclT K₂ V (ι x) ∈ Wc; rw [hι]; exact hx
      rw [hGD] at h1
      have h2 := inclT_mem_baseSpan K₂ W _ h1
      rw [hι] at h2
      exact mem_baseSpan_of_inclT K₁ W x h2
    · intro hx
      have h1 := inclT_mem_baseSpan K₁ W x hx
      rw [← hι] at h1 ⊢
      have h2 : ι x ∈ baseSpan K₂ W := mem_baseSpan_of_inclT K₂ W _ h1
      rw [← hGD] at h2
      exact h2
  have hWc : baseSpan Ω W = Wc := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨w, hw, rfl⟩
      have : (1 : K₂) ⊗ₜ[K] w ∈ descend K₂ Wc := hw
      exact this
    · rw [← hspan]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      exact inclT_mem_baseSpan K₁ W x ((hK1W x).mp hx)
  have hWfd : FiniteDimensional K W := Submodule.finiteDimensional_of_le hWU
  have hdescW : descend K₁ Wc = baseSpan K₁ W := by
    ext x; exact hK1W x
  refine ⟨W, hWU, hWc, K₁, hK₁, ρ, c, hc, fun x hx => ?_, ?_⟩
  · constructor
    · intro h
      have : x ∈ descend K₁ Wc := by
        rw [hdesc, Submodule.mem_inf, Submodule.mem_iInf]
        exact ⟨hx, fun i => h i⟩
      rw [hdescW] at this; exact this
    · intro h i
      have : inclT K₁ V x ∈ Wc := (hK1W x).mpr h
      exact hckill i this
  · rw [← hrank, hdescW, finrank_baseSpan K₁ W]

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.GlobQuotPf
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField

theorem globalQuot_holds : GlobalQuotStatement := by
  intro K _ _ ρ m hdet s β a b B Bfin hs hβ harch hdeg hfin
  classical
  set n : ℝ := (Module.finrank ℚ K : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Module.finrank_pos
  have hsum : ∑ σ : InfinitePlace K, (σ.mult : ℝ) = n := by
    rw [hn]; exact_mod_cast InfinitePlace.sum_mult_eq
  have hord := finite_ordAt (K := K) hdet
  have hsU : (⋃ i, Function.support (s i)).Finite := Set.finite_iUnion hs
  set T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
    (hord.union (hsU.union hβ)).toFinset with hT
  have memT : ∀ w, w ∈ (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => (ordAt v m.det : ℝ) * logN v) ∪
      ((⋃ i, Function.support (s i)) ∪ Function.support β) → w ∈ T := by
    intro w hw; rw [hT, Set.Finite.mem_toFinset]; exact hw
  have e1 : ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (ordAt w m.det : ℝ) * logN w = ∑ w ∈ T, (ordAt w m.det : ℝ) * logN w := by
    apply finsum_eq_sum_of_support_subset
    intro w hw; exact memT w (Or.inl hw)
  have e2 : ∀ i, ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), s i w * logN w = ∑ w ∈ T, s i w * logN w := by
    intro i; apply finsum_eq_sum_of_support_subset
    intro w hw
    simp only [Function.mem_support, ne_eq] at hw
    refine memT w (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨i, fun h => hw ?_⟩)))
    rw [h, zero_mul]
  have e3 : ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), β w * logN w = ∑ w ∈ T, β w * logN w := by
    apply finsum_eq_sum_of_support_subset
    intro w hw
    simp only [Function.mem_support, ne_eq] at hw
    refine memT w (Or.inr (Or.inr fun h => hw ?_))
    rw [h, zero_mul]
  have e0 : ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w =
      ∑ w ∈ T, ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w := by
    apply finsum_eq_sum_of_support_subset
    intro w hw
    simp only [Function.mem_support, ne_eq] at hw
    by_contra hnot
    apply hw
    have h1 : (ordAt w m.det : ℝ) * logN w = 0 := by
      by_contra h; exact hnot (memT w (Or.inl h))
    have h2 : ∀ i, s i w = 0 := fun i => by
      by_contra h; exact hnot (memT w (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨i, h⟩))))
    have h3 : β w = 0 := by
      by_contra h; exact hnot (memT w (Or.inr (Or.inr h)))
    rw [add_mul, add_mul, h1]
    simp [h2, h3]

  have hPF : ∑ w ∈ T, (ordAt w m.det : ℝ) * logN w =
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (σ m.det) := by
    rw [← e1]; exact finsum_ordAt hdet
  have hHad : ∀ σ : InfinitePlace K, Real.log (σ m.det) ≤
      ∑ j, b j σ - ∑ i, a i σ + (ρ : ℝ) / 2 * Real.log ρ := fun σ =>
    log_det_le m hdet σ (fun i => a i σ) (fun j => b j σ) fun i j h => harch σ i j h
  have hsumσ : ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (σ m.det) ≤
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * (∑ j, b j σ - ∑ i, a i σ + (ρ : ℝ) / 2 * Real.log ρ) :=
    Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hHad σ) (Nat.cast_nonneg _)
  have hexp : ∑ σ : InfinitePlace K, (σ.mult : ℝ) * (∑ j, b j σ - ∑ i, a i σ + (ρ : ℝ) / 2 * Real.log ρ) =
      ∑ j, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * b j σ -
        ∑ i, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * a i σ + n * ((ρ : ℝ) / 2 * Real.log ρ) := by
    have c1 : ∑ σ : InfinitePlace K, ∑ j, (σ.mult : ℝ) * b j σ =
        ∑ j, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * b j σ := Finset.sum_comm
    have c2 : ∑ σ : InfinitePlace K, ∑ i, (σ.mult : ℝ) * a i σ =
        ∑ i, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * a i σ := Finset.sum_comm
    have c3 : ∑ σ : InfinitePlace K, (σ.mult : ℝ) * ((ρ : ℝ) / 2 * Real.log ρ) =
        n * ((ρ : ℝ) / 2 * Real.log ρ) := by rw [← Finset.sum_mul, hsum]
    rw [← c1, ← c2, ← c3, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_add, mul_sub, Finset.mul_sum, Finset.mul_sum]

  have hdeg' : ∀ i, ∑ w ∈ T, s i w * logN w - ∑ σ : InfinitePlace K, (σ.mult : ℝ) * a i σ ≤ B i * n := by
    intro i
    have := hdeg i
    rw [e2 i, div_le_iff₀ hnpos] at this
    exact this
  have hdegS : ∑ i, ∑ w ∈ T, s i w * logN w - ∑ i, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * a i σ ≤
      (∑ i, B i) * n := by
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hdeg' i
  have hfin' : ∑ w ∈ T, β w * logN w ≤ Bfin * n := by
    have := hfin
    rw [e3, div_le_iff₀ hnpos] at this
    exact this
  have hfinρ : (ρ : ℝ) * ∑ w ∈ T, β w * logN w ≤ ρ * (Bfin * n) :=
    mul_le_mul_of_nonneg_left hfin' (Nat.cast_nonneg _)

  have hL : ∑ w ∈ T, ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w =
      ∑ w ∈ T, (ordAt w m.det : ℝ) * logN w + ∑ i, ∑ w ∈ T, s i w * logN w +
        ρ * ∑ w ∈ T, β w * logN w := by
    have hw : ∀ w, ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w =
        (ordAt w m.det : ℝ) * logN w + ∑ i, s i w * logN w + ρ * (β w * logN w) := fun w => by
      rw [add_mul, add_mul, Finset.sum_mul]; ring
    rw [Finset.sum_congr rfl fun w _ => hw w, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_comm]
  have hR : (∑ j, (∑ σ : InfinitePlace K, (σ.mult : ℝ) * b j σ) / n) * n =
      ∑ j, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * b j σ := by
    rw [← Finset.sum_div, div_mul_cancel₀ _ hnpos.ne']
  rw [e0, hL, div_le_iff₀ hnpos, add_mul, add_mul, add_mul, hR]
  linarith [hPF, hsumσ, hexp, hdegS, hfinρ]

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreH
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable def detCT {K K₁ V : Type*} [Field K] [NumberField K] [Field K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] {M : Submodule (𝓞 K) V} {ρ : ℕ}
    (c : Fin ρ → Module.Dual K₁ (K₁ ⊗[K] V)) (θ : Fin ρ → M) : K₁ :=
  (Matrix.of fun i j => c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V))).det

noncomputable def nnFun {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁]
    [Algebra K K₁] {ρ : ℕ} (D : K₁) (s : Fin ρ → HeightOneSpectrum (𝓞 K₁) → ℝ)
    (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (∑ᶠ w : {w : HeightOneSpectrum (𝓞 K₁) // LiesOver w la},
      (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * ((ordAt w.1 D : ℝ) + ∑ i, s i w.1)) /
    (Module.finrank K K₁ : ℝ)

def QCoreLocalStatement : Prop :=
  LenDescentStatement → QuotLocalStatement →
  ∀ (K K₁ V : Type) [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → Submodule.span K (M : Set V) = ⊤ →
    ∀ (W : Submodule K V) (θ : Fin (Module.finrank (𝓞 K) (QuotMW M W)) → M),
      Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W = ⊤ →
    ∀ (c : Fin (Module.finrank (𝓞 K) (QuotMW M W)) → Module.Dual K₁ (K₁ ⊗[K] V)),
      (∀ x : K₁ ⊗[K] V, (∀ i, c i x = 0) ↔
        x ∈ Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V))) →
    ∀ (be : HeightOneSpectrum (𝓞 K) → ℝ)
      (s : Fin (Module.finrank (𝓞 K) (QuotMW M W)) → HeightOneSpectrum (𝓞 K₁) → ℝ),
      (∀ la, 0 ≤ be la) → (∀ i, (Function.support (s i)).Finite) →
      (∀ (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la →
        ∀ i, ∀ m ∈ M, c i ((1 : K₁) ⊗ₜ[K] m) ≠ 0 →
          -((w.asIdeal.ramificationIdx (𝓞 K) : ℝ) * be la) ≤
            (ordAt w (c i ((1 : K₁) ⊗ₜ[K] m)) : ℝ) + s i w) →
      detCT c θ ≠ 0 ∧
      ∀ la : HeightOneSpectrum (𝓞 K), ∃ ℓ : ℕ,
        lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
          (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) = ℓ ∧
        (ℓ : ℝ) ≤ nnFun (detCT c θ) s la + (Module.finrank (𝓞 K) (QuotMW M W) : ℝ) * be la

def QCoreGlobalStatement : Prop :=
  ∀ (K K₁ V : Type) [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] (M : Submodule (𝓞 K) V) (ρ : ℕ)
    (θ : Fin ρ → M) (c : Fin ρ → Module.Dual K₁ (K₁ ⊗[K] V)), detCT c θ ≠ 0 →
    ∀ (s : Fin ρ → HeightOneSpectrum (𝓞 K₁) → ℝ), (∀ i, (Function.support (s i)).Finite) →
    ∀ (supN : (K →+* ℂ) → V → ℝ) (a : Fin ρ → InfinitePlace K₁ → ℝ) (Bθ Carch Bdeg : ℝ),
      (∀ τ v, supN ((starRingEnd ℂ).comp τ) v = supN τ v) →
      (∀ j, (∑ τ : K →+* ℂ, Real.log (supN τ ((θ j : M) : V))) / (Fintype.card (K →+* ℂ) : ℝ) ≤ Bθ) →
      (∀ (σ : InfinitePlace K₁) i j, c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V)) ≠ 0 →
        Real.log (σ (c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V)))) + a i σ ≤
          Real.log (supN (σ.embedding.comp (algebraMap K K₁)) ((θ j : M) : V)) + Carch) →
      (∀ i, ((∑ᶠ w, s i w * logN w) - ∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * a i σ) /
          (Module.finrank ℚ K₁ : ℝ) ≤ Bdeg) →
      (Function.support (nnFun (K := K) (detCT c θ) s)).Finite ∧
      (∑ᶠ la : HeightOneSpectrum (𝓞 K), nnFun (K := K) (detCT c θ) s la * logN la) /
          (Module.finrank ℚ K : ℝ) ≤
        (ρ : ℝ) * (Bθ + Carch + Bdeg) + (ρ : ℝ) / 2 * Real.log ρ

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

