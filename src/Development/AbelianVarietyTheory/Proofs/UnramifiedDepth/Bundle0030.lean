import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0019
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenvectorMemSpanBlockOfBasis
section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem eigenvector_mem_span_block_of_basis : ∀ (K C : Type) [Field K] [Field C] (ι : K →+* C) (O A : Type) [Fintype A] (n : A → ℕ) (d : ℕ) (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C) (u : (Σ a : A, Fin (n a)) → Fin d → K), Function.Injective em → (∀ x q, (M x).mulVec (fun s => ι (u q s)) = em q.1 x • fun s => ι (u q s)) → (∀ z : Fin d → K, ∃! b : (Σ a : A, Fin (n a)) → K, ∀ s, ∑ q, b q * u q s = z s) → ∀ (a : A) (z : Fin d → C), (∀ x, (M x).mulVec z = em a x • z) → ∃ b : Fin (n a) → C, z = ∑ i, b i • fun s => ι (u ⟨a, i⟩ s) := by
  intro K C _ _ ι O A _ n d M em u hem hM hb a z hz
  classical
  let U : Matrix (Σ a : A, Fin (n a)) (Fin d) K := Matrix.of u
  let W : Matrix (Fin d) (Σ a : A, Fin (n a)) K :=
    Matrix.of fun t => (hb (Pi.single t 1)).exists.choose
  have hWU : W * U = 1 := by
    ext t s
    have := (hb (Pi.single t 1)).exists.choose_spec s
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [W, U, Matrix.of_apply]
    rw [this, Pi.single_apply]
    simp [eq_comm]
  have hUW : U * W = 1 := by
    have h1 : U * W * U = U := by rw [Matrix.mul_assoc, hWU, Matrix.mul_one]
    have h2 : (1 : Matrix (Σ a : A, Fin (n a)) (Σ a : A, Fin (n a)) K) * U = U := Matrix.one_mul _
    ext q q'
    have := (hb (u q)).unique (y₁ := (U * W) q)
      (y₂ := (1 : Matrix (Σ a : A, Fin (n a)) (Σ a : A, Fin (n a)) K) q)
      (fun s => by
        have := congrFun (congrFun h1 q) s
        rw [Matrix.mul_apply] at this
        exact this)
      (fun s => by
        have := congrFun (congrFun h2 q) s
        rw [Matrix.mul_apply] at this
        exact this)
    exact congrFun this q'
  have hWU' : W.map ι * U.map ι = 1 := by
    rw [← Matrix.map_mul, hWU, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hUW' : U.map ι * W.map ι = 1 := by
    rw [← Matrix.map_mul, hUW, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hvm : ∀ c : (Σ a : A, Fin (n a)) → C,
      Matrix.vecMul c (U.map ι) = ∑ q, c q • fun s => ι (u q s) := by
    intro c
    funext s
    simp [Matrix.vecMul, dotProduct, U, Finset.sum_apply]
  have hind : ∀ c : (Σ a : A, Fin (n a)) → C,
      (∑ q, c q • fun s => ι (u q s)) = 0 → c = 0 := by
    intro c hc
    rw [← hvm] at hc
    have : Matrix.vecMul (Matrix.vecMul c (U.map ι)) (W.map ι) = c := by
      rw [Matrix.vecMul_vecMul, hUW', Matrix.vecMul_one]
    rw [← this, hc, Matrix.zero_vecMul]
  obtain ⟨c, hc⟩ : ∃ c : (Σ a : A, Fin (n a)) → C, z = ∑ q, c q • fun s => ι (u q s) := by
    refine ⟨Matrix.vecMul z (W.map ι), ?_⟩
    rw [← hvm, Matrix.vecMul_vecMul, hWU', Matrix.vecMul_one]
  have hzero : ∀ q : (Σ a : A, Fin (n a)), q.1 ≠ a → c q = 0 := by
    intro q hq
    by_contra hcq
    apply hq
    apply hem
    funext x
    have h := hz x
    have h3 : (∑ q : (Σ a : A, Fin (n a)), ((em q.1 x - em a x) * c q) • fun s => ι (u q s)) = 0 := by
      have e1 : (M x).mulVec z
          = ∑ q : (Σ a : A, Fin (n a)), (em q.1 x * c q) • fun s => ι (u q s) := by
        rw [hc, Matrix.mulVec_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Matrix.mulVec_smul, hM, smul_smul, mul_comm]
      have e2 : em a x • z
          = ∑ q : (Σ a : A, Fin (n a)), (em a x * c q) • fun s => ι (u q s) := by
        rw [hc, Finset.smul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [smul_smul]
      simp only [sub_mul, sub_smul, Finset.sum_sub_distrib]
      rw [← e1, ← e2, h, sub_self]
    have h4 := congrFun (hind _ h3) q
    simp only [Pi.zero_apply, mul_eq_zero] at h4
    exact sub_eq_zero.mp (h4.resolve_right hcq)
  refine ⟨fun i => c ⟨a, i⟩, ?_⟩
  rw [hc, Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro a' _ ha'
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hzero ⟨a', i⟩ ha', zero_smul]
  · intro h
    exact absurd (Finset.mem_univ a) h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralBasisLinearCoordinates
section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem exists_integral_basis_linear_coordinates :
    ∀ (V K C : Type) [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Field C] [Algebra K C] (R : Subring C), (∀ x : V, algebraMap K C (algebraMap V K x) ∈ R) → ∀ s : Finset C, (∀ x ∈ s, x ∈ R) → ∃ (r : ℕ) (c : Fin r → C) (φ : Fin r → (C →ₗ[K] K)), (∀ j, c j ∈ R) ∧ ∀ x ∈ s, (∀ j, φ j x ∈ (algebraMap V K).range) ∧ x = ∑ j, algebraMap K C (φ j x) * c j := by
  intro V K C _ _ _ _ _ _ _ _ R hR s hs
  classical
  letI : Algebra V C := ((algebraMap K C).comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap V C) :=
    (algebraMap K C).injective.comp (IsFractionRing.injective V K)
  haveI : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 hinj
  let M : Submodule V C := Submodule.span V (s : Set C)
  haveI : Module.Finite V M := Module.Finite.span_of_finite V s.finite_toSet
  haveI : Module.Free V M := inferInstance
  have hMR : ∀ x ∈ M, x ∈ R := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hs x hx
    | zero => exact R.zero_mem
    | add x y _ _ hx hy => exact R.add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def]
      exact R.mul_mem (hR a) hx
  let b := Module.finBasis V M
  let c : Fin (Module.finrank V M) → C := fun j => (b j : C)
  have hcV : LinearIndependent V c :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hcK : LinearIndependent K c := (LinearIndependent.iff_fractionRing V K).1 hcV
  obtain ⟨g, hg⟩ := (Fintype.linearCombination K c).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (by
      exact hcK.fintypeLinearCombination_injective))
  refine ⟨_, c, fun j => (LinearMap.proj j).comp g, fun j => hMR _ (b j).2, ?_⟩
  intro x hx
  have hxM : x ∈ M := Submodule.subset_span hx
  have h1 : x = Fintype.linearCombination K c (fun j => algebraMap V K (b.repr ⟨x, hxM⟩ j)) := by
    have := congrArg Subtype.val (b.sum_repr ⟨x, hxM⟩)
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at this
    rw [Fintype.linearCombination_apply]
    simp only [algebraMap_smul]
    exact this.symm
  have h2 : g x = fun j => algebraMap V K (b.repr ⟨x, hxM⟩ j) := by
    have := LinearMap.congr_fun hg (fun j => algebraMap V K (b.repr ⟨x, hxM⟩ j))
    rw [LinearMap.comp_apply, ← h1] at this
    exact this
  refine ⟨fun j => ⟨b.repr ⟨x, hxM⟩ j, ?_⟩, ?_⟩
  · simp [h2]
  · simp only [LinearMap.comp_apply, LinearMap.proj_apply, h2, ← Algebra.smul_def]
    rw [Fintype.linearCombination_apply] at h1
    exact h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeSubMainTermIntegralLowBidegree
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

private theorem ge_coeff_rename_inl {C : Type} [Field C] (V : VF C) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (F : MvPowerSeries ι C) (μ : ι ⊕ ι' →₀ ℕ)
    (h : ∀ ν : ι →₀ ℕ, ν.degree = ∑ c, μ (Sum.inl c) → V.Ge 0 (MvPowerSeries.coeff ν F)) :
    V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.rename Sum.inl F)) := by
  rw [MvPowerSeries.coeff_rename]
  apply VF.Ge.sum
  intro ν hν
  rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hν
  apply h
  rw [Finsupp.degree_eq_sum, ← hν]
  simp [Finsupp.mapDomain_apply Sum.inl_injective]

private theorem ge_coeff_rename_inr {C : Type} [Field C] (V : VF C) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (F : MvPowerSeries ι' C) (μ : ι ⊕ ι' →₀ ℕ)
    (h : ∀ ν : ι' →₀ ℕ, ν.degree = ∑ c, μ (Sum.inr c) → V.Ge 0 (MvPowerSeries.coeff ν F)) :
    V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.rename Sum.inr F)) := by
  rw [MvPowerSeries.coeff_rename]
  apply VF.Ge.sum
  intro ν hν
  rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hν
  apply h
  rw [Finsupp.degree_eq_sum, ← hν]
  simp [Finsupp.mapDomain_apply Sum.inr_injective]

private theorem constantCoeff_linPull_eq_zero {C : Type} [Field C] {σ ι : Type} [Fintype σ]
    [Fintype ι] (e : ι → σ → C) (F : MvPowerSeries σ C)
    (h : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (linPull e F) = 0 := by
  unfold linPull
  apply MvPowerSeries.constantCoeff_subst_eq_zero
  · exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp)
  · intro x
    simp
  · exact h

private theorem pderiv_inr_mainM_one {C : Type} [Field C] (V : VF C) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (Φ : ι' → ι → C) (b : ι') :
    MvPowerSeries.pderiv C (Sum.inr b) (mainM V 1 Φ) =
      MvPowerSeries.rename Sum.inl ((V.l : C)⁻¹ • ∑ c : ι,
        Φ b c • (MvPowerSeries.X c : MvPowerSeries ι C) ^ V.l) := by
  have hE : expE V.l 1 = 1 := by simp [expE]
  unfold mainM
  rw [hE, pow_one, pow_one]
  simp only [map_smul, map_sum, MvPowerSeries.rename_X, map_pow, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_eq_single b]
  · rw [Derivation.map_smul, Derivation.leibniz, MvPowerSeries.pderiv_X_self, Derivation.leibniz_pow,
      MvPowerSeries.pderiv_X_of_ne Sum.inl_ne_inr]
    simp [mul_comm]
  · intro x _ hx
    rw [Derivation.map_smul, Derivation.leibniz, Derivation.leibniz_pow,
      MvPowerSeries.pderiv_X_of_ne Sum.inl_ne_inr,
      MvPowerSeries.pderiv_X_of_ne (fun h => hx (Sum.inr_injective h))]
    simp
  · intro hb
    exact absurd (Finset.mem_univ b) hb

theorem mPlus_of_good_tangents : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → 1 < d → ∀ (g : Fin 2) (a : ZMod d) (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (N : ℕ) (em : Fin N ↪ I g) (v' : Fin X.n → I (1 - g) → C), (∀ δ, (X.G g).ty (Sum.inl (em δ)) = a) → (∀ δ x, (S g).al (em δ) 1 x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + ((1 : ℕ) : ZMod d) → v' b k = 0) → X.MPlusConcl g a N (fun δ => (S g).tan (em δ)) v' (fun b c => ∑ κ : J g, ∑ k : I (1 - g), -((V.l : C) * (S g).be (em c) 1 κ) * X.pair g κ k * v' b k) := by
  intro C _ V d _ I J _ _ X hAlt hd g a S t hT N em v' hty hal hint hpure μ hμl hμr
  by_cases h0 : ∀ b, μ (Sum.inr b) = 0
  · rw [GlobalTheory.T.coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis _ _ _ _ _ X g a 1 _ _ _ v' _ μ h0]
    exact VF.Ge.zero 0
  simp only [not_forall] at h0
  obtain ⟨b, hb⟩ := h0
  have he_pure : ∀ (c : Fin N) (x : I g), (X.G g).ty (Sum.inl x) ≠ a →
      (fun δ => (S g).tan (em δ)) c x = 0 := by
    intro c x hx
    exact tan_pure (S g) (em c) x (by rw [hty c]; exact hx)
  obtain ⟨γ, hγ, hγeq⟩ := GlobalTheory.T.pderiv_leafGauge_eq_pairing_add_integral C V d I J X hAlt g a 1 odd_one hd S t hT (Fin N) (Fin X.n)
    (fun δ => (S g).tan (em δ)) v' he_pure hint hpure b
  have h91 := GlobalTheory.T.hPullW_upG_twoGroupEmbedding_eq_rename C I g (Fin N) (Fin X.n) (fun δ => (S g).tan (em δ)) v'
  have hsingle : Finsupp.single (Sum.inr b) 1 ≤ μ :=
    Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hb)
  obtain ⟨μ', rfl⟩ : ∃ μ', μ = μ' + Finsupp.single (Sum.inr b) 1 :=
    ⟨μ - Finsupp.single (Sum.inr b) 1, (tsub_add_cancel_of_le hsingle).symm⟩
  have hl' : ∑ c, μ' (Sum.inl c) < V.l ^ 2 :=
    lt_of_le_of_lt (Finset.sum_le_sum fun c _ => by rw [Finsupp.add_apply]; exact Nat.le_add_right _ _) hμl
  have hr' : ∑ b', μ' (Sum.inr b') < V.l :=
    lt_of_le_of_lt (Finset.sum_le_sum fun c _ => by rw [Finsupp.add_apply]; exact Nat.le_add_right _ _) hμr
  have hbl : μ' (Sum.inr b) + 1 < V.l := by
    refine lt_of_le_of_lt ?_ hμr
    have := Finset.single_le_sum (f := fun b' => (μ' + Finsupp.single (Sum.inr b) 1 : Fin N ⊕ Fin X.n →₀ ℕ) (Sum.inr b'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using this
  have hunit : V.v ((μ' (Sum.inr b) : C) + 1) = 0 := by
    have hc : ((μ' (Sum.inr b) : C) + 1) = ((μ' (Sum.inr b) + 1 : ℕ) : C) := by push_cast; ring
    rw [hc]
    exact ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_zero_of_coprime V.v V.v_l
      (Nat.coprime_of_lt_prime (by omega) hbl V.l_prime)
  have hne : ((μ' (Sum.inr b) : C) + 1) ≠ 0 := by
    intro h
    rw [h] at hunit
    simp at hunit
  set Φ : Fin X.n → Fin N → C := fun b c => ∑ κ : J g, ∑ k : I (1 - g),
    -((V.l : C) * (S g).be (em c) 1 κ) * X.pair g κ k * v' b k with hΦ
  set F := X.hM g a 1 (fun δ => (S g).tan (em δ)) v' - mainM V 1 Φ with hF
  have hcoeff : MvPowerSeries.coeff (μ' + Finsupp.single (Sum.inr b) 1) F =
      ((μ' (Sum.inr b) : C) + 1)⁻¹ * MvPowerSeries.coeff μ' (MvPowerSeries.pderiv C (Sum.inr b) F) := by
    rw [MvPowerSeries.coeff_pderiv]
    field_simp
  rw [hcoeff]
  refine VF.Ge.mul_int (inv_unit_int hunit) ?_
  set G : MvPowerSeries (Fin N) C :=
    (∑ κ : J g, (∑ k, X.pair g κ k * v' b k) • linPull (fun δ => (S g).tan (em δ)) ((S g).ze (t g) κ)) -
      (V.l : C)⁻¹ • ∑ c : Fin N, Φ b c • (MvPowerSeries.X c : MvPowerSeries (Fin N) C) ^ V.l with hG
  have hsplit : MvPowerSeries.pderiv C (Sum.inr b) F =
      MvPowerSeries.subst (fun w : WV I => hPullW (upG w.1 (t w.1 w.2))
        (fun c => toW g ((fun δ => (S g).tan (em δ)) c)) (fun b => toW (1 - g) (v' b))) γ +
      MvPowerSeries.rename Sum.inl G := by
    rw [hF, map_sub, hγeq, pderiv_inr_mainM_one V Φ b]
    simp only [h91.1, hG, map_sub, map_sum, map_smul]
    abel
  rw [hsplit, map_add]
  refine VF.Ge.add ?_ ?_
  · have h2 : ∀ j g : Fin 2, j = g ∨ j = 1 - g := by decide
    refine GlobalTheory.T.coeffIntegralOnExponents_subst_of_lower_set C V (Fin N ⊕ Fin X.n) (WV I)
      (fun ν => ∑ c, ν (Sum.inl c) < V.l ^ 2 ∧ ∑ b', ν (Sum.inr b') < V.l) ?_ γ _ hγ ?_ ?_ μ' ⟨hl', hr'⟩
    · intro ν ν' hle hP
      exact ⟨lt_of_le_of_lt (Finset.sum_le_sum fun c _ => hle (Sum.inl c)) hP.1,
        lt_of_le_of_lt (Finset.sum_le_sum fun c _ => hle (Sum.inr c)) hP.2⟩
    · rintro ⟨j, x⟩
      rcases h2 j g with rfl | rfl
      · simp only
        rw [h91.1, MvPowerSeries.constantCoeff_rename]
        exact constantCoeff_linPull_eq_zero _ _ ((hT j).1 x)
      · simp only
        rw [h91.2, MvPowerSeries.constantCoeff_rename]
        exact constantCoeff_linPull_eq_zero _ _ ((hT (1 - g)).1 x)
    · rintro ⟨j, x⟩ ν hP
      rcases h2 j g with rfl | rfl
      · simp only
        rw [h91.1]
        apply ge_coeff_rename_inl V
        intro ν' hν'
        rw [(GlobalTheory.T.coeff_coordinates_good_tangents_lt_sq C V d (I j) (J j) (X.G j) (S j) (t j) (hT j) N em hal ν'
          (by rw [hν']; exact hP.1)).1 x, map_sum]
        apply VF.Ge.sum
        intro δ _
        split_ifs
        · rw [MvPowerSeries.coeff_X]
          split_ifs
          exacts [VF.Ge.one, VF.Ge.zero 0]
        · rw [map_zero]
          exact VF.Ge.zero 0
      · simp only
        rw [h91.2]
        apply ge_coeff_rename_inr V
        intro ν' hν'
        exact GlobalTheory.T.linearSubst_coordinate_integral_of_degree_lt C V d (I (1 - g)) (J (1 - g)) (X.G (1 - g)) (S (1 - g)) (t (1 - g))
          (hT (1 - g)) X.n v' hint ν' (by rw [hν']; exact hP.2) x
  · apply ge_coeff_rename_inl V
    intro ν hν
    have hdeg : ν.degree < V.l ^ 2 := by rw [hν]; exact hl'
    have h19 := (GlobalTheory.T.coeff_coordinates_good_tangents_lt_sq C V d (I g) (J g) (X.G g) (S g) (t g) (hT g) N em hal ν hdeg).2
    have hz : MvPowerSeries.coeff ν G = 0 := by
      rw [hG, map_sub, map_sum]
      simp only [MvPowerSeries.coeff_smul, h19, map_neg, map_sum, hΦ]
      have hL : (V.l : C) ≠ 0 := VF.l_ne_zero
      rw [sub_eq_zero]
      simp only [Finset.mul_sum, Finset.sum_mul, mul_neg, Finset.sum_neg_distrib, neg_mul]
      rw [neg_inj, Finset.sum_comm]
      refine Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun k _ => ?_
      field_simp
    rw [hz]
    exact VF.Ge.zero 0

end GlobalTheory.MainTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MapDofNIterate
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.InvDerCopiesMap

open MvPowerSeries

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

theorem map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv R i f) = pderiv S i (MvPowerSeries.map φ f) := by
  ext m
  simp [coeff_map, coeff_pderiv]

theorem map_ev_axis {d n : ℕ} (b : Fin n) (g : PS R 2 d) :
    MvPowerSeries.map φ (ev (n := n) ![pt R d b, 0] g) =
      ev (n := n) ![pt S d b, 0] (MvPowerSeries.map φ g) := by
  unfold ev
  have h : HasSubst (fun p : Fin 2 × Fin d => (![pt R d b, 0] : Fin 2 → Pt R n d) p.1 p.2) := by
    apply hasSubst_of_constantCoeff_zero
    rintro ⟨j, i⟩
    fin_cases j <;> simp [pt]
  rw [MvPowerSeries.map_subst h]
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> simp [pt]

theorem map_DofN {d n : ℕ} (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (f : PS R n d) :
    MvPowerSeries.map φ (DofN F b u f) =
      DofN (fun i => MvPowerSeries.map φ (F i)) b (fun i => φ (u i)) (MvPowerSeries.map φ f) := by
  simp only [DofN, map_sum, map_mul, map_C, map_ev_axis, map_pderiv]

theorem map_DofN_iterate {d n : ℕ} (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (f : PS R n d) :
    MvPowerSeries.map φ ((DofN F b u)^[k] f) =
      (DofN (fun i => MvPowerSeries.map φ (F i)) b (fun i => φ (u i)))^[k] (MvPowerSeries.map φ f) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_DofN, ih]

theorem map_DmonN {d n : ℕ} (F : Fin d → PS R 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R n d) :
    MvPowerSeries.map φ (DmonN F cp u m f) =
      DmonN (fun i => MvPowerSeries.map φ (F i)) cp (fun l i => φ (u l i)) m (MvPowerSeries.map φ f) := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, List.foldr_cons, map_DofN_iterate, ih]

end GlobalTheory.InvDerCopiesMap

namespace GlobalTheory

theorem dpolyN_map : ∀ (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (d n : ℕ) (F : Fin d → PS S 2 d) (κ : Type) [Fintype κ] (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S) (f : PS S n d), DpolyN (fun i => MvPowerSeries.map ψ (F i)) cp (fun l j => ψ (u l j)) (MvPolynomial.map ψ P) (MvPowerSeries.map ψ f) = MvPowerSeries.map ψ (DpolyN F cp u P f) := by
  intro S S' _ _ ψ d n F κ _ cp u P f
  unfold DpolyN
  rw [Finset.sum_subset (MvPolynomial.support_map_subset ψ P) (fun m _ hm => by
    rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]), map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, MvPowerSeries.map_C, InvDerCopiesMap.map_DmonN, MvPolynomial.coeff_map]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.VVAlgebraMapNonnegDvr
section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem vV_algebraMap_nonneg_dvr (T : CDVR) (x : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr x) := by
  unfold vV valV
  rw [neg_nonneg]
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := T.Fr)
    (IsDiscreteValuationRing.maximalIdeal T.V) x
  by_cases h0 : (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr
      (IsDiscreteValuationRing.maximalIdeal T.V)) (algebraMap T.V T.Fr x) = 0
  · rw [h0, WithZero.log_zero]
  · rw [WithZero.log_le_iff_le_exp h0]
    simpa using h1

theorem nval_eq_of_extension :
    ∀ (T : CDVR) (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l ≠ 0 → v (l : C) = 1 → ∀ (ι : T.Fr →+* C), (∀ x : T.Fr, x ≠ 0 → v (ι x) = (((vV T.V x : ℝ) / (vV T.V ((l : ℕ) : T.Fr) : ℝ) : ℝ) : WithTop ℝ)) → (∀ x : T.V, ((0 : ℝ) : WithTop ℝ) ≤ v (ι (algebraMap T.V T.Fr x))) ∧ ∀ x : T.Fr, nval T.V (vV T.V ((l : ℕ) : T.Fr)).toNat x = (WithBot.some (v (ι x)) : WithBot (WithTop ℝ)) := by
  intro T C _ v l hl hv ι hι
  have hvl : 0 ≤ vV T.V ((l : ℕ) : T.Fr) := by
    have h := vV_algebraMap_nonneg_dvr T (l : T.V)
    rwa [map_natCast] at h
  have hcast : (((vV T.V ((l : ℕ) : T.Fr)).toNat : ℕ) : ℝ) = ((vV T.V ((l : ℕ) : T.Fr) : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hvl]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · by_cases hx : x = 0
    · subst hx
      simp
    · have hx' : algebraMap T.V T.Fr x ≠ 0 := fun h =>
        hx ((IsFractionRing.injective T.V T.Fr) (by rw [h, map_zero]))
      rw [hι _ hx']
      have h1 : (0 : ℝ) ≤ (vV T.V (algebraMap T.V T.Fr x) : ℝ) := by
        exact_mod_cast vV_algebraMap_nonneg_dvr T x
      have h2 : (0 : ℝ) ≤ (vV T.V ((l : ℕ) : T.Fr) : ℝ) := by exact_mod_cast hvl
      exact WithTop.coe_le_coe.mpr (div_nonneg h1 h2)
  · unfold nval
    split_ifs with hx
    · subst hx
      simp only [map_zero, AddValuation.map_zero]
      rfl
    · rw [hι x hx, hcast]
      rfl

end GlobalTheory
end

