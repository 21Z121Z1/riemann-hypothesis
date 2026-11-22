import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLagrangianContainingIsotropicRat
section
open Matrix

namespace GlobalTheory

open Module

theorem exists_lagrangian_containing_isotropic_rat : ∀ (g r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (I : Submodule ℚ (Fin r → ℚ)), r = 2 * g → Mqᵀ = -Mq → Mq.det ≠ 0 → (∀ x ∈ I, ∀ y ∈ I, x ⬝ᵥ Mq *ᵥ y = 0) → ∃ L : Submodule ℚ (Fin r → ℚ), I ≤ L ∧ (∀ x ∈ L, ∀ y ∈ L, x ⬝ᵥ Mq *ᵥ y = 0) ∧ Module.finrank ℚ L = g := by
  classical
  intro g r M I hr hskew hdet hI
  set B : LinearMap.BilinForm ℚ (Fin r → ℚ) := Matrix.toBilin' M with hBdef
  have hB : ∀ v w, B v w = v ⬝ᵥ M *ᵥ w := fun v w => by
    simp [hBdef, Matrix.toBilin'_apply']
  have hskewB : ∀ v w, B v w = - B w v := by
    intro v w
    rw [hB, hB, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hskew, Matrix.neg_mulVec,
      neg_dotProduct, dotProduct_comm]
  have hBalt : ∀ v, B v v = 0 := fun v => by have := hskewB v v; linarith
  have hnd : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' M hdet
  have hIB : ∀ x ∈ I, ∀ y ∈ I, B x y = 0 := fun x hx y hy => by rw [hB]; exact hI x hx y hy
  let P : ℕ → Prop := fun n => ∃ L : Submodule ℚ (Fin r → ℚ), I ≤ L ∧
    (∀ x ∈ L, ∀ y ∈ L, B x y = 0) ∧ finrank ℚ L = n
  have PI : P (finrank ℚ I) := ⟨I, le_rfl, hIB, rfl⟩
  have hIr : finrank ℚ I ≤ r := by simpa using Submodule.finrank_le I
  obtain ⟨L, hIL, hLiso, hLdim⟩ : P (Nat.findGreatest P r) := Nat.findGreatest_spec hIr PI
  have hmax : ∀ v, (∀ l ∈ L, B v l = 0) → v ∈ L := by
    intro v hvL
    by_contra hv
    have hlt : L < L ⊔ Submodule.span ℚ {v} := lt_of_le_of_ne le_sup_left (fun h => hv (by
      rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
    have hiso : ∀ x ∈ L ⊔ Submodule.span ℚ {v}, ∀ y ∈ L ⊔ Submodule.span ℚ {v}, B x y = 0 := by
      intro x hx y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hb'
      have h1 := hLiso a ha a' ha'
      have h2 := hvL a' ha'
      have h3 : B a v = 0 := by rw [hskewB, hvL a ha, neg_zero]
      have h4 := hBalt v
      simp [map_add, map_smul, h1, h2, h3, h4]
    have hP : P (finrank ℚ ↥(L ⊔ Submodule.span ℚ {v})) :=
      ⟨_, hIL.trans le_sup_left, hiso, rfl⟩
    have h5 := Nat.le_findGreatest (by simpa using Submodule.finrank_le (L ⊔ Submodule.span ℚ {v})) hP
    have h6 := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hLo : B.orthogonal L = L := by
    apply le_antisymm
    · intro x hx
      exact hmax x (fun l hl => by rw [hskewB, hx l hl, neg_zero])
    · intro x hx l hl
      exact hLiso l hl x hx
  have hdim := LinearMap.BilinForm.finrank_orthogonal hnd L
  rw [hLo] at hdim
  have hV : finrank ℚ (Fin r → ℚ) = r := by simp
  rw [hV] at hdim
  have hLr : finrank ℚ L ≤ r := by simpa using Submodule.finrank_le L
  refine ⟨L, hIL, fun x hx y hy => by rw [← hB]; exact hLiso x hx y hy, ?_⟩
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLimitSeries
section
namespace GlobalTheory.LimitSeriesPowSmul

theorem mem_pow_smul_top_iff {R : Type} [CommRing R] (p : R) (n : ℕ) (x : R) :
    x ∈ ((Ideal.span {p}) ^ n • (⊤ : Submodule R R)) ↔ p ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem exists_limit_series {R : Type} [CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R]
    (f : ℕ → R) : ∃ (L : R), ∀ (k : ℕ), p ^ k ∣ ∑ i ∈ Finset.range k, p ^ i * f i - L := by
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p})
    (fun k => ∑ i ∈ Finset.range k, p ^ i * f i) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_pow_smul_top_iff, ← Finset.sum_range_add_sum_Ico _ hmn,
        sub_add_cancel_left, dvd_neg]
      refine Finset.dvd_sum fun i hi => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow p (Finset.mem_Ico.mp hi).1) _)
  exact ⟨L, fun k => (mem_pow_smul_top_iff p k _).mp ((SModEq.sub_mem).mp (hL k))⟩

theorem target : ∀ {R : Type} [inst : CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R]
    (f : ℕ → R), ∃ (L : R), ∀ (k : ℕ), p ^ k ∣ ∑ i ∈ Finset.range k, p ^ i * f i - L :=
  by
  intro R _ p _ f
  exact exists_limit_series p f

end GlobalTheory.LimitSeriesPowSmul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinearMapOfGram
section
namespace GlobalTheory.GramLinearMap

theorem gram_comb {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
    {P' : Type} [AddCommGroup P'] [Module ℂ P'] {B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ} {U : Type}
    (f : U → P) (f' : U → P') {c d : ℂ}
    (h : ∀ u v : U, B (f u) (f v) * c = d * B' (f' u) (f' v)) (x y : U →₀ ℂ) :
    B (Finsupp.linearCombination ℂ f x) (Finsupp.linearCombination ℂ f y) * c =
      d * B' (Finsupp.linearCombination ℂ f' x) (Finsupp.linearCombination ℂ f' y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, add_mul, mul_add, h₁, h₂]
  | single u a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, add_mul, mul_add, h₁, h₂]
    | single v b =>
      simp only [Finsupp.linearCombination_single, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      linear_combination (b * (starRingEnd ℂ) a) * h u v

theorem exists_linearMap_of_gram {P : Type} [AddCommGroup P] [Module ℂ P]
    {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
    {P' : Type} [AddCommGroup P'] [Module ℂ P'] {B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ} {U : Type}
    (f : U → P) (f' : U → P') (hB : ∀ y : P, B y y = 0 → y = 0) {c d : ℂ} (hc : c ≠ 0)
    (h : ∀ u v : U, B (f u) (f v) * c = d * B' (f' u) (f' v)) :
    ∃ ψ : P' →ₗ[ℂ] P, ∀ u : U, ψ (f' u) = f u := by
  set T := Finsupp.linearCombination ℂ f with hT
  set T' := Finsupp.linearCombination ℂ f' with hT'
  have hker : ∀ x, T' x = 0 → T x = 0 := by
    intro x hx
    apply hB
    have := gram_comb f f' h x x
    rw [← hT, ← hT', hx] at this
    simpa [hc] using this
  obtain ⟨g, hg⟩ := T'.rangeRestrict.exists_rightInverse_of_surjective T'.range_rangeRestrict
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend (T ∘ₗ g)
  refine ⟨ψ, fun u => ?_⟩
  have h1 : T' (Finsupp.single u 1) = f' u := by simp [hT']
  have h2 : T (Finsupp.single u 1) = f u := by simp [hT]
  let z : LinearMap.range T' := ⟨f' u, _, h1⟩
  have h3 : ψ (f' u) = T (g z) := LinearMap.congr_fun hψ z
  have h4 : T' (g z) = f' u := congrArg Subtype.val (LinearMap.congr_fun hg z)
  have h5 : T (g z - Finsupp.single u 1) = 0 := hker _ (by rw [map_sub, h4, h1, sub_self])
  rw [map_sub, sub_eq_zero] at h5
  rw [h3, h5, h2]

end GlobalTheory.GramLinearMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMatrixBasisLatticeUpToDenominatorNotMem
section
set_option autoImplicit false
noncomputable section

open NumberField IsDedekindDomain Matrix Module
open scoped BigOperators nonZeroDivisors

namespace GlobalTheory.LatticeLocBasis

theorem exists_basis_up_to_fintype {O A E : Type} [CommRing O] [CommRing A] [IsDomain A] [Field E] [Algebra O A]
    [Algebra A E] [Algebra O E] [IsScalarTower O A E] (S : Submonoid O) [IsLocalization S A] [IsFractionRing A E]
    [IsPrincipalIdealRing A] {n : Type} [Fintype n] (L : Submodule O (n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (n → E)) = ⊤) :
    ∃ (s : S) (b : n → n → E), LinearIndependent E b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, (s : O) • w ∈ Submodule.span O (Set.range b) := by
  classical
  set M : Submodule A (n → E) := Submodule.span A (L : Set (n → E)) with hM
  have : Submodule.IsLattice E M :=
    { fg := by
        obtain ⟨s, hs⟩ := hfg
        refine ⟨s, ?_⟩
        rw [hM, ← hs, Submodule.span_span_of_tower]
      span_eq_top := by rw [hM, Submodule.span_span_of_tower, hsp] }
  have hrk : Module.finrank A M = Fintype.card n := by
    simpa using Submodule.IsLattice.finrank_of_pi E M
  let c : Basis n A M := (Module.finBasisOfFinrankEq A M hrk).reindex (Fintype.equivFin n).symm
  have hc : ∀ i, ∃ t : S, (t : O) • (c i : n → E) ∈ L := fun i => by
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S A (L : Set (n → E)) _ (c i).2
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using hc
  let u : n → Aˣ := fun i => (IsLocalization.map_units A (t i)).unit
  let c' : Basis n A M := c.unitsSMul u
  have hc' : ∀ i, (c' i : n → E) = (t i : O) • (c i : n → E) := fun i => by
    simp only [c', Basis.unitsSMul_apply, u, Units.smul_def, IsUnit.unit_spec, algebraMap_smul,
      Submodule.coe_smul_of_tower]
  let b : n → n → E := fun i => (c' i : n → E)
  have hli : LinearIndependent E b := by
    have h : b = c'.extendOfIsLattice E := funext fun i => by simp [b]
    rw [h]
    exact (c'.extendOfIsLattice E).linearIndependent
  have hspanA : Submodule.span A (Set.range b) = M := by
    have : Set.range b = M.subtype '' Set.range c' := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, c'.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hw : ∀ w ∈ L, ∃ r : S, (r : O) • w ∈ Submodule.span O (Set.range b) := fun w hw => by
    obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span S A (Set.range b) w
      (hspanA ▸ Submodule.subset_span hw)
    exact ⟨r, hr⟩
  obtain ⟨G, hG⟩ := hfg
  choose! r hr using hw
  refine ⟨∏ x ∈ G, r x, b, hli, fun i => by simpa only [b, hc'] using ht i, fun w hw => ?_⟩
  rw [← hG] at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ G := hy
    rw [← Finset.prod_erase_mul G r hy', Submonoid.coe_mul, mul_smul]
    exact Submodule.smul_mem _ _ (hr y (hG ▸ Submodule.subset_span hy))
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy

theorem exists_matrix_up_to_notMem : ∀ (K : Type) [Field K] [NumberField K] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule (𝓞 K) (n → K)) (𝔭 : HeightOneSpectrum (𝓞 K)), L.FG → Submodule.span K (L : Set (n → K)) = ⊤ → ∃ g : Matrix n n K, IsUnit g.det ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ x ∈ L, ∀ i, (t : K) * (g⁻¹ *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ j, (t : K) • (fun i => g i j) ∈ L := by
  intro K _ _ n _ _ L 𝔭 hfg hsp
  have hp := 𝔭.isPrime
  have hS : 𝔭.asIdeal.primeCompl ≤ (𝓞 K)⁰ := Ideal.primeCompl_le_nonZeroDivisors _
  let A := Localization.subalgebra K 𝔭.asIdeal.primeCompl hS
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) 𝔭.ne_bot A
  obtain ⟨⟨s, hs⟩, b, hli, hb, hw⟩ := exists_basis_up_to_fintype (A := A) 𝔭.asIdeal.primeCompl L hfg hsp
  let g : Matrix n n K := Matrix.of fun i j => b j i
  have hcol : g.col = b := by funext j i; rfl
  have hunit : IsUnit g := Matrix.linearIndependent_cols_iff_isUnit.1 (hcol ▸ hli)
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  refine ⟨g, hdet, s, hs, ?_, ?_⟩
  · intro x hx i
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hw x hx)
    have hg : g *ᵥ (fun i => algebraMap (𝓞 K) K (a i)) = (s : K) • x := by
      have : (s : K) • x = s • x := algebraMap_smul K s x
      rw [this]
      change _ = ((⟨s, hs⟩ : 𝔭.asIdeal.primeCompl) : 𝓞 K) • x
      rw [← ha]
      funext i
      simp only [Matrix.mulVec, dotProduct, g, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    have h2 : (s : K) • (g⁻¹ *ᵥ x) = fun i => algebraMap (𝓞 K) K (a i) := by
      rw [← Matrix.mulVec_smul, ← hg, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    exact ⟨a i, (congrFun h2 i).symm⟩
  · intro j
    have : (s : K) • (fun i => g i j) = s • b j := algebraMap_smul K s (b j)
    rw [this]
    exact L.smul_mem _ (hb j)

end GlobalTheory.LatticeLocBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemPairingEqSingleNonradical
section
open Matrix

namespace GlobalTheory

theorem dualV_pairing_exists : ∀ (r g rk : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)) (ε : Fin g → Fin r → ℚ), Mqᵀ = -Mq → LinearIndependent ℚ ε → (∀ i : Fin g, i.val < rk → ∀ w ∈ V, ε i ⬝ᵥ Mq *ᵥ w = 0) → (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → y ∈ Submodule.span ℚ (ε '' {i | i.val < rk})) → ∀ j : Fin g, rk ≤ j.val → ∃ x ∈ V, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0 := by
  intro r g rk Mq V ε hskew hli horth hperp j hj
  have skew : ∀ x y : Fin r → ℚ, x ⬝ᵥ Mq *ᵥ y = -(y ⬝ᵥ Mq *ᵥ x) := by
    intro x y
    rw [dotProduct_mulVec x Mq y, dotProduct_comm y, ← vecMul_transpose, hskew, vecMul_neg,
      neg_dotProduct, neg_neg]
  let Φ : (Fin r → ℚ) →ₗ[ℚ] (Fin g → ℚ) :=
    { toFun := fun x i => x ⬝ᵥ Mq *ᵥ ε i
      map_add' := by intro x y; funext i; simp [add_dotProduct]
      map_smul' := by intro c x; funext i; simp [smul_dotProduct] }
  have hΦ : ∀ x i, Φ x i = x ⬝ᵥ Mq *ᵥ ε i := fun _ _ => rfl
  suffices h : Pi.single j (1 : ℚ) ∈ V.map Φ by
    obtain ⟨x, hx, hxe⟩ := h
    refine ⟨x, hx, fun i => ?_⟩
    rw [← hΦ, hxe, Pi.single_apply]
  by_contra hnot
  obtain ⟨f, hfj, hfS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hf0 : ∀ s ∈ V.map Φ, f s = 0 := by
    intro s hs
    have : f s ∈ (V.map Φ).map f := Submodule.mem_map_of_mem hs
    rw [hfS] at this
    simpa using this
  set a : Fin g → ℚ := fun i => f (Pi.single i 1) with ha
  have hfsum : ∀ s : Fin g → ℚ, f s = ∑ i, a i * s i := by
    intro s
    conv_lhs => rw [pi_eq_sum_univ s]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    congr 1
    simp only [ha]
    congr 1
    funext k
    simp [Pi.single_apply, eq_comm]
  set a' : Fin g → ℚ := fun i => if rk ≤ i.val then a i else 0 with ha'
  have hΦlow : ∀ w ∈ V, ∀ i : Fin g, i.val < rk → Φ w i = 0 := by
    intro w hw i hi
    rw [hΦ, skew, horth i hi w hw, neg_zero]
  have hsum' : ∀ w ∈ V, ∑ i, a' i * Φ w i = 0 := by
    intro w hw
    have h1 : ∑ i, a' i * Φ w i = ∑ i, a i * Φ w i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : rk ≤ i.val
      · simp [ha', hi]
      · simp [ha', hi, hΦlow w hw i (by omega)]
    rw [h1, ← hfsum]
    exact hf0 _ (Submodule.mem_map_of_mem hw)
  set e : Fin r → ℚ := ∑ i, a' i • ε i with he
  have heV : ∀ w ∈ V, e ⬝ᵥ Mq *ᵥ w = 0 := by
    intro w hw
    rw [he, sum_dotProduct]
    have : ∑ i, (a' i • ε i) ⬝ᵥ Mq *ᵥ w = -∑ i, a' i * Φ w i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_dotProduct, smul_eq_mul, hΦ, skew w, mul_neg, neg_neg]
    rw [this, hsum' w hw, neg_zero]
  have hespan := hperp e heV
  rw [Finsupp.mem_span_image_iff_linearCombination] at hespan
  obtain ⟨l, hl, hc⟩ := hespan
  let c' : Fin g → ℚ := fun i => l i
  have hc' : ∑ i, c' i • ε i = e := by
    rw [← hc, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp
  have hzero : ∑ i, (a' i - c' i) • ε i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hc', he, sub_self]
  have := Fintype.linearIndependent_iff.mp hli _ hzero j
  have hcj : c' j = 0 := (Finsupp.mem_supported' ℚ l).mp hl j (by simp; omega)
  have haj : a' j = a j := by simp [ha', hj]
  rw [hcj, haj, sub_zero] at this
  exact hfj this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulEqInteger
section
namespace GlobalTheory.MulEqIntegerExists

open NumberField

theorem exists_mul_eq_integer {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ a b : RingOfIntegers E, b ≠ 0 ∧ (algebraMap (RingOfIntegers E) E b) * c
      = algebraMap (RingOfIntegers E) E a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨a, b, hb0, ?_⟩
  have : algebraMap (RingOfIntegers E) E b ≠ 0 :=
    fun h => hb0 (IsFractionRing.injective (RingOfIntegers E) E (by rw [h, map_zero]))
  rw [mul_div_assoc', mul_div_cancel_left₀ _ this]

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ ν : RingOfIntegers E, ν ≠ 0 ∧ ν • y ∈ L := by
  have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem b hax
    · rw [mul_smul]; exact L.smul_mem a hbz
  | smul c x _ hx =>
    obtain ⟨ν, hν, hνx⟩ := hx
    obtain ⟨a, b, hb, hab⟩ := exists_mul_eq_integer c
    refine ⟨b * ν, mul_ne_zero hb hν, ?_⟩
    have h : (b * ν) • (c • x) = a • (ν • x) := by
      rw [← algebraMap_smul E (b * ν), ← algebraMap_smul E a, ← algebraMap_smul E ν,
        smul_smul, smul_smul, map_mul, ← hab]
      congr 1
      ring
    rw [h]
    exact L.smul_mem a hνx

end GlobalTheory.MulEqIntegerExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulEqInteger
section
universe u_1 u_2

namespace GlobalTheory.NatMulIntegerMultiple

open NumberField

theorem exists_nat_mul_eq_integer {K : Type*} [Field K] [NumberField K] (k : K) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : 𝓞 K, (n : K) * k = algebraMap (𝓞 K) K a := by
  have halg : IsAlgebraic ℤ k :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic k)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨n, by rintro rfl; exact hy rfl, ⟨(n : K) * k, ?_⟩, rfl⟩
    have : (n : K) * k = (n : ℤ) • k := by rw [zsmul_eq_mul]; push_cast; rfl
    rw [this]; exact hint
  · refine ⟨n, by rintro rfl; exact hy rfl, ⟨(n : K) * k, ?_⟩, rfl⟩
    have : (n : K) * k = -((-(n : ℤ)) • k) := by rw [zsmul_eq_mul]; push_cast; ring
    rw [this]; exact hint.neg

theorem exists_nsmul_mem {K : Type*} {V : Type*} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) :
    ∀ x ∈ Submodule.span K (L : Set V), ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => exact ⟨1, one_ne_zero, by simpa using h⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨n, hn, hny⟩ := hy
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    rw [smul_add]
    have e1 : (m * n) • x = n • (m • x) := by rw [mul_nsmul]
    have e2 : (m * n) • y = m • (n • y) := by rw [mul_comm, mul_nsmul]
    rw [e1, e2]
    exact L.add_mem (L.nsmul_mem hmx n) (L.nsmul_mem hny m)
  | smul c x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, a, ha⟩ := exists_nat_mul_eq_integer c
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have : (m * n) • (c • x) = a • (n • x) := by
      calc (m * n) • (c • x) = ((m : K) * c) • (n • x) := by
            rw [← Nat.cast_smul_eq_nsmul K (m * n), ← Nat.cast_smul_eq_nsmul K n, smul_smul, smul_smul]
            push_cast; ring_nf
        _ = algebraMap (𝓞 K) K a • (n • x) := by rw [ha]
        _ = a • (n • x) := algebraMap_smul K a (n • x)
    rw [this]; exact L.smul_mem a hnx

theorem main : ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    ∀ x ∈ Submodule.span K (↑L : Set V), ∃ (n : ℕ), n ≠ (0 : ℕ) ∧ n • x ∈ L :=
  fun L => exists_nsmul_mem L

end GlobalTheory.NatMulIntegerMultiple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulIntegral
section
namespace GlobalTheory.NatMulIntegralExists

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by
  have hz : IsAlgebraic ℤ a := IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ a)
  obtain ⟨y, hy, hint⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact hint.neg

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E)),
    Submodule.span E (↑Λ : Set (Fin r → E)) = ⊤ →
    ∀ (w : Fin r → E), ∃ (k : ℕ), (0 : ℕ) < k ∧ (↑k : E) • w ∈ Λ := by
  intro E _ _ r Λ hspan w
  have hw : w ∈ Submodule.span E (↑Λ : Set (Fin r → E)) := by rw [hspan]; trivial

  have hnat : ∀ (n : ℕ) (v : Fin r → E), v ∈ Λ → (n : E) • v ∈ Λ := by
    intro n v hv
    rw [Nat.cast_smul_eq_nsmul]
    exact Λ.nsmul_mem hv n
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k₁, hk₁, h₁⟩ := hx
    obtain ⟨k₂, hk₂, h₂⟩ := hy
    refine ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, ?_⟩
    have e : ((k₁ * k₂ : ℕ) : E) • (x + y) = (k₂ : E) • ((k₁ : E) • x) + (k₁ : E) • ((k₂ : E) • y) := by
      rw [smul_add, smul_smul, smul_smul]; push_cast; ring_nf
    rw [e]
    exact Λ.add_mem (hnat _ _ h₁) (hnat _ _ h₂)
  | smul a x _ hx =>
    obtain ⟨k, hk, h⟩ := hx
    obtain ⟨d, hd, hint⟩ := exists_nat_mul_integral a
    refine ⟨d * k, Nat.mul_pos hd hk, ?_⟩
    let c : NumberField.RingOfIntegers E := ⟨(d : E) * a, hint⟩
    have e : ((d * k : ℕ) : E) • (a • x) = c • ((k : E) • x) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Algebra.smul_def]
      change _ = ((d : E) * a) * _
      push_cast; ring
    rw [e]
    exact Λ.smul_mem c h

end GlobalTheory.NatMulIntegralExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralOfFiniteBaseChangeImage
section
open TensorProduct

namespace GlobalTheory

theorem integral_of_finite_base_change_image : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C] (φ : U ⊗[T] C →+* L ⊗[F] K), (∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) → ∀ (ω : L ⊗[F] K) (p : Polynomial (U ⊗[T] C)), p.Monic → p.eval₂ φ ω = 0 → IsIntegral U ω := by
  intro T U C F K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ hφ ω p hp h
  letI : Algebra (U ⊗[T] C) (L ⊗[F] K) := φ.toAlgebra
  have hmap : algebraMap (U ⊗[T] C) (L ⊗[F] K) = φ := rfl
  haveI : IsScalarTower U (U ⊗[T] C) (L ⊗[F] K) := by
    refine IsScalarTower.of_algebraMap_eq fun u => ?_
    rw [hmap]
    change algebraMap U (L ⊗[F] K) u = φ (u ⊗ₜ 1)
    rw [hφ, map_one]
    rfl
  have hint : IsIntegral (U ⊗[T] C) ω := ⟨p, hp, h⟩
  haveI : Algebra.IsIntegral U (U ⊗[T] C) := inferInstance
  exact isIntegral_trans ω hint

end GlobalTheory
end

