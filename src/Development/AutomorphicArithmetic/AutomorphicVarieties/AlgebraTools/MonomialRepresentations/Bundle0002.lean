import Mathlib

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.IdComp
section
open Polynomial Matrix

private theorem comp_image {G : Type} [TopologicalSpace G] (e : G ≃ₜ G) {Z : Set G}
    (hZ : Z ∈ irreducibleComponents G) : e '' Z ∈ irreducibleComponents G := by
  refine ⟨hZ.1.image e e.continuous.continuousOn, fun y hy hsub => ?_⟩
  have h1 : Z ⊆ e.symm '' y := by
    intro z hz
    exact ⟨e z, hsub ⟨z, hz, rfl⟩, e.symm_apply_apply z⟩
  have h2 := hZ.2 (hy.image e.symm e.symm.continuous.continuousOn) h1
  intro w hw
  exact ⟨e.symm w, h2 ⟨w, hw, rfl⟩, e.apply_symm_apply w⟩

private theorem exists_unique_pt {G : Type} [TopologicalSpace G] [TopologicalSpace.NoetherianSpace G]
    (a : G) : ∃ x : G, ∀ Z ∈ irreducibleComponents G, ∀ W ∈ irreducibleComponents G,
      x ∈ Z → x ∈ W → Z = W := by
  classical
  obtain ⟨Z, hZ, haZ⟩ : ∃ Z ∈ irreducibleComponents G, a ∈ Z :=
    ⟨_, irreducibleComponent_mem_irreducibleComponents a, mem_irreducibleComponent⟩
  have hfin : (irreducibleComponents G \ {Z}).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.diff
  have hnot : ¬ Z ⊆ ⋃₀ (irreducibleComponents G \ {Z}) := by
    intro hsub
    obtain ⟨W, hW, hZW⟩ := (isIrreducible_iff_sUnion_isClosed.1 hZ.1) hfin.toFinset
      (fun W hW => isClosed_of_mem_irreducibleComponents W (hfin.mem_toFinset.1 hW).1)
      (by simpa using hsub)
    rw [hfin.mem_toFinset] at hW
    exact hW.2 (Set.mem_singleton_iff.2 (le_antisymm (hZ.2 hW.1.1 hZW) hZW))
  obtain ⟨x, hxZ, hxn⟩ := Set.not_subset.1 hnot
  have key : ∀ Y ∈ irreducibleComponents G, x ∈ Y → Y = Z := by
    intro Y hY hxY
    by_contra hne
    exact hxn ⟨Y, ⟨hY, hne⟩, hxY⟩
  refine ⟨x, fun Z' hZ' W' hW' hx1 hx2 => ?_⟩
  rw [key Z' hZ' hx1, key W' hW' hx2]

theorem UpperTheory.V.AlgebraTools.idComp :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [TopologicalSpace.NoetherianSpace G],
      (∀ g : G, Continuous (fun x => g * x)) → (∀ g : G, Continuous (fun x => x * g)) →
      ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ IsClosed (N : Set G) ∧ IsIrreducible (N : Set G) ∧
        ∀ U : Subgroup G, U.FiniteIndex → (N : Set G) ⊆ closure ((U ⊓ N : Subgroup G) : Set G) := by
  intro G _ _ _ hL hR
  classical
  let hl : G → G ≃ₜ G := fun g =>
    { toFun := fun x => g * x, invFun := fun x => g⁻¹ * x,
      left_inv := fun x => by simp, right_inv := fun x => by simp,
      continuous_toFun := hL g, continuous_invFun := hL g⁻¹ }
  let hr : G → G ≃ₜ G := fun g =>
    { toFun := fun x => x * g, invFun := fun x => x * g⁻¹,
      left_inv := fun x => by simp, right_inv := fun x => by simp,
      continuous_toFun := hR g, continuous_invFun := hR g⁻¹ }
  obtain ⟨x, hx⟩ := exists_unique_pt (1 : G)
  have uniq : ∀ y : G, ∀ Z ∈ irreducibleComponents G, ∀ W ∈ irreducibleComponents G,
      y ∈ Z → y ∈ W → Z = W := by
    intro y Z hZ W hW hyZ hyW
    have hxy : (hl (x * y⁻¹)) y = x := by
      show x * y⁻¹ * y = x
      simp
    have h := hx _ (comp_image (hl (x * y⁻¹)) hZ) _ (comp_image (hl (x * y⁻¹)) hW)
      ⟨y, hyZ, hxy⟩ ⟨y, hyW, hxy⟩
    exact Set.image_injective.2 (hl (x * y⁻¹)).injective h
  obtain ⟨C, hC, h1C⟩ : ∃ C ∈ irreducibleComponents G, (1 : G) ∈ C :=
    ⟨_, irreducibleComponent_mem_irreducibleComponents 1, mem_irreducibleComponent⟩
  let N : Subgroup G :=
    { carrier := C
      one_mem' := h1C
      mul_mem' := fun {a b} ha hb => by
        have e1 : (hl a) '' C = C := uniq a _ (comp_image (hl a) hC) _ hC
          ⟨1, h1C, by show a * 1 = a; simp⟩ ha
        have h2 : a * b ∈ (hl a) '' C := ⟨b, hb, rfl⟩
        rwa [e1] at h2
      inv_mem' := fun {a} ha => by
        have e1 : (hl a⁻¹) '' C = C := uniq 1 _ (comp_image (hl a⁻¹) hC) _ hC
          ⟨a, ha, by show a⁻¹ * a = 1; simp⟩ h1C
        have h2 : a⁻¹ ∈ (hl a⁻¹) '' C := ⟨1, h1C, by show a⁻¹ * 1 = a⁻¹; simp⟩
        rwa [e1] at h2 }
  have hNC : ∀ y, y ∈ N ↔ y ∈ C := fun y => Iff.rfl
  have hfinQ : Finite (G ⧸ N) := by
    let F : G ⧸ N → irreducibleComponents G :=
      Quotient.lift (fun g => (⟨(hl g) '' C, comp_image (hl g) hC⟩ : irreducibleComponents G))
        (by
          intro a b hab
          have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.1 hab
          apply Subtype.ext
          exact uniq b _ (comp_image (hl a) hC) _ (comp_image (hl b) hC)
            ⟨a⁻¹ * b, hab', by show a * (a⁻¹ * b) = b; simp⟩ ⟨1, h1C, by show b * 1 = b; simp⟩)
    have hFinj : Function.Injective F := by
      intro p q hpq
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
      have h := congrArg Subtype.val hpq
      change (hl a) '' C = (hl b) '' C at h
      have hb : b ∈ (hl a) '' C := by
        rw [h]
        exact ⟨1, h1C, by show b * 1 = b; simp⟩
      obtain ⟨c, hc, hcb⟩ := hb
      change a * c = b at hcb
      apply QuotientGroup.eq.2
      rw [← hcb, inv_mul_cancel_left]
      exact hc
    haveI : Finite (irreducibleComponents G) :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
    exact Finite.of_injective F hFinj
  refine ⟨N, ⟨fun n hn g => ?_⟩, Subgroup.finiteIndex_of_finite_quotient,
    isClosed_of_mem_irreducibleComponents C hC, hC.1, fun U hU => ?_⟩
  · have e1 : ((hl g).trans (hr g⁻¹)) '' C = C := uniq 1 _ (comp_image _ hC) _ hC
      ⟨1, h1C, by show g * 1 * g⁻¹ = 1; simp⟩ h1C
    have h2 : g * n * g⁻¹ ∈ ((hl g).trans (hr g⁻¹)) '' C := ⟨n, hn, rfl⟩
    rw [e1] at h2
    exact h2
  · haveI : Finite (G ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
    haveI := Fintype.ofFinite (G ⧸ U)
    let S : G ⧸ U → Set G := fun q => {y | y ∈ C ∧ (y : G ⧸ U) = q}
    obtain ⟨z, hz, hCz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hC.1)
      (Finset.univ.image fun q => closure (S q)) (by simp [isClosed_closure]) (by
        intro y hy
        simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.sUnion_range,
          Set.mem_iUnion]
        exact ⟨(y : G ⧸ U), subset_closure ⟨hy, rfl⟩⟩)
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨n, hnC, hnq⟩ : (S q).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, closure_empty] at hCz
      exact hCz h1C
    have hSsub : S q ⊆ (hl n) '' ((U ⊓ N : Subgroup G) : Set G) := by
      rintro y ⟨hyC, hyq⟩
      refine ⟨n⁻¹ * y, Subgroup.mem_inf.2 ⟨?_, ?_⟩, by show n * (n⁻¹ * y) = y; simp⟩
      · exact QuotientGroup.eq.1 (hnq.trans hyq.symm)
      · exact N.mul_mem (N.inv_mem hnC) hyC
    intro y hy
    have h3 : n * y ∈ closure ((hl n) '' ((U ⊓ N : Subgroup G) : Set G)) :=
      closure_mono hSsub (hCz (N.mul_mem hnC hy))
    rw [← Homeomorph.image_closure] at h3
    obtain ⟨k, hk, hky⟩ := h3
    change n * k = n * y at hky
    rwa [mul_left_cancel hky] at hk
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.MonomialOfComm
section
open Polynomial Matrix

private theorem monomial_eigenbasis {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : A.charpoly.Separable) :
    ∃ (b : Module.Basis (Fin n) K (Fin n → K)) (l : Fin n → K), Function.Injective l ∧
      ∀ i, A *ᵥ b i = l i • b i := by
  classical
  have hnd : A.charpoly.roots.Nodup := Polynomial.nodup_roots hA
  have hcard : A.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, ← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e : A.charpoly.roots.toFinset ≃ Fin n := Finset.equivFinOfCardEq hcard
  let l : Fin n → K := fun i => (e.symm i : K)
  have hl : Function.Injective l := fun i j h => e.symm.injective (Subtype.ext h)
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' A) (l i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    have := (e.symm i).2
    rw [Multiset.mem_toFinset] at this
    exact Polynomial.isRoot_of_mem_roots this
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) l hl v hv
  have hsp : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  refine ⟨Module.Basis.mk hli hsp.ge, l, hl, fun i => ?_⟩
  rw [Module.Basis.mk_apply]
  have := (hv i).apply_eq_smul
  rwa [Matrix.toLin'_apply] at this

private theorem monomial_eigvec {K : Type} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (b : Module.Basis (Fin n) K (Fin n → K)) (l : Fin n → K)
    (hl : Function.Injective l) (hb : ∀ i, A *ᵥ b i = l i • b i) (v : Fin n → K) (c : K)
    (hv : A *ᵥ v = c • v) (j : Fin n) (hj : l j ≠ c) : b.repr v j = 0 := by
  classical
  have h1 : (b.coord j) ∘ₗ (Matrix.toLin' A) = l j • b.coord j := by
    refine b.ext fun i => ?_
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hb, map_smul, LinearMap.smul_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs with h
    · rw [h]
    · simp
  have h2 := LinearMap.congr_fun h1 v
  simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hv, map_smul, LinearMap.smul_apply,
      Module.Basis.coord_apply, smul_eq_mul] at h2
  have h3 : (l j - c) * b.repr v j = 0 := by rw [sub_mul, h2, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hj)

private theorem monomial_eigvec' {K : Type} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (b : Module.Basis (Fin n) K (Fin n → K)) (l : Fin n → K)
    (hl : Function.Injective l) (hb : ∀ i, A *ᵥ b i = l i • b i) (v : Fin n → K)
    (i : Fin n) (hv : A *ᵥ v = l i • v) : ∃ a : K, v = a • b i := by
  classical
  refine ⟨b.repr v i, b.ext_elem fun j => ?_⟩
  by_cases h : i = j
  · subst h; simp
  · rw [monomial_eigvec A b l hl hb v _ hv j (fun h' => h (hl h').symm)]
    simp [h]

theorem UpperTheory.V.AlgebraTools.monomialOfComm :
    ∀ (K G : Type) [Field K] [IsAlgClosed K] [Group G] (n : ℕ) (r : G →* Matrix (Fin n) (Fin n) K), Submodule.span K (Set.range r) = ⊤ →
      ∀ (N : Subgroup G) [N.Normal], (∀ g ∈ N, ∀ h ∈ N, r g * r h = r h * r g) → (∃ u ∈ N, (r u).charpoly.Separable) →
      ∃ (b : Module.Basis (Fin n) K (Fin n → K)) (π : G →* Equiv.Perm (Fin n)), N ≤ π.ker ∧
        (∀ g i, ∃ a : K, r g *ᵥ b i = a • b (π g i)) ∧ ∀ i j, ∃ g, π g i = j := by
  classical
  intro K G _ _ _ n r hspan N hN hcomm ⟨u, hu, hsep⟩
  obtain ⟨b, l, hl, hb⟩ := monomial_eigenbasis (r u) hsep
  have hne : ∀ g i, r g *ᵥ b i ≠ 0 := by
    intro g i h
    have : r g⁻¹ *ᵥ (r g *ᵥ b i) = b i := by
      rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
    rw [h, Matrix.mulVec_zero] at this
    exact b.ne_zero i this.symm
  have hNs : ∀ h ∈ N, ∀ i, ∃ a : K, r h *ᵥ b i = a • b i := by
    intro h hh i
    refine monomial_eigvec' (r u) b l hl hb _ i ?_
    rw [Matrix.mulVec_mulVec, hcomm u hu h hh, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_smul]
  have hex : ∀ g i, ∃ j, ∃ a : K, r g *ᵥ b i = a • b j := by
    intro g i
    obtain ⟨c, hc⟩ := hNs (g⁻¹ * u * g⁻¹⁻¹) (hN.conj_mem u hu g⁻¹) i
    have hv : r u *ᵥ (r g *ᵥ b i) = c • (r g *ᵥ b i) := by
      rw [← Matrix.mulVec_smul, ← hc, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← map_mul,
        ← map_mul]
      congr 2
      group
    by_cases hc' : ∃ j, l j = c
    · obtain ⟨j, rfl⟩ := hc'
      exact ⟨j, monomial_eigvec' (r u) b l hl hb _ j hv⟩
    · exfalso
      apply hne g i
      refine b.ext_elem fun j => ?_
      rw [monomial_eigvec (r u) b l hl hb _ _ hv j (fun h => hc' ⟨j, h⟩)]
      simp
  choose f hf using hex
  have huniq : ∀ g i j (a : K), r g *ᵥ b i = a • b j → f g i = j := by
    intro g i j a h
    obtain ⟨a', ha'⟩ := hf g i
    by_contra hij
    have h1 := congrArg (fun v => b.repr v j) (h.symm.trans ha')
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, hij,
      if_true, if_false, smul_eq_mul, mul_one, mul_zero] at h1
    apply hne g i
    rw [h, h1, zero_smul]
  let F : G →* Function.End (Fin n) :=
    { toFun := f
      map_one' := funext fun i => huniq 1 i i 1 (by simp)
      map_mul' := fun g h => funext fun i => by
        obtain ⟨a, ha⟩ := hf h i
        obtain ⟨a', ha'⟩ := hf g (f h i)
        refine huniq (g * h) i (f g (f h i)) (a * a') ?_
        rw [map_mul, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_smul, ha', smul_smul] }
  have hπ : ∀ g i, F.toHomPerm g i = f g i := fun g i => rfl
  refine ⟨b, F.toHomPerm, ?_, ?_, ?_⟩
  · intro h hh
    rw [MonoidHom.mem_ker]
    ext i
    obtain ⟨a, ha⟩ := hNs h hh i
    rw [hπ, huniq h i i a ha]
    rfl
  · intro g i
    exact hf g i
  · intro i j
    by_contra hno
    push Not at hno
    let φ : Matrix (Fin n) (Fin n) K →ₗ[K] K :=
      { toFun := fun M => b.repr (M *ᵥ b i) j
        map_add' := fun M M' => by simp [Matrix.add_mulVec]
        map_smul' := fun c M => by simp [Matrix.smul_mulVec] }
    have hle : Submodule.span K (Set.range r) ≤ LinearMap.ker φ := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      obtain ⟨a, ha⟩ := hf g i
      have hij : f g i ≠ j := hno g
      change b.repr (r g *ᵥ b i) j = 0
      rw [ha]
      simp [hij]
    have hM : LinearMap.toMatrix' ((b.coord i).smulRight (b j)) ∈ LinearMap.ker φ :=
      hle (hspan ▸ Submodule.mem_top)
    change b.repr (LinearMap.toMatrix' ((b.coord i).smulRight (b j)) *ᵥ b i) j = 0 at hM
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix'] at hM
    simp at hM
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.PermChar
section
open Polynomial Matrix

private theorem UpperTheory.V.AlgebraTools.perm_four_pow_three_or_four :
    ∀ σ : Equiv.Perm (Fin 4), σ ^ 3 = 1 ∨ σ ^ 4 = 1 := by
  set_option maxRecDepth 100000 in
  decide

theorem UpperTheory.V.AlgebraTools.permChar :
    ∀ (G K : Type) [Group G] [Field K] (π : G →* Equiv.Perm (Fin 4)) (χ : G →* Kˣ), π.ker ≤ χ.ker → 0 < orderOf χ ∧ orderOf χ ≤ 4 := by
  intro G K _ _ π χ hker
  have hχ : ∀ g : G, χ g ^ 3 = 1 ∨ χ g ^ 4 = 1 := fun g => by
    rcases UpperTheory.V.AlgebraTools.perm_four_pow_three_or_four (π g) with h | h
    · left
      have hm : g ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, h]
      have hm' := hker hm
      rwa [MonoidHom.mem_ker, map_pow] at hm'
    · right
      have hm : g ^ 4 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, h]
      have hm' := hker hm
      rwa [MonoidHom.mem_ker, map_pow] at hm'
  have hall : (∀ g : G, χ g ^ 3 = 1) ∨ (∀ g : G, χ g ^ 4 = 1) := by
    by_contra hne
    push_neg at hne
    obtain ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩ := hne
    have h4 : χ g ^ 4 = 1 := (hχ g).resolve_left hg
    have h3 : χ g' ^ 3 = 1 := (hχ g').resolve_right hg'
    rcases hχ (g * g') with h | h
    · rw [map_mul, mul_pow, h3, mul_one] at h
      exact hg h
    · rw [map_mul, mul_pow, h4, one_mul] at h
      exact hg' h
  have key : ∀ k, 0 < k → (∀ g : G, χ g ^ k = 1) → 0 < orderOf χ ∧ orderOf χ ≤ k := by
    intro k hk0 h
    have hp : χ ^ k = 1 := MonoidHom.ext fun g => by
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact h g
    exact ⟨orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hk0, hp⟩),
      orderOf_le_of_pow_eq_one hk0 hp⟩
  rcases hall with h | h
  · obtain ⟨a, b⟩ := key 3 (by norm_num) h
    exact ⟨a, b.trans (by norm_num)⟩
  · exact key 4 (by norm_num) h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.RelWeight
section
open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.relWeight :
    ∀ (A : Type) [CommGroup A] (ι : Type) [Fintype ι] (a : ι → A), (∀ i j, i ≠ j → ¬ IsOfFinOrder (a i / a j)) →
      ∃ w : ι → ℤ, Function.Injective w ∧ ∀ m : ι → ℤ, ∏ i, a i ^ m i = 1 → ∑ i, m i * w i = 0 := by
  intro A _ ι _ a ha
  classical
  obtain ⟨P, hP⟩ : ∃ P : (ι → ℤ) → A, ∀ m, P m = ∏ i, a i ^ m i := ⟨_, fun _ => rfl⟩
  have hPadd : ∀ m n, P (m + n) = P m * P n := by
    intro m n
    rw [hP, hP, hP, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.add_apply, _root_.zpow_add]
  have hPsmul : ∀ (c : ℤ) m, P (c • m) = P m ^ c := by
    intro c m
    rw [hP, hP, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, _root_.zpow_mul]
  have hPsub : ∀ m n, P (m - n) = P m / P n := by
    intro m n
    rw [eq_div_iff_mul_eq', ← hPadd, sub_add_cancel]
  have hPe : ∀ i, P (Pi.single i 1) = a i := by
    intro i
    rw [hP]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  let L : Submodule ℤ (ι → ℤ) :=
    { carrier := {m | ∃ k : ℤ, k ≠ 0 ∧ P (k • m) = 1}
      add_mem' := by
        rintro m n ⟨k, hk, hm⟩ ⟨l, hl, hn⟩
        refine ⟨k * l, mul_ne_zero hk hl, ?_⟩
        have e1 : P ((k * l) • m) = 1 := by rw [mul_comm, mul_smul, hPsmul, hm, _root_.one_zpow]
        have e2 : P ((k * l) • n) = 1 := by rw [mul_smul, hPsmul, hn, _root_.one_zpow]
        rw [smul_add, hPadd, e1, e2, one_mul]
      zero_mem' := ⟨1, one_ne_zero, by simp [hP]⟩
      smul_mem' := by
        rintro c m ⟨k, hk, hm⟩
        exact ⟨k, hk, by rw [smul_comm, hPsmul, hm, _root_.one_zpow]⟩ }
  haveI : Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ L) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x hx => by
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective L x
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨k, hk, h⟩ := hx
      by_cases hr : r = 0
      · exact Or.inl hr
      · right
        rw [Submodule.Quotient.mk_eq_zero]
        exact ⟨k * r, mul_ne_zero hk hr, by rw [mul_smul]; exact h⟩
  let q : ι → (ι → ℤ) ⧸ L := fun i => L.mkQ (Pi.single i 1)
  have hq : ∀ i j, i ≠ j → q i - q j ≠ 0 := by
    intro i j hij h
    rw [← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨k, hk, hk1⟩ := h
    apply ha i j hij
    rw [isOfFinOrder_iff_zpow_eq_one]
    refine ⟨k, hk, ?_⟩
    rw [hPsmul, hPsub, hPe, hPe] at hk1
    exact hk1
  have hex : ∃ f : Module.Dual ℤ ((ι → ℤ) ⧸ L), ∀ i j, i ≠ j → f (q i) ≠ f (q j) := by
    by_contra hno
    push_neg at hno
    let s : Finset (ι × ι) := Finset.univ.filter fun x => x.1 ≠ x.2
    let p : ι × ι → Submodule ℤ (Module.Dual ℤ ((ι → ℤ) ⧸ L)) :=
      fun x => LinearMap.ker (Module.Dual.eval ℤ _ (q x.1 - q x.2))
    have hc : ⋃ x ∈ s, (p x : Set (Module.Dual ℤ ((ι → ℤ) ⧸ L))) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro f
      obtain ⟨i, j, hij, h⟩ := hno f
      simp only [Set.mem_iUnion]
      refine ⟨(i, j), by simp [s, hij], ?_⟩
      simp [p, h]
    obtain ⟨⟨i, j⟩, hx, hfi⟩ := Submodule.exists_finiteIndex_of_cover hc
    have hij : i ≠ j := by simpa [s] using hx
    apply hq i j hij
    rw [← Module.forall_dual_apply_eq_zero_iff ℤ]
    intro f
    have h1 := AddSubgroup.nsmul_index_mem (p (i, j)).toAddSubgroup f
    have h2 : ((p (i, j)).toAddSubgroup.index • f) (q i - q j) = 0 := h1
    rw [LinearMap.smul_apply, smul_eq_zero] at h2
    exact h2.resolve_left hfi.index_ne_zero
  obtain ⟨f, hf⟩ := hex
  refine ⟨fun i => f (q i), fun i j h => ?_, fun m hm => ?_⟩
  · by_contra hij
    exact hf i j hij h
  · have hm0 : L.mkQ m = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨1, one_ne_zero, by rw [one_smul, hP]; exact hm⟩
    have hsum : m = ∑ i, m i • (Pi.single i 1 : ι → ℤ) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    have h3 : ∑ i, m i • q i = 0 := by
      rw [← hm0]
      conv_rhs => rw [hsum]
      simp only [q, map_sum, LinearMap.map_smul]
    calc ∑ i, m i * f (q i) = f (∑ i, m i • q i) := by simp [map_sum]
      _ = 0 := by rw [h3, map_zero]
end

