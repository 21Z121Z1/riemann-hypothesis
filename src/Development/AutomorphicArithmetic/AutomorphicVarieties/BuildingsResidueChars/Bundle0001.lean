import Mathlib

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAutomorphicFunctionWithValuesOnCosetReps
section
theorem UpperTheory.exists_automorphic_function_with_values_on_coset_reps :
    ∀ (Γ G K A M ι : Type) [Group Γ] [Group G] [Group K] [CommRing A] [AddCommGroup M] [Module A M] (gl : Γ →* G) (j : K →* G) (ρ : Representation A K M) (x : ι → G), (∀ g, ∃ γ i k, g = gl γ * x i * j k) → (∀ i i' γ k, x i' = gl γ * x i * j k → i = i') → (∀ i γ k, gl γ * x i = x i * j k → ρ k = 1) → ∀ v : ι → M, ∃ Φ : G → M, (∀ γ g, Φ (gl γ * g) = Φ g) ∧ (∀ g k, Φ (g * j k) = ρ k⁻¹ (Φ g)) ∧ ∀ i, Φ (x i) = v i := by
  intro Γ G K A M ι _ _ _ _ _ _ gl j ρ x hcov huniq hstab v
  have key : ∀ γ i k γ' i' k', gl γ * x i * j k = gl γ' * x i' * j k' →
      i = i' ∧ ρ k⁻¹ (v i) = ρ k'⁻¹ (v i') := by
    intro γ i k γ' i' k' h
    have e : x i' = gl (γ'⁻¹ * γ) * x i * j (k * k'⁻¹) := by
      calc x i' = (gl γ')⁻¹ * (gl γ' * x i' * j k') * (j k')⁻¹ := by group
        _ = (gl γ')⁻¹ * (gl γ * x i * j k) * (j k')⁻¹ := by rw [h]
        _ = gl (γ'⁻¹ * γ) * x i * j (k * k'⁻¹) := by
          simp only [map_mul, map_inv]
          group
    have hii : i = i' := huniq i i' _ _ e
    subst hii
    refine ⟨rfl, ?_⟩
    have e2 : gl (γ'⁻¹ * γ) * x i = x i * j (k' * k⁻¹) := by
      calc gl (γ'⁻¹ * γ) * x i = (gl (γ'⁻¹ * γ) * x i * j (k * k'⁻¹)) * (j (k * k'⁻¹))⁻¹ := by group
        _ = x i * j (k' * k⁻¹) := by
          rw [← e]
          simp only [map_mul, map_inv]
          group
    have hρ : ρ (k' * k⁻¹) = 1 := hstab i _ _ e2
    have : ρ k⁻¹ = ρ k'⁻¹ := by
      calc ρ k⁻¹ = ρ (k'⁻¹ * (k' * k⁻¹)) := by group
        _ = ρ k'⁻¹ * ρ (k' * k⁻¹) := map_mul _ _ _
        _ = ρ k'⁻¹ := by rw [hρ, mul_one]
    rw [this]
  choose γf iF kF hg using hcov
  refine ⟨fun g => ρ (kF g)⁻¹ (v (iF g)), ?_, ?_, ?_⟩
  · intro γ g
    have h : gl (γf (gl γ * g)) * x (iF (gl γ * g)) * j (kF (gl γ * g)) =
        gl (γ * γf g) * x (iF g) * j (kF g) := by
      rw [← hg (gl γ * g)]
      conv_lhs => rw [hg g]
      simp only [map_mul, mul_assoc]
    exact (key _ _ _ _ _ _ h).2
  · intro g k
    have h : gl (γf (g * j k)) * x (iF (g * j k)) * j (kF (g * j k)) =
        gl (γf g) * x (iF g) * j (kF g * k) := by
      rw [← hg (g * j k)]
      conv_lhs => rw [hg g]
      simp only [map_mul, mul_assoc]
    dsimp only
    rw [(key _ _ _ _ _ _ h).2, mul_inv_rev, map_mul]
    rfl
  · intro i
    have h : gl (γf (x i)) * x (iF (x i)) * j (kF (x i)) = gl 1 * x i * j 1 := by
      rw [← hg (x i), map_one, map_one, one_mul, mul_one]
    dsimp only
    rw [(key _ _ _ _ _ _ h).2, inv_one, map_one]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsEigenvectorOfRoot
section
open Polynomial

theorem UpperTheory.exists_eigenvector_of_root :
    ∀ {L C D W : Type} [Field L] [Field C] [AddCommGroup D] [Module L D] [FiniteDimensional L D] [AddCommGroup W] [Module C W] [FiniteDimensional C W] (s : L →+* C) (j : D →+ W) (S : Module.End L D) (T : Module.End C W), (∀ (a : L) (x : D), j (a • x) = s a • j x) → Submodule.span C (Set.range j) = ⊤ → (∀ x, T (j x) = j (S x)) → ∀ (q : L[X]) (b : C), b ∈ T.charpoly.roots → q.eval₂ s b = 0 → ∃ x : D, x ≠ 0 ∧ aeval S q x = 0 := by
  intro L C D W _ _ _ _ _ _ _ _ s j S T hj hspan hT q b hb hq
  by_contra hcon
  have hinj : Function.Injective (aeval S q) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    exact hcon ⟨x, h0, hx⟩
  have hsurj : Function.Surjective (aeval S q) := LinearMap.injective_iff_surjective.mp hinj
  have hpow : ∀ (n : ℕ) (x : D), (T ^ n) (j x) = j ((S ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hT, ih]
  have hcomm : ∀ (p : L[X]) (x : D), aeval T (p.map s) (j x) = j (aeval S p x) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p r hp hr =>
      intro x
      simp only [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hr]
    | monomial n a =>
      intro x
      rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
        Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, hj, hpow]
  have hsurj' : Function.Surjective (aeval T (q.map s)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨j x, hcomm q x⟩
  have hinj' : Function.Injective (aeval T (q.map s)) :=
    LinearMap.injective_iff_surjective.mpr hsurj'
  have hroot : T.charpoly.IsRoot b := (mem_roots'.mp hb).2
  have hev : T.HasEigenvalue b := (Module.End.hasEigenvalue_iff_isRoot_charpoly T b).mpr hroot
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q.map s) hv
  rw [eval_map, hq, zero_smul] at h1
  exact hv.2 (hinj' (by rw [h1, map_zero]))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsEquivariantProjectionsOfSumIrreducible
section
open scoped MonoidAlgebra

private theorem ss_proj {R V : Type} [Ring R] [AddCommGroup V] [Module R V]
    [IsSemisimpleModule R V] (s : Finset V) :
    ∃ (κ : Type) (_ : Fintype κ) (S : κ → Submodule R V) (P : κ → V →ₗ[R] V),
      (∀ i, IsAtom (S i)) ∧ (∀ i w, P i w ∈ S i) ∧ ∀ w ∈ s, ∑ i, P i w = w := by
  classical
  obtain ⟨t, e, -, ht⟩ := IsSemisimpleModule.exists_linearEquiv_dfinsupp R V
  let K : Finset t := s.biUnion fun w => (e w).support
  let Q : t → V →ₗ[R] V := fun m =>
    e.symm.toLinearMap ∘ₗ DFinsupp.lsingle (R := R) (M := fun m : t => m.1) m ∘ₗ
      DFinsupp.lapply (R := R) (M := fun m : t => m.1) m ∘ₗ e.toLinearMap
  let j : (m : t) → (m.1 →ₗ[R] V) := fun m =>
    e.symm.toLinearMap ∘ₗ DFinsupp.lsingle (R := R) (M := fun m : t => m.1) m
  have hj : ∀ m, Function.Injective (j m) := fun m =>
    e.symm.injective.comp (DFinsupp.single_injective (β := fun m : t => m.1) (i := m))
  refine ⟨K, inferInstance, fun i => LinearMap.range (j i.1), fun i => Q i.1, ?_, ?_, ?_⟩
  · intro i
    rw [← isSimpleModule_iff_isAtom]
    haveI := ht i.1
    exact IsSimpleModule.congr (LinearEquiv.ofInjective _ (hj i.1)).symm
  · intro i w
    exact ⟨e w i.1, rfl⟩
  · intro w hw
    rw [Finset.sum_coe_sort K (fun i => Q i w)]
    apply e.injective
    rw [map_sum]
    have h1 : ∀ i, e (Q i w) = DFinsupp.single i (e w i) := fun i => by simp [Q]
    simp_rw [h1]
    ext1 m
    rw [DFinsupp.finset_sum_apply]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb
      exact DFinsupp.single_eq_of_ne hb.symm
    · intro hm
      have : e w m = 0 := by
        by_contra h
        exact hm (Finset.mem_biUnion.mpr ⟨w, hw, DFinsupp.mem_support_iff.mpr h⟩)
      simp [this]

section
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W)

private noncomputable def toSub (U : Submodule ℂ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) :
    Submodule ℂ[H] ρ.asModule where
  carrier := {x | ρ.asModuleEquiv x ∈ U}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact U.add_mem ha hb
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    simp only [Set.mem_setOf_eq] at *
    rw [Representation.asModuleEquiv_map_smul]
    exact ρ.asAlgebraHom_mem_of_forall_mem U hU _ hx c

private theorem mem_toSub (U : Submodule ℂ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) (x : ρ.asModule) :
    x ∈ toSub ρ U hU ↔ ρ.asModuleEquiv x ∈ U := Iff.rfl

private noncomputable def fromSub (N : Submodule ℂ[H] ρ.asModule) : Submodule ℂ W :=
  (N.restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap

private theorem mem_fromSub (N : Submodule ℂ[H] ρ.asModule) (x : W) :
    x ∈ fromSub ρ N ↔ ρ.asModuleEquiv.symm x ∈ N := Iff.rfl

private theorem fromSub_inv (N : Submodule ℂ[H] ρ.asModule) (g : H) (u : W)
    (hu : u ∈ fromSub ρ N) : ρ g u ∈ fromSub ρ N := by
  rw [mem_fromSub] at *
  rw [Representation.asModuleEquiv_symm_map_rho]
  exact N.smul_mem _ hu

private theorem from_to (U : Submodule ℂ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) :
    fromSub ρ (toSub ρ U hU) = U := by
  ext x; simp [mem_fromSub, mem_toSub]

private theorem from_le_iff (A B : Submodule ℂ[H] ρ.asModule) :
    fromSub ρ A ≤ fromSub ρ B ↔ A ≤ B := by
  constructor
  · intro h x hx
    have := @h (ρ.asModuleEquiv x) (by simpa [mem_fromSub] using hx)
    simpa [mem_fromSub] using this
  · intro h x hx
    exact h hx

private theorem from_inj {A B : Submodule ℂ[H] ρ.asModule} (h : fromSub ρ A = fromSub ρ B) :
    A = B :=
  le_antisymm ((from_le_iff ρ A B).mp h.le) ((from_le_iff ρ B A).mp h.ge)

private theorem from_bot : fromSub ρ ⊥ = ⊥ := by
  ext x; simp [mem_fromSub]

private theorem atom_iff (A : Submodule ℂ[H] ρ.asModule) :
    IsAtom A ↔ fromSub ρ A ≠ ⊥ ∧
      ∀ N ≤ fromSub ρ A, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = fromSub ρ A := by
  constructor
  · intro hA
    refine ⟨fun h => hA.1 (from_inj ρ (h.trans (from_bot ρ).symm)), fun N hN hi => ?_⟩
    rw [← from_to ρ N hi] at hN ⊢
    rcases hA.le_iff.mp ((from_le_iff ρ _ _).mp hN) with h | h
    · left; rw [h, from_bot]
    · right; rw [h]
  · rintro ⟨h0, h⟩
    refine ⟨fun hA => h0 (by rw [hA, from_bot]), fun B hB => ?_⟩
    rcases h _ ((from_le_iff ρ _ _).mpr hB.le) (fromSub_inv ρ B) with h | h
    · exact from_inj ρ (h.trans (from_bot ρ).symm)
    · exact absurd (from_inj ρ h) hB.ne

end

theorem UpperTheory.exists_equivariant_projections_of_sum_irreducible :
    ∀ (H W : Type) [Group H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W), (∀ x : W, x ∈ ⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1) → ∀ M : Submodule ℂ W, FiniteDimensional ℂ M → ∃ (κ : Type) (_ : Fintype κ) (U : κ → Submodule ℂ W) (P : κ → W →ₗ[ℂ] W), (∀ i, U i ≠ ⊥ ∧ (∀ g, ∀ u ∈ U i, ρ g u ∈ U i) ∧ ∀ N ≤ U i, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U i) ∧ (∀ i w, P i w ∈ U i) ∧ (∀ i g w, P i (ρ g w) = ρ g (P i w)) ∧ ∀ w ∈ M, ∑ i, P i w = w := by
  intro H W _ _ _ ρ hsum M hM
  classical
  haveI : IsSemisimpleModule ℂ[H] ρ.asModule := by
    apply IsSemisimpleModule.of_sSup_simples_eq_top
    rw [eq_top_iff]
    intro y _
    have hle : (⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧
        ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1) ≤
        fromSub ρ (sSup {m : Submodule ℂ[H] ρ.asModule | IsSimpleModule ℂ[H] m}) := by
      refine iSup_le ?_
      rintro ⟨U, h0, hi, hU⟩
      show U ≤ _
      rw [← from_to ρ U hi, from_le_iff]
      apply le_sSup
      show IsSimpleModule ℂ[H] (toSub ρ U hi)
      rw [isSimpleModule_iff_isAtom, atom_iff, from_to]
      exact ⟨h0, hU⟩
    have := hle (hsum (ρ.asModuleEquiv y))
    simpa [mem_fromSub] using this
  obtain ⟨s, hs⟩ : M.FG := (Submodule.fg_iff_finiteDimensional M).mpr hM
  obtain ⟨κ, hκ, S, P, hS, hP, hsum'⟩ :=
    ss_proj (R := ℂ[H]) (V := ρ.asModule) (s.image ρ.asModuleEquiv.symm)
  let Q : κ → W →ₗ[ℂ] W := fun i =>
    ρ.asModuleEquiv.toLinearMap ∘ₗ (P i).restrictScalars ℂ ∘ₗ ρ.asModuleEquiv.symm.toLinearMap
  have hQ : ∀ i w, Q i w = ρ.asModuleEquiv (P i (ρ.asModuleEquiv.symm w)) := fun _ _ => rfl
  refine ⟨κ, hκ, fun i => fromSub ρ (S i), Q, ?_, ?_, ?_, ?_⟩
  · intro i
    have := (atom_iff ρ (S i)).mp (hS i)
    exact ⟨this.1, fromSub_inv ρ _, this.2⟩
  · intro i w
    rw [mem_fromSub, hQ, LinearEquiv.symm_apply_apply]
    exact hP i _
  · intro i g w
    apply ρ.asModuleEquiv.symm.injective
    rw [Representation.asModuleEquiv_symm_map_rho, hQ, hQ, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, Representation.asModuleEquiv_symm_map_rho, map_smul]
  · intro w hw
    rw [← hs] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      simp_rw [hQ]
      rw [← map_sum, hsum' _ (Finset.mem_image_of_mem _ hx), LinearEquiv.apply_symm_apply]
    | zero => simp
    | add x y _ _ hx hy => simp_rw [map_add]; rw [Finset.sum_add_distrib, hx, hy]
    | smul c x _ hx => simp_rw [map_smul]; rw [← Finset.smul_sum, hx]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFactorDualEmbeddingOfNeZeroTensor
section
open scoped TensorProduct

theorem UpperTheory.exists_factor_dual_embedding_of_ne_zero_tensor :
    ∀ (I : Type) [Finite I] (W : I → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, FiniteDimensional ℂ (W i)] (N : Type) [AddCommGroup N] [Module ℂ N] (Φ : Module.Dual ℂ (⨂[ℂ] i, W i) →ₗ[ℂ] N), Φ ≠ 0 → ∀ y : I, ∃ E : Module.Dual ℂ (W y) →ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] i, W i), Φ ∘ₗ E ≠ 0 ∧ ∀ T : ∀ i, W i →ₗ[ℂ] W i, (∀ i, i ≠ y → T i = LinearMap.id) → ∀ m, E m ∘ₗ PiTensorProduct.map T = E (m ∘ₗ T y) := by
  intro I _ W _ _ _ N _ _ Φ hΦ y
  classical
  have := Fintype.ofFinite I
  have hinv := PiTensorProduct.dualDistrib_dualDistribInvOfBasis_left_inverse
    (R := ℂ) (M := W) (fun i => Module.Free.chooseBasis ℂ (W i))
  have hf : ∃ f : ∀ i, Module.Dual ℂ (W i),
      Φ (PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ f)) ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : Φ ∘ₗ PiTensorProduct.dualDistrib = 0 := by
      apply PiTensorProduct.ext
      ext f
      simpa using h f
    apply hΦ
    rw [← LinearMap.comp_id Φ, ← hinv, ← LinearMap.comp_assoc, h0, LinearMap.zero_comp]
  obtain ⟨f, hf⟩ := hf
  refine ⟨PiTensorProduct.dualDistrib ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap f y, ?_, ?_⟩
  · intro h
    apply hf
    have := LinearMap.congr_fun h (f y)
    simpa using this
  · intro T hT m
    apply PiTensorProduct.ext
    ext w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      PiTensorProduct.map_tprod, MultilinearMap.toLinearMap_apply,
      PiTensorProduct.dualDistrib_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i = y
    · subst hi
      simp
    · simp [Function.update_of_ne hi, hT i hi]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFixedRotationBasisOfCharpoly
section
open Matrix

private lemma cayley_hamilton_rank_three_factored {K : Type} [Field K] (τ : K) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X + 1)) :
    (M - 1) * (M * M - τ • M + 1) = 0 := by
  have h := Matrix.aeval_self_charpoly M
  rw [hM] at h
  simp only [map_mul, map_sub, map_add, map_one, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C] at h
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, sq] at h
  exact h

private lemma trace_inverseGram_conj_smul_eq {K : Type} [Field K] [CharZero K] (τ : K) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X + 1)) :
    Matrix.trace M = 1 + τ ∧ Matrix.trace (M * M) = τ ^ 2 - 1 := by
  have hp : ∀ t : K, (Matrix.scalar (Fin 3) t - M).det = (t - 1) * (t ^ 2 - τ * t + 1) := by
    intro t
    rw [← Matrix.eval_charpoly, hM]
    simp
  have e0 := hp 0
  have e1 := hp 1
  have em := hp (-1)
  simp only [Matrix.det_fin_three, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply] at e0 e1 em
  simp only [Fin.isValue, Fin.reduceEq, if_true, if_false, eq_self_iff_true] at e0 e1 em
  constructor
  · rw [Matrix.trace_fin_three]
    linear_combination e0 - e1 / 2 - em / 2
  · rw [Matrix.trace_fin_three]
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (M 0 0 + M 1 1 + M 2 2 + 1 + τ) * (e0 - e1 / 2 - em / 2) - (e1 - em)

theorem UpperTheory.exists_fixed_rotation_basis_of_charpoly :
    ∀ (K : Type) [Field K] [CharZero K] (τ : K), τ ^ 2 - 4 ≠ 0 → ∀ M : Matrix (Fin 3) (Fin 3) K,
        M.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X + 1) →
        ∃ e v : Fin 3 → K, M *ᵥ e = e ∧ M *ᵥ (M *ᵥ v) = τ • (M *ᵥ v) - v ∧ (Matrix.of ![e, v, M *ᵥ v]).det ≠ 0 := by
  intro K _ _ τ hτ M hM
  have hPQ := cayley_hamilton_rank_three_factored τ M hM
  obtain ⟨htr1, htr2⟩ := trace_inverseGram_conj_smul_eq τ M hM
  have hc : (2 - τ : K) ≠ 0 := by
    intro h0
    apply hτ
    have h2 : τ = 2 := by linear_combination -h0
    rw [h2]
    norm_num
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin 3) (Fin 3) K, Q = M * M - τ • M + 1 := ⟨_, rfl⟩
  rw [← hQdef] at hPQ
  have hMQ : M * Q = Q := by
    rw [sub_mul, one_mul, sub_eq_zero] at hPQ
    exact hPQ
  have hQM : Q * M = Q := by
    have hc' : Q * M = M * Q := by
      rw [hQdef]
      simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
        mul_smul_comm, mul_assoc]
    rw [hc', hMQ]
  have hQQ : Q * Q = (2 - τ) • Q := by
    calc Q * Q = Q * (M * M - τ • M + 1) := by rw [← hQdef]
      _ = Q * M * M - τ • (Q * M) + Q := by
        simp only [mul_add, mul_sub, mul_one, mul_smul_comm, mul_assoc]
      _ = (2 - τ) • Q := by
        rw [hQM, hQM, sub_smul, two_smul]
        abel
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin 3) (Fin 3) K, E = (2 - τ)⁻¹ • Q := ⟨_, rfl⟩
  have hEE : E * E = E := by
    rw [hE, smul_mul_smul_comm, hQQ, smul_smul]
    congr 1
    field_simp
  have hME : M * E = E := by rw [hE, mul_smul_comm, hMQ]
  have hEM : E * M = E := by rw [hE, smul_mul_assoc, hQM]
  have htrQ : Matrix.trace Q = 2 - τ := by
    rw [hQdef, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, htr1, htr2, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul]
    push_cast
    ring
  have htrE : Matrix.trace E = 1 := by
    rw [hE, Matrix.trace_smul, htrQ, smul_eq_mul, inv_mul_cancel₀ hc]
  obtain ⟨F, hF⟩ : ∃ F : Matrix (Fin 3) (Fin 3) K, F = 1 - E := ⟨_, rfl⟩
  have htrF : Matrix.trace F = 2 := by
    rw [hF, Matrix.trace_sub, Matrix.trace_one, htrE]
    simp only [Fintype.card_fin]
    norm_num
  have hQF : Q * F = 0 := by
    rw [hF, mul_sub, mul_one, hE, mul_smul_comm, hQQ, smul_smul, inv_mul_cancel₀ hc, one_smul,
      sub_self]
  have hEF : E * F = 0 := by rw [hF, mul_sub, mul_one, hEE, sub_self]
  have hMF : M * F = F * M := by rw [hF, mul_sub, sub_mul, mul_one, one_mul, hME, hEM]
  have hQv : ∀ x : Fin 3 → K, Q *ᵥ x = M *ᵥ (M *ᵥ x) - τ • (M *ᵥ x) + x := by
    intro x
    rw [hQdef, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_mulVec]
  have hdet : (Matrix.scalar (Fin 3) (1 : K) - M).det = 0 := by
    rw [← Matrix.eval_charpoly, hM]
    simp
  obtain ⟨e, he0, he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hMe : M *ᵥ e = e := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at he
    simpa using he.symm
  have hEe : E *ᵥ e = e := by
    have h1 : Q *ᵥ e = (2 - τ) • e := by
      rw [hQv, hMe, hMe, sub_smul, two_smul]
      abel
    rw [hE, Matrix.smul_mulVec, h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
  let W : Submodule K (Fin 3 → K) := LinearMap.range (Matrix.toLin' F)
  have hW : ∀ x ∈ W, Matrix.toLin' M x ∈ W := by
    rintro x ⟨y, rfl⟩
    refine ⟨M *ᵥ y, ?_⟩
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hMF]
  let g : W →ₗ[K] W := (Matrix.toLin' M).restrict hW
  obtain ⟨v0, hv0⟩ : ∃ v : W, LinearIndependent K ![v, g v] := by
    by_contra hno
    push_neg at hno
    obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hno
    have hMFx : ∀ x : Fin 3 → K, M *ᵥ (F *ᵥ x) = a • (F *ᵥ x) := by
      intro x
      have h := congrArg (fun h : W →ₗ[K] W => ((h ⟨F *ᵥ x, x, rfl⟩ : W) : Fin 3 → K)) ha
      simpa [g, LinearMap.restrict_apply, Matrix.toLin'_apply] using h
    have hMFm : M * F = a • F := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro z
      rw [map_smul, LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
        ← Matrix.mulVec_mulVec, hMFx]
    have htrM : Matrix.trace M = 1 + 2 * a := by
      have hsplit : M = M * E + M * F := by rw [← mul_add, hF, add_sub_cancel, mul_one]
      rw [hsplit, Matrix.trace_add, hME, hMFm, Matrix.trace_smul, htrE, htrF, smul_eq_mul]
      ring
    have hF0 : ∃ x : Fin 3 → K, F *ᵥ x ≠ 0 := by
      by_contra hall
      push_neg at hall
      have hF00 : F = 0 := by
        apply Matrix.toLin'.injective
        apply LinearMap.ext
        intro z
        rw [map_zero, LinearMap.zero_apply, Matrix.toLin'_apply, hall z]
      rw [hF00, Matrix.trace_zero] at htrF
      norm_num at htrF
    obtain ⟨x, hx⟩ := hF0
    have hq : (a ^ 2 - τ * a + 1) • (F *ᵥ x) = 0 := by
      have h := hQv (F *ᵥ x)
      rw [Matrix.mulVec_mulVec, hQF, Matrix.zero_mulVec, hMFx, Matrix.mulVec_smul, hMFx] at h
      rw [h]
      module
    have hq' : a ^ 2 - τ * a + 1 = 0 := by
      rcases smul_eq_zero.mp hq with h | h
      · exact h
      · exact absurd h hx
    apply hτ
    have ht : τ = 2 * a := by linear_combination htr1.symm.trans htrM
    linear_combination (τ - 2 * a) * ht - 4 * hq'
  obtain ⟨y, hy⟩ := v0.2
  set v : Fin 3 → K := (v0 : Fin 3 → K) with hvdef
  have hvF : v = F *ᵥ y := by rw [← hy, Matrix.toLin'_apply]
  have hv : LinearIndependent K ![v, M *ᵥ v] := by
    have h := hv0.map' W.subtype (Submodule.ker_subtype W)
    have hfun : (W.subtype ∘ ![v0, g v0]) = ![v, M *ᵥ v] := by
      ext i : 1
      fin_cases i <;> simp [g, LinearMap.restrict_apply, Matrix.toLin'_apply, hvdef]
    rw [hfun] at h
    exact h
  have hQv0 : Q *ᵥ v = 0 := by rw [hvF, Matrix.mulVec_mulVec, hQF, Matrix.zero_mulVec]
  refine ⟨e, v, hMe, ?_, ?_⟩
  · have h := hQv v
    rw [hQv0] at h
    rw [eq_sub_iff_add_eq, ← sub_eq_zero, h]
    abel
  · have hEv : E *ᵥ v = 0 := by rw [hvF, Matrix.mulVec_mulVec, hEF, Matrix.zero_mulVec]
    have hEMv : E *ᵥ (M *ᵥ v) = 0 := by rw [Matrix.mulVec_mulVec, hEM, hEv]
    have hli : LinearIndependent K ![e, v, M *ᵥ v] := by
      change LinearIndependent K (Fin.cons e ![v, M *ᵥ v])
      rw [linearIndependent_fin_cons]
      refine ⟨hv, fun hmem => ?_⟩
      have hle : Submodule.span K (Set.range ![v, M *ᵥ v]) ≤ LinearMap.ker (Matrix.toLin' E) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i <;> simp [Matrix.toLin'_apply, hEv, hEMv]
      have h0 := hle hmem
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, hEe] at h0
      exact he0 h0
    have hu : IsUnit (Matrix.of ![e, v, M *ᵥ v]) := Matrix.linearIndependent_rows_iff_isUnit.mp hli
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
end

