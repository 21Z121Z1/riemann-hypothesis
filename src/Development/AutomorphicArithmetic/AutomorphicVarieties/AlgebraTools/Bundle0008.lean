import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDualEx
section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem exists_lt_apply {n : ℕ} (w : Perm (Fin n)) (hw : w ≠ 1) : ∃ i, i < w i := by
  by_contra h
  push_neg at h
  apply hw
  have hs : ∑ i, (w i).val = ∑ i : Fin n, i.val := Equiv.sum_comp w (fun i => i.val)
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), (w i).val ≤ i.val := fun i _ => h i
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hs
  exact Equiv.ext fun i => Fin.ext (by simpa using heq i (Finset.mem_univ _))

theorem UpperTheory.V.AlgebraTools.hkDualEx :
    ∀ (R : Type) [CommRing R] (n : ℕ), ∃ (ι : Type) (_ : Fintype ι) (a b : ι → MvPolynomial (Fin n) R), IsDual a b := by
  intro R _ n
  refine ⟨Finset (Fin n × Fin n), inferInstance,
    fun t => if t ⊆ pairs n then ∏ p ∈ t, (X p.2 : MvPolynomial (Fin n) R) else 0,
    fun t => ∏ p ∈ pairs n \ t, (-X p.1 : MvPolynomial (Fin n) R), ?_⟩
  intro w
  have hsum : ∑ t : Finset (Fin n × Fin n), (if t ⊆ pairs n then ∏ p ∈ t, (X p.2 : MvPolynomial (Fin n) R) else 0) *
      rename w (∏ p ∈ pairs n \ t, (-X p.1 : MvPolynomial (Fin n) R)) =
      ∏ p ∈ pairs n, ((X p.2 : MvPolynomial (Fin n) R) + -X (w p.1)) := by
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun t : Finset (Fin n × Fin n) => t ⊆ pairs n) = (pairs n).powerset := by
      ext t
      simp
    rw [hf, Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [map_prod, rename_X]
  refine hsum.trans ?_
  split_ifs with h1
  · subst h1
    rw [De]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp [sub_eq_add_neg]
  · obtain ⟨i, hi⟩ := exists_lt_apply w h1
    apply Finset.prod_eq_zero (i := (i, w i))
    · simp [pairs, hi]
    · simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagCoi
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.lag_coi :
    ∀ {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] (a : ι → R) (P : E), (∀ i j, i ≠ j → IsUnit (a i - a j)) → aeval P (∏ i, (X - C (a i))) = 0 → CompleteOrthogonalIdempotents (lag a P) ∧ (∀ i, P * lag a P i = a i • lag a P i) ∧ (∀ (q : R[X]) i, aeval P q * lag a P i = q.eval (a i) • lag a P i) ∧ ∀ y i, Commute y P → Commute y (lag a P i) := by
  intro R E ι _ _ _ _ _ a P ha hm
  have hc : ∀ i, IsUnit (∏ j ∈ Finset.univ.erase i, (a i - a j)) := fun i =>
    IsUnit.prod_iff.2 (fun j hj => ha i j (Ne.symm (Finset.ne_of_mem_erase hj)))
  let L : ι → R[X] := fun i =>
    C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))) * ∏ j ∈ Finset.univ.erase i, (X - C (a j))
  have hL : ∀ i, lag a P i = aeval P (L i) := by
    intro i
    simp only [L, lag, map_mul, aeval_C, Algebra.smul_def]
  have hLe : ∀ i k, (L i).eval (a k) = if i = k then 1 else 0 := by
    intro i k
    simp only [L, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    split_ifs with h
    · subst h
      exact Ring.inverse_mul_cancel _ (hc i)
    · rw [Finset.prod_eq_zero (f := fun j => a k - a j)
        (Finset.mem_erase.2 ⟨Ne.symm h, Finset.mem_univ k⟩) (sub_self (a k)), mul_zero]
  have hroot : ∀ i, aeval P (X - C (a i)) * lag a P i = 0 := by
    intro i
    rw [hL, ← map_mul]
    have : (X - C (a i)) * L i =
        C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))) * ∏ j, (X - C (a j)) := by
      simp only [L]
      rw [mul_left_comm, Finset.mul_prod_erase Finset.univ (fun j => X - C (a j)) (Finset.mem_univ i)]
    rw [this, map_mul, hm, mul_zero]
  have hq : ∀ (q : R[X]) i, aeval P q * lag a P i = q.eval (a i) • lag a P i := by
    intro q i
    obtain ⟨g, hg⟩ := (X_sub_C_dvd_sub_C_eval : X - C (a i) ∣ q - C (q.eval (a i)))
    have hq' : q = g * (X - C (a i)) + C (q.eval (a i)) := by
      rw [mul_comm, ← hg]
      ring
    conv_lhs => rw [hq']
    rw [map_add, map_mul, add_mul, mul_assoc, hroot, mul_zero, zero_add, aeval_C, Algebra.smul_def]
  have hP : ∀ i, P * lag a P i = a i • lag a P i := by
    intro i
    have := hq X i
    rwa [aeval_X, eval_X] at this
  have hcomm : ∀ y i, Commute y P → Commute y (lag a P i) := by
    intro y i hy
    rw [hL]
    generalize L i = f
    induction f using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact hp.add_right hq
    | monomial n c =>
      rw [aeval_monomial]
      exact Commute.mul_right (show Commute y (algebraMap R E c) from (Algebra.commutes c y).symm)
        (hy.pow_right n)
  have hsum : ∑ i, lag a P i = 1 := by
    have h1 : ∏ i, (X - C (a i)) ∣ 1 - ∑ i, L i := by
      apply Finset.prod_dvd_of_coprime
      · intro i _ j _ hij
        exact isCoprime_X_sub_C_of_isUnit_sub (ha i j hij)
      · intro k _
        rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_one, eval_finset_sum]
        simp only [hLe, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    obtain ⟨g, hg⟩ := h1
    have h2 := congrArg (aeval P) hg
    rw [map_mul, hm, zero_mul, map_sub, map_one, map_sum, sub_eq_zero] at h2
    simp only [hL]
    exact h2.symm
  refine ⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, hsum⟩, hP, hq, hcomm⟩
  · show lag a P i * lag a P i = lag a P i
    have := hq (L i) i
    rw [← hL, hLe, if_pos rfl, one_smul] at this
    exact this
  · have := hq (L i) j
    rw [← hL, hLe, if_neg hij, zero_smul] at this
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LemmaB
section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.lemma_B_range {A H Q : Type} [CommRing A] [AddCommGroup H] [Module A H]
    [AddCommGroup Q] [Module A Q] (N : Submodule A H) (φ : H →ₗ[A] Q) (h : N ≤ LinearMap.ker φ) :
    Module.length A (LinearMap.range φ) ≤ Module.length A (H ⧸ N) := by
  refine Module.length_le_of_surjective (N.liftQ φ.rangeRestrict (by rwa [LinearMap.ker_rangeRestrict])) ?_
  intro y
  obtain ⟨x, rfl⟩ := φ.surjective_rangeRestrict y
  exact ⟨N.mkQ x, rfl⟩

private theorem UpperTheory.V.AlgebraTools.lemma_B_sup {A Q : Type} [CommRing A] [AddCommGroup Q] [Module A Q]
    (P U V : Submodule A Q) (h : P ≤ U ⊔ V) :
    Module.length A P ≤ Module.length A U + Module.length A V := by
  have hsurj : Function.Surjective ((Submodule.inclusion (le_sup_left : U ≤ U ⊔ V)).coprod
      (Submodule.inclusion (le_sup_right : V ≤ U ⊔ V))) := by
    rintro ⟨y, hy⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
  calc Module.length A P ≤ Module.length A (U ⊔ V : Submodule A Q) :=
        Module.length_le_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
    _ ≤ Module.length A (U × V) := Module.length_le_of_surjective _ hsurj
    _ = Module.length A U + Module.length A V := Module.length_prod _ _ _

private theorem UpperTheory.V.AlgebraTools.lemma_B_le {A M M' S : Type} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup M'] [Module A M']
    [Module.Finite A M'] (I : Ideal A) (f : S → M →ₗ[A] M') :
    ∃ c : ℕ, ∀ m : ℕ, (⨅ s, (I ^ (m + c) • (⊤ : Submodule A M')).comap (f s)) ≤
      (⨅ s, LinearMap.ker (f s)) ⊔ I ^ m • (⊤ : Submodule A M) := by
  classical
  obtain ⟨_, ⟨T, rfl⟩, hT⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian A (M →ₗ[A] M'))
    (Set.range fun T : Finset S => Submodule.span A (f '' (T : Set S))) ⟨_, ⟨∅, rfl⟩⟩
  have hspan : ∀ s, f s ∈ Submodule.span A (f '' (T : Set S)) := by
    intro s
    by_contra hs
    refine hT _ ⟨insert s T, rfl⟩ (lt_of_le_of_ne (Submodule.span_mono ?_) ?_)
    · apply Set.image_mono
      rw [Finset.coe_insert]
      exact Set.subset_insert _ _
    · intro heq
      apply hs
      simp only at heq
      rw [heq]
      exact Submodule.subset_span ⟨s, by simp, rfl⟩
  have hker : ⨅ t : T, LinearMap.ker (f t) ≤ ⨅ s, LinearMap.ker (f s) := by
    intro x hx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    intro s
    have hle : Submodule.span A (f '' (T : Set S)) ≤
        LinearMap.ker (LinearMap.applyₗ (R := A) (M₂ := M') x) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      simpa using hx ⟨t, ht⟩
    simpa using hle (hspan s)
  let F : M →ₗ[A] (T → M') := LinearMap.pi fun t => f t
  obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.comap_pow_le I F
  refine ⟨c, fun m x hx => ?_⟩
  have hFx : F x ∈ I ^ (m + c) • (⊤ : Submodule A (T → M')) := by
    rw [← Finset.univ_sum_single (F x)]
    refine Submodule.sum_mem _ fun t _ => ?_
    have h1 : f t x ∈ I ^ (m + c) • (⊤ : Submodule A M') := by
      simpa using (Submodule.mem_iInf _).mp hx t
    simpa [F] using Submodule.smul_top_le_comap_smul_top (I ^ (m + c))
      (LinearMap.single A (fun _ : T => M') t) h1
  have hm := hc m hFx
  have hle : LinearMap.ker F ≤ ⨅ s, LinearMap.ker (f s) := by
    simp only [F, LinearMap.ker_pi]
    exact hker
  exact (sup_le_sup_right hle _) hm

theorem UpperTheory.V.AlgebraTools.lemma_B :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {M M' S : Type} [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup M'] [Module A M'] [Module.Finite A M'] (f : S → M →ₗ[A] M'), ∃ e : ℕ, ∀ j : ℕ, Module.length A ((⨅ s, (maximalIdeal A ^ j • (⊤ : Submodule A M')).comap (f s)).map (maximalIdeal A ^ j • (⊤ : Submodule A M)).mkQ) ≤ ((Module.finrank A (⨅ s, LinearMap.ker (f s) : Submodule A M) * j + e : ℕ) : ℕ∞) := by
  intro A _ _ _ M M' S _ _ _ _ _ _ f
  set K : Submodule A M := ⨅ s, LinearMap.ker (f s) with hKdef
  obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.lemma_B_le (maximalIdeal A) f
  obtain ⟨cK, -, hK⟩ := UpperTheory.V.AlgebraTools.len_fg_quot (A := A) K
  obtain ⟨cM, -, hM⟩ := UpperTheory.V.AlgebraTools.len_fg_quot (A := A) M
  refine ⟨cK + Module.finrank A M * c + cM, fun j => ?_⟩
  set P := ⨅ s, (maximalIdeal A ^ j • (⊤ : Submodule A M')).comap (f s) with hPdef
  set N := maximalIdeal A ^ j • (⊤ : Submodule A M) with hNdef
  have hQ : Module.length A (P.map N.mkQ) ≤ Module.length A (M ⧸ N) :=
    Module.length_le_of_injective (Submodule.subtype _) (Submodule.injective_subtype _)
  by_cases hj : j < c
  · refine le_trans hQ (le_trans (hM j).2 ?_)
    have h1 := Nat.mul_le_mul_left (Module.finrank A M) hj.le
    have h2 := Nat.zero_le (Module.finrank A K * j)
    exact_mod_cast (show Module.finrank A M * j + cM ≤
      Module.finrank A K * j + (cK + Module.finrank A M * c + cM) by omega)
  · push_neg at hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + c := ⟨j - c, by omega⟩
    have hP : P ≤ K ⊔ maximalIdeal A ^ m • ⊤ := hc m
    have hU : Module.length A (K.map N.mkQ) ≤ ((Module.finrank A K * (m + c) + cK : ℕ) : ℕ∞) := by
      refine le_trans ?_ (hK (m + c)).2
      have := UpperTheory.V.AlgebraTools.lemma_B_range (maximalIdeal A ^ (m + c) • (⊤ : Submodule A K))
        (N.mkQ ∘ₗ K.subtype) ?_
      · rwa [LinearMap.range_comp, Submodule.range_subtype] at this
      · intro x hx
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_top_le_comap_smul_top _ K.subtype hx
    let g : (M ⧸ N) →ₗ[A] (M ⧸ (maximalIdeal A ^ m • (⊤ : Submodule A M))) :=
      N.liftQ (Submodule.mkQ _) (by
        rw [Submodule.ker_mkQ]
        exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right m c)))
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
      exact ⟨N.mkQ x, rfl⟩
    have hV : (maximalIdeal A ^ m • (⊤ : Submodule A M)).map N.mkQ = LinearMap.ker g := by
      rw [Submodule.ker_liftQ, Submodule.ker_mkQ]
    have hlen := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
      (Submodule.injective_subtype _) hg (LinearMap.exact_subtype_ker_map g)
    have hVb : Module.length A (LinearMap.ker g) ≤ ((Module.finrank A M * c + cM : ℕ) : ℕ∞) := by
      have h1 := (hM (m + c)).2
      have h2 := (hM m).1
      rw [hlen] at h1
      have h3 : Module.length A (LinearMap.ker g) + ((Module.finrank A M * m : ℕ) : ℕ∞) ≤
          ((Module.finrank A M * (m + c) + cM : ℕ) : ℕ∞) :=
        le_trans (add_le_add le_rfl h2) h1
      have hfin : Module.length A (LinearMap.ker g) ≠ ⊤ := by
        intro htop
        rw [htop, top_add, top_le_iff] at h3
        exact ENat.coe_ne_top _ h3
      obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfin
      rw [← ha] at h3 ⊢
      norm_cast at h3 ⊢
      rw [Nat.mul_add] at h3
      omega
    calc Module.length A (P.map N.mkQ)
        ≤ Module.length A (K.map N.mkQ) +
          Module.length A ((maximalIdeal A ^ m • (⊤ : Submodule A M)).map N.mkQ) := by
          apply UpperTheory.V.AlgebraTools.lemma_B_sup
          rw [← Submodule.map_sup]
          exact Submodule.map_mono hP
      _ ≤ ((Module.finrank A K * (m + c) + cK : ℕ) : ℕ∞) + ((Module.finrank A M * c + cM : ℕ) : ℕ∞) := by
          rw [hV]
          exact add_le_add hU hVb
      _ = _ := by
          push_cast
          ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LimElt
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_lim_elt :
    ∀ (G ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (U : Ultrafilter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal],
      (∀ a : ι → G, ∃ b : G, ∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), b⁻¹ * a i ∈ O.toSubgroup) ∧
      (∀ (a : ι → G) (b b' : G), (∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), b⁻¹ * a i ∈ K i ⊔ O.toSubgroup) →
        (∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), b'⁻¹ * a i ∈ K i ⊔ O.toSubgroup) → b⁻¹ * b' ∈ limKer (U : Filter ι) K) := by
  intro G ι _ _ _ _ _ U K _
  refine ⟨fun a => ?_, fun a b b' hb hb' => ?_⟩
  · obtain ⟨b, hl⟩ : ∃ b : G, Tendsto a (U : Filter ι) (nhds b) := by
      refine ⟨(U.map a).lim, ?_⟩
      have h' := (U.map a).le_nhds_lim
      rw [Ultrafilter.coe_map] at h'
      exact h'
    refine ⟨b, fun O => ?_⟩
    have hopen : IsOpen {y : G | b⁻¹ * y ∈ O.toSubgroup} :=
      O.toOpenSubgroup.isOpen.preimage (continuous_mul_left _)
    exact hl.eventually (hopen.mem_nhds (by simp))
  · rw [mem_limKer]
    intro O
    filter_upwards [hb O, hb' O] with i h1 h2
    have heq : b⁻¹ * b' = (b⁻¹ * a i) * (b'⁻¹ * a i)⁻¹ := by group
    rw [heq]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LimKer
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem limKer_key {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : Ultrafilter ι) (K : ι → Subgroup G) (O : OpenNormalSubgroup G) (x : G) :
    (∀ᶠ i in (U : Filter ι), x ∈ K i ⊔ O.toSubgroup) ↔
      x ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup := by
  haveI := O.isNormal'
  constructor
  · intro h
    have hex : ∀ᶠ i in (U : Filter ι), ∃ k ∈ K i, k⁻¹ * x ∈ O.toSubgroup := by
      refine h.mono fun i hi => ?_
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 hi
      refine ⟨y, hy, ?_⟩
      rw [← hyz]
      simpa using hz
    classical
    obtain ⟨k, hk⟩ : ∃ k : ι → G, ∀ᶠ i in (U : Filter ι), k i ∈ K i ∧ (k i)⁻¹ * x ∈ O.toSubgroup := by
      refine ⟨fun i => if hi : ∃ k ∈ K i, k⁻¹ * x ∈ O.toSubgroup then hi.choose else 1, ?_⟩
      refine hex.mono fun i hi => ?_
      simp only [dif_pos hi]
      exact hi.choose_spec
    obtain ⟨l, hl⟩ : ∃ l : G, Tendsto k (U : Filter ι) (nhds l) := by
      refine ⟨(U.map k).lim, ?_⟩
      have h' := (U.map k).le_nhds_lim
      rw [Ultrafilter.coe_map] at h'
      exact h'
    have hlL : l ∈ limKer (U : Filter ι) K := by
      rw [mem_limKer]
      intro O'
      have hopen : IsOpen {y : G | l⁻¹ * y ∈ O'.toSubgroup} :=
        O'.toOpenSubgroup.isOpen.preimage (continuous_mul_left _)
      filter_upwards [hl.eventually (hopen.mem_nhds (by simp)), hk] with i h1 h2
      have heq : l = k i * (l⁻¹ * k i)⁻¹ := by group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h2.1) (Subgroup.mem_sup_right (Subgroup.inv_mem _ h1))
    have hC : IsClosed {y : G | y⁻¹ * x ∈ O.toSubgroup} :=
      O.toOpenSubgroup.isClosed.preimage (continuous_inv.mul continuous_const)
    have hlx : l⁻¹ * x ∈ O.toSubgroup := hC.mem_of_tendsto hl (hk.mono fun i h => h.2)
    have heq : x = l * (l⁻¹ * x) := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlL) (Subgroup.mem_sup_right hlx)
  · intro h
    let S : Subgroup G :=
      { carrier := {g | ∀ᶠ i in (U : Filter ι), g ∈ K i ⊔ O.toSubgroup}
        mul_mem' := fun ha hb =>
          Filter.Eventually.mono (Filter.Eventually.and ha hb) fun i hi => Subgroup.mul_mem _ hi.1 hi.2
        one_mem' := Filter.Eventually.of_forall fun i => Subgroup.one_mem _
        inv_mem' := fun ha => Filter.Eventually.mono ha fun i hi => Subgroup.inv_mem _ hi }
    have hle : limKer (U : Filter ι) K ⊔ O.toSubgroup ≤ S :=
      sup_le (fun g hg => (mem_limKer.1 hg) O)
        (fun g hg => Filter.Eventually.of_forall fun i => Subgroup.mem_sup_right hg)
    exact hle h

theorem UpperTheory.V.AlgebraTools.limKer_sup :
    ∀ (G ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (U : Ultrafilter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal],
      IsClosed (limKer (U : Filter ι) K : Set G) ∧
      (∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), K i ⊔ O.toSubgroup = limKer (U : Filter ι) K ⊔ O.toSubgroup) ∧
      (∀ O : OpenNormalSubgroup G, limKer (U : Filter ι) K ≤ O.toSubgroup ↔ ∀ᶠ i in (U : Filter ι), K i ≤ O.toSubgroup) := by
  intro G ι _ _ _ _ _ U K _
  have h2 : ∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι),
      K i ⊔ O.toSubgroup = limKer (U : Filter ι) K ⊔ O.toSubgroup := by
    intro O
    obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
      (fun g : G => {y : G | g⁻¹ * y ∈ O.toSubgroup})
      (fun g => O.toOpenSubgroup.isOpen.preimage (continuous_mul_left _))
      (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
    have hev : ∀ᶠ i in (U : Filter ι), ∀ t ∈ T,
        (t ∈ K i ⊔ O.toSubgroup ↔ t ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup) := by
      refine (Filter.eventually_all_finset T).2 (fun t _ => ?_)
      by_cases ht : t ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup
      · exact ((limKer_key U K O t).2 ht).mono fun i hi => iff_of_true hi ht
      · have hn : ¬ ∀ᶠ i in (U : Filter ι), t ∈ K i ⊔ O.toSubgroup :=
          fun h => ht ((limKer_key U K O t).1 h)
        exact (Ultrafilter.eventually_not.2 hn).mono fun i hi => iff_of_false hi ht
    filter_upwards [hev] with i hi
    ext g
    obtain ⟨t, htT, hgt⟩ : ∃ t ∈ T, t⁻¹ * g ∈ O.toSubgroup := by
      have := hT (Set.mem_univ g)
      simp only [Set.mem_iUnion] at this
      obtain ⟨t, htT, hgt⟩ := this
      exact ⟨t, htT, hgt⟩
    have mem_iff : ∀ M : Subgroup G, O.toSubgroup ≤ M → (g ∈ M ↔ t ∈ M) := by
      intro M hM
      have hg : g = t * (t⁻¹ * g) := by group
      rw [hg]
      exact mul_mem_cancel_right (hM hgt)
    rw [mem_iff _ le_sup_right, mem_iff _ le_sup_right]
    exact hi t htT
  have hclosed : IsClosed (limKer (U : Filter ι) K : Set G) := by
    have hset : (limKer (U : Filter ι) K : Set G) =
        ⋂ O : OpenNormalSubgroup G, ((limKer (U : Filter ι) K ⊔ O.toSubgroup : Subgroup G) : Set G) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_iInter]
      constructor
      · intro hx O
        exact Subgroup.mem_sup_left hx
      · intro hx
        rw [mem_limKer]
        intro O
        exact (limKer_key U K O x).2 (hx O)
    rw [hset]
    exact isClosed_iInter fun O =>
      Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right O.toOpenSubgroup.isOpen)
  refine ⟨hclosed, h2, fun O => ⟨fun h => ?_, fun h => ?_⟩⟩
  · filter_upwards [h2 O] with i hi
    rw [sup_eq_right.2 h] at hi
    exact sup_eq_right.1 hi
  · intro x hx
    obtain ⟨i, hi1, hi2⟩ := ((mem_limKer.1 hx O).and h).exists
    exact (sup_le hi2 le_rfl) hi1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.OrthonormalLocal
section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.sqrt_of_residue {R' : Type} [CommRing R'] [HenselianLocalRing R']
    (h2 : IsUnit (2 : R')) (u : R') (hu : IsUnit u) (hs : IsSquare (residue R' u)) :
    ∃ a : R', a * a = u := by
  obtain ⟨b, hb⟩ := hs
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective b
  have hres : residue R' (a₀ ^ 2 - u) = 0 := by rw [map_sub, map_pow, hb, pow_two, sub_self]
  have ha₀ : IsUnit a₀ := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    intro h0
    have hu0 : residue R' u = 0 := by rw [hb, h0, mul_zero]
    exact (hu.map (residue R')).ne_zero hu0
  have hev : eval a₀ (X ^ 2 - C u) ∈ maximalIdeal R' := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa using hres
  have hd : eval a₀ (derivative (X ^ 2 - C u)) = 2 * a₀ := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
      eval_pow, eval_X]
    norm_num
  have hdu : IsUnit (eval a₀ (derivative (X ^ 2 - C u))) := by
    rw [hd]
    exact h2.mul ha₀
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 - C u)
    (monic_X_pow_sub_C u two_ne_zero) a₀ hev hdu
  refine ⟨a, ?_⟩
  have h0 := ha.eq_zero
  simp only [eval_sub, eval_pow, eval_X, eval_C] at h0
  rw [← pow_two]
  exact sub_eq_zero.mp h0

theorem UpperTheory.V.AlgebraTools.orthonormal_local :
    ∀ {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [HenselianLocalRing R'] (φ : R →+* R') {n : ℕ} (H : Matrix (Fin n) (Fin n) R), IsUnit (2 : R) → Hᵀ = H → IsUnit H.det → (∀ c : Rˣ, IsSquare (residue R' (φ c))) → ∃ P : GL (Fin n) R', (P : Matrix (Fin n) (Fin n) R')ᵀ * H.map φ * P = 1 := by
  intro R R' _ _ _ _ φ n H h2 hT hdet hsq
  obtain ⟨P, c, hP⟩ := UpperTheory.V.AlgebraTools.diag_local H h2 hT hdet
  have h2' : IsUnit (2 : R') := by
    have h := h2.map φ
    rwa [map_ofNat] at h
  have hroot : ∀ i, ∃ a : R', a * a = φ (c i) := fun i =>
    UpperTheory.V.AlgebraTools.sqrt_of_residue h2' _ ((c i).isUnit.map φ) (hsq (c i))
  choose a ha using hroot
  have hau : ∀ i, IsUnit (a i) := fun i =>
    isUnit_of_mul_isUnit_left (y := a i) (by rw [ha i]; exact (c i).isUnit.map φ)
  let D : GL (Fin n) R' :=
    ⟨diagonal fun i => (((hau i).unit⁻¹ : R'ˣ) : R'), diagonal fun i => a i,
      by rw [diagonal_mul_diagonal]; convert diagonal_one using 2; simp,
      by rw [diagonal_mul_diagonal]; convert diagonal_one using 2; simp⟩
  have hmap : ((Matrix.GeneralLinearGroup.map φ P : GL (Fin n) R') : Matrix (Fin n) (Fin n) R') =
      (P : Matrix (Fin n) (Fin n) R).map φ := by
    ext i j
    exact Matrix.GeneralLinearGroup.map_apply φ i j P
  have key : ((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ *
      (P : Matrix (Fin n) (Fin n) R).map φ = diagonal fun i => φ (c i) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hP, diagonal_map (map_zero φ)]
  refine ⟨Matrix.GeneralLinearGroup.map φ P * D, ?_⟩
  rw [Units.val_mul, hmap, Matrix.transpose_mul]
  have hD : ((D : GL (Fin n) R') : Matrix (Fin n) (Fin n) R') =
      diagonal fun i => (((hau i).unit⁻¹ : R'ˣ) : R') := rfl
  calc ((D : Matrix (Fin n) (Fin n) R'))ᵀ * ((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ *
        ((P : Matrix (Fin n) (Fin n) R).map φ * (D : Matrix (Fin n) (Fin n) R'))
      = ((D : Matrix (Fin n) (Fin n) R'))ᵀ * (((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ *
        (P : Matrix (Fin n) (Fin n) R).map φ) * (D : Matrix (Fin n) (Fin n) R') := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [key, hD, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
      convert diagonal_one using 2
      funext i
      rw [← ha i]
      calc ((hau i).unit⁻¹ : R'ˣ).val * (a i * a i) * ((hau i).unit⁻¹ : R'ˣ).val
          = (((hau i).unit⁻¹ : R'ˣ).val * (hau i).unit.val) *
            ((hau i).unit.val * ((hau i).unit⁻¹ : R'ˣ).val) := by
            simp only [IsUnit.unit_spec]; ring
        _ = 1 := by simp
end

