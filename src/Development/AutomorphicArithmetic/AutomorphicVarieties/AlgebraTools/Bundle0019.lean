import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0016
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0012

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TowerCompl
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem tc_mod (R : Type) [CommRing R] (a : Ideal R) (k : ℕ) (N : Type) [AddCommGroup N]
    [Module R N] (h : (a ^ k • ⊤ : Submodule R N) = ⊥) :
    ∃ _ : Module (AdicCompletion a R) N, ∀ (s : AdicCompletion a R) (r : R),
      AdicCompletion.evalₐ a k s = Ideal.Quotient.mk _ r → ∀ x : N, s • x = r • x := by
  have ht : Module.IsTorsionBySet R N ((a ^ k : Ideal R) : Set R) := fun x b => by
    have hb : (b : R) • x ∈ (a ^ k • ⊤ : Submodule R N) :=
      Submodule.smul_mem_smul b.2 Submodule.mem_top
    rw [h] at hb
    exact (Submodule.mem_bot R).mp hb
  letI iq : Module (R ⧸ a ^ k) N := ht.module
  letI inst : Module (AdicCompletion a R) N :=
    Module.compHom N (AdicCompletion.evalₐ a k).toRingHom
  refine ⟨inst, fun s r hs x => ?_⟩
  show (AdicCompletion.evalₐ a k s) • x = r • x
  rw [hs]
  exact ht.mk_smul r x

private theorem tc_eval (R : Type) [CommRing R] (a : Ideal R) (k : ℕ) (s : AdicCompletion a R) :
    ∃ r : R, AdicCompletion.evalₐ a (k + 1) s = Ideal.Quotient.mk _ r ∧
      AdicCompletion.evalₐ a k s = Ideal.Quotient.mk _ r := by
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective a R s
  refine ⟨x (k + 1), AdicCompletion.evalₐ_mk a (k + 1) x, ?_⟩
  rw [AdicCompletion.evalₐ_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  have hc := x.property (Nat.le_succ k)
  rw [SModEq.sub_mem] at hc
  simpa [Ideal.smul_eq_mul, Ideal.mul_top] using hc

private theorem tc_smul {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (a : Ideal R) (k : ℕ)
    (N : Type) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (x : N) :
    x ∈ ((a.map (algebraMap R S)) ^ k • ⊤ : Submodule S N) ↔ x ∈ (a ^ k • ⊤ : Submodule R N) := by
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem R, Ideal.smul_restrictScalars,
    Submodule.restrictScalars_top]

theorem UpperTheory.V.AlgebraTools.exists_tower_limit_completion :
    ∀ (R : Type) [CommRing R] (a : Ideal R), a.FG → ∀ (P : ℕ → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] (π : ∀ k, P (k + 1) →ₗ[R] P k),
      (∀ k, Function.Surjective (π k)) → (∀ k, LinearMap.ker (π k) = a ^ k • ⊤) → (∀ k, (a ^ k • ⊤ : Submodule R (P k)) = ⊥) →
      Module.Finite R (P 1) →
      ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (_ : Module (AdicCompletion a R) M) (_ : IsScalarTower R (AdicCompletion a R) M)
        (q : ∀ k, M →ₗ[R] P k), Module.Finite (AdicCompletion a R) M ∧ (∀ k, Function.Surjective (q k)) ∧
        (∀ k, LinearMap.ker (q k) = a ^ k • ⊤) ∧ (∀ k x, π k (q (k + 1) x) = q k x) ∧
        ∀ x : M, (∀ k, q k x = 0) → x = 0 := by
  intro R _ a ha P _ _ π hπ hker hkill hfin
  haveI : IsAdicComplete (a.map (algebraMap R (AdicCompletion a R))) (AdicCompletion a R) :=
    AdicCompletion.isAdicComplete_self a ha
  choose inst hinst using fun k => tc_mod R a k (P k) (hkill k)
  haveI tow : ∀ k, IsScalarTower R (AdicCompletion a R) (P k) := fun k => ⟨fun r s x => by
    obtain ⟨r₀, h₀⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ a k s)
    have h1 : AdicCompletion.evalₐ a k (r • s) = Ideal.Quotient.mk _ (r * r₀) := by
      rw [map_smul, ← h₀, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
    rw [hinst k (r • s) (r * r₀) h1, hinst k s r₀ h₀.symm, mul_smul]⟩
  let π' : ∀ k, P (k + 1) →ₗ[AdicCompletion a R] P k := fun k =>
    { toFun := π k
      map_add' := (π k).map_add
      map_smul' := fun s x => by
        obtain ⟨r, h1, h2⟩ := tc_eval R a k s
        show π k (s • x) = s • π k x
        rw [hinst (k + 1) s r h1, hinst k s r h2, (π k).map_smul] }
  have hker' : ∀ k, LinearMap.ker (π' k) = (a.map (algebraMap R (AdicCompletion a R))) ^ k • ⊤ := by
    intro k
    ext x
    rw [tc_smul (S := AdicCompletion a R) a k (P (k + 1)) x, ← hker k, LinearMap.mem_ker,
      LinearMap.mem_ker]
    all_goals exact Iff.rfl
  have hkill' : ∀ k, ((a.map (algebraMap R (AdicCompletion a R))) ^ k • ⊤ :
      Submodule (AdicCompletion a R) (P k)) = ⊥ := by
    intro k
    rw [eq_bot_iff]
    intro x hx
    rw [tc_smul (S := AdicCompletion a R) a k (P k) x, hkill k] at hx
    exact (Submodule.mem_bot _).mpr ((Submodule.mem_bot _).mp hx)
  have hfin' : Module.Finite (AdicCompletion a R) (P 1) :=
    Module.Finite.of_restrictScalars_finite R _ (P 1)
  obtain ⟨M, _, _, q, hfinM, hsurj, hkerq, hcompat, hsep⟩ :=
    UpperTheory.V.AlgebraTools.exists_tower_limit (AdicCompletion a R) (a.map (algebraMap R (AdicCompletion a R)))
      P π' (fun k => hπ k) hker' hkill' hfin'
  letI : Module R M := Module.compHom M (algebraMap R (AdicCompletion a R))
  haveI : IsScalarTower R (AdicCompletion a R) M := ⟨fun r s m => by
    show (r • s) • m = (algebraMap R (AdicCompletion a R) r) • (s • m)
    rw [Algebra.smul_def, mul_smul]⟩
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
    fun k => (q k).restrictScalars R, hfinM, fun k => hsurj k, ?_, fun k x => hcompat k x,
    fun x hx => hsep x hx⟩
  intro k
  ext x
  rw [LinearMap.mem_ker, ← tc_smul (S := AdicCompletion a R) a k M x, ← hkerq k, LinearMap.mem_ker]
  all_goals exact Iff.rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimKer
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem exists_sum_of_mem_span_smul_top {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    {n : ℕ} (g : Fin n → R) (x : M) (hx : x ∈ (Ideal.span (Set.range g) • ⊤ : Submodule R M)) :
    ∃ q : Fin n → M, x = ∑ c, g c • q c := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hr
    refine ⟨fun i => c i • m, ?_⟩
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  · rintro x y ⟨q, rfl⟩ ⟨q', rfl⟩
    exact ⟨fun i => q i + q' i, by simp [smul_add, Finset.sum_add_distrib]⟩

theorem UpperTheory.V.AlgebraTools.ULim.mem_smul_top_iff :
    ∀ (R : Type) [CommRing R] (F : Filter ℕ), F ≤ atTop → ∀ (I : ℕ → Ideal R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (a : Ideal R), a.FG → Antitone I →
      ∀ p : ∀ i, M i, ULim.mk F I M p ∈ (a • ⊤ : Submodule R (ULim F I M)) ↔
        ∀ j, ∀ᶠ N in F, p N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N)) := by
  intro R _ F hF I M _ _ a ha hI p
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 ha
  have hg' : Ideal.span (Set.range g) = a := hg
  have hga : ∀ c, g c ∈ a := fun c => hg' ▸ Ideal.subset_span ⟨c, rfl⟩
  constructor
  · intro hp j
    rw [← hg'] at hp
    obtain ⟨q, hq⟩ := exists_sum_of_mem_span_smul_top g _ hp
    choose q' hq' using fun c => ULim.mk_surjective F I M (q c)
    have h0 : ULim.mk F I M (p - ∑ c, g c • q' c) = 0 := by
      rw [map_sub, map_sum, hq]
      simp only [map_smul, hq', sub_self]
    filter_upwards [ULim.mk_eq_zero.1 h0 j] with N hN
    have h1 : (∑ c, g c • q' c) N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N)) := by
      rw [Finset.sum_apply]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem_smul (Ideal.mem_sup_left (hga c)) Submodule.mem_top
    have h2 := Submodule.add_mem ((a ⊔ I j) • ⊤ : Submodule R (M N)) (Submodule.smul_mono_left (le_sup_right : I j ≤ a ⊔ I j) hN) h1
    simpa using h2
  · intro hp
    obtain ⟨ν, hν, hP⟩ := exists_diag F hF
      (fun j N => p N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N))) hp
    have key : ∀ N, ∃ q : Fin n → M N, p N ∈ ((a ⊔ I (ν N)) • ⊤ : Submodule R (M N)) →
        p N - ∑ c, g c • q c ∈ (I (ν N) • ⊤ : Submodule R (M N)) := by
      intro N
      by_cases h : p N ∈ ((a ⊔ I (ν N)) • ⊤ : Submodule R (M N))
      · have h' := h
        rw [Submodule.sup_smul] at h'
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h'
        rw [← hg'] at hy
        obtain ⟨q, hq⟩ := exists_sum_of_mem_span_smul_top g _ hy
        refine ⟨q, fun _ => ?_⟩
        rw [← hq, ← hyz, add_sub_cancel_left]
        exact hz
      · exact ⟨0, fun h' => absurd h' h⟩
    choose q hq using key
    have h0 : ULim.mk F I M (p - ∑ c, g c • fun N => q N c) = 0 := by
      refine ULim.mk_eq_zero.2 fun j => ?_
      filter_upwards [hP, hν.eventually_ge_atTop j] with N hN hj
      have := Submodule.smul_mono_left (hI hj) (hq N (hN _ le_rfl))
      simpa [Finset.sum_apply] using this
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, map_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem_smul (hga c) Submodule.mem_top
end

