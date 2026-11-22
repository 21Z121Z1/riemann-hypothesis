import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0006
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0005

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GcDescend
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

theorem test_descend : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (𝔮 : Ideal A) (M : Type) [AddCommGroup M] [Module A M] (L : Submodule A M) (x : M), 𝔮.IsPrime → 𝔮.height = 1 → Function.Injective (algebraMap A O) → (∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (algebraMap A O a)) < 1) → (1 : O) ⊗ₜ[A] x ∈ Submodule.span O ((fun y : M => (1 : O) ⊗ₜ[A] y) '' (L : Set M)) → ∃ s : A, s ∉ 𝔮 ∧ s • x ∈ L := by
  intro A K _ _ _ _ _ _ _ C _ v O _ _ hv _ q M _ _ L x hq h1 hinj hcen hx
  haveI : IsDomain O := hv.hom_inj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers _ hv
  haveI := dvr_of_height_one q h1
  have hu : ∀ s : q.primeCompl, IsUnit (algebraMap A O s) := fun s => by
    rw [hv.isUnit_iff_valuation_eq_one]
    exact le_antisymm (hv.map_le_one _) (not_lt.1 fun h => s.2 ((hcen s).2 h))
  let R := Localization.AtPrime q
  letI : Algebra R O := (IsLocalization.lift (M := q.primeCompl) hu).toAlgebra
  have hcomp : ∀ a : A, algebraMap R O (algebraMap A R a) = algebraMap A O a := fun a =>
    IsLocalization.lift_eq hu a
  haveI : IsScalarTower A R O := IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  have hinjR : Function.Injective (algebraMap R O) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl r
    have h2 : algebraMap A O a = 0 := by
      rw [← hcomp, ← IsLocalization.mk'_spec R a s, map_mul]
      simp only at hr
      rw [hr, zero_mul]
    have : a = 0 := hinj (by simpa using h2)
    simp [this]
  haveI : IsLocalHom (algebraMap R O) := ⟨fun r hr => by
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl r
    simp only at hr ⊢
    rw [IsLocalization.AtPrime.isUnit_mk'_iff R q]
    have h2 : IsUnit (algebraMap A O a) := by
      rw [← hcomp, ← IsLocalization.mk'_spec R a s, map_mul, hcomp]
      exact hr.mul (hu s)
    rw [hv.isUnit_iff_valuation_eq_one] at h2
    intro ha
    exact ((hcen a).1 ha).ne h2⟩
  haveI : FaithfulSMul R O := (faithfulSMul_iff_algebraMap_injective R O).2 hinjR
  haveI : Module.Flat R O := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  haveI : Module.FaithfullyFlat R O := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have h0 : (1 : O) ⊗ₜ[A] (L.mkQ x) = 0 := by
    have : Submodule.span O ((fun y : M => (1 : O) ⊗ₜ[A] y) '' (L : Set M)) ≤
        LinearMap.ker (L.mkQ.baseChange O) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      simp [(Submodule.Quotient.mk_eq_zero L).2 hy]
    simpa using this hx
  have h2 : (1 : O) ⊗ₜ[R] ((1 : R) ⊗ₜ[A] (L.mkQ x)) = 0 := by
    apply (AlgebraTensorModule.cancelBaseChange A R O O (M ⧸ L)).injective
    simpa using h0
  rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h2
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff q.primeCompl
    (TensorProduct.mk A R (M ⧸ L) 1)).1 h2
  refine ⟨s, s.2, ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
  exact hs

end PositivityTheory.HtPt.Gc
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GcIncl
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

private theorem mem_range_bc_of_entries_mem_intL {A K : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (k : K)
    (h : ∀ q : Ideal A, q.IsPrime → q.height = 1 →
      ∃ s : A, s ∉ q ∧ ∃ c : A, s • k = algebraMap A K c) :
    ∃ c : A, algebraMap A K c = k := by
  have hk : k ∈ Subalgebra.toSubmodule (⊥ : Subalgebra A K) := by
    rw [GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.proof A K]
    refine (Submodule.mem_iInf _).2 fun p => (Submodule.mem_iInf _).2 fun hp => ?_
    obtain ⟨s, hs, c, hc⟩ := h p.asIdeal p.isPrime hp
    refine ⟨s, hs, ?_⟩
    rw [hc, Subalgebra.mem_toSubmodule]
    exact Subalgebra.algebraMap_mem _ c
  rw [Subalgebra.mem_toSubmodule, Algebra.mem_bot] at hk
  obtain ⟨c, hc⟩ := hk
  exact ⟨c, hc⟩

theorem test_incl : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (x : Ω), M.IsLattice K → Module.Projective A M → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → ∃ s : A, s ∉ 𝔮 ∧ s • x ∈ M) → x ∈ M := by
  intro A K _ _ _ _ _ _ _ Ω _ _ _ _ M x hlat hproj hloc
  classical
  have hden : ∀ w ∈ Submodule.span K (M : Set Ω), ∃ d ∈ nonZeroDivisors A, d • w ∈ M := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact ⟨1, one_mem _, by rw [one_smul]; exact hw⟩
    | zero => exact ⟨1, one_mem _, by rw [smul_zero]; exact M.zero_mem⟩
    | add u w _ _ hu hw =>
      obtain ⟨d1, hd1, h1⟩ := hu
      obtain ⟨d2, hd2, h2⟩ := hw
      refine ⟨d1 * d2, mul_mem hd1 hd2, ?_⟩
      have e1 : (d1 * d2) • u = d2 • (d1 • u) := by rw [mul_comm, mul_smul]
      have e2 : (d1 * d2) • w = d1 • (d2 • w) := by rw [mul_smul]
      rw [smul_add, e1, e2]
      exact M.add_mem (M.smul_mem _ h1) (M.smul_mem _ h2)
    | smul k w _ hw =>
      obtain ⟨d, hd, h1⟩ := hw
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) k
      refine ⟨b * d, mul_mem hb hd, ?_⟩
      have hb0 : algebraMap A K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      have e : (b * d) • ((algebraMap A K a / algebraMap A K b) • w) = a • (d • w) := by
        rw [← algebraMap_smul K (b * d), smul_smul, smul_smul a d w, ← algebraMap_smul K (a * d) w]
        congr 1
        rw [map_mul, map_mul]
        field_simp
      rw [e]
      exact M.smul_mem a h1
  obtain ⟨d, hd, hdx⟩ := hden x (by rw [hlat.span_eq_top]; trivial)
  have hd0' : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  obtain ⟨σ, hσ⟩ := hproj.out
  set z : M := ⟨d • x, hdx⟩ with hzdef
  have hdiv : ∀ m : M, ∃ c : A, σ z m = d * c := by
    intro m
    have hl : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧
        ∃ c : A, s • (algebraMap A K (σ z m) / algebraMap A K d) = algebraMap A K c := by
      intro q hq hh
      obtain ⟨s, hs, hsx⟩ := hloc q hq hh
      refine ⟨s, hs, σ ⟨s • x, hsx⟩ m, ?_⟩
      have hz : s • z = d • (⟨s • x, hsx⟩ : M) := Subtype.ext (smul_comm s d x)
      have hm : s * σ z m = d * σ ⟨s • x, hsx⟩ m := by
        have h' := congrArg (fun f => f m) (congrArg σ hz)
        simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using h'
      rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, hm, map_mul]
      field_simp
    obtain ⟨c, hc⟩ := mem_range_bc_of_entries_mem_intL (K := K) _ hl
    refine ⟨c, IsFractionRing.injective A K ?_⟩
    rw [map_mul, hc]
    field_simp
  choose c hc using hdiv
  have hyM : (∑ m ∈ (σ z).support, c m • (m : Ω)) ∈ M :=
    M.sum_mem (fun m _ => M.smul_mem _ m.2)
  have hsum : (∑ m ∈ (σ z).support, (σ z m) • (m : Ω)) = (z : Ω) := by
    have h1 := congrArg Subtype.val (hσ z)
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum] at h1
    simpa using h1
  have hzy : d • (∑ m ∈ (σ z).support, c m • (m : Ω)) = d • x := by
    rw [Finset.smul_sum]
    refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) hsum
    rw [hc m, mul_smul]
  have hcancel : ∀ u w : Ω, d • u = d • w → u = w := by
    intro u w huw
    have h1 : (algebraMap A K d) • u = (algebraMap A K d) • w := by
      rw [algebraMap_smul, algebraMap_smul]
      exact huw
    have h2 : (algebraMap A K d)⁻¹ • ((algebraMap A K d) • u) =
        (algebraMap A K d)⁻¹ • ((algebraMap A K d) • w) := by rw [h1]
    rw [smul_smul, smul_smul, inv_mul_cancel₀ hd0', one_smul, one_smul] at h2
    exact h2
  rw [← hcancel _ _ hzy]
  exact hyM

theorem dvd_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {a t : A} (ha : a ≠ 0)
    (h : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧ a ∣ s * t) : a ∣ t := by
  classical
  have ha' : algebraMap A (FractionRing A) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr ha
  have hl : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧
      ∃ c : A, s • (algebraMap A (FractionRing A) t / algebraMap A (FractionRing A) a) =
        algebraMap A (FractionRing A) c := by
    intro q hq hh
    obtain ⟨s, hs, u, hu⟩ := h q hq hh
    refine ⟨s, hs, u, ?_⟩
    rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, hu, map_mul]
    field_simp
  obtain ⟨c, hc⟩ := mem_range_bc_of_entries_mem_intL (K := FractionRing A) _ hl
  refine ⟨c, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul, hc]
  field_simp

theorem smul_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {M : Type} [AddCommGroup M] [Module A M] [Module.Projective A M]
    {a : A} (ha : a ≠ 0) (x : M)
    (h : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧ ∃ y : M, s • x = a • y) :
    ∃ y : M, x = a • y := by
  classical
  obtain ⟨σ, hσ⟩ := ‹Module.Projective A M›.out
  have hdiv : ∀ m : M, a ∣ σ x m := by
    intro m
    refine dvd_of_height_one ha (fun q hq hh => ?_)
    obtain ⟨s, hs, y, hy⟩ := h q hq hh
    refine ⟨s, hs, σ y m, ?_⟩
    have h' := congrArg (fun f => f m) (congrArg σ hy)
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using h'
  choose c hc using hdiv
  refine ⟨∑ m ∈ (σ x).support, c m • m, ?_⟩
  conv_lhs => rw [← hσ x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp only [hc m, mul_smul, id_eq]

theorem test_div : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (x : Ω) (a b : A), M.FG → Module.Projective A M → x ∈ M → a ≠ 0 → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → a ∈ 𝔮 → b ∈ 𝔮) → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → b ∈ 𝔮 → ∃ s : A, s ∉ 𝔮 ∧ ∃ y ∈ M, s • x = a • y) → ∃ y ∈ M, x = a • y := by
  intro A K _ _ _ _ _ _ _ Ω _ _ _ _ M x a b _ hproj hx ha hab hloc
  have hloc' : ∀ q : Ideal A, q.IsPrime → q.height = 1 →
      ∃ s : A, s ∉ q ∧ ∃ y : M, s • (⟨x, hx⟩ : M) = a • y := by
    intro q hq hh
    by_cases hb : b ∈ q
    · obtain ⟨s, hs, y, hy, hsy⟩ := hloc q hq hh hb
      exact ⟨s, hs, ⟨y, hy⟩, Subtype.ext hsy⟩
    · exact ⟨a, fun haq => hb (hab q hq haq), ⟨x, hx⟩, rfl⟩
  obtain ⟨y, hy⟩ := smul_of_height_one ha (⟨x, hx⟩ : M) hloc'
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

end PositivityTheory.HtPt.Gc
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GdSplit
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Gd

private theorem isTorsionFree_of_projective {A P : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    [Module.Projective A P] : Module.IsTorsionFree A P := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective A P›
  have hinj : Function.Injective s :=
    Function.LeftInverse.injective (g := Finsupp.linearCombination A id)
      (fun x => LinearMap.congr_fun hs x)
  refine ⟨fun r hr p p' h => hinj ?_⟩
  have h' : r • s p = r • s p' := by
    rw [← map_smul, ← map_smul]
    exact congrArg s h
  ext x
  have hx := congrArg (fun g => g x) h'
  simp only [Finsupp.smul_apply, smul_eq_mul] at hx
  exact hr.left hx

theorem inj_mod_of_surj_mod {A : Type} [CommRing A] [IsDomain A] {P : Type} [AddCommGroup P]
    [Module A P] [Module.Finite A P] [Module.IsTorsionFree A P] {N : ℕ} (a : A)
    (φ : (Fin N → A) →ₗ[A] P) (hN : (N : Cardinal) ≤ Module.rank A P)
    (hs : ∀ y, ∃ x y', y = φ x + a • y') (x : Fin N → A) (y : P) (hx : φ x = a • y) :
    ∃ x', x = a • x' := by
  haveI : Module.IsTorsionFree A (Fin N → A) := isTorsionFree_of_projective
  obtain ⟨r, hr1, hrP⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (I := Ideal.span {a}) (N := LinearMap.range φ) (Module.Finite.fg_top (R := A) (M := P)) le_rfl
    (by
      intro z _
      obtain ⟨x₀, z', rfl⟩ := hs z
      exact Submodule.add_mem_sup (LinearMap.mem_range_self φ x₀)
        (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) Submodule.mem_top))
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr1
  by_cases hr : r = 0
  · refine ⟨-(c • x), ?_⟩
    rw [smul_neg, smul_smul, mul_comm, hc, hr]
    simp
  have hrange : ∀ p : P, r • p ∈ LinearMap.range φ := fun p =>
    hrP (Submodule.smul_mem_pointwise_smul p r ⊤ Submodule.mem_top)
  let f : P →ₗ[A] LinearMap.range φ :=
    LinearMap.codRestrict (LinearMap.range φ) (r • LinearMap.id) (fun p => hrange p)
  have hf : Function.Injective f := by
    intro p p' h
    have h' : r • p = r • p' := congrArg Subtype.val h
    exact smul_right_injective P hr h'
  have hrk : (N : Cardinal) ≤ Module.rank A (LinearMap.range φ) :=
    hN.trans (LinearMap.rank_le_of_injective f hf)
  have hsum := LinearMap.rank_range_add_rank_ker φ
  rw [rank_fin_fun] at hsum
  have hker : Module.rank A (LinearMap.ker φ) = 0 := by
    have hle : Module.rank A (LinearMap.range φ) ≤ N := by
      rw [← hsum]
      exact le_self_add
    rw [le_antisymm hle hrk, add_comm] at hsum
    exact (Cardinal.add_right_inj_of_lt_aleph0 Cardinal.natCast_lt_aleph0).mp (by rw [hsum, zero_add])
  have hinj : Function.Injective φ := LinearMap.ker_eq_bot.mp (Submodule.rank_eq_zero.mp hker)
  obtain ⟨z, hz⟩ := hrange y
  have hxz : r • x = a • z :=
    hinj (by rw [map_smul, map_smul, hx, hz, smul_smul, smul_smul, mul_comm])
  refine ⟨z - c • x, ?_⟩
  rw [smul_sub, ← hxz, smul_smul, ← sub_smul, mul_comm a c, hc]
  simp

theorem split_exact : ∀ (A : Type) [CommRing A] [IsDomain A] (P₁ P₂ : Type) [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁] [AddCommGroup P₂] [Module A P₂] [Module.Finite A P₂] [Module.Projective A P₂] (N : ℕ) (a : A) (i : P₁ →ₗ[A] (Fin N → A)) (r : (Fin N → A) →ₗ[A] P₁) (q : (Fin N → A) →ₗ[A] P₂), Module.finrank A P₁ + Module.finrank A P₂ = N → (∀ w, ∃ w', r (i w) = w + a • w') → (∀ y, ∃ x y', y = q x + a • y') → (∀ w, ∃ y, q (i w) = a • y) → ∀ x, (∃ y, q x = a • y) → ∃ w x', x = i w + a • x' := by
  intro A _ _ P₁ P₂ _ _ _ _ _ _ _ _ N a i r q hrank hri hq hqi x hx
  haveI : Module.IsTorsionFree A (P₁ × P₂) := isTorsionFree_of_projective
  have hN : (N : Cardinal) ≤ Module.rank A (P₁ × P₂) := by
    rw [← hrank, Nat.cast_add, Module.finrank_eq_rank, Module.finrank_eq_rank]
    exact rank_add_rank_le_rank_prod A P₁
  have hs : ∀ y : P₁ × P₂, ∃ x y', y = (r.prod q) x + a • y' := by
    rintro ⟨w, y⟩
    obtain ⟨x₀, y₀, rfl⟩ := hq y
    obtain ⟨w', hw'⟩ := hri (w - r x₀)
    obtain ⟨y'', hy''⟩ := hqi (w - r x₀)
    refine ⟨x₀ + i (w - r x₀), (-w', y₀ - y''), Prod.ext ?_ ?_⟩
    · show w = r (x₀ + i (w - r x₀)) + a • -w'
      rw [map_add, hw', smul_neg]
      abel
    · show q x₀ + a • y₀ = q (x₀ + i (w - r x₀)) + a • (y₀ - y'')
      rw [map_add, hy'', smul_sub]
      abel
  obtain ⟨w', hw'⟩ := hri (r x)
  obtain ⟨y'', hy''⟩ := hqi (r x)
  obtain ⟨y, hy⟩ := hx
  have hφ : (r.prod q) (x - i (r x)) = a • (-w', y - y'') := by
    refine Prod.ext ?_ ?_
    · show r (x - i (r x)) = a • -w'
      rw [map_sub, hw', smul_neg]
      abel
    · show q (x - i (r x)) = a • (y - y'')
      rw [map_sub, hy, hy'', smul_sub]
  obtain ⟨x', hx'⟩ := PositivityTheory.HtPt.Gd.inj_mod_of_surj_mod a (r.prod q) hN hs _ _ hφ
  refine ⟨r x, x', ?_⟩
  rw [← hx']
  abel

end PositivityTheory.HtPt.Gd
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GeFrame
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Ge

section
variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

noncomputable def qL (σ : E →+* K) : (Fin N → A) →ₗ[A] Ω where
  toFun := D.q σ
  map_add' x y := by simp [HTChart.q, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [HTChart.q, Finset.smul_sum, mul_smul]

theorem qL_apply (σ : E →+* K) (x : Fin N → A) : qL D σ x = D.q σ x := rfl

theorem frame_expand {σ : E →+* K} {m j k : ℕ}
    {i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)}
    {bW : Basis (Fin j) A (Module.Dual A (D.omHT (σ.comp c.toRingHom)))} {bM : Basis (Fin k) A (D.omHT σ)}
    {g : Matrix (Fin N) (Fin j ⊕ Fin k) A} (hex : D.ExactMod σ m i) (hg : D.IsFrame σ m i bW bM g)
    (x : Fin N → A) (t : Fin k → A) (y : Ω) (hy : y ∈ D.omHT σ)
    (e : D.q σ x = ∑ a, t a • (bM a : Ω) + ((p : A) ^ m) • y) :
    ∃ (s : Fin j → A) (z : Fin N → A), x = g.mulVec (Sum.elim s t) + ((p : A) ^ m) • z := by
  obtain ⟨hcol1, hcol2⟩ := hg
  choose x'' hx'' using hcol1
  choose yM hyM hq using hcol2
  have hx1 : ∃ y₁ ∈ D.omHT σ, D.q σ (x - ∑ a, t a • (fun l => g l (Sum.inr a))) = ((p : A) ^ m) • y₁ := by
    refine ⟨y - ∑ a, t a • yM a, ?_, ?_⟩
    · exact Submodule.sub_mem _ hy (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hyM a))
    · rw [← qL_apply, map_sub, map_sum]
      simp only [map_smul, qL_apply, hq, e, smul_add, Finset.sum_add_distrib, smul_sub, Finset.smul_sum]
      simp only [smul_comm (t _) ((p : A) ^ m)]
      abel
  obtain ⟨w, x', hw⟩ := (hex.2.1 _).1 hx1
  refine ⟨bW.repr w, x' - ∑ b, bW.repr w b • x'' b, ?_⟩
  have hiw : i w = ∑ b, bW.repr w b • i (bW b) := by
    conv_lhs => rw [← bW.sum_repr w]
    rw [map_sum]
    simp only [map_smul]
  have hcolL : ∀ b, i (bW b) = (fun l => g l (Sum.inl b)) - ((p : A) ^ m) • x'' b := fun b => by
    rw [hx'' b]
    abel
  have hx : x = ∑ a, t a • (fun l => g l (Sum.inr a)) + i w + ((p : A) ^ m) • x' := by
    rw [add_assoc, ← hw]
    abel
  rw [hx, hiw]
  simp only [hcolL]
  ext l
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
  ring_nf
  have s1 : ∑ x, g l (Sum.inl x) * (bW.repr w) x = ∑ x, (bW.repr w) x * g l (Sum.inl x) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have s2 : ∑ x, g l (Sum.inr x) * t x = ∑ x, t x * g l (Sum.inr x) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have s3 : ∑ x, (p : A) ^ m * (bW.repr w) x * x'' x l = ∑ x, (bW.repr w) x * (p : A) ^ m * x'' x l :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [s1, s2, s3]
  ring

end

theorem frame_exists : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (σ : E →+* K) (m j k : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)) (bW : Basis (Fin j) A (Module.Dual A (D.omHT (σ.comp c.toRingHom)))) (bM : Basis (Fin k) A (D.omHT σ)) (eqv : Fin j ⊕ Fin k ≃ Fin N), (∀ x, D.q σ x ∈ D.omHT σ) → D.ExactMod σ m i → (∃ g, D.IsFrame σ m i bW bM g) ∧ ∀ g, D.IsFrame σ m i bW bM g → ∃ h r : A, (g.submatrix id eqv.symm).det * h = 1 + (p : A) ^ m * r := by
  intro A K _ _ _ _ _ E _ _ c _ p R N _ Ω _ _ _ _ D σ m j k i bW bM eqv hqM hex
  refine ⟨?_, fun g hg => ?_⟩
  · have h3 : ∀ a : Fin k, ∃ x : Fin N → A, ∃ y ∈ D.omHT σ, D.q σ x = (bM a : Ω) + ((p : A) ^ m) • y := by
      intro a
      obtain ⟨x, y', hy', he⟩ := hex.2.2 (bM a) (bM a).2
      refine ⟨x, -y', Submodule.neg_mem _ hy', ?_⟩
      rw [he, smul_neg]
      abel
    choose xs ys hys hxs using h3
    refine ⟨Matrix.of fun l c => Sum.elim (fun a => i (bW a) l) (fun a => xs a l) c, fun a => ⟨0, ?_⟩,
      fun a => ⟨ys a, hys a, ?_⟩⟩
    · funext l
      simp
    · simpa using hxs a
  · have hsurj : ∀ x : Fin N → A, ∃ v : Fin j ⊕ Fin k → A, ∃ z : Fin N → A,
        x = g.mulVec v + ((p : A) ^ m) • z := by
      intro x
      obtain ⟨s, z, hz⟩ := frame_expand D hex hg x (bM.repr ⟨D.q σ x, hqM x⟩) 0 (Submodule.zero_mem _) (by
        rw [smul_zero, add_zero]
        have h5 := congrArg Subtype.val (bM.sum_repr ⟨D.q σ x, hqM x⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h5
        exact h5.symm)
      exact ⟨_, z, hz⟩
    choose v z hvz using fun l : Fin N => hsurj (Pi.single l 1)
    have hprod : g.submatrix id eqv.symm * Matrix.of (fun c l => v l (eqv.symm c)) =
        1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) := by
      ext l l'
      rw [Matrix.mul_apply]
      simp only [Matrix.submatrix_apply, id, Matrix.of_apply]
      have e1 : ∑ c, g l (eqv.symm c) * v l' (eqv.symm c) = (g.mulVec (v l')) l := by
        rw [Matrix.mulVec, dotProduct]
        exact Equiv.sum_comp eqv.symm (fun d => g l d * v l' d)
      rw [e1, eq_sub_of_add_eq (hvz l').symm]
      simp [Matrix.one_apply, Pi.single_apply]
    have hmem : (1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) : Matrix (Fin N) (Fin N) A).det - 1 ∈
        Ideal.span {((p : A) ^ m)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det, sub_eq_zero]
      have e2 : (Ideal.Quotient.mk (Ideal.span {((p : A) ^ m)})).mapMatrix
          (1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) : Matrix (Fin N) (Fin N) A) = 1 := by
        ext a b
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub,
          map_mul, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), zero_mul, sub_zero,
          Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [e2, Matrix.det_one]
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨(Matrix.of (fun c l => v l (eqv.symm c)) : Matrix (Fin N) (Fin N) A).det, r, ?_⟩
    rw [← Matrix.det_mul, hprod]
    linear_combination (-1 : A) * hr

end PositivityTheory.HtPt.Ge
end

