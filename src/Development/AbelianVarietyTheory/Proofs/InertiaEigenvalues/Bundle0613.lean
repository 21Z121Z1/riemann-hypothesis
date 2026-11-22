import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0117
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0156
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0602
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0599
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeIdempotentPositionInvolutionStable
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial

theorem exists_isIntegral_pow_smul : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ x : B.A,
    ∃ k : ℕ, IsIntegral K.O ((al K a ^ k) • x) := GlobalTheory.T.exists_isIntegral_smallElement_pow_smul

theorem isIntegral_or_of_fieldFactor : ∀ (K : UQ) (B : InvAlg K) (f y z : B.A), IsIdempotentElem f →
    (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) → f * y * z = f →
    IsIntegral K.O (f * y) ∨ IsIntegral K.O (f * z) := GlobalTheory.T.isIntegral_or_isIntegral_inv_in_fieldFactor

theorem exists_pow_smul_mem_adjoin_g : ∀ (K : UQ) (B : InvAlg K) (a : K.O), B.P.Separable → K.Small a →
    ∃ N : ℕ, ∀ r : B.A, IsIntegral K.O r → (al K a ^ N) • r ∈ Algebra.adjoin K.O {B.g} := GlobalTheory.T.exists_pow_smul_mem_adjoin_gen_of_separable

variable {K : UQ} (B : InvAlg K)

theorem al_ne (a : K.O) (ha : K.Small a) : al K a ≠ 0 := by
  intro h
  exact ha.1 ((IsFractionRing.injective K.O K.E) (by simpa using h))

theorem isIntegral_sigma {r : B.A} (hr : IsIntegral K.O r) : IsIntegral K.O (B.σ r) := by
  obtain ⟨q, hq, h0⟩ := hr
  have hsub : ∀ x : K.O, K.c (algebraMap K.O K.E x) ∈ (algebraMap K.O K.E).range := fun x => by
    obtain ⟨y, hy⟩ := K.c_int x; exact ⟨y, hy.symm⟩
  let ψ : K.O ≃+* (algebraMap K.O K.E).range :=
    RingEquiv.ofBijective (algebraMap K.O K.E).rangeRestrict
      ⟨fun x y h => IsFractionRing.injective K.O K.E (congrArg Subtype.val h), (algebraMap K.O K.E).rangeRestrict_surjective⟩
  let cO : K.O →+* K.O := ψ.symm.toRingHom.comp
    (((K.c : K.E →+* K.E).comp (algebraMap K.O K.E)).codRestrict _ hsub)
  have hcO : ∀ x, algebraMap K.O K.E (cO x) = K.c (algebraMap K.O K.E x) := fun x => by
    have := ψ.apply_symm_apply ⟨K.c (algebraMap K.O K.E x), hsub x⟩
    exact congrArg Subtype.val this
  have hcomp : (algebraMap K.O B.A).comp cO = (B.σ : B.A →+* B.A).comp (algebraMap K.O B.A) := by
    ext x
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, IsScalarTower.algebraMap_apply K.O K.E B.A x, B.σ_alg, hcO]
  refine ⟨q.map cO, hq.map cO, ?_⟩
  rw [eval₂_map, hcomp]
  have := hom_eval₂ q (algebraMap K.O B.A) (B.σ : B.A →+* B.A) r
  rw [h0, map_zero] at this
  exact this.symm

theorem sigma_smul (c : K.E) (x : B.A) : B.σ (c • x) = K.c c • B.σ x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, B.σ_alg]

theorem isIntegral_idem {f : B.A} (hf : IsIdempotentElem f) : IsIntegral K.O f :=
  ⟨X ^ 2 - X, by
    have : (X ^ 2 - X : K.O[X]) = X ^ 2 - C 1 * X ^ 1 := by simp
    rw [this]; exact monic_X_pow_sub (by simp), by simp [sq, hf.eq]⟩

theorem isIntegral_pow_smul (a : K.O) (n : ℕ) {x : B.A} (hx : IsIntegral K.O x) :
    IsIntegral K.O ((al K a ^ n) • x) := by
  have : (al K a ^ n) • x = algebraMap K.O B.A (a ^ n) * x := by
    simp only [al, Algebra.smul_def, IsScalarTower.algebraMap_apply K.O K.E B.A, map_pow]
  rw [this]; exact isIntegral_algebraMap.mul hx

theorem not_isIntegral_inv_smul (a : K.O) (ha : K.Small a) {f : B.A} (hf : IsIdempotentElem f)
    (hf0 : f ≠ 0) : ¬ IsIntegral K.O ((al K a ^ (-1 : ℤ)) • f) := by
  intro h
  let I : Ideal B.A := Ideal.span {1 - f}
  have hI : I ≠ ⊤ := by
    intro hT
    have : (1 : B.A) ∈ I := hT ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 this
    apply hf0
    calc f = f * (c * (1 - f)) := by rw [hc, mul_one]
      _ = c * (f - f * f) := by ring
      _ = 0 := by rw [hf.eq, sub_self, mul_zero]
  haveI : Nontrivial (B.A ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have hmk : Ideal.Quotient.mk I f = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), eq_comm, Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have h2 : IsIntegral K.O (algebraMap K.E (B.A ⧸ I) (al K a ^ (-1 : ℤ))) := by
    have := h.map (Ideal.Quotient.mkₐ K.O I)
    rwa [Ideal.Quotient.mkₐ_eq_mk, Algebra.smul_def, map_mul, hmk, mul_one,
      Ideal.Quotient.mk_algebraMap] at this
  have h3 : IsIntegral K.O (al K a ^ (-1 : ℤ)) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom K.O K.E (B.A ⧸ I))
      (algebraMap K.E (B.A ⧸ I)).injective).1 h2
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  have hne := al_ne a ha
  have h4 : algebraMap K.O K.E (a * t) = algebraMap K.O K.E 1 := by
    rw [map_mul, ht, map_one, zpow_neg_one]; exact mul_inv_cancel₀ hne
  have h5 : a * t = 1 := IsFractionRing.injective K.O K.E h4
  exact (IsLocalRing.mem_maximalIdeal a).1 ha.2.1 (⟨⟨a, t, h5, by rw [mul_comm]; exact h5⟩, rfl⟩)

theorem smul_mem_of_adjoin (M : Submodule K.O B.A) (hM : ∀ y ∈ M, B.g * y ∈ M) {s : B.A}
    (hs : s ∈ Algebra.adjoin K.O {B.g}) : ∀ m ∈ M, s * m ∈ M := by
  let T : Subalgebra K.O B.A :=
    { carrier := {s | ∀ m ∈ M, s * m ∈ M}
      mul_mem' := fun {x y} hx hy m hm => by rw [mul_assoc]; exact hx _ (hy m hm)
      one_mem' := fun m hm => by rw [one_mul]; exact hm
      add_mem' := fun {x y} hx hy m hm => by rw [add_mul]; exact M.add_mem (hx m hm) (hy m hm)
      zero_mem' := fun m hm => by rw [zero_mul]; exact M.zero_mem
      algebraMap_mem' := fun c m hm => by rw [← Algebra.smul_def]; exact M.smul_mem c hm }
  have : Algebra.adjoin K.O {B.g} ≤ T := Algebra.adjoin_le (by
    intro x hx; rw [Set.mem_singleton_iff.1 hx]; exact hM)
  exact this hs

theorem exists_pos : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι)
    (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S →
    ∃ N : ℕ, ∀ M ∈ B.Lin, ∃ p : ι → ℤ, Pos B a e N M p := by
  intro K B ι _ e π S a hP ha hF
  obtain ⟨N0, hN0⟩ := exists_pow_smul_mem_adjoin_g K B a hP ha
  refine ⟨N0 + 1, fun M hM => ?_⟩
  set t := al K a with ht_def
  have ht : t ≠ 0 := al_ne a ha
  have hct : K.c t = t := ha.2.2
  have hRM : ∀ r : B.A, IsIntegral K.O r → ∀ m ∈ M, (t ^ N0) • (r * m) ∈ M := fun r hr m hm => by
    rw [← smul_mul_assoc]; exact smul_mem_of_adjoin B M hM.2.1 (hN0 r hr) m hm
  have core : ∀ f : B.A, IsIdempotentElem f → (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) →
      ∀ (q : ℤ) (m : B.A), m ∈ M → ¬ IsIntegral K.O ((t ^ (-q)) • (f * m)) →
      ∀ r : B.A, IsIntegral K.O r → (t ^ (q + N0)) • (f * r) ∈ M := by
    intro f hf hfld q m hm hni r hr
    have hy0 : f * ((t ^ (-q)) • m) ≠ 0 := by
      intro h0; apply hni; rw [← mul_smul_comm, h0]; exact isIntegral_zero
    obtain ⟨z, hz⟩ := hfld _ hy0
    have hfz : IsIntegral K.O (f * z) := by
      rcases isIntegral_or_of_fieldFactor K B f ((t ^ (-q)) • m) z hf hfld hz with h | h
      · exact (hni (by rwa [mul_smul_comm] at h)).elim
      · exact h
    have key : (t ^ (q + N0)) • (f * r) = (t ^ N0) • ((r * (f * z)) * m) := by
      have e1 : f * r = (t ^ (-q)) • ((r * (f * z)) * m) := by
        calc f * r = r * (f * ((t ^ (-q)) • m) * z) := by rw [hz]; ring
          _ = _ := by simp only [Algebra.smul_def]; ring
      rw [e1, smul_smul, ← zpow_add₀ ht, show q + N0 + -q = (N0 : ℤ) by ring, zpow_natCast]
    rw [key]; exact hRM _ (hr.mul hfz) m hm
  have hpos : ∀ i, ∃ pi : ℤ, (∀ r : B.A, IsIntegral K.O r → (t ^ (pi + ↑(N0 + 1))) • (e i * r) ∈ M) ∧
      ∀ m ∈ M, IsIntegral K.O ((t ^ (-pi)) • (e i * m)) := by
    intro i
    obtain ⟨f, hf, hf0, hfld, hS, hnS⟩ := hF.1.2 i
    have hfe : f * e i = f := by
      by_cases hi : i ∈ S
      · rw [(hS hi).1, hf.eq]
      · rw [(hnS hi).2, mul_add, hf.eq, (hnS hi).1, add_zero]
    let P : Set ℤ := {p | ∀ m ∈ M, IsIntegral K.O ((t ^ (-p)) • (e i * m))}
    have hne : P.Nonempty := by
      obtain ⟨s, hs⟩ := hM.1.1
      choose k hk using fun x : B.A => exists_isIntegral_pow_smul K B a ha (e i * x)
      refine ⟨-((s.sup k : ℕ) : ℤ), fun m hm => ?_⟩
      rw [neg_neg, zpow_natCast]
      rw [← hs] at hm
      induction hm using Submodule.span_induction with
      | mem x hx =>
        have hle : k x ≤ s.sup k := Finset.le_sup hx
        rw [← Nat.sub_add_cancel hle, pow_add, ← smul_smul]
        exact isIntegral_pow_smul B a _ (hk x)
      | zero => rw [mul_zero, smul_zero]; exact isIntegral_zero
      | add x y _ _ hx hy => rw [mul_add, smul_add]; exact hx.add hy
      | smul c x _ hx =>
        rw [Algebra.smul_def c x, ← mul_assoc, mul_comm (e i), mul_assoc, ← mul_smul_comm]
        exact isIntegral_algebraMap.mul hx
    have hbdd : BddAbove P := by
      have hm0 : ∃ m ∈ M, f * m ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have hle : Submodule.span K.E (M : Set B.A) ≤ LinearMap.ker (LinearMap.mulLeft K.E f) := by
          rw [Submodule.span_le]; intro m hm; exact hcon m hm
        rw [hM.1.2] at hle
        have := hle (Submodule.mem_top : (1 : B.A) ∈ ⊤)
        simp at this; exact hf0 this
      obtain ⟨m0, hm0, hfm0⟩ := hm0
      obtain ⟨z, hz⟩ := hfld m0 hfm0
      obtain ⟨k, hk⟩ := exists_isIntegral_pow_smul K B a ha (f * z)
      refine ⟨k, fun p hp => ?_⟩
      by_contra hlt
      push_neg at hlt
      have h1 : IsIntegral K.O ((t ^ (-p)) • (e i * m0)) := hp m0 hm0
      have h2 : IsIntegral K.O ((t ^ (-p)) • (e i * m0) * (t ^ k • (f * z)) * f) :=
        (h1.mul hk).mul (isIntegral_idem B hf)
      have hq : e i * m0 * (f * z) * f = f := by
        calc e i * m0 * (f * z) * f = (f * e i) * m0 * z * f := by ring
          _ = f := by rw [hfe, hz, hf.eq]
      have h3 : (t ^ (-p)) • (e i * m0) * (t ^ k • (f * z)) * f = (t ^ ((k : ℤ) - p)) • f := by
        rw [sub_eq_add_neg, zpow_add₀ ht, zpow_natCast]
        simp only [Algebra.smul_def, map_mul]
        linear_combination (algebraMap K.E B.A (t ^ (-p)) * algebraMap K.E B.A (t ^ k)) * hq
      have h4 : (t ^ (-1 : ℤ)) • f = (t ^ ((p - k - 1 : ℤ).toNat)) • ((t ^ ((k : ℤ) - p)) • f) := by
        rw [smul_smul, ← zpow_natCast, ← zpow_add₀ ht, Int.toNat_of_nonneg (by omega),
          show (p - k - 1 : ℤ) + (k - p) = -1 by ring]
      exact not_isIntegral_inv_smul B a ha hf hf0 (h4 ▸ isIntegral_pow_smul B a _ (h3 ▸ h2))
    obtain ⟨pi, hmem, hnot⟩ : ∃ pi, pi ∈ P ∧ pi + 1 ∉ P :=
      ⟨sSup P, Int.csSup_mem hne hbdd, fun h => by have := le_csSup hbdd h; omega⟩
    refine ⟨pi, fun r hr => ?_, hmem⟩
    have hnot' : ¬ ∀ m ∈ M, IsIntegral K.O ((t ^ (-(pi + 1))) • (e i * m)) := hnot
    push_neg at hnot'
    obtain ⟨m, hm, hni⟩ := hnot'
    have hexp : pi + ↑(N0 + 1) = (pi + 1) + N0 := by push_cast; ring
    rw [hexp]
    by_cases hi : i ∈ S
    · rw [(hS hi).1] at hni ⊢
      exact core f hf hfld (pi + 1) m hm hni r hr
    · obtain ⟨hff, hei⟩ := hnS hi
      have Hf : ∀ r : B.A, IsIntegral K.O r → (t ^ (pi + 1 + N0)) • (f * r) ∈ M := by
        by_cases h1 : IsIntegral K.O ((t ^ (-(pi + 1))) • (f * m))
        · have h2 : ¬ IsIntegral K.O ((t ^ (-(pi + 1))) • (B.σ f * m)) := by
            intro h2; apply hni; rw [hei, add_mul, smul_add]; exact h1.add h2
          have h3 : ¬ IsIntegral K.O ((t ^ (-(pi + 1))) • (f * B.σ m)) := by
            intro h3; apply h2
            have := isIntegral_sigma B h3
            rwa [sigma_smul, map_mul, B.σ_σ, map_zpow₀, hct] at this
          exact core f hf hfld (pi + 1) (B.σ m) (hM.2.2 m hm) h3
        · exact core f hf hfld (pi + 1) m hm h1
      rw [hei, add_mul, smul_add]
      refine M.add_mem (Hf r hr) ?_
      have := hM.2.2 _ (Hf (B.σ r) (isIntegral_sigma B hr))
      rwa [sigma_smul, map_mul, B.σ_σ, map_zpow₀, hct] at this
  choose p hp using hpos
  exact ⟨p, hp⟩

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTeichmullerPowSemistablePeriods
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LogFlat

theorem rootT_cocycle_of_pow_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (g : GQ l) (y ϖ x : Per.Fl l) (n : ℕ) (a b : ℤ_[l]),
    y ^ n = ϖ * x → ϖ.untilt ≠ 0 →
    (∀ m, rootT (Per.σF g y) m = rootT C.ε m ^ (PadicInt.toZModPow m a).val * rootT y m) →
    (∀ m, rootT (Per.σF g ϖ) m = rootT C.ε m ^ (PadicInt.toZModPow m b).val * rootT ϖ m) →
    ∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m ((n : ℤ_[l]) * a - b)).val * rootT x m := by
  intro l _ C g y ϖ x n a b hyx hϖ ha hb m
  have hmul : ∀ u v : Per.Fl l, rootT (u * v) m = rootT u m * rootT v m := by
    intro u v; simp only [rootT, iterate_map_mul, map_mul]
  have hpow : ∀ u : Per.Fl l, rootT (u ^ n) m = rootT u m ^ n := by
    intro u; simp only [rootT, iterate_map_pow, map_pow]
  have hζ : rootT C.ε m ^ (l ^ m) = 1 := by
    rw [rootT_pow_eq_untilt]; exact (core_isEps l C).1
  have hϖm : rootT ϖ m ≠ 0 := by
    intro h0; apply hϖ; rw [← rootT_pow_eq_untilt, h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
  have hζ0 : ∀ k : ℕ, rootT C.ε m ^ k ≠ 0 := by
    intro k h0
    have : rootT C.ε m = 0 := pow_eq_zero_iff'.mp h0 |>.1
    rw [this, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hζ
    exact zero_ne_one hζ
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set A := (PadicInt.toZModPow m a).val
  set B := (PadicInt.toZModPow m b).val
  set Cc := (PadicInt.toZModPow m ((n : ℤ_[l]) * a - b)).val
  have hexp : rootT C.ε m ^ (n * A) = rootT C.ε m ^ (B + Cc) := by
    rw [pow_eq_pow_mod (n * A) hζ, pow_eq_pow_mod (B + Cc) hζ]
    congr 1
    rw [← ZMod.natCast_eq_natCast_iff']
    simp only [A, B, Cc, Nat.cast_mul, Nat.cast_add, ZMod.natCast_val, ZMod.cast_id', id, map_sub, map_mul,
      map_natCast]
    ring
  have h1 : rootT ((Per.σF g y) ^ n) m = rootT (Per.σF g ϖ * Per.σF g x) m := by
    rw [← map_pow, ← map_mul, hyx]
  rw [hpow, hmul, ha, hb, mul_pow, ← pow_mul, ← hpow y, hyx, hmul, mul_comm A n, hexp] at h1
  have h2 : rootT C.ε m ^ B * (rootT ϖ m * rootT ((Per.σF g) x) m) =
      rootT C.ε m ^ B * (rootT ϖ m * (rootT C.ε m ^ Cc * rootT x m)) := by
    rw [pow_add] at h1; linear_combination -h1
  have h3 := mul_left_cancel₀ (hζ0 B) h2
  exact mul_left_cancel₀ hϖm h3

theorem rootT_σF_tilt_l : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (C : Core l), C.ζ = P.ζQ → ∀ ϖ : Per.Fl l,
    (∀ m : ℕ, (rootT ϖ m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (lRoot l m)) → ∀ (g : GQ l) (m : ℕ),
    rootT (Per.σF g ϖ) m = rootT C.ε m ^ (PadicInt.toZModPow m (kummer P g)).val * rootT ϖ m := by
  intro l _ P C hζ ϖ hr g m
  have hit : ∀ k : ℕ, ((frobeniusEquiv (Per.Fl l) l).symm)^[k] (Per.σF g ϖ) =
      Per.σF g (((frobeniusEquiv (Per.Fl l) l).symm)^[k] ϖ) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]
  have hsig : rootT (Per.σF g ϖ) m = Per.σO g (rootT ϖ m) := by
    rw [rootT, hit, GlobalTheory.RingBasics.untilt_σF]; rfl
  rw [hsig]
  apply Subtype.ext
  have h1 : ((Per.σO g (rootT ϖ m) : Per.OC l) : ℂ_[l]) = Per.σC g (rootT ϖ m : ℂ_[l]) :=
    GlobalTheory.RingIface.sigO_coe l g _
  have h2 : Per.σC g (algebraMap (Om l) ℂ_[l] (lRoot l m)) = algebraMap (Om l) ℂ_[l] (g (lRoot l m)) :=
    GlobalTheory.RingBasics.σC_coe g _
  push_cast
  rw [h1, hr, h2, isKummer_kummer P g m, map_mul, map_pow, C.ε_root, hζ]

theorem exists_log_flat_pow_Bst : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (_ : True), ∃ (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) ∧ (∀ g, bk.FixFlat g → c g = 0) ∧ ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m := by
  intro l _ K bk P AI T C hF _
  obtain ⟨ϖ, hr⟩ := GlobalTheory.Pst.NoLog.exists_tilt (lRoot l) (lRoot_succ l) l (lRoot_zero l)
  have hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l) := Subtype.ext (by
    have := hr 0
    rw [lRoot_zero, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  obtain ⟨x, hxu, hx⟩ := GlobalTheory.T.tilt_uniformizer_pow_eq_mul_unit l K bk ϖ hϖ
  obtain ⟨cπ, hcπ, hfix⟩ := GlobalTheory.T.exists_kummer_cocycle_tilt_uniformizer l K bk C
  obtain ⟨bx, hφ, hgal⟩ := GlobalTheory.T.exists_teichmuller_log_unit_bcris l C x hxu
  have hϖ0 : ϖ.untilt ≠ 0 := by
    rw [hϖ]; exact_mod_cast (Fact.out : l.Prime).ne_zero
  refine ⟨T.eB.symm bx, fun g => (bk.Ep.natDegree : ℤ_[l]) * cπ g, ⟨fun g => ?_, ?_⟩,
    fun g hg => by simp [hfix g hg], GlobalTheory.T.exists_truncLog_gal_mod_filP l K bk C cπ hcπ⟩
  · have hx' := rootT_cocycle_of_pow_eq_mul l C (g : GQ l) bk.flat ϖ x bk.Ep.natDegree (cπ g) (kummer P g) hx hϖ0 (hcπ g)
      (rootT_σF_tilt_l l P C hF.ζ ϖ hr g)
    have h1 := hgal (g : GQ l) _ hx'
    have h2 : P.actQ (g : GQ l) (T.eB.symm bx) = T.eB.symm bx +
        (((bk.Ep.natDegree : ℤ_[l]) * cπ g - kummer P g : ℤ_[l]) : ℚ_[l]) • P.tB := by
      apply T.eB.injective
      rw [T.actB, RingEquiv.apply_symm_apply, h1, map_add, RingEquiv.apply_symm_apply, Algebra.smul_def, map_mul,
        T.zB, hF.t]
    rw [map_add, actSt_X, actSt_C, h2, Polynomial.C_add]
    have key : ((kummer P (g : GQ l) : ℤ_[l]) : ℚ_[l]) • P.tB +
        (((bk.Ep.natDegree : ℤ_[l]) * cπ g - kummer P g : ℤ_[l]) : ℚ_[l]) • P.tB =
        (((bk.Ep.natDegree : ℤ_[l]) * cπ g : ℤ_[l]) : ℚ_[l]) • P.tB := by
      rw [← add_smul]; congr 1; push_cast; ring
    show _ = _ + Polynomial.C ((((bk.Ep.natDegree : ℤ_[l]) * cπ g : ℤ_[l]) : ℚ_[l]) • P.tB)
    rw [← key, Polynomial.C_add]; ring
  · have h2 : P.φB (T.eB.symm bx) = (l : P.R.B) * T.eB.symm bx := by
      apply T.eB.injective
      rw [T.frob, RingEquiv.apply_symm_apply, hφ, map_mul, map_natCast, RingEquiv.apply_symm_apply]
    rw [map_add, phiSt_X, phiSt_C, h2, mul_add, Polynomial.C_mul, map_natCast]

end GlobalTheory.LogFlat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FischerInnerFormFockSubstitutionUnitaryInvariantStatement
section
open Formalism.BasicNotions Formalism.IndefR.Datum Formalism.IndefR.Links
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischerInnerForm_fockSubstitution_unitary_invariant : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ P Q : PolF D m n, GlobalTheory.FockIsotypic.fis (GlobalTheory.ExportSeries.fockSubst p U P) (GlobalTheory.ExportSeries.fockSubst p U Q) = GlobalTheory.FockIsotypic.fis P Q := by
  first | exact @GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary | exact GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary | (intros; apply GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineDcrisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedCoefficientChains_adm11 : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm11 D := by
  first | exact @GlobalTheory.Per.DcrisExact.fontaine_dcris | exact GlobalTheory.Per.DcrisExact.fontaine_dcris | (intros; apply GlobalTheory.Per.DcrisExact.fontaine_dcris <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPeriodMemNonZeroDivisorsDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem per_ne_zero {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) {τ : Ainf l} (h : bk.IsPer τ) : τ ≠ 0 := by
  rintro rfl
  obtain ⟨-, ε, η, hε, hφ⟩ := h
  rw [map_zero] at hφ
  have h1 : WittVector.teichmuller l ε - 1 = 0 := (Units.mul_right_eq_zero η).1 hφ.symm
  have h2 : ε = 1 := by
    have := congrArg (fun w => WittVector.coeff w 0) (sub_eq_zero.1 h1)
    simpa using this
  subst h2
  exact hε.2 (by simp)

theorem iA_per_mem_nonZeroDivisors : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l),
    bk.IsPer τ → bk.iA τ ∈ nonZeroDivisors (bk.DA bk.ρ₀) := by
  intro l _ K bk τ hτ
  obtain ⟨h0, h1, -, -⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk (Ainf l) bk.ev
  haveI : IsDomain (bk.DA bk.ρ₀) := (discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [← map_zero bk.iA]
  exact fun h => per_ne_zero bk hτ (hinj h)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FubiniCutoffIntegralGeneralLinearTorus
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem sigmaFinite_comap_of_measurable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (f : X → Y)
    (hf : Measurable f) (μ : Measure Y) [SigmaFinite μ] : SigmaFinite (μ.comap f) := by
  by_cases h : Function.Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ
  · refine ⟨⟨⟨fun n => f ⁻¹' spanningSets μ n, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
    · rw [Measure.comap_apply₀ f μ h.1 h.2 ((measurableSet_spanningSets μ n).preimage hf).nullMeasurableSet]
      exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top μ n)
    · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]
  · rw [Measure.comap, dif_neg h]; infer_instance

theorem fubini_cutoff : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (M : Meas r F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (α : GL (Fin r) F → ℝ) (Φ : GL (Fin r) F → ℂ), IsTest Φ → IsLocallyConstant α → HasCompactSupport α → (∀ g, 0 ≤ α g) → ∀ c : GL (Fin r) F, (∀ g, Φ g ≠ 0 → ∫ s, α (g * c * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1) → ∫ s, (letI := M.mG; ∫ g, Φ g * (α (g * c * LinDesc.tm A hG s) : ℂ) ∂M.μG) ∂(LinDesc.unitsMeas A μK) = (letI := M.mG; ∫ g, Φ g ∂M.μG) := by
  intro F E _ _ _ _ _ A r τ p hG M μK hμK α Φ hΦ hαlc hαcs hα0 c h1
  letI := M.mG
  haveI := M.bG
  haveI := M.haarG
  obtain ⟨hBor, hHaar, -⟩ := GlobalTheory.JR.LinDesc.unitsMeas_isHaar F E A μK hμK
  haveI := hBor
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology F := secondCountable_of_proper
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → F))
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin r) F) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin r) F) := Units.isEmbedding_embedProduct.t2Space
  have e := (LinDesc.bas A hG).equivFun
  have he1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  haveI : SecondCountableTopology A.K := (Homeomorph.mk e.toEquiv he1 he2).secondCountableTopology
  haveI : SigmaFinite μK := inferInstance
  haveI : SigmaFinite (LinDesc.unitsMeas A μK) := by
    unfold LinDesc.unitsMeas
    haveI : SigmaFinite (μK.withDensity fun t => ENNReal.ofReal (A.absK t)⁻¹) :=
      SigmaFinite.withDensity_ofReal _
    exact sigmaFinite_comap_of_measurable _ (measurable_iff_comap_le.2 le_rfl) _
  have htm : Continuous (LinDesc.tm A hG) := Continuous.units_map _
    (IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix (LinDesc.bas A hG)).toLinearMap)
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hαc : Continuous α := hαlc.continuous
  have hC : IsCompact (tsupport Φ) := hΦ.2
  have hz : ∀ g, g ∉ tsupport Φ → Φ g = 0 := fun g hg => image_eq_zero_of_notMem_tsupport hg
  haveI : IsFiniteMeasure (M.μG.restrict (tsupport Φ)) :=
    isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  set ν := LinDesc.unitsMeas A μK with hν
  set f : A.Kˣ → GL (Fin r) F → ℂ := fun s g => Φ g * (α (g * c * LinDesc.tm A hG s) : ℂ) with hf
  have hfc : Continuous (Function.uncurry f) := by
    refine (hΦc.comp continuous_snd).mul (Complex.continuous_ofReal.comp (hαc.comp ?_))
    exact (continuous_snd.mul continuous_const).mul (htm.comp continuous_fst)
  have hin : ∀ g, Integrable (fun s => f s g) ν := by
    intro g
    by_cases hg : Φ g = 0
    · simp [hf, hg]
    · have hi : Integrable (fun s => α (g * c * LinDesc.tm A hG s)) ν :=
        Integrable.of_integral_ne_zero (by rw [h1 g hg]; exact one_ne_zero)
      exact hi.ofReal.const_mul (Φ g)
  have hnorm : ∀ g, ∫ s, ‖f s g‖ ∂ν = ‖Φ g‖ := by
    intro g
    by_cases hg : Φ g = 0
    · simp [hf, hg]
    · simp only [hf, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hα0 _)]
      rw [integral_const_mul, h1 g hg, mul_one]
  have hint : Integrable (Function.uncurry f) (ν.prod (M.μG.restrict (tsupport Φ))) := by
    rw [integrable_prod_iff' hfc.aestronglyMeasurable]
    refine ⟨Eventually.of_forall hin, ?_⟩
    exact (hΦc.norm.continuousOn.integrableOn_compact hC).congr (Eventually.of_forall fun g => (hnorm g).symm)
  have eL : ∀ s, ∫ g, f s g ∂M.μG = ∫ g in tsupport Φ, f s g ∂M.μG := fun s =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => by simp [hf, hz g hg]).symm
  have eR : ∫ g, Φ g ∂M.μG = ∫ g in tsupport Φ, Φ g ∂M.μG :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => hz g hg).symm
  show ∫ s, ∫ g, f s g ∂M.μG ∂ν = ∫ g, Φ g ∂M.μG
  simp_rw [eL, eR]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  by_cases hg : Φ g = 0
  · simp [hf, hg]
  · simp only [hf]
    rw [integral_const_mul, integral_complex_ofReal, h1 g hg, Complex.ofReal_one, mul_one]

end GlobalTheory.JR.LinDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleResidualPointDescendsCoefficientExtenStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleResidualPoint_descends_coefficientExtension : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc), LocExt N₀ N₁ A₀ A₁ i₀ i₁ → (∃ r, GoodR N₀ i₀ r) → ZDecomp N₀ i₀ → Live N₁ i₁ → Live N₀ i₀ := by
  first | exact @GlobalTheory.LiveDescent.live_of_locExt | exact GlobalTheory.LiveDescent.live_of_locExt | (intros; apply GlobalTheory.LiveDescent.live_of_locExt <;> assumption)
end

