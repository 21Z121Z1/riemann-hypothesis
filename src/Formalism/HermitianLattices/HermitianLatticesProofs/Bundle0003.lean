import Mathlib
import Formalism.HermitianLattices.StatementLat
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
section
noncomputable section

namespace Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem locDual_mem_dualAt (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) (x : V) :
    x ∈ dualAt h p L ↔ ∀ y ∈ L, h y x ∈ locR (K := K) p := by
  simp only [dualAt, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]

theorem locDual_mem_locR (p : Ideal R) (k : K) :
    k ∈ locR (K := K) p ↔
      ∃ s ∈ hcompl (K := K) p, algebraMap R K s * k ∈ (1 : Submodule R K) := by
  show (∃ s ∈ hcompl (K := K) p, s • k ∈ (1 : Submodule R K)) ↔ _
  simp only [Algebra.smul_def]

theorem locDual_h_smul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (y x : V) :
    h y (r • x) = algebraMap R K r * h y x := by
  rw [← algebraMap_smul K r x, map_smul, smul_eq_mul]

theorem locDual_h_smul_left (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (y x : V) :
    h (r • y) x = star (algebraMap R K r) * h y x := by
  rw [← algebraMap_smul K r y, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply]

theorem locDual_one_mul {a b : K} (ha : a ∈ (1 : Submodule R K)) (hb : b ∈ (1 : Submodule R K)) :
    a * b ∈ (1 : Submodule R K) := by
  simpa using Submodule.mul_mem_mul ha hb

theorem locDual_alg_mem (r : R) : algebraMap R K r ∈ (1 : Submodule R K) :=
  Submodule.algebraMap_mem r

theorem locDual_dualAt_anti (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) {L M : Submodule R V}
    (hLM : L ≤ M) : dualAt h p M ≤ dualAt h p L := by
  intro x hx
  rw [locDual_mem_dualAt] at hx ⊢
  exact fun y hy => hx y (hLM hy)

private theorem mem_dual_iff_forall_mem_one (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) (x : V) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule R K) := by
  simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

theorem locDual_loc_dual_le (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) :
    loc (K := K) p (dual h L) ≤ dualAt h p L := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ hcompl (K := K) p, s • x ∈ dual h L := hx
  rw [mem_dual_iff_forall_mem_one] at hsx
  rw [locDual_mem_dualAt]
  intro y hy
  rw [locDual_mem_locR]
  refine ⟨s, hs, ?_⟩
  rw [← locDual_h_smul_right]
  exact hsx y hy

theorem locDual_dualAt_le (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (p : Ideal R) (L : Submodule R V) (hL : L.FG) :
    dualAt h p L ≤ loc (K := K) p (dual h L) := by
  classical
  intro x hx
  rw [locDual_mem_dualAt] at hx
  obtain ⟨t, rfl⟩ := hL
  have hloc : ∀ y ∈ t, ∃ s ∈ hcompl (K := K) p,
      algebraMap R K s * h y x ∈ (1 : Submodule R K) :=
    fun y hy => (locDual_mem_locR p _).mp (hx y (Submodule.subset_span hy))
  choose! s hs hsy using hloc
  refine ⟨∏ y ∈ t, s y, Submonoid.prod_mem _ (fun y hy => hs y hy), ?_⟩
  rw [mem_dual_iff_forall_mem_one]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [locDual_h_smul_right, ← Finset.mul_prod_erase t s hy, map_mul,
      mul_comm (algebraMap R K (s y)), mul_assoc]
    exact locDual_one_mul (locDual_alg_mem _) (hsy y hy)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [locDual_h_smul_left]
    obtain ⟨u, hu⟩ := hstar r
    rw [← hu]
    exact locDual_one_mul (locDual_alg_mem u) hy

theorem locDual_sigma_mem (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) (p : Ideal R)
    (s : R) (hs : s ∈ hcompl (K := K) p) :
    locBasic_sigma hinj hstar s ∈ hcompl (K := K) p := by
  have spec : ∀ r : R, algebraMap R K (locBasic_sigma hinj hstar r) = star (algebraMap R K r) :=
    fun r => (hstar r).choose_spec
  unfold hcompl at hs ⊢
  induction hs using Submonoid.closure_induction with
  | mem s hs =>
    apply Submonoid.subset_closure
    obtain ⟨hs1, hs2⟩ := hs
    refine ⟨hs2 _ (spec s), fun t ht => ?_⟩
    rw [spec, star_star] at ht
    rw [hinj ht]
    exact hs1
  | one => rw [map_one]; exact Submonoid.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Submonoid.mul_mem _ ha hb

theorem locDual_dualAt_loc (h : V →ₗ⋆[K] V →ₗ[K] K) (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (p : Ideal R) (L : Submodule R V) :
    dualAt h p (loc (K := K) p L) = dualAt h p L := by
  apply le_antisymm
  · apply locDual_dualAt_anti
    intro y hy
    show ∃ s ∈ hcompl (K := K) p, s • y ∈ L
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hy⟩
  · intro x hx
    rw [locDual_mem_dualAt] at hx ⊢
    intro y hy
    obtain ⟨s, hs, hsy⟩ : ∃ s ∈ hcompl (K := K) p, s • y ∈ L := hy
    have h1 := hx _ hsy
    rw [locDual_h_smul_left, locDual_mem_locR] at h1
    obtain ⟨t, ht, hty⟩ := h1
    rw [locDual_mem_locR]
    refine ⟨t * locBasic_sigma hinj hstar s,
      Submonoid.mul_mem _ ht (locDual_sigma_mem hinj hstar p s hs), ?_⟩
    have spec : algebraMap R K (locBasic_sigma hinj hstar s) = star (algebraMap R K s) :=
      (hstar s).choose_spec
    rw [map_mul, spec, mul_assoc]
    exact hty

end SlopeTestRemainingChoices

theorem locDual : LocDual := by
  intro R K V _ _ _ _ _ _ _ _ _ _ h _ hstar L hL
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have key : ∀ p : Ideal R, loc (K := K) p (dual h L) = dualAt h p L := fun p =>
    le_antisymm (locDual_loc_dual_le h p L) (locDual_dualAt_le h hstar p L hL)
  have key2 : ∀ p : Ideal R, dualAt h p (loc (K := K) p L) = dualAt h p L :=
    fun p => locDual_dualAt_loc h hinj hstar p L
  refine ⟨fun p _ => ⟨key p, key2 p⟩, ?_⟩
  unfold IsUnimodular IsUnimodularAt
  constructor
  · intro hu p _
    rw [key2, ← key, hu]
  · intro H
    have H' : ∀ p : Ideal R, p.IsMaximal → loc (K := K) p (dual h L) = loc (K := K) p L := by
      intro p hp
      rw [key, ← key2]
      exact H p hp

    have avoid : ∀ p : Ideal R, p.IsPrime → ∀ s ∈ hcompl (K := K) p, s ∉ p := by
      intro p hp s hs
      unfold hcompl at hs
      induction hs using Submonoid.closure_induction with
      | mem s hs => exact hs.1
      | one => exact (Ideal.ne_top_iff_one p).mp hp.ne_top
      | mul a b _ _ ha hb => exact fun hab => (hp.mem_or_mem hab).elim ha hb

    have incl : ∀ M N : Submodule R V,
        (∀ p : Ideal R, p.IsMaximal → loc (K := K) p M = loc (K := K) p N) → N ≤ M := by
      intro M N hMN x hx
      by_contra hxM
      let I : Ideal R := M.comap (LinearMap.toSpanSingleton R V x)
      have hI : I ≠ ⊤ := by
        intro hI
        apply hxM
        have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
        simpa [I] using h1
      obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
      have hxN : x ∈ loc (K := K) m N := by
        show ∃ s ∈ hcompl (K := K) m, s • x ∈ N
        exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hx⟩
      rw [← hMN m hm] at hxN
      obtain ⟨s, hs, hsx⟩ : ∃ s ∈ hcompl (K := K) m, s • x ∈ M := hxN
      exact avoid m hm.isPrime s hs (hIm (Submodule.mem_comap.mpr (by simpa using hsx)))
    exact le_antisymm (incl _ _ (fun p hp => (H' p hp).symm)) (incl _ _ H')

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.NeighbourBasic
section
noncomputable section

namespace Formalism.HermitianLatticesTheory

section Quot

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem neighbourBasic_smul_mem {I : Ideal R} {L N : Submodule R V}
    (e : (L ⧸ N.comap L.subtype) ≃ₗ[R] (R ⧸ I)) {r : R} (hr : r ∈ I) {l : V} (hl : l ∈ L) :
    r • l ∈ N := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (e (Submodule.Quotient.mk ⟨l, hl⟩))
  have h0 : e (r • Submodule.Quotient.mk (⟨l, hl⟩ : L)) = 0 := by
    rw [map_smul, ← ha, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact I.mul_mem_right a hr
  rw [LinearEquiv.map_eq_zero_iff, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero] at h0
  exact h0

theorem neighbourBasic_gen {I : Ideal R} {L N : Submodule R V}
    (e : (L ⧸ N.comap L.subtype) ≃ₗ[R] (R ⧸ I)) :
    ∃ l₀ ∈ L, ∀ l ∈ L, ∃ a : R, l - a • l₀ ∈ N := by
  obtain ⟨x₀, hx₀⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))
  refine ⟨x₀, x₀.2, fun l hl => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (e (Submodule.Quotient.mk ⟨l, hl⟩))
  refine ⟨a, ?_⟩
  have h1 : Submodule.Quotient.mk (p := N.comap L.subtype) (⟨l, hl⟩ - a • x₀) = 0 := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hx₀, ← map_smul,
      ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, ha, LinearEquiv.symm_apply_apply,
      sub_self]
  rw [Submodule.Quotient.mk_eq_zero] at h1
  exact h1

theorem neighbourBasic_gen' {I : Ideal R} (hI : I.IsMaximal) {L N : Submodule R V}
    (e : (L ⧸ N.comap L.subtype) ≃ₗ[R] (R ⧸ I)) {l : V} (hl : l ∈ L) (hlN : l ∉ N) :
    ∀ l' ∈ L, ∃ a : R, l' - a • l ∈ N := by
  intro l' hl'
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (e (Submodule.Quotient.mk ⟨l, hl⟩))
  obtain ⟨a', ha'⟩ := Submodule.Quotient.mk_surjective _ (e (Submodule.Quotient.mk ⟨l', hl'⟩))
  have haI : a ∉ I := by
    intro haI
    apply hlN
    have : e (Submodule.Quotient.mk ⟨l, hl⟩) = 0 := by
      rw [← ha, Submodule.Quotient.mk_eq_zero]; exact haI
    rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at this
    exact this
  obtain ⟨b, i, hi, hbi⟩ := hI.exists_inv haI
  refine ⟨a' * b, ?_⟩
  have h1 : e (Submodule.Quotient.mk (p := N.comap L.subtype) (⟨l', hl'⟩ - (a' * b) • ⟨l, hl⟩))
      = 0 := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, map_sub, map_smul, ← ha, ← ha',
      ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero,
      smul_eq_mul]
    have : a' - a' * b * a = a' * i := by
      linear_combination (-a') * hbi
    rw [this]
    exact I.mul_mem_left a' hi
  rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at h1
  exact h1

theorem neighbourBasic_not_le {I : Ideal R} (hI : I ≠ ⊤) {L N : Submodule R V}
    (e : (L ⧸ N.comap L.subtype) ≃ₗ[R] (R ⧸ I)) : ∃ l ∈ L, l ∉ N := by
  by_contra H
  push Not at H
  apply hI
  obtain ⟨x₀, hx₀⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))
  have h0 : Submodule.Quotient.mk (p := N.comap L.subtype) x₀ = 0 := by
    rw [Submodule.Quotient.mk_eq_zero]; exact H x₀ x₀.2
  rw [h0, eq_comm, LinearEquiv.symm_apply_eq, map_zero] at hx₀
  rw [Submodule.Quotient.mk_eq_zero] at hx₀
  exact (Ideal.eq_top_iff_one I).mpr hx₀

end Quot

section DedekindLFunctions

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem neighbourBasic_ded (P : Ideal R) (hP : P.IsMaximal) (c c' : K)
    (hc : ∀ p ∈ P, algebraMap R K p * c ∈ Set.range (algebraMap R K))
    (hc' : ∀ p ∈ P, algebraMap R K p * c' ∈ Set.range (algebraMap R K))
    (hnc : c' ∉ Set.range (algebraMap R K)) :
    ∃ a b : R, c = algebraMap R K a + algebraMap R K b * c' := by
  by_cases hbot : P = ⊥
  · exfalso
    apply hnc
    have hF : IsField R := Ring.isField_iff_maximal_bot.mpr (hbot ▸ hP)
    exact (IsFractionRing.surjective_iff_isField (R := R) (K := K)).mpr hF c'
  let J : Ideal R :=
    { carrier := {t | ∃ p ∈ P, ∃ q ∈ P, algebraMap R K t = algebraMap R K p +
        algebraMap R K q * c'}
      add_mem' := by
        rintro x y ⟨p, hp, q, hq, hx⟩ ⟨p', hp', q', hq', hy⟩
        refine ⟨p + p', P.add_mem hp hp', q + q', P.add_mem hq hq', ?_⟩
        simp only [map_add, hx, hy]; ring
      zero_mem' := ⟨0, P.zero_mem, 0, P.zero_mem, by simp⟩
      smul_mem' := by
        rintro r x ⟨p, hp, q, hq, hx⟩
        refine ⟨r * p, P.mul_mem_left r hp, r * q, P.mul_mem_left r hq, ?_⟩
        simp only [smul_eq_mul, map_mul, hx]; ring }
  have hPJ : P ≤ J := fun p hp => ⟨p, hp, 0, P.zero_mem, by simp⟩
  by_cases hJ : J = ⊤
  · have h1 : (1 : R) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨p, hp, q, hq, h1⟩ := h1
    obtain ⟨a, ha⟩ := hc p hp
    obtain ⟨b, hb⟩ := hc q hq
    refine ⟨a, b, ?_⟩
    rw [ha, hb]
    calc c = algebraMap R K 1 * c := by simp
      _ = _ := by rw [h1]; ring
  · exfalso
    have hPJ' : P = J := hP.eq_of_le hJ hPJ
    apply hnc
    have hinj := IsFractionRing.injective R K
    let N : Submodule R K := Submodule.map (Algebra.linearMap R K) P
    have hN : N ≠ ⊥ := by
      intro h0
      apply hbot
      rw [eq_bot_iff]
      intro p hp
      have : algebraMap R K p ∈ N := Submodule.mem_map_of_mem hp
      rw [h0, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact hinj (by rw [this, map_zero])
    have hN' : N.FG := (IsNoetherian.noetherian P).map _
    have hint : IsIntegral R c' := by
      refine isIntegral_of_smul_mem_submodule N hN hN' c' ?_
      intro n hn
      obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hn
      obtain ⟨t, ht⟩ := hc' q hq
      have htJ : t ∈ J := ⟨0, P.zero_mem, q, hq, by rw [ht]; simp⟩
      rw [← hPJ'] at htJ
      refine Submodule.mem_map.mpr ⟨t, htJ, ?_⟩
      simp only [Algebra.linearMap_apply, smul_eq_mul]
      rw [ht, mul_comm]
    exact IsIntegrallyClosed.isIntegral_iff.mp hint

end DedekindLFunctions

section Main

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem neighbourBasic_h_smul_left (h : V →ₗ⋆[K] V →ₗ[K] K) (a : R) (x y : V) :
    h (a • x) y = star (algebraMap R K a) * h x y := by
  rw [← algebraMap_smul K a x, LinearMap.map_smulₛₗ₂, starRingEnd_apply, smul_eq_mul]

theorem neighbourBasic_h_smul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (a : R) (x y : V) :
    h x (a • y) = algebraMap R K a * h x y := by
  rw [← algebraMap_smul K a y, map_smul, smul_eq_mul]

theorem neighbourBasic_unimod [IsDedekindDomain R] [IsFractionRing R K]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (P : Ideal R) (hP : P.IsMaximal) (hPc : (conjIdeal (K := K) P).IsMaximal)
    (L M : Submodule R V)
    (eL : (L ⧸ (L ⊓ M).comap L.subtype) ≃ₗ[R] (R ⧸ conjIdeal (K := K) P))
    (eM : (M ⧸ (L ⊓ M).comap M.subtype) ≃ₗ[R] (R ⧸ P))
    (hL : IsUnimodular h L) (hM : IsIntegralLat h M) : IsUnimodular h M := by
  have hone : ∀ k : K, k ∈ (1 : Submodule R K) ↔ k ∈ Set.range (algebraMap R K) :=
    fun k => by rw [Submodule.mem_one]; rfl
  have rmul : ∀ a b : K, a ∈ Set.range (algebraMap R K) → b ∈ Set.range (algebraMap R K) →
      a * b ∈ Set.range (algebraMap R K) := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩
  have radd : ∀ a b : K, a ∈ Set.range (algebraMap R K) → b ∈ Set.range (algebraMap R K) →
      a + b ∈ Set.range (algebraMap R K) := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add _ _ _⟩
  have ralg : ∀ r : R, algebraMap R K r ∈ Set.range (algebraMap R K) := fun r => ⟨r, rfl⟩
  have rstar : ∀ a : K, a ∈ Set.range (algebraMap R K) → star a ∈ Set.range (algebraMap R K) := by
    rintro _ ⟨x, rfl⟩; exact hstar x
  have memD : ∀ (A : Submodule R V) (x : V),
      x ∈ dual h A ↔ ∀ y ∈ A, h y x ∈ Set.range (algebraMap R K) := by
    intro A x; rw [dualBasic_mem_dual]; simp only [hone]
  have hMM : ∀ m ∈ M, m ∈ dual h M := fun m hm =>
    (memD M m).mpr (fun y hy => (hone _).mp (hM y hy m hm))
  obtain ⟨l₀, hl₀, hgen⟩ := neighbourBasic_gen eL
  obtain ⟨m₀, hm₀, hm₀N⟩ := neighbourBasic_not_le hP.ne_top eM
  have hm₀L : m₀ ∉ L := fun h' => hm₀N (Submodule.mem_inf.mpr ⟨h', hm₀⟩)
  have gen : ∀ y : V, (∀ n ∈ L ⊓ M, h n y ∈ Set.range (algebraMap R K)) →
      h l₀ y ∈ Set.range (algebraMap R K) → y ∈ L := by
    intro y hN h0
    rw [← hL, memD]
    intro l hl
    obtain ⟨a, ha⟩ := hgen l hl
    have e1 : l = a • l₀ + (l - a • l₀) := by abel
    rw [e1, map_add, LinearMap.add_apply, neighbourBasic_h_smul_left]
    exact radd _ _ (rmul _ _ (rstar _ (ralg a)) h0) (hN _ ha)
  have hNM : ∀ y ∈ dual h M, ∀ n ∈ L ⊓ M, h n y ∈ Set.range (algebraMap R K) :=
    fun y hy n hn => (memD M y).mp hy n (Submodule.mem_inf.mp hn).2
  have hPy : ∀ y ∈ dual h M, ∀ p ∈ P,
      algebraMap R K p * h l₀ y ∈ Set.range (algebraMap R K) := by
    intro y hy p hp
    obtain ⟨t, ht⟩ := hstar p
    have htP : t ∈ conjIdeal (K := K) P := Ideal.subset_span ⟨p, hp, ht⟩
    have := hNM y hy _ (neighbourBasic_smul_mem eL htP hl₀)
    rwa [neighbourBasic_h_smul_left, ht, star_star] at this
  have stepA : ∀ y ∈ L, y ∈ dual h M → y ∈ M := by
    intro y hyL hyM
    by_contra hyN'
    have hyN : y ∉ L ⊓ M := fun h' => hyN' (Submodule.mem_inf.mp h').2
    apply hm₀L
    rw [← hL, memD]
    intro l hl
    have hlD : l ∈ dual h M := by
      obtain ⟨a, ha⟩ := neighbourBasic_gen' hPc eL hyL hyN l hl
      have e1 : l = (l - a • y) + a • y := by abel
      rw [e1]
      exact (dual h M).add_mem (hMM _ (Submodule.mem_inf.mp ha).2) ((dual h M).smul_mem a hyM)
    have := (memD M l).mp hlD m₀ hm₀
    rw [← hs.eq m₀ l, starRingEnd_apply]
    exact rstar _ this
  show dual h M = M
  refine le_antisymm ?_ (fun m hm => hMM m hm)
  intro x hx
  have hm₀D := hMM m₀ hm₀
  have hc' : h l₀ m₀ ∉ Set.range (algebraMap R K) := fun h' => hm₀L (gen m₀ (hNM m₀ hm₀D) h')
  obtain ⟨a, b, hab⟩ :=
    neighbourBasic_ded P hP (h l₀ x) (h l₀ m₀) (hPy x hx) (hPy m₀ hm₀D) hc'
  have hyD : x - b • m₀ ∈ dual h M := (dual h M).sub_mem hx ((dual h M).smul_mem b hm₀D)
  have hy0 : h l₀ (x - b • m₀) ∈ Set.range (algebraMap R K) := by
    rw [map_sub, neighbourBasic_h_smul_right, hab]; exact ⟨a, by ring⟩
  have hyM := stepA _ (gen _ (hNM _ hyD) hy0) hyD
  have e1 : x = (x - b • m₀) + b • m₀ := by abel
  rw [e1]
  exact M.add_mem hyM (M.smul_mem b hm₀)

end Main

end Formalism.HermitianLatticesTheory
end
end

