import Mathlib

-- bundled from GroundTheory.ArithmeticGeometry.ToricVarieties.ExistsDualNegOfNotMemHullFinset
section
namespace GroundTheory.Arith.Toric

open Module PointedCone

section Field

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V W : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

theorem mem_hull_insert {a x : V} {s : Set V} :
    x ∈ hull 𝕜 (insert a s) ↔ ∃ c : 𝕜, 0 ≤ c ∧ ∃ y ∈ hull 𝕜 s, x = c • a + y := by
  rw [Submodule.mem_span_insert]
  constructor
  · rintro ⟨c, y, hy, rfl⟩
    exact ⟨c, c.2, y, hy, rfl⟩
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨⟨c, hc⟩, y, hy, rfl⟩

theorem exists_of_mem_hull_image (φ : V →ₗ[𝕜] W) {s : Set V} {y : W}
    (hy : y ∈ hull 𝕜 (φ '' s)) : ∃ z ∈ hull 𝕜 s, φ z = y := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, subset_hull hz, rfl⟩
  | zero => exact ⟨0, zero_mem _, map_zero φ⟩
  | add y y' _ _ h h' =>
    obtain ⟨z, hz, rfl⟩ := h
    obtain ⟨z', hz', rfl⟩ := h'
    exact ⟨z + z', add_mem hz hz', map_add φ z z'⟩
  | smul c y _ h =>
    obtain ⟨z, hz, rfl⟩ := h
    exact ⟨(c : 𝕜) • z, smul_mem _ c.2 hz, by rw [map_smul]; rfl⟩

theorem nonneg_of_mem_hull {f : Dual 𝕜 V} {s : Set V} (hs : ∀ y ∈ s, 0 ≤ f y) {x : V}
    (hx : x ∈ hull 𝕜 s) : 0 ≤ f x := by
  have h : hull 𝕜 s ≤ (positive 𝕜 𝕜).comap f :=
    Submodule.span_le.2 fun y hy => by simpa [mem_comap, mem_positive] using hs y hy
  simpa [mem_comap, mem_positive] using h hx

theorem exists_dual_neg_of_not_mem_hull {ι : Type*} (s : Finset ι) (v : ι → V) {x : V}
    (hx : x ∉ hull 𝕜 (v '' s)) : ∃ f : Dual 𝕜 V, (∀ i ∈ s, 0 ≤ f (v i)) ∧ f x < 0 := by
  classical
  induction s using Finset.induction_on generalizing v x with
  | empty =>
    have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero 𝕜 hx0
    rcases hf.lt_or_gt with h | h
    · exact ⟨f, by simp, h⟩
    · exact ⟨-f, by simp, by simpa using h⟩
  | insert a s ha ih =>
    have hsub : hull 𝕜 (v '' s) ≤ hull 𝕜 (v '' ↑(insert a s)) :=
      Submodule.span_mono (Set.image_mono (by simp))
    obtain ⟨f, hf, hfx⟩ := ih v (fun h => hx (hsub h))
    by_cases hfa : 0 ≤ f (v a)
    · refine ⟨f, fun i hi => ?_, hfx⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      exacts [hfa, hf i hi]
    replace hfa := not_le.1 hfa
    let φ : V →ₗ[𝕜] V := LinearMap.id - (f (v a))⁻¹ • f.smulRight (v a)
    have hφ : ∀ y, φ y = y - (f y / f (v a)) • v a := by
      intro y
      simp [φ, div_eq_mul_inv, mul_comm, smul_smul]
    have hφa : φ (v a) = 0 := by rw [hφ, div_self hfa.ne, one_smul, sub_self]
    have hnot : φ x ∉ hull 𝕜 ((φ ∘ v) '' s) := by
      intro h
      rw [Set.image_comp] at h
      obtain ⟨z, hz, hzx⟩ := exists_of_mem_hull_image φ h
      apply hx
      have hfz : 0 ≤ f z := nonneg_of_mem_hull (by rintro _ ⟨i, hi, rfl⟩; exact hf i hi) hz
      rw [Finset.coe_insert, Set.image_insert_eq, mem_hull_insert]
      refine ⟨(f x - f z) / f (v a), div_nonneg_of_nonpos (by linarith) hfa.le, z, hz, ?_⟩
      rw [hφ, hφ] at hzx
      rw [sub_div, sub_smul]
      linear_combination (norm := module) -hzx
    obtain ⟨g, hg, hgx⟩ := ih (φ ∘ v) hnot
    refine ⟨g ∘ₗ φ, fun i hi => ?_, hgx⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · simp [hφa]
    · exact hg i hi

theorem exists_dual_neg_of_not_mem_hull_finset (S : Finset V) {x : V}
    (hx : x ∉ hull 𝕜 (S : Set V)) : ∃ f : Dual 𝕜 V, (∀ y ∈ S, 0 ≤ f y) ∧ f x < 0 :=
  exists_dual_neg_of_not_mem_hull S id (by simpa using hx)

theorem exists_dual_neg_of_not_mem {C : PointedCone 𝕜 V} (hC : C.FG) {x : V} (hx : x ∉ C) :
    ∃ f : Dual 𝕜 V, (∀ y ∈ C, 0 ≤ f y) ∧ f x < 0 := by
  obtain ⟨S, rfl⟩ := hC
  obtain ⟨f, hf, hfx⟩ := exists_dual_neg_of_not_mem_hull_finset S hx
  exact ⟨f, fun y hy => nonneg_of_mem_hull hf hy, hfx⟩

theorem mem_iff_forall_dual {C : PointedCone 𝕜 V} (hC : C.FG) {x : V} :
    x ∈ C ↔ ∀ f : Dual 𝕜 V, (∀ y ∈ C, 0 ≤ f y) → 0 ≤ f x := by
  refine ⟨fun hx f hf => hf x hx, fun h => ?_⟩
  by_contra hx
  obtain ⟨f, hf, hfx⟩ := exists_dual_neg_of_not_mem hC hx
  exact (h f hf).not_gt hfx

theorem fg_top [FiniteDimensional 𝕜 V] : (⊤ : PointedCone 𝕜 V).FG := by
  classical
  let b := Module.finBasis 𝕜 V
  let S : Finset V := Finset.univ.image b ∪ Finset.univ.image (fun i => -b i)
  refine ⟨S, top_le_iff.1 fun x _ => ?_⟩
  have key : ∀ y ∈ Submodule.span 𝕜 (Set.range b),
      y ∈ hull 𝕜 (S : Set V) ∧ -y ∈ hull 𝕜 (S : Set V) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨subset_hull (by simp [S]), subset_hull (by simp [S])⟩
    | zero => simp
    | add y z _ _ hy hz =>
      exact ⟨add_mem hy.1 hz.1, by rw [neg_add]; exact add_mem hy.2 hz.2⟩
    | smul c y _ hy =>
      rcases le_total 0 c with hc | hc
      · exact ⟨smul_mem _ hc hy.1, by rw [← smul_neg]; exact smul_mem _ hc hy.2⟩
      · refine ⟨?_, ?_⟩
        · rw [← neg_neg c, neg_smul, ← smul_neg]; exact smul_mem _ (neg_nonneg.2 hc) hy.2
        · rw [← neg_smul]; exact smul_mem _ (neg_nonneg.2 hc) hy.1
  exact (key x (by rw [b.span_eq]; exact Submodule.mem_top)).1

theorem hull_inf_halfspace (S : Finset V) (g : Dual 𝕜 V) [DecidableEq V] :
    hull 𝕜 (S : Set V) ⊓ (positive 𝕜 𝕜).comap g =
      hull 𝕜 ((S.filter (fun s => 0 ≤ g s) ∪
        ((S ×ˢ S).filter (fun st => 0 < g st.1 ∧ g st.2 < 0)).image
          (fun st => g st.1 • st.2 - g st.2 • st.1) : Finset V) : Set V) := by
  set G : Finset V := S.filter (fun s => 0 ≤ g s) ∪
        ((S ×ˢ S).filter (fun st => 0 < g st.1 ∧ g st.2 < 0)).image
          (fun st => g st.1 • st.2 - g st.2 • st.1) with hG
  have memP : ∀ y ∈ S, 0 ≤ g y → y ∈ G := fun y hy hgy =>
    Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hy, hgy⟩)
  have memQ : ∀ s ∈ S, ∀ t ∈ S, 0 < g s → g t < 0 → g s • t - g t • s ∈ G :=
    fun s hs t ht h1 h2 => Finset.mem_union_right _
      (Finset.mem_image.2 ⟨(s, t), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hs, ht⟩, h1, h2⟩, rfl⟩)
  apply le_antisymm
  · rintro x ⟨hxS, hxg⟩
    have hxg : 0 ≤ g x := by simpa [mem_comap, mem_positive] using hxg
    by_contra hxG
    obtain ⟨h, hh, hhx⟩ := exists_dual_neg_of_not_mem_hull_finset G hxG
    obtain ⟨l, hl0, hlQ, hlP⟩ : ∃ l : 𝕜, 0 ≤ l ∧ (∀ t ∈ S, g t < 0 → h t / g t ≤ l) ∧
        (∀ s ∈ S, 0 < g s → l ≤ h s / g s) := by
      by_cases hT : (S.filter (fun t => g t < 0)).Nonempty
      · obtain ⟨t0, ht0, hmax⟩ := Finset.exists_max_image _ (fun t => h t / g t) hT
        obtain ⟨ht0S, hgt0⟩ := Finset.mem_filter.1 ht0
        refine ⟨max 0 (h t0 / g t0), le_max_left _ _,
          fun t ht hgt => (hmax t (Finset.mem_filter.2 ⟨ht, hgt⟩)).trans (le_max_right _ _),
          fun s hs hgs => max_le (div_nonneg (hh s (memP s hs hgs.le)) hgs.le) ?_⟩
        have h1 := hh _ (memQ s hs t0 ht0S hgs hgt0)
        simp only [map_sub, map_smul, smul_eq_mul] at h1
        rw [div_le_iff_of_neg hgt0, div_mul_eq_mul_div, div_le_iff₀ hgs]
        nlinarith
      · refine ⟨0, le_rfl, fun t ht hgt => absurd ⟨t, Finset.mem_filter.2 ⟨ht, hgt⟩⟩ hT,
          fun s hs hgs => div_nonneg (hh s (memP s hs hgs.le)) hgs.le⟩
    have hk : ∀ y ∈ (S : Set V), 0 ≤ (h - l • g) y := by
      intro y hy
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rcases lt_trichotomy (g y) 0 with hgy | hgy | hgy
      · have := hlQ y hy hgy
        rw [div_le_iff_of_neg hgy] at this
        linarith
      · rw [hgy, mul_zero, sub_zero]
        exact hh y (memP y hy hgy.ge)
      · have := hlP y hy hgy
        rw [le_div_iff₀ hgy] at this
        linarith
    have h1 := nonneg_of_mem_hull hk hxS
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    nlinarith [mul_nonneg hl0 hxg]
  · rw [Submodule.span_le]
    intro y hy
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hy) with hy | hy
    · obtain ⟨hyS, hgy⟩ := Finset.mem_filter.1 hy
      exact ⟨subset_hull hyS, by simpa [mem_comap, mem_positive] using hgy⟩
    · obtain ⟨⟨s, t⟩, hst, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨hst, h1, h2⟩ := Finset.mem_filter.1 hst
      obtain ⟨hs, ht⟩ := Finset.mem_product.1 hst
      refine ⟨?_, ?_⟩
      · rw [sub_eq_add_neg, ← neg_smul]
        exact add_mem (smul_mem _ h1.le (subset_hull ht))
          (smul_mem _ (neg_nonneg.2 h2.le) (subset_hull hs))
      · simp [mul_comm]

theorem fg_inf_halfspace {C : PointedCone 𝕜 V} (hC : C.FG) (g : Dual 𝕜 V) :
    (C ⊓ (positive 𝕜 𝕜).comap g).FG := by
  classical
  obtain ⟨S, rfl⟩ := hC
  rw [hull_inf_halfspace]
  exact ⟨_, rfl⟩

variable {M N : Type*} [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N]

theorem fg_dual_finset [FiniteDimensional 𝕜 N] (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) (s : Finset M) :
    (dual p (s : Set M)).FG := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fg_top
  | insert a s _ ih =>
    rw [Finset.coe_insert, dual_insert, dual_singleton, inf_comm]
    exact fg_inf_halfspace ih (p a)

theorem fg_dual [FiniteDimensional 𝕜 N] (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) {C : PointedCone 𝕜 M}
    (hC : C.FG) : (dual p (C : Set M)).FG := by
  obtain ⟨S, rfl⟩ := hC
  rw [dual_hull]
  exact fg_dual_finset p S

theorem dual_dual_flip_of_fg (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) (hp : Function.Surjective p)
    {C : PointedCone 𝕜 N} (hC : C.FG) : dual p (dual p.flip (C : Set N)) = C := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · by_contra hxC
    obtain ⟨f, hf, hfx⟩ := exists_dual_neg_of_not_mem hC hxC
    obtain ⟨m, rfl⟩ := hp f
    have hm : m ∈ dual p.flip (C : Set N) := fun y hy => by simpa using hf y hy
    exact (hx hm).not_gt hfx
  · intro m hm
    simpa using hm hx

theorem fg_iff_dualFG [FiniteDimensional 𝕜 M] [FiniteDimensional 𝕜 N]
    (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) (hp : Function.Surjective p) {C : PointedCone 𝕜 N} :
    C.FG ↔ C.DualFG p := by
  constructor
  · intro hC
    obtain ⟨T, hT⟩ := fg_dual p.flip hC
    refine ⟨T, ?_⟩
    rw [← dual_hull]
    change dual p (Submodule.span _ (T : Set M) : Set M) = C
    rw [hT]
    exact dual_dual_flip_of_fg p hp hC
  · rintro ⟨s, rfl⟩
    exact fg_dual_finset p s

end Field

end GroundTheory.Arith.Toric
end

-- bundled from GroundTheory.ArithmeticGeometry.ToricVarieties.KrullDomain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Toric

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] in

theorem smul_mk_eq_zero_iff {b r y : A} :
    r • (Ideal.Quotient.mk (Ideal.span {b}) y) = 0 ↔ b ∣ r * y := by
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

theorem height_eq_one_of_isAssociatedPrime {b : A} (hb : b ≠ 0) {P : Ideal A}
    (hP : IsAssociatedPrime P (A ⧸ Ideal.span {b})) : P.height = 1 := by
  classical
  obtain ⟨hPp, yb, hPy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yb
  have hmem : ∀ r, r ∈ P ↔ b ∣ r * y := by
    intro r
    rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_mk_eq_zero_iff]
  have hbP : b ∈ P := (hmem b).2 (dvd_mul_right b y)
  have hP0 : P ≠ ⊥ := fun h => hb (by rw [h] at hbP; exact (Submodule.mem_bot _).1 hbP)
  by_cases hcase : ∀ r s : A, r ∈ P → r * y = b * s → s ∈ P
  · exfalso
    let K := FractionRing A
    have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
    let N : Submodule A K := Submodule.map (Algebra.linearMap A K) P
    have hNfg : N.FG := (IsNoetherian.noetherian P).map _
    have hN0 : N ≠ ⊥ := by
      intro h
      have : algebraMap A K b ∈ N := Submodule.mem_map.2 ⟨b, hbP, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hb (hinj (by rw [this, map_zero]))
    have hbK : algebraMap A K b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hint : IsIntegral A (algebraMap A K y / algebraMap A K b) := by
      refine isIntegral_of_smul_mem_submodule N hN0 hNfg _ ?_
      intro n hn
      obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨s, hs⟩ := (hmem r).1 hr
      refine Submodule.mem_map.2 ⟨s, hcase r s hr hs, ?_⟩
      change algebraMap A K s = (algebraMap A K y / algebraMap A K b) * algebraMap A K r
      rw [div_mul_eq_mul_div, eq_div_iff hbK, ← map_mul, ← map_mul, mul_comm y r, hs, mul_comm]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hyz : y = b * z := by
      apply hinj
      rw [map_mul, hz, mul_div_cancel₀ _ hbK]
    apply hPp.ne_top
    rw [Ideal.eq_top_iff_one, hmem, one_mul, hyz]
    exact dvd_mul_right b z
  · push Not at hcase
    obtain ⟨r₀, s₀, hr₀, hrs, hs₀⟩ := hcase
    have hmin : P ∈ (Ideal.span {r₀}).minimalPrimes := by
      refine ⟨⟨hPp, (Ideal.span_singleton_le_iff_mem _).2 hr₀⟩, fun Q hQ hQP => ?_⟩
      obtain ⟨hQp, hQr⟩ := hQ
      intro r hr
      obtain ⟨s, hs⟩ := (hmem r).1 hr
      have key : r * s₀ = r₀ * s := by
        apply mul_left_cancel₀ hb
        calc b * (r * s₀) = r * (b * s₀) := by ring
          _ = r * (r₀ * y) := by rw [hrs]
          _ = r₀ * (r * y) := by ring
          _ = b * (r₀ * s) := by rw [hs]; ring
      have hin : r * s₀ ∈ Q := by
        rw [key]
        exact Q.mul_mem_right s ((Ideal.span_singleton_le_iff_mem _).1 hQr)
      exact (hQp.mem_or_mem hin).resolve_right fun h => hs₀ (hQP h)
    have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {r₀}) P hmin
    have hne : P.height ≠ 0 := fun h => hP0 (Ideal.height_eq_zero_iff_eq_bot.1 h)
    exact le_antisymm hle (Order.one_le_iff_ne_zero.2 hne)

theorem mem_range_of_forall_height_one {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (x : K) (h : ∀ p : Ideal A, p.IsPrime → p.height = 1 →
      ∃ a s : A, s ∉ p ∧ x * algebraMap A K s = algebraMap A K a) :
    x ∈ (algebraMap A K).range := by
  classical
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hbK : algebraMap A K b ≠ 0 := fun h => hb0 (hinj (by rw [h, map_zero]))
  by_cases hab : b ∣ a
  · obtain ⟨c, rfl⟩ := hab
    exact ⟨c, by rw [map_mul, mul_div_cancel_left₀ _ hbK]⟩
  · exfalso
    have hne : Ideal.Quotient.mk (Ideal.span {b}) a ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact hab
    obtain ⟨P, hP, hcol⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hne
    obtain ⟨a', s, hs, hx⟩ := h P hP.isPrime (height_eq_one_of_isAssociatedPrime hb0 hP)
    apply hs
    apply hcol
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_mk_eq_zero_iff, mul_comm]
    refine ⟨a', hinj ?_⟩
    rw [map_mul, map_mul, ← hx, div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ hbK]

end GroundTheory.Arith.Toric
end

