import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimSeq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Forms

variable {R : Type u} [CommRing R] {N : ℕ}

theorem homogeneousComponent_mul_form (r g : Poly R N) {d : ℕ} (hg : g.IsHomogeneous d) (e : ℕ) :
    homogeneousComponent e (r * g) ∈ Submodule.span R
      {z | ∃ (h : Poly R N) (d' : ℕ), h.IsHomogeneous d' ∧ d' + d = e ∧ z = h * g} := by
  rw [show r * g = ∑ i ∈ Finset.range (r.totalDegree + 1), homogeneousComponent i r * g by
    rw [← Finset.sum_mul, sum_homogeneousComponent], map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hm : homogeneousComponent i r * g ∈ homogeneousSubmodule (Fin (N + 1)) R (i + d) :=
    (mem_homogeneousSubmodule _ _).mpr ((homogeneousComponent_isHomogeneous i r).mul hg)
  rw [homogeneousComponent_of_mem hm]
  split_ifs with h
  · exact Submodule.subset_span ⟨_, i, homogeneousComponent_isHomogeneous i r, h.symm, rfl⟩
  · exact Submodule.zero_mem _

theorem mem_span_forms_of_mem_ideal {G : Set (Poly R N)} (deg : Poly R N → ℕ)
    (hG : ∀ g ∈ G, g.IsHomogeneous (deg g)) {f : Poly R N} {e : ℕ} (hf : f ∈ Ideal.span G)
    (he : f.IsHomogeneous e) :
    f ∈ Submodule.span R {z | ∃ g ∈ G, ∃ (h : Poly R N) (d' : ℕ), h.IsHomogeneous d' ∧
      d' + deg g = e ∧ z = h * g} := by
  obtain ⟨c, t, htG, -, rfl⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hf
  rw [← homogeneousComponent_eq_self he, map_sum]
  refine Submodule.sum_mem _ fun g hg => ?_
  have hc := homogeneousComponent_mul_form (c g) g (hG g (htG hg)) e
  rw [smul_eq_mul]
  refine Submodule.span_le.mpr ?_ hc
  rintro _ ⟨h, d', hh, hd, rfl⟩
  exact Submodule.subset_span ⟨g, htG hg, h, d', hh, hd, rfl⟩

theorem isHomogeneous_totalDegree {g : Poly R N} {d : ℕ} (hg : g.IsHomogeneous d) :
    g.IsHomogeneous g.totalDegree := by
  by_cases h0 : g = 0
  · rw [h0]; exact isHomogeneous_zero _ _ _
  · rwa [hg.totalDegree h0]

end Forms

section Chart

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem form_mul_mem_twistMod {h : Poly k N} {d : ℕ} (hh : h.IsHomogeneous d) {c : ℤ} (I : Chart x)
    {o : Ω} (ho : o ∈ twistMod k x c I) : aeval x h * o ∈ twistMod k x (c + d) I := by
  refine Submodule.span_induction (p := fun o _ => aeval x h * o ∈ twistMod k x (c + d) I) ?_ ?_ ?_ ?_ ho
  · rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    exact Submodule.subset_span ⟨h * f, s, e, d + e', hs, hh.mul hf, hse, by push_cast; omega,
      by rw [map_mul, mul_div_assoc]⟩
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    have := Submodule.smul_mem _ a hz
    rw [chartRing_smul_def] at this ⊢
    rwa [mul_left_comm]

theorem div_mem_chartRing {e : ℕ} (I : Chart x) {o : Ω} (ho : o ∈ twistMod k x e I) {s : Poly k N}
    (hs : s ∈ monos I.1) (hse : s.IsHomogeneous e) : o / aeval x s ∈ chartRing k x I := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span _ I hi, Submodule.mem_span_singleton] at ho
  obtain ⟨a, rfl⟩ := ho
  have hq : x i ^ (e : ℤ) / aeval x s ∈ chartRing k x I :=
    ⟨X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse, by rw [map_pow, aeval_X, zpow_natCast]⟩
  rw [chartRing_smul_def, mul_div_assoc]
  exact mul_mem a.2 hq

variable (T : StepData k x)

theorem StepData.form_mem_J {f : Poly k N} {e : ℕ} (hf : f ∈ T.J) (he : f.IsHomogeneous e) (I : Chart x)
    {δ : Ω} (hδ : δ ∈ T.D.sub I) : ∃ o ∈ twistMod k x e I, aeval x f * δ = T.si * o := by
  have hG : ∀ g ∈ {f : Poly k N | ∃ c : ℕ, f.IsHomogeneous c ∧ ∀ (I : Chart x), ∀ δ ∈ T.D.sub I,
      ∃ o ∈ twistMod k x (c : ℤ) I, aeval x f * δ = T.si * o}, g.IsHomogeneous g.totalDegree :=
    fun g ⟨c, hc, _⟩ => isHomogeneous_totalDegree hc
  have hmem := mem_span_forms_of_mem_ideal _ hG hf he
  refine Submodule.span_induction (p := fun f _ => ∃ o ∈ twistMod k x e I, aeval x f * δ = T.si * o)
    ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨g, ⟨c, hc, hg⟩, h, d', hh, hd, rfl⟩
    by_cases h0 : g = 0
    · exact ⟨0, Submodule.zero_mem _, by rw [h0, mul_zero, map_zero, zero_mul, mul_zero]⟩
    obtain ⟨o, ho, hgo⟩ := hg I δ hδ
    rw [hc.totalDegree h0] at hd
    refine ⟨aeval x h * o, ?_, by rw [map_mul, mul_assoc, hgo, mul_left_comm]⟩
    have := form_mul_mem_twistMod hh I ho
    rwa [show (c : ℤ) + d' = e by omega] at this
  · exact ⟨0, Submodule.zero_mem _, by rw [map_zero, zero_mul, mul_zero]⟩
  · rintro _ _ _ _ ⟨o, ho, h1⟩ ⟨o', ho', h2⟩
    exact ⟨o + o', Submodule.add_mem _ ho ho', by rw [map_add, add_mul, h1, h2, mul_add]⟩
  · rintro a _ _ ⟨o, ho, h1⟩
    refine ⟨a • o, (twistMod k x e I).smul_of_tower_mem a ho, ?_⟩
    rw [map_smul, smul_mul_assoc, h1, mul_smul_comm]

def StepData.Jg : FinGradedSub (S := k) (x := x) Ω where
  piece c := Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧ f.IsHomogeneous e ∧ (e : ℤ) = c ∧
    z = aeval x f}
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span k {z | ∃ (f : Poly k N)
      (e : ℕ), f ∈ T.J ∧ f.IsHomogeneous e ∧ (e : ℤ) = c + d ∧ z = aeval x f}) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨g, e, hg, hge, rfl, rfl⟩
      exact Submodule.subset_span ⟨f * g, d + e, T.J.mul_mem_left f hg, hf.mul hge,
        by push_cast; ring, by rw [map_mul, smul_eq_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; rw [smul_comm]; exact Submodule.smul_mem _ a hz
  fg := by
    classical
    set G : Set (Poly k N) := {f : Poly k N | ∃ c : ℕ, f.IsHomogeneous c ∧ ∀ (I : Chart x), ∀ δ ∈ T.D.sub I,
      ∃ o ∈ twistMod k x (c : ℤ) I, aeval x f * δ = T.si * o} with hGdef
    have hJ : T.J = Ideal.span G := rfl
    have hfg : (Submodule.span (Poly k N) G).FG := IsNoetherian.noetherian _
    obtain ⟨G₀, hG₀, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg
    have hG : ∀ g ∈ (G₀ : Set (Poly k N)), g.IsHomogeneous g.totalDegree :=
      fun g hg => by obtain ⟨c, hc, _⟩ := hG₀ hg; exact isHomogeneous_totalDegree hc
    let gj : Fin G₀.card → Poly k N := fun j => (G₀.equivFin.symm j : Poly k N)
    refine ⟨G₀.card, fun j => ((gj j).totalDegree : ℤ), fun j => aeval x (gj j), fun j => ?_, fun c => ?_⟩
    · refine Submodule.subset_span ⟨gj j, _, ?_, hG _ (G₀.equivFin.symm j).2, rfl, rfl⟩
      rw [hJ]; exact Ideal.subset_span (hG₀ (G₀.equivFin.symm j).2)
    · rw [Submodule.span_le]
      rintro _ ⟨f, e, hf, he, rfl, rfl⟩
      rw [hJ, Ideal.span, hspan] at hf
      have hm := mem_span_forms_of_mem_ideal _ hG hf he
      refine Submodule.span_induction (p := fun f _ => aeval x f ∈ _) ?_ ?_ ?_ ?_ hm
      · rintro _ ⟨g, hg, h, d', hh, hd, rfl⟩
        refine Submodule.subset_span ⟨G₀.equivFin ⟨g, hg⟩, h, d', hh, ?_, ?_⟩
        · simp only [gj, Equiv.symm_apply_apply]; omega
        · simp only [gj, Equiv.symm_apply_apply, map_mul, smul_eq_mul]
      · rw [map_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
      · intro a z _ hz; rw [map_smul]; exact Submodule.smul_mem _ a hz

theorem StepData.Jg_tilde (I : Chart x) : (T.Jg.tildeSys 0).sub I = idealMod T.J I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    refine Submodule.span_induction (p := fun m _ => (aeval x s)⁻¹ • m ∈ idealMod T.J I)
      ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨f, e', hf, hfe, rfl, rfl⟩
      have he : e' = e := by omega
      subst he
      exact Submodule.subset_span ⟨f, s, e', hf, hs, hfe, hse, by rw [smul_eq_mul, div_eq_inv_mul]⟩
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro c z _ hz; rw [smul_comm]; exact (idealMod T.J I).smul_of_tower_mem c hz
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    exact Submodule.subset_span ⟨aeval x f, s, e, e, hs, hse,
      Submodule.subset_span ⟨f, e, hf, hfe, rfl, rfl⟩, sub_self _, by rw [smul_eq_mul, div_eq_inv_mul]⟩

theorem StepData.isUnit_D (I : Chart x) : IsUnit (T.D.sub I) := by
  obtain ⟨i, hi⟩ := I.2.1
  have h0 : (twistSys k x 0).sub I = 1 := by
    change twistMod k x 0 I = 1
    rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]
  have hO : IsUnit ((twistSys k x (T.m - T.c₁)).sub I) :=
    IsUnit.of_mul_eq_one ((twistSys k x (-(T.m - T.c₁))).sub I) (by rw [twistSys_sub_mul, add_neg_cancel, h0])
  obtain ⟨Q', hQ'⟩ := T.M.invertible I
  rw [StepData.D, twistMul_sub]
  exact hO.mul ((IsUnit.of_mul_eq_one _ hQ').pow _)

theorem StepData.idealMod_mul_D (hZ : ZeroIdealChart.Statement.{u, w}) (I : Chart x) :
    idealMod T.J I * T.D.sub I = Submodule.span (chartRing k x I) {T.si} := by
  apply le_antisymm
  · refine Submodule.mul_le.mpr fun a ha δ hδ => ?_
    obtain ⟨g, s, e, hg, hs, hge, hse, rfl⟩ := idealMod_mem_form T.J I ha
    obtain ⟨o, ho, hgo⟩ := T.form_mem_J hg hge I hδ
    refine Submodule.mem_span_singleton.mpr ⟨⟨o / aeval x s, div_mem_chartRing I ho hs hse⟩, ?_⟩
    rw [chartRing_smul_def]
    change o / aeval x s * T.si = aeval x g / aeval x s * δ
    rw [div_mul_eq_mul_div (aeval x g), hgo]
    ring
  · obtain ⟨Q', hQ'⟩ := (T.isUnit_D I).exists_right_inv
    have hle : Submodule.span (chartRing k x I) {T.si} * Q' ≤ idealMod T.J I := by
      refine Submodule.mul_le.mpr fun a ha b hb => ?_
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ c (hZ k Ω N x T I b fun δ hδ => ?_)
      have h1 : b * δ ∈ T.D.sub I * Q' := by
        rw [mul_comm b]; exact Submodule.mul_mem_mul hδ hb
      rw [hQ', Submodule.mem_one] at h1
      obtain ⟨y, hy⟩ := h1
      rw [← hy]; exact y.2
    calc Submodule.span (chartRing k x I) {T.si}
        = Submodule.span (chartRing k x I) {T.si} * Q' * T.D.sub I := by
          rw [mul_assoc, mul_comm Q', hQ', mul_one]
      _ ≤ idealMod T.J I * T.D.sub I := Submodule.mul_le.mpr fun a ha b hb => Submodule.mul_mem_mul (hle ha) hb

end Chart

theorem ClaimSeq.proof (hZ : ZeroIdealChart.Statement.{u, w}) : ClaimSeq.Statement.{u, w} := by
  intro k _ Ω _ _ N x T
  refine ⟨T.Jg, fun c => rfl, fun b c I z => ?_⟩
  have hm : (twistSys k x T.m).sub I = (twistSys k x T.c₁).sub I * (twistSys k x (T.m - T.c₁)).sub I := by
    rw [twistSys_sub_mul, show T.c₁ + (T.m - T.c₁) = T.m by ring]
  have hc : (twistSys k x (c + T.c₁)).sub I = (twistSys k x c).sub I * (twistSys k x T.c₁).sub I := by
    rw [twistSys_sub_mul]
  have hJD := T.idealMod_mul_D hZ I
  have hL : T.L.sub I = (twistSys k x T.c₁).sub I * T.D.sub I := by
    rw [StepData.L, StepData.D, twistMul_sub, twistMul_sub, hm, mul_assoc]
  have key : ((T.Jg.tildeSys 0).twist ((T.L.pow (b + 1)).twist (twistSys k x c))).sub I =
      Submodule.span (chartRing k x I) {T.si} * ((T.L.pow b).twist (twistSys k x (c + T.c₁))).sub I := by
    simp only [SubSystem.twist_sub_eq_mul_of_line, SubSystem.pow_sub, T.Jg_tilde I, hc, ← hJD, hL]
    ring
  rw [key, Submodule.mem_span_singleton_mul]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFiniteSections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Tilde

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem zpow_mul_mem_tilde (M : FinGradedSub (S := S) (x := x) Ω) {I : Chart x} {i : Fin (N + 1)}
    (hi : i ∈ I.1) (c d : ℤ) {y : Ω} (hy : y ∈ M.tilde d I) : x i ^ c * y ∈ M.tilde (d + c) I := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine Submodule.span_induction (p := fun y _ => x i ^ c * y ∈ M.tilde (d + c) I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · refine Submodule.subset_span ⟨aeval x (X i ^ n : Poly S N) • m, s, a + n, e, hs, hse,
        M.smul_mem n a _ m (isHomogeneous_X_pow i n) hm, by omega, ?_⟩
      simp only [map_pow, aeval_X, smul_eq_mul, zpow_natCast]
      ring
    · refine Submodule.subset_span ⟨m, s * X i ^ n, a, e + n, mul_mem hs (pow_mem (X_mem_monos hi) n),
        hse.mul (isHomogeneous_X_pow i n), hm, by push_cast; omega, ?_⟩
      simp only [map_mul, map_pow, aeval_X, smul_eq_mul, zpow_neg, zpow_natCast, mul_inv]
      ring
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
  · intro a y _ hy
    have : x i ^ c * (a • y) = a • (x i ^ c * y) := by
      rw [chartRing_smul_def, chartRing_smul_def]; ring
    rw [this]
    exact Submodule.smul_mem _ a hy

theorem tilde_eq_twist (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ) (I : Chart x) :
    M.tilde c I = ((M.tildeSys 0).twist (twistSys S x c)).sub I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  apply le_antisymm
  · intro y hy
    have h0 : x i ^ (-c) * y ∈ M.tilde 0 I := by
      simpa using zpow_mul_mem_tilde M hi (-c) c hy
    refine Submodule.subset_span ⟨x i ^ c, ?_, x i ^ (-c) * y, h0, ?_⟩
    · change x i ^ c ∈ twistMod S x c I
      rw [twistMod_eq_span c I hi]
      exact Submodule.mem_span_singleton_self _
    · rw [smul_eq_mul, ← mul_assoc, ← zpow_add₀ hxi, add_neg_cancel, zpow_zero, one_mul]
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x c I at hq
    rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
    obtain ⟨a, rfl⟩ := hq
    have hy' : x i ^ c * y ∈ M.tilde c I := by
      simpa using zpow_mul_mem_tilde M hi c 0 hy
    have : (a • x i ^ c) • y = a • (x i ^ c * y) := by
      rw [chartRing_smul_def, chartRing_smul_def, smul_eq_mul, mul_assoc]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ a hy'

end Tilde

section Generic

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]
  [IsFractionRing S F]

omit [IsFractionRing S F] in

theorem exists_monos_map {I : Finset (Fin (N + 1))} {s : Poly F N} (hs : s ∈ monos I) :
    ∃ s' : Poly S N, s' ∈ monos I ∧ map (algebraMap S F) s' = s := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨X i, Submonoid.subset_closure ⟨i, hi, rfl⟩, map_X _ _⟩
  | one => exact ⟨1, one_mem _, map_one _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨a' * b', mul_mem ha' hb', map_mul _ _ _⟩

theorem algebraMap_ne_zero_of_mem (F : Type u) [Field F] [Algebra S F] [Algebra F Ω]
    [IsScalarTower S F Ω] [IsFractionRing S F] {t : S} (ht : t ∈ nonZeroDivisors S) : algebraMap S Ω t ≠ 0 := by
  have : Nontrivial S := (algebraMap S F).domain_nontrivial
  rw [IsScalarTower.algebraMap_apply S F Ω]
  exact (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht)

theorem exists_mul_mem_chartRing {I : Chart x} {a : Ω} (ha : a ∈ chartRing F x I) :
    ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * a ∈ chartRing S x I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  obtain ⟨s', hs', rfl⟩ := exists_monos_map (S := S) hs
  have hinj : Function.Injective (algebraMap S F) := IsFractionRing.injective S F
  have hse' : s'.IsHomogeneous e := fun d hd => hse (by
    rw [coeff_map]; exact fun h => hd (hinj (h.trans (map_zero _).symm)))
  have hsum : aeval x f / aeval x (map (algebraMap S F) s') =
      ∑ d ∈ f.support, coeff d f • (aeval x (monomial d (1 : S)) / aeval x s') := by
    rw [aeval_map_algebraMap]
    conv_lhs => rw [f.as_sum]
    rw [map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [aeval_monomial, aeval_monomial, map_one, one_mul, Algebra.smul_def, mul_div_assoc]
  rw [hsum]
  refine Finset.sum_induction _ (fun a => ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * a ∈ chartRing S x I)
    ?_ ⟨1, one_mem _, by rw [mul_zero]; exact zero_mem _⟩ ?_
  · rintro a b ⟨t, ht, hta⟩ ⟨t', ht', htb⟩
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    have : algebraMap S Ω (t * t') * (a + b) =
        algebraMap S Ω t' * (algebraMap S Ω t * a) + algebraMap S Ω t * (algebraMap S Ω t' * b) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) hta)
      (mul_mem (Subalgebra.algebraMap_mem _ _) htb)
  · intro d hd
    have hmem : aeval x (monomial d (1 : S)) / aeval x s' ∈ chartRing S x I :=
      ⟨monomial d 1, s', e, hs', isHomogeneous_monomial _ (by
        rw [Finsupp.degree_eq_weight_one]; exact hf (mem_support_iff.mp hd)), hse', rfl⟩
    obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := S) (coeff d f)
    refine ⟨v, hv, ?_⟩
    have hv0 : algebraMap S Ω v ≠ 0 := algebraMap_ne_zero_of_mem F hv
    have : algebraMap S Ω v * (coeff d f • (aeval x (monomial d (1 : S)) / aeval x s')) =
        algebraMap S Ω u * (aeval x (monomial d (1 : S)) / aeval x s') := by
      rw [Algebra.smul_def, ← huv, map_div₀, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
      field_simp
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) hmem

theorem exists_mul_mem_of_mem_extend (Q : SubSystem S x Ω) (I : Chart x) {z : Ω}
    (hz : z ∈ (Q.extend F).sub I) : ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * z ∈ Q.sub I := by
  have hS : ∀ (t : S) {y : Ω}, y ∈ Q.sub I → algebraMap S Ω t * y ∈ Q.sub I := fun t y hy => by
    rw [← Algebra.smul_def]; exact (Q.sub I).smul_of_tower_mem t hy
  refine Submodule.span_induction
    (p := fun z _ => ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * z ∈ Q.sub I) ?_ ?_ ?_ ?_ hz
  · intro z hz
    exact ⟨1, one_mem _, by rw [map_one, one_mul]; exact hz⟩
  · exact ⟨1, one_mem _, by rw [mul_zero]; exact zero_mem _⟩
  · rintro a b _ _ ⟨t, ht, hta⟩ ⟨t', ht', htb⟩
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    have : algebraMap S Ω (t * t') * (a + b) =
        algebraMap S Ω t' * (algebraMap S Ω t * a) + algebraMap S Ω t * (algebraMap S Ω t' * b) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (hS t' hta) (hS t htb)
  · rintro a z _ ⟨t, ht, htz⟩
    obtain ⟨u, hu, hua⟩ := exists_mul_mem_chartRing (S := S) a.2
    refine ⟨u * t, mul_mem hu ht, ?_⟩
    have : algebraMap S Ω (u * t) * (a • z) =
        (⟨_, hua⟩ : chartRing S x I) • (algebraMap S Ω t * z) := by
      rw [chartRing_smul_def, chartRing_smul_def, map_mul]; ring
    rw [this]
    exact Submodule.smul_mem _ _ htz

theorem span_secs_eq_secs_extend (Q : SubSystem S x Ω) :
    Submodule.span F (Q.secs : Set Ω) = (Q.extend F).secs := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.mpr fun z hz => ?_
    rw [SetLike.mem_coe, SubSystem.secs, Submodule.mem_iInf] at hz ⊢
    intro I
    exact Submodule.subset_span (hz I)
  · intro z hz
    rw [SubSystem.secs, Submodule.mem_iInf] at hz
    choose t ht htz using fun I => exists_mul_mem_of_mem_extend Q I (hz I)
    have hS : ∀ (I : Chart x) (t : S) {y : Ω}, y ∈ Q.sub I → algebraMap S Ω t * y ∈ Q.sub I :=
      fun I t y hy => by rw [← Algebra.smul_def]; exact (Q.sub I).smul_of_tower_mem t hy
    set t₀ := ∏ I, t I with ht₀
    have ht₀m : t₀ ∈ nonZeroDivisors S := prod_mem fun I _ => ht I
    have hmem : algebraMap S Ω t₀ * z ∈ Q.secs := by
      rw [SubSystem.secs, Submodule.mem_iInf]
      intro I
      rw [ht₀, ← Finset.mul_prod_erase _ _ (Finset.mem_univ I), map_mul, mul_comm (algebraMap S Ω (t I)),
        mul_assoc]
      exact hS I _ (htz I)
    have h0 : algebraMap S F t₀ ≠ 0 := by
      have : Nontrivial S := (algebraMap S F).domain_nontrivial
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht₀m
    have : z = (algebraMap S F t₀)⁻¹ • (algebraMap S Ω t₀ * z) := by
      rw [Algebra.smul_def, map_inv₀, IsScalarTower.algebraMap_apply S F Ω,
        inv_mul_cancel_left₀ ((map_ne_zero _).mpr h0)]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end Generic

theorem FiniteSections.proof (hE : Extension.Statement.{u, w, w}) (hT : TildeTail.Statement.{u, w}) :
    FiniteSections.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x Q hx

  have tail : ∀ c₁ : ℤ, ∃ (n : ℕ) (deg : Fin n → ℤ) (gen : Fin n → Ω),
      (∀ j, c₁ ≤ deg j ∧ gen j ∈ (Q.twist (twistSys S x (deg j))).secs) ∧
      ∀ c : ℤ, c₁ ≤ c → (Q.twist (twistSys S x c)).secs ≤ Submodule.span S {z | ∃ (j : Fin n)
        (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ (e : ℤ) + deg j = c ∧ z = aeval x f * gen j} := by
    intro c₁
    obtain ⟨M, -, hM⟩ := hE S Ω N x Ω Q.toSubFamily Q.fg
    have h0 : M.tildeSys 0 = Q.toSubSystem := SubSystem.ext_sub hM
    have hc : ∀ c : ℤ, M.tildeSys c = Q.twist (twistSys S x c) := fun c =>
      SubSystem.ext_sub fun I => by rw [← h0]; exact tilde_eq_twist M c I
    obtain ⟨n, deg, gen, hgen, hspan⟩ := hT S Ω N x M hx c₁
    refine ⟨n, deg, gen, fun j => ⟨(hgen j).1, ?_⟩, fun c hc₁ => ?_⟩
    · rw [← hc]; exact (hgen j).2
    · rw [← hc]; exact hspan c hc₁
  refine ⟨?_, tail, fun F _ _ _ _ _ => span_secs_eq_secs_extend Q.toSubSystem⟩

  obtain ⟨n, deg, gen, hgen, hspan⟩ := tail 0
  have hle : Q.secs ≤ Submodule.span S (Set.range gen) := by
    have h := hspan 0 le_rfl
    rw [SubSystem.twist_twistSys_zero] at h
    refine h.trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨j, f, e, hf, hej, rfl⟩
    have he : e = 0 := by have := (hgen j).1; omega
    subst he
    have hfC : f = C (coeff 0 f) := totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hf.totalDegree_le)
    rw [hfC, aeval_C, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have := isNoetherian_span_of_finite S (Set.finite_range gen)
  exact Module.Finite.iff_fg.mpr (Submodule.FG.of_le_of_isNoetherian hle)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

universe u w

theorem curveClosure {S : Type u} [CommRing S] [IsDomain S] {F : Type u} [Field F] [Algebra S F]
    [IsFractionRing S F] {N : ℕ} (pp : Ideal (Poly F N)) [pp.IsPrime] :
    (∀ s : S, (C s : Poly S N) ∈ pp.comap (MvPolynomial.map (algebraMap S F)) → s = 0) ∧
      (pp.comap (MvPolynomial.map (algebraMap S F))).map (MvPolynomial.map (algebraMap S F)) = pp := by
  refine ⟨fun s hs => ?_, ?_⟩
  · by_contra h0
    have hs' : (C (algebraMap S F s) : Poly F N) ∈ pp := by
      rw [Ideal.mem_comap, map_C] at hs; exact hs
    have hu : IsUnit (C (algebraMap S F s) : Poly F N) :=
      (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective S F)).mpr h0)).map C
    exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ hs' hu)
  · let _ : Algebra (Poly S N) (Poly F N) := MvPolynomial.algebraMvPolynomial
    have : IsLocalization ((nonZeroDivisors S).map (C : S →+* Poly S N)) (Poly F N) :=
      MvPolynomial.isLocalization (nonZeroDivisors S) F
    exact IsLocalization.map_under ((nonZeroDivisors S).map (C : S →+* Poly S N)) (Poly F N) pp

theorem NefGeneric.proof (hC : ConservationOfDegree.Statement.{u, w}) :
    NefGeneric.Statement.{u, w} := by
  intro S _ _ F _ _ _ Ω _ _ _ _ N x M 𝔪 h𝔪 hM pp _ hpp
  have : pp.IsPrime := hpp.isPrime
  obtain ⟨hconst, hmap⟩ := curveClosure (S := S) pp
  have hpp' := hpp
  rw [← hmap] at hpp'
  have key := hC S F Ω N x M 𝔪 h𝔪 _ inferInstance hconst hpp'
  rw [hmap] at key
  rw [key]
  refine finsum_nonneg fun G => ?_
  split_ifs with hG
  · exact mul_nonneg (Int.natCast_nonneg _) (hM G (le_sup_right.trans hG.1.1.2) hG.2)
  · exact le_rfl

end GroundTheory.Heights₂.Heights.Kleiman
end

