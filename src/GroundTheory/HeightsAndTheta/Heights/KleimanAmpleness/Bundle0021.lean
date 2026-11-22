import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MulMemSecsTwistIdealSys
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Kleiman

noncomputable section

section Kill

variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem mul_mem_secs_twist_idealSys (J : Ideal (Poly R N)) {a : R} (ha : C a ∈ J)
    (F : SubSystem R x Ω) {y : Ω} (hy : y ∈ F.secs) :
    algebraMap R Ω a * y ∈ (F.twist (idealSys x J)).secs := by
  simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hy ⊢
  intro I
  rw [SubSystem.twist_sub_eq_mul_of_line]
  refine Submodule.mul_mem_mul (Submodule.subset_span ⟨C a, 1, 0, ha, one_mem _, isHomogeneous_C _ _,
    isHomogeneous_one _ _, by simp⟩) (hy I)

end Kill

section Local

variable {S : Type*} [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] {O : Type*} [CommRing O] [Algebra S O]
  [IsLocalization.AtPrime O 𝔪] {Ω : Type*} [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
  {N : ℕ} {x : Fin (N + 1) → Ω}

theorem exists_map_eq_C_mul (f : Poly O N) :
    ∃ t : S, t ∉ 𝔪 ∧ ∃ g : Poly S N, map (algebraMap S O) g = C (algebraMap S O t) * f ∧
      ∀ d, g.coeff d ≠ 0 → f.coeff d ≠ 0 := by
  classical
  obtain ⟨⟨t, ht⟩, hb⟩ := IsLocalization.exist_integer_multiples 𝔪.primeCompl f.support (fun d => f.coeff d)
  have hb' : ∀ d ∈ f.support, ∃ r : S, algebraMap S O r = t • f.coeff d :=
    fun d hd => RingHom.mem_rangeS.mp (hb d hd)
  choose! c hc using hb'
  have hcoeff : ∀ d, (∑ d' ∈ f.support, monomial d' (c d') : Poly S N).coeff d =
      if d ∈ f.support then c d else 0 := by
    intro d
    rw [coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
  refine ⟨t, ht, ∑ d' ∈ f.support, monomial d' (c d'), ?_, ?_⟩
  · ext d
    rw [coeff_map, coeff_C_mul, hcoeff]
    split_ifs with hd
    · rw [hc d hd, Algebra.smul_def]
    · rw [mem_support_iff, not_not] at hd
      rw [hd, map_zero, mul_zero]
  · intro d hd
    rw [hcoeff] at hd
    split_ifs at hd with h
    · exact mem_support_iff.mp h
    · exact absurd rfl hd

omit [IsLocalization.AtPrime O 𝔪] in

theorem exists_monos_map {I : Finset (Fin (N + 1))} {s : Poly O N} (hs : s ∈ monos (S := O) I) :
    ∃ s₀ ∈ monos (S := S) I, map (algebraMap S O) s₀ = s := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨X i, Submonoid.subset_closure ⟨i, hi, rfl⟩, map_X _ _⟩
  | one => exact ⟨1, one_mem _, map_one _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    exact ⟨a₀ * b₀, mul_mem ha₀ hb₀, map_mul _ _ _⟩

theorem exists_lift_frac {I : Chart x} {f s : Poly O N} {e : ℕ} (hf : f.IsHomogeneous e)
    (hs : s ∈ monos I.1) (hse : s.IsHomogeneous e) :
    ∃ t : S, t ∉ 𝔪 ∧ ∃ g s₀ : Poly S N, g.IsHomogeneous e ∧ s₀ ∈ monos I.1 ∧ s₀.IsHomogeneous e ∧
      map (algebraMap S O) g = C (algebraMap S O t) * f ∧
      algebraMap S Ω t * (aeval x f / aeval x s) = aeval x g / aeval x s₀ := by
  obtain ⟨t, ht, g, hg, hgc⟩ := exists_map_eq_C_mul 𝔪 f
  obtain ⟨s₀, hs₀, rfl⟩ := exists_monos_map (S := S) hs
  obtain ⟨e₀, he₀⟩ := monos_isHomogeneous hs₀
  have hs0 : map (algebraMap S O) s₀ ≠ 0 := fun h =>
    eval_ne_zero_of_mem_monos I hs (by rw [h, map_zero])
  have hee : e₀ = e := (he₀.map (algebraMap S O)).inj_right hse hs0
  subst hee
  refine ⟨t, ht, g, s₀, ?_, hs₀, he₀, hg, ?_⟩
  · intro d hd
    exact hf (hgc d hd)
  · rw [← aeval_map_algebraMap (A := O) x g, hg, ← aeval_map_algebraMap (A := O) x s₀, map_mul, aeval_C,
      IsScalarTower.algebraMap_apply S O Ω, mul_div_assoc]

theorem exists_mul_mem_chartRing {I : Chart x} {a : Ω} (ha : a ∈ chartRing O x I) :
    ∃ t : S, t ∉ 𝔪 ∧ algebraMap S Ω t * a ∈ chartRing S x I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  obtain ⟨t, ht, g, s₀, hg, hs₀, hs₀e, -, hval⟩ := exists_lift_frac 𝔪 hf hs hse
  exact ⟨t, ht, hval ▸ ⟨g, s₀, e, hs₀, hg, hs₀e, rfl⟩⟩

omit [IsLocalization.AtPrime O 𝔪] [IsScalarTower S O Ω] in

theorem mul_not_mem {t₁ t₂ : S} (h₁ : t₁ ∉ 𝔪) (h₂ : t₂ ∉ 𝔪) : t₁ * t₂ ∉ 𝔪 := fun h =>
  ((Ideal.IsPrime.mem_or_mem inferInstance h).elim h₁ h₂)

theorem exists_mul_mem_sub {G : SubSystem S x Ω} {I : Chart x} {z : Ω} (hz : z ∈ (G.baseChange O).sub I) :
    ∃ t : S, t ∉ 𝔪 ∧ algebraMap S Ω t * z ∈ G.sub I := by
  change z ∈ Submodule.span (chartRing O x I) (G.sub I : Set Ω) at hz
  induction hz using Submodule.span_induction with
  | mem y hy => exact ⟨1, fun h => (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr h),
      by rw [map_one, one_mul]; exact hy⟩
  | zero => exact ⟨1, fun h => (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr h),
      by rw [mul_zero]; exact zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨t₁, ht₁, h₁⟩ := ha
    obtain ⟨t₂, ht₂, h₂⟩ := hb
    refine ⟨t₁ * t₂, mul_not_mem 𝔪 ht₁ ht₂, ?_⟩
    have e : algebraMap S Ω (t₁ * t₂) * (a + b) =
        t₂ • (algebraMap S Ω t₁ * a) + t₁ • (algebraMap S Ω t₂ * b) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]; ring
    rw [e]
    exact add_mem ((G.sub I).smul_of_tower_mem t₂ h₁) ((G.sub I).smul_of_tower_mem t₁ h₂)
  | smul a z _ hz =>
    obtain ⟨t, ht, hzt⟩ := hz
    obtain ⟨t', ht', hb⟩ := exists_mul_mem_chartRing 𝔪 a.2
    refine ⟨t' * t, mul_not_mem 𝔪 ht' ht, ?_⟩
    have e : algebraMap S Ω (t' * t) * (a • z) =
        (⟨_, hb⟩ : chartRing S x I) • (algebraMap S Ω t * z) := by
      rw [chartRing_smul_def, chartRing_smul_def, map_mul]; ring
    rw [e]
    exact (G.sub I).smul_mem _ hzt

omit [Algebra S O] [IsScalarTower S O Ω] in

theorem mem_secs_baseChange {G : SubSystem S x Ω} {y : Ω} (hy : y ∈ G.secs) :
    y ∈ (G.baseChange O).secs := by
  simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hy ⊢
  exact fun I => Submodule.subset_span (hy I)

theorem exists_mul_mem_secs {G : SubSystem S x Ω} {z : Ω} (hz : z ∈ (G.baseChange O).secs) :
    ∃ t : S, t ∉ 𝔪 ∧ algebraMap S Ω t * z ∈ G.secs := by
  classical
  simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hz ⊢
  choose t ht hzt using fun I => exists_mul_mem_sub 𝔪 (hz I)
  refine ⟨∏ I, t I, fun h => ?_, fun I => ?_⟩
  · obtain ⟨I, -, hI⟩ := (Ideal.IsPrime.prod_mem_iff (hp := inferInstance)).mp h
    exact ht I hI
  · rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ I), map_mul, mul_comm (algebraMap S Ω (t I)),
      mul_assoc, ← Algebra.smul_def]
    exact (G.sub I).smul_of_tower_mem _ (hzt I)

theorem exists_inv_algebraMap {t : S} (ht : t ∉ 𝔪) : ∃ u : O, algebraMap O Ω u * algebraMap S Ω t = 1 := by
  obtain ⟨v, hv⟩ := IsLocalization.map_units O (⟨t, ht⟩ : 𝔪.primeCompl)
  refine ⟨(v⁻¹ : Oˣ), ?_⟩
  rw [IsScalarTower.algebraMap_apply S O Ω, ← map_mul]
  change algebraMap O Ω ((v⁻¹ : Oˣ) * algebraMap S O t) = 1
  rw [← hv, Units.inv_mul, map_one]

include 𝔪 in

theorem idealSys_localize (pp' : Ideal (Poly O N)) :
    idealSys x pp' =
      (idealSys x (pp'.comap (map (algebraMap S O) : Poly S N →+* Poly O N))).baseChange O := by
  refine SubSystem.ext_sub fun I => ?_
  change idealMod pp' I = Submodule.span (chartRing O x I)
    (idealMod (pp'.comap (map (algebraMap S O) : Poly S N →+* Poly O N)) I : Set Ω)
  simp only [idealMod]
  rw [span_baseChange_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    obtain ⟨t, ht, g, s₀, hg, hs₀, hs₀e, hmap, hval⟩ := exists_lift_frac 𝔪 hfe hs hse
    obtain ⟨u, hu⟩ := exists_inv_algebraMap 𝔪 (O := O) (Ω := Ω) ht
    have hg' : g ∈ pp'.comap (map (algebraMap S O) : Poly S N →+* Poly O N) := by
      rw [Ideal.mem_comap]
      change map (algebraMap S O) g ∈ pp'
      rw [hmap]
      exact Ideal.mul_mem_left _ _ hf
    have e' : aeval x f / aeval x s = (⟨algebraMap O Ω u, Subalgebra.algebraMap_mem _ u⟩ : chartRing O x I) •
        (aeval x g / aeval x s₀) := by
      rw [chartRing_smul_def, ← hval, ← mul_assoc, hu, one_mul]
    rw [SetLike.mem_coe, e']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, s₀, e, hg', hs₀, hg, hs₀e, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨g, s, e, hg, hs, hge, hse, rfl⟩
    exact Submodule.subset_span ⟨map (algebraMap S O) g, map (algebraMap S O) s, e, hg,
      map_mem_monos_baseChange hs, hge.map _, hse.map _, by
        rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩

omit [IsScalarTower S O Ω] in

theorem length_eq_of_killed {Q : Type*} [AddCommGroup Q] [Module O Q] [Module S Q] [IsScalarTower S O Q]
    (hkill : ∀ m ∈ 𝔪, ∀ q : Q, m • q = 0) : Module.length S Q = Module.length O Q := by
  have stable : ∀ (P : Submodule S Q) (o : O) (n : Q), n ∈ P → o • n ∈ P := by
    intro P o n hn
    obtain ⟨⟨a, ⟨t, ht⟩⟩, h⟩ := IsLocalization.surj 𝔪.primeCompl o
    obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv (inferInstance : 𝔪.IsMaximal) ht
    have h' : algebraMap S O y * algebraMap S O t + algebraMap S O i = 1 := by
      rw [← map_mul, ← map_add, hyi, map_one]
    have ho : o = algebraMap S O (y * a) + o * algebraMap S O i := by
      simp only at h
      rw [map_mul]
      linear_combination (algebraMap S O y) * h - o * h'
    rw [ho, add_smul, mul_smul, algebraMap_smul, algebraMap_smul, hkill i hi n, smul_zero, add_zero]
    exact P.smul_mem _ hn
  let e : Submodule O Q ≃o Submodule S Q :=
    { toFun := fun P => P.restrictScalars S
      invFun := fun P => { toAddSubmonoid := P.toAddSubmonoid, smul_mem' := fun o n hn => stable P o n hn }
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  rw [Module.length_eq_height, Module.length_eq_height, ← Order.height_orderIso e ⊤, e.map_top]

end Local

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleRingFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

theorem AmpleRingFinite.proof (hint : AmpleRingIntegral.Statement) (hft : AmpleRingFiniteType.Statement) :
    AmpleRingFinite.Statement := by
  intro S _ N Ω _ _ x H D j hj
  have hsub : ∀ l I, D.h l ∈ (H.pow D.m).sub I := by
    intro l I
    have := D.mem_secs l
    rw [SubSystem.secs, Submodule.mem_iInf] at this
    exact this I
  let R := TranslateEq.ampleSub H.toSubSystem D.m (D.h j) (hsub j)
  have hBR : ∀ b ∈ ampleBase (S := S) D.h j, b ∈ R := by
    intro b hb
    refine (Algebra.adjoin_le (R := S) (S := R) ?_) hb
    rintro _ ⟨l, rfl⟩
    refine Set.mem_iInter.mpr fun I => ⟨1, ?_⟩
    rw [pow_one, div_mul_cancel₀ _ hj, Nat.mul_one]
    exact hsub l I
  obtain ⟨r, g, hgR, hgen⟩ := hft S N Ω x H D j hj
  have hfg : Subalgebra.toSubmodule (Algebra.adjoin (ampleBase (S := S) D.h j) (Set.range g)) |>.FG :=
    fg_adjoin_of_finite (Set.finite_range g) (by
      rintro _ ⟨l, rfl⟩
      exact hint S N Ω x H D j hj (g l) (hgR l))
  obtain ⟨n, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hAR : ∀ y ∈ Algebra.adjoin (ampleBase (S := S) D.h j) (Set.range g), y ∈ R := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨l, rfl⟩ := hy
      exact hgR l
    | algebraMap c => exact hBR c c.2
    | add y z _ _ hy hz => exact R.add_mem hy hz
    | mul y z _ _ hy hz => exact R.mul_mem hy hz
  refine ⟨n, b, fun l => hAR _ ?_, fun f hf => ?_⟩
  · have hl : b l ∈ Submodule.span (ampleBase (S := S) D.h j) (Set.range b) :=
      Submodule.subset_span ⟨l, rfl⟩
    rw [hb] at hl
    exact hl
  · rw [hb]
    exact hgen hf

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Tilde

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem FinGradedSub.tildeSys_natCast_eq_twist (M : FinGradedSub (S := S) (x := x) E) (a : ℕ) :
    M.tildeSys (a : ℤ) = (M.tildeSys 0).twist (twistSys S x (a : ℤ)) := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have hA : x i ^ a ∈ twistMod S x (a : ℤ) I := by
    rw [twistMod_eq_span _ I hi, zpow_natCast]
    exact Submodule.mem_span_singleton_self _
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    refine Submodule.subset_span ⟨x i ^ a, hA, (aeval x (s * X i ^ a))⁻¹ • m,
      Submodule.subset_span ⟨m, s * X i ^ a, b, e + a, mul_mem hs (pow_mem (X_mem_monos hi) a),
        hse.mul (isHomogeneous_X_pow i a), hm, by push_cast; omega, rfl⟩, ?_⟩
    rw [smul_smul, map_mul, map_pow, aeval_X, mul_inv, ← mul_assoc, mul_comm (x i ^ a),
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero a hxi), mul_one]
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x (a : ℤ) I at hq
    rw [twistMod_eq_span _ I hi, zpow_natCast, Submodule.mem_span_singleton] at hq
    obtain ⟨β, rfl⟩ := hq
    have key : x i ^ a • y ∈ M.tilde (a : ℤ) I := by
      refine Submodule.span_induction (p := fun y _ => x i ^ a • y ∈ M.tilde (a : ℤ) I) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩
        refine Submodule.subset_span ⟨aeval x (X i ^ a : Poly S N) • m, s, b + a, e, hs, hse,
          M.smul_mem a b _ m (isHomogeneous_X_pow i a) hm, by omega, ?_⟩
        rw [smul_smul, smul_smul, map_pow, aeval_X, mul_comm]
      · rw [smul_zero]
        exact Submodule.zero_mem _
      · intro y y' _ _ h h'
        rw [smul_add]
        exact Submodule.add_mem _ h h'
      · intro c y _ h
        rw [Subalgebra.smul_def, smul_smul, mul_comm, ← smul_smul, ← Subalgebra.smul_def]
        exact Submodule.smul_mem _ c h
    rw [SetLike.mem_coe, chartRing_smul_def, ← smul_smul, ← Subalgebra.smul_def]
    exact Submodule.smul_mem _ β key

end Tilde

theorem AmpleVanish.proof (hC : VeryAmpleCech.Statement.{u, v, w}) (hE : Extension.Statement.{u, v, w})
    (hT : TildeVanish.Statement.{u, v, w}) : AmpleVanish.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ F hF H hH
  obtain ⟨r, h, hh⟩ := hH
  obtain ⟨F', hF', hiso⟩ := hC S Ω N x E F hF H r h hh
  obtain ⟨M, -, hM⟩ := hE S Ω r h E F' hF'
  obtain ⟨c₀, hc₀⟩ := hT S Ω r h E M
  refine ⟨c₀.toNat, fun i a hi ha => ?_⟩
  obtain ⟨e⟩ := hiso a i
  have hsys : F'.toSubSystem = M.tildeSys 0 := SubSystem.ext_sub fun J => (hM J).symm
  have hv := hc₀ i hi a (by omega)
  rw [M.tildeSys_natCast_eq_twist a, ← hsys] at hv
  exact e.toEquiv.subsingleton

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section ClaimLemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem coordGraded_tilde_mem_chartRing {I : Chart x} {y : Ω}
    (hy : y ∈ (coordGraded k x).tilde 0 I) : y ∈ chartRing k x I := by
  refine Submodule.span_induction (p := fun y _ => y ∈ chartRing k x I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hm' : m ∈ Submodule.span k {z | ∃ (f : Poly k N) (e' : ℕ), f.IsHomogeneous e' ∧
        (e' : ℤ) = a ∧ z = aeval x f} := hm
    refine Submodule.span_induction (p := fun m _ => (aeval x s)⁻¹ • m ∈ chartRing k x I)
      ?_ ?_ ?_ ?_ hm'
    · rintro _ ⟨f, e', hf, he', rfl⟩
      have hee : e' = e := by omega
      subst hee
      exact ⟨f, s, e', hs, hf, hse, by rw [smul_eq_mul, div_eq_inv_mul]⟩
    · rw [smul_zero]; exact (chartRing k x I).zero_mem
    · intro a b _ _ ha hb; rw [smul_add]; exact (chartRing k x I).add_mem ha hb
    · intro r a _ ha; rw [smul_comm]; exact (chartRing k x I).smul_mem ha r
  · exact (chartRing k x I).zero_mem
  · intro a b _ _ ha hb; exact (chartRing k x I).add_mem ha hb
  · intro a y _ hy; rw [chartRing_smul_def]; exact (chartRing k x I).mul_mem a.2 hy

theorem coordGraded_tildeSys_twist (X : SubSystem k x Ω) :
    ((coordGraded k x).tildeSys 0).twist X = X := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    have hyA := coordGraded_tilde_mem_chartRing hy
    have hqy : q • y = (⟨y, hyA⟩ : chartRing k x I) • q := by
      rw [smul_eq_mul, chartRing_smul_def, mul_comm]
    rw [SetLike.mem_coe, hqy]
    exact (X.sub I).smul_mem _ hq
  · intro q hq
    refine Submodule.subset_span ⟨q, hq, 1, ?_, by rw [smul_eq_mul, mul_one]⟩
    exact Submodule.subset_span ⟨1, 1, 0, 0, one_mem _, isHomogeneous_one _ _,
      Submodule.subset_span ⟨1, 0, isHomogeneous_one _ _, by simp, by simp⟩, by simp, by simp⟩

theorem twist_tildeSys_mono {M₁ M₂ : FinGradedSub (S := k) (x := x) Ω}
    (h : ∀ c, M₂.piece c ≤ M₁.piece c) (X : SubSystem k x Ω) (I : Chart x) :
    ∀ y ∈ ((M₂.tildeSys 0).twist X).sub I, y ∈ ((M₁.tildeSys 0).twist X).sub I := by
  intro y hy
  refine Submodule.span_mono ?_ hy
  rintro _ ⟨q, hq, z, hz, rfl⟩
  refine ⟨q, hq, z, Submodule.span_mono ?_ hz, rfl⟩
  rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
  exact ⟨m, s, a, e, hs, hse, h a hm, hae, rfl⟩

variable (T : StepData k x) (Jg : FinGradedSub (S := k) (x := x) Ω)
  (hJg : ∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧
    f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f})

include hJg in

theorem claim_le : ∀ c, Jg.piece c ≤ (coordGraded k x).piece c := by
  intro c
  rw [hJg]
  refine Submodule.span_mono ?_
  rintro _ ⟨f, e, -, hf, he, rfl⟩
  exact ⟨f, e, hf, he, rfl⟩

include hJg in

theorem claim_kill : ∀ (f : Poly k N) (e : ℕ), f ∈ T.J → f.IsHomogeneous e → ∀ (a : ℤ),
    ∀ z ∈ (coordGraded k x).piece a, aeval x f • z ∈ Jg.piece (a + e) := by
  intro f e hf hfe a z hz
  have hz' : z ∈ Submodule.span k {z | ∃ (g : Poly k N) (e' : ℕ), g.IsHomogeneous e' ∧
      (e' : ℤ) = a ∧ z = aeval x g} := hz
  refine Submodule.span_induction (p := fun z _ => aeval x f • z ∈ Jg.piece (a + e)) ?_ ?_ ?_ ?_ hz'
  · rintro _ ⟨g, e', hg, he', rfl⟩
    rw [hJg]
    exact Submodule.subset_span ⟨f * g, e + e', T.J.mul_mem_right g hf, hfe.mul hg,
      by push_cast; omega, by rw [map_mul, smul_eq_mul]⟩
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha

end ClaimLemmas

theorem ClaimVanish.proof (h₁ : StepTwo.Statement.{u, w, w}) (h₂ : TwistVanish.Statement.{u, w})
    (h₃ : ClaimSeq.Statement.{u, w}) : ClaimVanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK
  obtain ⟨Jg, hJg, hseq⟩ := h₃ k Ω N x T
  obtain ⟨cS, hS⟩ := h₁ k Ω N x T hK Ω (coordGraded k x) Jg (claim_le T Jg hJg)
    (claim_kill T Jg hJg)
  obtain ⟨cB, hB⟩ := h₂ k Ω N x (twistBundle k x 0) (twistBundle k x 1) N x (twist_hyps k N x).1
    (twist_hyps k N x).2
  refine ⟨max cS cB, fun b => ?_⟩
  induction b with
  | zero =>
    intro c hc
    have h0 := hB 0 c (le_trans (le_max_right _ _) hc)
    have e : ((twistBundle k x 0).twist ((twistBundle k x 1).pow 0)).twist (twistSys k x c) =
        (T.L.pow 0).twist (twistSys k x c) := by
      show ((twistSys k x 0).twist (twistSys k x 0)).twist (twistSys k x c) =
        (twistSys k x 0).twist (twistSys k x c)
      rw [twistSys_zero_twist]
    rw [e] at h0
    exact h0
  | succ b ih =>
    intro c hc
    have hq := hS (b + 1) c (le_trans (le_max_left _ _) hc)
    rw [coordGraded_tildeSys_twist] at hq
    refine SubSystem.subsingleton_H_one_of_quot _
      ((Jg.tildeSys 0).twist ((T.L.pow (b + 1)).twist (twistSys k x c))) ?_ ?_ hq
    · intro I y hy
      have hy' := twist_tildeSys_mono (claim_le T Jg hJg) _ I y hy
      rwa [coordGraded_tildeSys_twist] at hy'
    · exact SubSystem.subsingleton_H_one_of_smul _ _ T.si T.si_ne (hseq b c)
        (ih (c + T.c₁) (le_trans hc (by linarith [T.c₁_pos])))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PLineTwist
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u w

theorem LineTwist.proof : LineTwist.Statement.{u, w} :=
  fun _ _ _ _ _ _ _ Q₁ Q₂ => ⟨Q₁.tensorProd Q₂, rfl⟩

end GroundTheory.Heights₂.Heights.Kleiman
end

