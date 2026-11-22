import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlus
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisMap

theorem smodEq_iff {R : Type} [CommRing R] (a : R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule R R)] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem complete_of_sandwich (p N : ℕ) {B R : Type} [CommRing B] [CommRing R]
    (hB : IsAdicComplete (Ideal.span {(p : B)}) B) (g : B →+* R) (hg : Function.Injective g)
    (h : ∀ r : R, ∃ b : B, (p : R) ^ N * r = g b) : IsAdicComplete (Ideal.span {(p : R)}) R := by
  have key : ∀ (b : B) (k : ℕ), (p : R) ^ (k + N) ∣ g b → (p : B) ^ k ∣ b := by
    rintro b k ⟨y, hy⟩
    obtain ⟨c, hc⟩ := h y
    refine ⟨c, hg ?_⟩
    rw [hy, map_mul, map_pow, map_natCast, ← hc]
    ring
  refine { haus' := fun x hx => ?_, prec' := fun x hx => ?_ }
  · simp only [smodEq_iff, sub_zero] at hx
    obtain ⟨y, hy⟩ := hx N
    obtain ⟨b, hb⟩ := h y
    have : b = 0 := by
      refine IsHausdorff.haus hB.toIsHausdorff b fun k => ?_
      rw [smodEq_iff, sub_zero]
      exact key b k (by rw [← hb, ← hy]; exact hx _)
    rw [hy, hb, this, map_zero]
  · simp only [smodEq_iff] at hx ⊢
    have h1 : ∀ k, ∃ b : B, x (k + N) - x N = g b := fun k => by
      obtain ⟨y, hy⟩ := hx (Nat.le_add_left N k)
      obtain ⟨b, hb⟩ := h y
      exact ⟨-b, by rw [map_neg, ← hb, ← hy]; ring⟩
    choose b hb using h1
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hB.toIsPrecomplete (f := b) (fun {m n} hmn => by
      rw [smodEq_iff]
      refine key _ _ ?_
      rw [map_sub, ← hb, ← hb, sub_sub_sub_cancel_right]
      exact hx (Nat.add_le_add_right hmn N))
    refine ⟨x N + g L, fun n => ?_⟩
    have h2 := map_dvd g ((smodEq_iff _ _ _ _).1 (hL n))
    rw [map_pow, map_natCast, map_sub, ← hb] at h2
    have h3 := dvd_add (hx (Nat.le_add_right n N)) h2
    convert h3 using 1
    ring

theorem exists_extend (p : ℕ) {D R : Type} [CommRing D] [CommRing R]
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) (f : D →+* R) :
    ∃ F : AdicCompletion (Ideal.span {(p : D)}) D →+* R, ∀ d, F (algebraMap D _ d) = f d := by
  have hf : (Ideal.span {(p : D)}).map f ≤ Ideal.span {(p : R)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  refine ⟨((AdicCompletion.ofAlgEquiv (Ideal.span {(p : R)})).symm : _ →+* R).comp
    (GlobalTheory.AdicMaps.adicMap (Ideal.span {(p : D)}) (Ideal.span {(p : R)}) f
      (Ideal.map_le_iff_le_comap.1 hf)), fun d => ?_⟩
  rw [RingHom.comp_apply, GlobalTheory.AdicMaps.adicMap_alg]
  exact (AdicCompletion.ofAlgEquiv (Ideal.span {(p : R)})).symm_apply_apply (f d)

theorem extend_unique (p : ℕ) {D R : Type} [CommRing D] [CommRing R]
    (hR : IsHausdorff (Ideal.span {(p : R)}) R) (F G : AdicCompletion (Ideal.span {(p : D)}) D →+* R)
    (h : ∀ d, F (algebraMap D _ d) = G (algebraMap D _ d)) : F = G := by
  ext1 x
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hR _ fun k => ?_
  rw [smodEq_iff, sub_zero]
  obtain ⟨s, z, rfl⟩ := GlobalTheory.PrincipalCompletion.dense (p : D) x k
  refine ⟨F z - G z, ?_⟩
  simp only [map_add, map_mul, map_pow, map_natCast, h]
  ring

theorem exists_lift (p : ℕ) {D P : Type} [CommRing D] [CommRing P] (I : Ideal P) (f : D →+* P)
    (h : ∀ n : ℕ, IsAdicComplete
      (Ideal.span {(p : ((Ideal.Quotient.mk (I ^ n)).comp f).range)})
      ((Ideal.Quotient.mk (I ^ n)).comp f).range) :
    ∃ j : AdicCompletion (Ideal.span {(p : D)}) D →+* AdicCompletion I P,
      (∀ d, j (algebraMap D _ d) = algebraMap P _ (f d)) ∧
      ∀ n x, ∃ d, AdicCompletion.evalₐ I n (j x) = Ideal.Quotient.mk _ (f d) := by
  choose F hF using fun n => exists_extend p (h n) ((Ideal.Quotient.mk (I ^ n)).comp f).rangeRestrict
  have hc : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp
      ((Subring.subtype _).comp (F n)) = (Subring.subtype _).comp (F m) := by
    intro m n hle
    have hm : ∀ x, (Ideal.Quotient.factorPow I hle).comp ((Subring.subtype _).comp (F n)) x ∈
        ((Ideal.Quotient.mk (I ^ m)).comp f).range := fun x => by
      obtain ⟨d, hd⟩ := (F n x).2
      refine ⟨d, ?_⟩
      simp only [RingHom.comp_apply, Subring.subtype_apply, ← hd]
      rfl
    have := extend_unique p (h m).toIsHausdorff (RingHom.codRestrict _ _ hm) (F m) fun d => by
      refine Subtype.ext ?_
      simp only [RingHom.codRestrict_apply, RingHom.comp_apply, hF]
      rfl
    rw [← this]
    rfl
  refine ⟨AdicCompletion.liftRingHom I (fun n => (Subring.subtype _).comp (F n)) hc, fun d => ?_,
    fun n x => ?_⟩
  · refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [AdicCompletion.evalₐ_liftRingHom, RingHom.comp_apply, hF]
    simp [AdicCompletion.algebraMap_apply]
  · obtain ⟨d, hd⟩ := (F n x).2
    exact ⟨d, by rw [AdicCompletion.evalₐ_liftRingHom]; exact hd.symm⟩

variable (l : ℕ) [Fact l.Prime]

theorem exists_isEps : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  refine ⟨ε, Subtype.ext ?_, fun h2 => h1 ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact this
  · have h3 := h 1
    have h4 : rootT ε 1 = 1 := h2
    rw [h4] at h3
    exact (algebraMap (Om l) ℂ_[l]).injective (by rw [← h3, map_one]; rfl)

theorem bound (n : ℕ) (s : Per.AinfP l) (hs : s ∈ Per.Acris0 l) : ∃ a : Per.Ainf l,
    (l : Per.AinfP l) ^ n * s - algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ n := by
  obtain ⟨e, he⟩ := exists_isEps l
  rw [mem_Acris0_iff_span l e he] at hs
  induction hs using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := hy
    rcases le_total k n with hkn | hkn
    · obtain ⟨c, hc⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l k
      have hc' : ((k.factorial : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.zA l c) =
          (l : Per.AinfP l) ^ k := by
        have h := congrArg ((algebraMap (Per.Ainf l) (Per.AinfP l)).comp (Per.zA l)) hc
        rwa [map_mul, map_natCast, map_pow, map_natCast, RingHom.comp_apply] at h
      refine ⟨(l : Per.Ainf l) ^ (n - k) * Per.zA l c * xi e ^ k, ?_⟩
      have : (l : Per.AinfP l) ^ n * y = algebraMap (Per.Ainf l) (Per.AinfP l)
          ((l : Per.Ainf l) ^ (n - k) * Per.zA l c * xi e ^ k) := by
        rw [map_mul, map_mul, map_pow, map_pow, map_natCast, ← hk]
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
        rw [Nat.add_sub_cancel_left, pow_add, ← hc']
        ring
      rw [this, sub_self]
      exact zero_mem _
    · refine ⟨0, ?_⟩
      obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero).exists_left_inv
      have hy : y = u * algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ k := by
        rw [← hk, ← mul_assoc, hu, one_mul]
      rw [map_zero, sub_zero, hy, GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
        (Ideal.pow_le_pow_right hkn (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k)))
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    convert add_mem ha hb using 1
    rw [map_add]
    ring
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨c * a, ?_⟩
    convert Ideal.mul_mem_left _ (algebraMap (Per.Ainf l) (Per.AinfP l) c) ha using 1
    rw [map_mul, Algebra.smul_def]
    ring

theorem algebraMap_mem_kerTheta_pow_iff₂ (e : Per.Fl l) (he : IsEps e) (n : ℕ) (a : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ n ↔ a ∈ Ideal.span {xi e ^ n} := by
  have h1 : Per.kerP l ^ n = (Ideal.span {xi e ^ n}).map (algebraMap (Per.Ainf l) (Per.AinfP l)) := by
    rw [GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow]
  rw [h1]
  refine ⟨fun h => ?_, Ideal.mem_map_of_mem _⟩
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers (l : Per.Ainf l))] at h
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := h
  rw [Ideal.mem_span_singleton] at hk ⊢
  induction k with
  | zero => simpa using hk
  | succ k ih =>
    refine ih ((GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l e he n).1 _ ?_)
    convert hk using 1
    ring

theorem range_complete (n : ℕ) : IsAdicComplete
    (Ideal.span {(l : ((Ideal.Quotient.mk (Per.kerP l ^ n)).comp (Per.Acris0 l).val.toRingHom).range)})
    ((Ideal.Quotient.mk (Per.kerP l ^ n)).comp (Per.Acris0 l).val.toRingHom).range := by
  obtain ⟨e, he⟩ := exists_isEps l
  let g0 : Per.Ainf l →+* ((Ideal.Quotient.mk (Per.kerP l ^ n)).comp (Per.Acris0 l).val.toRingHom).range :=
    ((Ideal.Quotient.mk (Per.kerP l ^ n)).comp (Per.Acris0 l).val.toRingHom).rangeRestrict.comp
      (algebraMap (Per.Ainf l) (Per.Acris0 l))
  have hg0 : ∀ a, (g0 a).1 = Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a) := fun _ => rfl
  have hk : ∀ a, g0 a = 0 ↔ a ∈ Ideal.span {xi e ^ n} := fun a => by
    rw [← algebraMap_mem_kerTheta_pow_iff₂ l e he, ← Ideal.Quotient.eq_zero_iff_mem, ← hg0]
    exact Subtype.ext_iff
  refine complete_of_sandwich l n (GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l e he n).2
    (Ideal.Quotient.lift _ g0 fun a ha => (hk a).2 ha) ?_ ?_
  · refine RingHom.lift_injective_of_ker_le_ideal _ _ fun a ha => (hk a).1 ha
  · rintro ⟨_, s, rfl⟩
    obtain ⟨a, ha⟩ := bound l n s s.2
    refine ⟨Ideal.Quotient.mk _ a, Subtype.ext ?_⟩
    rw [Ideal.Quotient.lift_mk, hg0, ← (Ideal.Quotient.eq).2 ha, map_mul, map_pow, map_natCast,
      Subring.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
    rfl

end GlobalTheory.MemLoc.CrisMap

namespace GlobalTheory.MemLoc

theorem exists_isCrisP : ∀ (l : ℕ) [Fact l.Prime], ∃ j : Per.Acris l →+* Per.BdRp l, IsCrisP j := by
  intro l _
  obtain ⟨j, h0, h1⟩ := CrisMap.exists_lift l (Per.kerP l) (Per.Acris0 l).val.toRingHom
    (CrisMap.range_complete l)
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  obtain ⟨e', he0, he1⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  refine ⟨e'.symm.toRingHom.comp (j.comp e.toRingHom), fun a => ?_, fun n => ⟨n, fun x => ?_⟩⟩
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [he, h0, RingEquiv.symm_apply_eq, he0]
    rfl
  · obtain ⟨d, hd⟩ := h1 n (e x)
    obtain ⟨a, ha⟩ := CrisMap.bound l n d d.2
    refine ⟨a, ?_⟩
    have h2 : Per.ev l n (e'.symm (j (e x))) = Ideal.Quotient.mk _ (d : Per.AinfP l) := by
      rw [← he1, RingEquiv.apply_symm_apply]
      exact hd
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [map_mul, map_pow, map_natCast, ← (Ideal.Quotient.eq).2 ha, map_mul, map_pow, map_natCast, h2]

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMaxUnramifiedEmbeddingIntoBcris
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_factor_of_range {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* D) (ι : B →+* D)
    (hι : Function.Injective ι) (h : ∀ x, f x ∈ ι.range) : ∃ u : A →+* B, ∀ x, ι (u x) = f x := by
  let e : B ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b hab => hι (congrArg Subtype.val hab), ι.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (f.codRestrict ι.range h), fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (f.codRestrict ι.range h x))

theorem padic_mem_range {l : ℕ} [Fact l.Prime] {B D : Type} [CommRing B] [CommRing D] (g : ℚ_[l] →+* D)
    (ι : B →+* D) (hz : ∀ z : ℤ_[l], g z ∈ ι.range) (hl : IsUnit (l : B)) (q : ℚ_[l]) : g q ∈ ι.range := by
  obtain ⟨w, hw⟩ := hl.exists_right_inv
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have h1 : g (l : ℚ_[l])⁻¹ = ι w := by
    have a : (l : D) * ι w = 1 := by simpa using congrArg ι hw
    have b : g (l : ℚ_[l])⁻¹ * (l : D) = 1 := by
      rw [← map_natCast g, ← map_mul, inv_mul_cancel₀ hl0, map_one]
    calc g (l : ℚ_[l])⁻¹ = g (l : ℚ_[l])⁻¹ * ((l : D) * ι w) := by rw [a, mul_one]
      _ = ι w := by rw [← mul_assoc, b, one_mul]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(l : ℚ_[l]) ^ n * q‖ ≤ 1 := by
    have hp : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp).mul_const ‖q‖
    rw [zero_mul] at ht
    obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds one_pos)).exists
    exact ⟨n, by rwa [norm_mul, norm_pow]⟩
  have e : q = ((l : ℚ_[l])⁻¹) ^ n * ((⟨_, hn⟩ : ℤ_[l]) : ℚ_[l]) := by
    change q = _ * ((l : ℚ_[l]) ^ n * q)
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hl0, one_pow, one_mul]
  rw [e, map_mul, map_pow, h1]
  exact mul_mem (pow_mem (ι.mem_range_self w) n) (hz _)

theorem exists_unram_to_cris : ∀ (l : ℕ) [Fact l.Prime], ∀ (o : Om l →+* Per.BdRp l) (ι : Per.Bcris l →+* Per.BdR l), IsSec o → Function.Injective ι → (∀ a : Per.Ainf l, ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a)) → IsUnit (l : Per.Bcris l) → ∃ u : ↥(MaximalUnramifiedExtension l) →+* Per.Bcris l, ∀ c : ↥(MaximalUnramifiedExtension l), ι (u c) = algebraMap (Per.BdRp l) (Per.BdR l) (o (c : Om l)) := by
  intro l _ o ι ho hι ha hl
  let f : Om l →+* Per.BdR l := (algebraMap (Per.BdRp l) (Per.BdR l)).comp o
  have hq : ∀ q : ℚ_[l], f (algebraMap ℚ_[l] (Om l) q) ∈ ι.range :=
    padic_mem_range (f.comp (algebraMap ℚ_[l] (Om l))) ι
      (fun z => ⟨Per.aB l (Per.zA l z), (ha _).trans (by
        rw [← ho.z]; rfl)⟩) hl
  let S : Subalgebra ℚ_[l] (Om l) :=
    { (ι.range.comap f).toSubsemiring with algebraMap_mem' := hq }
  have key : ∀ x ∈ MaximalUnramifiedExtension l, f x ∈ ι.range := by
    intro x hx
    unfold MaximalUnramifiedExtension at hx
    rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun y _ => Algebra.IsAlgebraic.isAlgebraic y)] at hx
    refine (Algebra.adjoin_le (S := S) ?_) hx
    rintro c ⟨m, h0, h1, h2⟩
    obtain ⟨⟨xb, hxb⟩, h⟩ := GlobalTheory.T.rootOfUnity_prime_to_teichmuller_lift l o ho c m h0 h1 h2
    refine ⟨Per.aB l (Per.tm xb), ?_⟩
    exact (ha _).trans (by rw [(h xb hxb).2.2]; rfl)
  exact exists_factor_of_range (f.comp (MaximalUnramifiedExtension l).val.toRingHom) ι hι (fun x => key x x.2)

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
section
open IsLocalRing

namespace GlobalTheory

theorem finite_integralClosure_of_isLocalization {R S L : Type*} [CommRing R] [CommRing S]
    [CommRing L] [Algebra R S] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    (M : Submonoid R) [IsLocalization M S] [Module.Finite R (integralClosure R L)] :
    Module.Finite S (integralClosure S L) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := integralClosure R L)
  let f : integralClosure R L → integralClosure S L := fun z => ⟨z, IsIntegral.tower_top z.2⟩
  refine ⟨⟨s.image f, ?_⟩⟩
  rw [eq_top_iff]
  rintro y -
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M (Rₘ := S) (y : L) y.2
  have key : ∀ z ∈ Submodule.span R (s : Set (integralClosure R L)),
      f z ∈ Submodule.span S (↑(s.image f) : Set (integralClosure S L)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem f hx))
    | zero =>
      have : f 0 = 0 := rfl
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : f (x + y) = f x + f y := rfl
      rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : f (a • x) = algebraMap R S a • f x := by
        apply Subtype.ext
        change a • (x : L) = algebraMap R S a • (x : L)
        rw [algebraMap_smul]
      rw [this]; exact Submodule.smul_mem _ _ hx
  have hz : (⟨m • (y : L), hm⟩ : integralClosure R L) ∈ Submodule.span R (s : Set _) :=
    hs ▸ Submodule.mem_top
  have e : y = IsLocalization.mk' S (1 : R) m • f ⟨m • (y : L), hm⟩ := by
    apply Subtype.ext
    change (y : L) = IsLocalization.mk' S (1 : R) m • ((m : R) • (y : L))
    rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S L, ← mul_assoc,
      ← map_mul, IsLocalization.mk'_spec, map_one, map_one, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ (key _ hz)

theorem finite_integralClosure_of_essFiniteType_int :
    ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
      Module.Finite D (integralClosure D (FractionRing D)) := by
  intro D _ _ _
  obtain ⟨S₀, M, hft, hloc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra ℤ D).mp inferInstance
  let K := FractionRing D
  have hinj : Function.Injective (algebraMap S₀ D) := Subtype.val_injective
  haveI hfr : IsFractionRing S₀ K := by
    have h := IsLocalization.localization_localization_isLocalization_of_has_all_units M (nonZeroDivisors D) K
      (fun x hx => hx.mem_nonZeroDivisors)
    have e : (nonZeroDivisors D).comap (algebraMap S₀ D) = nonZeroDivisors S₀ := by
      ext x
      simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, ne_eq]
      exact (map_eq_zero_iff _ hinj).not
    rw [e] at h
    exact h
  suffices h : Module.Finite S₀ (integralClosure S₀ K) from
    finite_integralClosure_of_isLocalization M
  rcases CharP.char_is_prime_or_zero D (ringChar D) with hp | h0
  · haveI : Fact (ringChar D).Prime := ⟨hp⟩
    haveI : CharP D (ringChar D) := ringChar.charP D
    haveI : CharP S₀ (ringChar D) := ⟨fun n => by
      rw [← map_eq_zero_iff _ hinj, map_natCast, CharP.cast_eq_zero_iff D]⟩
    letI : Algebra (ZMod (ringChar D)) S₀ := (ZMod.castHom dvd_rfl S₀).toAlgebra
    haveI : Algebra.FiniteType (ZMod (ringChar D)) S₀ :=
      .of_restrictScalars_finiteType ℤ (ZMod (ringChar D)) S₀
    exact NormFin.finite_integralClosure_of_perfectField (ZMod (ringChar D)) S₀ K K
  · haveI : CharZero D := (CharP.ringChar_zero_iff_CharZero D).mp h0
    haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective D K)
    haveI : Algebra.EssFiniteType S₀ D := .of_isLocalization D M
    haveI : Algebra.EssFiniteType D K := .of_isLocalization K (nonZeroDivisors D)
    haveI : Algebra.EssFiniteType S₀ K := .comp S₀ D K
    exact finite_integralClosure_of_essFiniteType_field ℤ S₀ K

example : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
    Module.Finite D (integralClosure D (FractionRing D)) := finite_integralClosure_of_essFiniteType_int

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrmOfPosDef
section
open NumberField
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.AmbCrd

open Formalism.L2.DIV

section Frames

variable {K : Type} [Field K] [NumberField K]

open Classical in

def frm {n : ℕ} (H : Matrix (Fin n) (Fin n) K) : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun v => if (H.map v.embedding).PosDef then frameOf (H.map v.embedding) else 1

theorem frm_det {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) : IsUnit (frm H v).det := by
  unfold frm
  split_ifs with h
  · exact (frameOfSpec _ _ h).1
  · simp

theorem frm_of_posDef {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (h : (H.map v.embedding).PosDef) :
    frm H v = frameOf (H.map v.embedding) := by
  unfold frm
  rw [if_pos h]

end Frames

section Coord

variable {K : Type} [Field K]

def rdx {a b : ℕ} (h : a = b) : (Fin b → K) ≃ₗ[K] (Fin a → K) := LinearEquiv.funCongrLeft K K (finCongr h)

theorem rdx_apply {a b : ℕ} (h : a = b) (x : Fin b → K) (i : Fin a) : rdx h x i = x (Fin.cast h i) := rfl

theorem rdx_refl {a : ℕ} (h : a = a) (x : Fin a → K) : rdx h x = x := by
  funext i
  rw [rdx_apply]
  rfl

end Coord

end GlobalTheory.AmbCrd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusAcrisDecompositionMuPowerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_acris_decomposition_mu_power : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ w : Per.Acris l, (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) → ∀ y : Per.Acris l, ∃ (a : Per.Ainf l) (z : Per.Acris l), phiA l y = algebraMap (Per.Ainf l) (Per.Acris l) a + w * z := by
  first | exact @GlobalTheory.MemLoc.phiA_mem_ainf_add | exact GlobalTheory.MemLoc.phiA_mem_ainf_add | (intros; apply GlobalTheory.MemLoc.phiA_mem_ainf_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAbsIrrCharMapRingHomStatement
section
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbsIrrChar_map_ringHom : ∀ {K K' G : Type} [Field K] [Field K'] [CharZero K] [CharZero K'] [Group G] [Fintype G] (φ : K →+* K') (χ : G → K), IsAbsIrrChar χ → IsAbsIrrChar (fun g => φ (χ g)) := by
  first | exact @GlobalTheory.AbsIrrMap.isAbsIrrChar_map | exact GlobalTheory.AbsIrrMap.isAbsIrrChar_map | (intros; apply GlobalTheory.AbsIrrMap.isAbsIrrChar_map <;> assumption)
end

