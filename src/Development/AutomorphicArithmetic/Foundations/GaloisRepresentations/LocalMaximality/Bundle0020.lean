import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0037
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocEq
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section LocEqAux
variable {L : Type} [Field L] [Algebra ℂ L]

private def locRes {R B : Subalgebra ℂ L} (h : R ≤ B) (e : B →ₐ[ℂ] ℂ) : R →ₐ[ℂ] ℂ :=
  e.comp (Subalgebra.inclusion h)

private lemma loc_val_eq {R B : Subalgebra ℂ L} (h : R ≤ B) (e : B →ₐ[ℂ] ℂ)
    (hB : B ≤ loc R (locRes h e)) :
    loc B e = loc R (locRes h e) ∧ ∀ v c, Val B e v c ↔ Val R (locRes h e) v c := by
  have key : ∀ {b v : L} (hb : b ∈ B) (hbv : b * v ∈ B),
      ∃ t : L, ∃ (ht : t ∈ B), e ⟨t, ht⟩ ≠ 0 ∧ t * b ∈ R ∧ t * b * v ∈ R := by
    intro b v hb hbv
    obtain ⟨⟨r, hr⟩, hr0, hrb⟩ := hB hb
    obtain ⟨⟨r', hr'⟩, hr'0, hr'bv⟩ := hB hbv
    refine ⟨r' * r, B.mul_mem (h hr') (h hr), ?_, ?_, ?_⟩
    · rw [show (⟨r' * r, B.mul_mem (h hr') (h hr)⟩ : B) = ⟨r', h hr'⟩ * ⟨r, h hr⟩ from rfl, map_mul]
      exact mul_ne_zero hr'0 hr0
    · rw [mul_assoc]
      exact R.mul_mem hr' hrb
    · have hre : r' * r * b * v = r * (r' * (b * v)) := by ring
      rw [hre]
      exact R.mul_mem hr hr'bv
  refine ⟨le_antisymm ?_ ?_, fun v c => ⟨?_, ?_⟩⟩
  · rintro v ⟨⟨b, hb⟩, hb0, hbv⟩
    obtain ⟨t, ht, ht0, htb, htbv⟩ := key hb hbv
    refine ⟨⟨t * b, htb⟩, ?_, htbv⟩
    show e ⟨t * b, h htb⟩ ≠ 0
    rw [show (⟨t * b, h htb⟩ : B) = ⟨t, ht⟩ * ⟨b, hb⟩ from rfl, map_mul]
    exact mul_ne_zero ht0 hb0
  · rintro v ⟨⟨r, hr⟩, hr0, hrv⟩
    exact ⟨⟨r, h hr⟩, hr0, h hrv⟩
  · rintro ⟨b, hb, hbv, hb0, hval⟩
    obtain ⟨t, ht, ht0, htb, htbv⟩ := key hb hbv
    refine ⟨t * b, htb, htbv, ?_, ?_⟩
    · show e ⟨t * b, h htb⟩ ≠ 0
      rw [show (⟨t * b, h htb⟩ : B) = ⟨t, ht⟩ * ⟨b, hb⟩ from rfl, map_mul]
      exact mul_ne_zero ht0 hb0
    · show e ⟨t * b * v, h htbv⟩ = e ⟨t * b, h htb⟩ * c
      rw [show (⟨t * b * v, h htbv⟩ : B) = ⟨t, ht⟩ * ⟨b * v, hbv⟩ from Subtype.ext (mul_assoc _ _ _),
        show (⟨t * b, h htb⟩ : B) = ⟨t, ht⟩ * ⟨b, hb⟩ from rfl, map_mul, map_mul, hval, mul_assoc]
  · rintro ⟨r, hr, hrv, hr0, hval⟩
    exact ⟨r, h hr, h hrv, hr0, hval⟩

end LocEqAux

section LocEqAux2

private lemma mem_rB_of {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] {d : ℕ} (x : Fin (d + 1) → F) (I : Finset (Fin (d + 1))) {f : F}
    (hf : f ∈ rA ℂ x I) : algebraMap F L f ∈ rB ℂ L x I := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  have hx : algebraMap F L f = algebraMap (rA ℂ x I) L ⟨f, hf⟩ := rfl
  rw [hx]
  exact isIntegral_algebraMap

private lemma div_mem_rA {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → F)
    {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (j : Fin (d + 1)) :
    x j / x i ∈ rA ℂ x I :=
  Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

end LocEqAux2

theorem UpperTheory.Gal.productCup_of_system.locEq_of :
    ValBasic → RYBasic → LocEq := by
  intro hV hY F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY0 I J i hi e
  obtain ⟨hRY0, -, hmono, h4, h5⟩ := hY F K K' d x j2 hY0
  have hRB : rB ℂ K' (xv x) {i} ≤ RY (xv x) j2 I J := by
    have hle := hmono {i} I ∅ J (Finset.singleton_subset_iff.mpr hi) (Finset.empty_subset _)
    rwa [hRY0] at hle
  obtain ⟨hRloc, -, -, hinv⟩ := hV K' (rB ℂ K' (xv x) {i}) (locRes hRB e)
  obtain ⟨j, hj⟩ := hY0.cov i (locRes hRB e)
  have hIB : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J := le_sup_left
  have hR2B : R2 (xv x) j2 J ≤ RY (xv x) j2 I J := le_sup_right
  have unit_lemma : ∀ {y w w' : K'}, w ∈ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) →
      w' ∈ RY (xv x) j2 I J → w * w' = 1 → y * w ∈ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) →
      y ∈ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    intro y w w' hw hw' hww hyw
    obtain ⟨⟨b, hbR⟩, hb0, hbw⟩ := hw
    have hne : locRes hRB e ⟨b * w, hbw⟩ ≠ 0 := by
      intro h0
      have hprod : e ⟨b * w, hRB hbw⟩ * e ⟨w', hw'⟩ = e ⟨b, hRB hbR⟩ := by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        show b * w * w' = b
        rw [mul_assoc, hww, mul_one]
      rw [show e ⟨b * w, hRB hbw⟩ = 0 from h0, zero_mul] at hprod
      exact hb0 hprod.symm
    have hval : Val (rB ℂ K' (xv x) {i}) (locRes hRB e) w
        (locRes hRB e ⟨b * w, hbw⟩ / locRes hRB e ⟨b, hbR⟩) := by
      refine ⟨b, hbR, hbw, hb0, ?_⟩
      field_simp
    obtain ⟨hw0, hwinv⟩ := hinv w _ hval (div_ne_zero hne hb0)
    have hy : y = (y * w) * w⁻¹ := by field_simp
    rw [hy]
    exact Subalgebra.mul_mem _ hyw hwinv
  have hI : rB ℂ K' (xv x) I ≤ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    intro y hy
    obtain ⟨N, hN⟩ := ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K' d (xv x) hY0.covY I i hi).2 y).1 hy
    refine unit_lemma (w := algebraMap F K' (∏ a ∈ I, xv x a / xv x i) ^ N)
      (w' := algebraMap F K' (∏ a ∈ I, xv x i / xv x a) ^ N) ?_ ?_ ?_ (hRloc hN)
    · exact hRloc (Subalgebra.pow_mem _ (mem_rB_of (L := K') (xv x) {i}
        (Subalgebra.prod_mem _ (fun a _ => div_mem_rA (xv x) (Finset.mem_singleton_self i) a))) N)
    · exact hIB (Subalgebra.pow_mem _ (mem_rB_of (L := K') (xv x) I
        (Subalgebra.prod_mem _ (fun a ha => div_mem_rA (xv x) ha i))) N)
    · rw [← mul_pow, ← map_mul, ← Finset.prod_mul_distrib]
      rw [Finset.prod_eq_one (fun a _ => by
        rw [div_mul_div_comm, mul_comm (xv x a), div_self (mul_ne_zero (x i).ne_zero (x a).ne_zero)])]
      rw [map_one, one_pow]
  have hR2 : ∀ S : Finset (Fin (d + 1)), S ⊆ J →
      R2 (xv x) j2 (insert j S) ≤ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.insert_empty]
      exact hj
    | insert m S hmS ih =>
      intro hS y hy
      rw [Finset.insert_comm] at hy
      obtain ⟨N, hN⟩ := h5 (insert j S) j (Finset.mem_insert_self _ _) m y hy
      have hmJ : m ∈ J := hS (Finset.mem_insert_self _ _)
      refine unit_lemma (w := j2 (algebraMap F K (xv x m / xv x j)) ^ N)
        (w' := j2 (algebraMap F K (xv x j / xv x m)) ^ N) ?_ ?_ ?_
        (ih (fun a ha => hS (Finset.mem_insert_of_mem ha)) hN)
      · exact Subalgebra.pow_mem _ (hj (h4 {j} _ (mem_rB_of (L := K) (xv x) {j}
          (div_mem_rA (xv x) (Finset.mem_singleton_self j) m))).2) N
      · exact Subalgebra.pow_mem _ (hR2B (h4 J _ (mem_rB_of (L := K) (xv x) J
          (div_mem_rA (xv x) hmJ j))).2) N
      · rw [← mul_pow, ← map_mul, ← map_mul, div_mul_div_comm, mul_comm (xv x m),
          div_self (mul_ne_zero (x j).ne_zero (x m).ne_zero), map_one, map_one, one_pow]
  have hB : RY (xv x) j2 I J ≤ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    refine le_trans (hmono I I J (insert j J) (subset_refl _) (Finset.subset_insert _ _)) ?_
    exact sup_le hI (hR2 J (subset_refl _))
  obtain ⟨h1, h2⟩ := loc_val_eq hRB e hB
  exact ⟨locRes hRB e, h1, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocMax
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma red_art {R : Type} [CommRing R] [IsArtinianRing R] [IsReduced R] (y : R) :
    ∃ z, y * (1 - y * z) = 0 := by
  obtain ⟨n, w, hw⟩ := IsArtinian.exists_pow_succ_smul_dvd y (1 : R)
  simp only [smul_eq_mul, mul_one] at hw
  refine ⟨w, IsReduced.eq_zero _ ⟨n + 1, ?_⟩⟩
  have h : y ^ n * (1 - y * w) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, hw, sub_self]
  rw [mul_pow, pow_succ, pow_succ]
  calc y ^ n * y * ((1 - y * w) ^ n * (1 - y * w))
      = y * (1 - y * w) ^ n * (y ^ n * (1 - y * w)) := by ac_rfl
    _ = 0 := by rw [h, mul_zero]

private theorem exists_const_sub_mem_span_tco_of_mem_rA {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] (d : ℕ) (x : Fin (d + 1) → Fˣ) (f : F) (hf : f ∈ rA ℂ (xv x) {0}) :
    ∃ c : ℂ, ∃ hb : algebraMap F L f ∈ rB ℂ L (xv x) {0},
      (⟨_, hb⟩ : rB ℂ L (xv x) {0}) - algebraMap ℂ _ c ∈ Ideal.span (Set.range fun j : Fin d =>
        (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})) := by
  have memB : ∀ g ∈ rA ℂ (xv x) {0}, algebraMap F L g ∈ rB ℂ L (xv x) {0} := by
    intro g hg
    rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (x := (⟨g, hg⟩ : rA ℂ (xv x) {0}))
  unfold rA at hf
  induction hf using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, hi, j, rfl⟩ := hy
    rw [Finset.mem_singleton] at hi
    subst hi
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · refine ⟨1, memB _ (Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, 0, rfl⟩), ?_⟩
      convert Ideal.zero_mem _
      rw [sub_eq_zero]
      apply Subtype.ext
      simp
    · refine ⟨0, tco_mem ℂ L (xv x) k, ?_⟩
      rw [map_zero, sub_zero]
      exact Ideal.subset_span ⟨k, rfl⟩
  | algebraMap c0 =>
    refine ⟨c0, memB _ (Subalgebra.algebraMap_mem _ c0), ?_⟩
    convert Ideal.zero_mem _
    rw [sub_eq_zero]
    apply Subtype.ext
    simp [IsScalarTower.algebraMap_apply ℂ F L]
  | add f g _ _ ihf ihg =>
    obtain ⟨c, hb, h⟩ := ihf
    obtain ⟨c', hb', h'⟩ := ihg
    refine ⟨c + c', by rw [map_add]; exact Subalgebra.add_mem _ hb hb', ?_⟩
    convert Ideal.add_mem _ h h' using 1
    apply Subtype.ext
    simp only [map_add, Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_algebraMap]
    ring
  | mul f g _ _ ihf ihg =>
    obtain ⟨c, hb, h⟩ := ihf
    obtain ⟨c', hb', h'⟩ := ihg
    refine ⟨c * c', by rw [map_mul]; exact Subalgebra.mul_mem _ hb hb', ?_⟩
    convert Ideal.add_mem _ (Ideal.mul_mem_right (⟨_, hb'⟩ : rB ℂ L (xv x) {0}) _ h)
      (Ideal.mul_mem_left _ (algebraMap ℂ (rB ℂ L (xv x) {0}) c) h') using 1
    apply Subtype.ext
    simp only [map_mul, Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul,
      Subalgebra.coe_algebraMap]
    ring

private lemma fin_quot {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] (d : ℕ) (x : Fin (d + 1) → Fˣ) (hc : IsFinCover ℂ L (xv x)) :
    Module.Finite ℂ ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := by
  classical
  have hfin := (GlobalTheory.T.finite_cover_chart_smooth_normal ℂ F L d (xv x) hc {0} (Finset.singleton_nonempty 0)).1
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨⟨s.image (fun z => Ideal.Quotient.mk _ (⟨z.1, z.2⟩ : rB ℂ L (xv x) {0})), ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hy : (⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L) ∈
      Submodule.span (rA ℂ (xv x) {0}) (s : Set (integralClosure (rA ℂ (xv x) {0}) L)) := by
    rw [hs]
    trivial
  change Ideal.Quotient.mk _ (⟨(⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L).1,
    (⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L).2⟩ : rB ℂ L (xv x) {0}) ∈ _
  generalize (⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L) = z at hy ⊢
  induction hy using Submodule.span_induction with
  | mem w hw => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hw))
  | zero =>
    convert Submodule.zero_mem _ using 1
    exact map_zero (Ideal.Quotient.mk _)
  | add u w _ _ hu hw =>
    convert Submodule.add_mem _ hu hw using 1
    exact map_add (Ideal.Quotient.mk _) _ _
  | smul r u _ hu =>
    obtain ⟨c, hb, hc'⟩ := exists_const_sub_mem_span_tco_of_mem_rA (L := L) d x r.1 r.2
    have e : (⟨((r • u : integralClosure (rA ℂ (xv x) {0}) L) : L), (r • u).2⟩ : rB ℂ L (xv x) {0}) =
        ⟨_, hb⟩ * ⟨u.1, u.2⟩ := by
      apply Subtype.ext
      simp [Algebra.smul_def]
      exact Or.inl rfl
    rw [e, map_mul, Ideal.Quotient.eq.mpr hc', Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c hu

theorem UpperTheory.Gal.productCup_of_system.locMax_of :
    ValBasic → LocMax := by
  intro _ F L _ _ _ _ _ _ d x hc hred e v hv
  obtain ⟨b, hb, hbv, heb, hev⟩ := hv
  rw [mul_zero] at hev
  haveI : Module.Finite ℂ ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := fin_quot d x hc
  haveI : IsArtinianRing ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := IsArtinianRing.of_finite ℂ _
  haveI : IsReduced ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := hred
  obtain ⟨zq, hz⟩ := red_art (Ideal.Quotient.mk (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0}))) ⟨b * v, hbv⟩)
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective zq
  have hmem : (⟨b * v, hbv⟩ : rB ℂ L (xv x) {0}) * (1 - ⟨b * v, hbv⟩ * z) ∈
      Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, map_one, map_mul]
    exact hz
  obtain ⟨c, hcsum⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  have he1 : e.1 (1 - ⟨b * v, hbv⟩ * z) = 1 := by
    rw [map_sub, map_one, map_mul]
    change 1 - e.1 ⟨b * v, hbv⟩ * e.1 z = 1
    rw [hev, zero_mul, sub_zero]
  have hes : e.1 (⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z)) ≠ 0 := by
    rw [map_mul, he1, mul_one]
    exact heb
  have hs0 : ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) ≠ 0 := by
    intro h
    apply hes
    rw [show (⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) = 0 from Subtype.ext h, map_zero]
  have key : ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) * v =
      ∑ l, (c l : L) * tt L x l := by
    have h1 : (((⟨b * v, hbv⟩ : rB ℂ L (xv x) {0}) * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) =
        ∑ l, (c l : L) * tt L x l := by
      rw [← hcsum]
      simp [tt]
    rw [← h1]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one]
    ring
  refine ⟨fun l => (c l : L) * ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L)⁻¹,
    fun l => ⟨⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z), hes, ?_⟩, ?_⟩
  · rw [mul_comm, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
    exact (c l).2
  · calc v = ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L)⁻¹ *
          (((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) * v) := by
          rw [← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
      _ = _ := by
          rw [key, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocOne
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem locOne_nak {L : Type} [Field L] [Algebra ℂ L] (B O : Subalgebra ℂ L)
    [Algebra.FiniteType ℂ B] (hBO : B ≤ O) (ev : O →ₐ[ℂ] ℂ) (hunit : ∀ u : O, ev u ≠ 0 → IsUnit u)
    (hden : ∀ v : O, ∃ b : B, ev ⟨b, hBO b.2⟩ ≠ 0 ∧ (b : L) * v ∈ B)
    {d : ℕ} (t : Fin d → O) (ht : ∀ l, ev (t l) = 0)
    (hmax : ∀ v : O, ev v = 0 → ∃ a : Fin d → O, v = ∑ l, a l * t l) (v : O) :
    D ℂ L (v : L) ∈ Submodule.span O (Set.range fun l => D ℂ L (t l : L)) := by
  classical
  set I : Ideal O := RingHom.ker ev with hI
  set N : Submodule O (Ω[L⁄ℂ]) := Submodule.span O (Set.range fun l => D ℂ L (t l : L)) with hN
  set M : Submodule O (Ω[L⁄ℂ]) := Submodule.span O (Set.range fun w : O => D ℂ L (w : L)) with hM
  have hvM : D ℂ L (v : L) ∈ M := Submodule.subset_span ⟨v, rfl⟩
  suffices hMN : M ≤ N from hMN hvM
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := I)
  · obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType ℂ B).out
    set G : Submodule O (Ω[L⁄ℂ]) := Submodule.span O ((fun b : B => D ℂ L (b : L)) '' (s : Set B)) with hG
    have hB : ∀ b : B, D ℂ L (b : L) ∈ G := by
      intro b
      have hb : b ∈ Algebra.adjoin ℂ (s : Set B) := hs ▸ Algebra.mem_top
      induction hb using Algebra.adjoin_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | algebraMap r => simp
      | add y z _ _ hy hz =>
        rw [Subalgebra.coe_add, map_add]
        exact Submodule.add_mem _ hy hz
      | mul y z _ _ hy hz =>
        rw [Subalgebra.coe_mul, Derivation.leibniz]
        exact Submodule.add_mem _ (Submodule.smul_mem G (⟨y, hBO y.2⟩ : O) hz)
          (Submodule.smul_mem G (⟨z, hBO z.2⟩ : O) hy)
    have hGM : M = G := by
      apply le_antisymm
      · rw [hM, Submodule.span_le]
        rintro _ ⟨w, rfl⟩
        obtain ⟨b, hb0, hbw⟩ := hden w
        obtain ⟨u, hu⟩ := hunit _ hb0
        have h1 : D ℂ L ((b : L) * (w : L)) ∈ G := hB ⟨_, hbw⟩
        rw [Derivation.leibniz] at h1
        have h2 : (⟨b, hBO b.2⟩ : O) • D ℂ L (w : L) ∈ G := by
          have h4 := Submodule.sub_mem G h1 (Submodule.smul_mem G w (hB b))
          convert h4 using 1
          simp [Subalgebra.smul_def]
        have h3 := Submodule.smul_mem G (↑u⁻¹ : O) h2
        rw [← hu, smul_smul, Units.inv_mul, one_smul] at h3
        exact h3
      · rw [hG, Submodule.span_le]
        rintro _ ⟨b, _, rfl⟩
        exact Submodule.subset_span ⟨⟨b, hBO b.2⟩, rfl⟩
    rw [hGM]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · intro y hy
    rw [Ideal.mem_jacobson_bot]
    intro z
    apply hunit
    have hy0 : ev y = 0 := hy
    simp [hy0]
  · rw [hM, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    obtain ⟨a, ha⟩ := hmax (w - algebraMap ℂ O (ev w)) (by simp)
    have hD : D ℂ L (w : L) = ∑ l, ((a l : O) • D ℂ L (t l : L) + (t l : O) • D ℂ L (a l : L)) := by
      have h1 : (w : L) = algebraMap ℂ L (ev w) + ∑ l, (a l : L) * (t l : L) := by
        have h5 := congrArg (fun u : O => (u : L)) ha
        push_cast at h5
        linear_combination h5
      rw [h1, map_add, Derivation.map_algebraMap, zero_add, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Derivation.leibniz]
      rfl
    show D ℂ L (w : L) ∈ _
    rw [hD]
    refine Submodule.sum_mem _ fun l _ => Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
    · apply Submodule.mem_sup_right
      apply Submodule.smul_mem_smul
      · show ev (t l) = 0
        exact ht l
      · exact Submodule.subset_span ⟨a l, rfl⟩

theorem UpperTheory.Gal.productCup_of_system.locOne_of :
    LocMax → ValBasic → LocOne := by
  intro hMax hVal F L _ _ _ _ _ _ d x hc hred e v hv
  obtain ⟨hle, ⟨ev, hev⟩, hbv, hinv⟩ := hVal L (rB ℂ L (xv x) {0}) e.1
  haveI := hc.smooth 0
  haveI : Algebra.FiniteType ℂ (rB ℂ L (xv x) {0}) := inferInstance
  have hevB : ∀ b : rB ℂ L (xv x) {0}, ev ⟨b, hle b.2⟩ = e.1 b := by
    intro b
    obtain ⟨h, hb⟩ := (hev _ _).1 (hbv b)
    exact hb
  have hunit : ∀ u : loc (rB ℂ L (xv x) {0}) e.1, ev u ≠ 0 → IsUnit u := by
    intro u hu
    obtain ⟨h0, h1⟩ := hinv u (ev u) ((hev _ _).2 ⟨u.2, rfl⟩) hu
    exact IsUnit.of_mul_eq_one (⟨_, h1⟩ : loc (rB ℂ L (xv x) {0}) e.1)
      (Subtype.ext (mul_inv_cancel₀ h0))
  have hden : ∀ v : loc (rB ℂ L (xv x) {0}) e.1, ∃ b : rB ℂ L (xv x) {0},
      ev ⟨b, hle b.2⟩ ≠ 0 ∧ (b : L) * v ∈ rB ℂ L (xv x) {0} := by
    intro v
    obtain ⟨b, hb, hbv'⟩ := v.2
    exact ⟨b, by rw [hevB]; exact hb, hbv'⟩
  let t : Fin d → loc (rB ℂ L (xv x) {0}) e.1 := fun l => ⟨tt L x l, hle (tco_mem ℂ L (xv x) l)⟩
  have ht : ∀ l, ev (t l) = 0 := fun l =>
    (hevB ⟨_, tco_mem ℂ L (xv x) l⟩).trans (e.2 l)
  have hmax : ∀ v : loc (rB ℂ L (xv x) {0}) e.1, ev v = 0 → ∃ a : Fin d → loc (rB ℂ L (xv x) {0}) e.1,
      v = ∑ l, a l * t l := by
    intro v h0
    obtain ⟨a, ha, hv'⟩ := hMax F L d x hc hred e v ((hev _ _).2 ⟨v.2, h0⟩)
    refine ⟨fun l => ⟨a l, ha l⟩, Subtype.ext ?_⟩
    rw [hv', AddSubmonoidClass.coe_finset_sum]
    rfl
  have hmem := locOne_nak _ _ hle ev hunit hden t ht hmax ⟨v, hv⟩
  obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
  exact ⟨fun l => c l, fun l => (c l).2, hc'.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PTrTop
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem kahlerMap_volumeForm {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K']
    [Algebra F K] [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K']
    [IsScalarTower ℂ F K'] {d : ℕ} (x : Fin (d + 1) → F) :
    mapDR ℂ K K' (vol0 ℂ K x) = vol0 ℂ K' x := by
  simp only [vol0, ExteriorAlgebra.ιMulti_apply]
  rw [map_list_prod]
  congr 1
  simp only [List.map_ofFn]
  congr 1
  funext j
  have h1 : ∀ w : Ω[K⁄ℂ], mapDR ℂ K K' (ExteriorAlgebra.ι K w) = map1 ℂ K K' w := fun w => by
    simp [mapDR]
  have h2 : ∀ a : K, map1 ℂ K K' (D ℂ K a) = ExteriorAlgebra.ι K' (D ℂ K' (algebraMap K K' a)) := fun a => by
    simp [map1, ι1, KaehlerDifferential.map_D]
  simp only [Function.comp, h1, map_smul, h2, map_inv₀]
  rw [← algebraMap_smul K' ((algebraMap F K (x j.succ / x 0))⁻¹), map_inv₀, ← IsScalarTower.algebraMap_apply]

theorem UpperTheory.Gal.productCup_of_system.trTop_of :
    TrTop := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY τ hτ ρ hρ
  haveI : FiniteDimensional F K := hY.covZ.fin
  haveI : FiniteDimensional F K' := hY.covY.fin
  haveI : FiniteDimensional K K' := FiniteDimensional.right F K K'
  have hTr := (GlobalTheory.T.deRhamFormTrace_exists_unique ℂ K K').1
  have second : ∀ h : K', trF ℂ τ ρ (trDR ℂ K K' (h • vol0 ℂ K' (xv x))) = ρ (Algebra.trace F K' h) := by
    intro h
    rw [← kahlerMap_volumeForm (K := K) (K' := K') (xv x), hTr h (vol0 ℂ K (xv x))]
    simp only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_smul, hτ.1, smul_eq_mul, mul_one]
    rw [Algebra.trace_trace]
  refine ⟨fun w y => ((GlobalTheory.T.deRhamFormTrace_projection_formula ℂ K K') w y).1, second, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  obtain ⟨⟨τ', hτ'⟩, hvol⟩ := GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F K' d (xv x) hY.covY
  have key : ∀ i : Fin (d + 1), trF ℂ τ ρ (trDR ℂ K K' (y' (Finset.univ.erase i))) = 0 := by
    intro i
    have hm : y' (Finset.univ.erase i) ∈ (if (Finset.univ.erase i : Finset (Fin (d + 1))).Nonempty ∧
        (((Finset.univ.erase i : Finset (Fin (d + 1))).card : ℕ) : ℤ) = ((d : ℤ) - 1) + 1 then
        omB ℂ K' (rB ℂ K' (xv x) (Finset.univ.erase i)) d else ⊥ : Submodule ℂ (DR ℂ K')) :=
      hy' (Finset.univ.erase i) (Set.mem_univ _)
    by_cases hne : (Finset.univ.erase i : Finset (Fin (d + 1))).Nonempty
    · have hc : (((Finset.univ.erase i : Finset (Fin (d + 1))).card : ℕ) : ℤ) = ((d : ℤ) - 1) + 1 := by
        simp
      rw [if_pos ⟨hne, hc⟩] at hm
      have hle : omB ℂ K' (rB ℂ K' (xv x) (Finset.univ.erase i)) d ≤ (⋀[K']^d Ω[K'⁄ℂ]).restrictScalars ℂ := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, -, v, -, rfl⟩
        refine (⋀[K']^d Ω[K'⁄ℂ]).smul_mem b ?_
        rw [← ExteriorAlgebra.ιMulti_span_fixedDegree]
        exact Submodule.subset_span ⟨_, rfl⟩
      rw [hvol τ' hτ' _ (hle hm), second]
      have h1 := (GlobalTheory.T.complementaryModule_standardOpens_iff ℂ F K' d (xv x) hY.covY τ' hτ' _ hne (τ' (y' (Finset.univ.erase i)))).2 ⟨_, hm, rfl⟩ 1
        (one_mem _)
      rw [mul_one] at h1
      exact GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) hY.covY.pd ρ hρ i _ hne (by simp) _ h1
    · rw [if_neg (fun h => hne h.1)] at hm
      rw [(Submodule.mem_bot ℂ).1 hm]
      simp
  change trF ℂ τ ρ (trDR ℂ K K' (∑ i ∈ Finset.univ, _ • y' (Finset.univ.erase i))) = 0
  simp only [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_zsmul, map_zsmul, key i, smul_zero]
end

