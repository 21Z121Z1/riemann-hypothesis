import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0030

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGenericRestrLen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Localisation

variable {S : Type u} [CommRing S] {F : Type u} [Field F] [Algebra S F] [IsFractionRing S F]
  {Ω : Type w} [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]

theorem exists_smul_mem_of_mem_span (P : Submodule S Ω) {z : Ω}
    (hz : z ∈ Submodule.span F (P : Set Ω)) : ∃ t ∈ nonZeroDivisors S, t • z ∈ P := by
  refine Submodule.span_induction (p := fun z _ => ∃ t ∈ nonZeroDivisors S, t • z ∈ P)
    (fun z hz => ⟨1, one_mem _, by rwa [one_smul]⟩)
    ⟨1, one_mem _, by rw [smul_zero]; exact P.zero_mem⟩ ?_ ?_ hz
  · rintro a b _ _ ⟨t, ht, ha⟩ ⟨t', ht', hb⟩
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    rw [smul_add]
    refine P.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact P.smul_mem t' ha
    · rw [mul_smul]; exact P.smul_mem t hb
  · rintro c z _ ⟨t, ht, hz⟩
    obtain ⟨⟨a, s⟩, hc⟩ := IsLocalization.surj (nonZeroDivisors S) c
    refine ⟨s * t, mul_mem s.2 ht, ?_⟩
    have key : ((s : S) * t) • (c • z) = a • (t • z) := by
      simp only [Algebra.smul_def, IsScalarTower.algebraMap_apply S F Ω, map_mul] at hc ⊢
      rw [← hc, map_mul]
      ring
    rw [key]
    exact P.smul_mem a hz

variable (F) in

def spanQuotMap (A B : Submodule S Ω) :
    (A ⧸ B.comap A.subtype) →ₗ[S]
      (Submodule.span F (A : Set Ω) ⧸
        (Submodule.span F (B : Set Ω)).comap (Submodule.span F (A : Set Ω)).subtype) :=
  (B.comap A.subtype).liftQ
    ((((Submodule.span F (B : Set Ω)).comap (Submodule.span F (A : Set Ω)).subtype).mkQ.restrictScalars S) ∘ₗ
      { toFun := fun a => ⟨a, Submodule.subset_span a.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })
    (fun _a ha => LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ha)))

theorem isLocalizedModule_spanQuotMap (A B : Submodule S Ω) :
    IsLocalizedModule (nonZeroDivisors S) (spanQuotMap F A B) where
  map_units s := by
    rw [← (Algebra.lsmul S (A := F) S _).commutes]; exact (IsLocalization.map_units F s).map _
  surj y := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨t, ht, hz⟩ := exists_smul_mem_of_mem_span A z.2
    exact ⟨(Submodule.Quotient.mk ⟨t • (z : Ω), hz⟩, ⟨t, ht⟩), rfl⟩
  exists_of_eq {a₁ a₂} h := by
    obtain ⟨a₁, rfl⟩ := Submodule.Quotient.mk_surjective _ a₁
    obtain ⟨a₂, rfl⟩ := Submodule.Quotient.mk_surjective _ a₂
    have hB : (a₁ : Ω) - a₂ ∈ Submodule.span F (B : Set Ω) := (Submodule.Quotient.eq
      ((Submodule.span F (B : Set Ω)).comap (Submodule.span F (A : Set Ω)).subtype)).mp h
    obtain ⟨t, ht, htB⟩ := exists_smul_mem_of_mem_span B hB
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq]
    change t • (a₁ : Ω) - t • (a₂ : Ω) ∈ B
    rwa [← smul_sub]

theorem length_spanQuot_toNat (A B : Submodule S Ω) :
    (Module.length F (Submodule.span F (A : Set Ω) ⧸
        (Submodule.span F (B : Set Ω)).comap (Submodule.span F (A : Set Ω)).subtype)).toNat =
      Module.finrank S (A ⧸ B.comap A.subtype) := by
  have := isLocalizedModule_spanQuotMap (F := F) A B
  rw [Module.length_eq_rank, Cardinal.toNat_toENat]
  change Module.finrank F _ = _
  rw [IsLocalization.finrank_eq F (nonZeroDivisors S) le_rfl]
  exact IsLocalizedModule.finrank_eq (p := nonZeroDivisors S) (f := spanQuotMap F A B) (hp := le_rfl)

end Localisation

section Ideal

variable {S : Type u} [CommRing S] {F : Type u} [Field F] [Algebra S F] {N : ℕ}

theorem mem_span_of_mem_map (qq : Ideal (Poly S N)) {f : Poly F N}
    (hf : f ∈ qq.map (MvPolynomial.map (algebraMap S F))) :
    f ∈ Submodule.span F (MvPolynomial.map (algebraMap S F) '' (qq : Set (Poly S N))) := by
  set T := Submodule.span F (MvPolynomial.map (algebraMap S F) '' (qq : Set (Poly S N)))
  have hX : ∀ (i : Fin (N + 1)) (g : Poly F N), g ∈ T → X i * g ∈ T := fun i g hg => by
    refine Submodule.span_induction (p := fun g _ => X i * g ∈ T) ?_
      (by rw [mul_zero]; exact T.zero_mem)
      (fun a b _ _ ha hb => by rw [mul_add]; exact T.add_mem ha hb)
      (fun c g _ hg => by rw [mul_smul_comm]; exact T.smul_mem c hg) hg
    rintro _ ⟨p, hp, rfl⟩
    exact Submodule.subset_span ⟨X i * p, qq.mul_mem_left _ hp, by rw [map_mul, map_X]⟩
  have hmul : ∀ (c g : Poly F N), g ∈ T → c * g ∈ T := fun c => by
    induction c using MvPolynomial.induction_on with
    | C a => intro g hg; rw [← smul_eq_C_mul]; exact T.smul_mem a hg
    | add p q hp hq => intro g hg; rw [add_mul]; exact T.add_mem (hp g hg) (hq g hg)
    | mul_X p i hp => intro g hg; rw [mul_assoc]; exact hp _ (hX i g hg)
  refine Submodule.span_induction (p := fun g _ => g ∈ T) (fun g hg => Submodule.subset_span hg)
    T.zero_mem (fun a b _ _ ha hb => T.add_mem ha hb) (fun c g _ hg => hmul c g hg) hf

variable [IsFractionRing S F] {Ω : Type w} [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]

theorem idealSys_map_eq_extend (x : Fin (N + 1) → Ω) (qq : Ideal (Poly S N))
    (hq : ∀ p ∈ qq, ∀ d : ℕ, homogeneousComponent d p ∈ qq) :
    idealSys x (qq.map (MvPolynomial.map (algebraMap S F))) = (idealSys x qq).extend F := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · change idealMod _ I ≤ Submodule.span (chartRing F x I) (idealMod qq I : Set Ω)
    unfold idealMod
    rw [span_extend_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    obtain ⟨s', hs', rfl⟩ := exists_monos_map (S := S) hs
    have hinj : Function.Injective (algebraMap S F) := IsFractionRing.injective S F
    have hse' : s'.IsHomogeneous e := fun d hd => hse (by
      rw [coeff_map]; exact fun h => hd (hinj (h.trans (map_zero _).symm)))
    rw [SetLike.mem_coe, ← homogeneousComponent_eq_self hfe, aeval_map_algebraMap]
    refine Submodule.span_induction (p := fun g _ => aeval x (homogeneousComponent e g) / aeval x s' ∈
      Submodule.span (chartRing F x I) {a | ∃ (f s : Poly S N) (e : ℕ), f ∈ qq ∧ s ∈ monos I.1 ∧
        f.IsHomogeneous e ∧ s.IsHomogeneous e ∧ a = aeval x f / aeval x s}) ?_ ?_ ?_ ?_
      (mem_span_of_mem_map qq hf)
    · rintro _ ⟨p, hp, rfl⟩
      rw [homogeneousComponent_map_eq, aeval_map_algebraMap]
      exact Submodule.subset_span ⟨_, s', e, hq p hp e, hs', homogeneousComponent_isHomogeneous e p, hse', rfl⟩
    · rw [map_zero, map_zero, zero_div]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [map_add, map_add, add_div]; exact Submodule.add_mem _ ha hb
    · intro c g _ hg
      rw [map_smul, map_smul, smul_div_assoc]
      exact Submodule.smul_of_tower_mem _ c hg
  · change Submodule.span (chartRing F x I) (idealMod qq I : Set Ω) ≤ idealMod _ I
    unfold idealMod
    rw [span_extend_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    exact ⟨map (algebraMap S F) f, map (algebraMap S F) s, e, Ideal.mem_map_of_mem _ hf, map_mem_monos hs,
      hfe.map _, hse.map _, by rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩

end Ideal

theorem GenericRestrLen.proof : GenericRestrLen.Statement.{u, w} := by
  intro S _ _ F _ _ _ Ω _ _ _ _ N x Q qq hq
  unfold restrLen
  rw [idealSys_map_eq_extend x qq hq, ← SubSystem.extend_twist, ← span_secs_eq_secs_extend,
    ← span_secs_eq_secs_extend, length_spanQuot_toNat]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeDecomp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

namespace KHFreeDecomp

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cellMon_monomial {I : ∀ k, Finset (ι k)} {t : MRingOver S ι} (ht : t ∈ KH.cellMon S I) :
    ∃ u : (Σ k, ι k) →₀ ℕ, t = monomial u 1 ∧ ∀ q ∈ u.support, q.2 ∈ I q.1 := by
  classical
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    refine ⟨Finsupp.single ⟨k, i⟩ 1, rfl, fun q hq => ?_⟩
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hq)]
    exact hi
  | one => exact ⟨0, by rw [← C_1, C_apply], by simp⟩
  | mul f g _ _ hf hg =>
    obtain ⟨u, rfl, hu⟩ := hf
    obtain ⟨v, rfl, hv⟩ := hg
    refine ⟨u + v, by rw [monomial_mul, one_mul], fun q hq => ?_⟩
    rcases Finset.mem_union.mp (Finsupp.support_add hq) with h | h
    · exact hu q h
    · exact hv q h

section Frac

variable {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

def overDen (T : Submonoid (MRingOver S ι)) (t : T) : M →ₗ[S] LocalizedModule T M where
  toFun m := LocalizedModule.mk m t
  map_add' x y := by
    simp only [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_add]
  map_smul' s m := by
    rw [RingHom.id_apply, LocalizedModule.smul'_mk]

theorem overDen_apply (T : Submonoid (MRingOver S ι)) (t : T) (m : M) :
    overDen T t m = LocalizedModule.mk m t := rfl

end Frac

theorem quot_mk_smul (s : S) (p : MRingOver S ι) :
    Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (s • p) = s • Ideal.Quotient.mk ⊥ p := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]

theorem mk_monomial_eq (I : ∀ k, Finset (ι k)) (u v : (Σ k, ι k) →₀ ℕ) (hu : ∀ q ∈ u.support, q.2 ∈ I q.1)
    (ht : (monomial u (1 : S) : MRingOver S ι) ∈ KH.cellMon S I) :
    LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (monomial v 1)) ⟨monomial u 1, ht⟩ =
      monoFrac S I (fun q => (v q : ℤ) - u q) := by
  classical
  have hneg : ∀ k, negSet (fun q => (v q : ℤ) - u q) k ⊆ I k := by
    intro k i hi
    simp only [negSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hu ⟨k, i⟩ (Finsupp.mem_support_iff.mpr (by omega))
  have hexp : negExp (fun q => (v q : ℤ) - u q) + v = u + posExp (fun q => (v q : ℤ) - u q) := by
    ext q
    simp only [Finsupp.add_apply, posExp, negExp, Finsupp.coe_equivFunOnFinite_symm]
    omega
  rw [monoFrac, dif_pos hneg, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    monomial_mul, mul_one]
  rw [hexp]

theorem locPart_le (I : ∀ k, Finset (ι k)) (c d : K → ℤ) :
    KH.locPart ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) (KH.cellMon S I) c ≤
      Submodule.span S (monoFrac S I '' {a | blockSum a = c + d}) := by
  classical
  rcases subsingleton_or_nontrivial S with hS | hS
  · intro x _
    have hx : x = 0 := by rw [← one_smul S x, Subsingleton.elim (1 : S) 0, zero_smul]
    rw [hx]
    exact zero_mem _
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, ⟨t, ht⟩, b, htb, hm, rfl⟩
  obtain ⟨u, rfl, huI⟩ := cellMon_monomial ht
  have hub : ∀ k, ∑ i, u ⟨k, i⟩ = b k := by
    intro k
    refine htb u ?_ k
    rw [support_monomial, if_neg one_ne_zero]
    exact Finset.mem_singleton_self u
  have hle : KH.quotPart S (⊥ : Ideal (MRingOver S ι)) ((c + fun k => (b k : ℤ)) + d) ≤
      (Submodule.span S (monoFrac S I '' {a | blockSum a = c + d})).comap
        (overDen (KH.cellMon S I) ⟨monomial u 1, ht⟩) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, ⟨hpos, hp⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have hsum : p = ∑ v ∈ p.support, coeff v p • (monomial v 1 : MRingOver S ι) := by
      conv_lhs => rw [p.as_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hsum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    rw [quot_mk_smul, map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun q => (v q : ℤ) - u q, ?_, ?_⟩)
    · have hv' := hp v hv
      show blockSum _ = c + d
      funext k
      simp only [blockSum, Finset.sum_sub_distrib]
      have h1 : ∑ i, ((v ⟨k, i⟩ : ℕ) : ℤ) = ((((c + fun k => (b k : ℤ)) + d) k).toNat : ℤ) := by
        exact_mod_cast hv' k
      have h2 : ∑ i, ((u ⟨k, i⟩ : ℕ) : ℤ) = b k := by exact_mod_cast hub k
      have h3 := hpos k
      simp only [Pi.add_apply] at h1 h3 ⊢
      omega
    · rw [overDen_apply, mk_monomial_eq I u v huI ht]
  exact hle hm

theorem embed_apply_cell [LinearOrder K] [∀ k, LinearOrder (ι k)] (a : (Σ k, ι k) → ℤ) (n : ℕ)
    (F : KH.Cell K ι n → S) (I : KH.Cell K ι n) :
    embed S a n (fun J => F J.1) I = F I • monoFrac S I.1 a := by
  classical
  unfold embed
  rw [LinearMap.pi_apply]
  split_ifs with h
  · rfl
  · rw [LinearMap.zero_apply, monoFrac, dif_neg h, smul_zero]

end KHFreeDecomp

open KHFreeDecomp in

theorem KHFreeDecomp.full : KHFreeDecomp.Statement := by
  intro S _ K _ _ ι _ _ c d n φ hφ
  classical
  have hI : ∀ I : KH.Cell K ι n, ∃ l : ((Σ k, ι k) → ℤ) →₀ S,
      l ∈ Finsupp.supported S S {a | blockSum a = c + d} ∧
        Finsupp.linearCombination S (monoFrac S I.1) l = φ I := by
    intro I
    have hx : φ I ∈ KH.locPart ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d))
        (KH.cellMon S I.1) c := hφ I (Set.mem_univ _)
    exact (Finsupp.mem_span_image_iff_linearCombination S).mp (locPart_le I.1 c d hx)
  choose l hl hlφ using hI
  let _ : Fintype (KH.Cell K ι n) := by unfold KH.Cell; infer_instance
  refine ⟨Finset.univ.biUnion fun I => (l I).support, fun a J => l J.1 a, ?_, ?_⟩
  · intro a ha
    obtain ⟨I, -, haI⟩ := Finset.mem_biUnion.mp ha
    exact hl I haI
  · funext I
    rw [Finset.sum_apply, ← hlφ I, Finsupp.linearCombination_apply, Finsupp.sum]
    beta_reduce
    refine (Finset.sum_subset (s₁ := (l I).support) (s₂ := Finset.univ.biUnion fun I => (l I).support)
      (f := fun a => l I a • monoFrac S I.1 a) (fun a ha => Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ _, ha⟩) ?_).trans
      (Finset.sum_congr rfl fun a _ => (embed_apply_cell a n (fun J => l J a) I).symm)
    intro a _ ha
    rw [Finsupp.mem_support_iff, not_not] at ha
    rw [ha, zero_smul]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeIndep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

namespace KHFreeIndep

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem cellMon_monomial {I : ∀ k, Finset (ι k)} {t : MRingOver S ι} (ht : t ∈ KH.cellMon S I) :
    ∃ e, t = monomial e 1 := by
  unfold KH.cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, -, rfl⟩ := hx
    exact ⟨Finsupp.single ⟨k, i⟩ 1, rfl⟩
  | one => exact ⟨0, by rw [monomial_zero', C_1]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨e', rfl⟩ := hy
    exact ⟨e + e', by rw [monomial_mul, mul_one]⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem eq_zero_of_monomial_mul (e : (Σ k, ι k) →₀ ℕ) {p : MRingOver S ι}
    (h : monomial e (1 : S) * p = 0) : p = 0 := by
  ext d
  have := congrArg (coeff (e + d)) h
  rw [coeff_monomial_mul, one_mul, coeff_zero] at this
  rw [this, coeff_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem eq_zero_of_mk_eq_zero {I : ∀ k, Finset (ι k)} {p : MRingOver S ι}
    (h : LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) p) (1 : KH.cellMon S I) = 0) :
    p = 0 := by
  rw [← LocalizedModule.zero_mk (1 : KH.cellMon S I), LocalizedModule.mk_eq] at h
  obtain ⟨t, ht⟩ := h
  rw [one_smul, one_smul, smul_zero, Submonoid.smul_def, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at ht
  obtain ⟨e, he⟩ := cellMon_monomial t.2
  rw [he] at ht
  exact eq_zero_of_monomial_mul e ht

theorem shift_injective (u : (Σ k, ι k) →₀ ℕ) {b b' : (Σ k, ι k) → ℤ} (hb : negExp b ≤ u)
    (hb' : negExp b' ≤ u) (h : posExp b + u - negExp b = posExp b' + u - negExp b') : b = b' := by
  funext p
  have h1 := DFunLike.congr_fun h p
  have h2 := Finsupp.le_def.1 hb p
  have h3 := Finsupp.le_def.1 hb' p
  simp only [posExp, negExp, Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
    Finsupp.coe_equivFunOnFinite_symm] at h1 h2 h3
  omega

theorem smul_smul_monoFrac (I : ∀ k, Finset (ι k)) (u : (Σ k, ι k) →₀ ℕ) (r : S) (b : (Σ k, ι k) → ℤ)
    (hI : ∀ k, negSet b k ⊆ I k) (hb : negExp b ≤ u) :
    (monomial u (1 : S) : MRingOver S ι) • (r • monoFrac S I b) =
      LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι))
        (monomial (posExp b + u - negExp b) r)) (1 : KH.cellMon S I) := by
  rw [monoFrac, dif_pos hI, LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  rw [one_smul, one_smul, one_smul, Submonoid.smul_def]
  rw [← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
  congr 1
  simp only [smul_eq_mul, smul_monomial, monomial_mul, mul_one, one_mul]
  congr 1
  rw [add_tsub_cancel_of_le (le_add_left hb), add_comm]

theorem eq_zero_of_sum_smul_monoFrac (I : ∀ k, Finset (ι k)) (A : Finset ((Σ k, ι k) → ℤ))
    (g : ((Σ k, ι k) → ℤ) → S) (hg : ∀ b ∈ A, ¬ (∀ k, negSet b k ⊆ I k) → g b = 0)
    (h : ∑ b ∈ A, g b • monoFrac S I b = 0) : ∀ a ∈ A, g a = 0 := by
  classical
  set u : (Σ k, ι k) →₀ ℕ := ∑ b ∈ A.filter (fun b => ∀ k, negSet b k ⊆ I k), negExp b with hu
  set c : ((Σ k, ι k) → ℤ) → ((Σ k, ι k) →₀ ℕ) := fun b => posExp b + u - negExp b with hc
  have hle : ∀ b ∈ A, (∀ k, negSet b k ⊆ I k) → negExp b ≤ u := fun b hb hI =>
    Finset.single_le_sum (f := negExp) (fun _ _ => zero_le) (Finset.mem_filter.2 ⟨hb, hI⟩)
  have hterm : ∀ b ∈ A, (monomial u (1 : S) : MRingOver S ι) • (g b • monoFrac S I b) =
      LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (monomial (c b) (g b)))
        (1 : KH.cellMon S I) := by
    intro b hb
    by_cases hI : ∀ k, negSet b k ⊆ I k
    · exact smul_smul_monoFrac I u (g b) b hI (hle b hb hI)
    · rw [hg b hb hI, zero_smul, smul_zero, monomial_zero, map_zero, LocalizedModule.zero_mk]
  have key : ∑ b ∈ A, monomial (c b) (g b) = 0 := by
    apply eq_zero_of_mk_eq_zero (I := I)
    have e1 : LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι))
        (∑ b ∈ A, monomial (c b) (g b))) (1 : KH.cellMon S I) =
        ∑ b ∈ A, LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι))
          (monomial (c b) (g b))) (1 : KH.cellMon S I) := by
      rw [map_sum]
      exact map_sum (LocalizedModule.mkLinearMap (KH.cellMon S I) _) _ _
    rw [e1, ← Finset.sum_congr rfl hterm, ← Finset.smul_sum, h, smul_zero]
  intro a ha
  by_cases hI : ∀ k, negSet a k ⊆ I k
  · have hk := congrArg (coeff (c a)) key
    rw [coeff_sum, Finset.sum_eq_single a, coeff_monomial, if_pos rfl, coeff_zero] at hk
    · exact hk
    · intro b hb hba
      by_cases hbI : ∀ k, negSet b k ⊆ I k
      · rw [coeff_monomial, if_neg]
        exact fun hcb => hba (shift_injective u (hle b hb hbI) (hle a ha hI) hcb)
      · rw [hg b hb hbI, monomial_zero, coeff_zero]
    · exact fun hna => absurd ha hna
  · exact hg a ha hI

end KHFreeIndep

theorem KHFreeIndep.full : KHFreeIndep.Statement := by
  intro S _ K _ _ ι _ _ n A f h a ha
  classical
  funext J
  let g : ((Σ k, ι k) → ℤ) → S := fun b =>
    if hb : ∀ k, negSet b k ⊆ J.1.1 k then f b ⟨J.1, hb⟩ else 0
  have hsum : ∑ b ∈ A, g b • monoFrac S J.1.1 b = 0 := by
    have h0 := congrFun h J.1
    rw [Finset.sum_apply, Pi.zero_apply] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [embed, LinearMap.pi_apply, g]
    split_ifs with hb1
    · rfl
    · simp [monoFrac, hb1]
  have hJ := KHFreeIndep.eq_zero_of_sum_smul_monoFrac J.1.1 A g (fun b _ hb => dif_neg hb) hsum a ha
  rw [show g a = f a J from dif_pos J.2] at hJ
  simpa using hJ

end

end GroundTheory.Heights₂.Heights.Kleiman
end

