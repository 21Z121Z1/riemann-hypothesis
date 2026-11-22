import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFiltStep
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictTwist
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefProductNonneg

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplitFiltStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace CycleSplit.Filt.Step

theorem length_ne_top_of_smul_eq_zero {S : Type u} [CommRing S] {T : Type w} [AddCommGroup T] [Module S T]
    [Module.Finite S T] (𝔪 : Ideal S) [𝔪.IsMaximal] (h : ∀ a ∈ 𝔪, ∀ t : T, a • t = 0) :
    Module.length S T ≠ ⊤ := by
  let := Ideal.Quotient.field 𝔪
  have hT : Module.IsTorsionBySet S T 𝔪 := by
    intro t a
    exact h a a.2 t
  let : Module (S ⧸ 𝔪) T := hT.module
  have : IsScalarTower S (S ⧸ 𝔪) T := hT.isScalarTower
  have : Module.Finite (S ⧸ 𝔪) T := Module.Finite.of_restrictScalars_finite S (S ⧸ 𝔪) T
  rw [Module.length_eq_of_surjective (R := S ⧸ 𝔪) (M := T) Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

theorem proof (hSC : SurjectiveClosed.Statement.{u, w}) (hFS : FiniteSections.Statement.{u, w}) :
    CycleSplit.Filt.Step.Statement.{u, w} := by
  classical
  intro S _ _ Ω _ _ N x 𝔪 h𝔪 K pp g e hKh hK h𝔪K hg hpph hpp Q
  obtain ⟨c₀, hc₀⟩ := hSC S Ω N x Q pp hpph
  filter_upwards [eventually_ge_atTop (c₀ + e).toNat] with c hc
  have hce : c₀ ≤ (c : ℤ) - e := by
    have := Int.toNat_le.mp hc
    omega
  set F : SubSystem S x Ω := Q.twist (twistSys S x (c : ℤ)) with hF
  set F' : SubSystem S x Ω := Q.twist (twistSys S x ((c : ℤ) - e)) with hF'
  have hF'eq : F' = F.twist (twistSys S x (-(e : ℤ))) := by
    rw [hF', hF, SubSystem.twist_assoc, twistSys_twist_eq_add, sub_eq_add_neg]
  have hsub : ∀ (J : Ideal (Poly S N)) (I : Chart x),
      (F.twist (idealSys x J)).sub I = idealMod J I * F.sub I :=
    fun J I ↦ SubSystem.twist_sub_eq_mul_of_line _ _ I
  have hF's : ∀ I, F'.sub I = twistMod S x (-(e : ℤ)) I * F.sub I := fun I ↦ by
    rw [hF'eq]; exact SubSystem.twist_sub_eq_mul_of_line _ _ I
  have hF'p : ∀ I, (F'.twist (idealSys x pp)).sub I =
      idealMod pp I * (twistMod S x (-(e : ℤ)) I * F.sub I) := fun I ↦ by
    rw [SubSystem.twist_sub_eq_mul_of_line, hF's]; rfl
  have hinv : ∀ I, ∃ Q' : Submodule (chartRing S x I) Ω, F.sub I * Q' = 1 :=
    fun I ↦ (Q.tensorProd (twistBundle S x (c : ℤ))).invertible I

  have hgK' : ∀ I : Chart x, ∀ y ∈ F'.sub I,
      aeval x g * y ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).sub I := by
    intro I y hy
    obtain ⟨i, hi⟩ := I.2.1
    rw [hF's, twistMod_eq_span _ I hi] at hy
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_span_singleton_mul.mp hy
    rw [hsub]
    have hγ : aeval x g / x i ^ e ∈ idealMod (K ⊔ Ideal.span {g}) I :=
      Submodule.subset_span ⟨g, X i ^ e, e, Ideal.mem_sup_right (Ideal.mem_span_singleton_self g),
        pow_mem (X_mem_monos hi) e, hg, isHomogeneous_X_pow i e, by simp⟩
    have h1 : aeval x g * (x i ^ (-(e : ℤ)) * q) = aeval x g / x i ^ e * q := by
      rw [← mul_assoc, zpow_neg, zpow_natCast, div_eq_mul_inv]
    rw [h1]
    exact Submodule.mul_mem_mul hγ hq
  have hU : ∀ I (y : Ω), y ∈ F'.sub I → aeval x g * y ∈ (F.twist (idealSys x K)).sub I →
      y ∈ (F'.twist (idealSys x pp)).sub I := by
    intro I y hy hgy
    obtain ⟨i, hi⟩ := I.2.1
    obtain ⟨Q', hQ'⟩ := hinv I
    rw [hF's] at hy
    rw [hsub] at hgy
    rw [hF'p]
    exact SectionCount.Drop.Filt.Step.mem_chart_of_mul_mem hK hpp hg I hi _ Q' hQ' hy hgy
  have hC : ∀ I (y : Ω), y ∈ (F'.twist (idealSys x pp)).sub I →
      aeval x g * y ∈ (F.twist (idealSys x K)).sub I := by
    intro I y hy
    obtain ⟨i, hi⟩ := I.2.1
    rw [hF'p] at hy
    rw [hsub]
    exact SectionCount.Drop.Filt.Step.mul_mem_chart hpp hg I hi _ hy
  have hE : ∀ s ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs, ∀ I,
      ∃ y ∈ F'.sub I, s - aeval x g * y ∈ (F.twist (idealSys x K)).sub I := by
    intro s hs I
    obtain ⟨i, hi⟩ := I.2.1
    have hsI := SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hs I
    rw [hsub] at hsI
    rw [hF's, hsub]
    exact SectionCount.Drop.Filt.Step.exists_chart hKh hg I hi _ hsI

  have hWV : ∀ z, z ∈ (F.twist (idealSys x K)).secs →
      z ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs := by
    intro z hz
    refine SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ ?_
    have h1 := SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hz I
    rw [hsub] at h1 ⊢
    have hle : idealMod K I ≤ idealMod (K ⊔ Ideal.span {g}) I := by
      refine Submodule.span_mono ?_
      rintro _ ⟨f, s, d, hf, hs, hfd, hsd, rfl⟩
      exact ⟨f, s, d, Ideal.mem_sup_left hf, hs, hfd, hsd, rfl⟩
    exact (Submodule.mul_le.mpr fun m hm n hn ↦ Submodule.mul_mem_mul (hle hm) hn) h1
  have hVH : ∀ z, z ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs → z ∈ F.secs := fun z hz ↦
    SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ SurjectiveClosed.twist_idealSys_le F _ I (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hz I)
  have hgsec : ∀ y ∈ F'.secs, aeval x g * y ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs :=
    fun y hy ↦ SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ hgK' I y (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp hy I)

  have hlift : ∀ s ∈ (F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs,
      ∃ t ∈ F'.secs, s - aeval x g * t ∈ (F.twist (idealSys x K)).secs := by
    intro s hs
    choose y hy hys using hE s hs
    have hcomp : ∀ (I₁ I₂ : Chart x), I₁.1 ⊆ I₂.1 →
        y I₁ - y I₂ ∈ (F'.twist (idealSys x pp)).sub I₂ := by
      intro I₁ I₂ h
      refine hU I₂ _ (sub_mem (F'.mono I₁ I₂ h _ (hy I₁)) (hy I₂)) ?_
      have h1 := sub_mem (hys I₂) ((F.twist (idealSys x K)).mono I₁ I₂ h _ (hys I₁))
      convert h1 using 1
      ring
    obtain ⟨t, ht, htI⟩ := hc₀ _ hce y hy hcomp
    refine ⟨t, ht, SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ ?_⟩
    have h1 := add_mem (hys I) (hC I _ (neg_mem (htI I)))
    convert h1 using 1
    ring

  set H := F.secs with hH
  set H' := F'.secs with hH'
  set A := ((F.twist (idealSys x K)).secs).comap H.subtype with hA
  set B := ((F.twist (idealSys x (K ⊔ Ideal.span {g}))).secs).comap H.subtype with hB
  set P := ((F'.twist (idealSys x pp)).secs).comap H'.subtype with hP
  have hAB : A ≤ B := fun z hz ↦ Submodule.mem_comap.mpr (hWV _ (Submodule.mem_comap.mp hz))
  let μ0 : H' →ₗ[S] H := (LinearMap.mulLeft S (aeval x g)).restrict (p := H') (q := H)
    (fun y hy ↦ hVH _ (hgsec y hy))
  let μ : H' →ₗ[S] H ⧸ A := A.mkQ ∘ₗ μ0
  have hμ : ∀ y : H', y ∈ P ↔ μ y = 0 := by
    intro y
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.mem_comap]
    change (y : Ω) ∈ _ ↔ aeval x g * (y : Ω) ∈ _
    constructor
    · intro h
      exact SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ hC I _ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp h I)
    · intro h
      exact SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ hU I _ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp y.2 I) (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp h I)
  let μb : (H' ⧸ P) →ₗ[S] H ⧸ A := P.liftQ μ (fun y hy ↦ (hμ y).mp hy)
  have hinj : Function.Injective μb := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (fun y hy ↦ (hμ y).mpr hy)
  let π : (H ⧸ A) →ₗ[S] H ⧸ B := Submodule.factor hAB
  have hsurj : Function.Surjective π := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective B z
    exact ⟨A.mkQ m, rfl⟩
  have hex : Function.Exact μb π := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective A z
    change B.mkQ m = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    constructor
    · intro hm
      obtain ⟨t, ht, hst⟩ := hlift _ hm
      change (m : Ω) - aeval x g * t ∈ _ at hst
      refine ⟨P.mkQ ⟨t, ht⟩, ?_⟩
      change A.mkQ (μ0 ⟨t, ht⟩) = A.mkQ m
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
      change aeval x g * t - (m : Ω) ∈ _
      have h1 := neg_mem hst
      convert h1 using 1
      ring
    · rintro ⟨w, hw⟩
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective P w
      change A.mkQ (μ0 y) = A.mkQ m at hw
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap] at hw
      change aeval x g * (y : Ω) - m ∈ _ at hw
      change (m : Ω) ∈ _
      have h1 := sub_mem (hgsec _ y.2) (hWV _ hw)
      convert h1 using 1
      ring
  have hlen := Module.length_eq_add_of_exact μb π hinj hsurj hex

  have hfin : Module.length S (H ⧸ A) ≠ ⊤ := by
    by_cases hx : x = 0
    · have hE0 : IsEmpty (Chart x) := ⟨fun I ↦ by
        obtain ⟨i, hi⟩ := I.2.1
        exact (mem_support x).mp (I.2.2 hi) (by simp [hx])⟩
      have hAt : A = ⊤ := eq_top_iff.mpr fun m _ ↦
        Submodule.mem_comap.mpr (SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ isEmptyElim I)
      have : Subsingleton (H ⧸ A) := Submodule.Quotient.subsingleton_iff.mpr hAt
      rw [Module.length_eq_zero]
      exact ENat.zero_ne_top
    · have : Module.Finite S H := (hFS S Ω N x (Q.tensorProd (twistBundle S x (c : ℤ))) hx).1
      have := h𝔪
      refine length_ne_top_of_smul_eq_zero 𝔪 fun a ha z ↦ ?_
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective A z
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      change a • (m : Ω) ∈ _
      refine SectionCount.Drop.Filt.Step.mem_secs_iff'.mpr fun I ↦ ?_
      rw [hsub, Algebra.smul_def]
      refine Submodule.mul_mem_mul ?_ (SectionCount.Drop.Filt.Step.mem_secs_iff'.mp m.2 I)
      exact Submodule.subset_span ⟨C a, 1, 0, h𝔪K (Ideal.mem_map_of_mem _ ha), one_mem _,
        isHomogeneous_C _ _, isHomogeneous_one _ _, by simp⟩
  have hB' : Module.length S (H ⧸ B) ≠ ⊤ := fun h ↦ hfin (by rw [hlen, h, add_top])
  have hP' : Module.length S (H' ⧸ P) ≠ ⊤ := fun h ↦ hfin (by rw [hlen, h, top_add])
  change ((Module.length S (H ⧸ A)).toNat : ℤ) =
    ((Module.length S (H ⧸ B)).toNat : ℤ) + ((Module.length S (H' ⧸ P)).toNat : ℤ)
  rw [hlen, ENat.toNat_add hP' hB']
  push_cast
  ring

end CycleSplit.Filt.Step

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFibreHilbertFlat
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

theorem interSum_single_eq {R : Type*} [CommRing R] {Ω : Type w} [Field Ω] [Algebra R Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (pp : Ideal (Poly R N)) (L : SubSystem R x Ω) (c : ℕ) :
    interSum pp ![L] c = restrLen pp (L.twist (twistSys R x (c : ℤ))) - restrLen pp (twistSys R x (c : ℤ)) := by
  have huniv : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  have h0 : tensorSub ![L] ∅ = twistSys R x 0 := rfl
  have h1 : tensorSub ![L] {0} = (twistSys R x 0).twist L := rfl
  rw [interSum, huniv, Finset.sum_pair (by decide), h0, h1, twistSys_zero_twist, twistSys_zero_twist]
  simp only [Finset.card_empty, Finset.card_singleton, Nat.sub_zero, Nat.sub_self, pow_one, pow_zero]
  ring

theorem FibreHilbertFlat.proof (h : FibreSectionsFlat.Statement.{u, w}) : FibreHilbertFlat.Statement.{u, w} := by
  intro S _ _ F _ _ _ Ω _ _ _ _ N x M 𝔪 h𝔪 qq hq hconst hsub
  have hM := h S F Ω N x M 𝔪 h𝔪 qq hq hconst 1 hsub
  have hO := h S F Ω N x (twistBundle S x 0) 𝔪 h𝔪 qq hq hconst 1 hsub
  filter_upwards [hM, hO] with c eM eO
  have hO0 : (twistBundle S x 0).toSubSystem = twistSys S x 0 := rfl
  rw [hO0, SubSystem.extend_twistSys, twistSys_zero_twist, twistSys_zero_twist] at eO
  rw [interSum_single_eq, interSum_single_eq, eM, eO]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFibreSectionsFlat
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

open scoped Pointwise

noncomputable section

universe u w

theorem homogeneousComponent_map_eq {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') {N : ℕ}
    (d : ℕ) (p : Poly R N) :
    homogeneousComponent d (MvPolynomial.map φ p) = MvPolynomial.map φ (homogeneousComponent d p) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem mem_of_map_mem_map {S : Type u} [CommRing S] [IsDomain S] {F : Type u} [Field F] [Algebra S F]
    [IsFractionRing S F] {N : ℕ} {qq : Ideal (Poly S N)} (hq : qq.IsPrime)
    (hconst : ∀ s : S, (C s : Poly S N) ∈ qq → s = 0) {p : Poly S N}
    (hp : MvPolynomial.map (algebraMap S F) p ∈ qq.map (MvPolynomial.map (algebraMap S F))) : p ∈ qq := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Fin (N + 1)) (R := S) (S := F)
  have hdisj : Disjoint (((nonZeroDivisors S).map (C : S →+* Poly S N) : Submonoid (Poly S N)) : Set (Poly S N))
      (qq : Set (Poly S N)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsq
    exact nonZeroDivisors.ne_zero hs (hconst s hsq)
  have h := IsLocalization.under_map_of_isPrime_disjoint ((nonZeroDivisors S).map (C : S →+* Poly S N))
    (Poly F N) hq hdisj
  rw [← h]
  exact hp

theorem FibreSectionsFlat.proof (hG : GenericRestrLen.Statement.{u, w}) (hK : FibreRestrKer.Statement.{u, w})
    (hT : RestrQuotTorsionFree.Statement.{u, w}) (hR : DedekindFibreRank.Statement.{u, w})
    (hF : FiniteSections.Statement.{u, w}) : FibreSectionsFlat.Statement.{u, w} := by
  intro S _ _ F _ _ _ Ω _ _ _ _ N x L 𝔪 h𝔪 qq hq hconst e hsub

  have hhom : ∀ p ∈ qq, ∀ d : ℕ, homogeneousComponent d p ∈ qq := fun p hp d => by
    refine mem_of_map_mem_map (F := F) hq hconst ?_
    rw [← homogeneousComponent_map_eq]
    exact hsub.homog _ (Ideal.mem_map_of_mem _ hp) d
  have hx : x ≠ 0 := by
    obtain ⟨i, hi⟩ := hsub.relevant
    rintro rfl
    exact hi (hsub.le ((mem_primeOf_of_isHomogeneous (S := F) _ (isHomogeneous_X F i)).mpr (by simp)))
  filter_upwards [hK S F Ω N x L 𝔪 h𝔪 qq hq hconst e hsub] with c hc
  set Q : LineBundle S x := L.tensorProd (twistBundle S x (c : ℤ)) with hQdef
  have hQ : Q.toSubSystem = L.toSubSystem.twist (twistSys S x (c : ℤ)) := rfl

  rw [← SubSystem.extend_twistSys (S := S) (F := F) (c : ℤ), ← SubSystem.extend_twist, ← hQ,
    hG S F Ω N x Q.toSubSystem qq hhom]

  rw [← hQ] at hc
  rw [restrLen, hc]
  set A := Q.toSubSystem.secs
  set Bq := (Q.toSubSystem.twist (idealSys x qq)).secs
  set K := Bq.comap A.subtype
  have hcomap : (Bq ⊔ 𝔪 • A).comap A.subtype = K ⊔ 𝔪 • (⊤ : Submodule S A) := by
    apply Submodule.map_injective_of_injective A.injective_subtype
    rw [Submodule.map_comap_subtype, Submodule.map_sup, Submodule.map_comap_subtype, Submodule.map_smul'',
      Submodule.map_subtype_top, inf_comm, sup_comm, sup_inf_assoc_of_le _ (Submodule.smul_le_right),
      inf_comm, sup_comm]
  have hmap : (K ⊔ 𝔪 • (⊤ : Submodule S A)).map K.mkQ = 𝔪 • (⊤ : Submodule S (A ⧸ K)) := by
    rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ,
      Submodule.mkQ_map_self, bot_sup_eq]
  have hlen : Module.length S (A ⧸ (K ⊔ 𝔪 • (⊤ : Submodule S A))) =
      Module.length S ((A ⧸ K) ⧸ 𝔪 • (⊤ : Submodule S (A ⧸ K))) := by
    rw [← hmap]
    exact ((Submodule.quotientQuotientEquivQuotient K _ le_sup_left).length_eq).symm
  have : Module.Finite S A := (hF S Ω N x Q hx).1
  rw [hcomap, hlen, hR S (A ⧸ K) inferInstance (hT S F Ω N x Q qq hq hconst e hsub) 𝔪 h𝔪]
  simp

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PInterNumRestrict
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace InterNumRestrict

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {K' : Type w} [Field K'] [Algebra k K'] {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}

theorem inr_foldl_restrict {n : ℕ} (L : Fin n → LineBundle k x) (L' : Fin n → LineBundle k y)
    (rr : Fin n → Ω → K') (hL : ∀ i, RestrictData (L i).toSubSystem hxy (L' i).toSubSystem (rr i)) :
    ∀ (l : List (Fin n)) (Q : LineBundle k x) (Q' : LineBundle k y) (r : Ω → K'),
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r →
      ∃ (P : LineBundle k x) (P' : LineBundle k y) (s : Ω → K'),
        l.foldl (fun F i => F.twist (L i).toSubSystem) Q.toSubSystem = P.toSubSystem ∧
        l.foldl (fun F i => F.twist (L' i).toSubSystem) Q'.toSubSystem = P'.toSubSystem ∧
        RestrictData P.toSubSystem hxy P'.toSubSystem s
  | [], Q, Q', r, h => ⟨Q, Q', r, rfl, rfl, h⟩
  | i :: l, Q, Q', r, h => by
    obtain ⟨s, hs⟩ := RestrictTwist.proof.2 k Ω N x K' y hxy Q (L i) Q' (L' i) r (rr i) h (hL i)
    exact inr_foldl_restrict L L' rr hL l (Q.tensorProd (L i)) (Q'.tensorProd (L' i)) s hs

theorem proof (hRL : RestrLenRestrict.Statement.{u, w}) : InterNumRestrict.Statement.{u, w} := by
  intro k _ Ω _ _ N x K' _ _ y hxy hle pp n hsub L L' rr hL
  have hT : ∀ T : Finset (Fin n), ∀ᶠ c : ℕ in atTop,
      restrLen pp ((tensorSub (fun i => (L' i).toSubSystem) T).twist (twistSys k y (c : ℤ))) =
        restrLen pp ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys k x (c : ℤ))) := by
    intro T
    obtain ⟨r0, h0⟩ := RestrictTwist.proof.1 k Ω N x K' y hxy hle 0
    obtain ⟨P, P', s, hP, hP', hs⟩ := inr_foldl_restrict L L' rr hL
      ((List.finRange n).filter (· ∈ T)) (twistBundle k x 0) (twistBundle k y 0) r0 h0
    have e1 : tensorSub (fun i => (L i).toSubSystem) T = P.toSubSystem := hP
    have e2 : tensorSub (fun i => (L' i).toSubSystem) T = P'.toSubSystem := hP'
    rw [e1, e2]
    exact hRL k Ω N x K' y hxy hle pp n hsub P P' s hs
  have hall : ∀ᶠ c : ℕ in atTop, interSum pp (fun i => (L' i).toSubSystem) c =
      interSum pp (fun i => (L i).toSubSystem) c := by
    filter_upwards [Filter.eventually_all.2 hT] with c hc
    unfold interSum
    exact Finset.sum_congr rfl fun T _ => by rw [hc T]
  unfold interNum limUnder
  rw [Filter.map_congr hall]

end InterNumRestrict

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PLeadingCoeffPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

theorem nef_of_isVeryAmple (hR : GenericPointSectionInput.Statement.{u, w}) {k : Type u} [Field k] {Ω : Type w} [Field Ω]
    [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω} (L : LineBundle k x) (hL : IsVeryAmple L.toSubSystem) :
    Nef L.toSubSystem := by
  intro pp _ hW
  have h := interNum_nonneg_of_veryAmple hR 1 pp (fun _ => L) hW (fun _ => hL)
  have he : (fun _ : Fin 1 => L.toSubSystem) = ![L.toSubSystem] := by
    funext i; fin_cases i; rfl
  rwa [he] at h

theorem LeadingCoeffPos.proof (hR : GenericPointSectionInput.Statement.{u, w})
    (hNef : NefProductNonneg.Statement.{u, w}) (hPos : VeryAmpleProductPos.Statement.{u, w}) :
    LeadingCoeffPos.Statement.{u, w} := by
  intro k _ Ω _ _ N x d M Nb q m b hZ hM hNb hva hb
  let L : Fin (d + 1) → LineBundle k x := fun _ => Nb
  have hV : ((M.tpow q).tensor (twistBundle k x m)).toSubSystem = Nb.toSubSystem := by
    rw [hNb, LineBundle.tensor_toSubSystem, LineBundle.tpow_toSubSystem]
    rfl
  have hm0 : 0 ≤ m := by
    have : (0 : ℤ) ≤ ((d + 1 : ℕ) : ℤ) * b := by positivity
    linarith
  obtain ⟨mn, hmn⟩ := Int.eq_ofNat_of_zero_le hm0

  have h1 : interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) =
      q * bundleNum (primeOf (S := k) x) (Function.update L 0 M) +
        m * bundleNum (primeOf (S := k) x) (Function.update L 0 (twistBundle k x 1)) := by
    have e1 : interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) =
        bundleNum (primeOf (S := k) x) (Function.update L 0 ((M.tpow q).tensor (twistBundle k x m))) := by
      unfold bundleNum
      congr 1
      funext j
      by_cases hj : j = 0
      · subst hj
        simp only [Function.update_self, hV]
      · simp only [Function.update_of_ne hj, L]
    rw [e1, bundleNum_tensor hR hZ, bundleNum_tpow hR hZ, hmn, bundleNum_twist hR hZ]

  have h2 : interNum (primeOf (S := k) x)
      (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
        (fun _ : Fin d => Nb.toSubSystem)) =
      b * bundleNum (primeOf (S := k) x) (Function.update L 0 (twistBundle k x 1)) := by
    rw [← bundleNum_twist hR hZ]
    unfold bundleNum
    congr 1
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero, Function.update_self, twistBundle_toSubSystem]
    · simp only [Fin.cons_succ, Function.update_of_ne (Fin.succ_ne_zero i), L]

  have hX : 0 ≤ bundleNum (primeOf (S := k) x) (Function.update L 0 M) := by
    refine hNef k Ω N x (d + 1) _ _ hZ fun i => ?_
    by_cases hi : i = 0
    · subst hi
      simpa only [Function.update_self] using hM
    · simp only [Function.update_of_ne hi, L]
      exact nef_of_isVeryAmple hR Nb hva

  have hY : 0 < bundleNum (primeOf (S := k) x) (Function.update L 0 (twistBundle k x 1)) := by
    refine hPos k Ω N x (d + 1) _ _ hZ fun i => ?_
    by_cases hi : i = 0
    · subst hi
      simpa only [Function.update_self, twistBundle_toSubSystem] using
        (isVeryAmple_twistSys_one (S := k) (x := x))
    · simp only [Function.update_of_ne hi, L]
      exact hva
  rw [h1, h2]
  have hc := mul_pos (sub_pos.mpr hb) hY
  have hq := mul_nonneg (Int.natCast_nonneg q) hX
  nlinarith

end GroundTheory.Heights₂.Heights.Kleiman
end

