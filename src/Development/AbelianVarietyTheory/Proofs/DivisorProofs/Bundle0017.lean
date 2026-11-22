import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetRelIndexInfConjConst
section
namespace GlobalTheory.DoubleCosetWeight

open Subgroup

theorem inf_map_conj_mul_eq {G : Type} [Group G] (T K : Subgroup G) {t k : G}
    (ht : t ∈ T) (hk : k ∈ K) (q : G) :
    T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom =
      (T ⊓ K.map (MulAut.conj q).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
  ext x
  simp only [mem_inf, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hxT, y, hy, rfl⟩
    refine ⟨q * (k * y * k⁻¹) * q⁻¹, ⟨?_, k * y * k⁻¹, K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk), rfl⟩, ?_⟩
    · have : q * (k * y * k⁻¹) * q⁻¹ = t⁻¹ * (t * q * k * y * (t * q * k)⁻¹) * t := by group
      rw [this]; exact T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
    · group
  · rintro ⟨z, ⟨hzT, y, hy, rfl⟩, rfl⟩
    refine ⟨T.mul_mem (T.mul_mem ht hzT) (T.inv_mem ht), k⁻¹ * y * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hy) hk, ?_⟩
    group

def gen {G : Type} [Group G] (T K : Subgroup G) : Subgroup G :=
  ⨆ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom

theorem gen_map_le {G : Type} [Group G] (T K : Subgroup G) {t : G} (ht : t ∈ T) :
    (gen T K).map (MulAut.conj t).toMonoidHom ≤ gen T K := by
  rw [map_le_iff_le_comap]
  refine iSup_le fun q => ?_
  intro x hx
  rw [mem_comap]
  have h1 : (MulAut.conj t).toMonoidHom x ∈ T ⊓ K.map (MulAut.conj (t * q * 1)).toMonoidHom := by
    rw [inf_map_conj_mul_eq T K ht K.one_mem q]
    exact mem_map_of_mem _ hx
  exact (le_iSup (fun q : G => T ⊓ K.map (MulAut.conj q).toMonoidHom) (t * q * 1)) h1

theorem gen_map_eq {G : Type} [Group G] (T K : Subgroup G) {t : G} (ht : t ∈ T) :
    (gen T K).map (MulAut.conj t).toMonoidHom = gen T K := by
  refine le_antisymm (gen_map_le T K ht) fun x hx => ?_
  have : (MulAut.conj t⁻¹).toMonoidHom x ∈ gen T K :=
    gen_map_le T K (T.inv_mem ht) (mem_map_of_mem _ hx)
  refine ⟨_, this, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

theorem relIndex_eq {G : Type} [Group G] (T C K : Subgroup G)
    (hC : ∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) :
    ∀ t ∈ T, ∀ k ∈ K, ∀ q : G,
      (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C =
        (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C := by
  intro t ht k hk q
  have hN : gen T K ≤ C := iSup_le hC
  have hA : ∀ p : G, T ⊓ K.map (MulAut.conj p).toMonoidHom ≤ gen T K := fun p =>
    le_iSup (fun q : G => T ⊓ K.map (MulAut.conj q).toMonoidHom) p
  have e1 := relIndex_mul_relIndex _ _ _ (hA (t * q * k)) hN
  have e2 := relIndex_mul_relIndex _ _ _ (hA q) hN
  rw [← e1, ← e2, inf_map_conj_mul_eq T K ht hk q]
  congr 1
  conv_lhs => rw [← gen_map_eq T K ht]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj t).injective

end GlobalTheory.DoubleCosetWeight

theorem GlobalTheory.doubleCoset_relIndex_const : ∀ (G : Type) [Group G] (T C K : Subgroup G), (∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) → ∀ t ∈ T, ∀ k ∈ K, ∀ q : G, (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C = (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C :=
  fun G _ T C K hC => GlobalTheory.DoubleCosetWeight.relIndex_eq T C K hC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSemidirectRepSurjective
section
namespace GlobalTheory

theorem doubleCoset_semidirect_surj :
    ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P),
      (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) →
      ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N),
        (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) →
        ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM →
          (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) →
          (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) →
          ∀ d : DoubleCoset.Quotient (TP : Set P) (KP : Set P), ∃ X : N,
            DoubleCoset.mk TP KP (s (Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d)))) * u X)
              = d := by
  intro P M N _ _ _ s π u hs _ hker KP KM L hKs _ _ TM CM TP CP _ hTP _ _ d
  obtain ⟨t, ht, k, hk, hm⟩ := (DoubleCoset.eq TM KM
    (Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d)))) (π (Quotient.out d))).1
    (DoubleCoset.out_eq' TM KM _)
  generalize Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d))) = q at hm ⊢
  obtain ⟨X, hX⟩ := (hker ((s q)⁻¹ * (s t)⁻¹ * Quotient.out d * (s k)⁻¹)).1 (by
    simp only [map_mul, map_inv, hs]
    rw [hm]; group)
  refine ⟨X, ?_⟩
  rw [hX]
  conv_rhs => rw [← DoubleCoset.out_eq' TP KP d]
  rw [DoubleCoset.eq]
  exact ⟨s t, (hTP _).2 ⟨t, ht, rfl⟩, s k, hKs k hk, by group⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSumFundamentalDomain
section
open MeasureTheory

namespace GlobalTheory.DoubleCosetAdjoint

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)

omit [μ.IsMulLeftInvariant] [Countable Γ] in

theorem isFundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H) :
    IsFundamentalDomain Γ ((fun h => h * y) ⁻¹' 𝓕) μ :=
  h𝓕.preimage_of_equiv (measurePreserving_mul_right μ y).quasiMeasurePreserving
    (e := id) Function.bijective_id (fun g h => by
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc])

omit [μ.IsMulLeftInvariant] [Countable Γ] [μ.IsMulRightInvariant] [TopologicalSpace H]
  [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] in
theorem preimage_preimage_mul (y : H) :
    (fun h => h * y) ⁻¹' ((fun h => h * y⁻¹) ⁻¹' 𝓕) = 𝓕 := by
  ext h; simp

theorem setIntegral_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (u : H → ℂ)
    (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (y : H) :
    ∫ h in 𝓕, u (h * y) ∂μ = ∫ h in 𝓕, u h ∂μ := by
  have h1 := (measurePreserving_mul_right μ y).setIntegral_preimage_emb
    (measurableEmbedding_mulRight y) u ((fun h => h * y⁻¹) ⁻¹' 𝓕)
  rw [preimage_preimage_mul] at h1
  rw [h1]
  exact (isFundamentalDomain_mul_right μ Γ 𝓕 h𝓕 y⁻¹).setIntegral_eq h𝓕
    (fun g h => hu g g.2 h)

theorem integrableOn_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (u : H → ℂ)
    (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (y : H) (hi : IntegrableOn u 𝓕 μ) :
    IntegrableOn (fun h => u (h * y)) 𝓕 μ := by
  have h1 := (measurePreserving_mul_right μ y).integrableOn_comp_preimage
    (measurableEmbedding_mulRight y) (f := u) (s := (fun h => h * y⁻¹) ⁻¹' 𝓕)
  rw [preimage_preimage_mul] at h1
  refine h1.2 ?_
  exact ((isFundamentalDomain_mul_right μ Γ 𝓕 h𝓕 y⁻¹).integrableOn_iff h𝓕
    (fun g h => hu g g.2 h)).2 hi

omit [Group H] [IsTopologicalGroup H] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] in

theorem integrableOn_star_mul (F F' : H → ℂ) (hF : Continuous F) (hF' : Continuous F')
    (h1 : IntegrableOn (fun h => star (F h) * F h) 𝓕 μ)
    (h2 : IntegrableOn (fun h => star (F' h) * F' h) 𝓕 μ) :
    IntegrableOn (fun h => star (F h) * F' h) 𝓕 μ := by
  refine Integrable.mono' (h1.norm.add h2.norm)
    (hF.star.mul hF').aestronglyMeasurable (Filter.Eventually.of_forall fun h => ?_)
  simp only [Pi.add_apply, norm_mul, norm_star]
  nlinarith [sq_nonneg (‖F h‖ - ‖F' h‖), mul_nonneg (norm_nonneg (F h)) (norm_nonneg (F' h))]

end GlobalTheory.DoubleCosetAdjoint

open GlobalTheory.DoubleCosetAdjoint in

theorem GlobalTheory.doubleCosetSum_adjoint : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ K : Subgroup H) [Countable Γ] (𝓕 : Set H) (x : H) (A A' : Finset H) (F F' : H → ℂ), IsFundamentalDomain Γ 𝓕 μ → (∀ a ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x * k₂) → (∀ a ∈ A', ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x⁻¹ * k₂) → A.card = A'.card → Continuous F → Continuous F' → (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) → (∀ γ ∈ Γ, ∀ h, F' (γ * h) = F' h) → (∀ k ∈ K, ∀ h, F (h * k) = F h) → (∀ k ∈ K, ∀ h, F' (h * k) = F' h) → IntegrableOn (fun h => star (F h) * F h) 𝓕 μ → IntegrableOn (fun h => star (F' h) * F' h) 𝓕 μ → ∫ h in 𝓕, star (∑ a ∈ A, F (h * a)) * F' h ∂μ = ∫ h in 𝓕, star (F h) * ∑ a ∈ A', F' (h * a) ∂μ := by
  intro H _ _ _ _ _ μ _ _ Γ K _ 𝓕 x A A' F F' h𝓕 hA hA' hc cF cF' lF lF' rF rF' iF iF'
  set u : H → ℂ := fun h => star (F (h * x)) * F' h with hu
  have lu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h := by
    intro γ hγ h
    simp only [hu, mul_assoc, lF γ hγ, lF' γ hγ]
  have iu : IntegrableOn u 𝓕 μ := by
    refine integrableOn_star_mul μ 𝓕 (fun h => F (h * x)) F'
      (cF.comp (continuous_mul_right x)) cF' ?_ iF'
    exact integrableOn_mul_right μ Γ 𝓕 h𝓕 (fun h => star (F h) * F h)
      (fun γ hγ h => by simp only [lF γ hγ]) x iF
  have eA : ∀ a ∈ A, ∃ y, ∀ h, star (F (h * a)) * F' h = u (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA a ha
    refine ⟨k₁, fun h => ?_⟩
    simp only [hu, ← mul_assoc, rF k₂ hk₂, rF' k₁ hk₁]
  have eA' : ∀ a ∈ A', ∃ y, ∀ h, star (F h) * F' (h * a) = u (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA' a ha
    refine ⟨k₁ * x⁻¹, fun h => ?_⟩
    simp only [hu, ← mul_assoc, rF' k₂ hk₂, inv_mul_cancel_right, rF k₁ hk₁]
  have key : ∀ (B : Finset H) (t : H → H → ℂ), (∀ a ∈ B, ∃ y, ∀ h, t a h = u (h * y)) →
      ∫ h in 𝓕, ∑ a ∈ B, t a h ∂μ = B.card • ∫ h in 𝓕, u h ∂μ := by
    intro B t ht
    rw [integral_finset_sum, ← Finset.sum_const]
    · refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨y, hy⟩ := ht a ha
      simp only [hy]
      exact setIntegral_mul_right μ Γ 𝓕 h𝓕 u lu y
    · intro a ha
      obtain ⟨y, hy⟩ := ht a ha
      have : t a = fun h => u (h * y) := funext hy
      rw [this]
      exact integrableOn_mul_right μ Γ 𝓕 h𝓕 u lu y iu
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [key A (fun a h => star (F (h * a)) * F' h) eA,
    key A' (fun a h => star (F h) * F' (h * a)) eA', hc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualHopfOrderGaussSum
section
open IsLocalRing Polynomial

namespace GlobalTheory.EtaleSpreadReg

theorem isDedekindDomain_atPrime (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (p : Ideal A) [p.IsPrime] (hp : p.height ≤ 1) :
    IsDedekindDomain (Localization.AtPrime p) := by
  have hic : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hd : Ring.KrullDimLE 1 (Localization.AtPrime p) := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p]
    exact_mod_cast hp
  have : Ring.DimensionLEOne (Localization.AtPrime p) :=
    ⟨fun {P} hP hPp => Ring.krullDimLE_one_iff_of_isPrime_bot.mp hd P hP hPp⟩
  exact {}

theorem isRegularLocalRing_polynomial_atPrime (A : Type*) [CommRing A] (Q₀ : Ideal A[X])
    [Q₀.IsPrime] [IsRegularRing (Localization.AtPrime (Q₀.under A))] :
    IsRegularLocalRing (Localization.AtPrime Q₀) := by
  set p : Ideal A := Q₀.under A with hpdef
  let Ap := Localization.AtPrime p
  letI : Algebra A[X] Ap[X] := Polynomial.algebra A Ap
  let M : Submonoid A[X] := Submonoid.map C p.primeCompl
  haveI : IsLocalization M Ap[X] := Polynomial.isLocalization p.primeCompl Ap
  have hdisj : Disjoint (M : Set A[X]) (Q₀ : Set A[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ haQ
    exact ha haQ
  let Q' : Ideal Ap[X] := Q₀.map (algebraMap A[X] Ap[X])
  haveI hQ' : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M Ap[X] Q₀ inferInstance hdisj
  have hc : Q'.comap (algebraMap A[X] Ap[X]) = Q₀ :=
    IsLocalization.comap_map_of_isPrime_disjoint M Ap[X] inferInstance hdisj
  have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime Q') Q'
  have e : (Q'.comap (algebraMap A[X] Ap[X])).primeCompl = Q₀.primeCompl := by
    ext x; simp only [Ideal.mem_primeCompl_iff, hc]
  have h2 : IsLocalization Q₀.primeCompl (Localization.AtPrime Q') := by
    rw [← e]; exact h
  have hreg : IsRegularLocalRing (Localization.AtPrime Q') := isRegularRing_iff.mp inferInstance Q'
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv Q₀.primeCompl (Localization.AtPrime Q') (Localization.AtPrime Q₀)).toRingEquiv

theorem isRegularLocalRing_atPrime_of_etale (S T : Type*) [CommRing S] [IsNoetherianRing S]
    [CommRing T] [Algebra S T] [Algebra.Etale S T] (q : Ideal T) [q.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime (q.under S))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing S T
  let p : Ideal S := q.under S
  let := Localization.AtPrime.algebraOfLiesOver p q
  have hun : Algebra.IsUnramifiedAt S q := inferInstance
  have hm := ((Algebra.isUnramifiedAt_iff_map_eq S p q).mp hun).2
  have hm' : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [← hm, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have h1 := Ideal.spanFinrank_map_le_of_fg
    (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)).fg_of_isNoetherianRing
  rw [hm'] at h1
  have h2 : p.height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q]
    exact le_self_add
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
  refine le_trans ?_ (WithBot.coe_le_coe.mpr h2)
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
    ← hreg.spanFinrank_maximalIdeal]
  exact_mod_cast h1

theorem isRegularLocalRing_atPrime :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime] (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
    (P.comap (algebraMap A (Localization.AtPrime QA))).height ≤ 1 →
    IsRegularLocalRing (Localization.AtPrime P) := by
  intro A _ _ _ _ EA _ _ _ _ _ QA _ P _ hP
  let Q : Ideal EA := P.comap (algebraMap EA (Localization.AtPrime QA))
  haveI hLoc : IsLocalization.AtPrime (Localization.AtPrime P) Q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization QA.primeCompl
      (Localization.AtPrime P) P
  have hpe : (Q.under (Polynomial A)).under A = P.comap (algebraMap A (Localization.AtPrime QA)) := by
    rw [Ideal.under_under]
    show Ideal.comap (algebraMap A EA) (Ideal.comap (algebraMap EA (Localization.AtPrime QA)) P) = _
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  haveI : IsDedekindDomain (Localization.AtPrime ((Q.under (Polynomial A)).under A)) :=
    isDedekindDomain_atPrime A _ (hpe ▸ hP)
  have h0 := isRegularLocalRing_polynomial_atPrime A (Q.under (Polynomial A))
  have h1 := isRegularLocalRing_atPrime_of_etale (Polynomial A) EA Q h0
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) (Localization.AtPrime P)).toRingEquiv

end GlobalTheory.EtaleSpreadReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberDeformationExtendsAway
section
namespace GlobalTheory

def dualNumberRingHomMap {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') :
    DualNumber S →+* DualNumber S' where
  toFun x := TrivSqZeroExt.inl (f x.fst) + TrivSqZeroExt.inr (f x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, mul_comm] <;> ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring

theorem dualNumber_deformation_extends_away :
    ∀ {S S' : Type} [CommRing S] [CommRing S'] [Algebra S S'] (g : S) [IsLocalization.Away g S']
      (d : S →+* DualNumber S), (∀ s, (d s).fst = s) →
      ∃ d' : S' →+* DualNumber S', (∀ s, (d' s).fst = s) ∧
        ∀ s, (d' (algebraMap S S' s)).snd = algebraMap S S' (d s).snd := by
  intro S S' _ _ _ g _ d hd
  let ψ : S →+* DualNumber S' := (dualNumberRingHomMap (algebraMap S S')).comp d
  have hψ : ∀ s, ψ s = TrivSqZeroExt.inl (algebraMap S S' (d s).fst)
      + TrivSqZeroExt.inr (algebraMap S S' (d s).snd) := fun s => rfl
  have hu : IsUnit (ψ g) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hψ]
    simpa [hd] using IsLocalization.Away.algebraMap_isUnit (S := S') g
  refine ⟨IsLocalization.Away.lift g hu, ?_, ?_⟩
  · have h : (TrivSqZeroExt.fstHom S' S' S').toRingHom.comp (IsLocalization.Away.lift g hu)
        = RingHom.id S' := by
      apply IsLocalization.ringHom_ext (Submonoid.powers g)
      ext s
      simp [IsLocalization.Away.lift, IsLocalization.lift_eq, hψ, hd]
    intro s
    exact congrArg (fun F : S' →+* S' => F s) h
  · intro s
    simp [IsLocalization.Away.lift, IsLocalization.lift_eq, hψ]
    rw [Algebra.smul_def, mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrExistsUnitPowEqMulUniformizer
section
namespace GlobalTheory

theorem dvr_pow_mul_eq_unit_mul_pow_unif :
    ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V], Function.Injective (algebraMap T V) →
    ∀ (α : V) (ϖ u : T) (m k : ℕ), Irreducible ϖ → IsUnit u → 0 < k →
    α ^ (m * k) = algebraMap T V (u * ϖ ^ k) →
    ∃ γ : V, IsUnit γ ∧ α ^ m = γ * algebraMap T V ϖ ∧ γ ^ k = algebraMap T V u := by
  intro T V _ _ _ _ _ _ _ hinj α ϖ u m k hϖ hu hk h
  have hw : algebraMap T V ϖ ≠ 0 := by
    intro h0
    apply hϖ.ne_zero
    apply hinj
    rw [h0, map_zero]
  have hu' : IsUnit (algebraMap T V u) := hu.map _
  have hxk : (α ^ m) ^ k = algebraMap T V u * (algebraMap T V ϖ) ^ k := by
    rw [← pow_mul, h, map_mul, map_pow]
  have hwk : (algebraMap T V ϖ) ^ k ≠ 0 := pow_ne_zero _ hw
  rcases ValuationRing.dvd_total (α ^ m) (algebraMap T V ϖ) with ⟨c, hc⟩ | ⟨c, hc⟩
  ·
    have heq : (c ^ k * algebraMap T V u) * (algebraMap T V ϖ) ^ k = 1 * (algebraMap T V ϖ) ^ k := by
      calc c ^ k * algebraMap T V u * (algebraMap T V ϖ) ^ k
          = c ^ k * (α ^ m) ^ k := by rw [hxk]; ring
        _ = (α ^ m * c) ^ k := by ring
        _ = (algebraMap T V ϖ) ^ k := by rw [← hc]
        _ = 1 * (algebraMap T V ϖ) ^ k := by ring
    have h1 := mul_right_cancel₀ hwk heq
    have hc' : IsUnit c := (isUnit_pow_iff hk.ne').mp (IsUnit.of_mul_eq_one _ h1)
    obtain ⟨cu, rfl⟩ := hc'
    refine ⟨↑cu⁻¹, Units.isUnit _, ?_, ?_⟩
    · rw [hc, mul_comm (α ^ m), ← mul_assoc, Units.inv_mul, one_mul]
    · calc ((↑cu⁻¹ : V)) ^ k = (↑cu⁻¹ : V) ^ k * ((↑cu : V) ^ k * algebraMap T V u) := by
            rw [h1, mul_one]
        _ = algebraMap T V u := by
            rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  ·
    have heq : c ^ k * (algebraMap T V ϖ) ^ k = algebraMap T V u * (algebraMap T V ϖ) ^ k := by
      rw [← hxk, hc]; ring
    have h1 := mul_right_cancel₀ hwk heq
    exact ⟨c, (isUnit_pow_iff hk.ne').mp (h1 ▸ hu'), by rw [hc, mul_comm], h1⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrLocPrincipalPrime
section
noncomputable section

namespace GlobalTheory

theorem dvr_loc_principal_prime : ∀ {L : Type} [Field L] (A : Subring L) (t : A), IsNoetherianRing A → (t : L) ≠ 0 →
    (Ideal.span {t}).IsPrime → (∀ f : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (V : ValuationSubring L) (hA : ∀ a ∈ A, a ∈ V),
      IsDiscreteValuationRing V ∧ Irreducible (⟨t, hA _ t.2⟩ : V) ∧
      (∀ s : A, s ∉ Ideal.span {t} → IsUnit (⟨s, hA _ s.2⟩ : V)) ∧
      (∀ f : V, ∃ a s : A, s ∉ Ideal.span {t} ∧ (f : L) * s = a) ∧
      (A.subtype.codRestrict V fun a => hA _ a.2).EssFiniteType := by
  intro L _ A t hN ht hp hfr
  set p : Ideal A := Ideal.span {t} with hpdef
  haveI : IsFractionRing A L := IsFractionRing.of_field A L fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hfr z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by
      show z = a / b
      rw [← h, mul_div_cancel_right₀ _ hb0]⟩
  let V0 : Subalgebra A L := Localization.subalgebra.ofField L p.primeCompl p.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime V0 p := Localization.subalgebra.isLocalization_ofField _ _ _
  haveI : IsLocalRing V0 := IsLocalization.AtPrime.isLocalRing V0 p
  haveI : IsNoetherianRing V0 := IsLocalization.isNoetherianRing p.primeCompl V0 hN
  have hmax : IsLocalRing.maximalIdeal V0 = Ideal.span {algebraMap A V0 t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p V0, hpdef, Ideal.map_span, Set.image_singleton]
  have ht0 : algebraMap A V0 t ≠ 0 := fun h => ht (congrArg Subtype.val h)
  have hnf : ¬ IsField V0 := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact ht0
  have hdvr : IsDiscreteValuationRing V0 :=
    ((IsDiscreteValuationRing.TFAE V0 hnf).out 0 4).2
      (⟨⟨_, hmax⟩⟩ : (IsLocalRing.maximalIdeal V0).IsPrincipal)
  haveI : IsFractionRing V0 L := IsFractionRing.of_field V0 L fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hfr z
    exact ⟨algebraMap A V0 ⟨a, ha⟩, algebraMap A V0 ⟨b, hb⟩, by
      show z = a / b
      rw [← h, mul_div_cancel_right₀ _ hb0]⟩
  let V : ValuationSubring L :=
    { V0.toSubring with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger V0 x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact Or.inl (hy ▸ y.2)
        · exact Or.inr (hy ▸ y.2) }
  have hA : ∀ a ∈ A, a ∈ V := fun a ha => V0.algebraMap_mem (⟨a, ha⟩ : A)
  refine ⟨V, hA, hdvr, ?_, ?_, ?_, ?_⟩
  · exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  · intro s hs
    exact IsLocalization.map_units V0 (⟨s, hs⟩ : p.primeCompl)
  · intro f
    obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective p.primeCompl (show V0 from f)
    refine ⟨x, y, y.2, ?_⟩
    have := congrArg (algebraMap V0 L) (IsLocalization.mk'_spec V0 x y)
    have hxy' : IsLocalization.mk' V0 x y = (show V0 from f) := hxy
    rw [hxy', map_mul] at this
    exact this
  · have h := (RingHom.essFiniteType_algebraMap (R := A) (S := V0)).2
      (Algebra.EssFiniteType.of_isLocalization V0 p.primeCompl)
    exact h

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvectorMemSpanTwistedTraceImage
section
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

open scoped BigOperators Matrix in
open Polynomial in

theorem _root_.GlobalTheory.eigenvector_mem_span_twistedTrace_image :
    ∀ (H K V : Type) [Group H] [Fintype H] [Field K] [CharZero K] [AddCommGroup V] [Module K V] (st : H → V →ₗ[K] V), (∀ h h' x, st (h * h') x = st h' (st h x)) → ∀ (χ : H →* Kˣ) (s : Set V), Submodule.span K s = ⊤ → ∀ x : V, (∀ h, st h x = ((χ h : Kˣ) : K) • x) → x ∈ Submodule.span K ((fun y => ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h y) '' s) := by
  intro H K V _ _ _ _ _ _ st _ χ s hs x hx
  let P : V →ₗ[K] V := ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h
  have hP : (fun y => ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h y) = ⇑P := by
    funext y
    simp [P, LinearMap.sum_apply]
  have hPx : P x = (Fintype.card H : K) • x := by
    rw [← hP]
    simp only [hx, smul_smul, Units.inv_mul, one_smul, Finset.sum_const, Finset.card_univ]
    rw [Nat.cast_smul_eq_nsmul]
  have hcard : (Fintype.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hxP : x = P ((Fintype.card H : K)⁻¹ • x) := by
    rw [map_smul, hPx, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [hP, Submodule.span_image, hs, hxP]
  exact Submodule.mem_map_of_mem Submodule.mem_top

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EntireEqOfEqOnHalfPlane
section
namespace GlobalTheory.EntireFunctionHalfPlane

open Filter Topology

theorem entire_eq_of_eqOn_halfPlane {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (a : ℝ) (h : ∀ s : ℂ, a < s.re → f s = g s) : f = g := by
  have hf' : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hg' : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have hopen : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((a + 1 : ℝ) : ℂ) ∈ {s : ℂ | a < s.re} := by
    simp
  have hev : f =ᶠ[𝓝 ((a + 1 : ℝ) : ℂ)] g :=
    Filter.eventually_of_mem (hopen.mem_nhds hmem) (fun s hs => h s hs)
  exact AnalyticOnNhd.eq_of_eventuallyEq hf' hg' hev

end GlobalTheory.EntireFunctionHalfPlane
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtChart
section
noncomputable section
namespace GlobalTheory.DenseSec

def EtChart (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {g : ℕ} (t : Fin g → A) (h : A) : Prop :=
  letI : Algebra (MvPolynomial (Fin g) R) (Localization.Away h) :=
    ((algebraMap A (Localization.Away h)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  Algebra.Etale (MvPolynomial (Fin g) R) (Localization.Away h)

def pt {R A Ω : Type} [CommRing R] [CommRing A] [Algebra R A] [Field Ω] [Algebra R Ω] (a : A →ₐ[R] Ω) :
    TensorProduct R Ω A →ₐ[Ω] Ω :=
  Algebra.TensorProduct.lift (AlgHom.id Ω Ω) a (fun _ _ => Commute.all _ _)

end GlobalTheory.DenseSec
end
end

