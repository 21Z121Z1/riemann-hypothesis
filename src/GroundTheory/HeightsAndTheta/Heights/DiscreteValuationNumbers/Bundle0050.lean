import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleHomLocLaurent
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleHomLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial HomLocLaurent

noncomputable section

universe u

set_option linter.style.haveILetI false

section Mult

theorem length_quotient_of_surjective {S C : Type*} [CommRing S] [CommRing C] [Algebra S C]
    (h : Function.Surjective (algebraMap S C)) (I : Ideal C) :
    Module.length S (C ⧸ I) = Module.length C (C ⧸ I) :=
  Module.length_eq_of_surjective h

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
  {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime]

theorem multAt_eq_length_locC (hPW : P ≤ W) (x : MRing ι R) :
    multAt (P ⊔ Ideal.span {x}) W =
      Module.length (locC hPW) (locC hPW ⧸ Ideal.span {algQC hPW (Ideal.Quotient.mk P x)}) := by
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  set J := P ⊔ Ideal.span {x}
  set I : Ideal (locC hPW) := Ideal.span {algQC hPW (Ideal.Quotient.mk P x)}
  set θ : MRing ι R →+* locC hPW := (algQC hPW).comp (Ideal.Quotient.mk P) with hθ
  have hne : ∀ {g : MRing ι R}, g ∉ W → fr P g ≠ 0 := fun hg => fr_ne_zero fun h => hg (hPW h)
  have hunit : ∀ {s : MRing ι R}, s ∉ W → IsUnit (θ s) := fun hs =>
    (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mpr
      fun h => hs ((Ideal.mem_quotient_iff_mem hPW).mp h)
  obtain ⟨θW, hθWdef⟩ : ∃ φ : Localization.AtPrime W →+* locC hPW,
      φ = IsLocalization.lift (M := W.primeCompl) (g := θ) fun s => hunit s.2 := ⟨_, rfl⟩
  have hθW : ∀ f, θW (algebraMap (MRing ι R) (Localization.AtPrime W) f) = θ f := fun f => by
    rw [hθWdef]
    exact IsLocalization.lift_eq _ _

  have hval : ∀ (a s : MRing ι R) (hs : s ∈ W.primeCompl),
      (θW (IsLocalization.mk' (Localization.AtPrime W) a ⟨s, hs⟩) : FractionRing (MRing ι R ⧸ P)) *
        fr P s = fr P a := by
    intro a s hs
    have := congrArg θW (IsLocalization.mk'_spec (Localization.AtPrime W) a ⟨s, hs⟩)
    rw [RingHom.map_mul, hθW, hθW] at this
    exact congrArg Subtype.val this
  have hsurj : Function.Surjective θW := by
    rintro ⟨c, a', s', hs', rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
    have hsW : s ∉ W := fun h => hs' (Ideal.mem_map_of_mem _ h)
    refine ⟨IsLocalization.mk' (Localization.AtPrime W) a (⟨s, hsW⟩ : W.primeCompl), Subtype.ext ?_⟩
    have h := hval a s hsW
    change _ = fr P a * (fr P s)⁻¹
    rw [← h, mul_assoc, mul_inv_cancel₀ (hne hsW), mul_one]
  letI : Algebra (Localization.AtPrime W) (locC hPW) := θW.toAlgebra
  let f : Localization.AtPrime W →ₐ[Localization.AtPrime W] (locC hPW ⧸ I) :=
    Algebra.ofId (Localization.AtPrime W) (locC hPW ⧸ I)
  have hf : ∀ y, f y = Ideal.Quotient.mk I (θW y) := fun y => rfl
  have hfs : Function.Surjective f := fun q => by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨y, rfl⟩ := hsurj c
    exact ⟨y, hf y⟩
  have hker : RingHom.ker f = J.map (algebraMap (MRing ι R) (Localization.AtPrime W)) := by
    apply le_antisymm
    · intro y hy
      rw [RingHom.mem_ker, hf, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hy
      obtain ⟨⟨c, b', t', ht', hc⟩, hcy⟩ := hy
      obtain ⟨⟨a, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl y
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t'
      have htW : t ∉ W := fun h => ht' (Ideal.mem_map_of_mem _ h)
      have h1 := hval a s hs
      rw [← hcy] at h1
      change c * fr P x * fr P s = fr P a at h1
      rw [hc] at h1
      change fr P b * (fr P t)⁻¹ * fr P x * fr P s = fr P a at h1
      have hat : a * t - b * x * s ∈ P := by
        have h2 : fr P a * fr P t = fr P b * fr P x * fr P s := by
          rw [← h1]
          calc _ = fr P b * fr P x * fr P s * ((fr P t)⁻¹ * fr P t) := by ring
            _ = _ := by rw [inv_mul_cancel₀ (hne htW), mul_one]
        rw [← fr_eq_zero_iff, map_sub, map_mul, map_mul, map_mul, h2, sub_self]
      have hatJ : a * t ∈ J := by
        have : a * t = (a * t - b * x * s) + (b * s) * x := by ring
        rw [this]
        exact J.add_mem (Ideal.mem_sup_left hat)
          (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
      have hst : s * t ∈ W.primeCompl := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs htW
      have heq : IsLocalization.mk' (Localization.AtPrime W) a (⟨s, hs⟩ : W.primeCompl) *
          algebraMap (MRing ι R) (Localization.AtPrime W) (s * t) =
            algebraMap (MRing ι R) (Localization.AtPrime W) (a * t) := by
        rw [map_mul, ← mul_assoc, IsLocalization.mk'_spec, map_mul]
      have hu : IsUnit (algebraMap (MRing ι R) (Localization.AtPrime W) (s * t)) :=
        IsLocalization.map_units (Localization.AtPrime W) (⟨s * t, hst⟩ : W.primeCompl)
      rw [← Ideal.mul_unit_mem_iff_mem _ hu, heq]
      exact Ideal.mem_map_of_mem _ hatJ
    · rw [Ideal.map_le_iff_le_comap]
      intro j hj
      rw [Ideal.mem_comap, RingHom.mem_ker, hf, hθW, Ideal.Quotient.eq_zero_iff_mem]
      have hJ : J ≤ I.comap θ := by
        refine sup_le (fun p hp => ?_) ?_
        · have h0 : Ideal.Quotient.mk P p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
          rw [Ideal.mem_comap, hθ, RingHom.comp_apply, h0, RingHom.map_zero]
          exact zero_mem _
        · rw [Ideal.span_le, Set.singleton_subset_iff]
          exact Ideal.subset_span rfl
      exact Ideal.mem_comap.mp (hJ hj)
  have hlen := (Ideal.quotientKerAlgEquivOfSurjective hfs).toLinearEquiv.length_eq
  rw [multAt, length_localizedModule_quotient_eq, ← (Submodule.quotEquivOfEq _ _ hker).length_eq, hlen]
  exact length_quotient_of_surjective hsurj I

end Mult

theorem DivCycleHomLoc.proof (h : HomLocRingLocal.Statement.{u}) : DivCycleHomLoc.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP c x hx hxP W hW hWrel g hg hgW hz
  haveI := hP.isPrime
  haveI : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_trans le_sup_left hW.1.2
  have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.proof O K ι _ W
    (isMultiHomogIdeal_sup_span_of_form hP.multiHomog hx) hW
  haveI : IsLocalRing (homLocRing P W) := (h O K ι P hP c x hx hxP W hW hWrel).1
  choose T hT using hWrel
  rw [← length_quotient_incAC T hPW hT hP.multiHomog hWh, multAt_eq_length_locC hPW x]
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  have hgu : IsUnit (algQC hPW (Ideal.Quotient.mk P g)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mpr
      fun h => hgW ((Ideal.mem_quotient_iff_mem hPW).mp h)
  have hxz : algQC hPW (Ideal.Quotient.mk P x) =
      incAC hPW ⟨_, hz⟩ * algQC hPW (Ideal.Quotient.mk P g) := by
    apply Subtype.ext
    change fr P x = fr P x / fr P g * fr P g
    rw [div_mul_cancel₀ _ (fr_ne_zero fun h => hgW (hPW h))]
  rw [hxz, Ideal.span_singleton_mul_right_unit hgu]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingIsLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem HomLocRingIsLocal.proof (h : HomLocRingMem.Statement.{u}) : HomLocRingIsLocal.Statement.{u} := by
  intro R _ K _ ι P W _ hW hPW
  let F := FractionRing (MRing ι R ⧸ P)
  let φ : MRing ι R →+* F := (algebraMap (MRing ι R ⧸ P) F).comp (Ideal.Quotient.mk P)
  have hφ : ∀ a, φ a = 0 ↔ a ∈ P := by
    intro a
    simp only [φ, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hne : ∀ a, a ∉ W → φ a ≠ 0 := fun a ha h0 => ha (hPW ((hφ a).1 h0))
  have key : ∀ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b → IsMultiHomog g b → g ∉ W →
      ∀ hz : φ f / φ g ∈ homLocRing P W, IsUnit (⟨_, hz⟩ : homLocRing P W) ↔ f ∉ W := by
    intro b f g hf hg hgW hz
    constructor
    · rintro ⟨u, hu⟩ hfW
      obtain ⟨b', f', g', -, -, hg'W, hw⟩ :=
        (h R K ι P W hW hPW ((u⁻¹ : (homLocRing P W)ˣ) : homLocRing P W)).1 (u⁻¹ : (homLocRing P W)ˣ).1.2
      have h1 : (φ f / φ g) * (φ f' / φ g') = 1 := by
        have e := congrArg Subtype.val u.mul_inv
        rw [Subring.coe_mul, hu, Subring.coe_one] at e
        rw [← e]
        congr 1
        exact hw.symm
      have h2 : φ (f * f' - g * g') = 0 := by
        rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hne g hgW) (hne g' hg'W))] at h1
        rw [map_sub, map_mul, map_mul, h1, sub_self]
      have h3 : f * f' - g * g' ∈ W := hPW ((hφ _).1 h2)
      have h4 : g * g' ∈ W := by
        have := W.sub_mem (W.mul_mem_right f' hfW) h3
        simpa using this
      rcases hW.mem_or_mem h4 with h5 | h5
      exacts [hgW h5, hg'W h5]
    · intro hfW
      have hgf : φ g / φ f ∈ homLocRing P W := Subring.subset_closure ⟨b, g, f, hg, hf, hfW, rfl⟩
      refine IsUnit.of_mul_eq_one ⟨_, hgf⟩ ?_
      apply Subtype.ext
      rw [Subring.coe_mul, Subring.coe_one]
      rw [div_mul_div_comm, mul_comm (φ f) (φ g)]
      exact div_self (mul_ne_zero (hne g hgW) (hne f hfW))
  refine ⟨?_, key⟩
  have hnu : ∀ z : homLocRing P W, ¬ IsUnit z → ∃ (b : K → ℕ) (f g : MRing ι R),
      IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ W ∧ f ∈ W ∧ (z : F) = φ f / φ g := by
    intro z hz
    obtain ⟨b, f, g, hf, hg, hgW, hzfg⟩ := (h R K ι P W hW hPW z).1 z.2
    refine ⟨b, f, g, hf, hg, hgW, ?_, hzfg⟩
    by_contra hfW
    have hmem : φ f / φ g ∈ homLocRing P W := hzfg ▸ z.2
    have e : z = ⟨_, hmem⟩ := Subtype.ext hzfg
    exact hz (e ▸ (key b f g hf hg hgW hmem).2 hfW)
  refine IsLocalRing.of_nonunits_add ?_
  intro x y hx hy
  obtain ⟨b₁, f₁, g₁, hf₁, hg₁, hg₁W, hf₁W, hx'⟩ := hnu x hx
  obtain ⟨b₂, f₂, g₂, hf₂, hg₂, hg₂W, hf₂W, hy'⟩ := hnu y hy
  have hnum : IsMultiHomog (f₁ * g₂ + f₂ * g₁) (b₁ + b₂) :=
    IsWeightedHomogeneous.add (IsWeightedHomogeneous.mul hf₁ hg₂)
      (by rw [add_comm]; exact IsWeightedHomogeneous.mul hf₂ hg₁)
  have hden : IsMultiHomog (g₁ * g₂) (b₁ + b₂) := IsWeightedHomogeneous.mul hg₁ hg₂
  have hdenW : g₁ * g₂ ∉ W := fun h5 => (hW.mem_or_mem h5).elim hg₁W hg₂W
  have hsum : ((x + y : homLocRing P W) : F) = φ (f₁ * g₂ + f₂ * g₁) / φ (g₁ * g₂) := by
    rw [Subring.coe_add, hx', hy', div_add_div _ _ (hne g₁ hg₁W) (hne g₂ hg₂W), map_add, map_mul, map_mul,
      map_mul, mul_comm (φ g₁) (φ f₂)]
  have hmem : φ (f₁ * g₂ + f₂ * g₁) / φ (g₁ * g₂) ∈ homLocRing P W := hsum ▸ (x + y).2
  have e : x + y = ⟨_, hmem⟩ := Subtype.ext hsum
  rw [mem_nonunits_iff, e, key (b₁ + b₂) _ _ hnum hden hdenW hmem, not_not]
  exact W.add_mem (W.mul_mem_right _ hf₁W) (W.mul_mem_right _ hf₂W)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem homLocRing_form_not_mem {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {R : Type u} [CommRing R] {W : Ideal (MRing ι R)} (hW : W.IsPrime) (hrel : IsRelevant W)
    (c : K → ℕ) : ∃ g : MRing ι R, IsMultiHomog g c ∧ g ∉ W := by
  choose i hi using hrel
  refine ⟨∏ k, X ⟨k, i k⟩ ^ c k, ?_, ?_⟩
  · have hc : c = ∑ k, c k • blockWeight ι ⟨k, i k⟩ := by
      funext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    have h := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ c k)
      (fun k => c k • blockWeight ι ⟨k, i k⟩)
      fun k _ => (isWeightedHomogeneous_X R (blockWeight ι) _).pow _
    rw [← hc] at h
    exact h
  · intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hW)).mp h
    exact hi k (hW.mem_of_pow_mem _ hk)

theorem HomLocRingLocal.proof (hloc : HomLocRingIsLocal.Statement.{u})
    (hnoeth : HomLocRingNoetherian.Statement.{u}) (hdim : HomLocRingDimLe.Statement.{u}) :
    HomLocRingLocal.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP c x hx hxP W hW hWrel
  have := hP.isPrime
  have hWp : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hxW : x ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  obtain ⟨hlocal, hunit⟩ := hloc O K ι P W hWp hPW
  have hnoe := hnoeth O K ι P W hP.multiHomog hWp hWrel hPW
  refine ⟨hlocal, hnoe, le_antisymm ?_ ?_⟩
  · refine (hdim O K ι P W hP.multiHomog hWp hWrel hPW).trans ?_
    have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
    exact_mod_cast h1
  · obtain ⟨g, hg, hgW⟩ := homLocRing_form_not_mem hWp hWrel c
    have hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) ∈
          homLocRing P W :=
      Subring.subset_closure ⟨c, x, g, hx, hg, hgW, rfl⟩
    have hnu : ¬ IsUnit (⟨_, hz⟩ : homLocRing P W) :=
      fun h => (hunit c x g hx hg hgW hz).mp h hxW
    have hne : (⟨_, hz⟩ : homLocRing P W) ≠ 0 := by
      intro h0
      have h1 := congrArg Subtype.val h0
      simp only [ZeroMemClass.coe_zero, div_eq_zero_iff,
        IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h1
      rcases h1 with h1 | h1
      · exact hxP h1
      · exact hgW (hPW h1)
    have hlt : (⊥ : Ideal (homLocRing P W)) < IsLocalRing.maximalIdeal (homLocRing P W) := by
      refine bot_lt_iff_ne_bot.mpr fun h => hne ?_
      have hm := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rwa [h, Ideal.mem_bot] at hm
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    have h3 : (1 : ℕ∞) ≤ (IsLocalRing.maximalIdeal (homLocRing P W)).height :=
      le_trans le_add_self h2
    exact_mod_cast h3

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem HomLocRingMem.algebraMap_mk_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) [P.IsPrime] {g : MRing ι R} (hg : g ∉ P) :
    algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  exact hg

theorem HomLocRingMem.proof : HomLocRingMem.Statement := by
  intro R _ K _ ι P W _ hW hPW z
  have hne : ∀ g : MRing ι R, g ∉ W →
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 :=
    fun g hg => HomLocRingMem.algebraMap_mk_ne_zero P (fun h => hg (hPW h))
  have h1W : (1 : MRing ι R) ∉ W := fun h => hW.ne_top ((Ideal.eq_top_iff_one W).mpr h)
  constructor
  · intro hz
    refine Subring.closure_induction (fun x hx => hx) ?_ ?_ ?_ ?_ ?_ hz
    · exact ⟨0, 0, 1, isWeightedHomogeneous_zero R _ _, isWeightedHomogeneous_one R _, h1W, by simp⟩
    · exact ⟨0, 1, 1, isWeightedHomogeneous_one R _, isWeightedHomogeneous_one R _, h1W, by simp⟩
    · rintro x y - - ⟨b₁, f₁, g₁, hf₁, hg₁, hW₁, rfl⟩ ⟨b₂, f₂, g₂, hf₂, hg₂, hW₂, rfl⟩
      refine ⟨b₁ + b₂, f₁ * g₂ + g₁ * f₂, g₁ * g₂, (hf₁.mul hg₂).add ?_, hg₁.mul hg₂,
        fun h => (hW.mem_or_mem h).elim hW₁ hW₂, ?_⟩
      · rw [add_comm b₁ b₂, mul_comm g₁ f₂]
        exact hf₂.mul hg₁
      · simp only [map_add, map_mul]
        rw [div_add_div _ _ (hne g₁ hW₁) (hne g₂ hW₂)]
    · rintro x - ⟨b, f, g, hf, hg, hgW, rfl⟩
      exact ⟨b, -f, g, hf.neg, hg, hgW, by simp only [map_neg, neg_div]⟩
    · rintro x y - - ⟨b₁, f₁, g₁, hf₁, hg₁, hW₁, rfl⟩ ⟨b₂, f₂, g₂, hf₂, hg₂, hW₂, rfl⟩
      refine ⟨b₁ + b₂, f₁ * f₂, g₁ * g₂, hf₁.mul hf₂, hg₁.mul hg₂,
        fun h => (hW.mem_or_mem h).elim hW₁ hW₂, ?_⟩
      simp only [map_mul]
      rw [div_mul_div_comm]
  · intro hz
    exact Subring.subset_closure hz

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHorizontalComponentModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

universe u

theorem sup_span_C_ne_top_of_multiHomog {O : Type*} [CommRing O] {K : Type} [DecidableEq K]
    (ι : K → Type) {W : Ideal (MRing ι O)} (hW : IsMultiHomogIdeal W)
    (h0 : W.comap (C : O →+* MRing ι O) = ⊥) {ϖ : O} (hϖ : ¬ IsUnit ϖ) :
    W ⊔ Ideal.span {(C ϖ : MRing ι O)} ≠ ⊤ := by
  intro htop
  have h1 : (1 : MRing ι O) ∈ W ⊔ Ideal.span {(C ϖ : MRing ι O)} := htop ▸ Submodule.mem_top
  obtain ⟨w, hw, t, ht, hwt⟩ := Submodule.mem_sup.mp h1
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp ht
  have hw0 : (C (coeff 0 w) : MRing ι O) ∈ W := by
    have h := hW w hw 0
    rwa [weightedHomogeneousComponent_zero] at h
    intro v hv
    have := congrFun hv v.1
    simp [blockWeight] at this
  have hc : coeff 0 w = 0 := by
    have h : coeff 0 w ∈ W.comap (C : O →+* MRing ι O) := hw0
    rw [h0] at h
    exact h
  have h2 := congrArg (coeff 0) hwt
  rw [coeff_add, mul_comm s, coeff_C_mul, hc, zero_add, coeff_zero_one] at h2
  exact hϖ (isUnit_iff_exists_inv.mpr ⟨_, h2⟩)

theorem ringKrullDim_quotient_eq_of_minimalPrime_of_sup_ne_top {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι O)} [P.IsPrime] {f : MRing ι O} (hfP : f ∉ P)
    (hWmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    (hWϖ : W ⊔ Ideal.span {(C ϖ : MRing ι O)} ≠ ⊤) (N : ℕ)
    (hdim : ringKrullDim (MRing ι O ⧸ P) = ((N + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MRing ι O ⧸ W) = (N : WithBot ℕ∞) := by
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hfW : f ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hup := ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_add_one_le hPW hfW hfP

  have hq : W.map (Ideal.Quotient.mk P) ∈ (Ideal.span {Ideal.Quotient.mk P f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk P f} = (Ideal.span {f}).map (Ideal.Quotient.mk P) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_comm]
    exact ⟨W, hWmin, rfl⟩
  have : (W.map (Ideal.Quotient.mk P)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk P f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hk : (W.map (Ideal.Quotient.mk P)).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq

  obtain ⟨m, hm, hWm'⟩ := Ideal.exists_le_maximal _ hWϖ
  have hWm : W ≤ m := le_sup_left.trans hWm'
  have : m.IsPrime := hm.isPrime
  have hmge := le_height_of_isMaximal_of_uniformiser_mem hϖ m hm
    (hWm' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  have hdimS := ringKrullDim_mvPolynomial_dvr (σ := Σ k, ι k) O
  have hfin : FiniteRingKrullDim (MRing ι O) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top, hdimS]
    exact ⟨by rw [← WithBot.coe_natCast]; exact WithBot.coe_ne_bot, by
      rw [← WithBot.coe_natCast]
      exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))⟩
  have hmax : ∀ m' : Ideal (MRing ι O), m'.IsMaximal →
      m'.height ≤ ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := by
    intro m' hm'
    have := Ideal.height_le_ringKrullDim_of_ne_top hm'.ne_top
    rw [hdimS] at this
    exact_mod_cast this
  have hmeq : m.height = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := le_antisymm (hmax m hm) hmge

  have hcat1 := DimF.height_eq_height_add_of_isRegularRing P W hPW
  have hcat2 := DimF.height_eq_height_add_of_isRegularRing W m hWm
  have hsum : P.height + (W.map (Ideal.Quotient.mk P)).height + (m.map (Ideal.Quotient.mk W)).height
      = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := by
    rw [← hcat1, ← hcat2, hmeq]
  have hPfin : P.height ≠ ⊤ := fun h => by
    simp only [h, top_add] at hsum; exact ENat.top_ne_natCast _ hsum
  have hafin : (W.map (Ideal.Quotient.mk P)).height ≠ ⊤ := fun h => by
    simp only [h, top_add, add_top] at hsum; exact ENat.top_ne_natCast _ hsum
  have hbfin : (m.map (Ideal.Quotient.mk W)).height ≠ ⊤ := fun h => by
    simp only [h, add_top] at hsum; exact ENat.top_ne_natCast _ hsum
  obtain ⟨h0, hh0⟩ : ∃ h0 : ℕ, P.height = h0 := ⟨_, (ENat.natCast_toNat hPfin).symm⟩
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℕ, (W.map (Ideal.Quotient.mk P)).height = a0 :=
    ⟨_, (ENat.natCast_toNat hafin).symm⟩
  obtain ⟨b0, hb0⟩ : ∃ b0 : ℕ, (m.map (Ideal.Quotient.mk W)).height = b0 :=
    ⟨_, (ENat.natCast_toNat hbfin).symm⟩
  rw [hh0, ha0, hb0] at hsum
  rw [ha0] at hk
  have hsum' : h0 + a0 + b0 = Nat.card (Σ k, ι k) + 1 := by exact_mod_cast hsum
  have hk' : a0 ≤ 1 := by exact_mod_cast hk

  have hPdim := ringKrullDim_quotient_le_sub_height P (Nat.card (Σ k, ι k) + 1) h0 hmax hh0
  rw [hdim] at hPdim
  have hPdim' : N + 1 ≤ Nat.card (Σ k, ι k) + 1 - h0 := by exact_mod_cast hPdim

  have hlow := Ideal.height_le_ringKrullDim_of_ne_top
    (DimF.isPrime_map_mk (A := MRing ι O) (q := W) (M := m) hWm).ne_top
  rw [hb0] at hlow
  have hb' : N ≤ b0 := by omega
  have hlow' : ((N : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ W) :=
    le_trans (by exact_mod_cast hb') hlow
  rw [hdim] at hup
  exact withBot_eq_of_le_of_add_one_le hlow' hup

theorem HorizontalComponentModel.proof : HorizontalComponentModel.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP c x hxc hxP W hW hϖW
  have hWd : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h
    · exact absurd rfl hW
  obtain ⟨hWmin, hrel⟩ := hWd
  have hWp : W.IsPrime := hWmin.1.1
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hWh : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.proof O K ι _ W
      (SupSpanMultiHomog.proof O K ι P x c hP.multiProj.multiHomog hxc) hWmin

  have h0 : W.comap (C : O →+* MRing ι O) = ⊥ := by
    by_contra hne
    have hmx : (W.comap (C : O →+* MRing ι O)).IsMaximal :=
      haveI : (W.comap (C : O →+* MRing ι O)).IsPrime := Ideal.IsPrime.comap _
      IsPrime.to_maximal_ideal hne
    have hϖm : ϖ ∈ W.comap (C : O →+* MRing ι O) := by
      rw [IsLocalRing.eq_maximalIdeal hmx]
      exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
    exact hϖW hϖm
  have hdim := ringKrullDim_quotient_eq_of_minimalPrime_of_sup_ne_top hϖ hxP hWmin
    (sup_span_C_ne_top_of_multiHomog ι hWh h0 hϖ.not_isUnit) (d + 1 + Fintype.card K)
    (by rw [hP.dim, show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by ring])
  exact ⟨⟨hWp, hWh, hrel⟩, h0, hdim⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

