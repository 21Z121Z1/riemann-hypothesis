import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0035
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ResidualContraction.proof (hle : BlowUpOrderLe.Statement.{u})
    (hcomp : ResidualContractionComponent.Statement.{u}) :
    ResidualContraction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
    x hxP
  have hGmin := hcomp O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'

  have hG'supp : G' ∈ (blowUpOf P (blowUpGens s g f m e) ⊔ Ideal.span {liftForm s}).minimalPrimes ∧
      IsRelevant G' := by
    by_contra h; unfold divCycle at hsG'; rw [dif_neg h] at hsG'; exact lt_irrefl _ hsG'

  have hsP' : liftForm (J := BlowUpIdx ι) s ∉ blowUpOf P (blowUpGens s g f m e) := by
    rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hsP
  exact hle O K ι (BlowUpIdx ι) P hP.multiProj.isPrime (blowUpGens s g f m e) G' (liftForm s) hsP'
    hG'supp.1 hG'supp.2 s hsP hGmin x hxP

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

theorem BlowUpHorizontalLift.full : BlowUpHorizontalLift.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime
  obtain ⟨hWp, hPW, hrelW⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  have hWmin : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  have hxW : x ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  obtain ⟨j₀, hj₀⟩ := hloc W hWp hPW hrelW hϖW
  choose v w hvW hvw using hj₀

  have hu₀ : u j₀ ∉ P := by
    intro h0
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have h2 := P.add_mem (hvw j) (P.mul_mem_left (w j) h0)
      rwa [sub_add_cancel] at h2
    rcases hPp.mem_or_mem h1 with h2 | h2
    · exact hvW j (hPW h2)
    · exact hj h2

  set V : MRing ι O := ∏ j, v j with hV
  set a : J → MRing ι O := fun j => w j * ∏ i ∈ Finset.univ.erase j, v i with ha_def
  have hVW : V ∉ W := by
    intro h
    obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hvW j hj
  have ha : ∀ j, V * u j - u j₀ * a j ∈ P := by
    intro j
    have e : V * u j - u j₀ * a j = (∏ i ∈ Finset.univ.erase j, v i) * (v j * u j - w j * u j₀) := by
      simp only [hV, ha_def]
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]
      ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hVa : V - a j₀ ∈ P := by
    have h1 : (V - a j₀) * u j₀ ∈ P := by
      have h2 := ha j₀
      rwa [show V * u j₀ - u j₀ * a j₀ = (V - a j₀) * u j₀ by ring] at h2
    exact (hPp.mem_or_mem h1).resolve_right hu₀
  have haW : a j₀ ∉ W := fun h => hVW (by simpa using W.add_mem (hPW hVa) h)

  set Wt : Ideal (MRing (extIdx ι J) O) :=
    (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) W).comap
      (aeval (R := O) (chartSubst a)) with hWt
  have hWtp : Wt.IsPrime := Ideal.comap_isPrime _ _
  have hcomap : ∀ s, liftForm (J := J) s ∈ Wt ↔ s ∈ W := by
    intro s
    rw [hWt, Ideal.mem_comap, aeval_chartSubst_liftForm]
    constructor
    · intro h
      simpa using Ideal.mem_map_C_iff.mp h 0
    · intro h
      exact Ideal.mem_map_of_mem _ h
  have hBWt : blowUpOf P u ≤ Wt := fun F hF =>
    Ideal.map_mono hPW (aeval_chartSubst_mem_of_mem_blowUpOf hPp hu₀ ha hF)
  have hxWt : liftForm x ∈ Wt := (hcomap x).2 hxW
  have hrelWt : IsRelevant Wt := by
    rintro (_ | k)
    · refine ⟨j₀, fun h => haW ?_⟩
      rw [hWt, Ideal.mem_comap] at h
      simp only [aeval_X, chartSubst] at h
      simpa using Ideal.mem_map_C_iff.mp h 1
    · obtain ⟨i, hi⟩ := hrelW k
      refine ⟨i, fun h => hi ((hcomap _).1 ?_)⟩
      rw [liftForm_X]
      exact h

  have hmin : Wt ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    refine ⟨⟨hWtp, sup_le hBWt ((Ideal.span_singleton_le_iff_mem _).mpr hxWt)⟩, fun Q hQ hQWt => ?_⟩
    have hQp := hQ.1
    have hBQ : blowUpOf P u ≤ Q := le_sup_left.trans hQ.2
    have hxQ : liftForm x ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hle : Q.comap (liftForm (J := J)) ≤ W := fun s hs => (hcomap s).1 (hQWt hs)
    have hQ₀ : Q.comap (liftForm (J := J)) = W :=
      le_antisymm hle (hWmin.2 ⟨Ideal.comap_isPrime _ _,
        sup_le (fun p hp => hBQ (liftForm_mem_blowUpOf hp))
          ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)⟩ hle)
    intro F hF
    refine mem_of_aeval_chartSubst_mem hQp hQ₀.ge j₀ (fun h => haW ?_) (fun j => hBQ ?_) hF
    · rw [← hQ₀]
      exact h
    · apply mem_blowUpOf_of_sub
      have e : u j * a j₀ - u j₀ * a j = (V * u j - u j₀ * a j) - u j * (V - a j₀) := by ring
      rw [e]
      exact P.sub_mem (ha j) (P.mul_mem_left _ hVa)
  refine ⟨Wt, ?_, fun h => hϖW ((hcomap _).1 (by rw [liftForm_C]; exact h)), ?_⟩
  ·
    unfold divCycle
    rw [dif_pos ⟨hmin, hrelWt⟩]
    have hne := length_localizedQuot_ne_top (blowUpOf P u ⊔ Ideal.span {liftForm x}) Wt hmin
    have hnz : multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) Wt ≠ 0 := by
      unfold multAt
      rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
      intro hs
      obtain ⟨r, hr, hr0⟩ := hs (Ideal.Quotient.mk _ 1)
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
        Ideal.Quotient.eq_zero_iff_mem] at hr0
      exact hr (hmin.1.2 hr0)
    have htn : (multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) Wt).toNat ≠ 0 :=
      fun h0 => (ENat.toNat_eq_zero.mp h0).elim hnz hne
    exact_mod_cast htn
  · ext s
    rw [Ideal.mem_comap]
    exact hcomap s

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalMinimal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

theorem BlowUpHorizontalMinimal.full : BlowUpHorizontalMinimal.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  obtain ⟨hWp, hBW, hWrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  set W₀ := W.comap (liftForm (ι := ι) (J := J) (R := O)) with hW₀
  obtain ⟨hW₀p, hPW₀, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hWrel
  have hϖW₀ : (C ϖ : MRing ι O) ∉ W₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖW
  obtain ⟨j₀, hj₀⟩ := hloc W₀ hW₀p hPW₀ hrel₀ hϖW₀
  choose v w hv hvw using hj₀

  have huj₀ : u j₀ ∉ P := by
    intro h
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have := P.add_mem (hvw j) (P.mul_mem_left (w j) h)
      rwa [sub_add_cancel] at this
    exact hj ((hPp.mem_or_mem h1).resolve_left fun h' => hv j (hPW₀ h'))

  obtain ⟨u₀, a, hu₀W, hrelP⟩ : ∃ (u₀ : MRing ι O) (a : J → MRing ι O), u₀ ∉ W₀ ∧
      ∀ j, u₀ * u j - u j₀ * a j ∈ P := by
    have := hW₀p
    refine ⟨∏ j, v j, fun j => w j * ∏ j' ∈ Finset.univ.erase j, v j',
      fun h => W₀.primeCompl.prod_mem (fun j _ => hv j) h, fun j => ?_⟩
    have e : (∏ j, v j) * u j - u j₀ * (w j * ∏ j' ∈ Finset.univ.erase j, v j') =
        (∏ j' ∈ Finset.univ.erase j, v j') * (v j * u j - w j * u j₀) := by
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]; ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hu₀P : u₀ ∉ P := fun h => hu₀W (hPW₀ h)
  have ha₀ : a j₀ ∉ W₀ := by
    intro h
    have h1 : u j₀ * (u₀ - a j₀) ∈ P := by
      have := hrelP j₀
      rwa [show u₀ * u j₀ - u j₀ * a j₀ = u j₀ * (u₀ - a j₀) by ring] at this
    have h2 : u₀ - a j₀ ∈ W₀ := hPW₀ ((hPp.mem_or_mem h1).resolve_left huj₀)
    exact hu₀W (by simpa using W₀.add_mem h2 h)

  have hrelB : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u := by
    intro j
    apply mem_blowUpOf_of_sub
    have e : u₀ * (u j * a j₀ - u j₀ * a j) =
        a j₀ * (u₀ * u j - u j₀ * a j) - a j * (u₀ * u j₀ - u j₀ * a j₀) := by ring
    have h1 : u₀ * (u j * a j₀ - u j₀ * a j) ∈ P := by
      rw [e]; exact P.sub_mem (P.mul_mem_left _ (hrelP j)) (P.mul_mem_left _ (hrelP j₀))
    exact (hPp.mem_or_mem h1).resolve_left hu₀P

  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine ⟨⟨hW₀p, sup_le hPW₀ ((Ideal.span_singleton_le_iff_mem _).mpr hxW)⟩, fun P' hP' hP'W₀ => ?_⟩
  have := hP'.1
  have hxP' : x ∈ P' := hP'.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))

  let Q' := (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P').comap
    (aeval (R := O) (chartSubst a))
  have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hBQ' : blowUpOf P u ⊔ Ideal.span {liftForm x} ≤ Q' := by
    refine sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact Ideal.map_mono (le_sup_left.trans hP'.2)
        (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
    · rw [Ideal.mem_comap, aeval_chartSubst_liftForm]
      exact Ideal.mem_map_of_mem _ hxP'
  have hQ'W : Q' ≤ W := fun G hG =>
    mem_of_aeval_chartSubst_mem hWp hP'W₀ j₀ ha₀ (fun j => hBW (hrelB j)) hG

  have hWQ' : W ≤ Q' := hmin.2 ⟨hQ'p, hBQ'⟩ hQ'W
  intro p hp
  have h5 : Polynomial.C p ∈ Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P' := by
    rw [← aeval_chartSubst_liftForm a p]
    exact hWQ' hp
  simpa using Ideal.mem_map_C_iff.mp h5 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpHorizontalSat
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Saturation

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem exists_pow_mul_mem_of_aeval_chartSubst_mem {P : Ideal (MRing ι R)} {u a : J → MRing ι R}
    {W : Ideal (MRing ι R)} (j₀ : J)
    (hrel : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u)
    {F : MRing (extIdx ι J) R}
    (hF : aeval (chartSubst a) F ∈ Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) W) :
    ∃ n : ℕ, liftForm (a j₀ ^ n) * F ∈
      blowUpOf P u ⊔ Ideal.map (liftForm (J := J) : MRing ι R →ₐ[R] MRing (extIdx ι J) R) W := by
  set B' := blowUpOf P u ⊔ Ideal.map (liftForm (J := J) : MRing ι R →ₐ[R] MRing (extIdx ι J) R) W
  let π := Ideal.Quotient.mk B'
  let x₀ := π (liftForm (a j₀))
  let L := Localization.Away x₀
  let q : MRing (extIdx ι J) R →+* L := (algebraMap _ L).comp π
  let t : L := IsLocalization.Away.invSelf x₀
  have hinv : q (liftForm (a j₀)) * t = 1 := IsLocalization.Away.mul_invSelf x₀
  let ψ : Polynomial (MRing ι R) →+* L :=
    Polynomial.eval₂RingHom (q.comp (liftForm (J := J) : MRing ι R →ₐ[R] _).toRingHom) (q (newVar j₀) * t)
  have key : ψ.comp (aeval (R := R) (chartSubst a)).toRingHom = q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ]
    · rintro ⟨_ | k, i⟩
      · change J at i
        have hm : π (newVar i * liftForm (a j₀) - newVar j₀ * liftForm (a i)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (hrel i))
        have h1 : q (newVar i * liftForm (a j₀) - newVar j₀ * liftForm (a i)) = 0 := by
          show algebraMap _ L (π _) = 0
          rw [hm, map_zero]
        rw [map_sub, map_mul, map_mul, sub_eq_zero] at h1
        simp only [ψ, chartSubst, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
        change q (liftForm (a i)) * (q (newVar j₀) * t) = q (newVar i)
        linear_combination (-t) * h1 + q (newVar i) * hinv
      · simp [ψ, chartSubst, liftForm]
  have hle : Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) W ≤ RingHom.ker ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simp only [ψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, q]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hp)), map_zero]
  have h2 := RingHom.mem_ker.mp (hle hF)
  have h3 := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h3
  rw [h3] at h2
  obtain ⟨⟨m, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers x₀) L (π F)).mp h2
  refine ⟨n, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_pow]
  exact hm

end Saturation

theorem BlowUpHorizontalSat.full : BlowUpHorizontalSat.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW F
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  obtain ⟨hWp, hBW, hWrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  set W₀ := W.comap (liftForm (ι := ι) (J := J) (R := O)) with hW₀
  obtain ⟨hW₀p, hPW₀, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hWrel
  have hϖW₀ : (C ϖ : MRing ι O) ∉ W₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖW
  obtain ⟨j₀, hj₀⟩ := hloc W₀ hW₀p hPW₀ hrel₀ hϖW₀
  choose v w hv hvw using hj₀

  have huj₀ : u j₀ ∉ P := by
    intro h
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have := P.add_mem (hvw j) (P.mul_mem_left (w j) h)
      rwa [sub_add_cancel] at this
    exact hj ((hPp.mem_or_mem h1).resolve_left fun h' => hv j (hPW₀ h'))

  obtain ⟨u₀, a, hu₀W, hrelP⟩ : ∃ (u₀ : MRing ι O) (a : J → MRing ι O), u₀ ∉ W₀ ∧
      ∀ j, u₀ * u j - u j₀ * a j ∈ P := by
    have := hW₀p
    refine ⟨∏ j, v j, fun j => w j * ∏ j' ∈ Finset.univ.erase j, v j',
      fun h => W₀.primeCompl.prod_mem (fun j _ => hv j) h, fun j => ?_⟩
    have e : (∏ j, v j) * u j - u j₀ * (w j * ∏ j' ∈ Finset.univ.erase j, v j') =
        (∏ j' ∈ Finset.univ.erase j, v j') * (v j * u j - w j * u j₀) := by
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]; ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hu₀P : u₀ ∉ P := fun h => hu₀W (hPW₀ h)
  have ha₀ : a j₀ ∉ W₀ := by
    intro h
    have h1 : u j₀ * (u₀ - a j₀) ∈ P := by
      have := hrelP j₀
      rwa [show u₀ * u j₀ - u j₀ * a j₀ = u j₀ * (u₀ - a j₀) by ring] at this
    have h2 : u₀ - a j₀ ∈ W₀ := hPW₀ ((hPp.mem_or_mem h1).resolve_left huj₀)
    exact hu₀W (by simpa using W₀.add_mem h2 h)

  have hrelB : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u := by
    intro j
    apply mem_blowUpOf_of_sub
    have e : u₀ * (u j * a j₀ - u j₀ * a j) =
        a j₀ * (u₀ * u j - u j₀ * a j) - a j * (u₀ * u j₀ - u j₀ * a j₀) := by ring
    have h1 : u₀ * (u j * a j₀ - u j₀ * a j) ∈ P := by
      rw [e]; exact P.sub_mem (P.mul_mem_left _ (hrelP j)) (P.mul_mem_left _ (hrelP j₀))
    exact (hPp.mem_or_mem h1).resolve_left hu₀P

  have := hW₀p
  let Q' := (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) W₀).comap
    (aeval (R := O) (chartSubst a))
  have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hBQ' : blowUpOf P u ⊔ Ideal.span {liftForm x} ≤ Q' := by
    refine sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact Ideal.map_mono hPW₀ (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
    · rw [Ideal.mem_comap, aeval_chartSubst_liftForm]
      exact Ideal.mem_map_of_mem _ hxW
  have hQ'W : Q' ≤ W := fun G hG =>
    mem_of_aeval_chartSubst_mem hWp le_rfl j₀ ha₀ (fun j => hBW (hrelB j)) hG
  have hWQ' : W ≤ Q' := hmin.2 ⟨hQ'p, hBQ'⟩ hQ'W
  constructor
  · intro hF
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_aeval_chartSubst_mem j₀ hrelB (hWQ' hF)
    exact ⟨a j₀ ^ m, fun h => ha₀ (hW₀p.mem_of_pow_mem _ h), hm⟩
  · rintro ⟨s, hs, hsF⟩
    have h1 : liftForm s * F ∈ W := sup_le hBW Ideal.map_comap_le hsF
    exact (hWp.mem_or_mem h1).resolve_left hs

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem GenericProjClosureModel.proof (h₁ : TwistedDualGensExist.Statement)
    (h₂ : GenericProjClosureDim.Statement) (h₃ : GenericProjClosureDivisor.Statement) :
    GenericProjClosureModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB Φ _ _ _ _ e t ht
  obtain ⟨a₁, ha₁⟩ := h₁ O Ω K ι y N E B
  obtain ⟨M, φ, hφ⟩ := ha₁ a₁ le_rfl
  obtain ⟨a₁', ha₁'⟩ := h₁ O Ω K ι y N E B'
  obtain ⟨M', φ', hφ'⟩ := ha₁' a₁' le_rfl
  have hZ := h₂ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht
  obtain ⟨f₀, g₀, hD, hfg⟩ :=
    h₃ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht hZ
  exact ⟨M, M', a₁, a₁', φ, φ', hφ, hφ', hZ, f₀, g₀, hD, hfg⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocCyclePos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem localizedModule_quot_nontrivial {R : Type u} [CommRing R] (J W : Ideal R) [W.IsPrime]
    (hJW : J ≤ W) : Nontrivial (LocalizedModule W.primeCompl (R ⧸ J)) := by
  refine ⟨⟨LocalizedModule.mk (1 : R ⧸ J) 1, 0, fun h => ?_⟩⟩
  rw [← LocalizedModule.zero_mk (1 : W.primeCompl), LocalizedModule.mk_eq] at h
  obtain ⟨v, hv⟩ := h
  have hv' : ((v : R) : R ⧸ J) = 0 := by
    simpa [Submonoid.smul_def, Algebra.smul_def] using hv
  exact v.2 (hJW (Ideal.Quotient.eq_zero_iff_mem.mp hv'))

theorem LocCyclePos.proof : LocCyclePos.Statement := by
  intro R _ _ J W hW
  have : W.IsPrime := hW.1.1
  have hfin := ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hW
  unfold ReciprocityTheory.ChartRestriction.G.AI.locLen at hfin
  have := localizedModule_quot_nontrivial J W hW.1.2
  have hpos : 0 < Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) :=
    Module.length_pos
  unfold locCycle
  rw [dif_pos hW]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  simp only at hn
  rw [← hn] at hpos ⊢
  simp only [ENat.toNat_natCast, Nat.cast_pos]
  exact_mod_cast hpos

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairBundleTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PairBundleTrdeg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
      Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O (pairProjCoord y e φ φ' t)) =
        Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + ((N + 1 : ℕ) : Cardinal)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

