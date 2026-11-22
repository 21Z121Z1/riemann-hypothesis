import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0062
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberRelabel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocPointLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem blowUpEval_ne_zero_of_not_mem {K : Type} [DecidableEq K] {ι : K → Type} {J : Type} {O : Type u}
    [CommRing O] {P : Ideal (MRing ι O)} [P.IsPrime] {u : J → MRing ι O} {F : MRing (extIdx ι J) O}
    {b : Option K → ℕ} (hF : IsMultiHomog F b) (hFb : F ∉ blowUpOf P u) :
    algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  intro h
  apply hFb
  show F ∈ RingHom.ker (aeval (blowUpSubst P u))
  rw [RingHom.mem_ker]
  show aeval (blowUpSubst P u) F = 0
  rw [aeval_blowUpSubst_of_isMultiHomog P u hF, h, map_zero, zero_mul]

theorem div_mul_div_mul_cancel_of_ne_zero {F : Type*} [Field F] (a b c w : F) (hb : b ≠ 0) :
    a / b * (b / c * w) = a / c * w := by
  rw [← mul_assoc, div_mul_div_comm, mul_comm a b, mul_div_mul_left _ _ hb]

theorem BlowUpOverLocPointLoc.proof (hfin : BlowUpOverLocFinite.Statement.{u})
    (hcen : BlowUpOverLocMaxCentre.Statement.{u}) (hinj : BlowUpLocRingInj.Statement.{u}) :
    BlowUpOverLocPointLoc.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW'p hmh hW'rel hbl hW'W
  have hBR : blowUpOverLoc P W u ≤ blowUpLocRing P u W' :=
    iInf₂_le W' ⟨hW'p, hmh, hW'rel, hbl, hW'W.le⟩
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := BlowUpLocRingIso.proof O K ι J P u W' hbl
  obtain ⟨hlocT, hunitT⟩ :=
    HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hbl
  have : IsLocalRing (blowUpLocRing P u W') := φ.isLocalRing
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hWp : W.IsPrime := hWmin.1.1
  obtain ⟨hlocA, hunitA⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof O K ι P W hWp hPW
  let 𝔫 : Ideal (blowUpOverLoc P W u) :=
    (IsLocalRing.maximalIdeal (blowUpLocRing P u W')).comap (Subring.inclusion hBR)

  have hcomapA : (𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal (homLocRing P W) ≤
        𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) := by
      rintro ⟨z, hz⟩ ha
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
      obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := (HomLocRingMem.proof O K ι P W hWp hPW z).mp hz
      have hfW : f ∈ W := by
        by_contra hfW
        exact ha ((hunitA b f g hf hg hgW hz).mpr hfW)
      have hgW' : liftForm (J := J) g ∉ W' := fun h => hgW (by rw [← hW'W]; exact h)
      have hfW' : liftForm (J := J) f ∈ W' := by rw [← hW'W] at hfW; exact hfW
      have hlf := isMultiHomog_liftForm (J := J) hf
      have hlg := isMultiHomog_liftForm (J := J) hg
      have hz' : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm f)) /
          algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm g)) ∈
          homLocRing (blowUpOf P u) W' :=
        Subring.subset_closure ⟨liftMDeg b, _, _, hlf, hlg, hgW', rfl⟩
      have hnu : ¬ IsUnit (⟨_, hz'⟩ : homLocRing (blowUpOf P u) W') :=
        fun h => (hunitT _ _ _ hlf hlg hgW' hz').mp h hfW'
      have hφz : Subring.inclusion hBR (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hz⟩) =
          φ ⟨_, hz'⟩ := by
        apply Subtype.ext
        rw [hφ _ _ _ hlf hlg hgW', blowUpEval_liftForm, blowUpEval_liftForm]
        rfl
      rw [Ideal.mem_comap, Ideal.mem_comap, hφz, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        isUnit_map_iff]
      exact hnu
    have hne : 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) ≠ ⊤ :=
      Ideal.comap_ne_top _ (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
    rw [le_antisymm (IsLocalRing.le_maximalIdeal hne) hle]
    infer_instance
  obtain ⟨hfinite, -⟩ := hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have h𝔫 : 𝔫.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔫 hcomapA
  refine ⟨hBR, 𝔫, h𝔫, ?_⟩

  obtain ⟨W₁, hW₁p, hW₁h, hW₁r, hW₁b, -, h₁, hl₁⟩ :=
    hcen O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel 𝔫 h𝔫
  let _ := (Subring.inclusion h₁).toAlgebra
  have := h𝔫.isPrime
  have hl : IsLocalization.AtPrime (blowUpLocRing P u W₁) 𝔫 := hl₁

  have hunitB : ∀ s : blowUpOverLoc P W u, s ∉ 𝔫 → IsUnit (Subring.inclusion hBR s) := by
    intro s hs
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)

  have h3 : blowUpLocRing P u W₁ ≤ blowUpLocRing P u W' := by
    intro z hz
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj 𝔫.primeCompl (⟨z, hz⟩ : blowUpLocRing P u W₁)
    obtain ⟨t, ht⟩ := (hunitB s s.2).exists_right_inv
    have e₁ : z * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) :=
      congrArg Subtype.val hbs
    have e₂ : ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * (t : FractionRing (MRing ι O ⧸ P)) = 1 := congrArg Subtype.val ht
    have hzt : z = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * t := by
      calc z = z * (((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * t) := by rw [e₂, mul_one]
        _ = (z * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P))) * t := by ring
        _ = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) * t := by rw [e₁]
    rw [hzt]
    exact (blowUpLocRing P u W').mul_mem (hBR b.2) t.2

  have hdom : ∀ (y : FractionRing (MRing ι O ⧸ P)) (hy₁ : y ∈ blowUpLocRing P u W₁) (hy' : y ∈ blowUpLocRing P u W'),
      IsUnit (⟨y, hy'⟩ : blowUpLocRing P u W') → IsUnit (⟨y, hy₁⟩ : blowUpLocRing P u W₁) := by
    intro y hy₁ hy' hyu
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj 𝔫.primeCompl (⟨y, hy₁⟩ : blowUpLocRing P u W₁)
    have e₁ : y * ((s : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) = ((b : blowUpOverLoc P W u) : FractionRing (MRing ι O ⧸ P)) :=
      congrArg Subtype.val hbs
    have hb : b ∉ 𝔫 := by
      intro hb
      have hb' : Subring.inclusion hBR b ∈ IsLocalRing.maximalIdeal (blowUpLocRing P u W') := hb
      apply (IsLocalRing.mem_maximalIdeal _).mp hb'
      have hprod : Subring.inclusion hBR b = (⟨y, hy'⟩ : blowUpLocRing P u W') * Subring.inclusion hBR s :=
        Subtype.ext e₁.symm
      rw [hprod]
      exact hyu.mul (hunitB s s.2)
    have hbu : IsUnit (algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W₁) b) :=
      IsLocalization.map_units (M := 𝔫.primeCompl) _ (⟨b, hb⟩ : 𝔫.primeCompl)
    rw [← hbs] at hbu
    exact isUnit_of_mul_isUnit_left hbu

  have h5 : blowUpLocRing P u W' ≤ blowUpLocRing P u W₁ := by
    refine Subring.closure_le.mpr ?_
    rintro z ⟨d, F, G, hF, hG, hGW', rfl⟩
    obtain ⟨i, hi⟩ := powMonomial_not_mem hW₁p hW₁r d
    have hH := isMultiHomog_powMonomial (R := O) d i
    have hσH : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) ≠ 0 :=
      blowUpEval_ne_zero_of_not_mem hH (fun h => hi (hW₁b h))
    have hσG : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) ≠ 0 := blowUpEval_ne_zero_of_not_mem hG (fun h => hGW' (hbl h))
    have hy₁ : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) ∈ blowUpLocRing P u W₁ :=
      Subring.subset_closure ⟨d, G, _, hG, hH, hi, rfl⟩
    have hFH : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) ∈ blowUpLocRing P u W₁ :=
      Subring.subset_closure ⟨d, F, _, hF, hH, hi, rfl⟩
    have hinv : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) ∈ blowUpLocRing P u W' :=
      Subring.subset_closure ⟨d, _, G, hH, hG, hGW', rfl⟩
    have hyu : IsUnit (⟨_, h3 hy₁⟩ : blowUpLocRing P u W') := by
      refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : blowUpLocRing P u W') (Subtype.ext ?_)
      show algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) * (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G)) = 1
      field_simp
    obtain ⟨v, hv⟩ := hdom _ hy₁ (h3 hy₁) hyu
    have e : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
        (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P)) = 1 := by
      have := congrArg Subtype.val v.mul_inv
      rw [hv] at this
      exact this
    have hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
        (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P)) := by
      calc algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G)
          = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) * (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
            (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P))) := by rw [e, mul_one]
        _ = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) / algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (powMonomial d i)) *
            (((v⁻¹ : (blowUpLocRing P u W₁)ˣ) : blowUpLocRing P u W₁) : FractionRing (MRing ι O ⧸ P)) :=
          div_mul_div_mul_cancel_of_ne_zero _ _ _ _ hσG
    rw [hz]
    exact (blowUpLocRing P u W₁).mul_mem hFH (Subtype.property _)
  have heq : W₁ = W' :=
    hinj O K ι J P u W₁ W' hW₁p hW₁h hW₁r hW₁b hW'p hmh hW'rel hbl (le_antisymm h3 h5)
  subst heq
  exact hl

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GenericProjClosureDivisor

noncomputable section

namespace SegreFlagCutChart

theorem exists_pow_mul_mem_of_mem_sup_map {R S F : Type*} [CommRing R] [CommRing S] [FunLike F S R]
    [RingHomClass F S R] (f : F) (A I : Ideal R) (J : Ideal S) (v : R) (hI : I ≤ A)
    (hJ : ∀ q ∈ J, ∃ n : ℕ, v ^ n * f q ∈ A) : ∀ x ∈ I ⊔ J.map f, ∃ n : ℕ, v ^ n * x ∈ A := by
  let T : Ideal R :=
    { carrier := {x | ∃ n : ℕ, v ^ n * x ∈ A}
      add_mem' := by
        rintro a b ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have h : v ^ (m + n) * (a + b) = v ^ n * (v ^ m * a) + v ^ m * (v ^ n * b) := by ring
        rw [h]
        exact A.add_mem (A.mul_mem_left _ hm) (A.mul_mem_left _ hn)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have h : v ^ n * (c • x) = c * (v ^ n * x) := by rw [smul_eq_mul]; ring
        rw [h]
        exact A.mul_mem_left _ hn }
  have hle : I ⊔ J.map f ≤ T :=
    sup_le (fun x hx => ⟨0, by simpa using hI hx⟩) (Ideal.map_le_iff_le_comap.2 fun q hq => hJ q hq)
  exact fun x hx => hle hx

end SegreFlagCutChart

open SegreFlagCutChart in

theorem SegreFlagCutChart.proof (hCS : SegreFlagCutChartSection.Statement)
    (hPre : SegreFlagCutPreimage.Statement) : SegreFlagCutChart.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk W hW hWr hPW hϖW
  classical

  choose c hc using fun j : K => hWr (some (some j))
  have nz : ∀ j, y ⟨j, c j⟩ ≠ 0 := by
    intro j h0
    refine hc j (hPW (mem_of_homog (isWeightedHomogeneous_X O _ _) ?_))
    rw [aeval_X]
    show algebraMap Ω Φ (y ⟨j, c j⟩) = 0
    rw [h0, map_zero]
  have hcne : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => nz j
  have hvW : (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ∉ W := fun hm => by
    obtain ⟨j, -, hj⟩ := hW.prod_mem_iff.mp hm
    exact hc j hj
  obtain ⟨-, dl, dm, l, μ, m, hμ, hl, hμh, hdeg, hval, hsat⟩ :=
    hCS O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk c hcne
  have hμW : μ ∉ W := by
    rw [hμ]
    intro hm
    obtain ⟨j, -, hj⟩ := hW.prod_mem_iff.mp hm
    exact hc j (hW.mem_of_pow_mem _ hj)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  ·
    refine ⟨dl, dm, l, μ, _, hl, hμh, hdeg, hμW, hvW, hval, fun _ hlW => ?_, fun h => absurd h (lt_irrefl 0)⟩
    obtain ⟨j, hj⟩ := hWr none
    have hq : (X ⟨none, j⟩ : MvPolynomial (Σ o : Option K, bundleIdx (bundleIdx ι M) M' (secondFactorBlocks o)) O) ∈
        pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t 0) := by
      refine mem_of_homog (isWeightedHomogeneous_X O _ _) ?_
      rw [aeval_X]
      show flagClosurePt y w e φ φ' t 0 ⟨none, j⟩ = 0
      simp [flagClosurePt, pairProjCoord, flagCoord]
    obtain ⟨n, hn⟩ := hsat _ hq
    have h1 := sup_le hPW ((Ideal.span_singleton_le_iff_mem W).2 hlW) hn
    rw [rename_X] at h1
    rcases hW.mem_or_mem h1 with h2 | h2
    · exact hvW (hW.mem_of_pow_mem _ h2)
    · exact hj h2
  ·
    obtain ⟨u₀, hu₀W, hu₀⟩ := hPre O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
      Φ e t ht k hk W hW hWr hPW hϖW
    refine ⟨dl, dm, l, μ, u₀ * ∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O), hl, hμh, hdeg,
      hμW, fun hm => ?_, hval, fun h => absurd h (Nat.pos_iff_ne_zero.mp hk0), fun _ q hq => ?_⟩
    · rcases hW.mem_or_mem hm with h | h
      · exact hu₀W h
      · exact hvW h
    · obtain ⟨n, hn⟩ := hu₀ q hq
      obtain ⟨m', hm'⟩ := exists_pow_mul_mem_of_mem_sup_map _ _ _ _ _ le_sup_left hsat _ hn
      refine ⟨n + m', ?_⟩
      have h : (u₀ * ∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ (n + m') * q =
          u₀ ^ m' * (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ n *
            ((∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ m' * (u₀ ^ n * q)) := by
        ring
      rw [h]
      exact Ideal.mul_mem_left _ _ hm'

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection IsProjVarF)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField assocDeg assocVar)

namespace PairNumberJoinLeft

theorem verticalComponentFibre : VerticalComponentFibre.Statement :=
  VerticalComponentFibre.proof (FibreVarieties.proof GenericFibProps.full GenericDimBound.full
    GenericDimGe.proof SpecialIdealCorresp.full SpecialIdealMultiHomog.full SupSpanMultiHomog.full
    MinimalPrimeMultiHomog.full SpecialQuotDim.full ComponentDim.proof)

theorem pairNum_fieldNum {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ)
    (hP : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d) (I : IFamily (IsLocalRing.ResidueField O) ι)
    (hI : IsFieldIntersection I) {r : ℕ} (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O)
    (hv : ∀ l, IsVertDiv O P (y l - y' l) (f l) (g l)) (G : MvPolynomial (Fin r) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I P d y y' f g G =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) P d
        y y' f g G := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hM⟩ := (BundleExamples.isModelOver_iff O P d).mp hP
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
  refine Finset.sum_congr rfl fun l _ => ?_
  have hdiv : IsVerticalDivisor P ϖ (y l - y' l) (f l) (g l) :=
    (VerticalDivisorCharacterisation.proof O K ι P ϖ _ _ _ hϖ hM.multiProj).mp (hv l)
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  refine Finsupp.sum_congr fun W hW => ?_
  have hW' : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P (f l) (g l) W ≠ 0 := Finsupp.mem_support_iff.mp hW
  have hvert : (C ϖ : MRing ι O) ∈ W := hdiv.vertical W (by rwa [← BundleExamples.ratCyc_eq])
  obtain ⟨bf, bg, hf, hg, -⟩ := hdiv.degrees
  have hor : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (f l) W ≠ 0 ∨ ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (g l) W ≠ 0 := by
    by_contra hc
    simp only [not_or, ne_eq, not_not] at hc
    apply hW'
    simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, hc.1, hc.2]
  have hVar : IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d := by
    rcases hor with h | h
    · have hs := JoinPointNumbers.mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := verticalComponentFibre O ϖ hϖ K ι P d hM (f l) bf hf hdiv.num_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
    · have hs := JoinPointNumbers.mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := verticalComponentFibre O ϖ hϖ K ι P d hM (g l) bg hg hdiv.den_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
  congr 1
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  split_ifs with h
  · exact Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI _ d _ hVar
  · rfl

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

def assocSigma (ι : K → Type) (ι' : K' → Type) (ι₂ : K₂ → Type) :
    (Σ k : (K ⊕ K') ⊕ K₂, Sum.elim (Sum.elim ι ι') ι₂ k) ≃
      (Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) where
  toFun
    | ⟨.inl (.inl k), i⟩ => ⟨.inl k, i⟩
    | ⟨.inl (.inr k), i⟩ => ⟨.inr (.inl k), i⟩
    | ⟨.inr k, i⟩ => ⟨.inr (.inr k), i⟩
  invFun
    | ⟨.inl k, i⟩ => ⟨.inl (.inl k), i⟩
    | ⟨.inr (.inl k), i⟩ => ⟨.inl (.inr k), i⟩
    | ⟨.inr (.inr k), i⟩ => ⟨.inr k, i⟩
  left_inv := by rintro ⟨(k | k) | k, i⟩ <;> rfl
  right_inv := by rintro ⟨k | k | k, i⟩ <;> rfl

theorem assocSigma_fst (v : Σ k : (K ⊕ K') ⊕ K₂, Sum.elim (Sum.elim ι ι') ι₂ k) :
    (assocSigma ι ι' ι₂ v).1 = Equiv.sumAssoc K K' K₂ v.1 := by
  obtain ⟨(k | k) | k, i⟩ := v <;> rfl

theorem assocSigma_symm_fst (v : Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) :
    ((assocSigma ι ι' ι₂).symm v).1 = (Equiv.sumAssoc K K' K₂).symm v.1 := by
  obtain ⟨k | k | k, i⟩ := v <;> rfl

theorem pointIdeal_map_rename {K₁ K₃ : Type} {κ₁ : K₁ → Type} {κ₃ : K₃ → Type} (R : Type) [CommRing R]
    {Ω : Type} [Field Ω] [Algebra R Ω] (e : K₁ ≃ K₃) (σ : (Σ k, κ₁ k) ≃ (Σ k, κ₃ k))
    (hσ : ∀ v, (σ v).1 = e v.1) (y : (Σ k, κ₁ k) → Ω) :
    (pointIdeal R y).map (rename σ) = pointIdeal R (y ∘ σ.symm) := by
  have hp : ∀ p, (σ.symm p).1 = e.symm p.1 := fun p => by
    rw [Equiv.eq_symm_apply, ← hσ, Equiv.apply_symm_apply]
  have key : (pointConeMap R y).comp (rename σ.symm) =
      ((rename e.symm).restrictScalars R).comp (pointConeMap R (y ∘ σ.symm)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap, hp]
  have hmap : (pointIdeal R y).map (rename σ) = (pointIdeal R y).comap (rename σ.symm) := by
    have h := Ideal.map_comap_of_equiv (I := pointIdeal R y) (renameEquiv R σ).toRingEquiv
    exact h
  rw [hmap]
  ext f
  rw [Ideal.mem_comap]
  unfold pointIdeal
  rw [RingHom.mem_ker, RingHom.mem_ker]
  have hf := congrArg (fun φ => φ f) key
  simp only [AlgHom.comp_apply] at hf
  change (pointConeMap R y) (rename σ.symm f) = 0 ↔ _
  rw [hf, AlgHom.restrictScalars_apply]
  exact map_eq_zero_iff _ (rename_injective _ e.symm.injective)

theorem assocDeg_comp (b : K ⊕ K' → ℤ) :
    assocDeg (K₂ := K₂) b ∘ Equiv.sumAssoc K K' K₂ = joinDeg (K' := K₂) b := by
  funext k
  rcases k with (k | k) | k <;> rfl

theorem rename_assocVar {R : Type} [CommRing R] (f : MRing (Sum.elim ι ι') R) :
    rename (assocVar ι₂) f = rename (assocSigma ι ι' ι₂) (joinForm (ι' := ι₂) f) := by
  rw [joinForm, rename_rename]
  refine congrArg (fun φ => rename φ f) ?_
  funext p
  obtain ⟨k | k, i⟩ := p <;> rfl

theorem fnField_assoc (O : Type) [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] (x : (Σ k, ι k) → Ω)
    (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (hfn : fnField O (joinCoord x (joinCoord z w)) = fnField O (joinCoord x z)) :
    fnField O (joinCoord (joinCoord x z) w) = fnField O (joinCoord x z) := by
  apply le_antisymm
  · refine Subfield.closure_le.mpr ?_
    rintro _ (⟨c, rfl⟩ | ⟨⟨(k | k) | k, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨.inl k, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨.inr k, i, j⟩, rfl⟩)
    · rw [← hfn]
      exact Subfield.subset_closure (Or.inr ⟨⟨.inr (.inr k), i, j⟩, rfl⟩)
  · refine Subfield.closure_le.mpr ?_
    rintro _ (⟨c, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨.inl k, i, j⟩, rfl⟩)

end PairNumberJoinLeft

open PairNumberJoinLeft in

theorem PairNumberJoinLeft.proof (hPull : PairNumberPullback.Statement)
    (hVert : JoinVerticalDivisorLeft.Statement) (hBir : BirationalJoin.Statement) :
    PairNumberJoinLeft.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w d hF hZ hfn I I₁ hI hI₁ n a a' f g hv H hH
  let _ := Classical.decEq K
  let _ := Classical.decEq K'
  let _ := Classical.decEq K₂
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hvZ : ∀ i, IsVertDiv O (mcIdeal O (joinCoord x (joinCoord z w)))
      (assocDeg (K₂ := K₂) (a i) - assocDeg (K₂ := K₂) (a' i))
      (rename (assocVar ι₂) (f i)) (rename (assocVar ι₂) (g i)) := by
    intro i
    have h := hVert O Ω K ι x K' ι' z K₂ ι₂ w _ _ _ (hv i)
    convert h using 1
    funext k
    rcases k with k | k | k <;> simp [assocDeg]
  rw [pairNum_fieldNum _ d hF I₁ hI₁ _ _ _ _ hv, pairNum_fieldNum _ d hZ I hI _ _ _ _ hvZ,
    BundleExamples.pairNum_eq _ d _ _ _ _ hH, BundleExamples.pairNum_eq _ d _ _ _ _ hH]
  set Gs := fun l => rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l H) with hGs
  have hσ := assocSigma_fst (ι := ι) (ι' := ι') (ι₂ := ι₂)
  have hσ' := assocSigma_symm_fst (ι := ι) (ι' := ι') (ι₂ := ι₂)
  have hPZ : (pointIdeal O (joinCoords (joinCoords x z) w)).map (rename (assocSigma ι ι' ι₂)) =
      mcIdeal O (joinCoord x (joinCoord z w)) := by
    rw [pointIdeal_map_rename O (Equiv.sumAssoc K K' K₂) _ hσ]
    change pointIdeal O _ = pointIdeal O _
    congr 1
    funext p
    obtain ⟨k | k | k, i⟩ := p <;> rfl
  have hZP : (mcIdeal O (joinCoord x (joinCoord z w))).map (rename (assocSigma ι ι' ι₂).symm) =
      pointIdeal O (joinCoords (joinCoords x z) w) := by
    rw [BundleExamples.mcIdeal_eq_pointIdeal,
      pointIdeal_map_rename O (Equiv.sumAssoc K K' K₂).symm _ hσ']
    congr 1
    funext p
    obtain ⟨(k | k) | k, i⟩ := p <;> rfl
  have hrel := (PairNumberRelabel.proof O ϖ ((K ⊕ K') ⊕ K₂) (Sum.elim (Sum.elim ι ι') ι₂)
    (K ⊕ (K' ⊕ K₂)) (Sum.elim ι (Sum.elim ι' ι₂)) (Equiv.sumAssoc K K' K₂) (assocSigma ι ι' ι₂) hσ
    (pointIdeal O (joinCoords (joinCoords x z) w))).2.2 n (fun i => assocDeg (a i))
    (fun i => assocDeg (a' i)) (fun i => joinForm (f i)) (fun i => joinForm (g i)) Gs []
  rw [hPZ] at hrel
  simp only [← rename_assocVar, assocDeg_comp, List.map_nil] at hrel
  rw [hrel]
  have hmodF : IsModelOver (pointIdeal O (joinCoords x z)) d := by
    rw [BundleExamples.joinCoords_eq]
    exact ((BundleExamples.isModelOver_iff O _ d).mp hF).2
  have hmodZ : IsModelOver (pointIdeal O (joinCoords (joinCoords x z) w)) (d + 0) := by
    rw [← hZP]
    exact (PairNumberRelabel.proof O ϖ (K ⊕ (K' ⊕ K₂)) (Sum.elim ι (Sum.elim ι' ι₂)) ((K ⊕ K') ⊕ K₂)
      (Sum.elim (Sum.elim ι ι') ι₂) (Equiv.sumAssoc K K' K₂).symm (assocSigma ι ι' ι₂).symm hσ'
      (mcIdeal O (joinCoord x (joinCoord z w)))).1 d ((BundleExamples.isModelOver_iff O _ d).mp hZ).2
  have hbir : IsBirationalJoin O (joinCoords x z) w := by
    rw [BundleExamples.joinCoords_eq]
    exact hBir O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) K₂ ι₂ w (fnField_assoc O x z w hfn)
  have hvF : ∀ i, IsVerticalDivisor (pointIdeal O (joinCoords x z)) ϖ (a i - a' i) (f i) (g i) := by
    intro i
    rw [BundleExamples.joinCoords_eq]
    exact (VerticalDivisorCharacterisation.proof O (K ⊕ K') (Sum.elim ι ι') _ ϖ _ _ _ hϖ
      ((BundleExamples.isModelOver_iff O _ d).mp hF).2.multiProj).mp (hv i)
  have hexp := dividedDifferenceExpansion.proof n (d + 1) H hH
  have key := (hPull O ϖ hϖ Ω (K ⊕ K') (Sum.elim ι ι') K₂ ι₂ (joinCoords x z) w d 0 hmodF hmodZ n a a' f g
    hvF (d + 1) H hH Gs hexp [] (by simp)).2 hbir
  rw [BundleExamples.mcIdeal_eq_pointIdeal, ← BundleExamples.joinCoords_eq]
  exact key.symm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

