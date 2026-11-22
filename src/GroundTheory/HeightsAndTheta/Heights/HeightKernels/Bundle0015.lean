import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutCaseSharp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem KRest.smallPowerSum_isHomogeneous (f r a : ℕ) (cs : RestTerms.SmallBlock) (n : ℕ) (τ : Fin f) :
    (RestTerms.smallPowerSum f r a cs n τ).IsHomogeneous n :=
  IsHomogeneous.sum _ _ _ fun i _ => by
    simpa [RestTerms.yRoot] using ((isHomogeneous_C_mul_X (R := ℚ) _ (RestTerms.yIndex f r a cs τ i)).pow n)

theorem RestCutCaseSharp.proof (h₁ : RestTerms.RestBound.Statement) (h₂ : RestCutCaseCompare.Statement)
    (h₃ : RestCutCaseDecomp.Statement) (h₄ : RestCutTermEq.Statement)
    (h₅ : RestCutPrimeEq.Statement) : RestCutCaseSharp.Statement := by
  intro f j k r a cs e hf hj hk hr ha hN hra hF hJ hlie I hI vol hvol P hP B₀ hB φ
  have hB' : 4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ := by rw [hN]; exact hB
  obtain ⟨hex0, hall0⟩ := h₁ f r a cs B₀ hf hr ha hB'
  obtain ⟨c, hcomp, hdeg⟩ := h₂ f j k r a cs e hf hr ha hN hJ I hI
  obtain ⟨⟨Q₀, hQ₀, hQ₀h⟩, hexQ⟩ := h₃ f j k r a cs e hf hN (by omega) hF hex0
  refine ⟨hexQ, fun Q hQ => ?_⟩
  have hQ' : IsPowerSumDecomposition f j k
      (restTransport f j k (r + a) e (RestTerms.restPolynomial f r a cs)) Q := by
    rw [hF]; exact hQ
  have hterm : ∀ m : ℕ, 2 ≤ m → m ≤ r + a → ∀ τ τ' : Fin f,
      I (restTransport f j k (r + a) e (RestTerms.smallPowerSum f r a cs (m - 1) τ') * Q τ m) =
        c * RestTerms.flagIntegral f (r + a)
          (RestTerms.smallPowerSum f r a cs (m - 1) τ' * Q₀ m τ) := fun m hm2 hmN τ τ' =>
    h₄ f j k (r + a) e I c hcomp _ Q₀ hQ₀ hQ₀h Q hQ' m (by omega) hmN τ _
      (KRest.smallPowerSum_isHomogeneous f r a cs (m - 1) τ')
  obtain ⟨s, ε, hε, heq⟩ := h₅ f j k r a cs e hf hj hk hN hlie I hI c Q₀ Q hQ hterm φ
  obtain ⟨hsum, hbound⟩ := hall0 Q₀ hQ₀ s ε hε P
  have hfun : (fun p : primesAbove P B₀ => restAt f j k I vol φ Q p.1) =
      fun p : primesAbove P B₀ => (vol * c) * RestTerms.restPrimeModel f r a cs Q₀ s ε p.1 :=
    funext fun p => heq vol p.1
  rw [hfun]
  refine ⟨(hsum.of_abs).mul_left _, ?_⟩
  rw [tsum_mul_left, abs_mul, abs_mul, abs_of_pos hvol, hdeg, abs_mul]
  have hn : (((f * (r * a) + 1 : ℕ)) : ℝ) = ((f * j * k : ℕ) : ℝ) + 1 := by
    rw [hra]; push_cast; ring
  rw [hn] at hbound
  have hc : 0 ≤ vol * |c| := by positivity
  calc vol * |c| * |∑' p : primesAbove P B₀, RestTerms.restPrimeModel f r a cs Q₀ s ε p.1|
      ≤ vol * |c| * (1.6 * (((f * j * k : ℕ) : ℝ) + 1) * |(RestTerms.fibreDegree f r a cs : ℝ)|) :=
        mul_le_mul_of_nonneg_left hbound hc
    _ = 1.6 * (((f * j * k : ℕ) : ℝ) + 1) * vol * (|c| * |(RestTerms.fibreDegree f r a cs : ℝ)|) := by
        ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem RestCutCompare.flagIntegral_sub_C_mul (f N : ℕ) (P Q : RestTerms.RootRing f N) (b : ℚ) :
    RestTerms.flagIntegral f N (P - C b * Q) =
      RestTerms.flagIntegral f N P - b * RestTerms.flagIntegral f N Q := by
  unfold RestTerms.flagIntegral
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_sub, coeff_C_mul]
  ring

theorem RestCutCompare.proof (h₁ : RestTerms.CoinvariantTopDegree.Statement)
    (h₂ : RestCutStairHom.Statement) (h₃ : RestCutFlagKillsIdeal.Statement)
    (h₄ : RestCutIKillsIdeal.Statement) : RestCutCompare.Statement := by
  intro f j k N e I hI hs H hH
  have hN : N = j + k := by
    have := Fintype.card_congr e
    simpa using this
  have hD : flagDim f j k = RestTerms.topDegree f N := by
    subst hN
    rfl
  rw [hD] at hH
  obtain ⟨b, hb⟩ := h₁ f N H hH
  change H - C b * restStair f N ∈ restPsumIdeal f N at hb
  have hAh : (H - C b * restStair f N).IsHomogeneous (flagDim f j k) := by
    rw [hD]
    exact hH.sub ((h₂ f N).C_mul b)
  have hflag : RestTerms.flagIntegral f N H = b * RestTerms.flagIntegral f N (restStair f N) := by
    have h := h₃ f N _ hb
    rw [RestCutCompare.flagIntegral_sub_C_mul] at h
    linarith
  have hC : restTransport f j k N e (C b) = C (b : ℝ) := by
    simp [restTransport, restRename]
  have hIH : I (restTransport f j k N e H) =
      (b : ℝ) * I (restTransport f j k N e (restStair f N)) := by
    have h := h₄ f j k N e I hI _ hb hAh
    rw [map_sub, map_mul, hC, C_mul', map_sub, map_smul, smul_eq_mul] at h
    linarith
  have hs' : (RestTerms.flagIntegral f N (restStair f N) : ℝ) ≠ 0 := by exact_mod_cast hs
  unfold restCompareConst
  rw [hIH, hflag]
  push_cast
  field_simp

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutCompareReal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace RestCutCompareReal

theorem realFlagIntegral_monomial (f N : ℕ) (α : Fin f × Fin N →₀ ℕ) (r : ℝ) :
    realFlagIntegral f N (monomial α r) =
      r * (RestTerms.flagIntegral f N (monomial α (1 : ℚ)) : ℝ) := by
  unfold realFlagIntegral RestTerms.flagIntegral
  rw [Rat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [coeff_monomial, coeff_monomial]
  split_ifs <;> push_cast <;> ring

theorem realFlagIntegral_eq_sum (f N : ℕ) (P : MvPolynomial (Fin f × Fin N) ℝ) :
    realFlagIntegral f N P =
      ∑ α ∈ P.support, realFlagIntegral f N (monomial α (coeff α P)) := by
  unfold realFlagIntegral
  conv_lhs => rw [P.as_sum]
  simp only [coeff_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem restRename_monomial (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k)
    (α : Fin f × Fin N →₀ ℕ) (r : ℝ) :
    restRename f j k N e (monomial α r) = r • restTransport f j k N e (monomial α (1 : ℚ)) := by
  have h : (monomial α r : MvPolynomial (Fin f × Fin N) ℝ) =
      r • map (algebraMap ℚ ℝ) (monomial α (1 : ℚ)) := by
    rw [map_monomial, smul_monomial, map_one, smul_eq_mul, mul_one]
  rw [h, map_smul]
  rfl

end RestCutCompareReal

open RestCutCompareReal in

theorem RestCutCompareReal.proof : RestCutCompareReal.Statement := by
  intro f j k N e I c d hI P hP
  have hmono : ∀ α ∈ P.support, I (restRename f j k N e (monomial α (coeff α P))) =
      c * realFlagIntegral f N (monomial α (coeff α P)) := by
    intro α hα
    have hdeg : (monomial α (1 : ℚ) : RestTerms.RootRing f N).IsHomogeneous d :=
      isHomogeneous_monomial 1 (by
        by_contra h
        exact mem_support_iff.mp hα (hP.coeff_eq_zero h))
    rw [restRename_monomial, map_smul, hI _ hdeg, realFlagIntegral_monomial, smul_eq_mul]
    ring
  have hL : I (restRename f j k N e P) =
      ∑ α ∈ P.support, I (restRename f j k N e (monomial α (coeff α P))) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum, map_sum]
  rw [hL, realFlagIntegral_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl hmono

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutFlagKillsIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Finset

theorem flagIntegral_sum {ι : Type*} (f N : ℕ) (s : Finset ι)
    (P : ι → RestTerms.RootRing f N) :
    RestTerms.flagIntegral f N (∑ i ∈ s, P i) = ∑ i ∈ s, RestTerms.flagIntegral f N (P i) := by
  unfold RestTerms.flagIntegral
  simp only [coeff_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem RestCutFlagKillsIdeal.proof (h₁ : RestTerms.FlagIntegralKillsPowerSums.Statement)
    (h₂ : RestCutIdealSum.Statement) : RestCutFlagKillsIdeal.Statement := by
  intro f N A hA
  obtain ⟨G, rfl⟩ := h₂ f N A hA
  rw [flagIntegral_sum]
  refine Finset.sum_eq_zero fun i _ => h₁ f N ((i.1 : ℕ) + 1) i.2 (G i) (by omega) ?_
  have := i.1.isLt
  omega

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutHomDecomp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem RestCutHomDecomp.proof : RestCutHomDecomp.Statement := by
  intro f N F Q d hF hFh hNd
  unfold RestTerms.IsPowerSumDecomposition at hF ⊢
  have h := congrArg (homogeneousComponent d) hF
  rw [homogeneousComponent_eq_self hFh] at h
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hlN : l ≤ N := (Finset.mem_Icc.mp hl).2
  have hp : (RestTerms.blockPowerSum f N l τ).IsHomogeneous l := by
    unfold RestTerms.blockPowerSum
    exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _
  rw [KRest.homogeneousComponent_mul_left hp, if_pos (hlN.trans hNd)]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutIKillsIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem rootPsum_isHomogeneous (f j k m : ℕ) (τ : Fin f) :
    (rootPsum f j k m τ).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_X_pow _ _

theorem restTransport_isHomogeneous (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k)
    {A : RestTerms.RootRing f N} {d : ℕ} (hA : A.IsHomogeneous d) :
    (restTransport f j k N e A).IsHomogeneous d := by
  show (rename (fun p : Fin f × Fin N => (p.1, e p.2)) (map (algebraMap ℚ ℝ) A)).IsHomogeneous d
  exact (hA.map _).rename_isHomogeneous

theorem RestCutIKillsIdeal.proof (h₁ : RestCutIdealSum.Statement)
    (h₂ : RestCutTransportPsum.Statement) : RestCutIKillsIdeal.Statement := by
  intro f j k N e I hI A hA hhom
  obtain ⟨G, hG⟩ := h₁ f N A hA
  have hT := restTransport_isHomogeneous f j k N e hhom
  have hC := homogeneousComponent_of_mem (m := flagDim f j k) hT
  rw [if_pos rfl] at hC
  rw [← hC]
  rw [hG, map_sum, map_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_mul, h₂, KRest.homogeneousComponent_mul_left (rootPsum_isHomogeneous f j k _ i.2)]
  split_ifs with hle
  · exact hI.kills _ _ _ (Nat.succ_le_succ (Nat.zero_le _)) hle
      (homogeneousComponent_isHomogeneous _ _)
  · exact map_zero I

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutIdealSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem restPsumIdeal_generators_eq_range (f N : ℕ) :
    {P | ∃ k τ, 1 ≤ k ∧ k ≤ N ∧ P = RestTerms.blockPowerSum f N k τ} =
      Set.range fun i : Fin N × Fin f => RestTerms.blockPowerSum f N ((i.1 : ℕ) + 1) i.2 := by
  ext P
  constructor
  · rintro ⟨k, τ, hk1, hkN, rfl⟩
    refine ⟨(⟨k - 1, by omega⟩, τ), ?_⟩
    simp only
    congr 1
    omega
  · rintro ⟨i, rfl⟩
    exact ⟨(i.1 : ℕ) + 1, i.2, by omega, by omega, rfl⟩

theorem RestCutIdealSum.proof : RestCutIdealSum.Statement := by
  intro f N A hA
  rw [restPsumIdeal, restPsumIdeal_generators_eq_range, Ideal.mem_span_range_iff_exists_fun] at hA
  obtain ⟨c, hc⟩ := hA
  exact ⟨c, by rw [← hc]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutLieFirst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace RestCutLieFirst

theorem transport_smallPowerSum (f j k m : ℕ) (τ : Fin f) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.smallPowerSum f j k .first m τ) =
      (-1) ^ m * ∑ a : Fin j, (X (τ, Sum.inl a) : RootPoly f j k) ^ m := by
  rw [Finset.mul_sum]
  simp only [RestTerms.smallPowerSum, map_sum, map_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hidx : (restFirstEquiv j k) (⟨a.val, by omega⟩ : Fin (j + k)) = Sum.inl a := by
    have : (⟨a.val, by omega⟩ : Fin (j + k)) = Fin.castAdd k a := rfl
    rw [this, restFirstEquiv, finSumFinEquiv_symm_apply_castAdd]
  simp only [RestTerms.yRoot, RestTerms.yIndex, RestTerms.SmallBlock.sign, restTransport,
    restRename, RingHom.comp_apply, map_mul, map_C, map_X, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, rename_X, rename_C, hidx]
  rw [mul_pow]
  congr 1
  simp

end RestCutLieFirst

theorem RestCutLieFirst.proof : RestCutLieFirst.Statement := by
  intro f j k _ m σ
  obtain ⟨τ, b⟩ := σ
  have hC1 : (C ((((-1 : ℚ) ^ m : ℚ) : ℝ)) : RootPoly f j k) = (-1) ^ m := by simp
  have hC2 : (C (((-1 : ℚ) : ℚ) : ℝ) : RootPoly f j k) = -1 := by simp
  have hC3 : (C ((-1 : ℝ) ^ m) : RootPoly f j k) = (-1) ^ m := by simp
  cases b with
  | false =>
    refine ⟨(-1) ^ m, 0, neg_one_pow_eq_or ℚ m, ?_⟩
    rw [RestCutLieFirst.transport_smallPowerSum, hC1]
    simp only [lieClass, map_zero, zero_mul, add_zero]
    rw [← mul_assoc, ← mul_pow]
    simp
  | true =>
    refine ⟨-1, (-1) ^ m, Or.inr rfl, ?_⟩
    rw [RestCutLieFirst.transport_smallPowerSum, hC2, hC3]
    simp only [lieClass, rootPsum, Fintype.sum_sum_type]
    ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutLieLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace RestCutLieLast

theorem transport_smallPowerSum (f j k m : ℕ) (τ : Fin f) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.smallPowerSum f k j .last m τ) =
      ∑ b : Fin k, X (τ, Sum.inr b) ^ m := by
  unfold RestTerms.smallPowerSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have he : restLastEquiv j k ⟨j + b.val, by have := b.isLt; omega⟩ = Sum.inr b := by
    have : (finCongr (Nat.add_comm k j)) ⟨j + b.val, by have := b.isLt; omega⟩ = Fin.natAdd j b :=
      Fin.ext rfl
    simp only [restLastEquiv, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_natAdd]
  simp [restTransport, restRename, RestTerms.yRoot, RestTerms.yIndex, RestTerms.SmallBlock.sign,
    he]

end RestCutLieLast

theorem RestCutLieLast.proof : RestCutLieLast.Statement := by
  intro f j k _ m σ
  obtain ⟨τ, b⟩ := σ
  cases b with
  | true =>
    refine ⟨(-1) ^ m, 0, neg_one_pow_eq_or ℚ m, ?_⟩
    rw [RestCutLieLast.transport_smallPowerSum]
    simp [lieClass]
  | false =>
    refine ⟨-1, 1, Or.inr rfl, ?_⟩
    rw [RestCutLieLast.transport_smallPowerSum]
    simp only [lieClass, rootPsum, Fintype.sum_sum_type, map_one, one_mul]
    simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutPrimeEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem RestCutPrimeEq.proof : RestCutPrimeEq.Statement := by
  intro f j k r a cs e hf hj hk hN hlie I hI c Q₀ Q hQ hterm φ
  choose εf δf hεf hlief using hlie
  refine ⟨fun p n τ => (φ p n τ).1, fun p n τ m => εf (m - 1) (φ p n τ),
    fun p n τ m => hεf _ _, ?_⟩
  intro vol p
  have hN2 : 2 ≤ j + k := by omega
  have hDm : j + k - 1 ≤ flagDim f j k := by
    have h1 : (j + k - 1) * 2 ≤ (j + k) * (j + k - 1) := by
      rw [mul_comm]; exact Nat.mul_le_mul_right _ hN2
    have h2 : j + k - 1 ≤ (j + k) * (j + k - 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 h1
    unfold flagDim
    exact h2.trans (Nat.le_mul_of_pos_left _ hf)
  have key : ∀ τ : Fin f, ∀ m ∈ Finset.Icc 2 (r + a), ∀ n : ℕ,
      ((p : ℝ) ^ ((n + 1) * m))⁻¹ * m * I (lieClass f j k (m - 1) (φ p (n + 1) τ) * Q τ m) =
        c * (((p : ℝ) ^ ((n + 1) * m))⁻¹ *
          ((εf (m - 1) (φ p (n + 1) τ) * RestTerms.restTerm f (r + a) Q₀ m τ
            (RestTerms.smallPowerSum f r a cs (m - 1) (φ p (n + 1) τ).1) : ℚ) : ℝ)) := by
    intro τ m hm n
    rw [Finset.mem_Icc] at hm
    set σ := φ p (n + 1) τ
    have hkill : I (rootPsum f j k (m - 1) σ.1 * Q τ m) = 0 := by
      refine hI.kills (m - 1) σ.1 (Q τ m) (by omega) (by omega) ?_
      have := hQ.1 τ m (by omega) (by omega)
      rwa [show flagDim f j k + 1 - m = flagDim f j k - (m - 1) by omega] at this
    have ht := hterm m hm.1 hm.2 τ σ.1
    have hI' : I (lieClass f j k (m - 1) σ * Q τ m) = (εf (m - 1) σ : ℝ) *
        (c * (RestTerms.flagIntegral f (r + a)
          (RestTerms.smallPowerSum f r a cs (m - 1) σ.1 * Q₀ m τ) : ℝ)) := by
      rw [hlief, add_mul, mul_assoc, mul_assoc, C_mul', C_mul', map_add, LinearMap.map_smul,
        LinearMap.map_smul, hkill, ht, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
    rw [hI', RestTerms.restTerm]
    push_cast
    ring
  unfold restAt RestTerms.restPrimeModel
  rw [← hN]
  have : ∀ τ : Fin f, ∑ m ∈ Finset.Icc 2 (r + a), ∑' n : ℕ,
      ((p : ℝ) ^ ((n + 1) * m))⁻¹ * m * I (lieClass f j k (m - 1) (φ p (n + 1) τ) * Q τ m) =
      c * ∑ m ∈ Finset.Icc 2 (r + a), ∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * m))⁻¹ *
          ((εf (m - 1) (φ p (n + 1) τ) * RestTerms.restTerm f (r + a) Q₀ m τ
            (RestTerms.smallPowerSum f r a cs (m - 1) (φ p (n + 1) τ).1) : ℚ) : ℝ) := by
    intro τ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [← tsum_mul_left]
    exact tsum_congr fun n => key τ m hm n
  simp_rw [this, ← Finset.mul_sum]
  ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutPsiFlag
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem RestCutPsiFlag.proof : RestCutPsiFlag.Statement := by
  intro f N
  refine ⟨fun H => ?_, fun ψ P => ?_⟩
  · unfold realFlagIntegral RestTerms.flagIntegral
    push_cast [Rat.cast_sum, Rat.cast_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [coeff_map, eq_ratCast]
    ring
  · unfold realFlagIntegral RestTerms.flagIntegral
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [KRest.coeff_psiPoly]
    have h : coeff α P * ((coeff α (RestTerms.blockVandermonde f N) *
        α.prod (fun _ e => (e.factorial : ℚ)) : ℚ) : ℝ) =
        (coeff α (RestTerms.blockVandermonde f N) *
          α.prod (fun _ e => (e.factorial : ℚ))) • coeff α P := by
      rw [Rat.smul_def, mul_comm]
    rw [h, ψ.map_smul, smul_eq_mul]
    ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutStairNonzero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem flagIntegral_sub_C_mul (f N : ℕ) (H S : RestTerms.RootRing f N) (b : ℚ) :
    RestTerms.flagIntegral f N (H - C b * S) =
      RestTerms.flagIntegral f N H - b * RestTerms.flagIntegral f N S := by
  unfold RestTerms.flagIntegral
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_sub, coeff_C_mul]
  ring

theorem RestCutStairNonzero.proof (h₁ : RestTerms.CoinvariantTopDegree.Statement)
    (h₂ : RestCutFlagKillsIdeal.Statement) : RestCutStairNonzero.Statement := by
  intro f N H hH hne hstair
  obtain ⟨b, hb⟩ := h₁ f N H hH
  have hmem : H - C b * restStair f N ∈ restPsumIdeal f N := hb
  have h0 := h₂ f N _ hmem
  rw [flagIntegral_sub_C_mul, hstair, mul_zero, sub_zero] at h0
  exact hne h0

end GroundTheory.Heights₂.Heights
end

