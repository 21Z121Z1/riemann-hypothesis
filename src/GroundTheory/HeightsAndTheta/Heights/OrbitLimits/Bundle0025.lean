import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsAlgebraicAdjoinRangeIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixedField
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ContractMixedField

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [Fintype K] [Fintype K'] in

theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {t : MRingOver F ι} {a : K → ℕ} (ht : IsMultiHomog t a) :
    IsMultiHomog (rename v t) (Function.extend κ a 0) := by
  classical
  have ht' := (Bridge.isMultiHomog_iff t a).mpr ht
  refine (Bridge.isMultiHomog_iff _ _).mp ?_
  have e := FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent hv.2.2.1 hv.1 hv.2.1 a t
  rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same ht'] at e
  rw [e]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

omit [Fintype K] [Fintype K'] in

theorem isMultiProjPrime_imageVar {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {W : Ideal (MRingOver F ι')} (hW : IsMultiProjPrime W) : IsMultiProjPrime (imageVar F v W) := by
  classical
  have h := FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (R := F) hv.2.2.1 hv.1 hv.2.1
    (fun w hw => hv.2.2.2 w hw) ((Bridge.isMultiProjPrime_iff W).mpr hW)
  exact (Bridge.isMultiProjPrime_iff _).mp h

theorem exists_dim {V : Ideal (MRingOver F ι)} (hV : IsMultiProjPrime V) :
    ∃ D : ℕ, Fintype.card K ≤ D ∧ ringKrullDim (MRingOver F ι ⧸ V) = D := by
  classical
  have := hV.1
  have hmh := (Bridge.isMultiHomogIdeal_iff V).mpr hV.2.1
  exact FieldNumbers.PFContracted.exists_ringKrullDim_eq
    (fun T q hq => FieldNumbers.PFContracted.killBlocks_mem_of_isMultiHomogIdeal hmh T hq) hV.2.2

theorem mem_divSupp_of_ne_zero {P : Ideal (MRingOver F ι)} {s : MRingOver F ι} {W : Ideal (MRingOver F ι)}
    (h : divCycle P s W ≠ 0) : W ∈ divSupp P s := by
  classical
  by_contra hW
  apply h
  simp [divCycle, Finsupp.ofSupportFinite_coe, hW]

theorem component [DecidableEq K'] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {V' : Ideal (MRingOver F ι')} {n d₀ : ℕ} (hV' : IsProjVarF V' (n + 1))
    (hI : IsProjVarF (imageVar F v V') d₀) {t : MRingOver F ι} {a : K → ℕ} (ht : IsMultiHomog t a)
    (htV : t ∉ imageVar F v V') {W : Ideal (MRingOver F ι')} (hW : divCycle V' (rename v t) W ≠ 0) :
    IsProjVarF W n ∧ ∃ d₁ : ℕ, d₁ < d₀ ∧ IsProjVarF (imageVar F v W) d₁ := by
  classical
  have hWs := mem_divSupp_of_ne_zero hW
  have hVW : V' ≤ W := le_sup_left.trans hWs.1.1.2
  have htW : rename v t ∈ W := hWs.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hrel : FieldNumbers.relDim V' = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    NumbersDVR.relDim_eq_of_ringKrullDim V' (n + 1) hV'.2
  have hW' : NumbersDVR.divCycle V' (rename v t) W ≠ 0 := by
    rw [← NumbersDVR.VocabDivCycle.proof F K' ι' V' (rename v t) W]
    exact_mod_cast hW
  obtain ⟨hWm, hWd⟩ := FieldNumbers.DivCycleSupport.full F K' ι' V' ((Bridge.isMultiProjPrime_iff V').mpr hV'.1)
    n hrel (Function.extend κ a 0) (rename v t)
    ((Bridge.isMultiHomog_iff _ _).mpr (isMultiHomog_rename hv ht)) (fun h => htV h) W hW'
  have hWm' := (Bridge.isMultiProjPrime_iff W).mp hWm
  refine ⟨⟨hWm', NumbersDVR.Numbers.ringKrullDim_eq_of_relDim W n hWd⟩, ?_⟩
  have hIm := isMultiProjPrime_imageVar hv hWm'
  obtain ⟨D, hKD, hD⟩ := exists_dim hIm
  have hle : imageVar F v V' ≤ imageVar F v W := Ideal.comap_mono hVW
  have : (imageVar F v V').IsPrime := hI.1.1
  have hdim := Inter.krullDim_quot_add_one_le hle (show t ∈ imageVar F v W from htW) htV
  rw [hD, hI.2] at hdim
  have hD' : D + 1 ≤ d₀ + Fintype.card K := by exact_mod_cast hdim
  refine ⟨D - Fintype.card K, by omega, hIm, ?_⟩
  rw [hD, Nat.sub_add_cancel hKD]

open Classical in

theorem intNum_eq_zero [DecidableEq K'] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) :
    ∀ (n : ℕ) (V' : Ideal (MRingOver F ι')) (d₀ : ℕ) (bs : Fin n → K' → ℤ),
      IsProjVarF V' n → IsProjVarF (imageVar F v V') d₀ →
      d₀ < (∑ i, if ∃ a : K → ℤ, bs i = pullDeg κ a then 1 else 0) →
      NumbersDVR.intNum F V' bs = 0 := by
  intro n
  induction n with
  | zero =>
    intro V' d₀ bs _ _ h
    simp at h
  | succ n ih =>
    intro V' d₀ bs hV' hI hcount
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (ne_of_gt (lt_of_le_of_lt (Nat.zero_le d₀) hcount))
    obtain ⟨a, ha⟩ : ∃ a : K → ℤ, bs i = pullDeg κ a := by
      by_contra h
      exact hi (if_neg h)
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin (n + 1)), σ (Fin.last n) = i :=
      ⟨Equiv.swap i (Fin.last n), Equiv.swap_apply_right _ _⟩
    rw [← FieldNumbers.IntNumSymm.full F K' ι' V' (n + 1) bs σ]
    have hlast : (bs ∘ σ) (Fin.last n) = pullDeg κ a := by
      show bs (σ (Fin.last n)) = _
      rw [hσ, ha]
    have e : bs ∘ σ = Fin.snoc (α := fun _ => K' → ℤ) (Fin.init (bs ∘ σ)) (pullDeg κ a) := by
      rw [← hlast]
      exact (Fin.snoc_init_self _).symm

    have hsum : (∑ i, if ∃ a : K → ℤ, bs i = pullDeg κ a then 1 else 0) =
        (∑ j : Fin n, if ∃ a : K → ℤ, Fin.init (bs ∘ σ) j = pullDeg κ a then 1 else 0) + 1 := by
      rw [← Equiv.sum_comp σ (fun j => if ∃ a : K → ℤ, bs j = pullDeg κ a then 1 else 0),
        Fin.sum_univ_castSucc, hσ, if_pos ⟨a, ha⟩]
      rfl

    classical
    obtain ⟨bf, bg, f, g, hf, hg, hfI, hgI, hfg⟩ :=
      FieldNumbers.ExistsForm.full F K ι _ ((Bridge.isMultiProjPrime_iff _).mpr hI.1) a
    have hf' := (Bridge.isMultiHomog_iff f bf).mp hf
    have hg' := (Bridge.isMultiHomog_iff g bg).mp hg
    have hsec : IsRatSection V' (pullDeg κ a) (rename v f) (rename v g) := by
      refine ⟨Function.extend κ bf 0, Function.extend κ bg 0, isMultiHomog_rename hv hf',
        isMultiHomog_rename hv hg', fun h => hfI h, fun h => hgI h, fun k' => ?_⟩
      by_cases hk : ∃ k, κ k = k'
      · obtain ⟨k, rfl⟩ := hk
        simp only [ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg, hv.1.extend_apply, ← hfg]
      · simp only [ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg, Function.extend_apply' _ _ _ hk, Pi.zero_apply,
          Nat.cast_zero, sub_zero]
    have key := (NumbersDVR.IntNumIsFieldIntersection.full F K' ι').2 V' n (Fin.init (bs ∘ σ)) _ _ _ hV' hsec
    dsimp only at key
    rw [e, key]
    unfold cycEval Finsupp.sum
    refine Finset.sum_eq_zero fun W hW => ?_
    rw [Finsupp.mem_support_iff] at hW
    suffices h0 : NumbersDVR.intNum F W (Fin.init (bs ∘ σ)) = 0 by simp only [h0, mul_zero]
    have hcases : divCycle V' (rename v f) W ≠ 0 ∨ divCycle V' (rename v g) W ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hW
      simp [ratDiv, hc.1, hc.2]
    have hpair : IsProjVarF W n ∧ ∃ d₁ : ℕ, d₁ < d₀ ∧ IsProjVarF (imageVar F v W) d₁ := by
      rcases hcases with hc | hc
      · exact component hv hV' hI hf' (fun h => hfI h) hc
      · exact component hv hV' hI hg' (fun h => hgI h) hc
    obtain ⟨hWn, d₁, hd₁, hWI⟩ := hpair
    exact ih W d₁ _ hWn hWI (by omega)

end ContractMixedField

open ContractMixedField in

theorem contractMixedField : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedFieldStatement := by
  intro F _ K _ ι _ K' _ ι' _ J' hJ' κ v V' d₀ d r L N hv hV' hI hd
  classical
  rw [NumbersDVR.Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
    FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full J' hJ' V' (d + r) _ hV']
  refine intNum_eq_zero hv (d + r) V' d₀ _ hV' hI ?_
  rw [Fin.sum_univ_add]
  have h1 : ∀ j : Fin d, (if ∃ a : K → ℤ, Fin.append (fun j => pullDeg κ (L j)) N (Fin.castAdd r j) =
      pullDeg κ a then 1 else 0) = 1 := fun j => if_pos ⟨L j, by rw [Fin.append_left]⟩
  rw [Finset.sum_congr rfl fun j _ => h1 j]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArith
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem ImageArith.of_found (hBT : BlockTrdeg.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.ImageArithStatement := by
  intro K _ ι _ K' _ ι' _ κ v P' d' hK hbm hP'
  classical
  obtain ⟨-, hMP', hHor', hdim'⟩ := hP'

  have hMP : IsMultiProjPrime (imageZ v P') := by
    rw [← Bridge.isMultiProjPrime_iff] at hMP' ⊢
    exact FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (j := κ) (g := v) hbm.2.2.1 hbm.1 hbm.2.1
      (fun w hw ↦ hbm.2.2.2 w hw |>.imp fun _ h ↦ h) hMP'

  have hHor : IsHorizontal (imageZ v P') := by
    refine (Ideal.ext fun a ↦ ?_).trans hHor'
    simp only [imageZ, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C]

  have : (P').IsPrime := hMP'.1
  set A' := MRing ι' ⧸ P'
  set L := FractionRing A'
  have hinj : Function.Injective (algebraMap ℤ A') := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at ha
    have h' : a ∈ (P').comap (C : ℤ →+* MRing ι') := ha
    rw [show (P').comap (C : ℤ →+* MRing ι') = ⊥ from hHor'] at h'
    exact (Submodule.mem_bot ℤ).mp h'
  have : CharZero A' := charZero_of_injective_algebraMap hinj
  have : CharZero L := charZero_of_injective_algebraMap (IsFractionRing.injective A' L)
  set φ' : MRing ι' →+* L := (algebraMap A' L).comp (Ideal.Quotient.mk P')
  have hker' : RingHom.ker φ' = P' := by
    rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective A' L),
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  set φ : MRing ι →+* L := φ'.comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom
  have hker : RingHom.ker φ = imageZ v P' := by
    rw [← RingHom.comap_ker, hker']
    rfl

  obtain ⟨s', hs', hd'⟩ := TrdegAdjoin.ringKrullDim_quotient_ker φ'
  obtain ⟨s, hs, hd⟩ := TrdegAdjoin.ringKrullDim_quotient_ker φ
  rw [hker'] at hd'
  rw [hker] at hd
  have hφX : (Set.range fun p : Σ k, ι k ↦ φ (X p)) = Set.range fun p ↦ φ' (X (v p)) := by
    simp [φ]
  rw [hφX] at hs

  have h1 := hBT K ι K' ι' κ v P' L φ' hbm hMP' hker'
  rw [hs, hs'] at h1
  have h2 := @hBT Empty _ (fun k ↦ k.elim) (fun k ↦ k.elim) K _ ι _ (fun k ↦ k.elim) (fun p ↦ p.1.elim)
    (imageZ v P') L _ _ φ
    ⟨fun a ↦ a.elim, fun p ↦ p.1.elim, fun p ↦ p.1.elim, fun q ⟨a, _⟩ ↦ a.elim⟩ hMP hker
  rw [hφX, hs] at h2
  simp only [Fintype.card_empty, Nat.sub_zero] at h2
  have h1' : s + (Fintype.card K' - Fintype.card K) ≤ s' := by exact_mod_cast h1
  have h2' : Fintype.card K ≤ s := by
    have := le_trans (self_le_add_left _ _) h2
    exact_mod_cast this
  have hKK : Fintype.card K ≤ Fintype.card K' := Fintype.card_le_of_injective κ hbm.1
  rw [hdim'] at hd'
  have h3 : d' + Fintype.card K' = s' + 1 := by exact_mod_cast hd'
  refine ⟨s + 1 - Fintype.card K, by omega, hK, hMP, hHor, ?_⟩
  rw [hd]
  have : s + 1 - Fintype.card K + Fintype.card K = s + 1 := by omega
  rw [this]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LogRegLineTensor
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem log_regLine_tensor {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι)
    (s : MRing ι) {ε : ℝ} (hε : 0 < ε) {a : K → ℕ} (ha : ∀ k, A.a k = a k) (hs : IsMultiHomog s a)
    (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (((regLine A s ε ha hs).tensor A).h z) =
      Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2 := by
  have hh : 0 < A.h z := A.pos z hz
  have hreg : Real.log ((regLine A s ε ha hs).h z) = regLog A s ε z := congrFun (log_regLine A s ε ha hs) z
  have hpos : 0 < (regLine A s ε ha hs).h z := (regLine A s ε ha hs).pos z hz
  show Real.log ((regLine A s ε ha hs).h z * A.h z) = _
  rw [Real.log_mul hpos.ne' hh.ne', hreg]
  unfold regLog normSq
  set x := ‖eval z (map (Int.castRingHom ℂ) s)‖
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hnum : 0 < x ^ 2 + ε * A.h z ^ 2 := by positivity
  have hq : (x / A.h z) ^ 2 + ε = (x ^ 2 + ε * A.h z ^ 2) / A.h z ^ 2 := by
    field_simp
  rw [hq, Real.log_div hnum.ne' (pow_pos hh 2).ne', Real.log_pow]
  push_cast
  ring

theorem PoincareLelongLimit.proof (hInt : PtsIntegrableStatement) (hLel : LelongSectionLimit.Statement) :
    PoincareLelongLimit.Statement := by
  intro K _ ι _ P n L A B s hP hL hA hB hBa hs
  obtain ⟨a, ha, hsa, -⟩ := id hs
  have hAdd := Inter.PtsAddFirst.proof hInt
  have key : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) (fun z => Real.log (B.h z)) -
        ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (fun z => Real.log (B.h z)) =
      ptsIntegral P (Fin.cons (regLog A s ε) (pot L)) (fun z => Real.log (B.h z)) := by
    intro ε hε
    have h1 := Inter.ptsIntegral_add_first_log hAdd (Q := P) (e := n) (L := L)
      (M := regLine A s ε ha hsa) (N := A) (D := B) hP hL (isSmoothHerm_regLine hA hε ha hsa) hA hB hBa
    rw [log_regLine] at h1
    have h2 : ptsIntegral P (Fin.cons (fun z => Real.log (((regLine A s ε ha hsa).tensor A).h z)) (pot L))
          (fun z => Real.log (B.h z)) =
        ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) (fun z => Real.log (B.h z)) := by
      refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun j => ?_) (fun _ _ => rfl)
      refine Fin.cases ?_ (fun i => ?_) j
      · intro z hz
        simp only [Fin.cons_zero]
        exact log_regLine_tensor A s hε ha hsa z hz.1
      · intro z _
        simp only [Fin.cons_succ]
    rw [← h2, h1]
    ring
  exact ((hLel K ι P n L A B s hP hL hA hB hBa hs).sub_const _).congr'
    (eventually_nhdsWithin_of_forall key)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PAmpleCountAlongMultiples
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

theorem charZero_of_isArithVar_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    simp only [mConeMap, map_natCast]
    rw [← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [h.2.2.1] at hmem
  exact_mod_cast (Ideal.mem_bot).1 hmem

theorem AmpleCountAlongMultiples.proofAmple (hL : LiftModel.Statement) (hC : LiftCountAlongMultiples.Statement) :
    AmpleCountAlongMultiples.StatementAmple := by
  intro K _ _ ι _ _ Ω _ y D N P0 II hD hII har hb hP0 hs hcj hgen hc hfib ε hε
  have : CharZero Ω := charZero_of_isArithVar_mCoordIdeal har
  obtain ⟨a, ι', _, x', ha, hmem, hgo, hbir⟩ := hL K ι Ω y D N.a har hb hgen hc hfib
  refine ⟨a, ha, ?_⟩
  have hapos : (0 : ℝ) < (a : ℝ) ^ (D + 1) := pow_pos (by exact_mod_cast ha) _
  filter_upwards [hC K ι Ω y D N P0 II a ι' x' hD hII har hb hP0 hs hcj ha hmem hgo hbir
    (ε * (a : ℝ) ^ (D + 1)) (mul_pos hε hapos)] with k hk
  have key : (II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε) *
        (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =
      ((a : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε * (a : ℝ) ^ (D + 1)) *
        ((k : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
    push_cast
    ring
  rw [key]
  exact hk

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorCompare
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsSectionOn ptsIntegral pot segre divSupp IsHorizontal
  multAt divSupp_finite divSuppArith)
open GroundTheory.Heights₂.Heights (varInt localMult IsDegZeroSmooth segreChartSet segreChartComponents chartLift
  SegreChartIntegral.Statement)

theorem segreChartSet_mono {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)}
    (h : P ≤ W) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    segreChartSet W σ i ⊆ segreChartSet P σ i := by
  rintro _ ⟨z, ⟨hz1, hz2⟩, hzi, rfl⟩
  exact ⟨z, ⟨hz1, fun f hf => hz2 f (h hf)⟩, hzi, rfl⟩

theorem ptsIntegral_eq_sum_chart (hInt : SegreChartIntegral.Statement) (hPts : SegreChartIntegralPoints.Statement)
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)} {n m : ℕ}
    {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k} {L : Fin n → HermLine ι} {g : ((Σ k, ι k) → ℂ) → ℝ} {δ : ℝ}
    {G : (Fin m → ℂ) → ℝ} {Φ : Fin n → (Fin m → ℂ) → ℝ} (hW : IsArithVar W (n + 1)) (hPW : P ≤ W)
    (hL : ∀ j, IsSmoothHerm (L j)) (hg : IsDegZeroSmooth g) (hδ : 0 < δ)
    (hsupp : ∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0)
    (hgerm : ∀ x ∈ segreChartSet P σ i,
      G =ᶠ[𝓝 x] g ∘ chartLift σ i ∧ ∀ j, Φ j =ᶠ[𝓝 x] pot L j ∘ chartLift σ i) :
    ptsIntegral W (pot L) g = ∑ W' ∈ segreChartComponents W σ i, varInt W' n G Φ := by
  have hsub := segreChartSet_mono hPW σ i
  cases n with
  | zero => exact hPts K ι W m σ i L g δ G Φ hW hg hδ hsupp fun x hx => (hgerm x (hsub hx)).1
  | succ e => exact hInt K ι W e m σ i L g δ G Φ hW hL hg hδ (Or.inl hsupp) fun x hx => hgerm x (hsub hx)

theorem ChartDivisorCompare.proof (hInt : SegreChartIntegral.Statement) (hPts : SegreChartIntegralPoints.Statement)
    (hComp : ChartDivisorComponents.Statement) (hLen : ChartDivisorLength.Statement) :
    ChartDivisorCompare.Statement := by
  classical
  intro K _ _ ι _ P n m σ i L A s g δ G Φ hP hL hs hg hδ hsupp hgerm
  obtain ⟨hmin, hdisj⟩ := hComp K ι P n m σ i A s hP hs
  have hfin : {W | W ∈ divSupp P s ∧ IsHorizontal W}.Finite := (divSupp_finite P s).subset fun _ h => h.1
  set S := hfin.toFinset with hS
  set T := S.biUnion fun W => segreChartComponents W σ i with hT
  have hA : ∀ J ∈ segreChartComponents P σ i,
      ∑ᶠ (W' : Ideal (MvPolynomial (Fin m) ℂ)) (_ : W' ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {chartSection σ i s}) W' : ℝ) * varInt W' n G Φ =
        ∑ W' ∈ T, if J ≤ W' then
          (localMult (J ⊔ Ideal.span {chartSection σ i s}) W' : ℝ) * varInt W' n G Φ else 0 := by
    intro J hJ
    have hset : (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes = ↑(T.filter fun W' => J ≤ W') := by
      ext W'
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, hmin J hJ W', hT, hS, Finset.mem_biUnion,
        Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      tauto
    rw [hset, finsum_mem_coe_finset, Finset.sum_filter]
  have hB : ∀ W ∈ S, ∀ W' ∈ segreChartComponents W σ i,
      ∑ J ∈ segreChartComponents P σ i, (if J ≤ W' then
          (localMult (J ⊔ Ideal.span {chartSection σ i s}) W' : ℝ) * varInt W' n G Φ else 0) =
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * varInt W' n G Φ := by
    intro W hW W' hW'
    rw [Set.Finite.mem_toFinset] at hW
    rw [← Finset.sum_filter, ← Finset.sum_mul, ← Nat.cast_sum, hLen K ι P n m σ i A s hP hs W hW.1 hW.2 W' hW']
  have hdisjT : (↑S : Set (Ideal (MRing ι))).PairwiseDisjoint fun W => segreChartComponents W σ i := by
    intro W₁ h₁ W₂ h₂ hne
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at h₁ h₂
    exact Finset.disjoint_left.2 fun W' hW₁ hW₂ => hne (hdisj W₁ W₂ h₁ h₂ W' hW₁ hW₂)
  rw [Finset.sum_congr rfl hA, Finset.sum_comm, Finset.sum_biUnion hdisjT,
    Finset.sum_congr rfl fun W hW => Finset.sum_congr rfl (hB W hW), eq_comm]
  refine (finsum_mem_eq_finite_toFinset_sum
    (fun W => (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) g) hfin).trans ?_
  refine Finset.sum_congr rfl fun W hW => ?_
  rw [← Finset.mul_sum]
  rw [Set.Finite.mem_toFinset] at hW
  have hWv : IsArithVar W (n + 1) := (divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2
  rw [ptsIntegral_eq_sum_chart hInt hPts hWv (le_sup_left.trans hW.1.1.1.2) hL hg hδ hsupp hgerm]

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartConeLength
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal PBlk fsLine Xc)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartComponents localMult)

def ChartConeLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (A : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s →
      ∀ W, W ∈ divSupp P s → IsHorizontal W → ∀ W' ∈ segreChartComponents W σ i,
        ∀ W'' ∈ (W.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
          W''.map (chartSubst σ i : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ) ≤ W' →
            localMult (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}) W' =
              localMult ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))) W''

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSheetLift
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre IsSheet PBlk)

def SheetLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ)
    (h : (Fin e → ℂ) → ((k : K) → ι k) → ℂ),
    IsMultiHomogIdeal P →
    (∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ h y' ∧ (∃ z ∈ mcPts P, segre z = h y') ∧ Ψ (h y') = Fin.cons 1 y') →
      ∃ γ, IsSheet P Ψ y (h y) γ

end GroundTheory.Heights₂.Heights
end
end

