import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FinitelyManyMarkedClassesTermDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1499
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0420
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1334
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0143
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1510
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkWeightedFixedPointDefinitePairOddOfCounts
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.LKDef
open scoped TensorProduct Classical

namespace GlobalTheory.RootSumWeights

theorem exists_root_enum {F : Type} [Field F] (τ : F →+* ℂ) (n : ℕ) :
    ∃ sel : Fin n → Polynomial F → ℂ, ∀ P : Polynomial F, P.Monic → P.natDegree = n →
      (P.map τ).roots = Finset.univ.val.map fun i => sel i P := by
  have key : ∀ P : Polynomial F, ∃ g : Fin n → ℂ, P.Monic → P.natDegree = n →
      (P.map τ).roots = Finset.univ.val.map g := by
    intro P
    by_cases h : P.Monic ∧ P.natDegree = n
    · have hc : (P.map τ).roots.toList.length = n := by
        rw [Multiset.length_toList, ← (IsAlgClosed.splits (P.map τ)).natDegree_eq_card_roots,
          h.1.natDegree_map, h.2]
      obtain ⟨l, hl, hl'⟩ : ∃ l : List ℂ, l.length = n ∧ (P.map τ).roots = (l : Multiset ℂ) :=
        ⟨_, hc, (Multiset.coe_toList _).symm⟩
      subst hl
      exact ⟨l.get, fun _ _ => by rw [Fin.univ_val_map, List.ofFn_get, hl']⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose g hg using key
  exact ⟨fun i P => g P i, hg⟩

theorem markWeightedFixedPoint_definitePair_odd_of_counts : GlobalTheory.LKDef.MoveDefInv → GlobalTheory.RootSumWeights.CxCountRegMark → GlobalTheory.RootSumWeights.FinitelyManyMarkedClassesTermDegreeOne → GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd := by
  intro hmove hcount hfin p _ G ha hn v hv c L f hf hreg K' f' hf' h0
  rw [hcount p G ha v hv c L f hf hreg K' f' hf']
  obtain ⟨sel, hsel⟩ := exists_root_enum v.embedding G.n
  have hmon : ∀ x : G.C, (minpoly G.F x).Monic := fun x => minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hmem : ∀ P : Polynomial G.F, P.Monic → P.natDegree = G.n → ∀ μ : ℂ,
      P.eval₂ v.embedding μ = 0 ↔ ∃ i, sel i P = μ := by
    intro P hm hd μ
    rw [← Polynomial.eval_map, ← Polynomial.IsRoot.def, ← Polynomial.mem_roots (hm.map _).ne_zero, hsel P hm hd]
    simp
  have hIs : ∀ i, IsSel G (sel i) := by
    intro i w hw P hm hd
    have hc : Fintype.card {w : InfinitePlace G.F // sigPosH (G.gram_herm w) = 1} = 1 := ha
    obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.1 hc
    have hwv : w = v := congrArg Subtype.val ((hu ⟨w, hw⟩).trans (hu ⟨v, hv⟩).symm)
    subst hwv
    exact (hmem P hm hd _).2 ⟨i, rfl⟩
  have hF := hfin p G ha L f K' f' hf hf'

  have hL : markSumC G c L.K.toSubgroup f K' f' =
      ∑ i, markedSumIrr G (fun P => c P (sel i P)) (sel i) L.K.toSubgroup f 1 K' f' := by
    unfold markSumC markedSumIrr
    rw [← finsum_sum_comm]
    · refine finsum_congr fun q => ?_
      set P : Pair G := Quot.out q
      by_cases hm : ∃ μ, P.Mark μ
      · rw [dif_pos hm]
        by_cases hi : Irreducible P.pol
        · have hμ := hm.choose_spec
          obtain ⟨j, hj⟩ := (hmem P.pol (hmon _) P.reg.1 _).1 (mark_isRoot_pol p G P _ ha hμ v hv)
          have hnd : (Finset.univ.val.map fun i => sel i P.pol).Nodup := by
            rw [← hsel P.pol (hmon _) P.reg.1]
            exact Polynomial.nodup_roots (P.reg.2.map)
          have hinj := Multiset.inj_on_of_nodup_map hnd
          rw [Finset.sum_eq_single j]
          · rw [if_pos ⟨hi, hj ▸ hμ⟩]
            beta_reduce
            rw [hj]
          · intro i _ hij
            rw [if_neg]
            rintro ⟨-, hi'⟩
            exact hij (hinj i (Finset.mem_univ_val i) j (Finset.mem_univ_val j)
              ((Pair.mark_unique p G P _ _ ha hi' hμ).trans hj.symm))
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [h0 P hm hi, mul_zero]
          exact (Finset.sum_eq_zero fun i _ => if_neg fun h => hi h.1).symm
      · rw [dif_neg hm]
        exact (Finset.sum_eq_zero fun i _ => if_neg fun h => hm ⟨_, h.2⟩).symm
    · intro i _
      refine hF.subset fun q hq => ?_
      rw [Function.mem_support] at hq
      split_ifs at hq with h
      · exact ⟨⟨_, h.2⟩, right_ne_zero_of_mul hq⟩
      · exact absurd rfl hq

  have hD : {q : DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
    obtain ⟨e, he⟩ := cls_equiv_dcls_irr p G ha hn _ (hIs ⟨0, G.n_pos⟩)
    have h1 := (hF.preimage (f := fun q : {q : Cls G // Irreducible (Quot.out q).pol ∧
      (Quot.out q).Mark (sel ⟨0, G.n_pos⟩ (Quot.out q).pol)} => q.1) Subtype.val_injective.injOn).image
      fun q => (e q).1
    refine h1.subset fun d hd => ⟨e.symm ⟨d, hd.1⟩, ⟨⟨_, (e.symm ⟨d, hd.1⟩).2.2⟩, ?_⟩, by simp⟩
    rw [← (he _).2 L.K.toSubgroup f 1 K' f' one_pos hf.2.2.1 hf'.2.2.1, Equiv.apply_symm_apply]
    exact hd.2
  rw [hL, Finset.sum_congr rfl fun i _ =>
    hmove p G ha hn _ _ (hIs i) L.K.toSubgroup f 1 K' f' one_pos hf.2.2.1 hf'.2.2.1]
  unfold dSumIrr
  rw [← finsum_sum_comm]
  · refine finsum_congr fun q => ?_
    set Q : DPair G := Quot.out q
    by_cases hi : Irreducible Q.pol
    · simp only [if_pos hi]
      rw [← Finset.sum_mul, rootSum, hsel Q.pol (hmon _) Q.reg.1, Multiset.map_map]
      rfl
    · simp only [if_neg hi, Finset.sum_const_zero]
  · intro i _
    refine hD.subset fun q hq => ?_
    rw [Function.mem_support] at hq
    split_ifs at hq with h
    · exact ⟨h, right_ne_zero_of_mul hq⟩
    · exact absurd rfl hq

end GlobalTheory.RootSumWeights
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogSupNormLossLeLinearInWeight
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LamSize

theorem one_le_fdeg_of_cm (E : Type) [Field E] [NumberField E] [IsCMField E] : 1 ≤ fdeg E := by
  have h : Module.finrank ℚ E = 2 * fdeg E := by rw [fdeg, IsTotallyComplex.finrank E]; omega
  have := Module.finrank_pos (R := ℚ) (M := E)
  omega

theorem one_le_dE_field (E : Type) [Field E] [NumberField E] : 1 ≤ dE E := by
  unfold dE
  have h := Int.one_le_abs (NumberField.discr_ne_zero E)
  rw [← Int.cast_abs]
  exact_mod_cast h

theorem neg_log_epStar_le (f M d w : ℝ) (hf : 1 ≤ f) (hM : 1 ≤ M) (hd : 1 ≤ d) (hw : 1 ≤ w) :
    0 < epStar (2 * M * Real.sqrt d) f w 1 ∧ epStar (2 * M * Real.sqrt d) f w 1 ≤ 1 ∧
      -Real.log (epStar (2 * M * Real.sqrt d) f w 1) ≤
        Real.log 2 + Real.log M + 1 / 2 * Real.log d + Real.log f + Real.log w := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hpi := Real.pi_gt_three
  have hsd : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd
  have hfw : 1 ≤ f * w := one_le_mul_of_one_le_of_one_le hf hw
  set A := 2 * M * Real.sqrt d * f * w with hA
  have hA1 : 1 ≤ A := by
    have h1 : 1 ≤ M * Real.sqrt d := one_le_mul_of_one_le_of_one_le hM hsd
    have : A = 2 * (M * Real.sqrt d) * (f * w) := by rw [hA]; ring
    rw [this]; nlinarith
  have hA0 : 0 < A := by linarith
  have hB : 0 < 2 * M * Real.sqrt d * (f * w + 2) * 1 * Real.log 2 := by positivity
  have hlow : 1 / A ≤ epStar (2 * M * Real.sqrt d) f w 1 := by
    unfold epStar
    refine le_min ((div_le_one hA0).2 hA1) ?_
    rw [div_le_div_iff₀ hA0 hB]
    have hMd : 0 < 2 * M * Real.sqrt d := by positivity
    have key : (f * w + 2) * Real.log 2 ≤ Real.pi * (f * w) := by nlinarith
    have : 1 * (2 * M * Real.sqrt d * (f * w + 2) * 1 * Real.log 2) = (2 * M * Real.sqrt d) * ((f * w + 2) * Real.log 2) := by ring
    rw [this]
    have : Real.pi * A = (2 * M * Real.sqrt d) * (Real.pi * (f * w)) := by rw [hA]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left key hMd.le
  have he0 : 0 < epStar (2 * M * Real.sqrt d) f w 1 := lt_of_lt_of_le (by positivity) hlow
  refine ⟨he0, min_le_left _ _, ?_⟩
  have h1 : Real.log (1 / A) ≤ Real.log (epStar (2 * M * Real.sqrt d) f w 1) :=
    Real.log_le_log (by positivity) hlow
  rw [one_div, Real.log_inv] at h1
  have hlA : Real.log A = Real.log 2 + Real.log M + 1 / 2 * Real.log d + Real.log f + Real.log w := by
    rw [hA, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_sqrt (by linarith)]
    ring
  linarith

theorem log_radius_le (E : Type) [Field E] [NumberField E] [IsCMField E] (r d M : ℕ) (w L : ℝ)
    (hr : 1 ≤ r) (hd : 1 ≤ d) (hM : 1 ≤ M) (hL : 1 ≤ L) (hw : 1 ≤ w)
    (hfr : Real.log (fdeg E * r) ≤ L) (hlM : Real.log M ≤ 30 * L) (hdE : Real.log (dE E) ≤ 4 * fdeg E * L)
    (hld : Real.log d ≤ 4 * L) (hlw : Real.log w ≤ 2 * L) :
    1 ≤ 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E) (Real.sqrt (epsLev E d M w) / Real.sqrt (fdeg E)))
      (3 * frameRadius w r / 5) ∧
    Real.log (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E) (Real.sqrt (epsLev E d M w) / Real.sqrt (fdeg E)))
      (3 * frameRadius w r / 5)) ≤ (4 * fdeg E + 32) * L := by
  have hf1 := one_le_fdeg_of_cm E
  have hf' : (1 : ℝ) ≤ fdeg E := by exact_mod_cast hf1
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hdE1 := one_le_dE_field E
  obtain ⟨he0, he1, hne⟩ := neg_log_epStar_le (fdeg E) M d w hf' hM' hd' hw
  have hepsdef : epsLev E d M w = epStar (2 * M * Real.sqrt d) (fdeg E) w 1 := rfl
  rw [← hepsdef] at he0 he1 hne
  obtain ⟨hX0, hX⟩ := GlobalTheory.room_log_radius (fdeg E) r (dE E) (epsLev E d M w) w hf1 hr hdE1 he0 hw
  set X := 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E) (Real.sqrt (epsLev E d M w) / Real.sqrt (fdeg E)))
    (3 * frameRadius w r / 5) with hXdef
  clear_value X
  have hle : Real.log (epsLev E d M w) ≤ 0 := Real.log_nonpos he0.le he1
  have hn : (1 : ℝ) ≤ (fdeg E : ℝ) * r := one_le_mul_of_one_le_of_one_le hf' hr'
  have a1 : 0 ≤ Real.log (dE E) := Real.log_nonneg hdE1
  have a2 : 0 ≤ Real.log w := Real.log_nonneg hw
  have a3 : 0 ≤ Real.log (fdeg E : ℝ) := Real.log_nonneg hf'
  have a4 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
  have a5 : 0 ≤ Real.log ((fdeg E : ℝ) * r) := Real.log_nonneg hn
  have a6 : 0 ≤ Real.log (1600 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have a7 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM'
  have a8 : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd'
  have hmul : Real.log ((fdeg E : ℝ) * r) = Real.log (fdeg E : ℝ) + Real.log r :=
    Real.log_mul (by positivity) (by positivity)
  have hc : Real.log (1600 / 3 : ℝ) ≤ 7 := by
    have h1 : Real.log (1600 / 3 : ℝ) ≤ Real.log ((2 : ℝ) ^ 10) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h1
    have := Real.log_two_lt_d9
    push_cast at h1
    linarith
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hfdL : 0 ≤ (fdeg E : ℝ) * L := by positivity
  have hX1 : 0 ≤ Real.log X := by rw [hX]; linarith
  refine ⟨?_, ?_⟩
  · by_contra hc'
    have := Real.log_neg hX0 (not_le.1 hc')
    linarith
  · rw [hX]
    have : (4 * (fdeg E : ℝ) + 32) * L = 4 * ((fdeg E : ℝ) * L) + 32 * L := by ring
    rw [this]
    linarith

theorem lamSup_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r q d M : ℕ) (Om s t L : ℝ), 1 ≤ r → 1 ≤ d → 1 ≤ M → 1 ≤ L → 0 ≤ s → 0 ≤ t → Real.log (fdeg E * r) ≤ L → Real.log M ≤ 30 * L → Real.log (dE E) ≤ 4 * fdeg E * L → Real.log d ≤ 4 * L → Real.log (s + t + 1) ≤ 2 * L → lamSup E r q d M Om s t ≤ ((1 + |Om|) / 2 + L + (2 * q + 1) * (6 * fdeg E + 48) * L) * (s + t) := by
  intro E _ _ _ r q d M Om s t L hr hd hM hL hs ht hfr hlM hdE hld hlw
  have hw : (1 : ℝ) ≤ s + t + 1 := by linarith
  obtain ⟨hX1, hXle⟩ := log_radius_le E r d M (s + t + 1) L hr hd hM hL hw hfr hlM hdE hld hlw
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hcm : cmLen E r q d M (s + t + 1) = (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E)
      (Real.sqrt (epsLev E d M (s + t + 1)) / Real.sqrt (fdeg E))) (3 * frameRadius (s + t + 1) r / 5)) ^ (2 * q + 1) := rfl
  unfold lamSup
  rw [hcm]
  set X := 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E)
      (Real.sqrt (epsLev E d M (s + t + 1)) / Real.sqrt (fdeg E))) (3 * frameRadius (s + t + 1) r / 5) with hXdef
  clear_value X
  have hX0 : 0 < X := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  unfold Formalism.L2.LamCM.pDeg
  push_cast
  set K : ℝ := 2 * (q : ℝ) + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  set Y := K * Real.log X with hY
  have hY0 : 0 ≤ Y := mul_nonneg hK0 hlX
  have hYle : Y ≤ K * ((4 * fdeg E + 32) * L) := mul_le_mul_of_nonneg_left hXle hK0
  have hlr : Real.log r ≤ L := by
    have hf' : (1 : ℝ) ≤ fdeg E := by exact_mod_cast one_le_fdeg_of_cm E
    have : Real.log (r : ℝ) ≤ Real.log ((fdeg E : ℝ) * r) :=
      Real.log_le_log (by positivity) (le_mul_of_one_le_left (by positivity) hf')
    linarith
  have a4 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
  have hst : 0 ≤ s + t := by linarith
  have c1 : s * (Real.log r + Y) ≤ (s + t) * (L + Y) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) hst
  have c2 : (3 / 2 * Y) * (s + t) ≤ (K * (6 * fdeg E + 48) * L) * (s + t) := by
    refine mul_le_mul_of_nonneg_right ?_ hst
    have : K * (6 * (fdeg E : ℝ) + 48) * L = 3 / 2 * (K * ((4 * fdeg E + 32) * L)) := by ring
    rw [this]; linarith
  nlinarith

end GlobalTheory.LamSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticTransfer
section
open scoped SchwartzMap Matrix

noncomputable section

namespace GlobalTheory.ArchUniq

open GlobalTheory.RealWeil

theorem pairingCoords : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v v', GlobalTheory.RealWeil.sympl (φ v) (φ v') = -GlobalTheory.ArchUniq.omega P v v') ∧
      ∀ v (f : EuclideanSpace ℝ (Fin n) → ℂ),
        GlobalTheory.ArchUniq.schrF P v (f ∘ C) = GlobalTheory.RealWeil.rhoFun (φ v) f ∘ C := GlobalTheory.T.exists_pairing_coordinates_schrodinger_folland

theorem symplMatrix : ∀ (l : Type) [Fintype l] [DecidableEq l] (ψ : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ w w', GlobalTheory.RealWeil.sympl (ψ w) (ψ w') = GlobalTheory.RealWeil.sympl w w') →
    ∃ M : Matrix.symplecticGroup l ℝ, ∀ w, (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w = ψ w := GlobalTheory.T.exists_symplecticGroup_matrix_of_preserves_phaseSpaceForm

end GlobalTheory.ArchUniq

open scoped SchwartzMap Matrix TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq

namespace GlobalTheory.ArchUniq

end GlobalTheory.ArchUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyEquivOfJhMultNeZero
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.RegMult

theorem jhMult_cell_eq_zero_of_row {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h : ℕ} {d : Fin h → ℕ} {X : Fin h → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] {ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)}
    (hc : ∀ a, IsCuspidal (ρ a)) (b : SizeMatrix (fun a => Fin (d a)) (fun a => Fin (d a)))
    {i j j' : Fin h} (hjj : j < j') (hj : b.1 i j ≠ 0) (hj' : b.1 i j' ≠ 0)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d j))
    {Y : Type} [AddCommGroup Y] [Module ℂ Y] {τ : Representation ℂ (Levi k fun a => Fin (d a)) Y}
    (hτ : τ.IsIrreducible) : jhMult τ (cellFunctor f g (piTensor ρ)) = 0 := by
  have hne : unipRad k (f i) ≠ ⊥ := by
    rw [GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff]
    refine ⟨f i ⟨j, ⟨0, Nat.pos_of_ne_zero hj⟩⟩, f i ⟨j', ⟨0, Nat.pos_of_ne_zero hj'⟩⟩, ?_⟩
    simpa [blk_apply] using hjj
  haveI hs : Subsingleton (Jacquet (ρ i) (unipRad k (f i))) := (hc i).2 h (fun j => b.1 i j) (f i) hne
  haveI := GlobalTheory.SmGL.CellSemis.subsingleton_piTensor
    (X := fun a => Jacquet (ρ a) (unipRad k (f a))) i
  obtain ⟨φ⟩ := GlobalTheory.T.relative_jacquet_functor_piTensor_equiv k (Fin h) (Fin h) (fun a => Fin (d a)) (fun i j => Fin (b.1 i j)) f X ρ
  haveI : Subsingleton (Jacquet (piTensor ρ) (relUnip k f)) := φ.toLinearEquiv.injective.subsingleton
  exact GlobalTheory.SmGL.CellSemis.jhMult_relInd_of_subsingleton g _ hτ

end GlobalTheory.RegMult

noncomputable section

namespace GlobalTheory.RegMult

def glCast (R : Type) [CommRing R] {n m : ℕ} (h : n = m) : GL (Fin n) R ≃* GL (Fin m) R :=
  h ▸ MulEquiv.refl _

def permHom (R : Type) [CommRing R] {α : Type} (d : α → ℕ) (σ : α ≃ α) (hσ : ∀ i, d (σ i) = d i) :
    Levi R (fun a => Fin (d a)) →* Levi R (fun a => Fin (d a)) where
  toFun p i := glCast R (hσ i) (p (σ i))
  map_one' := funext fun i => map_one (glCast R (hσ i))
  map_mul' p q := funext fun i => map_mul (glCast R (hσ i)) (p (σ i)) (q (σ i))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.RegMult

end

noncomputable section

namespace GlobalTheory.RegMult

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.RegMult

end

namespace GlobalTheory.RegMult

theorem exists_perm {h : ℕ} {d : Fin h → ℕ} (hd : ∀ a, 0 < d a)
    (b : SizeMatrix (fun a => Fin (d a)) (fun a => Fin (d a)))
    (hrow : ∀ i j j', b.1 i j ≠ 0 → b.1 i j' ≠ 0 → j = j') :
    ∃ σ : Fin h ≃ Fin h, (∀ i, d (σ i) = d i) ∧ (∀ i j, j ≠ σ i → b.1 i j = 0) ∧ ∀ i, b.1 i (σ i) = d i := by
  have hr : ∀ i, ∑ j, b.1 i j = d i := fun i => by simpa using b.2.1 i
  have hc : ∀ j, ∑ i, b.1 i j = d j := fun j => by simpa using b.2.2 j
  have h1 : ∀ i, ∃ j, b.1 i j ≠ 0 := fun i => by
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero ((hr i).trans_ne (hd i).ne')
    exact ⟨j, hj⟩
  choose s hs using h1
  have hz : ∀ i j, j ≠ s i → b.1 i j = 0 := fun i j hj => by_contra fun h0 => hj (hrow i _ _ h0 (hs i))
  have hsurj : Function.Surjective s := fun j => by
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero ((hc j).trans_ne (hd j).ne')
    exact ⟨i, hrow i _ _ (hs i) hi⟩
  have hinj : Function.Injective s := Finite.injective_iff_surjective.2 hsurj
  have hb : ∀ i, b.1 i (s i) = d i := fun i => by
    rw [← hr i, Finset.sum_eq_single (s i) (fun j _ hj => hz i j hj) (by simp)]
  refine ⟨Equiv.ofBijective s ⟨hinj, hsurj⟩, fun i => ?_, hz, hb⟩
  show d (s i) = d i
  rw [← hc, Finset.sum_eq_single i (fun a _ ha => hz a _ fun e => ha (hinj e).symm) (by simp), hb]

theorem nonempty_equiv_of_jhMult_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (hσ : σ.IsIrreducible)
    (hρ : ρ.IsIrreducible) (h : jhMult σ ρ ≠ 0) : Nonempty (ρ.Equiv σ) :=
  (jhMult_ne_zero_iff.1 h).nonempty_equiv hσ hρ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

noncomputable def cellMult {h : ℕ} {d : Fin h → ℕ} (s : ∀ a, IrrRep (GL (Fin (d a)) k)) (b : Fin h → Fin h → ℕ)
    (f : ∀ i, (Σ j, Fin (b i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b i j)) ≃ Fin (d j)) : ℕ∞ :=
  jhMult (piTensor fun a => (s a).ρ) (cellFunctor (m := fun a => Fin (d a)) (m' := fun a => Fin (d a))
    f g (piTensor fun a => (s a).ρ))

end GlobalTheory.RegMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRow0OfRowsSmul
section
noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.OneMapBase

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Scale

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

theorem phi_smul (u : ℂ) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : C.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    O.phi (u • cc) f h = u * O.phi cc f h := by
  show u * cc _ * _ * _ = u * (cc _ * _ * _)
  ring

theorem equivAt_smul (u : ℂ) {cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ} (h : O.EquivAt κ cc) : O.EquivAt κ (u • cc) := by
  intro g k hk f hf
  obtain ⟨h1, h2⟩ := h g k hk f hf
  refine ⟨h1, fun x => ?_⟩
  rw [phi_smul, phi_smul, h2 x]
  ring

theorem phRat_smul (u : ℂ) {v₀ : (R.MW i (sg0 D A)).Vec} {cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ} {ph : ℂ}
    (h : O.PhRat κ v₀ cc ph) : O.PhRat κ v₀ (u • cc) (u * ph) := by
  intro x
  obtain ⟨n, a, f, hf⟩ := h x
  refine ⟨n, a, f, fun y => ?_⟩
  rw [mul_assoc, hf y, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [phi_smul]
  ring

end Scale

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m)

theorem oneMapRow0_of_rows (cc : (T.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ph : ℂ)
    (hpins : OMPins T R κ v₀ O i)
    (hequiv : (O i).EquivAt (κ i) cc)
    (hid : OneMapRow (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (Wc D i)
      (unfBC (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c')) (O i).dict (O i).mu (xiR D) (wtA (κ i))
      (actLev (O i).c' (O i).lev2) (O i).dδ (O i).Cl' (O i).w (O i).La (O i).Nc (O i).gam (O i).vol (O i).ep (O i).io
      (O i).thAd (O i).Plc D.what₂.embLL.toRatAlgHom.fieldRange
      (cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank) cc ph)
    (hrat : (O i).PhRat (κ i) (v₀ i (sg0 D A)) cc ph) :
    OneMapRow0 T R κ v₀ O i :=
  ⟨cc, ph, hequiv, ⟨hpins.1.ge, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ (O i).hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ (O i).hle _ _ hpins.2.act.1).2, hid⟩, hrat⟩

theorem oneMapRow0_of_rows_smul (cc : (T.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ph u u' : ℂ) (hu : u ≠ 0) (hu' : u' ≠ 0)
    (hpins : OMPins T R κ v₀ O i)
    (hequiv : (O i).EquivAt (κ i) (u • cc))
    (hid : OneMapRow (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (Wc D i)
      (unfBC (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c')) (O i).dict (O i).mu (xiR D) (wtA (κ i))
      (actLev (O i).c' (O i).lev2) (O i).dδ (O i).Cl' (O i).w (O i).La (O i).Nc (O i).gam (O i).vol (O i).ep (O i).io
      (O i).thAd (O i).Plc D.what₂.embLL.toRatAlgHom.fieldRange
      (cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank) cc ph)
    (hrat : (O i).PhRat (κ i) (v₀ i (sg0 D A)) (u' • cc) (u' * ph)) :
    OneMapRow0 T R κ v₀ O i := by
  have h1 := equivAt_smul (O i) (κ i) u⁻¹ hequiv
  have h2 := phRat_smul (O i) (κ i) u'⁻¹ hrat
  rw [inv_smul_smul₀ hu] at h1
  rw [inv_smul_smul₀ hu', inv_mul_cancel_left₀ hu'] at h2
  exact oneMapRow0_of_rows T R κ v₀ O i cc ph hpins h1 hid h2

end GlobalTheory.OneMapBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRationalPointTestSupportDoubleCosetsFinitStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularRationalPoint_testSupport_doubleCosets_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (finU E n)) (finPt γ) : Set (finU E n)) (globLev S K' : Set (finU E n)) | globFn S f ((Quotient.out q)⁻¹ * finPt γ * (MonoidHom.id (finU E n)) (Quotient.out q)) ≠ 0}.Finite := by
  first | exact @GlobalTheory.BCT.ClsSupp.finite_supp | exact GlobalTheory.BCT.ClsSupp.finite_supp | (intros; apply GlobalTheory.BCT.ClsSupp.finite_supp <;> assumption)
end

