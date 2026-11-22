import Formalism.GaussJetBounds.Bundle0001
import Formalism.GaussJetBounds.Bundle0003
import Formalism.GaussJetBounds.GaussJetProofs.Bundle0005
import Formalism.GaussJetBounds.Bundle0002
import Formalism.GaussJetBounds.Bundle0007
import Formalism.GaussJetBounds.GaussJetProofs.Bundle0002
import Formalism.GaussJetBounds.GaussJetProofs.WeightsAddOverOrbits

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.TheoremAOneMonomialLogLoss
section
noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem ThmAJetA_of (hS : LemmaS.{u}) (hR : LemmaRA.{u, 0}) (hA : ThmAAssembly)
    (hFP : FramePure.{u}) : ThmAJetA.{u} := by
  intro K _ _ _ l d N0 N1 _ hl hl3 hd hde hpi h0 K0 hK0 ζ hζ be hbe x hx g hg0 hg U hU ε hε
    TT nu1 nu2 size hnu21 hnu1s a ha hsa spec κ hκtop hκD hspec hcap hkill
  classical
  have hodd : Odd l := hl.odd_of_ne_two (by omega)
  have hl2 : 2 ≤ l := hl.two_le
  have hlpos : 0 < l := by omega
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  obtain ⟨⟨sig, hsigD, hsigA, hFn⟩, -⟩ := lemmaFa l d hl3 hd hde
    (fun s => (Dl d TT nu1 size s : ℝ)) (fun s => Nat.cast_nonneg _)
  have hsig0 : ∀ s, 0 ≤ sig s := fun s => (hsigD.1 s).1
  have hnotop : ∀ (s : ZMod d) (k : Fin N0), (s ∈ TT ∧ k.val = 0) → spec (s, k) = none := by
    intro s k hsk
    rcases h : spec (s, k) with _ | ⟨s0, j⟩
    · rfl
    · exact absurd hsk (hspec s k s0 j h).2.2.2.1
  obtain ⟨eps, heps0, hepsT, hmain⟩ := hA l d hl3 hd hde TT nu1 nu2 size hnu21 hnu1s sig
    ⟨hsigD, hFn⟩ (ZV d N0 N1) (fun y => y.1) (frameTop TT) (fun y => spec (y.1, y.2.1))
    (fun y => κ y)
    (by
      intro i hi
      have hi' := of_decide_eq_true hi
      exact ⟨hi'.1, hnotop _ _ hi'⟩)
    (by
      intro s hs
      have hset : Finset.univ.filter (fun i : ZV d N0 N1 => i.1 = s ∧ frameTop TT i = true) =
          Finset.univ.image (fun b : Fin N1 => ((s, ⟨0, h0⟩, b) : ZV d N0 N1)) := by
        ext ⟨s', k, b⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, frameTop,
          decide_eq_true_eq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, -, hk⟩
          exact ⟨b, rfl, Fin.ext hk.symm, rfl⟩
        · rintro ⟨b', rfl, rfl, rfl⟩
          exact ⟨rfl, hs, rfl⟩
      rw [hset, Finset.sum_image (fun b _ b' _ h => by simpa using h)]
      exact_mod_cast hκtop s hs)
    (by intro s; exact_mod_cast hκD s)
    (by
      intro i s0 j h
      obtain ⟨h1, h2, h3, -, h5, h6⟩ := hspec i.1 i.2.1 s0 j h
      exact ⟨h1, h2, h3, h5, h6⟩)
    (by intro s0 j; exact_mod_cast hcap s0 j)
  have R := dualRadiiInequalities l d hl3 hd hde TT sig eps hsigA hsig0 heps0 hepsT
  obtain ⟨hS1, hS2⟩ := hS K l d hl hodd hd hde hpi K0 hK0 ζ hζ be hbe
  have hM1 : ∀ (z i : ZV d N0 N1), ‖frameM (N1 := N1) x z i‖ ≤ 1 := by
    intro z i
    unfold frameM
    split_ifs
    · exact hx _
    · simp
  have hMlt : ∀ (z i : ZV d N0 N1), frameM (N1 := N1) x z i ≠ 0 → i.1 = z.1 := by
    intro z i h
    unfold frameM at h
    split_ifs at h with h'
    · exact h'.1
    · exact absurd rfl h

  have hsmall : ∀ (i j : ZV d N0 N1) (α β : ℕ),
      ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
        (MvPowerSeries.coeff (pureMon l i j α β) (bSum (frameM (N1 := N1) x) be)) →
      i.1 ≠ j.1 ∧ i.1 + (α : ZMod d) = j.1 + (β : ZMod d) ∧ Odd (α + β) := by
    intro i j α β hnot
    apply jet_bipower hde hl2
    by_contra hnb
    apply hnot
    have hc := jet_collapse (fun y : ZV d N0 N1 => y.1) (frameM (N1 := N1) x) hM1 hMlt be
      (pureMon l i j α β)
    have hmd : (pureMon l i j α β).mapDomain (fun y : ZV d N0 N1 => y.1) =
        Finsupp.single i.1 (l ^ α) + Finsupp.single j.1 (l ^ β) := by
      simp [pureMon, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    rw [hmd] at hc
    have h2 := hS2 _ hnb
    rw [monoWtGe_iff] at h2 ⊢
    refine hc.trans (h2.trans_eq ?_)
    congr 2
    rw [asmR_dot_pureMon, dot_add, asmR_dot_single, asmR_dot_single]
    push_cast
    ring

  have key : ∀ (i j : ZV d N0 N1) (α β : ℕ), pureMon l i j α β ≤ κ →
      ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
        (MvPowerSeries.coeff (pureMon l i j α β) (bSum (frameM (N1 := N1) x) be)) →
      frameTop TT i = true → frameTop TT j = false →
      1 ≤ (l : ℝ) ^ α * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) i +
        (l : ℝ) ^ β * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) j := by
    rintro ⟨s0, k0, b⟩ ⟨s, k, b'⟩ α β hle hnot hti htj
    obtain ⟨hne, heq, hab⟩ := hsmall _ _ α β hnot
    simp only at hne heq
    have hti' : s0 ∈ TT ∧ k0.val = 0 := of_decide_eq_true hti
    have htj' : ¬ (s ∈ TT ∧ k.val = 0) := of_decide_eq_false htj
    obtain rfl : k0 = ⟨0, h0⟩ := Fin.ext hti'.2
    rw [jet_rowRad_top l sig eps _ _ _ _ hti]
    obtain ⟨hz, hw⟩ := hFP K l d N0 N1 hl hpi h0 x hx be hS1 s0 s hne k b b' α β
    have hbb : b = b' := by
      by_contra hbb
      apply hnot
      rw [hz hbb, monoWtGe_iff, norm_zero]
      exact Real.rpow_nonneg hpi0.le _
    subst hbb
    have hij : ((s0, ⟨0, h0⟩, b) : ZV d N0 N1) ≠ (s, k, b) := fun h => hne (congrArg Prod.fst h)
    have hκi : l ^ α ≤ κ (s0, ⟨0, h0⟩, b) := by
      have := hle (s0, ⟨0, h0⟩, b)
      simpa [pureMon, Finsupp.single_apply, hij, Ne.symm hij] using this
    have hκj : l ^ β ≤ κ (s, k, b) := by
      have := hle (s, k, b)
      simpa [pureMon, Finsupp.single_apply, hij, Ne.symm hij] using this
    have hnu : κ (s0, ⟨0, h0⟩, b) ≤ nu1 s0 := by
      rw [← hκtop s0 hti'.1]
      exact Finset.single_le_sum (f := fun b => κ (s0, ⟨0, h0⟩, b)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    have hsz : κ (s, k, b) ≤ size s := by
      have h1 : κ (s, k, b) ≤ Dl d TT nu1 size s := by
        rw [← hκD s]
        exact Finset.single_le_sum (f := fun y => κ y) (fun _ _ => Nat.zero_le _)
          (by simp [htj])
      refine h1.trans ?_
      unfold Dl
      split_ifs <;> omega
    obtain ⟨j0, hj0⟩ : ∃ j0 : ℤ, j0 = (α : ℤ) - β := ⟨_, rfl⟩
    have hsj : s = s0 + (j0 : ZMod d) := by
      rw [hj0]
      push_cast
      linear_combination (-1 : ZMod d) * heq
    have hjodd : Odd j0 := by
      obtain ⟨c, hc⟩ := hab
      exact ⟨(c : ℤ) - β, by omega⟩
    have hlev1 : 0 < j0 → l ^ j0.toNat ≤ nu1 s0 := by
      intro hj
      have : j0.toNat = α - β := by omega
      rw [this]
      exact (Nat.pow_le_pow_right hlpos (Nat.sub_le α β)).trans (hκi.trans hnu)
    have hlev2 : j0 < 0 → l ^ (-j0).toNat ≤ size s := by
      intro hj
      have : (-j0).toNat = β - α := by omega
      rw [this]
      exact (Nat.pow_le_pow_right hlpos (Nat.sub_le β α)).trans (hκj.trans hsz)
    by_cases hsp : spec (s, k) = some (s0, j0)
    · rw [jet_rowRad_spec l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
        (fun y => spec (y.1, y.2.1)) (s, k, b) htj hsp]
      rcases lt_trichotomy α β with hαβ | hαβ | hαβ
      · rw [if_neg (by omega)]
        have ht : (-j0).toNat = β - α := by omega
        rw [ht]
        have := R.2.2.1 s0 α (β - α) (max (sig s) ((l : ℝ) ^ (β - α))⁻¹) (by omega)
          (le_max_right _ _)
        rwa [Nat.add_sub_cancel' hαβ.le] at this
      · subst hαβ
        exfalso
        obtain ⟨c, hc⟩ := hab
        omega
      · rw [if_pos (by omega)]
        have ht : j0.toNat = α - β := by omega
        rw [ht]
        have := R.2.1 s0 β (α - β) (max (sig s) (1 - (l : ℝ) ^ (α - β) * eps s0)) (by omega)
          (le_max_right _ _)
        rwa [Nat.add_sub_cancel' hαβ.le] at this
    · exfalso
      apply hnot
      apply hw
      have hk := hkill s0 hti'.1 s k j0 htj' hjodd hsj hlev1 hlev2 hsp
      by_cases hβα : β ≤ α
      · rw [if_pos hβα]
        rw [if_pos (by omega : (0 : ℤ) ≤ j0)] at hk
        have ht : j0.toNat = α - β := by omega
        rwa [ht] at hk
      · rw [if_neg hβα]
        rw [if_neg (by omega : ¬ (0 : ℤ) ≤ j0)] at hk
        have ht : (-j0).toNat = β - α := by omega
        rwa [ht] at hk
  have hpure : ∀ (i j : ZV d N0 N1) (α β : ℕ), pureMon l i j α β ≤ κ →
      ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
        (MvPowerSeries.coeff (pureMon l i j α β) (bSum (frameM (N1 := N1) x) be)) →
      1 ≤ (l : ℝ) ^ α * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) i +
        (l : ℝ) ^ β * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) j := by
    intro i j α β hle hnot
    obtain ⟨hne, heq, hab⟩ := hsmall i j α β hnot
    have hsw : pureMon l j i β α = pureMon l i j α β := by
      unfold pureMon; exact add_comm _ _
    cases hti : frameTop TT i <;> cases htj : frameTop TT j
    · exact R.1 i.1 j.1 α β _ _ (jet_rowRad_ge l sig eps _ _ _ i hti)
        (jet_rowRad_ge l sig eps _ _ _ j htj) hab heq
    · have h := key j i β α (by rw [hsw]; exact hle) (by rw [hsw]; exact hnot) htj hti
      linarith
    · exact key i j α β hle hnot hti htj
    · rw [jet_rowRad_top l sig eps _ _ _ _ hti, jet_rowRad_top l sig eps _ _ _ _ htj]
      exact R.2.2.2 i.1 (of_decide_eq_true hti).1 j.1 (of_decide_eq_true htj).1 α β hab heq

  have hκa : ∀ y : ZV d N0 N1, κ y ≤ a := by
    rintro ⟨s, k, b⟩
    cases hty : frameTop TT ((s, k, b) : ZV d N0 N1)
    · have h1 : κ (s, k, b) ≤ Dl d TT nu1 size s := by
        rw [← hκD s]
        exact Finset.single_le_sum (f := fun y => κ y) (fun _ _ => Nat.zero_le _)
          (by simp [hty])
      have h2 : Dl d TT nu1 size s ≤ size s := by
        unfold Dl
        split_ifs <;> omega
      exact h1.trans (h2.trans (hsa s))
    · have hty' : s ∈ TT ∧ k.val = 0 := of_decide_eq_true hty
      obtain rfl : k = ⟨0, h0⟩ := Fin.ext hty'.2
      have h1 : κ (s, ⟨0, h0⟩, b) ≤ nu1 s := by
        rw [← hκtop s hty'.1]
        exact Finset.single_le_sum (f := fun b => κ (s, ⟨0, h0⟩, b)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ b)
      exact h1.trans ((hnu1s s).trans (hsa s))
  have hLR := hR K l d N0 N1 hl hodd hd hde hpi K0 hK0 ζ hζ be hbe (ZV d N0 N1)
    (fun y => y.1) (frameM (N1 := N1) x) hM1 hMlt g hg0 hg U hU ε hε
    (rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT) (fun y => spec (y.1, y.2.1)))
    (jet_rowRad_nonneg l sig eps _ _ _ hsig0 heps0) κ a ha hκa hpure
  have hcard : (Fintype.card (ZV d N0 N1) : ℝ) = (d : ℝ) * N0 * N1 := by
    simp only [ZV, Fintype.card_prod, ZMod.card, Fintype.card_fin]
    push_cast
    ring
  rw [hcard] at hLR
  refine hLR.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hpi.le ?_)
  linarith [hmain]

theorem theorem_A_one_monomial_log_loss : ThmAJetA.{u} :=
  ThmAJetA_of lemmaS.{u} lemma_R_log_loss.{u, 0} rowRadiusAssembly frame_pure_weight.{u}

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.WeightsAddOverOrbitsLogLoss
section
noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem unipotent_weight_bound : UWt.{u, v, w} := by
  classical
  intro K _ _ _ l hl hpi τ _ _ p g hg0 hg U hU ι _ M hM1 sig hsig
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have h1 : ‖(l : K)‖ ≤ 1 := hpi.le
  have hrho : 0 ≤ rho l := by
    unfold rho
    apply div_nonneg zero_le_one
    nlinarith
  have hr : ∀ i, (fun _ : ι => rho l) i ≤ (fun i => rho l + sig i) i := fun i => by
    simp only
    linarith [hsig i]
  have hlin0 : ∀ x, MvPowerSeries.constantCoeff
      (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i : MvPowerSeries ι K) = 0 := by
    intro x
    simp
  have hU0 : WtGe ‖(l : K)‖ (fun _ : τ => rho l) 0 U := by
    intro n
    rw [monoWtGe_iff]
    refine le_trans (hU n) (Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 ?_)
    linarith [asmR_dot_nonneg n (r := fun _ : τ => rho l) fun _ => hrho]
  have hgw := generalized_log_weight K l hl hpi τ p g hg0 hg
  have hgU : WtGe ‖(l : K)‖ (fun _ : τ => rho l) 0 (MvPowerSeries.subst g U) :=
    substitution_weight_bound K ‖(l : K)‖ h0 hpi τ τ g (fun _ => rho l) (fun _ => rho l) 0 U hg0 hgw hU0
  have hlinw : ∀ x, WtGe ‖(l : K)‖ (fun _ : ι => rho l) (rho l)
      (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i : MvPowerSeries ι K) := by
    intro x n
    rw [monoWtGe_iff]
    simp only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _)
      fun i _ => ?_
    split_ifs with h
    · subst h
      rw [mul_one, asmR_dot_single]
      simpa using hM1 x i
    · simpa using Real.rpow_nonneg h0.le _
  have hY : WtGe ‖(l : K)‖ (fun _ : ι => rho l) 0
      (MvPowerSeries.subst (fun x => (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i :
        MvPowerSeries ι K)) (MvPowerSeries.subst g U)) :=
    substitution_weight_bound K ‖(l : K)‖ h0 hpi τ ι _ (fun _ => rho l) (fun _ => rho l) 0 _
      hlin0 hlinw hgU
  exact (radical_weight_monotone K ‖(l : K)‖ h0 hpi ι (fun _ => rho l) (fun i => rho l + sig i) 0 hr).1 _ hY

theorem lemma_R_core_log_loss : RCoreA.{u, v} := by
  intro K _ _ _ l hl hpi ι _ sig κ a ha hκa B U hB0 hB hU
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have hrg : gam l = 1 / ((l : ℝ) - 1) - rho l := by
    have ha : (l : ℝ) - 1 ≠ 0 := by linarith
    have hb : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    unfold gam rho
    field_simp
    ring
  have hExp := exponential_weight_le K l hl hpi ι (fun i => rho l + sig i) κ B hB0 hB
  have hk := multiplicative_weight_le K ‖(l : K)‖ h0 ι (fun i => rho l + sig i) 0 0 κ U (mvExp B) hU hExp
    κ le_rfl
  rw [monoWtGe_iff] at hk
  have hf := factValA (K := K) hl hpi κ ha hκa
  rw [norm_mul]
  calc _ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) -
          (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1)) *
        ‖(l : K)‖ ^ (0 + 0 - dot κ (fun i => rho l + sig i)) :=
        mul_le_mul hf hk (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = _ := by
      rw [← Real.rpow_add h0]
      congr 1
      rw [coreL_dot_fintype, hrg]
      have key : ∑ i, (κ i : ℝ) * (1 / ((l : ℝ) - 1) - rho l - sig i) =
          (∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - ∑ i, (κ i : ℝ) * (rho l + sig i) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      linarith

end Formalism.DworkPowerSeriesWeights
end
end

