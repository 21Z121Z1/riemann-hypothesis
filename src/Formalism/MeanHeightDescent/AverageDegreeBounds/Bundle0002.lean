import Mathlib
import Formalism.MeanHeightDescent.AverageDegreeBounds.Bundle0001
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0005
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.MeanHeightDescent.MuMaxMinkowski
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtImage
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0004

-- bundled from Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeAssemblyHolds
section
open Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

theorem log_covolume_slope_mu : LcvMu := by
  intro K _ _ _ _ d hd X hX M hM
  have hfg : M.FG := Submodule.IsLattice.fg (self := hM)
  have hspan : Submodule.span K (M : Set (Fin d → K)) = ⊤ :=
    Submodule.IsLattice.span_eq_top (self := hM)
  have hrk : Formalism.HN.rkK M = d := by
    unfold Formalism.HN.rkK
    rw [hspan]
    simp
  have hne : M ≠ ⊥ := by
    intro h
    have h2 : Formalism.HN.rkK (⊥ : Submodule (𝓞 K) (Fin d → K)) = 0 := by
      unfold Formalism.HN.rkK
      simp
    rw [h, h2] at hrk
    omega
  obtain ⟨-, hmu, -⟩ := Formalism.HN.size_maximal_slope K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX M hfg hne
  have hht : 0 < Formalism.HN.ht (Pi.basisFun K (Fin d)) X M :=
    (Formalism.HN.place_lattice_structure K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX M hfg).2.2
  have hn : (finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by
    exact_mod_cast Formalism.HN.sizeMu_finrank_eq K
  have hf : (0 : ℝ) < Formalism.HN.nPl K := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
  have hDr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [hmu, Formalism.HN.size, Real.log_rpow hht, hrk, Formalism.DivisionValues.lcv, hn]
  field_simp

set_option maxHeartbeats 800000 in

theorem covolume_assembly_holds : CovolumeEstimateOfSlopeChain := by
  unfold CovolumeEstimateOfSlopeChain
  intro K _ _ _ _ d D hD hdD XW hXW M hM Pl _ w c1 ua muU muA muN muG mmax dA dB dN dg db C1 Cf Cc cfl ε δ Q P Λ G P9 pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47 h48 h49 h50
  have hd : 0 < d := by omega
  have hlcv := log_covolume_slope_mu K d hd XW hXW M hM
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hdD' : (d : ℝ) = D := by exact_mod_cast hdD
  rw [hlcv, hdD', neg_div, mul_div_cancel_left₀ _ hDpos.ne']
  set Sw := ∑ τ, w τ with hSwdef
  set Su := ∑ τ, ua τ with hSudef
  set X := 2 * (C1 * LL0 * Su + b / 4) with hXdef
  have hQ0 : 0 ≤ Q := le_trans (abs_nonneg _) h10
  have hL1 : 1 ≤ L := by
    rw [h38]
    exact Real.one_le_rpow h36 h37.le
  have hb1 : 1 ≤ b := by
    rw [h39]
    exact Real.one_le_exp (by linarith)
  have hlrd : 0 ≤ Real.log rd := Real.log_nonneg h40
  have hlx : 0 ≤ Real.log x := Real.log_nonneg h36
  have hlogbrd : Real.log (b * rd) = L + Real.log rd := by
    rw [Real.log_mul (by linarith : (0:ℝ) < b).ne' (by linarith : (0:ℝ) < rd).ne', h39, Real.log_exp]
  have hLL0 : LL0 ≤ 4 * L * llx := by
    rw [h46, hlogbrd]
    linarith [mul_nonneg (sub_nonneg.mpr h41) (by linarith : (0:ℝ) ≤ llx),
      mul_nonneg (by linarith : (0:ℝ) ≤ L) (sub_nonneg.mpr h45), h43, h44, h42]
  have hLL0nn : 0 ≤ LL0 := by
    rw [h46, hlogbrd]
    linarith [mul_nonneg (by linarith : (0:ℝ) ≤ L + Real.log rd) (by linarith : (0:ℝ) ≤ llx), h42, hlx]
  have hw0 : ∀ τ, 0 ≤ w τ := fun τ => (h28 τ).1
  have hSw0 : 0 ≤ Sw := Finset.sum_nonneg (fun τ _ => hw0 τ)
  have hSw : Sw ≤ 2 * b * f := by
    have e1 : Sw ≤ ∑ _τ : Pl, 2 * b := Finset.sum_le_sum (fun τ _ => (h28 τ).2)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at e1
    linarith [mul_le_mul_of_nonneg_right h31 (by linarith : (0:ℝ) ≤ 2 * b)]
  have hSu0 : 0 ≤ Su := by linarith [h27]
  have hSu : Su ≤ 8 * b * f * m := by
    have e1 : Su ≤ ∑ τ, (2 * m * w τ + 4 * b) :=
      Finset.sum_le_sum (fun τ _ => by linarith [(h26 τ).2, h29, h30])
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← hSwdef] at e1
    linarith [mul_le_mul_of_nonneg_left hSw (by linarith : (0:ℝ) ≤ 2 * m),
      mul_le_mul_of_nonneg_right h31 (by linarith : (0:ℝ) ≤ 4 * b),
      mul_le_mul_of_nonneg_left h32 (mul_nonneg (by linarith : (0:ℝ) ≤ b) (by linarith : (0:ℝ) ≤ f))]
  have hwc1 : -(pq * logOm / 2 + Cc * q' * (Real.log rd + Lchi)) * Sw ≤ ∑ τ, w τ * c1 τ := by
    rw [hSwdef, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro τ _
    have h := (abs_le.mp (h25 τ)).1
    linarith [mul_le_mul_of_nonneg_left h (hw0 τ), hw0 τ]
  have hpq : ∑ ρ, pq * w ρ * logOm = pq * logOm * Sw := by
    rw [hSwdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    ring
  have hδ : δ * dN ≤ (1 / 12) * dN := mul_le_mul_of_nonneg_right h18 h13.le
  have hdg : (3 / 4) * dN ≤ dg := by linarith [h14, h16, hδ]
  have hmuG : muN - 12 * δ * Q ≤ muG := by
    have e1 : db * (-(3 * Q)) ≤ db * (muN - mmax - G) :=
      mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp h20).1, h21, h22]) h15
    have f1 : Q * db ≤ Q * (3 * δ * dN) := mul_le_mul_of_nonneg_left h16 hQ0
    have f2 : (12 * δ * Q) * ((3 / 4) * dN) ≤ (12 * δ * Q) * dg :=
      mul_le_mul_of_nonneg_left hdg (mul_nonneg (mul_nonneg (by norm_num) h17) hQ0)
    have hdgpos : 0 < dg := by linarith
    have h19' : (dg + db) * muN ≤ dg * muG + db * (mmax + G) := by
      rw [← h14]
      exact h19
    have key : 0 ≤ dg * (muG - muN + 12 * δ * Q) := by linarith [h19', e1, f1, f2]
    by_contra hcon
    push_neg at hcon
    have hneg : dg * (muG - muN + 12 * δ * Q) < 0 := mul_neg_of_pos_of_neg hdgpos (by linarith)
    linarith
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    have := mul_nonneg (mul_nonneg h48 hLL0nn) hSu0
    linarith
  have hdBpos : 0 < dB := by linarith
  have hmuN : -X + 2 * cfl - P - b / 2 ≤ muN := by
    have g1 : dA * (-X) ≤ dA * muU := mul_le_mul_of_nonneg_left h1 h4.le
    have g1' : dB * (-X) ≤ dA * (-X) := by
      linarith [mul_nonneg (by linarith : (0:ℝ) ≤ dB - dA) hX0]
    have g2 : (dB - dA) * (2 * cfl) ≤ (dB - dA) * Q :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) h10) (by linarith)
    have g3 : (dB - dA) * Λ ≤ (dB - dA) * Q := mul_le_mul_of_nonneg_left h11 (by linarith)
    have g4 : (dB - dA) * Q ≤ (ε * dB) * Q := mul_le_mul_of_nonneg_right (by linarith) hQ0
    have g5 : dA * P ≤ dB * P := mul_le_mul_of_nonneg_right h5 h8
    have g6 : dA * (muU + 2 * cfl - P) ≤ dA * (muA - P) := mul_le_mul_of_nonneg_left (by linarith) h4.le
    have g7 : dB * (ε * Q) ≤ dB * (b / 4) := mul_le_mul_of_nonneg_left h12 hdBpos.le
    have key : dB * (-X + 2 * cfl - P - b / 2) ≤ dB * muN := by
      linarith [h9, g1, g1', g2, g3, g4, g5, g6, g7]
    exact le_of_mul_le_mul_left key hdBpos
  have hμlow : -Formalism.HN.muDef (Pi.basisFun K (Fin d)) XW M ≤ X - 2 * cfl + 3 * b / 2 := by
    linarith [h23, hmuG, hmuN, h24]
  have hcfl : -(2 * cfl) ≤ pq * logOm * Sw + 2 * (Cc * q' * (Real.log rd + Lchi)) * Sw +
      2 * Cf * q' * Real.log rd * Sw + 2 * Cf * L := by
    rw [h2]
    linarith [hwc1]
  have hB0 : B0 = f * m * b * L := by rw [h47, ← h38]
  have hfm : 1 ≤ f * m := by
    have := mul_le_mul h33 h32 zero_le_one (by linarith)
    linarith
  have hfmb : 1 ≤ f * m * b := by
    have := mul_le_mul hfm hb1 zero_le_one (by linarith)
    linarith
  have hfmL : 1 ≤ f * m * L := by
    have := mul_le_mul hfm hL1 zero_le_one (by linarith)
    linarith
  have hB0nn : 0 ≤ B0 := by
    rw [hB0]
    exact mul_nonneg (by linarith) (by linarith)
  have hLB : L ≤ B0 := by
    rw [hB0]
    linarith [mul_le_mul_of_nonneg_right hfmb (show (0:ℝ) ≤ L by linarith)]
  have hbB : b ≤ B0 := by
    rw [hB0]
    linarith [mul_le_mul_of_nonneg_left hfmL (show (0:ℝ) ≤ b by linarith)]
  have hBll : B0 ≤ B0 * llx := by linarith [mul_le_mul_of_nonneg_left h45 hB0nn]
  have hT1 : C1 * LL0 * Su ≤ 32 * (C1 * (B0 * llx)) := by
    have e1 : LL0 * Su ≤ (4 * L * llx) * (8 * b * f * m) :=
      mul_le_mul hLL0 hSu hSu0 (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
    have e2 := mul_le_mul_of_nonneg_left e1 h48
    have e5 : C1 * ((4 * L * llx) * (8 * b * f * m)) = 32 * (C1 * (B0 * llx)) := by
      rw [hB0]
      ring
    linarith [e2, e5]
  have hT2 : Cc * q' * (Real.log rd + Lchi) * Sw ≤ 4 * (Cc * (B0 * llx)) := by
    have e1 : q' * (Real.log rd + Lchi) ≤ m * (2 * L) :=
      mul_le_mul h35 (by linarith) (by linarith) (by linarith)
    have e2 : q' * (Real.log rd + Lchi) * Sw ≤ m * (2 * L) * (2 * b * f) :=
      mul_le_mul e1 hSw hSw0 (mul_nonneg (by linarith) (by linarith))
    have e3 := mul_le_mul_of_nonneg_left e2 h50
    have e4 : Cc * B0 ≤ Cc * (B0 * llx) := mul_le_mul_of_nonneg_left hBll h50
    have e5 : Cc * (m * (2 * L) * (2 * b * f)) = 4 * (Cc * B0) := by
      rw [hB0]
      ring
    linarith [e3, e4, e5]
  have hT3 : Cf * q' * Real.log rd * Sw + Cf * L ≤ 3 * (Cf * (B0 * llx)) := by
    have e1 : q' * Real.log rd ≤ m * L := mul_le_mul h35 h41 hlrd (by linarith)
    have e2 : q' * Real.log rd * Sw ≤ m * L * (2 * b * f) := mul_le_mul e1 hSw hSw0 (mul_nonneg (by linarith) (by linarith))
    have e3 := mul_le_mul_of_nonneg_left e2 h49
    have e4 : Cf * L ≤ Cf * B0 := mul_le_mul_of_nonneg_left hLB h49
    have e5 : Cf * (m * L * (2 * b * f)) = 2 * (Cf * B0) := by
      rw [hB0]
      ring
    have e6 : Cf * B0 ≤ Cf * (B0 * llx) := mul_le_mul_of_nonneg_left hBll h49
    linarith [e3, e4, e5, e6]
  have hT4 : b ≤ B0 * llx := le_trans hbB hBll
  have hpos : 0 ≤ Cf * (B0 * llx) := mul_nonneg h49 (mul_nonneg hB0nn (by linarith))
  rw [hpq]
  linarith [hμlow, hcfl, hT1, hT2, hT3, hT4, hXdef, hpos]

end Formalism.ExtensionFiltration
end
end

-- bundled from Formalism.MeanHeightDescent.AverageDegreeBounds.DescentSlope
section
open Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

open Formalism.HN

theorem slope_image_injective
    {K V ι W κ : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (hX : ∀ v, IsUnit (X v).det) (hX' : ∀ v, IsUnit (X' v).det)
    (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) (hAfg : A.FG) (hA0 : A ≠ ⊥)
    (hinj : Function.Injective φ) :
    rkK (A.map (φ.restrictScalars (𝓞 K))) = rkK A ∧
      2 * slope (Formalism.HermitianLatticesTheory.realize b X) A - htMap b X b' X' φ ≤
        2 * slope (Formalism.HermitianLatticesTheory.realize b' X') (A.map (φ.restrictScalars (𝓞 K))) := by
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have hrkeq := sizeIneq_rk φ A
  obtain ⟨hsat, hht⟩ := height_image_formula K V ι W κ b X b' X' hX hX' φ A hAfg
  have hker : A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = ⊥ := by
    rw [LinearMap.ker_eq_bot.2 hinj, Submodule.restrictScalars_bot, inf_bot_eq]
  rw [hker] at hrkeq hsat hht
  have hrkbot : rkK (K := K) (⊥ : Submodule (𝓞 K) V) = 0 := by
    unfold rkK
    simp
  rw [hrkbot, add_zero] at hrkeq
  refine ⟨hrkeq, ?_⟩
  set I := A.map (φ.restrictScalars (𝓞 K)) with hIdef
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'
  have hIfg : I.FG := hAfg.map _
  have hI0 : I ≠ ⊥ := by
    intro h
    apply hA0
    rw [eq_bot_iff]
    intro x hx
    have hm : φ x ∈ I := ⟨x, hx, rfl⟩
    rw [h] at hm
    have h0 : φ x = 0 := (Submodule.mem_bot _).1 hm
    exact (Submodule.mem_bot _).2 (hinj (by rw [h0, map_zero]))
  obtain ⟨hAlat, -, -⟩ := place_lattice_structure K V ι b X hX A hAfg
  obtain ⟨-, -, hhtI⟩ := place_lattice_structure K W κ b' X' hX' I hIfg
  obtain ⟨-, -, hsQ, -, -, -⟩ := size_maximal_slope K V ι b X hX A hAfg hA0
  have hSI := (size_maximal_slope K W κ b' X' hX' I hIfg hI0).1
  have hSBA := saturation_basic_properties (𝓞 K) V _ ρ A hAlat
  have hq := hSBA.2.2.2.2.2.2.2 ⊥ hsat
  have hrb : rk ρ (⊥ : Submodule (𝓞 K) V) = 0 := (hSBA.2.2.2.1 ⊥ bot_le).2 rfl
  have hdb : deg ρ (⊥ : Submodule (𝓞 K) V) = 0 := hSBA.2.2.2.2.1
  have hslQ : Formalism.F.slope (Formalism.F.quot (zl ρ A) (zl ρ (⊥ : Submodule (𝓞 K) V))) = slope ρ A := by
    unfold Formalism.F.slope
    rw [hq.1, hq.2.2, hrb, hdb, Nat.sub_zero, sub_zero]
    rfl
  have hsQ' := hsQ ⊥ hsat (Ne.symm hA0)
  rw [hslQ] at hsQ'
  set P := ∏ v, opNormAt b X b' X' v φ with hPdef
  have hP : 0 ≤ P := Finset.prod_nonneg (fun v _ => norm_nonneg _)
  have hf : (0 : ℝ) < nPl K := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have hs : (0 : ℝ) < rkK I := by
    rw [hrkeq]
    have h : Submodule.span K (A : Set V) ≠ ⊥ := by
      intro h
      apply hA0
      rw [Submodule.span_eq_bot] at h
      exact (Submodule.eq_bot_iff _).2 (fun x hx => h x hx)
    have : 0 < rkK (K := K) A :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 h)
    exact_mod_cast this
  have hrkR : ((rkK A : ℝ) - rkK (K := K) (⊥ : Submodule (𝓞 K) V)) = rkK I := by
    rw [hrkbot, hrkeq]; simp
  rw [Finset.prod_pow, ← hPdef] at hht
  have hX0 : 0 ≤ P ^ (2 * rkK I) := pow_nonneg hP _
  have hQpos : 0 < htQ b X A ⊥ := pos_of_mul_pos_right (lt_of_lt_of_le hhtI hht) hX0
  have hPpos : 0 < P := by
    rcases hP.lt_or_eq with h | h
    · exact h
    · exfalso
      have hne : 2 * rkK I ≠ 0 := by
        have : 0 < rkK I := by exact_mod_cast hs
        omega
      rw [← h, zero_pow hne, zero_mul] at hht
      exact absurd hhtI (not_lt.2 hht)
  have he : (0 : ℝ) ≤ 1 / (2 * (nPl K : ℝ) * (rkK I : ℝ)) := by positivity
  have hcore : size b' X' I ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * sizeQ b X A ⊥ := by
    unfold size sizeQ
    rw [hrkR]
    calc ht b' X' I ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ)))
        ≤ (P ^ (2 * rkK I) * htQ b X A ⊥) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.rpow_le_rpow hhtI.le hht he
      _ = (P ^ (2 * rkK I)) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) *
            htQ b X A ⊥ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.mul_rpow hX0 hQpos.le
      _ = P ^ ((1 : ℝ) / (nPl K : ℝ)) *
            htQ b X A ⊥ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hP]
          congr 1
          push_cast
          field_simp
  rw [hSI, hsQ', Real.rpow_def_of_pos hPpos, ← Real.exp_add, Real.exp_le_exp] at hcore
  have hht2 : htMap b X b' X' φ = 2 * (Real.log P * (1 / (nPl K : ℝ))) := by
    unfold htMap
    have hne : ∀ v ∈ (Finset.univ : Finset (InfinitePlace K)), opNormAt b X b' X' v φ ≠ 0 := by
      intro v hv h0
      exact hPpos.ne' (Finset.prod_eq_zero hv h0)
    rw [hPdef, Real.log_prod hne]
    simp only [Real.log_pow]
    rw [← Finset.mul_sum]
    push_cast
    ring
  rw [hht2]
  linarith

theorem descent_slope : DescentSlope := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B hAfg hBfg hA0 hinj hIB
  obtain ⟨hrkeq, hsl⟩ := slope_image_injective b X b' X' hX hX' φ A hAfg hA0 hinj
  set I := A.map (φ.restrictScalars (𝓞 K)) with hIdef
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'
  have hIfg : I.FG := hAfg.map _
  have hI0 : I ≠ ⊥ := by
    intro h
    apply hA0
    rw [eq_bot_iff]
    intro x hx
    have hm : φ x ∈ I := ⟨x, hx, rfl⟩
    rw [h] at hm
    have h0 : φ x = 0 := (Submodule.mem_bot _).1 hm
    exact (Submodule.mem_bot _).2 (hinj (by rw [h0, map_zero]))
  have hB0 : B ≠ ⊥ := fun h => hI0 (le_bot_iff.mp (h ▸ hIB))
  obtain ⟨hBlat, hrkB, -⟩ := place_lattice_structure K W κ b' X' hX' B hBfg
  obtain ⟨-, hrkI, -⟩ := place_lattice_structure K W κ b' X' hX' I hIfg
  have hSBB := saturation_basic_properties (𝓞 K) W _ ρ' B hBlat
  have hMB := slope_characterization (𝓞 K) W _ ρ' B hBlat hB0
  have hmin := (hMB.2.1 (muMin ρ' B)).1 le_rfl I hIB
  have hrkIpos : 0 < rk ρ' I := by
    rcases Nat.eq_zero_or_pos (rk ρ' I) with h | h
    · exact absurd ((hSBB.2.2.2.1 I hIB).1 h) hI0
    · exact h
  have hrkBpos : 0 < rk ρ' B := by
    rcases Nat.eq_zero_or_pos (rk ρ' B) with h | h
    · exact absurd ((hSBB.2.2.2.1 B le_rfl).1 h) hB0
    · exact h
  have hdI : deg ρ' I = slope ρ' I * (rk ρ' I : ℝ) := by
    have : (rk ρ' I : ℝ) ≠ 0 := by exact_mod_cast hrkIpos.ne'
    show deg ρ' I = deg ρ' I / (rk ρ' I : ℝ) * (rk ρ' I : ℝ)
    field_simp
  have hdB : deg ρ' B = slope ρ' B * (rk ρ' B : ℝ) := by
    have : (rk ρ' B : ℝ) ≠ 0 := by exact_mod_cast hrkBpos.ne'
    show deg ρ' B = deg ρ' B / (rk ρ' B : ℝ) * (rk ρ' B : ℝ)
    field_simp
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  rw [hdI, hdB, hrkB, hrkI, hrkeq] at hmin
  push_cast at hmin
  have hmin' : muMin ρ' B * ((rkK B : ℝ) - rkK A) ≤
      slope ρ' B * (rkK B : ℝ) - slope ρ' I * (rkK A : ℝ) := by
    refine le_of_mul_le_mul_left ?_ hn
    linarith
  have hra : (0 : ℝ) ≤ (rkK A : ℝ) := Nat.cast_nonneg _
  have h2 := mul_le_mul_of_nonneg_left hsl hra
  unfold muDef muMinDef
  simp only [← hρ, ← hρ']
  nlinarith [h2, hmin']

end Formalism.ExtensionFiltration
end
end

