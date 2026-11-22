import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.Bundle0001
import Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0171
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrime
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDegreesSmallAgainstTypePrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

noncomputable section

namespace GlobalTheory.AtG.KernelSizes

variable {D : D7} {L : SizeData₂ D}

theorem key_ineq (A N Y : ℝ) (hA : 10 ≤ A) (hN : 2 ≤ N) (h1 : A ^ 8 ≤ Y) (h2 : N ^ 16 ≤ Y) :
    6 * A ^ 2 * N + 2 < Y := by
  have hA1 : 1 ≤ A := by linarith
  by_cases h : N ≤ A ^ 5
  · have hA7 : 1 ≤ A ^ 7 := one_le_pow₀ hA1
    have e1 : 6 * A ^ 2 * N ≤ 6 * A ^ 7 := by
      have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 6 * A ^ 2)
      calc 6 * A ^ 2 * N ≤ 6 * A ^ 2 * A ^ 5 := this
        _ = 6 * A ^ 7 := by ring
    have e2 : A ^ 8 = A * A ^ 7 := by ring
    have e3 : 10 * A ^ 7 ≤ A * A ^ 7 := mul_le_mul_of_nonneg_right hA (by positivity)
    linarith
  · push_neg at h
    have hA25 : A ^ 2 ≤ A ^ 5 := pow_le_pow_right₀ hA1 (by norm_num)
    have hAN : A ^ 2 < N := lt_of_le_of_lt hA25 h
    have e1 : 6 * A ^ 2 * N < 6 * N * N := by nlinarith
    have hN14 : 8 ≤ N ^ 14 := by
      have : (2 : ℝ) ^ 14 ≤ N ^ 14 := pow_le_pow_left₀ (by norm_num) hN 14
      linarith
    have e2 : N ^ 16 = N ^ 2 * N ^ 14 := by ring
    have e3 : N ^ 2 * 8 ≤ N ^ 2 * N ^ 14 := mul_le_mul_of_nonneg_left hN14 (by positivity)
    nlinarith

theorem exists_Y (P : ParameterChoice' D L) :
    ∃ Y : ℝ, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ Y ∧ (D.R.N D.R.m : ℝ) ^ 16 ≤ Y ∧ ∀ i, Y ≤ (D.host.g i : ℝ) := by
  obtain ⟨Y, h1, h2, -, h4⟩ := P.g_Y
  have hx0 : (0 : ℝ) < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hq : (0 : ℝ) < D.host.q := lt_trans (Real.rpow_pos_of_pos hx0 _) P.qd_pow.1
  have hd : (0 : ℝ) < D.host.d := lt_trans (Real.rpow_pos_of_pos hx0 _) P.qd_pow.2
  have hq1 : (1 : ℝ) ≤ D.host.q := by
    have : 0 < D.host.q := by exact_mod_cast hq
    exact_mod_cast this
  have hd1 : (1 : ℝ) ≤ D.host.d := by
    have : 0 < D.host.d := by exact_mod_cast hd
    exact_mod_cast this
  have hQ1 : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hc : (1 : ℝ) ≤ (LevelStarExponents.condE D : ℝ) := by
    unfold LevelStarExponents.condE
    push_cast
    calc (1 : ℝ) ≤ 1 * 1 * 1 := by norm_num
      _ ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by gcongr
  have hcC : 1 ≤ (LevelStarExponents.condE D : ℝ) ^ P.CY := Real.one_le_rpow hc P.CY_pos.le
  have hY0 : 0 ≤ Y := le_trans (by positivity) h1
  have hN4 : (D.R.N D.R.m : ℝ) ^ 4 ≤ Y ^ ((1 : ℝ) / 4) := by
    have hN : 0 ≤ (D.R.N D.R.m : ℝ) ^ 4 := by positivity
    nlinarith
  refine ⟨Y, h1, ?_, fun i => (h4 i).1⟩
  have h5 : ((D.R.N D.R.m : ℝ) ^ 4) ^ 4 ≤ (Y ^ ((1 : ℝ) / 4)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hN4 4
  have h6 : (Y ^ ((1 : ℝ) / 4)) ^ 4 = Y := by
    rw [← Real.rpow_natCast (Y ^ ((1 : ℝ) / 4)), ← Real.rpow_mul hY0]
    norm_num
  rw [h6] at h5
  calc (D.R.N D.R.m : ℝ) ^ 16 = ((D.R.N D.R.m : ℝ) ^ 4) ^ 4 := by ring
    _ ≤ Y := h5

theorem nuAbs_le (P : ParameterChoice' D L) (u : D.what₂.Word) (j : ℕ) (hj : j ∈ LiftErrorLocal.lifts D) (τ : D.what₂.Tau) :
    nuAbs D u j τ ≤ (D.R.N D.R.m : ℝ) * (3 * L.sc.a) := by
  unfold LiftErrorLocal.lifts at hj
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m := by omega
  have hb : ∀ t, (L.bT t : ℝ) ≤ 2 * L.sc.b' := fun t => by
    have := P.bT_le' t
    have := GlobalTheory.CoreHt.RowsRange.b'_pos L
    linarith
  have hT : GlobalTheory.CoreHt.ThickUp L := fun j h1 h2 τ hc => (L.win_thick j h1 h2 τ hc).2
  have ha : 0 ≤ L.sc.a := by
    unfold Scale.a
    have := GlobalTheory.CoreHt.RowsRange.one_le_b L
    have := L.sc.one_lt_alt
    positivity
  have hrow : ∀ r ∈ Finset.range (D.R.N (i + 1 - 1)), DV.nuRow D u (i + 1) τ r ≤ 3 * L.sc.a := by
    intro r hr
    rw [Finset.mem_range, Nat.add_sub_cancel] at hr
    exact (RowWeightLemmas.nuRow_anti' D u i hi τ r 0 (Nat.zero_le _) hr).trans
      (GlobalTheory.CoreHt.RowsRange.nuRow_zero_le_three_mul L P hb hT u i hi τ)
  unfold nuAbs
  have hs := Finset.sum_le_card_nsmul _ _ _ hrow
  rw [Finset.card_range, nsmul_eq_mul, Nat.add_sub_cancel] at hs
  have hNi : (D.R.N i : ℝ) ≤ D.R.N D.R.m := by
    have : D.R.N i ≤ D.R.N D.R.m := by
      unfold Ranks.N
      have := Nat.mul_le_mul_right (D.R.t + 1) hi.le
      omega
    exact_mod_cast this
  rw [Nat.add_sub_cancel]
  calc _ ≤ (D.R.N i : ℝ) * (3 * L.sc.a) := hs
    _ ≤ _ := mul_le_mul_of_nonneg_right hNi (by positivity)

theorem Dpi_le (P : ParameterChoice' D L) (u : D.what₂.Word) (j : ℕ) (hj : j ∈ LiftErrorLocal.lifts D) :
    LiftErrorLocal.Dpi D u j ≤ (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) * (3 * L.sc.a)) := by
  unfold LiftErrorLocal.Dpi
  have hs := Finset.sum_le_card_nsmul (Finset.univ : Finset D.what₂.Tau) (fun τ => nuAbs D u j τ) _
    (fun τ _ => nuAbs_le P u j hj τ)
  rw [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at hs
  exact hs

theorem sizeAt_of_params : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L →
    Formalism.MainNotions.SizesAt L → L.sc.eps = eps → x0 ≤ L.sc.x → ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i := by
  intro eps _ _
  refine ⟨0, fun D L P hS _ _ i => ?_⟩
  obtain ⟨Y, hY1, hY2, hY3⟩ := exists_Y P
  have hx1 := L.sc.one_lt_alt
  have hk5 : (5 : ℝ) ≤ D.R.k := P.five_le_k
  have hb2 : 2 ≤ L.sc.b := by
    have h1 := GlobalTheory.CoreHt.RowsRange.one_le_scL L
    have h2 := Real.add_one_le_exp L.sc.L
    unfold Scale.b
    linarith
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by
    have : D.R.f ≤ D.R.k := D.R.f_le_k
    exact_mod_cast this
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hNk : (D.R.k : ℝ) ≤ D.R.N D.R.m := by
    have : D.R.k ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    exact_mod_cast this

  have hxk : L.sc.x ≤ D.R.k := by
    have hK := hS.2.2.1.1
    have he : (1 : ℝ) ≤ 9 / 2 + 10 * L.sc.eps - szTh L := by
      unfold szTh
      linarith [L.sc.eps_pos, L.sc.eps_lt]
    have := Real.rpow_le_rpow_of_exponent_le hx1.le he
    rw [Real.rpow_one] at this
    linarith
  have hak : L.sc.a ≤ D.R.k * L.sc.b := by
    unfold Scale.a
    exact mul_le_mul_of_nonneg_right hxk (by linarith)
  set A : ℝ := (D.R.k : ℝ) * L.sc.b with hA
  set N : ℝ := (D.R.N D.R.m : ℝ) with hN
  have hA10 : 10 ≤ A := by rw [hA]; nlinarith
  have hN2 : 2 ≤ N := by linarith
  have hkey := key_ineq A N Y hA10 hN2 hY1 hY2
  have hkA : (D.R.k : ℝ) ^ 2 * L.sc.b ≤ A ^ 2 := by
    rw [hA]
    have : (D.R.k : ℝ) ^ 2 * L.sc.b * 1 ≤ (D.R.k : ℝ) ^ 2 * L.sc.b * L.sc.b :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith

  have hD : ∀ u : D.what₂.Word, ∀ j ∈ LiftErrorLocal.lifts D, LiftErrorLocal.Dpi D u j ≤ 3 * A ^ 2 * N := by
    intro u j hj
    have h1 := Dpi_le P u j hj
    have hN0 : 0 ≤ N := by linarith
    have h2 : (D.R.f : ℝ) * (N * (3 * L.sc.a)) ≤ (D.R.k : ℝ) * (N * (3 * (D.R.k * L.sc.b))) := by
      apply mul_le_mul hfk _ (by have := GlobalTheory.CoreHt.RowsRange.one_le_b L; unfold Scale.a; positivity) (by linarith)
      exact mul_le_mul_of_nonneg_left (by linarith) hN0
    have h3 : (D.R.k : ℝ) * (N * (3 * (D.R.k * L.sc.b))) = 3 * ((D.R.k : ℝ) ^ 2 * L.sc.b) * N := by ring
    have h4 : 3 * ((D.R.k : ℝ) ^ 2 * L.sc.b) * N ≤ 3 * A ^ 2 * N := by
      have := mul_le_mul_of_nonneg_left hkA (by norm_num : (0 : ℝ) ≤ 3)
      exact mul_le_mul_of_nonneg_right this hN0
    linarith
  have hg := hY3 i
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  refine ⟨?_, fun u j hj => ?_⟩
  · have h1 : (2 * D.R.f * D.R.N D.R.m + 1 : ℝ) < D.host.g i := by
      have : (2 : ℝ) * D.R.f * N ≤ 2 * (3 * A ^ 2 * N) := by
        have : (D.R.f : ℝ) ≤ 3 * A ^ 2 := by nlinarith
        nlinarith
      linarith
    exact_mod_cast h1
  · have h := hD u j hj
    constructor
    · linarith
    · nlinarith

end GlobalTheory.AtG.KernelSizes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentTempered
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CsdTempered

theorem hasInfChar_of_isRegAlg {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (ha : 2 ≤ a) {π : CuspSub E a}
    (hr : (CG.mk π).IsRegAlg) (τ : E →+* ℂ) : ∃ m, π.HasInfChar τ m := by
  by_contra hn
  have hn' : ¬ ∃ m, (CG.mk π).HasInfChar τ m := hn
  have h1 := (hr τ).1
  rw [CG.infChar, dif_neg hn'] at h1
  rw [Multiset.nodup_iff_count_le_one] at h1
  have h2 := h1 0
  rw [Multiset.count_replicate_self] at h2
  omega

theorem tempered_of_prime (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) {E Ω : Type} [Field E] [NumberField E]
    [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {a : ℕ} (ha : 2 ≤ a) {π : CuspSub E a}
    (hr : (CG.mk π).IsRegAlg) (hc : π.IsCsd) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    (h : IsPlaceOver A w) {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc)
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) :
    (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).tempered := by
  have ha1 : 1 ≤ a := by omega
  obtain ⟨r, wt, HT, H⟩ := hG.of_isCsd Ω ι ha1 hr hc
  have hwt := GlobalTheory.T.galois_weight_eq_dim_sub_one E Ω l ι a ha1 π _ r wt HT (hasInfChar_of_isRegAlg ha hr) hc H
  have h1 := H.tempered_wdOf hl h
  rw [H.wdOf_eq hl hrc hσ, WD.lpTw_add, hwt,
    show (1 - (a : ℝ)) / 2 + ((((a : ℤ) - 1 : ℤ) : ℝ)) / 2 = 0 by push_cast; ring, WD.lpTw_zero] at h1
  exact h1

theorem main : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 2 ≤ a → ∀ π : CuspSub E a, (CG.mk π).IsRegAlg → π.IsCsd → ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).tempered := by
  intro hG E Ω _ _ _ _ _ _ a ha π hr hc A w h rc hrc σ hσ
  by_cases h2 : ((2 : ℕ) : 𝓞 E) ∈ w.asIdeal
  · have h3 : ((3 : ℕ) : 𝓞 E) ∉ w.asIdeal := fun h3 => w.isPrime.ne_top <| by
      rw [Ideal.eq_top_iff_one]
      have e : ((3 : ℕ) : 𝓞 E) - ((2 : ℕ) : 𝓞 E) = 1 := by push_cast; ring
      rw [← e]
      exact w.asIdeal.sub_mem h3 h2
    obtain ⟨ι⟩ : Nonempty (Qbar 3 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 3
    exact tempered_of_prime hG ha hr hc h hrc hσ 3 ι h3
  · obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
    exact tempered_of_prime hG ha hr hc h hrc hσ 2 ι h2

end GlobalTheory.CsdTempered
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalPointThetaExhaustion
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PtLocalPin

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_fixed_of_finset {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)}
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (t : Finset (Submodule ℂ (GAf L n → W))) :
    (↑t ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ t, i), f ≠ 0 →
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) →
      ∃ S' ∈ t, ∃ g ∈ S', g ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g = g := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf hf0 _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    exact absurd hf hf0
  | insert a t ha ih =>
    intro hsub f hf hf0 hfix
    have haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a := hsub (Finset.mem_insert_self a t)
    have htF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), NG.rt L n h g ∈ (⨆ i ∈ t, i) :=
      GlobalTheory.HeckeScalarAll.iSup_finset_stable' t (fun i hi => (htF hi).1.1.stable)
    have hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ y = y := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add] at e
        have hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      have hzfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ z = z := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add, hyfix κ hκ hκt] at e
        exact add_left_cancel e
      by_cases hy0 : y = 0
      · subst hy0
        rw [zero_add] at hf0
        obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih htF z hz hf0 hzfix
        exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩
      · exact ⟨a, Finset.mem_insert_self a t, y, hy, hy0, hyfix⟩
    · have hle : a ≤ ⨆ i ∈ t, i := inf_eq_left.1 htop
      obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih htF f ((sup_le hle le_rfl) hf) hf0 hfix
      exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩

theorem fixed_of_iso {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (GAf L n → W)} (hS : NG.IsSubrep ρ S)
    (hiso : NG.IsoRep S S') (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g' : GAf L n → W)
    (hg' : g' ∈ S') (hg0 : g' ≠ 0) (hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g' = g') :
    ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g = g := by
  obtain ⟨T, hT⟩ := hiso
  set g : S := T.symm ⟨g', hg'⟩ with hgdef
  have hTg : T g = ⟨g', hg'⟩ := T.apply_symm_apply _
  refine ⟨g, g.2, fun h => hg0 ?_, fun κ hκ ht => ?_⟩
  · have h0 : g = 0 := Subtype.ext h
    rw [h0, map_zero] at hTg
    exact (congrArg Subtype.val hTg).symm
  · have e := hT κ g ⟨_, hS.stable κ _ g.2⟩ rfl
    rw [hTg] at e
    have e' : T ⟨NG.rt L n κ g, hS.stable κ _ g.2⟩ = T g := by
      rw [hTg]
      exact Subtype.ext (e.trans (hfix κ hκ ht))
    exact congrArg Subtype.val (T.injective e')

theorem exists_fixed_of_isoTyp {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)}
    (hS : NG.IsIrrRep ρ S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (f : GAf L n → W)
    (hf : f ∈ NG.isoTyp ρ S) (hf0 : f ≠ 0) (hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) :
    ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g = g := by
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  obtain ⟨S', hS', g', hg', hg0, hgf⟩ := exists_fixed_of_finset v t ht f hft hf0 hfix
  exact fixed_of_iso hS.1 (ht hS').2 v g' hg' hg0 hgf

end Gen

theorem coeff_eq {N n : ℕ} (hN : N ≠ 0) {c c' : ℕ → ℂ}
    (h : (X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) * c k) * X ^ (n - k) : ℂ[X]) =
      X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) * c' k) * X ^ (n - k))
    {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n) : c k = c' k := by
  have key : ∀ d : ℕ → ℂ, (X ^ n + ∑ j ∈ Finset.Icc 1 n,
      C ((-1 : ℂ) ^ j * ((N : ℂ)) ^ (j * (j - 1) / 2) * d j) * X ^ (n - j) : ℂ[X]).coeff (n - k) =
        (-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) * d k := by
    intro d
    rw [coeff_add, coeff_X_pow, if_neg (by omega), zero_add, finset_sum_coeff, Finset.sum_eq_single k]
    · rw [coeff_C_mul_X_pow, if_pos rfl]
    · intro j hj hjk
      rw [Finset.mem_Icc] at hj
      rw [coeff_C_mul_X_pow, if_neg (by omega)]
    · intro hk
      exact absurd (Finset.mem_Icc.2 ⟨h1, h2⟩) hk
  have e := congrArg (fun p : ℂ[X] => p.coeff (n - k)) h
  rw [key c, key c'] at e
  have hne : (-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hN))
  exact mul_left_cancel₀ hne e

theorem eig_at {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (P : Pin hL D) (i : D.nd.Loc) (Q : D.naut.AV i)
    (w : PlE D.host) (hw : SplitOut D.nd i w) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (hcw : IsConjPl D.host w s.w)
    (hu : IsUnif D.host.E s.v ϖ) :
    ∃ c : ℕ → ℂ, X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      galPol D.naut (D.naut.lpTw (D.naut.locV i Q w) ((1 - (D.R.nV : ℝ)) / 2)) ∧
      ∀ k, 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ D.naut.typeV i Q,
        NG.tN (P.M.loc i).J s ϖ k ((P.M.loc i).real y) = c k • (P.M.loc i).real y := by
  classical
  have HT := P.H.hecke
  have hsB : s.v ∉ badPl D i := GlobalTheory.HeckeScalarAll.not_bad HT i hw s hcw
  have hex : ∀ k, ∃ c : ℂ, ∀ f ∈ P.H.av.S i Q,
      (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) →
      NG.tN (Umax D.host.E D.R.nV) s ϖ k f = c • f := fun k =>
    GlobalTheory.T.splitPlace_heckeOperator_scalar_on_spherical D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s ϖ k hu
  choose c hc using hex
  have hfT : ∀ y, (P.M.loc i).real y ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    intro y
    rw [← (P.M.loc i).real_range]; exact ⟨y, rfl⟩
  have hfI : ∀ y ∈ D.naut.typeV i Q, (P.M.loc i).real y ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    intro y hy
    rw [P.H.av.typeV] at hy; exact hy
  have hfix : ∀ y, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      NG.rt D.host.E D.R.nV κ ((P.M.loc i).real y) = (P.M.loc i).real y := by
    intro y κ hκ ht
    have ht' : TrivOutside (badPl D i)ᶜ κ :=
      GlobalTheory.HeckeScalarAll.trivOutside_mono (Set.singleton_subset_iff.2 hsB) ht
    obtain ⟨h1, h2⟩ := HT.J_hyp i κ ht'
    have hJ : κ ∈ (P.M.loc i).J := h1.2 hκ
    have e := (hfT y).2 ⟨κ, hJ⟩
    rw [h2 hJ] at e
    simpa using e
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨y0, hy0, hy00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i Q)
    have hf0 : (P.M.loc i).real y0 ≠ 0 := fun h =>
      hy00 ((P.M.loc i).real_inj (h.trans (map_zero (P.M.loc i).real).symm))
    obtain ⟨g, hg, hg0, hgfix⟩ := exists_fixed_of_isoTyp (P.H.av.irr i Q) s.v _ (hfI y0 hy0) hf0 (hfix y0)
    have hpol := P.H.au.locPol (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q) s w ϖ hcw hu
      (Umax D.host.E D.R.nV) (fun κ _ => Iff.rfl) g hg hg0 hgfix c (fun k _ _ => hc k g hg hgfix)
    rw [hpol, D.nbc.embAV_loc, P.H.emb]
  · intro k _ _ y hy
    have hfinU := GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (Umax D.host.E D.R.nV) 1 ∅
      (fun κ _ => ⟨Iff.rfl, fun _ => rfl⟩) s ϖ k (by simp) hu
    have e1 : NG.tN (P.M.loc i).J s ϖ k ((P.M.loc i).real y) =
        NG.tN (Umax D.host.E D.R.nV) s ϖ k ((P.M.loc i).real y) := by
      simp only [NG.tN]
      rw [GlobalTheory.HeckeScalarAll.heckeD_eq_of_fixed (P.M.loc i).J (P.M.loc i).χ (badPl D i) (HT.J_hyp i) s hsB ϖ k _
        (hfix y)]
    rw [e1]
    exact GlobalTheory.HeckeScalarAll.tN_isoTyp (P.H.av.irr i Q) s ϖ k hfinU (c k) (hc k) _ (hfI y hy) (hfix y)

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ i,
    GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  intro hL D P i
  refine GlobalTheory.T.pointLocalEigen_galoisPolynomial_split D P.M P.H.hecke P.H.rational P.H.av P.H.cover i ?_
  intro Q w hw
  obtain ⟨s0, ϖ0, hc0, hu0⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw.1
  obtain ⟨c0, hp0, -⟩ := eig_at P i Q w hw s0 ϖ0 hc0 hu0
  have hN : normV w ≠ 0 := (lt_trans zero_lt_one (GlobalTheory.WeilDeligne.one_lt_normV w)).ne'
  refine ⟨c0, hp0.symm, fun k s ϖ hc hu h1 h2 y hy => ?_⟩
  obtain ⟨c, hp, hy'⟩ := eig_at P i Q w hw s ϖ hc hu
  rw [hy' k h1 h2 y hy, coeff_eq hN (hp.trans hp0.symm) h1 h2]

end GlobalTheory.PtLocalPin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAllPlacesStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedThetaFamily_normalised_all_places : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L L') (fun z => B.eNat χ N N' L L' (s.flatV N N' z)) p ι := by
  first | exact @GlobalTheory.ThLoc.latAt_all | exact GlobalTheory.ThLoc.latAt_all | (intros; apply GlobalTheory.ThLoc.latAt_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoinStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_reading_of_join : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Join P → ∀ S : Reading P.T, IsTrue P S → RowUnit S → PairRead S := by
  first | exact @GlobalTheory.NPin.pairRead_of_join | exact GlobalTheory.NPin.pairRead_of_join | (intros; apply GlobalTheory.NPin.pairRead_of_join <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoSidedHeckePartner_inertPrime : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t P, Good R t P → conjPl P = P → FixAll R t P → TwoSided R t P := by
  first | exact @GlobalTheory.Hk3.TwoSidedInert.twoSided_of_inert | exact GlobalTheory.Hk3.TwoSidedInert.twoSided_of_inert | (intros; apply GlobalTheory.Hk3.TwoSidedInert.twoSided_of_inert <;> assumption)
end

