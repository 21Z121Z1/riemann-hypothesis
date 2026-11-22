import Mathlib
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ContDiffAtSectionFrameQuotient
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0454
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0642
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveHeckeLFunctionInvOfTrivialOnMaxReal
section
open NumberField IsDedekindDomain GlobalTheory.CMVal

noncomputable section

namespace GlobalTheory.CMVal.InvConj

open Formalism.L2.Host Formalism.L2.Host.CT

variable {E : Type} [Field E] [NumberField E]

theorem loc_eq_one_of_prod (ψ : HChar E) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (h : ∀ k : Eˣ, ∏ P ∈ S, ψ.locK P k = 1) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ S)
    (x : (w.adicCompletion E)ˣ) : ψ.loc w x = 1 := by
  classical
  choose n hn using fun P => GlobalTheory.Mem.UnrAe.exists_levelLe ψ P
  obtain ⟨y, hy0, hyw, hyv⟩ := GlobalTheory.HkFin.exists_weak_approx_unit E S w x (S.sup n + 1)
  have lev : ∀ P ∈ S, ∀ z : (P.adicCompletion E)ˣ,
      Valued.v ((z : P.adicCompletion E) - 1) ≤ WithZero.exp (-((S.sup n + 1 : ℕ) : ℤ)) → ψ.loc P z = 1 := by
    intro P hP z hz
    have h1 : Valued.v ((z : P.adicCompletion E) - 1) < Valued.v (1 : P.adicCompletion E) := by
      rw [map_one]
      refine lt_of_le_of_lt hz ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hu : IsUnitAt P z := by
      unfold IsUnitAt
      have e : (z : P.adicCompletion E) = ((z : P.adicCompletion E) - 1) + 1 := by ring
      rw [e, Valuation.map_add_eq_of_lt_right _ h1, map_one]
    refine hn P z hu (hz.trans ?_)
    rw [WithZero.exp_le_exp]
    have : n P ≤ S.sup n := Finset.le_sup hP
    omega
  have hS := h (Units.mk0 y hy0)
  rw [← Finset.mul_prod_erase S _ hw, Finset.prod_eq_one (fun P hP => ?_), mul_one] at hS
  · have e : ψ.loc w x = ψ.locK w (Units.mk0 y hy0) * (ψ.loc w (atFin w (Units.mk0 y hy0) * x⁻¹))⁻¹ := by
      rw [map_mul, map_inv, mul_inv, inv_inv, ← mul_assoc]; simp [HChar.locK]
    have h2 : ψ.loc w (atFin w (Units.mk0 y hy0) * x⁻¹) = 1 := lev w hw _ (by
      have := hyw
      exact this)
    rw [e, hS, h2, inv_one, mul_one]
  · obtain ⟨hPw, hPS⟩ := Finset.mem_erase.1 hP
    refine lev P hPS _ ?_
    have h3 := hyv P hPS hPw
    show Valued.v (algebraMap E (P.adicCompletion E) y - 1) ≤ _
    rw [← map_one (algebraMap E (P.adicCompletion E)), ← map_sub]
    first
      | exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (y - 1)).trans_le h3
      | (rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation]; exact h3)

end GlobalTheory.CMVal.InvConj

namespace GlobalTheory.CMVal.InvConj

open Formalism.L2.Host Formalism.L2.Host.CT

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev conjE : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

theorem conjE_apply (x : E) : conjE x = IsCMField.complexConj E x := rfl

theorem conjE_symm_apply (x : E) : (conjE (E := E)).symm x = IsCMField.complexConj E x := by
  rw [RingEquiv.symm_apply_eq, conjE_apply, IsCMField.complexConj_apply_apply]

theorem under_plMap (j : E ≃+* E) (hj : ∀ x : maximalRealSubfield E, j (x : E) = x) (P : HeightOneSpectrum (𝓞 E)) :
    (plMap j P).under (OF E) = P.under (OF E) := by
  ext a
  have e : RingOfIntegers.mapRingEquiv j (algebraMap (OF E) (𝓞 E) a) = algebraMap (OF E) (𝓞 E) a :=
    RingOfIntegers.ext (hj (a : maximalRealSubfield E))
  show algebraMap (OF E) (𝓞 E) a ∈ (plMap j P).asIdeal ↔ algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal
  rw [← mem_plMap j P, e]

theorem mem_aboveF (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)) :
    P ∈ aboveF (L := E) (maximalRealSubfield E) v ↔ P.under (OF E) = v := by
  unfold aboveF
  rw [Set.Finite.mem_toFinset]
  rfl

theorem prod_locK_conj (χ : HChar E) (hχ : TrivOnF χ) (v : HeightOneSpectrum (OF E)) (k : Eˣ) :
    ∏ P ∈ aboveF (L := E) (maximalRealSubfield E) v, (χ * transport conjE χ).locK P k = 1 := by
  have h1 : ∀ P, (χ * transport conjE χ).locK P k = χ.locK P k * (transport conjE χ).locK P k := fun P => rfl
  have hs : ∀ x : maximalRealSubfield E, (conjE (E := E)).symm (x : E) = x := fun x => by
    rw [conjE_symm_apply]; exact IsCMField.complexConj_apply_eq_self E x
  have hc : ∀ x : maximalRealSubfield E, (conjE (E := E)) (x : E) = x := fun x =>
    IsCMField.complexConj_apply_eq_self E x
  have h2 : ∏ P ∈ aboveF (L := E) (maximalRealSubfield E) v, (transport conjE χ).locK P k =
      ∏ P ∈ aboveF (L := E) (maximalRealSubfield E) v, χ.locK P (Units.map (conjE (E := E)).toMonoidHom k) := by
    symm
    refine Finset.prod_nbij' (fun P => plMap (conjE (E := E)).symm P) (fun P => plMap conjE P) ?_ ?_ ?_ ?_ ?_
    · intro P hP
      rw [mem_aboveF] at hP ⊢
      rw [under_plMap _ hs P]; exact hP
    · intro P hP
      rw [mem_aboveF] at hP ⊢
      rw [under_plMap _ hc P]; exact hP
    · intro P _; exact plMap_plMap_symm conjE P
    · intro P _; exact plMap_symm_plMap conjE P
    · intro P _
      show χ.loc P (atFin P _) = (transport conjE χ).loc (plMap (conjE (E := E)).symm P) (atFin _ k)
      rw [transport_loc, locMap_atFin]
  rw [Finset.prod_congr rfl (fun P _ => h1 P), Finset.prod_mul_distrib, h2, ← Finset.prod_mul_distrib]
  have hN : (k : E) * conjE (k : E) ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_mul, conjE_apply, IsCMField.complexConj_apply_apply, mul_comm]
  have hN0 : (⟨_, hN⟩ : maximalRealSubfield E) ≠ 0 := fun h0 =>
    mul_ne_zero k.ne_zero ((map_ne_zero _).2 k.ne_zero) (congrArg Subtype.val h0)
  have h3 := hχ.1 v (Units.mk0 _ hN0)
  unfold HChar.resFin at h3
  rw [MonoidHom.finset_prod_apply] at h3
  rw [← h3]
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [← map_mul]
  exact congrArg _ (Units.ext rfl)

theorem loc_transport (χ : HChar E) (hχ : TrivOnF χ) (P : HeightOneSpectrum (𝓞 E)) (x : (P.adicCompletion E)ˣ) :
    (transport conjE χ).loc P x = (χ.loc P x)⁻¹ := by
  have h := loc_eq_one_of_prod (χ * transport conjE χ) _ (prod_locK_conj χ hχ (P.under (OF E)))
    (w := P) ((mem_aboveF _ P).2 rfl) x
  rw [HChar.loc_mul] at h
  exact eq_inv_of_mul_eq_one_right h

theorem unrAt_inv_iff (χ : HChar E) (hχ : TrivOnF χ) (P : HeightOneSpectrum (𝓞 E)) :
    χ⁻¹.UnrAt P ↔ χ.UnrAt (plMap conjE P) := by
  rw [← transport_unrAt_iff]
  unfold HChar.UnrAt
  simp only [HChar.loc_inv, loc_transport χ hχ]

theorem val_inv_eq (χ : HChar E) (hχ : TrivOnF χ) (P : HeightOneSpectrum (𝓞 E)) (h : χ.UnrAt (plMap conjE P)) :
    χ⁻¹.val P = χ.val (plMap conjE P) := by
  rw [← transport_val conjE χ P h]
  show (χ.loc P _)⁻¹ = (transport conjE χ).loc P _
  rw [loc_transport χ hχ]

theorem eulerFactor_inv (χ : HChar E) (hχ : TrivOnF χ) (s : ℂ) (P : HeightOneSpectrum (𝓞 E)) :
    eulerFactor χ⁻¹ s P = eulerFactor χ s (plMap conjE P) := by
  unfold eulerFactor
  by_cases h : χ.UnrAt (plMap conjE P)
  · rw [if_pos ((unrAt_inv_iff χ hχ P).2 h), if_pos h, val_inv_eq χ hχ P h, absNorm_plMap]
  · rw [if_neg (fun h' => h ((unrAt_inv_iff χ hχ P).1 h')), if_neg h]

end GlobalTheory.CMVal.InvConj

open Formalism.L2.Host.CT GlobalTheory.CMVal.InvConj in

theorem GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E)
    (Λ : ℂ → ℂ), TrivOnF χ → IsHeckeL χ Λ → IsHeckeL χ⁻¹ Λ := by
  intro E _ _ _ χ Λ hχ hL
  refine ⟨hL.1, fun s hs => ?_⟩
  let e : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E) :=
    ⟨plMap conjE, plMap (conjE (E := E)).symm, plMap_symm_plMap conjE, plMap_plMap_symm conjE⟩
  have he : eulerFactor χ⁻¹ s = eulerFactor χ s ∘ e := funext fun P => eulerFactor_inv χ hχ s P
  rw [he, Equiv.hasProd_iff]
  exact hL.2 s hs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiLogarithmModIdealTopLinearCombination
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem ql_comb_top : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → ∀ w : ι → B, QL μ ⊤ (comb w e) := by
  intro B O Q _ _ _ _ θ d μ hμ ι _ e he w
  have hc : ∀ i, constantCoeff (up Q μ i) = 0 := by
    intro i
    simp [up, hμ.const i]
  have hzero : QL μ ⊤ (0 : MvPowerSeries (Fin d) Q) := by
    refine ⟨by simp, fun i => ⟨0, Submodule.mem_top, by simp [lin]⟩, fun α => ⟨0, Submodule.mem_top, ?_⟩⟩
    have := formalCoboundary_smul hc (0 : Q) 0
    rw [zero_smul, zero_smul] at this
    rw [this]; simp
  have hadd : ∀ f g : MvPowerSeries (Fin d) Q, QL μ ⊤ f → QL μ ⊤ g → QL μ ⊤ (f + g) := by
    rintro f g ⟨hf0, hf1, hf2⟩ ⟨hg0, hg1, hg2⟩
    refine ⟨by simp [hf0, hg0], fun i => ?_, fun α => ?_⟩
    · obtain ⟨a, -, ha⟩ := hf1 i
      obtain ⟨b, -, hb⟩ := hg1 i
      exact ⟨a + b, Submodule.mem_top, by simp only [lin, map_add] at ha hb ⊢; rw [ha, hb]⟩
    · obtain ⟨a, -, ha⟩ := hf2 α
      obtain ⟨b, -, hb⟩ := hg2 α
      exact ⟨a + b, Submodule.mem_top, by rw [formalCoboundary_add hc, map_add, ha, hb, map_add]⟩
  have hsmul : ∀ (c : B) (f : MvPowerSeries (Fin d) Q), QL μ ⊤ f → QL μ ⊤ (algebraMap B Q c • f) := by
    rintro c f ⟨hf0, hf1, hf2⟩
    refine ⟨by simp [hf0], fun i => ?_, fun α => ?_⟩
    · obtain ⟨a, -, ha⟩ := hf1 i
      refine ⟨c * a, Submodule.mem_top, ?_⟩
      simp only [lin, map_smul, smul_eq_mul] at ha ⊢
      rw [ha, map_mul]
    · obtain ⟨a, -, ha⟩ := hf2 α
      refine ⟨c * a, Submodule.mem_top, ?_⟩
      rw [formalCoboundary_smul hc, map_smul, smul_eq_mul, ha, map_mul]
  unfold comb
  exact Finset.sum_induction _ (QL μ ⊤) hadd hzero fun i _ => hsmul (w i) (e i) (he i)

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSSecGlueSectionByPartitionOfHolo
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem glue_isSSec_of_holo : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type)
    [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La)
    (u : Fin C.m → V n → ℂ), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) →
    A.IsSSec (A.kap + la) (glue C la u) := by
  intro n Y _ _ _ _ _ ι La _ A C la u hu
  refine ⟨fun i => ?_, fun i j y hi hj => ?_⟩
  · have key : ∀ a, ContDiffOn ℝ ∞ (fun v => (C.chi a ((A.chart i).symm v) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) *
        u a (A.chart (C.idx a) ((A.chart i).symm v))) (A.chart i).target := by
      intro a v hv
      apply ContDiffAt.contDiffWithinAt
      by_cases hy : (A.chart i).symm v ∈ tsupport (C.chi a)
      · have hs := C.supp a hy
        have hovo : IsOpen (ovl A.chart i (C.idx a)) :=
          (A.chart i).isOpen_inter_preimage_symm (A.chart (C.idx a)).open_source
        have hvov : v ∈ ovl A.chart i (C.idx a) := ⟨hv, hs.1⟩
        have hUo : IsOpen (ovl A.chart i (C.idx a) ∩
            (A.chart (C.idx a) ∘ (A.chart i).symm) ⁻¹' ball (C.c a) (C.r a)) :=
          (A.holo_trans i (C.idx a)).continuousOn.isOpen_inter_preimage hovo isOpen_ball
        have hvU : v ∈ ovl A.chart i (C.idx a) ∩
            (A.chart (C.idx a) ∘ (A.chart i).symm) ⁻¹' ball (C.c a) (C.r a) := ⟨hvov, hs.2⟩
        have h1 : ContDiffAt ℝ ∞ (C.chi a ∘ (A.chart i).symm) v :=
          (C.smooth a i).contDiffAt ((A.chart i).open_target.mem_nhds hv)
        have h1' : ContDiffAt ℝ ∞ (fun v => (C.chi a ((A.chart i).symm v) : ℂ)) v :=
          Complex.ofRealCLM.contDiff.contDiffAt.comp v h1
        have h2 : ContDiffAt ℝ ∞ (A.g (A.kap + la) i (C.idx a) ∘ (A.chart i).symm) v :=
          hyq_contDiffAt_of_holo hovo (A.holo_g _ _ _) hvov
        have h3 : ContDiffAt ℝ ∞ (u a ∘ (A.chart (C.idx a) ∘ (A.chart i).symm)) v :=
          hyq_contDiffAt_of_holo hUo ((hu a).comp
            ((A.holo_trans i (C.idx a)).mono Set.inter_subset_left) (fun w hw => hw.2)) hvU
        exact (h1'.mul h2).mul h3
      · have hn : (tsupport (C.chi a))ᶜ ∈ 𝓝 ((A.chart i).symm v) :=
          (isClosed_tsupport _).isOpen_compl.mem_nhds hy
        have h2 : ∀ᶠ w in 𝓝 v, (A.chart i).symm w ∉ tsupport (C.chi a) :=
          ((A.chart i).continuousAt_symm hv).preimage_mem_nhds hn
        refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [h2] with w hw
        simp [image_eq_zero_of_notMem_tsupport hw]
    have he : (glue C la u i ∘ (A.chart i).symm) = fun v => ∑ a, (C.chi a ((A.chart i).symm v) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) *
        u a (A.chart (C.idx a) ((A.chart i).symm v)) := by
      funext v; simp [glue]
    rw [he]
    exact ContDiffOn.sum fun a _ => key a
  · simp only [glue]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : C.chi a y = 0
    · simp [h]
    · have hk := (C.supp a (subset_tsupport _ h)).1
      rw [A.g_cocycle (A.kap + la) i j (C.idx a) y hi hj hk]
      ring

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegers
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FrameIntegers

theorem isFrame_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → IsFrame p C (RingHom.id O) := by
  intro p hp C _ _ _ v O _ _ hnu _ _ hv
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hmapp : algebraMap O C (p : O) = (p : C) := map_natCast _ _
  have hvp1 : v (p : C) < 1 := by
    have h1 := hv.map_le_one (p : O)
    rw [hmapp] at h1
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exact absurd (hv.isUnit_of_one (by rw [hmapp]; exact Ne.isUnit hpC) (by rw [hmapp]; exact h)) hnu.out
  have hint : ∀ z : ℤ, v (z : C) ≤ 1 := by
    intro z
    have := hv.map_le_one (z : O)
    rwa [map_intCast] at this
  refine ⟨Function.surjective_id, hv.hom_inj, ?_, Ne.isUnit hpC, ?_, ?_, ?_, inferInstance⟩
  · intro q
    obtain ⟨k, hk⟩ : ∃ k : ℕ, v (p : C) ^ k * v q ≤ 1 := by
      by_cases hq : v q = 0
      · exact ⟨0, by simp [hq]⟩
      · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr (pos_iff_ne_zero.mpr hq)) hvp1
        refine ⟨k, ?_⟩
        calc v (p : C) ^ k * v q ≤ (v q)⁻¹ * v q := mul_le_mul_of_nonneg_right hk.le zero_le
          _ = 1 := inv_mul_cancel₀ hq
    have hle : v ((p : C) ^ k * q) ≤ 1 := by rw [map_mul, map_pow]; exact hk
    obtain ⟨b, hb⟩ := hv.exists_of_le_one hle
    exact ⟨k, b, hb.symm⟩
  · intro n hn
    have hB : (n : C) * (Nat.gcdA n p : C) + (p : C) * (Nat.gcdB n p : C) = 1 := by
      have h := Nat.gcd_eq_gcd_ab n p
      rw [Nat.Coprime.gcd_eq_one hn] at h
      exact_mod_cast h.symm
    have hvn : v (n : C) = 1 := by
      have h1 : v (n : C) ≤ 1 := by exact_mod_cast hint n
      by_contra hne
      have hlt : v (n : C) < 1 := lt_of_le_of_ne h1 hne
      have a1 : v ((n : C) * (Nat.gcdA n p : C)) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hlt
      have a2 : v ((p : C) * (Nat.gcdB n p : C)) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hvp1
      have := Valuation.map_add_lt v a1 a2
      rw [hB, map_one] at this
      exact lt_irrefl _ this
    have hnC : (n : C) ≠ 0 := by
      intro h; rw [h, map_zero] at hvn; exact zero_ne_one hvn
    have hmapn : algebraMap O C (n : O) = (n : C) := map_natCast _ _
    exact hv.isUnit_of_one (by rw [hmapn]; exact Ne.isUnit hnC) (by rw [hmapn]; exact hvn)
  · intro x hx
    simp only [RingHom.id_apply] at hx
    subst hx
    exact ⟨0, rfl, by simp [hp0]⟩
  · intro a ha
    have hpO : (p : O) ≠ 0 := by
      intro h; apply hpC; rw [← hmapp, h, map_zero]
    exact (mul_eq_zero.mp ha).resolve_left hpO

end GlobalTheory.FrameIntegers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDetIsFrameOnCanonicalWeight
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem jdet_isFrameOn_kap : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → A.IsFrameOn A.kap U (jdet A z) := by
  intro n Y _ _ _ _ _ ι La _ A U z hz
  refine ⟨⟨fun i => ?_, fun i j y hy hi hj => ?_⟩, fun y hy => hz.det_ne _ y hy (A.mem_pick y)⟩
  · set S := (A.chart i).target ∩ (A.chart i).symm ⁻¹' U with hS
    have hSo : IsOpen S := (A.chart i).isOpen_inter_preimage_symm hz.isOpen
    have hk : ∀ k, ContDiffOn ℂ ∞ (fun v => (z ((A.chart i).symm v)) k) S := fun k =>
      contDiffOn_of_differentiableOn n _ S hSo (fun v hv =>
        (EuclideanSpace.proj k : V n →L[ℂ] ℂ).differentiableAt.comp_differentiableWithinAt v
          (hz.holo i v hv))
    have hpi := contDiffOn_pi.mpr hk
    have h1 : ContDiffOn ℂ ∞ (z ∘ (A.chart i).symm) S :=
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.contDiff.comp_contDiffOn hpi
    have h2 : ContDiffOn ℂ ∞ (fderiv ℂ (z ∘ (A.chart i).symm)) S :=
      h1.fderiv_of_isOpen hSo (by simp)
    have h3 : DifferentiableOn ℂ (fun v => (fderiv ℂ (z ∘ (A.chart i).symm) v).det) S := by
      intro v hv
      exact ((flL_det_contDiffAt ((h2 v hv).contDiffAt (hSo.mem_nhds hv))).differentiableAt
        (by simp)).differentiableWithinAt
    refine h3.congr fun v hv => ?_
    simp only [Function.comp_apply, jdet, jz, (A.chart i).right_inv hv.1]
  · have hyt : A.chart i y ∈ (A.chart i).target := (A.chart i).map_source hi
    have hov : IsOpen (ovl A.chart i j) :=
      (A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source
    have hmov : A.chart i y ∈ ovl A.chart i j := ⟨hyt, by simp [(A.chart i).left_inv hi, hj]⟩
    have hτ : DifferentiableAt ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y) :=
      (A.holo_trans i j).differentiableAt (hov.mem_nhds hmov)
    have hτy : (A.chart j ∘ (A.chart i).symm) (A.chart i y) = A.chart j y := by
      simp [(A.chart i).left_inv hi]
    have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
      (A.chart j).isOpen_inter_preimage_symm hz.isOpen
    have hmj : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
      ⟨(A.chart j).map_source hj, by simp [(A.chart j).left_inv hj, hy]⟩
    have hzj : DifferentiableAt ℂ (z ∘ (A.chart j).symm) ((A.chart j ∘ (A.chart i).symm) (A.chart i y)) := by
      rw [hτy]; exact (hz.holo j).differentiableAt (hSo.mem_nhds hmj)
    have hev : z ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i y)]
        (z ∘ (A.chart j).symm) ∘ (A.chart j ∘ (A.chart i).symm) := by
      filter_upwards [hov.mem_nhds hmov] with v hv
      simp only [Function.comp_apply, (A.chart j).left_inv hv.2]
    have hjz : jz A z i y = (jz A z j y).comp (fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y)) := by
      unfold jz
      rw [hev.fderiv_eq, fderiv_comp _ hzj hτ, hτy]
    simp only [jdet]
    rw [hjz, A.g_kap i j y hi hj]
    exact (LinearMap.det_comp _ _).trans (mul_comm _ _)

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerBoundaryLineBundleFirstChernClass
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.KumPic

theorem kummer_boundary_picClass : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0), Mono κ →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U))) →
  ∀ (z : Cocycle (res ℤ (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1) (s : ℤˣ),
  (∀ (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0) (ψ : cokernel κ ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 1),
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) → cokernel.π κ ≫ ψ = φ ≫ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).d 0 1 →
      ∀ w : Cocycle (sgl (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1, sglι (cokernel κ) ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug (cokernel κ))) z (zero_add 1)) = s • CohomologyClass.mk w) →
  ∀ (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ y : H ℤ E (cokernel κ) 1,
    HK.post ℤ _ (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) 1 y = picClass L →
    HK.ext ℤ _ z 1 (1 + 1) rfl y = s • restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) := by
  intro q _ κ h0 _ h2 _ _ h5 z s hz E L hE y hy
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_cocycle_lifting_lineBundle_transition_units q (cokernel κ) _ E L hE h5
  have hy' : y = CohomologyClass.mk (zcomp a (Cocycle.ofHom (resAug (cokernel κ))) (add_zero 1)) :=
    (GlobalTheory.T.etaleCohomology_bijective_of_support_bijective ℤ E _ (fun U hU => h5 U (hE U hU)) 1).1 (hy.trans (GlobalTheory.T.kummerLiftedCocycle_image_eq_picardClass _ _ E L a ha).symm)
  haveI : Injective ((res ℤ (twZ q)).X 0) :=
    inferInstanceAs (Injective ((injectiveResolution (twZ q)).cochainComplex.X 0))
  let φ : Gm ⟶ (res ℤ (twZ q)).X 0 := Injective.factorThru (resι ℤ (twZ q)) κ
  have hφ : κ ≫ φ = resι ℤ (twZ q) := Injective.comp_factorThru _ _
  have hd : κ ≫ (φ ≫ (res ℤ (twZ q)).d 0 1) = 0 := by
    rw [← Category.assoc, hφ, PicSpec.resι_d]
  let ψ : cokernel κ ⟶ (res ℤ (twZ q)).X 1 := cokernel.desc κ (φ ≫ (res ℤ (twZ q)).d 0 1) hd
  have hψ : cokernel.π κ ≫ ψ = φ ≫ (res ℤ (twZ q)).d 0 1 := cokernel.π_desc _ _ _
  have hψd : ψ ≫ (res ℤ (twZ q)).d 1 2 = 0 := by
    rw [← cancel_epi (cokernel.π κ), ← Category.assoc, hψ, Category.assoc, HomologicalComplex.d_comp_d,
      comp_zero, comp_zero]
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_cocycle_of_map_to_degreeOne_term (cokernel κ) (res ℤ (twZ q)) ψ hψd
  have hzw := hz φ ψ hφ hψ w hw
  have hext : HK.ext ℤ _ z 1 (1 + 1) rfl y = s • CohomologyClass.mk (zcomp a w rfl) := by
    rw [hy']
    change CohomologyClass.mk (zcomp (zcomp a (Cocycle.ofHom (resAug _)) (add_zero 1)) z rfl) = _
    have hc : zcomp (zcomp a (Cocycle.ofHom (resAug (cokernel κ))) (add_zero 1)) z rfl =
        zcomp a (zcomp (Cocycle.ofHom (resAug _)) z (zero_add 1)) rfl :=
      Cocycle.ext (Cochain.comp_assoc _ _ _ (add_zero 1) (zero_add 1) (by omega))
    rw [hc, ← cpre_mk, hzw]
    rw [Units.smul_def, Units.smul_def, map_zsmul]
    rfl
  rw [hext]
  congr 1
  refine GlobalTheory.T.kummerCocycle_sub_chernClass_coboundary q E L hE φ (GlobalTheory.T.kummerSplittingDefect_glue_qthRoots q φ (GlobalTheory.T.kummerSplittingDefect_eq_of_pow_eq q κ h2 φ hφ)) (cokernel κ) a w (fun U x v hv => ?_)
  obtain ⟨c, hc, hac⟩ := ha U x
  have hU : IsUnit (q : Γ(U, ⊤)) := hE U ⟨x.face 0⟩
  have hpow : ∀ n : ℕ, unitSec (v ^ n) = (n : ℤ) • unitSec v := by
    intro n
    induction n with
    | zero =>
      have := PicSpec.unitSec_mul (1 : (Γ(U, ⊤))ˣ) 1
      rw [mul_one] at this
      simpa using this
    | succ n ih => rw [pow_succ, PicSpec.unitSec_mul, ih]; push_cast; rw [add_smul, one_smul]
  have hcv : c = Sec.map (cokernel.π κ) (unitSec v) := by
    refine (h5 U hU).1 (hc.trans ?_)
    rw [PicSpec.sec_map_comp, cokernel.π_desc, ← hv, hpow]
    exact (map_zsmul (CupSpec.mapHom Gm Gm (unitSec v)) (q : ℤ) (𝟙 Gm)).symm
  rw [hac, PicSpec.sec_map_comp, hw, hcv, PicSpec.sec_map_comp, hψ]
  rfl

end GlobalTheory.EtC.KumPic

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSublevelTailLeOfFiniteStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_sublevel_tail_le_of_finite : ∀ (Y : Type) [MeasurableSpace Y] (μ : Measure Y) (g : Y → ℝ≥0∞) (x : Y → ℝ), Measurable x → ∫⁻ y, g y ∂μ < ⊤ → Measurable g → ∀ ε : ℝ≥0∞, 0 < ε → ∃ T0 : ℝ, ∀ T, T0 ≤ T → ∫⁻ y in {y | x y ≤ -T + 1}, g y ∂μ ≤ ε := by
  first | exact @GlobalTheory.lintegral_sublevel_tail_le | exact GlobalTheory.lintegral_sublevel_tail_le | (intros; apply GlobalTheory.lintegral_sublevel_tail_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRulesStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ : Type), (∀ (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ 1 ↔ ∃ g, Red p f g) ∧ (∀ (f : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f g' → g = g') ∧ (∀ g : MvPowerSeries σ k, Red p (Katz.lift p g) g) ∧ (∀ (f f' : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f' g' → Red p (f + f') (g + g') ∧ Red p (f - f') (g - g')) ∧ (∀ (r : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)) g, Red p f g → Red p (r • f) (WittVector.constantCoeff r • g)) ∧ (∀ f : MvPowerSeries (σ) (Fr p k), f ∈ intBy p k σ p ↔ Red p f 0) ∧ (∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c ↔ ∃ g ∈ intBy p k σ 1, f = c • g) := by
  first | exact @GlobalTheory.Katz.red_rules | exact GlobalTheory.Katz.red_rules | (intros; apply GlobalTheory.Katz.red_rules <;> assumption)
end

