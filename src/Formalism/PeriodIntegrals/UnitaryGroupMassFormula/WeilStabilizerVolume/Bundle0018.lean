import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0014
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0010
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0012
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.FiniteNeighbourhoodSecond
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0011

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensInfTop
section
noncomputable section

namespace PI.VolStabW

theorem submLocal_holds : SubmLocal := submLocal_of linDens_holds changeVar_holds

theorem submDens_holds : SubmDens := submDens_of_local submLocal_holds

theorem densInf_of_coord (h : CoordInf) : DensInf := densInf_of submDens_holds h

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensVGlue
section
noncomputable section

namespace PI.VolStabW

open MeasureTheory Topology Set

theorem densCos_of_filt (hP1 : HenselCount) (hP2 : CosDens) {V X Y : Type} [AddCommGroup V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure]
    [ν.IsAddHaarMeasure] (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X)
    (hG : Continuous G) (hfG : ∀ v, f v = ι (G v)) (y : V) (Λ : ℕ → AddSubgroup V)
    (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V)) (hΛc : ∀ n, IsCompact (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (hHb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N) (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n)
    (hyp : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) :
    ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), {z | z - y ∈ Λ 0}.indicator (fun _ => (1 : ℝ)) v ∂μ =
        ∫ b in S, g b ∂ν := by
  have hHa : Antitone H := fun m n hmn => by
    rw [← hD, ← hD]
    exact AddSubgroup.map_mono (hΛa hmn)
  set Q : Set V := {z | z - y ∈ Λ 0} with hQ
  have hQm : MeasurableSet Q := ((hΛo 0).preimage (continuous_id.sub continuous_const)).measurableSet
  have hQf : μ Q ≠ ⊤ := (isCompact_cos (Λ 0) (hΛc 0) y).measure_lt_top.ne
  set C : Set X := {z | z - G y ∈ H 0} with hC
  have hCo : IsOpen C := (hHo 0).preimage (continuous_id.sub continuous_const)
  have hCcl : IsClosed C :=
    (AddSubgroup.isClosed_of_isOpen _ (hHo 0)).preimage (continuous_id.sub continuous_const)
  have hGm : Measurable G := hG.measurable
  set m : Measure X := (μ.restrict Q).map G with hm
  have : IsFiniteMeasure (μ.restrict Q) := ⟨by rw [Measure.restrict_apply_univ]; exact hQf.lt_top⟩
  have : IsFiniteMeasure m := by rw [hm]; infer_instance
  have hcos_m : ∀ (h : X) (n : ℕ), m {z | z - h ∈ H n} =
      μ {Z | Z ∈ Λ 0 ∧ G (y + Z) - h ∈ H n} := by
    intro h n
    have hmeas : MeasurableSet {z : X | z - h ∈ H n} :=
      ((hHo n).preimage (continuous_id.sub continuous_const)).measurableSet
    rw [hm, Measure.map_apply hGm hmeas, Measure.restrict_apply (hGm hmeas)]
    have : G ⁻¹' {z | z - h ∈ H n} ∩ Q =
        (fun X => -y + X) ⁻¹' {Z | Z ∈ Λ 0 ∧ G (y + Z) - h ∈ H n} := by
      ext X
      simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, hQ, neg_add_eq_sub]
      rw [add_sub_cancel]
      exact and_comm
    rw [this, measure_preimage_add]
  have hcos_ν : ∀ (h : X) (n : ℕ), ν {z | z - h ∈ H n} = ν (H n) := by
    intro h n
    have : {z | z - h ∈ H n} = (fun z => -h + z) ⁻¹' (H n : Set X) := by
      ext z
      simp [neg_add_eq_sub]
    rw [this, measure_preimage_add]
  have hH0 : ν (H 0) ≠ 0 := ((hHo 0).measure_pos ν ⟨0, (H 0).zero_mem⟩).ne'
  have hH0t : ν (H 0) ≠ ⊤ := (hHc 0).measure_lt_top.ne
  set κ : ENNReal := μ (Λ 0) * (ν (H 0))⁻¹ with hκ
  have hcos : ∀ n h, h - G y ∈ H 0 → m {z | z - h ∈ H n} = κ * ν {z | z - h ∈ H n} := by
    intro n h hh
    have e := hP1 V X μ ν inferInstance inferInstance Λ H hΛo hΛc hΛa hHo hHc D hD G y hyp n h hh
    rw [hcos_m, hcos_ν]
    calc μ {Z | Z ∈ Λ 0 ∧ G (y + Z) - h ∈ H n}
        = μ {Z | Z ∈ Λ 0 ∧ G (y + Z) - h ∈ H n} * (ν (H 0) * (ν (H 0))⁻¹) := by
          rw [ENNReal.mul_inv_cancel hH0 hH0t, mul_one]
      _ = μ {Z | Z ∈ Λ 0 ∧ G (y + Z) - h ∈ H n} * ν (H 0) * (ν (H 0))⁻¹ := (mul_assoc _ _ _).symm
      _ = μ (Λ 0) * ν (H n) * (ν (H 0))⁻¹ := by rw [e]
      _ = κ * ν (H n) := by rw [hκ]; ring
  have hCc : m Cᶜ = 0 := by
    rw [hm, Measure.map_apply hGm hCo.measurableSet.compl, Measure.restrict_apply (hGm hCo.measurableSet.compl)]
    have : G ⁻¹' Cᶜ ∩ Q = ∅ := by
      ext X
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, hC, hQ, mem_setOf_eq,
        mem_empty_iff_false, iff_false, not_and]
      intro hn hX
      have e1 := hyp 0 0 (Λ 0).zero_mem (X - y) hX
      have e2 : D (X - y) ∈ H 0 := by rw [← hD 0]; exact ⟨X - y, hX, rfl⟩
      have e3 := (H 0).add_mem (hHa (Nat.zero_le 1) e1) e2
      simp only [add_zero, add_sub_cancel] at e3
      exact hn (by simpa [sub_add_cancel] using e3)
    rw [this, measure_empty]
  have key := hP2 X ν m inferInstance H hHo hHc hHa hHb (G y) κ hCc hcos
  have hgc : Continuous (C.indicator fun _ => (1 : ℝ)) := by
    refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro b
    by_cases hb : b ∈ C
    · exact ⟨C, hCo, hb, fun b' hb' => by rw [indicator_of_mem hb', indicator_of_mem hb]⟩
    · exact ⟨Cᶜ, hCcl.isOpen_compl, hb, fun b' hb' => by
        rw [indicator_of_notMem hb', indicator_of_notMem hb]⟩
  refine ⟨fun b => κ.toReal * C.indicator (fun _ => (1 : ℝ)) b, continuous_const.mul hgc,
    fun S hS => ?_⟩
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hP : f ⁻¹' (ι '' S) = G ⁻¹' S := by
    ext X
    simp only [mem_preimage, mem_image, hfG]
    exact ⟨fun ⟨s, hs, e⟩ => hι e ▸ hs, fun h => ⟨G X, h, rfl⟩⟩
  rw [hP, integral_indicator_const _ hQm, integral_const_mul, integral_indicator_const _ hCo.measurableSet,
    Measure.real, Measure.real, Measure.restrict_apply hQm, Measure.restrict_apply hCo.measurableSet,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.toReal_mul]
  congr 1
  have e := key S hS
  rw [hm, Measure.map_apply hGm hSm, Measure.restrict_apply (hGm hSm)] at e
  rw [inter_comm, e, inter_comm]

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensVSt
section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology
open scoped TensorProduct

def TensNA : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  ∀ v : HeightOneSpectrum (𝓞 F), HasCOSub (Fin a → Fin M → Fv F v ⊗[F] E)

def DensVLC : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
      DensOn (IsLCcOn {X | LinearIndependent (Fv F v ⊗[F] E) X}) μv (gramR (Fv F v) σ J)
        Subtype.val νv

theorem densV_of (hT : TensAll) (hNA : TensNA) (hLC : DensVLC) : DensV := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν
  obtain ⟨t1, t2, t3, t4, _t5, _t6, t7⟩ := (hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).2 v
  have := hμ.1
  have := hν.1
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
    t4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  exact (densAll_iff _ _ _ _ _).2 (densApprox_lc μv _ _ νv _ t7
    (hNA F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet v)
    (hLC F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν))

def DensVCs : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
      DensCos μv (gramR (Fv F v) σ J) Subtype.val νv {X | LinearIndependent (Fv F v ⊗[F] E) X}

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ExStabOrb
section
namespace PI.VolStabW

theorem exStab_of_nu (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_orb orbTup_holds hI hF hN

end PI.VolStabW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.FibTop
section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct

def FreeOpen : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  IsOpen {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} ∧
  ∀ v : HeightOneSpectrum (𝓞 F),
    IsOpen {X : Fin a → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X}

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensHSt
section
noncomputable section

namespace PI.VolStabW

open MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def FibLat : Prop :=
  ∀ (V X Y : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
    ∀ (f : V → Y) (ι : X → Y), Function.Injective ι → ∀ (G : V → X), Continuous G →
    (∀ x, f x = ι (G x)) → ∀ (U : Set V) (B : Set X) (fib : X → Measure V),
    IsFibreFamily μ f ι U ν B fib → ∀ (T : X), B ∈ 𝓝 T → ∀ Nb ∈ 𝓝 T, (∀ x, G x ∈ Nb → x ∈ U) →
    ∀ (L : AddSubgroup V), IsOpen (L : Set V) → IsCompact (L : Set V) →
    ∀ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X), Λ 0 ≤ L →
      (∀ n, IsOpen (Λ n : Set V)) → (∀ n, IsCompact (Λ n : Set V)) → Antitone Λ →
      (∀ n, IsOpen (H n : Set X)) → (∀ n, IsCompact (H n : Set X)) →
      (∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N') →
      (∀ y ∈ L, G y - T ∈ H 0 → ∃ D : V →+ X, (∀ n, (Λ n).map D = H n) ∧
        ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) →
      ∫ x, (L : Set V).indicator (1 : V → ℂ) x ∂(fib T) =
        (((μ ((L : Set V) ∩ G ⁻¹' {z | z - T ∈ H 0})) / ν (H 0)).toReal : ℂ)

def FibLatGen : Prop :=
  ∀ (V X Y : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
    ∀ (f : V → Y) (ι : X → Y), Function.Injective ι → ∀ (G : V → X), Continuous G →
    (∀ x, f x = ι (G x)) → ∀ (U : Set V) (B : Set X) (fib : X → Measure V),
    IsFibreFamily μ f ι U ν B fib → ∀ (T : X), B ∈ 𝓝 T →
    ∀ (L : AddSubgroup V), IsOpen (L : Set V) → IsCompact (L : Set V) →
    ∀ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X), Λ 0 ≤ L →
      (∀ n, IsOpen (Λ n : Set V)) → (∀ n, IsCompact (Λ n : Set V)) → Antitone Λ →
      (∀ n, IsOpen (H n : Set X)) → (∀ n, IsCompact (H n : Set X)) →
      (∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N') →
    ∀ (P : Set V), P ⊆ L → (∀ y ∈ P, ∀ Z ∈ Λ 0, y + Z ∈ P) → IsOpen P → IsClosed P →
    ∀ Nb ∈ 𝓝 T, (∀ x ∈ P, G x ∈ Nb → x ∈ U) →
      (∀ y ∈ P, G y - T ∈ H 0 → ∃ D : V →+ X, (∀ n, (Λ n).map D = H n) ∧
        ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) →
      ∫ x, P.indicator (1 : V → ℂ) x ∂(fib T) =
        (((μ (P ∩ G ⁻¹' {z | z - T ∈ H 0})) / ν (H 0)).toReal : ℂ)

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensQ
section
noncomputable section

namespace PI.VolStabW

open NumberField IsDedekindDomain Filter Asymptotics
open scoped nonZeroDivisors

namespace LocalCountingSum

variable (K : Type) [Field K] [NumberField K]

def cnt (n : ℕ) : ℝ := (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ)

theorem sum_cnt (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, cnt K k =
    (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by
  classical
  simp only [cnt, ← Nat.cast_sum]
  congr 1
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem sum_cnt_bigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, cnt K k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  simp only [sum_cnt, Real.rpow_one]
  have ht := (Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
  simp only [Function.comp_def, Nat.cast_le] at ht
  refine isBigO_of_div_tendsto_nhds
    (f := fun n : ℕ ↦ (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ))
    (g := fun n : ℕ ↦ (n : ℝ)) ?_ _ ht
  filter_upwards [eventually_ne_atTop 0] with n hn h
  exact absurd h (by exact_mod_cast hn)

theorem cnt_summable : Summable fun n : ℕ ↦ cnt K n / (n : ℝ) ^ 2 := by
  have hL := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := 2) (sum_cnt_bigO K)
    (fun n ↦ by unfold cnt; positivity) zero_le_one (by norm_num)
  refine hL.norm.congr fun n ↦ ?_
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by unfold cnt; positivity)]
    norm_num

end LocalCountingSum

theorem qV_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    qV v = (Ideal.absNorm v.asIdeal : ℝ) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem qvSum_holds : QvSum := by
  intro F _ _
  classical
  have hc := LocalCountingSum.cnt_summable F
  refine summable_of_sum_le (c := ∑' n, LocalCountingSum.cnt F n / (n : ℝ) ^ 2)
    (fun v ↦ by simp only [Pi.zero_apply]; positivity) fun S ↦ ?_
  let N : HeightOneSpectrum (𝓞 F) → ℕ := fun v ↦ Ideal.absNorm v.asIdeal
  have e1 : ∑ v ∈ S, (qV v)⁻¹ ^ 2 = ∑ v ∈ S, ((N v : ℝ))⁻¹ ^ 2 :=
    Finset.sum_congr rfl fun v _ ↦ by rw [qV_eq]
  rw [e1, Finset.sum_comp (fun n : ℕ ↦ ((n : ℝ))⁻¹ ^ 2) N]
  have hcard : ∀ n, ((S.filter fun v ↦ N v = n).card : ℝ) ≤ LocalCountingSum.cnt F n := by
    intro n
    unfold LocalCountingSum.cnt
    have : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    have hinj : Function.Injective
        (fun v : (S.filter fun v ↦ N v = n) ↦
          (⟨v.1.asIdeal, (Finset.mem_filter.mp v.2).2⟩ :
            {I : Ideal (𝓞 F) // Ideal.absNorm I = n})) := by
      intro x y h
      apply Subtype.ext
      apply HeightOneSpectrum.ext
      exact congrArg Subtype.val h
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card, Fintype.card_coe] at this
    exact_mod_cast this
  calc ∑ n ∈ S.image N, (S.filter fun v ↦ N v = n).card • ((n : ℝ))⁻¹ ^ 2
      ≤ ∑ n ∈ S.image N, LocalCountingSum.cnt F n / (n : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun n _ ↦ ?_
        rw [nsmul_eq_mul, div_eq_mul_inv, inv_pow]
        exact mul_le_mul_of_nonneg_right (hcard n) (by positivity)
    _ ≤ ∑' n, LocalCountingSum.cnt F n / (n : ℝ) ^ 2 :=
        hc.sum_le_tsum _ fun n _ ↦ by unfold LocalCountingSum.cnt; positivity

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensSA
section
noncomputable section

open IsDedekindDomain NumberField

namespace PI.VolStabW

def SAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (U : AddSubgroup (FiniteAdeleRing (𝓞 F) F)),
    IsOpen (U : Set (FiniteAdeleRing (𝓞 F) F)) →
    ∀ x : FiniteAdeleRing (𝓞 F) F, ∃ a : F, x - algebraMap F (FiniteAdeleRing (𝓞 F) F) a ∈ U

theorem sAf_holds : SAf := by
  intro F _ _ U hU x
  obtain ⟨m, hm, hmx⟩ := PIW.AdelClassFin.DictRing.af_denom x
  obtain ⟨N, hN1, hNU⟩ := PI.InvTopW.finite_neighbourhood_second F U (hU.mem_nhds U.zero_mem)
  obtain ⟨β, y, hy, hxy⟩ := PIW.AdelClassFin.DictRing.af_approx _ hmx (m * N)
    (Nat.mul_pos hm (by omega))
  refine ⟨(β : F) / (m : F), ?_⟩
  have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  have hu : IsUnit (algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F)) :=
    (IsUnit.mk0 _ hmF).map _
  have key : x - algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / (m : F)) =
      (N : FiniteAdeleRing (𝓞 F) F) * y := by
    apply hu.mul_left_cancel
    have e1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) = (m : FiniteAdeleRing (𝓞 F) F) :=
      map_natCast _ m
    have e2 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / (m : F)) =
        algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) β := by
      rw [← map_mul, mul_div_cancel₀ _ hmF, IsScalarTower.algebraMap_apply (𝓞 F) F]
    rw [mul_sub, e2, e1]
    rw [hxy]
    push_cast
    ring
  rw [key]
  exact hNU y hy

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.NuInvLoc
section
noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

def GramPres : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ (g : HA (AF F) σ J) (X : Fin a → Fin M → AF F ⊗[F] E),
    gramR (AF F) σ J (g • X) = gramR (AF F) σ J X

def PullLoc : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ (g : HA (AF F) σ J) (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    ∃ (Φinf' : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf' : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv' : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      Continuous Φinf' ∧ HasCompactSupport Φinf' ∧ IsPureFin b Φf' Φv' ∧
      IsProdInfFin (fun X => Φ (g • X)) Φinf' Φf' ∧
      (∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
        ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
        ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
        IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
          {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
        ∫ X, Φinf' X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) =
          ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
        ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
        ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
        IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
          {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
        ∫ X, Φv' v X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
          ∫ X, Φv v X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)))

theorem omInv_of (hG : GramPres) (hP : PullLoc) : OmInv := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν g
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hm : Measurable (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) :=
    (continuous_smul_tup σ J g).measurable
  have hG' := hG F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet g
  refine ⟨?_, ?_⟩
  · have hS : MeasurableSet {X : Fin a → Fin M → AF F ⊗[F] E |
        gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} :=
      (isClosed_eq (continuous_gramR (AF F) σ J) continuous_const).measurableSet.compl
    rw [Measure.map_apply hm hS]
    have e : (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) ⁻¹'
        {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} =
        {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} := by
      ext X
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hG' X]
    rw [e]
    exact hν.1
  obtain ⟨⟨μinf, hμinf⟩, a1⟩ := hν.2
  refine ⟨⟨μinf, hμinf⟩, fun μinf hμinf => ?_⟩
  obtain ⟨⟨νinf, hνinf⟩, a2⟩ := a1 μinf hμinf
  refine ⟨⟨νinf, hνinf⟩, fun νinf hνinf => ?_⟩
  obtain ⟨⟨μv, hμv⟩, a3⟩ := a2 νinf hνinf
  refine ⟨⟨μv, hμv⟩, fun μv hμv => ?_⟩
  obtain ⟨⟨νv, hνv⟩, a4⟩ := a3 μv hμv
  refine ⟨⟨νv, hνv⟩, fun νv hνv => ?_⟩
  obtain ⟨⟨fibInf, hfi⟩, a5⟩ := a4 νv hνv
  refine ⟨⟨fibInf, hfi⟩, fun fibInf hfi => ?_⟩
  obtain ⟨⟨fibV, hfv⟩, a6⟩ := a5 fibInf hfi
  refine ⟨⟨fibV, hfv⟩, fun fibV hfv => ?_⟩
  intro d b Φ Φinf Φf Φv hcΦ hcs hpure hprod
  obtain ⟨Φinf', Φf', Φv', hc', hcs', hpure', hprod', hI, hV⟩ :=
    hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ g d b Φ Φinf Φf Φv hcΦ hcs hpure hprod
  obtain ⟨hint, hmult, heq⟩ := a6 fibV hfv d b (fun X => Φ (g • X)) Φinf' Φf' Φv' hc' hcs' hpure'
    hprod'
  have hΦm : Measurable Φ :=
    TopoMeas.measurable_adm Φ ⟨d, b, Φinf, Φf, Φv, hcΦ, hcs, hpure, hprod⟩
  have eI := hI μinf hμinf νinf hνinf fibInf hfi
  have eV : (fun v => ∫ X, Φv' v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) =
      fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) :=
    funext fun v => hV v (μv v) (hμv v) (νv v) (hνv v) (fibV v) (hfv v)
  refine ⟨(integrable_map_measure hΦm.aestronglyMeasurable hm.aemeasurable).2 hint, ?_, ?_⟩
  · rw [← eV]; exact hmult
  · rw [integral_map hm.aemeasurable hΦm.aestronglyMeasurable, ← eI, ← eV]
    exact heq

theorem nuInv_of_loc (hG : GramPres) (hP : PullLoc) (hD : DetAdm) : NuInv :=
  nuInv_of (omUniq_of hD) (omInv_of hG hP)

end PI.VolStabW
end
end

