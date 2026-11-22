import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0007

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfTop
section
noncomputable section

namespace PI.VolStabS

theorem submLocal_holds : SubmLocal := submLocal_of linDens_holds changeVar_holds

theorem submDens_holds : SubmDens := submDens_of_local submLocal_holds

theorem densInf_of_coord (h : CoordInf) : DensInf := densInf_of submDens_holds h

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVGlue
section
noncomputable section

namespace PI.VolStabS

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

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVSt
section
noncomputable section

namespace PI.VolStabS

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

theorem densVLC_of (hT : TensAll) (hNA : TensNA) (hC : DensVCs) : DensVLC := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν
  obtain ⟨_t1, t2, _t3, _t4, _t5, _t6, _t7⟩ := (hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).2 v
  have := hμ.1
  have := hν.1
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  exact densLC_of_cos _ (hNA F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet v)
    (hC F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν)

theorem densV_of_cos (hT : TensAll) (hNA : TensNA) (hC : DensVCs) : DensV :=
  densV_of hT hNA (densVLC_of hT hNA hC)

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabOrb
section
namespace PI.VolStabS

theorem exStab_of_nu (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_orb orbTup_holds hI hF hN

end PI.VolStabS
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InvariantStabilizerAssembly
section
noncomputable section

namespace PI.VolStabS.InvariantStabilizerAssembly

open PI.VolStabS MeasureTheory Measure Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.VolFromSW
open scoped TensorProduct

theorem invStab_of_lamEx (hLam : LamEx) : InvStab := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ''
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  obtain ⟨μ, hμ⟩ := hSWa1.1
  have : μ.IsHaarMeasure := hμ
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J hSWa1
  have : IsMulRightInvariant μ :=
    unimod_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ hμ
  have hcl := us_isClosed_stab F E σ M a J X0
  have : LocallyCompactSpace (stabT (AF F) σ J X0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SigmaCompactSpace (stabT (AF F) σ J X0) := hcl.sigmaCompactSpace
  obtain ⟨lam, μ0, hμ0, hC, -⟩ :=
    hLam F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ hμ
  let s : (Fin a → Fin M → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
    if h : ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) X0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) X0 = y) →
      s y • ratTup (F := F) (AF F) X0 = y := by
    intro y h
    simp only [s, dif_pos h]
    exact h.choose_spec
  have : IsMulRightInvariant μ0 :=
    us_rightInv_of_compat μ (stabT (AF F) σ J X0).subtype μ0 lam s (fun f hf => hC.2 f hf s hs)
  have hc : μ'' = haarScalarFactor μ'' μ0 • μ0 := um_eq_smul_of_sigmaCompact μ'' μ0
  have : IsMulRightInvariant μ'' := by
    refine ⟨fun k => ?_⟩
    rw [hc, Measure.map_smul, map_mul_right_eq_self]
  exact us_invInv μ''

theorem invStab_of_finVol (hFV : FinVolStab) : InvStab := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ''
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hcl := us_isClosed_stab F E σ M a J X0
  have : LocallyCompactSpace (stabT (AF F) σ J X0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : Countable (HFinIn (AF F) σ J) := um_countable_HFinIn F E σ M J
  let f : ratIn F E σ M J (stabT (AF F) σ J X0) → HFinIn (AF F) σ J := fun x =>
    ⟨((x : stabT (AF F) σ J X0) : HA (AF F) σ J),
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext e)
  have : Countable (ratIn F E σ M J (stabT (AF F) σ J X0)) := hinj.countable
  obtain ⟨𝓕, h𝓕⟩ :=
    exFDStab_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ''
  have hfin := hFV F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ'' hμ'' 𝓕 h𝓕
  have : SigmaCompactSpace (stabT (AF F) σ J X0) :=
    um_sigmaCompact (ratIn F E σ M J (stabT (AF F) σ J X0)) μ'' 𝓕 h𝓕 hfin
  have : IsMulRightInvariant μ'' :=
    um_rightInv (ratIn F E σ M J (stabT (AF F) σ J X0)) μ'' 𝓕 h𝓕 hfin
  exact us_invInv μ''

end PI.VolStabS.InvariantStabilizerAssembly
end
end

