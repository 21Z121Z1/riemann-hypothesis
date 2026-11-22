import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.SdNormHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitScale
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0028
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0029
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0028
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0022
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0004
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdSd
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.SdW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
  PI.UnitaryGroupMassFormula.LocJacTyp.Sd.finDim

theorem boxScaleL_holds : BoxScaleL := by
  intro F E _ _ _ _ _ v ι _ hE μ _ x hx
  classical
  let z : ι → Fv F v ⊗[F] E := fun i => LocVol.sc v (x i)
  let f := PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL v z
  have hLM := PI.NglqJacSplitW.linModulusV_of
    (PI.NglqJacSplitW.linModulus_of PI.NglqJacSplitW.diagonal_one_jacobian)
  have hrank : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hE
  have hdet : LinearMap.det f = ∏ i, x i ^ 2 := by
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.BM.det_mulL]
    refine Finset.prod_congr rfl fun i _ => ?_
    change Algebra.norm (Fv F v) (algebraMap (Fv F v) (Fv F v ⊗[F] E) (x i)) = _
    rw [Algebra.norm_algebraMap, hrank]
  have hdet0 : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hx i)
  set S := Set.univ.pi fun i : ι => {c : Fv F v ⊗[F] E | LocVol.sc v (x i) * c ∈ LocVol.OEv v} with hSdef
  have hpre : S = f ⁻¹' (Set.univ.pi fun _ : ι => LocVol.OEv v) := by
    ext y
    simp [S, f, z, PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL_apply]
  have hcont : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have hS : MeasurableSet S := by
    rw [hpre]
    refine (IsOpen.preimage hcont ?_).measurableSet
    exact isOpen_set_pi Set.finite_univ fun i _ => PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_oev (E := E) v
  have himg : f '' S = Set.univ.pi fun _ : ι => LocVol.OEv v := by
    rw [hpre, Set.image_preimage_eq]
    intro y
    refine ⟨fun i => ((x i)⁻¹ ⊗ₜ[F] (1 : E)) * y i, ?_⟩
    funext i
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL_apply]
    change (x i ⊗ₜ[F] (1 : E)) * (((x i)⁻¹ ⊗ₜ[F] (1 : E)) * y i) = y i
    rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ (hx i), one_mul,
      ← Algebra.TensorProduct.one_def, one_mul]
  let b := Module.finBasis (Fv F v) (ι → Fv F v ⊗[F] E)
  let e0 := b.equivFun
  let e : (ι → Fv F v ⊗[F] E) ≃L[Fv F v] (Fin (Module.finrank (Fv F v) (ι → Fv F v ⊗[F] E)) → Fv F v) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  have h := hLM (Fv F v) (ι → Fv F v ⊗[F] E) (Fin _) ⟨e⟩ f hdet0 μ inferInstance S hS
  have hne : (∏ i, x i ^ 2) ≠ 0 := hdet ▸ hdet0
  rw [himg, hdet, PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv v _ hne, PI.UnitaryGroupMassFormula.LocJacTyp.BM.absV_prod] at h
  have hpos : ∀ i, 0 < PI.LocJacTyp.absV v (x i) := fun i => PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v (hx i)
  have hP : 0 < ∏ i, PI.LocJacTyp.absV v (x i ^ 2) :=
    Finset.prod_pos fun i _ => by rw [PI.UnitaryGroupMassFormula.LocJacTyp.absV_pow]; exact pow_pos (hpos i) 2
  have hR := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hP.le] at hR
  change (μ S).toReal = (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal *
    ∏ i, (PI.LocJacTyp.absV v (x i) ^ 2)⁻¹
  change (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal = _ at hR
  rw [hR, Finset.prod_inv_distrib]
  simp_rw [PI.UnitaryGroupMassFormula.LocJacTyp.absV_pow] at hP ⊢
  field_simp

theorem sdFromAnn_holds : SdFromAnn := by
  intro F E _ _ _ _ _ ψ v d _ hE hd hann ι _
  classical
  have hone : (1 : Fv F v ⊗[F] E) ∈ PI.LocJacTyp.OEv v := by
    simpa using PI.UnitaryGroupMassFormula.LocJacTyp.Sd.inclR_mem (E := E) v 1
  have hrank : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hE
  have hinv : LocVol.sc v d * (d⁻¹ ⊗ₜ[F] (1 : E)) = 1 := by
    change (d ⊗ₜ[F] (1 : E)) * (d⁻¹ ⊗ₜ[F] (1 : E)) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hd, one_mul,
      ← Algebra.TensorProduct.one_def]
  have hker : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.OpenKer v ψ := by
    refine PI.UnitaryGroupMassFormula.LocJacTyp.Sd.openKer_of v ψ (2 * d⁻¹) (mul_ne_zero two_ne_zero (inv_ne_zero hd)) ?_
    intro c hc
    have h1 := (hann (d⁻¹ ⊗ₜ[F] (1 : E))).mpr (by rw [hinv]; exact hone)
    have h2 := h1 (c • (1 : Fv F v ⊗[F] E)) (PI.UnitaryGroupMassFormula.LocJacTyp.Sd.oev_smul v hc hone)
    have htr : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c • (1 : Fv F v ⊗[F] E) * (d⁻¹ ⊗ₜ[F] (1 : E)))
        = c * (2 * d⁻¹) := by
      have : c • (1 : Fv F v ⊗[F] E) * (d⁻¹ ⊗ₜ[F] (1 : E))
          = algebraMap (Fv F v) (Fv F v ⊗[F] E) (c * d⁻¹) := by
        rw [Algebra.smul_def, mul_one, map_mul]; rfl
      rw [this, Algebra.trace_algebraMap, hrank]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      ring
    rw [← htr]; exact h2
  have hnt : ∃ r : Fv F v, psiV F ψ v r ≠ 1 := by
    by_contra hall
    push_neg at hall
    obtain ⟨t0, ht0⟩ := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.exists_not_mem_oev (E := E) v
    have h1 := (hann ((d⁻¹ ⊗ₜ[F] (1 : E)) * t0)).mp (fun x _ => hall _)
    rw [← mul_assoc, hinv, one_mul] at h1
    exact ht0 h1
  obtain hex := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.exists_sd (E := E) v ψ hker hnt ι
  have hμ : LocVol.sdE ψ v ι = hex.choose := by
    change PI.LocJacTyp.sdE ψ v ι = _
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.sdE_eq, dif_pos hex]
  have hsd := hex.choose_spec
  rw [hμ]
  haveI : hex.choose.IsAddHaarMeasure := hsd.1
  refine ⟨hsd.1, inferInstance, ?_⟩
  set μ := hex.choose
  have hDopen := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_dbox (E := E) v ψ hker ι
  have hDcpt := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isCompact_dbox (E := E) v ψ hker hnt ι
  have htest := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.sd_test v ψ ι μ hsd hDopen.measurableSet hDcpt.measure_lt_top
  have hD : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.Dbox v ψ ι
      = Set.univ.pi fun _ : ι => {c : Fv F v ⊗[F] E | LocVol.sc v d * c ∈ LocVol.OEv v} := by
    ext y
    simp only [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.Dbox, Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_congr' fun i => hann (y i)
  have hbs := boxScaleL_holds v ι hE μ (fun _ => d) (fun _ => hd)
  rw [← hD] at hbs
  simp only [Measure.real] at htest
  rw [hbs] at htest
  change (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal = _
  change (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal *
    ((μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal *
      ∏ _i : ι, (PI.LocJacTyp.absV v d ^ 2)⁻¹) = 1 at htest
  set a := (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal
  have hpos : 0 < PI.LocJacTyp.absV v d := PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v hd
  rw [Finset.prod_const, Finset.card_univ] at htest
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hsq : a ^ 2 = (PI.LocJacTyp.absV v d ^ Fintype.card ι) ^ 2 := by
    have hq : 0 < ((PI.LocJacTyp.absV v d ^ 2)⁻¹) ^ Fintype.card ι := by positivity
    have : a ^ 2 * ((PI.LocJacTyp.absV v d ^ 2)⁻¹) ^ Fintype.card ι = 1 := by
      rw [← htest]; ring
    rw [inv_pow, ← pow_mul] at this
    field_simp at this
    rw [this]; ring
  exact (pow_left_inj₀ ha (by positivity) two_ne_zero).mp hsq

end Formalism.L2.SG.Pf.NcVal.SdW
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OrthProjectionOfMemCompl
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

structure Good {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} (hc : IsCompl U (orthK h U))
    (M T : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (Λ : Submodule (𝓞 K) V) : Prop where
  iU : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h U M)
  iW : ∀ x ∈ Λ, prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T)
  oU : ∀ v ∈ locF 𝔭 (dualIn h U M), ∃ x ∈ Λ, prO hc x = v
  oW : ∀ v ∈ locF 𝔭 (dualIn h (orthK h U) T), ∃ x ∈ Λ, prO hc.symm x = v
  cU : Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M
  cW : Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}

theorem mk_eq_iff {X : Submodule K V} {L : Submodule (𝓞 K) V} (a b : ↥(locF 𝔭 (dualIn h X L))) :
    (Submodule.Quotient.mk a : DiscMod h X L 𝔭) = Submodule.Quotient.mk b ↔
      (a : V) - (b : V) ∈ locF 𝔭 L := by
  rw [Submodule.Quotient.eq]
  simp [Submodule.mem_comap]

private theorem prO_mem' {X Y : Submodule K V} (hc : IsCompl X Y) (x : V) : prO hc x ∈ X := by
  first
  | exact (Submodule.linearProjOfIsCompl X Y hc x).2
  | exact Submodule.projection_apply_mem hc x
  | exact Submodule.projection_apply_mem X Y hc x
  | simp [prO]
  | simp [prO, Submodule.projection]

private theorem prO_eq_zero_of_mem_compl {X Y : Submodule K V} (hc : IsCompl X Y) {x : V} (hx : x ∈ Y) :
    prO hc x = 0 := by
  have h1 : prO hc x ∈ X := prO_mem' hc x
  have h2 : prO hc x ∈ Y := by
    have e : prO hc x = x - prO hc.symm x := eq_sub_of_add_eq (prO_add hc x)
    rw [e]
    exact Y.sub_mem hx (prO_mem' hc.symm x)
  have h3 : prO hc x ∈ X ⊓ Y := Submodule.mem_inf.2 ⟨h1, h2⟩
  rw [hc.inf_eq_bot] at h3
  exact (Submodule.mem_bot K).1 h3

private theorem prO_eq_self_of_mem {X Y : Submodule K V} (hc : IsCompl X Y) {x : V} (hx : x ∈ X) :
    prO hc x = x := by
  have h0 : prO hc.symm x = 0 := prO_eq_zero_of_mem_compl hc.symm hx
  have e := prO_add hc x
  rw [h0, add_zero] at e
  exact e

theorem prO_mem (hc' : IsCompl U (orthK h U)) (x : V) : prO hc' x ∈ U := prO_mem' hc' x

theorem prO_symm_mem (hc' : IsCompl U (orthK h U)) (x : V) : prO hc'.symm x ∈ orthK h U := prO_mem' hc'.symm x

theorem orth_projection_of_mem_compl {hc' : IsCompl U (orthK h U)} {x : V} (hx : x ∈ orthK h U) : prO hc' x = 0 := by
  exact prO_eq_zero_of_mem_compl hc' hx

theorem orth_projection_symm_of_mem {hc' : IsCompl U (orthK h U)} {x : V} (hx : x ∈ orthK h U) :
    prO hc'.symm x = x := by
  exact prO_eq_self_of_mem hc'.symm hx

theorem prO_symm_of_mem_U {hc' : IsCompl U (orthK h U)} {x : V} (hx : x ∈ U) : prO hc'.symm x = 0 := by
  exact prO_eq_zero_of_mem_compl hc'.symm hx

theorem mem_of_proj (hG : Good hc M T 𝔭 Λ) {x x' : V} (hx' : x' ∈ Λ) (hU : prO hc x' = prO hc x)
    (hW : prO hc.symm x - prO hc.symm x' ∈ locF 𝔭 T) : x ∈ Λ := by
  have hle : locF 𝔭 T ≤ Λ := by
    rw [← hG.cW]
    exact inf_le_left
  have ht : prO hc.symm x - prO hc.symm x' ∈ Λ := hle hW
  have e1 := prO_add hc x
  have e2 := prO_add hc x'
  rw [hU] at e2
  have hx : x = x' + (prO hc.symm x - prO hc.symm x') := by
    calc x = prO hc x + prO hc.symm x := e1.symm
      _ = (prO hc x + prO hc.symm x') + (prO hc.symm x - prO hc.symm x') := by abel
      _ = x' + (prO hc.symm x - prO hc.symm x') := by rw [e2]
  rw [hx]
  exact Λ.add_mem hx' ht

def gam (hG : Good hc M T 𝔭 Λ) : DiscMod h U M 𝔭 ≃ₗ[𝓞 K] DiscMod h (orthK h U) T 𝔭 :=
  have hker : LinearMap.ker (toDisc h hc M Λ 𝔭 hG.iU) =
      LinearMap.ker (toDisc h hc.symm T Λ 𝔭 hG.iW) := by
    ext x
    rw [mem_ker_toDisc, mem_ker_toDisc, prO_mem_iff hc hG.cU, prO_mem_iff hc.symm hG.cW]
    have e := prO_add hc (x : V)
    constructor
    · intro H
      have : prO hc.symm (x : V) = (x : V) - prO hc (x : V) := eq_sub_of_add_eq' e
      rw [this]
      exact Λ.sub_mem x.2 H
    · intro H
      have : prO hc (x : V) = (x : V) - prO hc.symm (x : V) := eq_sub_of_add_eq e
      rw [this]
      exact Λ.sub_mem x.2 H
  ((LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc M Λ 𝔭 hG.iU hG.oU)).symm.trans
    (Submodule.quotEquivOfEq _ _ hker)).trans
    (LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc.symm T Λ 𝔭 hG.iW hG.oW))

theorem gam_mk (hG : Good hc M T 𝔭 Λ) {x : V} (hx : x ∈ Λ) :
    gam hG (Submodule.Quotient.mk ⟨prO hc x, hG.iU x hx⟩) =
      Submodule.Quotient.mk ⟨prO hc.symm x, hG.iW x hx⟩ := by
  have h1 : (Submodule.Quotient.mk ⟨prO hc x, hG.iU x hx⟩ : DiscMod h U M 𝔭) =
      toDisc h hc M Λ 𝔭 hG.iU ⟨x, hx⟩ := rfl
  have h2 : (Submodule.Quotient.mk ⟨prO hc.symm x, hG.iW x hx⟩ : DiscMod h (orthK h U) T 𝔭) =
      toDisc h hc.symm T Λ 𝔭 hG.iW ⟨x, hx⟩ := rfl
  rw [h1, h2, ← LinearMap.quotKerEquivOfSurjective_apply_mk (toDisc h hc M Λ 𝔭 hG.iU)
    (toDisc_surj h hc M Λ 𝔭 hG.iU hG.oU)]
  simp only [gam, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

end Formalism.L2.SG.Pf.OrthogonalProjections
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PushforwardOrthComplement
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G9

theorem cJof_cast {F : Type} [Field F] {n n' : ℕ} (e : n' = n) (𝔭 : Ideal (𝓞 F)) (a : Fin n → 𝓞 F) :
    cJof 𝔭 (fun i : Fin n' => a (Fin.cast e i)) = cJof 𝔭 a := by
  subst e
  rfl

theorem vJof_cast {F : Type} [Field F] {n n' : ℕ} (e : n' = n) (𝔭 : Ideal (𝓞 F)) (a : Fin n → 𝓞 F) :
    vJof 𝔭 (fun i : Fin n' => a (Fin.cast e i)) = vJof 𝔭 a := by
  subst e
  rfl

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}

theorem isTotPosDef_formOn (hpos : PosDefOn h (orthK h U)) :
    IsTotPosDef (formOn h (orthK h U)) :=
  fun x hx φ => hpos x x.2 (fun e => hx (Subtype.ext e)) φ

theorem jordan_data (h1 : JordanExists) (h5 : AlphaDisc) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hnd : Nondeg h) (hc : IsCompl U (orthK h U)) (hpos : PosDefOn h (orthK h U))
    (T : Submodule (𝓞 K) ↥(orthK h U)) (hT : Submodule.IsLattice K T)
    (hTi : Formalism.HermitianLatticesTheory.IsIntegralLat (formOn h (orthK h U)) T) (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsMaximal) :
    vJ h (orthK h U) (push _ T) 𝔭 = vd (formOn h (orthK h U)) T 𝔭 ∧
    alphaL (formOn h (orthK h U)) T 𝔭 = (discAut h (orthK h U) (push _ T) 𝔭 : ℝ) *
      alphaStd K 𝔭 (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T) 𝔭) ∧
    (vd (formOn h (orthK h U)) T 𝔭 = 0 → cJ h (orthK h U) (push _ T) 𝔭 = 0) := by
  have hWs := formOn_isSymm hs (orthK h U)
  have hWd := isTotPosDef_formOn hpos
  have hex : ∀ b a, IsJordanIn h (orthK h U) (push _ T) 𝔭 b a →
      vJof 𝔭 a = vd (formOn h (orthK h U)) T 𝔭 ∧
      alphaL (formOn h (orthK h U)) T 𝔭 = (discAut h (orthK h U) (push _ T) 𝔭 : ℝ) *
        alphaStd K 𝔭 (finrank K ↥(orthK h U) - cJof 𝔭 a) := by
    intro b a hb
    have hb' := isJordanIn_top h𝔭.isPrime hb
    have e1 := (h1 K F ↥(orthK h U) hK hF (formOn h (orthK h U)) hWs).2 T hT 𝔭 h𝔭 _ _ hb'
    have e2 := h5 K F ↥(orthK h U) hK hF (formOn h (orthK h U)) hWs hWd T hT hTi 𝔭 h𝔭 _ _ hb'
    rw [vJof_cast] at e1
    rw [cJof_cast, ← discAut_push h𝔭.isPrime] at e2
    exact ⟨e1.symm, e2⟩
  obtain ⟨b, a, hb⟩ := (h1 K F V hK hF h hs).1 (orthK h U) (push _ T) (nondegenerate_on_orth_compl hs hnd hc)
    ((isLatIn_push_iff_isLattice T).2 hT) ((isIntegralLat_push T).2 hTi) 𝔭 h𝔭
  have hvJ : vJ h (orthK h U) (push _ T) 𝔭 = vd (formOn h (orthK h U)) T 𝔭 := by
    unfold vJ
    obtain ⟨b', a', hb', e⟩ := Nat.sInf_mem (⟨_, b, a, hb, rfl⟩ :
      Set.Nonempty {v | ∃ b a, IsJordanIn h (orthK h U) (push _ T) 𝔭 b a ∧ v = vJof 𝔭 a})
    rw [e]
    exact (hex b' a' hb').1
  obtain ⟨b₀, a₀, hb₀, e₀⟩ := Nat.sInf_mem (⟨_, b, a, hb, rfl⟩ :
    Set.Nonempty {c | ∃ b a, IsJordanIn h (orthK h U) (push _ T) 𝔭 b a ∧ c = cJof 𝔭 a})
  have hcJ : cJ h (orthK h U) (push _ T) 𝔭 = cJof 𝔭 a₀ := e₀
  refine ⟨hvJ, by rw [hcJ]; exact (hex b₀ a₀ hb₀).2, fun hv => ?_⟩
  rw [hcJ]
  have h0 := (hex b₀ a₀ hb₀).1
  rw [hv] at h0
  unfold vJof at h0
  unfold cJof
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ hi
  exact hi ((Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ _))

theorem mem_of_isLatIn {X : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn X T) :
    ∀ v ∈ T, v ∈ X := fun _ hv => hT.2 ▸ Submodule.subset_span hv

theorem genusMassW_of (h1 : JordanExists) (h5 : AlphaDisc) : GenusMassW := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hc hpos T₀ hT₀ hT₀i c hmc
  obtain ⟨T', rfl⟩ : ∃ T', push (orthK h U) T' = T₀ := ⟨_, push_pull (mem_of_isLatIn hT₀)⟩
  have hT' : Submodule.IsLattice K T' := (isLatIn_push_iff_isLattice T').1 hT₀
  have hT'i := (isIntegralLat_push T').1 hT₀i
  have hWs := formOn_isSymm hs (orthK h U)
  have hWd := isTotPosDef_formOn hpos
  have hMB := Formalism.HermitianLatticesTheory.massBasic K ↥(orthK h U) (formOn h (orthK h U)) hWs (StabilizerLattices.trace_pos hWd) T' hT'
  obtain ⟨s', hs'⟩ := hMB.1
  have hmass := hMB.2.1 s' hs'
  have hMpos := hMB.2.2
  have hMC := hmc ↥(orthK h U) (formOn h (orthK h U)) T' hWs hWd rfl hT' hT'i
  refine ⟨s'.image (push (orthK h U)), ?_, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hT
    have hg := hs'.1 N hN
    exact ⟨(isLatIn_push_iff_isLattice N).2 hg.1, (sameGenusFix_push_iff hK hF hs hc T' N).2 hg.2⟩
  · intro T hT hgen
    obtain ⟨N, rfl⟩ : ∃ N, push (orthK h U) N = T := ⟨_, push_pull (mem_of_isLatIn hT)⟩
    have hN : N ∈ Formalism.HermitianLatticesTheory.genus (formOn h (orthK h U)) T' :=
      ⟨(isLatIn_push_iff_isLattice N).1 hT, (sameGenusFix_push_iff hK hF hs hc T' N).1 hgen⟩
    obtain ⟨N₁, ⟨hN₁, g, hg, hgN⟩, huniq⟩ := hs'.2 N hN
    refine ⟨push _ N₁, ⟨Finset.mem_image_of_mem _ hN₁, extId hc g, extId_mem hs hc hg, ?_⟩, ?_⟩
    · rw [gmap_extId_push hs hc hg, hgN]
    · rintro T₂ ⟨hT₂, g₂, hg₂, e₂⟩
      obtain ⟨N₂, hN₂, rfl⟩ := Finset.mem_image.mp hT₂
      have e : N₂ = N₁ := huniq N₂ ⟨hN₂, restr hg₂, restr_mem hg₂,
        push_injective _ (by rw [← gmap_push hg₂, e₂])⟩
      rw [e]
  · intro T hT _
    obtain ⟨N, rfl⟩ : ∃ N, push (orthK h U) N = T := ⟨_, push_pull (mem_of_isLatIn hT)⟩
    have hfin := Formalism.HermitianLatticesTheory.autFinite K ↥(orthK h U) (formOn h (orthK h U)) hWs (StabilizerLattices.trace_pos hWd) N
      ((isLatIn_push_iff_isLattice N).1 hT)
    have : Finite ↥(Formalism.ThetaLiftIndependence.autL (formOn h (orthK h U)) N) := hfin.to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (stabEquivW hs hc N).symm)
  · rw [Finset.sum_image (fun x _ y _ e => push_injective _ e)]
    simp_rw [card_stab_push hs hc]
    rw [← hmass, hMC]
    have hZ := finite_vd_ne_zero hK hF hWs hWd hT' hT'i
    set Z := hZ.toFinset with hZdef
    have hout : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ Z →
        vd (formOn h (orthK h U)) T' 𝔭.1 = 0 := fun 𝔭 h𝔭 => by
      rw [hZdef, Set.Finite.mem_toFinset] at h𝔭
      exact not_not.mp h𝔭
    have hjd := fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
      jordan_data h1 h5 hK hF hs hnd hc hpos T' hT' hT'i 𝔭.1 𝔭.2
    have hlam : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
        lamP (formOn h (orthK h U)) T' 𝔭.1 =
          alphaStd K 𝔭.1 (finrank K ↥(orthK h U)) *
            (Ideal.absNorm 𝔭.1 : ℝ) ^ (finrank K ↥(orthK h U) * vd (formOn h (orthK h U)) T' 𝔭.1) /
          ((discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) *
            alphaStd K 𝔭.1 (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T') 𝔭.1)) := by
      intro 𝔭
      unfold lamP
      rw [(hjd 𝔭).2.1]
    have hD1 : ∀ 𝔭 ∉ Z, discAut h (orthK h U) (push _ T') 𝔭.1 = 1 := by
      intro 𝔭 h𝔭
      have hv := hout 𝔭 h𝔭
      have hl := localMassFactor_of_valuation_eq_zero hK hF hWs hWd hT' hT'i 𝔭.2 hv
      rw [hlam 𝔭, hv, (hjd 𝔭).2.2 hv, Nat.sub_zero, mul_zero, pow_zero, mul_one] at hl
      have hA := (alphaStd_pos hK hF 𝔭.2 (finrank K ↥(orthK h U))).ne'
      have hDA : (discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) *
          alphaStd K 𝔭.1 (finrank K ↥(orthK h U)) ≠ 0 := fun e => by
        rw [e, div_zero] at hl
        exact zero_ne_one hl
      have e := (div_eq_one_iff_eq hDA).mp hl
      have e' : (discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) = 1 :=
        mul_right_cancel₀ hA (by rw [one_mul]; exact e.symm)
      exact_mod_cast e'
    have e1 : ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, discAut h (orthK h U) (push _ T') 𝔭.1 =
        ∏ 𝔭 ∈ Z, discAut h (orthK h U) (push _ T') 𝔭.1 := tprod_eq_prod hD1
    have e2 : lamG F (formOn h (orthK h U)) T' = ∏ 𝔭 ∈ Z, lamP (formOn h (orthK h U)) T' 𝔭.1 := by
      unfold lamG
      exact tprod_eq_prod fun 𝔭 h𝔭 => localMassFactor_of_valuation_eq_zero hK hF hWs hWd hT' hT'i 𝔭.2 (hout 𝔭 h𝔭)
    have e3 : nM F h (orthK h U) (push _ T') =
        ∏ 𝔭 ∈ Z, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd (formOn h (orthK h U)) T' 𝔭.1 := by
      unfold nM
      simp_rw [fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => (hjd 𝔭).1]
      exact tprod_eq_prod fun 𝔭 h𝔭 => by rw [hout 𝔭 h𝔭, pow_zero]
    have e4 : ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, alphaStd K 𝔭.1 (finrank K ↥(orthK h U)) /
          alphaStd K 𝔭.1 (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T') 𝔭.1) =
        ∏ 𝔭 ∈ Z, alphaStd K 𝔭.1 (finrank K ↥(orthK h U)) /
          alphaStd K 𝔭.1 (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T') 𝔭.1) :=
      tprod_eq_prod fun 𝔭 h𝔭 => by
        rw [(hjd 𝔭).2.2 (hout 𝔭 h𝔭), Nat.sub_zero,
          div_self (alphaStd_pos hK hF 𝔭.2 (finrank K ↥(orthK h U))).ne']
    have hDne : ∀ 𝔭 ∈ Z, (discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) ≠ 0 := by
      intro 𝔭 h𝔭 e
      have h0 : lamP (formOn h (orthK h U)) T' 𝔭.1 = 0 := by rw [hlam 𝔭, e, zero_mul, div_zero]
      have : Formalism.HermitianLatticesTheory.mass (formOn h (orthK h U)) T' = 0 := by
        rw [hMC, e2, Finset.prod_eq_zero h𝔭 h0, mul_zero]
      linarith
    have key : ∀ 𝔭 ∈ Z, (discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) * lamP (formOn h (orthK h U)) T' 𝔭.1 =
        ((Ideal.absNorm 𝔭.1 : ℝ) ^ vd (formOn h (orthK h U)) T' 𝔭.1) ^ finrank K ↥(orthK h U) *
          (alphaStd K 𝔭.1 (finrank K ↥(orthK h U)) /
            alphaStd K 𝔭.1 (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T') 𝔭.1)) := by
      intro 𝔭 h𝔭
      have hB := (alphaStd_pos hK hF 𝔭.2
        (finrank K ↥(orthK h U) - cJ h (orthK h U) (push _ T') 𝔭.1)).ne'
      rw [hlam 𝔭, ← pow_mul, mul_comm (vd _ _ _) (finrank K _)]
      field_simp [hDne 𝔭 h𝔭, hB]
    rw [e1, e2, e3, e4, Nat.cast_prod, ← Finset.prod_pow]
    calc (∏ 𝔭 ∈ Z, (discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ)) *
          (c * ∏ 𝔭 ∈ Z, lamP (formOn h (orthK h U)) T' 𝔭.1)
        = c * ∏ 𝔭 ∈ Z, ((discAut h (orthK h U) (push _ T') 𝔭.1 : ℝ) *
            lamP (formOn h (orthK h U)) T' 𝔭.1) := by
          rw [Finset.prod_mul_distrib]
          ring
      _ = _ := by
          rw [Finset.prod_congr rfl key, Finset.prod_mul_distrib]
          ring

end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

namespace Formalism.L2.SG.Pf.Cnt

theorem genusMassW_of (h1 : JordanExists) (h5 : AlphaDisc) : GenusMassW :=
  OrthogonalComplementGenusMass.genusMassW_of h1 h5

theorem glueMass_of' (h1 : JordanExists) (h2 : JordanInv) (h5 : AlphaDisc) (h6 : GlueLoc)
    (h8 : GlueProd) : GlueMass :=
  glueMass_of h1 h2 h6 h8 (OrthogonalComplementGenusMass.genusMassW_of h1 h5)

end Formalism.L2.SG.Pf.Cnt
end
end

