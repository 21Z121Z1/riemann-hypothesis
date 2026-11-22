import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFixingSubgroupMaxUnramifiedOfMemLocalGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0441
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0292
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0444
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0445
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepresentationHomFiniteDimensional
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DRDual

open GlobalTheory.DRFil

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def twistRep (χ : G →* LLˣ) (ρ : Representation LL G V) : Representation LL G V where
  toFun g := ((χ g : LLˣ) : LL) • ρ g
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

theorem act_zpow (T : Fˣ) (hT : (T : F) = PD.ι PD.t) (n : ℤ) (g : G) :
    PD.actdR g ((T ^ n : Fˣ) : F) = ((PD.χ g ^ n : Qpˣ) : Qp) • ((T ^ n : Fˣ) : F) := by
  have hsm : ∀ (q : Qp) (b : B), PD.ι (q • b) = q • PD.ι b := fun q b =>
    (PD.ι.toLinearMap.restrictScalars Qp).map_smul q b
  have h1 : Units.map (PD.actdR g : F →* F) T = Units.map (algebraMap Qp F : Qp →* F) (PD.χ g) * T := by
    ext
    have h2 := PD.ι_comm g PD.t
    rw [PD.t_act, hsm, ← hT, Algebra.smul_def] at h2
    exact h2.symm
  have h3 := congrArg (fun x : Fˣ => ((x ^ n : Fˣ) : F)) h1
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h3
  rw [Algebra.smul_def, ← map_zpow]
  exact h3

theorem twist_unit (ρ ρ' : Representation LL G V) (u : Fˣ) (n : ℤ) (ψ : G → Qpˣ)
    (hu : (u : F) ∈ PD.Fil n) (hu' : ((u⁻¹ : Fˣ) : F) ∈ PD.Fil (-n))
    (ha : ∀ g, PD.actdR g (u : F) = (ψ g : Qp) • (u : F))
    (ha' : ∀ g, PD.actdR g ((u⁻¹ : Fˣ) : F) = (((ψ g)⁻¹ : Qpˣ) : Qp) • ((u⁻¹ : Fˣ) : F))
    (hρ : ∀ g x, (ψ g : Qp) • ρ' g x = ρ g x) :
    (IsDR PD ρ → IsDR PD ρ') ∧
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), multV PD ρ' τ (n + a) = multV PD ρ τ a := by
  have hρ' : ∀ g x, (((ψ g)⁻¹ : Qpˣ) : Qp) • ρ g x = ρ' g x := fun g x => by
    rw [← hρ, smul_smul, Units.inv_mul, one_smul]
  let Φ : V ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F := mulR Qp F LL V u ∘ₗ ext Qp F LinearMap.id
  let Ψ : V ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F := mulR Qp F LL V (u⁻¹ : Fˣ) ∘ₗ ext Qp F LinearMap.id
  have h1 : ∀ x, Φ (Ψ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v b => simp [Φ, Ψ]
  have h2 : ∀ x, Ψ (Φ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v b => simp [Φ, Ψ]
  let E : V ⊗[Qp] F ≃ₗ[LL] V ⊗[Qp] F := LinearEquiv.ofLinear Φ Ψ (LinearMap.ext h1) (LinearMap.ext h2)
  have hD : (DdR PD ρ).map E.toLinearMap = DdR PD ρ' := by
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact twist_mem_DdR PD ρ ρ' LinearMap.id _ _ ha hρ hx
    · exact ⟨Ψ y, twist_mem_DdR PD ρ' ρ LinearMap.id _ _ ha' hρ' hy, h1 y⟩
  have hF : ∀ τ a, (FildR PD ρ τ a).map E.toLinearMap = FildR PD ρ' τ (n + a) := by
    intro τ a
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact twist_mem_FildR PD ρ ρ' LinearMap.id _ _ ha hρ τ hu hx
    · have := twist_mem_FildR PD ρ' ρ LinearMap.id _ _ ha' hρ' τ hu' hy
      rw [neg_add_cancel_left] at this
      exact ⟨Ψ y, this, h1 y⟩
  refine ⟨fun h => ?_, fun τ a => ?_⟩
  · rw [IsDR, ← hD, LinearEquiv.finrank_map_eq, h]
  · unfold multV
    rw [add_assoc, ← hF, ← hF, LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]

end Generic

theorem twisted_dual_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1) (j : ℤ), Function.Bijective m → (∀ g x y, m (ρ g x) (ρ' g y) = ((cycLL (P.PD K) ↥LL.1 g ^ j : (↥LL.1)ˣ) : ↥LL.1) * m x y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 → multV (P.PD K) ρ' τ (-a - j) = multV (P.PD K) ρ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' m j hm hg h
  have := K.2
  have := LL.2
  have := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ).1
  have hs := filSpans T K LL ρ h
  let ρ₀ : Representation ↥LL.1 ↥(GK K) V' := twistRep (cycLL (P.PD K) ↥LL.1 ^ (-j)) ρ'
  have hρ₀ : ∀ g y, ρ₀ g y = ((cycLL (P.PD K) ↥LL.1 g ^ (-j) : (↥LL.1)ˣ) : ↥LL.1) • ρ' g y :=
    fun g y => rfl
  have hβ : ∀ g x y, m (ρ g x) (ρ₀ g y) = m x y := fun g x y => by
    rw [hρ₀, map_smul, hg, smul_eq_mul, zpow_neg, Units.inv_mul_cancel_left]
  have hβ' : Function.Bijective m.flip := (LinearEquiv.ofBijective m hm).flip.bijective
  have h₀ : IsDR (P.PD K) ρ₀ := isDR_of_spans T K LL ρ₀
    (spans_dual_of_spans (P.PD K) ρ ρ₀ m (isField_dR T) hβ hβ' (hs.spans _))
  have ht : (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K : P.R.BdR) = (P.PD K).ι (P.PD K).t := rfl
  obtain ⟨h1, h2⟩ := twist_unit (P.PD K) ρ₀ ρ' (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K ^ (-j)) (-j)
    (fun g => (P.PD K).χ g ^ (-j)) (tdR_zpow_mem T K _)
    (by rw [← zpow_neg]; exact tdR_zpow_mem T K _) (act_zpow _ _ ht _)
    (fun g => by rw [← zpow_neg, ← zpow_neg]; exact act_zpow _ _ ht _ g)
    (fun g x => by
      rw [hρ₀, ← algebraMap_smul ↥LL.1]
      congr 1
      exact congrArg Units.val
        (map_zpow (Units.map (algebraMap ℚ_[l] ↥LL.1 : ℚ_[l] →* ↥LL.1)) ((P.PD K).χ g) (-j)))
  refine ⟨h1 h₀, fun τ a _ => ?_⟩
  obtain ⟨n, d, k, had⟩ := exists_adapted (P.PD K) (isField_dR T) ρ hs τ
  obtain ⟨d', had'⟩ := had.dual ρ₀ m hβ hβ'
  rw [show -a - j = -j + -a by ring, h2, had.multV_eq, had'.multV_eq]
  simp only [neg_inj]

end GlobalTheory.DRDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrExtensionClassFormula
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace GlobalTheory.HerrExtClass

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 4000000 in

theorem herr_extension_class_formula : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.HerrComplexNaturality.HerrExtensionClass D HW F := by
  intro D HW F
  unfold Formalism.MainNotions.HerrComplexNaturality.HerrExtensionClass Formalism.MainNotions.RamifiedCoefficientChains.adm16
  intro l _ K s LL h
  show Formalism.MainNotions.RamifiedCoefficientChains.HerrExt ((HW l).W K s LL h)
  have hA := GlobalTheory.Decompl.fontaine_and_decompletion D HW F
  have hU := GlobalTheory.WachUnit.unitVector D HW F l K s LL h
  obtain ⟨e, e₀, hspan, hT, hj, hN, hEE, hφ, hγ, htf⟩ := hU
  refine ⟨e, (e₀ : ((HW l).W K s LL h).one.V), ?_, ?_, ?_⟩
  · exact ⟨by rw [hN]; exact Submodule.subset_span rfl, hN, hEE, hφ, hγ, hT⟩
  · intro T Tp ι π κ hκ hcoc x c hx w h1 h2
    obtain ⟨hS, t, htT, hπt, hκt⟩ := hcoc
    let yt : ↥Tp.L.T := ⟨_, Tp.L.T.smul_mem c htT⟩
    let z : ↥((HW l).W K s LL h).one.L.T := ⟨_, ((HW l).W K s LL h).one.L.T.smul_mem c e₀.2⟩
    have hz : (z : ((HW l).W K s LL h).one.V) = π.f (yt : Tp.V) := by
      have := (π.f.restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at this
      rw [this, hπt]
    have he : (((F l).E K s LL h).tie).jD ((HW l).W K s LL h).one (((HW l).W K s LL h).map π x) = (1 : RW LL) ⊗ₜ[↥(OL LL)] z := by
      rw [hx, LinearMap.map_smul, hj, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      rfl
    have hcκ := (latticeCocycles T.L).smul_mem c hκ
    let cr : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs)) := ⟨_, Formalism.MainNotions.DeltaInvariantLattices.resFun_Z1T _ T _ hcκ⟩
    have hc : ∀ g : ↥((HW l).W K s LL h).GKs, ι.f ((cr : ↥((HW l).W K s LL h).GKs → T.V) g) = Tp.ρ (g : ↥(GK K)) (yt : Tp.V) - (yt : Tp.V) := by
      intro g
      have e1 := (ι.f.restrictScalars ↥(OL LL)).map_smul c (κ (g : ↥(GK K)))
      have e2 := ((Tp.ρ (g : ↥(GK K))).restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at e1 e2
      simp only [cr, yt, Formalism.MainNotions.DeltaInvariantLattices.resFun, LinearMap.funLeft_apply, Pi.smul_apply]
      rw [e1, hκt, e2]
      exact @smul_sub _ _ _ Tp.modO.toDistribMulAction.toDistribSMul c ((Tp.ρ (g : ↥(GK K))) t) t
    have key := GlobalTheory.Cyc.dict_ext_Ks D HW F hA l K s LL h T Tp ((HW l).W K s LL h).one ι π hS
      ((HW l).W K s LL h).one_triv yt z x hz he w h1 h2 cr hc
    refine Eq.trans key ?_
    unfold Formalism.MainNotions.RamifiedCoefficientChains.clsK Formalism.MainNotions.DeltaInvariantLattices.res
    rw [Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
    congr 1
  · intro _ hp2 T Tp ι π κ hκ hcoc x c hx hδ w h1 h2
    obtain ⟨hS, t, htT, hπt, hκt⟩ := hcoc
    let yt : ↥Tp.L.T := ⟨_, Tp.L.T.smul_mem c htT⟩
    let z : ↥((HW l).W K s LL h).one.L.T := ⟨_, ((HW l).W K s LL h).one.L.T.smul_mem c e₀.2⟩
    have hz : (z : ((HW l).W K s LL h).one.V) = π.f (yt : Tp.V) := by
      have := (π.f.restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at this
      rw [this, hπt]
    have he : (((F l).E K s LL h).tie).jD ((HW l).W K s LL h).one (((HW l).W K s LL h).map π x) = (1 : RW LL) ⊗ₜ[↥(OL LL)] z := by
      rw [hx, LinearMap.map_smul, hj, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      rfl
    have hcκ := (latticeCocycles T.L).smul_mem c hκ
    let cr : ↥(latticeCocycles T.L) := ⟨_, hcκ⟩
    have hc : ∀ g : ↥(GK K), ι.f ((cr : ↥(GK K) → T.V) g) = Tp.ρ g (yt : Tp.V) - (yt : Tp.V) := by
      intro g
      have e1 := (ι.f.restrictScalars ↥(OL LL)).map_smul c (κ g)
      have e2 := ((Tp.ρ g).restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at e1 e2
      simp only [cr, yt, Pi.smul_apply]
      rw [e1, hκt, e2]
      exact @smul_sub _ _ _ Tp.modO.toDistribMulAction.toDistribSMul c ((Tp.ρ g) t) t
    have hi : Formalism.MainNotions.LocalSituation.ell (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL h) = 2 → ∃ i : ↥K.1, i ^ 2 = -1 :=
      fun h2' => absurd h2' hp2
    have key := GlobalTheory.ExtDict.dict_K D HW F hA l K s LL h hi T Tp ((HW l).W K s LL h).one ι π hS
      ((HW l).W K s LL h).one_triv yt z x hz he hδ w h1 h2 cr hc
    refine Eq.trans key ?_
    unfold Formalism.MainNotions.RamifiedCoefficientChains.clsK
    rw [← Submodule.Quotient.mk_smul]
    rfl

end GlobalTheory.HerrExtClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HorizontalModBreuilKisinOfEulerNoPole
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.HorizPole

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
  [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

theorem X_pow_eq : (X : K⟦X⟧) ^ e = E K l e - l := by rw [E]; ring

theorem E_ne_zero : E K l e ≠ 0 := (isUnit_E (K := K) l e).ne_zero

theorem pow_mul_EN (j : ℕ) (f : K⟦X⟧) :
    E K l e ^ j * (E K l e * N K f) =
      E K l e * N K (E K l e ^ j * f) - (j : K⟦X⟧) * ((e : K⟦X⟧) * X ^ e) * (E K l e ^ j * f) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, N_E]
  cases j with
  | zero => simp
  | succ j => simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]; push_cast; ring

theorem N_pow_mul (j : ℕ) (G : K⟦X⟧) :
    N K (E K l e ^ (j + 1) * G) =
      E K l e ^ (j + 1) * N K G + ((j + 1 : ℕ) : K⟦X⟧) * E K l e ^ j * ((e : K⟦X⟧) * X ^ e) * G := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, N_E]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]; push_cast; ring

theorem EN_xiExt (D : BKDat O K l e a ι η H) (w : Vec K a ι) :
    D.EN (D.xiExt w) = D.xiExt (fun τ i => E K l e * N K (w τ i)) := by
  rw [PhiMod.EN_apply, PhiMod.conn_xiExt]
  exact (D.xiExt_smul_tot (fun _ => E K l e) _).symm

theorem N_mem_Rpi {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) : N K f ∈ Rpi O K l e :=
  N_mem (derivative_mem_R l hf)

theorem C_mem_Rpi (c : K) : C c ∈ Rpi O K l e := HasK.C_mem c

theorem cast_ne (j : ℕ) : (((j + 1) * e * l : ℕ) : K) ≠ 0 :=
  natCast_ne_zero' l (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.succ_ne_zero j) (NeZero.ne e))
    (Fact.out : l.Prime).ne_zero)

theorem C_inv_mul (j : ℕ) : C ((((j + 1) * e * l : ℕ) : K))⁻¹ * (((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (l : K⟦X⟧)) = 1 := by
  have h : (((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (l : K⟦X⟧)) = C ((((j + 1) * e * l : ℕ) : K)) := by
    rw [map_natCast]; push_cast; ring
  rw [h, ← map_mul, inv_mul_cancel₀ (cast_ne j), map_one]

theorem neg_step (D : BKDat O K l e a ι η H) (p : ℕ) (v : Vec K a ι)
    (hv : ∀ τ i, E K l e ^ (p + 1) * D.xiExt.symm v τ i ∈ Rpi O K l e) (hN : D.EN v ∈ D.Man) :
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧
      ∀ τ i, E K l e ^ p * D.xiExt.symm v₁ τ i ∈ Rpi O K l e := by
  set c : K := (((p + 1) * e * l : ℕ) : K) with hc
  refine ⟨v - c⁻¹ • D.EN v, ?_, ?_, fun τ i => ?_⟩
  · rw [sub_sub_cancel]; exact D.Man.smul_mem _ hN
  · rw [map_sub, map_smul]; exact sub_mem hN (D.Man.smul_mem _ (D.EN_mem_Man hN))
  · obtain ⟨w, rfl⟩ := D.xiExt.surjective v
    have hco : D.xiExt.symm (D.xiExt w - c⁻¹ • D.EN (D.xiExt w)) τ i =
        w τ i - C c⁻¹ * (E K l e * N K (w τ i)) := by
      rw [EN_xiExt, ← map_smul, ← map_sub, LinearEquiv.symm_apply_apply]
      simp [smul_eq_C_mul]
    rw [hco]
    have hF := hv τ i
    rw [LinearEquiv.symm_apply_apply] at hF
    have h2 := pow_mul_EN (l := l) (e := e) (p + 1) (w τ i)
    have h1 := C_inv_mul (K := K) (l := l) (e := e) p
    have hX := X_pow_eq (K := K) (l := l) (e := e)
    have key : E K l e * (E K l e ^ p * (w τ i - C c⁻¹ * (E K l e * N K (w τ i)))) =
        E K l e * (C c⁻¹ * (((p + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (E K l e ^ (p + 1) * w τ i) -
          N K (E K l e ^ (p + 1) * w τ i))) := by
      rw [← mul_assoc, ← pow_succ']
      linear_combination (-C c⁻¹) * h2 + (C c⁻¹ * ((p + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (E K l e ^ (p + 1) * w τ i)) * hX + (-(E K l e ^ (p + 1) * w τ i)) * h1
    rw [mul_left_cancel₀ E_ne_zero key]
    exact mul_mem (C_mem_Rpi _) (sub_mem (mul_mem (mul_mem (natCast_mem _ _) (natCast_mem _ _)) hF)
      (N_mem_Rpi hF))

theorem neg_all (D : BKDat O K l e a ι η H) (p : ℕ) : ∀ (v : Vec K a ι),
    (∀ τ i, E K l e ^ p * D.xiExt.symm v τ i ∈ Rpi O K l e) → D.EN v ∈ D.Man →
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧ ∀ τ i, D.xiExt.symm v₁ τ i ∈ Rpi O K l e := by
  induction p with
  | zero => exact fun v hv hN => ⟨v, by simp, hN, fun τ i => by simpa using hv τ i⟩
  | succ p ih =>
    intro v hv hN
    obtain ⟨v₁, h1, h2, h3⟩ := neg_step D p v hv hN
    obtain ⟨v₂, h4, h5, h6⟩ := ih v₁ h3 h2
    refine ⟨v₂, ?_, h5, h6⟩
    have := add_mem h1 h4
    rwa [sub_add_sub_cancel] at this

theorem pos_step (D : BKDat O K l e a ι η H) (j : ℕ) (v : Vec K a ι)
    (hv : ∀ τ i, D.xiExt.symm v τ i ∈ Rpi O K l e)
    (hG : ∀ τ i, ∃ G ∈ Rpi O K l e, N K (D.xiExt.symm v τ i) = E K l e ^ j * G)
    (hN : D.EN v ∈ D.Man) :
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧ (∀ τ i, D.xiExt.symm v₁ τ i ∈ Rpi O K l e) ∧
      ∀ τ i, ∃ G ∈ Rpi O K l e, N K (D.xiExt.symm v₁ τ i) = E K l e ^ (j + 1) * G := by
  set c : K := (((j + 1) * e * l : ℕ) : K) with hc
  obtain ⟨w, rfl⟩ := D.xiExt.surjective v
  simp only [LinearEquiv.symm_apply_apply] at hv hG
  have hco : ∀ τ i, D.xiExt.symm (D.xiExt w + c⁻¹ • D.EN (D.xiExt w)) τ i =
      w τ i + c⁻¹ • (E K l e * N K (w τ i)) := fun τ i => by
    rw [EN_xiExt, ← map_smul, ← map_add, LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨D.xiExt w + c⁻¹ • D.EN (D.xiExt w), ?_, ?_, fun τ i => ?_, fun τ i => ?_⟩
  · rw [sub_add_cancel_left]; exact neg_mem (D.Man.smul_mem _ hN)
  · rw [map_add, map_smul]; exact add_mem hN (D.Man.smul_mem _ (D.EN_mem_Man hN))
  · rw [hco, smul_eq_C_mul]
    exact add_mem (hv τ i) (mul_mem (C_mem_Rpi _) (mul_mem (E_mem l e _) (N_mem_Rpi (hv τ i))))
  · obtain ⟨G, hGm, hGe⟩ := hG τ i
    rw [hco]
    refine ⟨C c⁻¹ * (((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * G + N K G), mul_mem (C_mem_Rpi _)
      (add_mem (mul_mem (mul_mem (natCast_mem _ _) (natCast_mem _ _)) hGm) (N_mem_Rpi hGm)), ?_⟩
    have h3 := N_pow_mul (l := l) (e := e) j G
    have h1 := C_inv_mul (K := K) (l := l) (e := e) j
    have hX := X_pow_eq (K := K) (l := l) (e := e)
    rw [map_add, Derivation.map_smul, hGe, ← mul_assoc, ← pow_succ', h3, smul_eq_C_mul]
    linear_combination (C c⁻¹ * ((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * E K l e ^ j * G) * hX +
      (-(E K l e ^ j * G)) * h1

theorem pos_all (D : BKDat O K l e a ι η H) (j : ℕ) : ∀ (v : Vec K a ι),
    (∀ τ i, D.xiExt.symm v τ i ∈ Rpi O K l e) → D.EN v ∈ D.Man →
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧ (∀ τ i, D.xiExt.symm v₁ τ i ∈ Rpi O K l e) ∧
      ∀ τ i, ∃ G ∈ Rpi O K l e, N K (D.xiExt.symm v₁ τ i) = E K l e ^ j * G := by
  induction j with
  | zero => exact fun v hv hN => ⟨v, by simp, hN, hv, fun τ i => ⟨_, N_mem_Rpi (hv τ i), by simp⟩⟩
  | succ j ih =>
    intro v hv hN
    obtain ⟨v₁, h1, h2, h3, h4⟩ := ih v hv hN
    obtain ⟨v₂, h5, h6, h7, h8⟩ := pos_step D j v₁ h3 h4 h2
    refine ⟨v₂, ?_, h6, h7, h8⟩
    have := add_mem h1 h5
    rwa [sub_add_sub_cancel] at this

theorem one_div_lt : 1 / ((e : ℝ) * l) < 1 / e := by
  have he : (0 : ℝ) < e := by exact_mod_cast NeZero.pos e
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact one_div_lt_one_div_of_lt he (by nlinarith)

theorem init (D : BKDat O K l e a ι η H) (n : ℕ) (v : Vec K a ι) (hv : v ∈ divE l e n D.Man) :
    ∀ τ i, E K l e ^ (n + H) * D.xiExt.symm v τ i ∈ Rpi O K l e := by
  have h1 : E K l e ^ (n + H) • v ∈ D.ext (Rpi O K l e) := by
    rw [add_comm, pow_add, mul_smul]
    exact D.smul_mem_ext_of_basis (fun i => D.lower _ (D.bas_mem_M i)) (A_le_Rpi l e) (D.mem_Man.1 hv)
  have h2 := (GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι D.toPhiMod (1 / e) one_div_lt
    (E K l e ^ (n + H) • D.xiExt.symm v)).1 (by
      have := D.xiExt_smul_tot (fun _ => E K l e ^ (n + H)) (D.xiExt.symm v)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this ▸ h1)
  exact fun τ i => mem_tot.1 h2 τ i

theorem fin (D : BKDat O K l e a ι η H) (r : Vec K a ι) (hr : ∀ τ i, r τ i ∈ Rpi O K l e) :
    E K l e ^ η • D.xiExt r ∈ D.Man :=
  D.mem_Man.2 (D.smul_mem_Mext (A_le_Rpi l e)
    ((GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι D.toPhiMod (1 / e) one_div_lt r).2 (mem_tot.2 fun τ i => hr τ i)))

theorem taylor (f : K⟦X⟧) (hf : f ∈ Rpi O K l e) (B : ℕ) :
    ∃ g ∈ invL l (A O K), ∃ r ∈ Rpi O K l e, f - g = E K l e ^ B * r := by
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (idE O K l e) B (toHat O K l e ⟨f, hf⟩))
  obtain ⟨r, hr, h⟩ := (evalₐ_toHat_eq_iff l e B ⟨f, hf⟩ g).1 hg.symm
  exact ⟨g, g.2, r, hr, h⟩

theorem eulerDerivation_eisensteinPow_final_bound {f g r G : K⟦X⟧} (m B : ℕ) (hB : m + 1 ≤ B) (hg : g ∈ invL l (A O K))
    (hr : r ∈ Rpi O K l e) (hG : G ∈ Rpi O K l e) (hf : N K f = E K l e ^ m * G)
    (hfg : f - g = E K l e ^ B * r) :
    ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K g = E K l e ^ m * h := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hB
  have hX := X_pow_eq (K := K) (l := l) (e := e)
  set h' := G - (E K l e ^ (d + 1) * N K r +
    ((m + d + 1 : ℕ) : K⟦X⟧) * E K l e ^ d * ((e : K⟦X⟧) * X ^ e) * r) with hh'
  have hgf : g = f - E K l e ^ (m + d + 1) * r := by rw [show m + d + 1 = m + 1 + d by omega, ← hfg]; ring
  have hN : N K g = E K l e ^ m * h' := by
    rw [hgf, map_sub, hf, N_pow_mul, hh']
    ring
  have hh'R : h' ∈ Rpi O K l e := sub_mem hG (add_mem (mul_mem (pow_mem (E_mem l e _) _) (N_mem_Rpi hr))
    (mul_mem (mul_mem (mul_mem (natCast_mem _ _) (pow_mem (E_mem l e _) _))
      (mul_mem (natCast_mem _ _) (pow_mem HasU.X_mem _))) hr))
  obtain ⟨k, hk⟩ : N K g ∈ invL l (A O K) := N_mem (derivative_mem_away _ (fun _ => derivative_mem_A) hg)
  have hk' : (l : K⟦X⟧) ^ k * N K g ∈ A O K := by simpa using hk
  refine ⟨(l : K⟦X⟧) ^ k * h', mem_A_of_E_pow_mul_mem l e m
    (mul_mem (pow_mem (natCast_mem _ _) _) hh'R) ?_, k, ?_⟩
  · rw [hN] at hk'; convert hk' using 1; ring
  · rw [hN]; ring

theorem main : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (n : ℕ) (v : Vec K a ι), v ∈ divE l e n D.Man → D.EN v ∈ D.Man → ∀ m : ℕ, ∃ w ∈ D.Mext (invL l (A O K)), v - D.xiExt w ∈ D.Man ∧ ∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m * h := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D n v hv hN m
  obtain ⟨v₁, h1, h2, h3⟩ := neg_all D (n + H) v (init D n v hv) hN
  obtain ⟨v₂, h4, -, h6, h7⟩ := pos_all D m v₁ h3 h2
  choose G hGm hGe using h7
  choose g hg r hr hfg using fun (τ : ZMod a) (i : ι) => taylor (D.xiExt.symm v₂ τ i) (h6 τ i) (m + 1 + η)
  refine ⟨g, mem_tot.2 fun τ i => hg τ i, ?_, fun τ i =>
    eulerDerivation_eisensteinPow_final_bound m (m + 1 + η) (by omega) (hg τ i) (hr τ i) (hGm τ i) (hGe τ i) (hfg τ i)⟩
  have e0 : D.xiExt.symm v₂ - g = (fun _ : ZMod a => E K l e ^ (m + 1 + η)) • r :=
    funext fun τ => funext fun i => by simpa using hfg τ i
  have e1 : v₂ - D.xiExt g = E K l e ^ (m + 1) • (E K l e ^ η • D.xiExt r) := by
    rw [smul_smul, ← pow_add]
    have := D.xiExt_smul_tot (fun _ : ZMod a => E K l e ^ (m + 1 + η)) r
    rw [← e0, map_sub, LinearEquiv.apply_symm_apply] at this
    exact this
  have e2 : v - D.xiExt g = (v - v₁) + (v₁ - v₂) + (v₂ - D.xiExt g) := by abel
  rw [e2, e1]
  exact add_mem (add_mem h1 h4) (D.smul_mem_Man (pow_mem (E_mem l e _) _) (fin D r hr))

end GlobalTheory.HorizPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockRootFactorsRankOneDomainStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentBlock_rootFactors_rank_one_domain : ∀ {O : Type} [CommRing O] [IsDomain O] (n t : ℕ) (e X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O), 2 ≤ t → e * e = e → e * X₀ = X₀ → X₀ * e = X₀ → Set.InjOn ρ (Finset.Icc 1 t : Set ℕ) → ∏ c ∈ Finset.Icc 1 t, (Polynomial.X - Polynomial.C (ρ c)) = blockPol e X₀ → ((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O)).rank = 1 ∧ ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod * ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod = (∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) • ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
  first | exact @GlobalTheory.RootFactor.rank_one_and_sq | exact GlobalTheory.RootFactor.rank_one_and_sq | (intros; apply GlobalTheory.RootFactor.rank_one_and_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.BKGal

variable {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G]

theorem inclL_smul_coord (P : PhiMod O K l e a ι) (m : OA l O) (c : ι → OA l O) :
    inclL t ϖ P (fun i => m * c i) = inclO l O m • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply]
  have h : (fun i => inclO l O (m * c i)) = inclO l O m • fun i => inclO l O (c i) :=
    funext fun i => by simp only [map_mul, Pi.smul_apply, smul_eq_mul]
  rw [h, Matrix.mulVec_smul]

theorem IsCrisVal.sub {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} {w w' : ι → OW l O} {b b' : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) (h' : IsCrisVal t ϖ P jB w' b') : IsCrisVal t ϖ P jB (w - w') (b - b') := by
  obtain ⟨m, c, hu, hc, hb⟩ := h
  obtain ⟨m', c', hu', hc', hb'⟩ := h'
  refine ⟨m * m', fun i => m' * c i - m * c' i, by rw [map_mul]; exact hu.mul hu', ?_, ?_⟩
  · have e1 : (fun i => m' * c i - m * c' i) = (fun i => m' * c i) - (fun i => m * c' i) := rfl
    rw [e1, map_sub, inclL_smul_coord, inclL_smul_coord, ← hc, ← hc', smul_sub, smul_smul, smul_smul, map_mul,
      mul_comm (inclO l O m')]
  · have e2 : (fun i => toB l O (m' * c i - m * c' i)) =
        toB l O m' • (fun i => toB l O (c i)) - toB l O m • (fun i => toB l O (c' i)) :=
      funext fun i => by simp only [map_sub, map_mul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [e2, map_sub, map_smul, map_smul, ← hb, ← hb', smul_sub, smul_smul, smul_smul, map_mul,
      mul_comm (toB l O m')]

end GlobalTheory.BKGal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharpolyEqStatement
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_charpoly_eq : ∀ D : D7, GalAway D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), ((ρ s : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map (iotaO D.nd D.naut i) = D.naut.inePol (D.naut.locG π w) s := by
  first | exact @GlobalTheory.IneAway.charpoly_inertia | exact GlobalTheory.IneAway.charpoly_inertia | (intros; apply GlobalTheory.IneAway.charpoly_inertia <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentationStatement
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_compatible_conjugation_representation : ∀ D : D7, FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ (w : PlE D.host) (B : ValuationSubring D.nd.Om), w ∉ placesOver D.host.E (D.nd.l i) → IsPlaceOver (F := D.host.E) B w → ∀ s ∈ Ine (F := D.host.E) B, ∀ s' : G D.host.E D.nd.Om, (∀ y, s' (D.ntw.cc y) = D.ntw.cc (s y)) → ((ρ s' : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly = ((ρ s⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly ∧ D.nd.chi i 1 s' = D.nd.chi i 1 s⁻¹ := by
  first | exact @GlobalTheory.ConjPoly.conj_inertia | exact GlobalTheory.ConjPoly.conj_inertia | (intros; apply GlobalTheory.ConjPoly.conj_inertia <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjOnCharValuesAndLengthQuotientStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injOn_charValues_and_length_quotient : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [CharZero O] (s t : ℕ) (u v : ℤ_[l]ˣ) (χ : ℕ → Oˣ), 1 ≤ s → (l = 2 → 2 ≤ s) → (u : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ s * (v : ℤ_[l]) → (∀ c : ℕ, 1 ≤ c → c ≤ t → χ c = χ 1 * (Units.map (algebraMap ℤ_[l] O).toMonoidHom u) ^ (-((c : ℤ) - 1))) → Set.InjOn (fun c => (χ c : O)) (Finset.Icc 1 t : Set ℕ) ∧ lenUnit (O := O) l (O ⧸ Ideal.span {∏ c ∈ Finset.Ioc 1 t, ((χ 1 : O) - (χ c : O))}) = ∑ k ∈ Finset.Ioo 0 t, ((s : ℚ) + padicValNat l k) := by
  first | exact @GlobalTheory.CharValueLength.injOn_and_lenUnit | exact GlobalTheory.CharValueLength.injOn_and_lenUnit | (intros; apply GlobalTheory.CharValueLength.injOn_and_lenUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeOfIsBaseChangeQuotientStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBaseChange_of_isBaseChange_quotient_comp : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (𝔞 : Ideal S), 𝔞 ≤ Ideal.jacobson ⊥ → ∀ (P : Type) [AddCommGroup P] [Module R P] [Module.Finite R P] (V : Type) [AddCommGroup V] [Module S V] [Module R V] [IsScalarTower R S V] [Module.Finite S V] [Module.Projective S V] (W : Type) [AddCommGroup W] [Module (S ⧸ 𝔞) W] [Module S W] [Module R W] [IsScalarTower S (S ⧸ 𝔞) W] [IsScalarTower R (S ⧸ 𝔞) W] [IsScalarTower R S W] (u : P →ₗ[R] V) (g : V →ₗ[S] W), IsBaseChange (S ⧸ 𝔞) g → IsBaseChange (S ⧸ 𝔞) (g.restrictScalars R ∘ₗ u) → IsBaseChange S u := by
  first | exact @GlobalTheory.BSP.isBaseChange_of_isBaseChange_quotient | exact GlobalTheory.BSP.isBaseChange_of_isBaseChange_quotient | (intros; apply GlobalTheory.BSP.isBaseChange_of_isBaseChange_quotient <;> assumption)
end

