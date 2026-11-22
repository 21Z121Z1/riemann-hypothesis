import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0296
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainLevelIntegralRealZetaOfTwistedTransformLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw.LevIntProof

variable {D : D7}

theorem pet_tr {c : Com D} {s : PiLocalization₂ D} (hc : c.Is) {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (hM : IsMet c s ipD ip) (u₁ u₂ : s.CC c) (v : s.M.Vec) (b : GinfC s.V)
    (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v)) =
      Lev.levChi s.V s.β s.L κ * ip u₁ u₂ *
        ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  have hmem := (mem_multT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) (u₁ : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))).1 u₁.2
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
  obtain ⟨w, hw, hU⟩ := GlobalTheory.ChainOnto.mult_equiv_real D c.θ s.V s.par s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) hc.inf v b
  have hUw := hU _ hmem
  have ev : ∀ x : s.M.Vec, PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.lift.symm (u₁ : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) x := by
    intro x; simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
  have key : rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) =
      Lev.levChi s.V s.β s.L κ • PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ w) := by
    funext g
    rw [ev, ev, hUw]
    simp only [rTr, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc]
    exact hmap.lev v κ hκ (g * (b : GA D s.V))
  have hsch : s.pet (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ w)) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v)) =
      ip u₁ u₂ * ipD (PiTensorProduct.tprod ℂ w) (PiTensorProduct.tprod ℂ v) := hM.schur u₁ u₂ _ _
  rw [key, GlobalTheory.ChainOnto.PetCoef.pet_smul_left, hsch, hM.pure w v]
  simp only [hw, mul_assoc]

theorem leftInv_conj {V : HSp D} {F : GA D V → ℂ} (h : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) F) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (fun x => conj (F x)) :=
  fun γ hγ x => by simp only [h γ hγ x]

theorem rcoef_conj {s : PiLocalization₂ D} (hh : s.ν.IsHaarMeasure) (hf : IsFundamentalDomain (GQ s.V) s.fd s.ν)
    {F₁ F₂ : GA D s.V → ℂ} (h₁ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) F₁) (h₂ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) F₂) (g : GA D s.V) :
    GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F₁ x)) (fun x => conj (F₂ x)) g = conj (s.pet (rTr s.V g F₁) F₂) := by
  haveI := hh
  have hl : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) (rTr s.V g fun x => conj (F₁ x)) := (leftInv_conj h₁).mul_right g
  show GlobalTheory.AutomorphicL2Unitary.pet (GQ s.V) s.ν (rTr s.V g fun x => conj (F₁ x)) (fun x => conj (F₂ x)) = _
  rw [GlobalTheory.AutomorphicL2Unitary.pet_eq hf hl (leftInv_conj h₂)]
  show _ = conj (∫ x in s.fd, rTr s.V g F₁ x * starRingEnd ℂ (F₂ x) ∂s.ν)
  rw [← integral_conj]
  congr 1
  funext x
  simp [rTr]

theorem leftInv_val {c : Com D} {s : PiLocalization₂ D} (u : s.CC c) (v : s.M.Vec) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) := by
  have hmem := (mem_multT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))).1 u.2
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
  have e : PiLocalization₂.val u (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v := by
    simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
  rw [e]
  exact GlobalTheory.AutomorphicL2Unitary.leftInv_of_isAutFun (hmap.aut v).toIsAutFun

end GlobalTheory.ChainTw.LevIntProof

namespace GlobalTheory.ChainTw.LevIntProof

variable {D : D7}

theorem hgtL_real_lev {s : PiLocalization₂ D} (hsd : IsSelfDualC s.V s.Λ) {a : GL (Fin s.V.rank) (AE D)}
    (hmaj : GlobalTheory.Doubling.IsMaj s.V a) (b : GinfC s.V) (κ : GA D s.V) (hκf : κ ∈ GfC s.V)
    (hpr : ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) :
    GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a ((b : GA D s.V) * κ) = GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V) ∧
      ((GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V) : ℝ)) =
        ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V)) := by
  obtain ⟨_, h2, h3⟩ := GlobalTheory.ChainOnto.hgt_one_components D s.V s.Λ hsd
  obtain ⟨_, _, hoff⟩ := GlobalTheory.Core.Rk.IP.hgtL_props D s.V s.Λ a hsd hmaj
  have hb : (b : GA D s.V) ∈ GlobalTheory.Core.Rk.IP.openOff s.V s.Λ ∅ := fun v _ => by
    rw [h3 b b.2 v]; exact one_mem _
  have hbk : (b : GA D s.V) * κ ∈ GlobalTheory.Core.Rk.IP.openOff s.V s.Λ ∅ := fun v _ => by
    rw [map_mul, h3 b b.2 v, one_mul]; exact hpr v
  have e1 := (hoff ∅).2 _ hb
  have e2 := (hoff ∅).2 _ hbk
  simp only [Finset.prod_empty, mul_one] at e1 e2
  have hA : ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w ((b : GA D s.V) * κ) =
      GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V) := fun w => by
    rw [map_mul, h2 κ hκf w, mul_one]
  simp only [hA] at e2
  exact ⟨NNReal.coe_injective (e2.trans e1.symm), e1⟩

theorem flatInt_mul_lev {c : Com D} {s s' : PiLocalization₂ D} (hc : c.Is) (hh : s.ν.IsHaarMeasure)
    (hf : IsFundamentalDomain (GQ s.V) s.fd s.ν) (hsd : IsSelfDualC s.V s.Λ) {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (hM : IsMet c s ipD ip) (p : Step c s s') (m : Measure (WO s.V s'.V))
    (X : Set (WO s.V s'.V)) {a : GL (Fin s.V.rank) (AE D)} (hmaj : GlobalTheory.Doubling.IsMaj s.V a)
    (φ : PolF D s'.V.rank s.V.rank) (v : s.M.Vec)
    (hlaw : ∀ κ ∈ Lev.levG s.V s.β s.L, (p.ω (κ, 1)) (p.pt φ) = Lev.levChi s.V s.β s.L κ • p.pt φ)
    (hstab : ∀ κ ∈ Lev.levG s.V s.β s.L, ‖Lev.levChi s.V s.β s.L κ‖ = 1 ∧
      ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v)
    (u₁ u₂ : s.CC c) (z : ℂ) (b : GinfC s.V) (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    flatInt p m X a φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v)) z
        ((b : GA D s.V) * κ) =
      conj (ip u₁ u₂) * (zReal p m X φ v b *
        GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) (z - GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V)) := by
  have hκf : κ ∈ GfC s.V := (Subgroup.mem_inf.mp hκ).1
  obtain ⟨hn, hpr⟩ := hstab κ hκ
  have hn' : Lev.levChi s.V s.β s.L κ * conj (Lev.levChi s.V s.β s.L κ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; norm_num
  unfold flatInt GlobalTheory.Core.Rk.IP.integrand
  rw [show GlobalTheory.Core.Rk.IP.wcoef p.ω m X (p.pt φ) (p.pt φ) ((b : GA D s.V) * κ) =
      coefW p.ω m X (p.pt φ) ((b : GA D s.V) * κ) from rfl,
    GlobalTheory.ChainOnto.ZetaNeProof.coefW_mul_lev p m X φ hlaw _ κ hκ,
    rcoef_conj hh hf (leftInv_val u₁ v) (leftInv_val u₂ v), pet_tr hc hM u₁ u₂ v b κ hκ,
    (hgtL_real_lev hsd hmaj b κ hκf hpr).1]
  unfold zReal
  simp only [map_mul]
  linear_combination (coefW p.ω m X (p.pt φ) (b : GA D s.V) *
    GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) (z - GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V) *
    conj (ip u₁ u₂) *
    conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) * hn'

theorem levInt : ∀ D : D7, LevelLawQ D → LevInt D := by
  intro D hLaw hng c w hw k hk s s' hs hs' p hp ipD ip hM m X hcov mR hmR φ v hRC a hmaj
  have hc : c.Is := hw.com
  obtain ⟨hr, _, hfl⟩ := id hs
  obtain ⟨hr', _, hfl'⟩ := id hs'
  have hrk : s.V.rank = D.R.rankY k := hfl.rank
  have hrk' : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
  have hsz : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (D.R.t : ℂ) / 2 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero
    rw [hrk, hrk']
    simp only [Formalism.BasicNotions.Ranks.rankY]
    push_cast; ring
  have hh : s.ν.IsHaarMeasure := hfl.haar
  have hfd : IsFundamentalDomain (GQ s.V) s.fd s.ν := hfl.fund
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  obtain ⟨_, _, _, _, hstab, _⟩ := GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D c w hw k hk.le s hs
  have hlaw := (hLaw hng c w hw k hk s s' hs hs' p hp φ).1
  obtain ⟨_, hI⟩ := hRC
  obtain ⟨s₁, hs₁, hI₁⟩ := hI a hmaj
  have hmj : GlobalTheory.Doubling.IsMaj s.V a := hmaj.1
  obtain ⟨hcont, hpos, _⟩ := GlobalTheory.Core.Rk.IP.hgtL_props D s.V s.Λ a hsd hmj
  have hreal : ∀ b : GinfC s.V, ((GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V) : ℝ)) =
      ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V)) := fun b =>
    (hgtL_real_lev hsd hmj b 1 (one_mem _) fun v => by rw [map_one]; exact one_mem _).2
  have hint : ∀ z : ℝ, s₁ ≤ z → Integrable (fun b : GinfC s.V => zReal p m X φ v b *
      GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) ((z : ℂ) - (D.R.t : ℂ) / 2)) mR := by
    intro z hz
    have h0 : Integrable (fun b : GinfC s.V => zReal p m X φ v b *
        GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) ((s₁ : ℂ) - (D.R.t : ℂ) / 2)) mR := by
      refine hI₁.congr (ae_of_all _ fun b => ?_)
      simp only [GlobalTheory.Doubling.npow, hreal b]
    have hm : AEStronglyMeasurable (fun b : GinfC s.V =>
        GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) ((z : ℂ) - s₁)) mR := by
      have hme : Measurable fun b : GinfC s.V =>
          ((GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V) : ℝ) : ℂ) ^ ((z : ℂ) - s₁) :=
        (Complex.measurable_ofReal.comp
          (NNReal.continuous_coe.comp (hcont.comp continuous_subtype_val)).measurable).pow_const _
      exact hme.aestronglyMeasurable
    have hb : ∀ᵐ b : GinfC s.V ∂mR, ‖GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) ((z : ℂ) - s₁)‖ ≤ 1 :=
      ae_of_all _ fun b => by
        obtain ⟨h1, h2⟩ := hpos (b : GA D s.V)
        unfold GlobalTheory.Doubling.npow
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr h1)]
        apply Real.rpow_le_one (NNReal.coe_nonneg _) (by exact_mod_cast h2)
        simp only [Complex.sub_re, Complex.ofReal_re]
        linarith
    refine (h0.mul_bdd hm hb).congr (ae_of_all _ fun b => ?_)
    simp only
    rw [mul_assoc, ← GlobalTheory.Doubling.npow_add (hpos _).1]
    congr 2
    ring
  refine ⟨s₁, hs₁, fun u₁ u₂ => ?_⟩
  have hF : ∀ z : ℝ, s₁ ≤ z →
      IntegrableOn (flatInt p m X a φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v)) z)
        (levSet s) s.ν ∧
      ∫ g in levSet s, flatInt p m X a φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) (PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v))
        z g ∂s.ν = ∫ b, conj (ip u₁ u₂) * (zReal p m X φ v b *
          GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL s.V s.Λ a (b : GA D s.V)) ((z : ℂ) - (D.R.t : ℂ) / 2)) ∂mR := by
    intro z hz
    refine hmR.2 _ _ ((hint z hz).const_mul _) fun b κ hκ => ?_
    rw [flatInt_mul_lev hc hh hfd hsd hM p m X hmj φ v hlaw hstab u₁ u₂ _ b κ hκ, hsz]
  refine ⟨fun z hz => (hF z hz).1, ?_⟩
  rw [(hF ((D.R.t : ℝ) / 2) hs₁.le).2, integral_const_mul, mul_comm]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun b => ?_)
  simp only
  rw [show (((D.R.t : ℝ) / 2 : ℝ) : ℂ) - (D.R.t : ℂ) / 2 = 0 by push_cast; ring, GlobalTheory.Doubling.npow_zero, mul_one]

end GlobalTheory.ChainTw.LevIntProof

end

example : ∀ D : D7, LevelLawQ D → LevInt D := GlobalTheory.ChainTw.LevIntProof.levInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsKeepStandardLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.KLat

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev IA (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem inclE_mem_IA (r : 𝓞 E) : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (r : E) ∈ IA F E :=
  Subring.subset_closure (Or.inl ⟨⟨(r : E), ⟨r, rfl⟩⟩, rfl⟩)

theorem sigR_mem_IA (σ : E →ₐ[F] E) {y : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (hy : y ∈ IA F E) :
    Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) y ∈ IA F E := by
  have h : IA F E ≤ (IA F E).comap (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) := by
    refine Subring.closure_le.2 ?_
    rintro z (⟨⟨x, ⟨r, rfl⟩⟩, rfl⟩ | ⟨⟨w, hw⟩, rfl⟩)
    · have hi : IsIntegral ℤ (σ (algebraMap (𝓞 E) E r)) :=
        (NumberField.RingOfIntegers.isIntegral_coe r).map (RingHom.toIntAlgHom (σ : E →+* E))
      have e : Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) =
          inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (((⟨_, hi⟩ : 𝓞 E) : E)) := rfl
      show Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∈ IA F E
      rw [e]
      exact inclE_mem_IA (F := F) (⟨_, hi⟩ : 𝓞 E)
    · have e : Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] (w : FiniteAdeleRing (𝓞 F) F)) = (1 : E) ⊗ₜ[F] (w : FiniteAdeleRing (𝓞 F) F) := by
        simp [Formalism.UG.sigR]
      show Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] (w : FiniteAdeleRing (𝓞 F) F)) ∈ IA F E
      rw [e]
      exact Subring.subset_closure (Or.inr ⟨⟨w, hw⟩, rfl⟩)
  exact h hy

variable {n : ℕ}

def HatP (π : 𝓞 E) (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) : Prop :=
  ∀ j : Fin n, x j ∈ IA F E ∧
    (j.1 + 1 = n → ∃ s ∈ IA F E, x j = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((π : 𝓞 E) : E) * s)

theorem hatP_of_mem (π : 𝓞 E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ x, x ∈ L → ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r))
    {x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hx : x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (IA F E) L) : HatP π x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    intro j
    obtain ⟨r, hr, hd⟩ := hL z hz j
    refine ⟨by simp only [hr]; exact inclE_mem_IA r, fun hj => ?_⟩
    obtain ⟨t, rfl⟩ := hd hj
    refine ⟨_, inclE_mem_IA t, ?_⟩
    show inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z j) = _
    rw [hr, ← map_mul]; rfl
  | zero => intro j; exact ⟨zero_mem _, fun _ => ⟨0, zero_mem _, by simp⟩⟩
  | add x y _ _ hx hy =>
    intro j
    obtain ⟨a1, a2⟩ := hx j
    obtain ⟨b1, b2⟩ := hy j
    refine ⟨add_mem a1 b1, fun hj => ?_⟩
    obtain ⟨s, hs, e⟩ := a2 hj
    obtain ⟨s', hs', e'⟩ := b2 hj
    exact ⟨s + s', add_mem hs hs', by simp only [Pi.add_apply, e, e', mul_add]⟩
  | smul c x _ hx =>
    intro j
    obtain ⟨a1, a2⟩ := hx j
    have ec : (c • x) j = (c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * x j := rfl
    refine ⟨by rw [ec]; exact mul_mem c.2 a1, fun hj => ?_⟩
    obtain ⟨s, hs, e⟩ := a2 hj
    exact ⟨(c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * s, mul_mem c.2 hs, by rw [ec, e]; ring⟩

end Gen

end GlobalTheory.KLat

namespace GlobalTheory.KLat

section Lev
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem inv_eq_cT {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) (lev : StepLevel F E σ J T f bad)
    {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (a b : Fin n) :
    (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1 a b = Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F) (g.1 b a) := by
  have hu := ((lev.U_eq g).1 hg).1
  have h : Formalism.UG.cT (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) g.1 * (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) * g.1 =
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hu
  rw [hJ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h
  have e : (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1 = Formalism.UG.cT (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) g.1 := by
    calc (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1
        = (Formalism.UG.cT (Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F) F)) g.1 * g.1) * (g⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).1 := by
          rw [h, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [e]
  rfl

variable (π : 𝓞 E) {J : Matrix (Fin n) (Fin n) E} (lev : StepLevel F E σ J T f bad)
  (hLb : ∀ x, x ∈ lev.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r))

include hLb in
theorem img_hatP {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (y : Fin n → E) (hy : y ∈ lev.Lb) :
    HatP π (g.1 *ᵥ fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y i)) :=
  hatP_of_mem π lev.Lb (fun x hx => (hLb x).1 hx)
    ((GlobalTheory.Mem.Col2.SameOff.stepLevel_stab lev g hg _).1 (Submodule.subset_span ⟨y, hy, rfl⟩))

theorem incl_single (j : Fin n) (c : E) :
    (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((Pi.single j c : Fin n → E) i)) =
      Pi.single j (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) c) := by
  funext i
  by_cases hi : i = j
  · subst hi; simp
  · simp [hi]

include hLb in

theorem col_mem {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (j : Fin n) (hj : ¬ j.1 + 1 = n)
    (a : Fin n) : g.1 a j ∈ IA F E := by
  have hy : (Pi.single j 1 : Fin n → E) ∈ lev.Lb := by
    refine (hLb _).2 fun k => ?_
    by_cases hk : k = j
    · subst hk; exact ⟨1, by simp, fun h => absurd h hj⟩
    · exact ⟨0, by simp [hk], fun _ => dvd_zero _⟩
  have h := (img_hatP π lev hLb hg _ hy a).1
  rw [incl_single, map_one, Matrix.mulVec_single_one] at h
  simpa using h

include hLb in
theorem pi_ne_zero (l : Fin n) (hl : l.1 + 1 = n) : π ≠ 0 := by
  intro h0
  have hsub : (lev.Lb : Set (Fin n → E)) ⊆ (LinearMap.ker (LinearMap.proj l : (Fin n → E) →ₗ[E] E) : Set (Fin n → E)) := by
    intro x hx
    obtain ⟨r, hr, hd⟩ := (hLb x).1 hx l
    have hr0 : r = 0 := by rw [h0] at hd; exact zero_dvd_iff.1 (hd hl)
    simp [LinearMap.mem_ker, hr, hr0]
  have h2 := Submodule.span_le.2 hsub
  rw [lev.Lb_span, top_le_iff] at h2
  have h1 : (Pi.single l 1 : Fin n → E) ∈ LinearMap.ker (LinearMap.proj l : (Fin n → E) →ₗ[E] E) := by
    rw [h2]; trivial
  simp at h1

include hLb in

theorem last_mem {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (l : Fin n) (hl : l.1 + 1 = n) :
    g.1 l l ∈ IA F E := by
  have hy : (Pi.single l (π : E) : Fin n → E) ∈ lev.Lb := by
    refine (hLb _).2 fun k => ?_
    by_cases hk : k = l
    · subst hk; exact ⟨π, by simp, fun _ => dvd_rfl⟩
    · exact ⟨0, by simp [hk], fun _ => dvd_zero _⟩
  obtain ⟨s, hs, e⟩ := (img_hatP π lev hLb hg _ hy l).2 hl
  rw [incl_single, Matrix.mulVec_single] at e
  have hπ : (π : E) ≠ 0 := fun h => pi_ne_zero π lev hLb l hl (by exact_mod_cast h)
  have hu : IsUnit (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (π : E)) := (IsUnit.mk0 _ hπ).map _
  have e2 : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (π : E) * g.1 l l = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (π : E) * s := by
    rw [mul_comm]; exact e
  rw [hu.mul_left_cancel e2]
  exact hs

include hLb in

theorem entry_mem (hJ : J = 1) {g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hg : g ∈ lev.U) (a b : Fin n) :
    g.1 a b ∈ IA F E := by
  by_cases hb : b.1 + 1 = n
  · by_cases ha : a.1 + 1 = n
    · have hab : a = b := Fin.ext (by omega)
      subst hab
      exact last_mem π lev hLb hg a ha
    · have hi : g⁻¹ ∈ lev.U := inv_mem hg
      have e := inv_eq_cT hJ lev hi a b
      rw [inv_inv] at e
      rw [e]
      exact sigR_mem_IA σ (col_mem π lev hLb hi a ha b)
  · exact col_mem π lev hLb hg b hb a

theorem entry_memD {D : D7} {n : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (π : 𝓞 D.host.E) (lev : StepLevel D.host.F D.host.E (sigD D) J T f bad)
    (hLb : ∀ x, x ∈ lev.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → π ∣ r))
    (hJ : J = 1) {g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)} (hg : g ∈ lev.U) (a b : Fin n) :
    g.1 a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  entry_mem π lev hLb hJ hg a b

end Lev

end GlobalTheory.KLat

namespace GlobalTheory.AdForm

theorem levels_keep_stdLat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, ∀ k ∈ A.U i β, Moves _ (rankN (I.rec7 l Z) i hi) k (Formalism.L2.Col.stdLat B.fields.E _) := by
  intro B X I hI _ l Z u a Ch A hA i hi β k hk
  obtain ⟨-, κ, hκ⟩ := (hA.U i hi β k).1 hk
  have hV : ((I.rec7 l Z).sp.X i).gram = 1 := hI.gram_X i
  refine GlobalTheory.SplitDec.moves_std hV _ ?_
  have hJ : gramN (I.rec7 l Z) i hi = 1 := by
    unfold gramN
    rw [hV]
    simp
  have hLb := (hA.reads i hi).lb β
  intro p q
  have e : toEAf (I.rec7 l Z) (Formalism.L2.Theta.mt _ k p q) =
      finM _ (rankN (I.rec7 l Z) i hi) k (finCongr (rankN _ i hi) p) (finCongr (rankN _ i hi) q) := by
    simp [finM, Matrix.reindex_apply]
  rw [e, ← hκ]
  have hLb' : ∀ x, x ∈ (A.K i hi β).lev.Lb ↔ ∀ j : Fin ((I.rec7 l Z).R.N i), ∃ r : 𝓞 (I.rec7 l Z).host.E,
      x j = (r : (I.rec7 l Z).host.E) ∧ (j.1 + 1 = (I.rec7 l Z).R.N i → (X.piT u : 𝓞 (I.rec7 l Z).host.E) ∣ r) :=
    fun x => hLb x
  exact GlobalTheory.KLat.entry_memD _ (A.K i hi β).lev hLb' hJ κ.2 _ _

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateVectorCentralTwistStatement
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_vector_central_twist : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → PuNZ D → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ v : (W.Q.Rl.MY 0).Vec, ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → ∀ u, (∀ φ, ∃ C, IsCol W u C φ) ∧ (∀ T ∈ ThetaLiftSpaceZero W, ∀ C, ∃ b, IsPair W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b) ∧ ∃ (φ : D.what₂.Mu u) (C : _) (b : ℂ), ∃ T ∈ ThetaLiftSpaceZero W, IsCol W u C φ ∧ IsPair W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b ∧ b ≠ 0 := by
  first | exact @GlobalTheory.MiTop.anchor_pairs | exact GlobalTheory.MiTop.anchor_pairs | (intros; apply GlobalTheory.MiTop.anchor_pairs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteScalarComponentIsCuspAndCongruenceFixedAStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearForm_extV_mem_A0_and_prin_invariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t cA a, Defin R.θ (Vc D i) cA a → ∀ (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ), (fun g => l (R.extV i t y g)) ∈ GlobalTheory.Cusp.A0 R.θ (Vc D i) cA ∧ ∀ κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), ∀ g, l (R.extV i t y (g * κ)) = l (R.extV i t y g) := by
  first | exact @GlobalTheory.DownLift.DefiniteComp.definiteScalarComponent_isCusp_and_congruence_fixed | exact GlobalTheory.DownLift.DefiniteComp.definiteScalarComponent_isCusp_and_congruence_fixed | (intros; apply GlobalTheory.DownLift.DefiniteComp.definiteScalarComponent_isCusp_and_congruence_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_data_step_lattice : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, IsDG W j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1)) ((pk W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((pk W).ΛY j) M (fun _ => True) ∧ GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((pk W).ΛY (j + 1)) M' (fun _ => True) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j)) := by
  first | exact @GlobalTheory.MidVacLat.main | exact GlobalTheory.MidVacLat.main | (intros; apply GlobalTheory.MidVacLat.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalMatrixOfMemPeriodLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalMatrix_of_mem_periodLattice : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), ∀ x ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N', ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ∧ embH (tauE D) δ (toHom S T hS hT γ) = x ∧ ∃ v, GlobalTheory.AdTh.IsFinOf S T γ v := by
  first | exact @GlobalTheory.AdForm.LamPre.exists_mat_of_mem_lamC | exact GlobalTheory.AdForm.LamPre.exists_mat_of_mem_lamC | (intros; apply GlobalTheory.AdForm.LamPre.exists_mat_of_mem_lamC <;> assumption)
end

