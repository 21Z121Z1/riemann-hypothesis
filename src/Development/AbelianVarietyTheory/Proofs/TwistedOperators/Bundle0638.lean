import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0633
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0502
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0634
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0465
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0627
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0449
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0625
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0613
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowRealAverageHoweDualityFockComponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem halfInd_isSBHalf {S T : HSp D} (e : AE D) (Λ : AddSubgroup (WO S T)) : IsSBHalf e Λ (halfInd e Λ) := by
  refine ⟨fun x hx => ?_, 1, one_pos, fun u hu hu' x => ?_, fun x hx => ?_⟩
  · by_contra h; exact hx (if_neg fun h' => h h'.2)
  · rw [one_smul]
    have h1 : IsHalf e (x + u) ↔ IsHalf e x := forall₂_congr fun i j => by
      rw [Matrix.add_apply, mul_add, hu' i j, add_left_inj]
    exact halfInd_congr (and_congr (AddSubgroup.add_mem_cancel_right _ hu) h1)
  · rw [one_smul]; by_contra h; exact hx (if_neg fun h' => h h'.1)

theorem om_base_law {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    {f₀ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f₀) (hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀)
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) {h : GA D T}
    (hh : SuppAt e T h) :
    ∃ c : ℂ, om (1, h) f₀ = c • Tm fun x => halfInd e (latO S T ΛS ΛT fun _ => True) (actO S T 1⁻¹ h⁻¹ x) := by
  have he' : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have key := GlobalTheory.SplitLinear.splitLinearModel D ψ S T χS χT om hW ΛS ΛT hS hT P e he f₀ hf hv 1 one_ne_zero Tm hTm 1 h
    (GlobalTheory.SplitLinear.suppAt_one e S) hh _ _ (GlobalTheory.VecInv.isDetAt_detAt e he' S 1) (GlobalTheory.VecInv.isDetAt_detAt e he' T h)
    _ (halfInd_isSBHalf e _)
  have h0 : Tm (halfInd e (latO S T ΛS ΛT fun _ => True)) = f₀ := by simpa using hTm.vac
  rw [h0] at key
  refine ⟨(splitFacO χS χT (GlobalTheory.VecInv.detAt e he' S 1) (GlobalTheory.VecInv.detAt e he' T h) : ℂ) *
    (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac S T (GlobalTheory.VecInv.detAt e he' S 1) (GlobalTheory.VecInv.detAt e he' T h) : ℂ), key.trans ?_⟩
  rw [← map_smul]
  rfl

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem compAt_fin {θ : InfFam D} {V : HSp D} {h : GA D V} (hh : h ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt V h) = 1 := by
  have h1 : Formalism.UG.bc (infPart D) (matHom V h) = 1 := (GlobalTheory.UnitaryIdemCut.mem_GfC_iff V h).1 hh
  have h2 := congrArg Units.val h1
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [compAt, Matrix.map_apply]
  have h4 : infPart D (Formalism.L2.Theta.mt V h i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := h3
  rw [h4, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem actO_one_one {S T : HSp D} (u : WO S T) : actO S T 1 1 u = u := by
  simp [actO, GlobalTheory.AdelicLatMove.mt_one]

theorem om_keep_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (kS : S.SigOK) (kT : T.SigOK) {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (cS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ))
    (cT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f)
    {h : GA D T} (hh : h ∈ GfC T)
    (hk : ∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      actO S T 1 h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) :
    ∃ c : ℂ, om (1, h) f = c • f := by
  have hf' := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ 1 h
    (fun τ => by rw [compAt_fin (one_mem _) τ, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [compAt_fin hh τ, Matrix.mul_one, Matrix.one_mul])
    (fun u => ⟨fun hu => ⟨actO S T 1 h⁻¹ u, (hk _).2 (by rw [← GlobalTheory.SplitLinear.actO_mul, mul_one, mul_inv_cancel, actO_one_one]; exact hu),
        by rw [← GlobalTheory.SplitLinear.actO_mul, mul_one, mul_inv_cancel, actO_one_one]⟩,
      fun ⟨u₀, hu₀, e⟩ => e ▸ (hk u₀).1 hu₀⟩) f hf
  obtain ⟨c, -, hc⟩ := GlobalTheory.VacUnique.vacUniqueO D ψ θ hf.1 hθ S T sS sT kS kT cS cT ΛS ΛT hS hT f _ hf hf'
  exact ⟨c, hc⟩

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem exists_cut_hom (V : HSp D) (r : AF D.host.F)
    (hb : algebraMap (AF D.host.F) (AE D) r * algebraMap (AF D.host.F) (AE D) r = algebraMap (AF D.host.F) (AE D) r) :
    ∃ κ : GA D V →* GA D V, ∀ g, Formalism.L2.Theta.mt V (κ g) = algebraMap (AF D.host.F) (AE D) r • Formalism.L2.Theta.mt V g +
      (1 - algebraMap (AF D.host.F) (AE D) r) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  obtain ⟨κ, hκ⟩ := GlobalTheory.UnitaryIdemCut.exists_cutHA (AF D.host.F) D.sp.cm.sig V.gram r hb
  refine ⟨κ, fun g => ?_⟩
  have := congrArg Units.val (hκ g)
  rw [GlobalTheory.UnitaryIdemCut.cutGL_val] at this
  exact this

theorem actO_cut_half {S T : HSp D} {b e : AE D} (hbe : b * e = 0) {g : GA D T}
    {M : Matrix (Fin T.rank) (Fin T.rank) (AE D)}
    (hg : Formalism.L2.Theta.mt T g = b • M + (1 - b) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))) {y : WO S T}
    (hy : IsHalf e y) : actO S T 1 g y = y := by
  have hby : ∀ i j, b * y i j = 0 := fun i j => by rw [← hy i j, ← mul_assoc, hbe, zero_mul]
  have h1 : actO S T 1 g y = (HMul.hMul (Formalism.L2.Theta.mt T g) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) :
      Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    simp [actO, GlobalTheory.AdelicLatMove.mt_one]
  rw [h1, hg, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_eq_zero fun k _ => by rw [mul_left_comm, hby, mul_zero], zero_add, sub_mul, one_mul,
    hby, sub_zero]

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}

theorem cut_mul_cut {n : Type} [Fintype n] [DecidableEq n] {a : AE D} (ha : a * a = a) (M : Matrix n n (AE D)) :
    (a • M + (1 - a) • (1 : Matrix n n (AE D))) * ((1 - a) • M + (1 - (1 - a)) • (1 : Matrix n n (AE D))) = M := by
  have h0 : a * (1 - a) = 0 := by rw [mul_sub, mul_one, ha, sub_self]
  have h0' : (1 - a) * a = 0 := by rw [mul_comm, h0]
  have h1 : (1 - a) * (1 - a) = 1 - a := by rw [sub_mul, one_mul, h0, sub_zero]
  rw [sub_sub_cancel]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one]
  simp only [smul_add, smul_smul, h0, h0', ha, h1, zero_smul, zero_add, add_zero]
  rw [← add_smul, sub_add_cancel, one_smul]

end GlobalTheory.VacMoveLow

namespace GlobalTheory.VacMoveLow

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem exists_cut_pair (V : HSp D) {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) :
    ∃ κe κo : GA D V →* GA D V, (∀ g, g = κe g * κo g) ∧ (∀ g, SuppAt e V (κe g)) ∧ (∀ g ∈ GfC V, κo g ∈ GfC V) ∧
      (∀ g, Formalism.L2.Theta.mt V (κo g) = (1 - (e + cA D e)) • Formalism.L2.Theta.mt V g +
        (e + cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) ∧
      ∀ (S : HSp D) g (y : WO S V), IsHalf e y → actO S V 1 (κo g) y = y := by
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, he]
  have hec : cA D e * e = 0 := by rw [mul_comm]; exact hc
  obtain ⟨r, hr⟩ := GlobalTheory.PlaceModelSum.exists_add_conj e
  have hr1 : algebraMap (AF D.host.F) (AE D) (1 - r) = 1 - algebraMap (AF D.host.F) (AE D) r := by
    simp only [map_sub, map_one]
  have hrr : algebraMap (AF D.host.F) (AE D) r * algebraMap (AF D.host.F) (AE D) r =
      algebraMap (AF D.host.F) (AE D) r := by
    rw [hr, add_mul, mul_add, mul_add, he, hce, hc, hec, add_zero, zero_add]
  have hrr' : algebraMap (AF D.host.F) (AE D) (1 - r) * algebraMap (AF D.host.F) (AE D) (1 - r) =
      algebraMap (AF D.host.F) (AE D) (1 - r) := by
    rw [hr1, sub_mul, mul_sub, mul_sub, hrr, mul_one, one_mul, mul_one, sub_self, sub_zero]
  have hbe0 : algebraMap (AF D.host.F) (AE D) (1 - r) * e = 0 := by
    rw [map_sub, map_one, hr, sub_mul, add_mul, he, hec, one_mul, add_zero, sub_self]
  have hbe : (1 - algebraMap (AF D.host.F) (AE D) r) * e = 0 := by rw [← hr1]; exact hbe0
  obtain ⟨κe, hκe⟩ := exists_cut_hom V r hrr
  obtain ⟨κo, hκo⟩ := exists_cut_hom V (1 - r) hrr'
  rw [hr1] at hκo
  have hκo' : ∀ g, Formalism.L2.Theta.mt V (κo g) = (1 - (e + cA D e)) • Formalism.L2.Theta.mt V g +
      (e + cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := fun g => by
    rw [hκo, ← hr, sub_sub_cancel]
  refine ⟨κe, κo, fun g => ?_, fun g i j => ?_, fun g hg => ?_, hκo', fun S g y hy => ?_⟩
  · refine Subtype.ext (Units.ext ?_)
    change Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V (κe g * κo g)
    rw [GlobalTheory.AdelicLatMove.mt_mul, hκe, hκo, cut_mul_cut hrr]
  · have e1 : Formalism.L2.Theta.mt V (κe g) - 1 = algebraMap (AF D.host.F) (AE D) r • (Formalism.L2.Theta.mt V g - 1) := by
      rw [hκe, smul_sub, sub_smul, one_smul]; abel
    rw [e1, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← hr, hrr]
  · have e1 : matHom V (κo g) = GlobalTheory.UnitaryIdemCut.cutGL _ hrr' (matHom V g) :=
      Units.ext (by rw [GlobalTheory.UnitaryIdemCut.cutGL_val, hr1]; exact hκo g)
    rw [GlobalTheory.UnitaryIdemCut.mem_GfC_iff, e1]
    exact GlobalTheory.UnitaryIdemCut.bc_cutGL_eq_one _ _ _ ((GlobalTheory.UnitaryIdemCut.mem_GfC_iff _ _).1 hg)
  · exact actO_cut_half hbe (hκo g) hy

theorem halfInd_move {S T : HSp D} {e : AE D} (Λ : AddSubgroup (WO S T)) {h he ho : GA D T} (hs : h = he * ho)
    (hfix : ∀ w, IsHalf e w → actO S T 1 ho w = w) (hfix' : ∀ w, IsHalf e w → actO S T 1 ho⁻¹ w = w) (x : WO S T) :
    halfInd e Λ (actO S T 1⁻¹ he⁻¹ x) = halfInd e Λ (actO S T 1⁻¹ h⁻¹ x) := by
  apply halfInd_congr
  have e0 : actO S T 1⁻¹ (ho⁻¹ * he⁻¹) x = actO S T 1 ho⁻¹ (actO S T 1⁻¹ he⁻¹ x) := by
    rw [← GlobalTheory.SplitLinear.actO_mul, one_mul]
  rw [hs, mul_inv_rev, e0]
  constructor
  · rintro ⟨h1, h2⟩
    rw [hfix' _ h2]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have e2 := hfix _ h2
    rw [← GlobalTheory.SplitLinear.actO_mul, mul_one, mul_inv_cancel, actO_one_one] at e2
    rw [← e2] at h1 h2
    exact ⟨h1, h2⟩

end GlobalTheory.VacMoveLow

namespace GlobalTheory.ExpansionInvariance

theorem vac_move_low : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) Tm →
      ∃ c : ℂ, W.om (.top t j) (1, ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        c • Tm fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x) := by
  intro D T L sc G W U S t htU Φ β j hj k hk e he Tm hTm
  have hIn : (Pair.top t j : Pair T).InRange D.R.m := by
    show j + 1 ≤ D.R.m
    omega
  have hDef : GlobalTheory.FunObj.DefPair D.R.m (Pair.top t j : Pair T) := by
    show j + 1 ≤ D.R.m
    omega
  have hW := W.om_is _ hIn
  have hvac := S.Z.vac_is _ hDef
  have hSd : IsSelfDualC (G.pS (.top t j : Pair T)) (S.N.latS (.top t j)) :=
    S.N.selfDual (X := .top j) (show j ≤ D.R.m by omega)
  have hTd : IsSelfDualC (G.pT (.top t j : Pair T)) (S.N.latT (.top t j)) :=
    S.N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  have kS : (G.pS (.top t j : Pair T)).SigOK := (G.isV (X := .top j) (show j ≤ D.R.m by omega) (by simp)).sigOK
  have kT : (G.pT (.top t j : Pair T)).SigOK :=
    (G.isV (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega) (by simp)).sigOK
  have he' : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  obtain ⟨κe, κo, hsplit, hSupp, hFin, hmt, hfix⟩ := GlobalTheory.VacMoveLow.exists_cut_pair (G.V (.top (j + 1))) he' he.2
  set h : GA D (G.V (.top (j + 1))) := (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
    GA D (G.V (.top (j + 1)))) with hh_def
  have hoLat := GlobalTheory.CutStdLat.keep_stdLatO S htU j hj k hk e he (κo h) (hmt h)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.VacMoveLow.om_keep_vac hW W.θ_is kS kT
    (fun τ => W.cart_is (.top j) (show j ≤ D.R.m by omega) τ)
    (fun τ => W.cart_is (.top (j + 1)) (show j + 1 ≤ D.R.m by omega) τ) hSd hTd hvac
    (hFin h ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))).2) hoLat
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.VacMoveLow.om_base_law hW hSd hTd he hvac.2.theta hvac.2.lat hTm (hSupp h)
  refine ⟨c₁ * c₂, ?_⟩
  rw [show ((1 : GA D (G.pS (.top t j : Pair T))), h) = ((1 : GA D (G.pS (.top t j : Pair T))), κe h) * (1, κo h) by
    rw [Prod.mk_mul_mk, mul_one, ← hsplit], map_mul, Module.End.mul_apply, hc₁, map_smul, hc₂, smul_smul]
  congr 2
  funext x
  refine GlobalTheory.VacMoveLow.halfInd_move _ (hsplit h) (fun w hw => hfix _ h w hw) (fun w hw => ?_) x
  rw [← map_inv]
  exact hfix _ h⁻¹ w hw

end GlobalTheory.ExpansionInvariance
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjCharacterEqProdSymmetricEdgeCharacters
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

theorem GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∃ (ψ' : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (a : ∀ PP : Pl D.host.E, Fin D.R.r → Fin D.R.r → (kP PP)ˣ), IsGenericPsi R.Pg ψ' ∧ ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = ∏ PP ∈ R.Pg, ψ' PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a PP i j : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp β hβ hred
  classical
  obtain ⟨ψ, hψ, hdec⟩ := GlobalTheory.T.levelCharacter_on_stabilizer_eq_prod_residue_characters_alt R F X h hIs hGrp
  have hc : ∀ PP ∈ R.Pg, ∃ c : (kP PP)ˣ, ∀ t, ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.conjRes PP t) = ψ PP ((c : kP PP) * t) := by
    intro PP hP
    refine GlobalTheory.T.exists_unit_addChar_eq_mulShift_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 PP.isMaximal) (ψ PP)
      ((ψ (GlobalTheory.IdemSupport.cP PP)).compAddMonoidHom (GlobalTheory.SeeConjChar.conjRes PP).toAddMonoidHom) (hψ PP hP).1 ?_
    intro h1
    apply (hψ PP hP).2
    ext t
    obtain ⟨s, rfl⟩ := (GlobalTheory.SeeConjChar.conjRes PP).surjective t
    have := congrArg (fun χ : AddChar (kP PP) ℂ => χ s) h1
    simpa using this
  choose! c hc using hc
  refine ⟨fun PP => (ψ PP).mulShift (-1), fun PP i j =>
    if (i.1 < D.R.rS ∨ (i.1 + 1 < D.R.rS + D.R.k ∧ GlobalTheory.SeeConjChar.sideAt X h PP = true)) then 1
    else if i.1 = D.R.rS + D.R.k then c PP else -c PP, ?_, ?_⟩
  · intro PP hP h1
    apply (hψ PP hP).1
    ext t
    have := congrArg (fun χ : AddChar (kP PP) ℂ => χ (-t)) h1
    simpa [AddChar.mulShift_apply] using this
  · intro κ hS hK2
    have hK : ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset := (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 _ hK2
    rw [hdec κ hK, ← starRingEnd_apply, map_prod]
    refine Finset.prod_congr rfl fun PP hP => ?_
    rw [GlobalTheory.T.residue_levelCharacterArgument_at_typePlace R F X h hIs hGrp β hβ hred PP hP κ hS, GlobalTheory.T.residue_conjugatePlace_characterArgument_signedSum R F X h hIs hGrp β hβ hred PP hP κ hS hK2, hc PP hP,
      map_mul, ← AddChar.map_neg_eq_conj, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, AddChar.mulShift_apply]
    congr 1
    rw [Finset.mul_sum, ← neg_add, ← Finset.sum_add_distrib, neg_one_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hE
    · unfold GlobalTheory.SeeConjChar.wA GlobalTheory.SeeConjChar.wB
      simp only [apply_ite (fun u : (kP PP)ˣ => (u : kP PP)), Units.val_one, Units.val_neg]
      split_ifs <;> first | (exfalso; tauto) | (push_cast; ring1) | omega | (simp_all <;> omega)
    · simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteNodeCartanOrthonormalBasisAllPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) (X : Node), DefNode D.R.m X → ∀ ρ,
    IsCartanInv (gramAt D (G.V X) ρ) (W.cart X ρ) ∧ IsONBasis (gramAt D (G.V X) ρ) (W.cart X ρ) (W.onb X ρ) (G.V X).rank ∧
    IsCartanInv (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) ∧
      IsONBasis (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) (W.onb X ρ) 0 := by
  first | exact @GlobalTheory.RowReal.defNode_cart_onb_all | exact GlobalTheory.RowReal.defNode_cart_onb_all | (intros; apply GlobalTheory.RowReal.defNode_cart_onb_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseOfPolynomialStdGaussianMemSchwartz
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.AvgCol

theorem avg_col : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (Λ : Module.Dual ℂ (VV ℂ (wt G (.top j)))),
    ∃ Λ' : Module.Dual ℂ (VV ℂ (wt G (.top (j + 1)))), ∀ t ∈ U, ∀ d : FinDatum G t (.top t j), S.Z.HasVec d →
      ∀ κ : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
      ∀ (x : FinPt G (.top j)) (h : GA D (G.V (.top (j + 1)))) (v : VV ℂ (wt G (.top j))),
        ∫ k, W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * (k : GA D (G.V (.top j)))) h *
            Λ (realAct W.θ S.N.fr (.top j) ((k : GA D (G.V (.top j)))⁻¹) v) ∂κ =
          Λ' (realAct W.θ S.N.fr (.top (j + 1)) h⁻¹
            (fockComp W S.N.frC (.top t j) (S.Z.vec d) (x * S.N.u _) (finOf _ h * S.N.u _) v)) := by
  intro D T L sc G W U S μ0 hL j hj Q Λ
  obtain ⟨hr, huniq⟩ := GlobalTheory.T.realPoints_topNode_onto_unitary_haar_unique S hL j hj.le
  let r : GinfC (G.V (.top j)) →* (D.what₂.Tau → GL (Fin (G.V (.top j)).rank) ℂ) :=
    (realIn W.θ S.N.fr (.top j)).comp (GinfC (G.V (.top j))).subtype
  have hrk : (G.V (.top j)).rank ≤ (G.V (.top (j + 1))).rank ∧ 0 < (G.V (.top j)).rank := by
    rw [(node_isV G hL (X := .top j) (show j ≤ D.R.m by omega)).rank,
      (node_isV G hL (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)).rank]
    simp only [Node.rank, rankX, rankP, nRk]
    constructor
    · nlinarith
    · omega
  obtain ⟨hab, ha⟩ := hrk
  have hJ : Formalism.L2.Ker.JetInVV ℂ (wt G (.top j)) (wt G (.top (j + 1))) (nuEnd G (.top μ0 j)) :=
    (wtOK_of_defPair G (.top μ0 j) (show j + 1 ≤ D.R.m from hj)).2
  by_cases hex : ∃ κ₀ : Measure (GinfC (G.V (.top j))), κ₀.IsHaarMeasure ∧ IsProbabilityMeasure κ₀
  · obtain ⟨κ₀, h1, h2⟩ := hex
    haveI := h1
    haveI := h2
    obtain ⟨Λ', hΛ'⟩ := GlobalTheory.T.compactUnitaryAverage_fockPolynomial_jetFunctional D.what₂.Tau _ _ hab ha (wt G (.top j)) (wt G (.top (j + 1))) (nuEnd G (.top μ0 j)) hJ
      (GinfC (G.V (.top j))) κ₀ r hr (frChInv W S.N j Q) Λ
    refine ⟨Λ', fun t ht d hd κ hκ hκp x h v => ?_⟩
    obtain rfl := huniq κ κ₀ hκ hκp h1 h2
    let ℓ : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₗ[ℂ] ℂ :=
      (LinearMap.proj (R := ℂ) (φ := fun _ : WO (G.pS (.top t j)) (G.pT (.top t j)) => ℂ) 0).comp
        ((W.om (.top t j) (G.toPair (.top t j) (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))))).comp
          ((W.fock (.top t j) (movedVec t S d)).comp (frCh W S.N j).toLinearMap))
    have hℓ : ∀ P, ℓ P = W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (frCh W S.N j P))
        (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))) := fun P => rfl
    have e1 : ∀ k : GinfC (G.V (.top j)),
        W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * (k : GA D (G.V (.top j)))) h *
            Λ (realAct W.θ S.N.fr (.top j) ((k : GA D (G.V (.top j))))⁻¹ v) =
          (∏ τ, ((r k τ : GL (Fin (G.V (.top j)).rank) ℂ) : Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ).det ^ ((nuEnd G (.top μ0 j) τ : ℤ) - (wt G (.top j) τ).detShift) *
              ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ).det ^ (wt G (.top (j + 1)) τ).detShift) *
            ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ))
              (fun τ => (((r k τ)⁻¹ : GL (Fin (G.V (.top j)).rank) ℂ) : Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)ᵀ) (frChInv W S.N j Q)) *
            Λ (rhoK (wt G (.top j)) (invTrK (r k⁻¹)) v) := by
      intro k
      rw [GlobalTheory.T.columnArrowKernel_real_eq_detChar_mul_fockKernel S hL j hj t d hd Q x k k.2 h, hℓ]
      rfl
    rw [integral_congr_ae (Filter.Eventually.of_forall e1), hΛ' ℓ (realIn W.θ S.N.fr (.top (j + 1)) h) v,
      GlobalTheory.T.fockComponent_transportedPoints_eq_jetOperator S hL j hj t d hd x (finOf _ h)]
    have e2 : realAct W.θ S.N.fr (.top (j + 1)) h⁻¹ =
        rhoK (wt G (.top (j + 1))) (invTrK (realIn W.θ S.N.fr (.top (j + 1)) h)⁻¹) := by
      simp only [realAct, MonoidHom.comp_apply, map_inv]
    rw [e2]
    rfl
  · exact ⟨0, fun t _ d _ κ hκ hκp => absurd ⟨κ, hκ, hκp⟩ hex⟩

end GlobalTheory.AvgCol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridCoreIffFirstRowExtByZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeGridCore_iff_firstRow_extByZero : OnStd fun {D} _ _ _ {G} _ F => ∀ (h : 2 * 0 + 2 ≤ D.R.m) (a : WO (G.V (.core 1)) (Yc D 0)), F.oz.jA ⬝ a ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) a ∈ latRow G 0 := by
  first | exact @GlobalTheory.CoreRowLat.jA_mem_latCore_iff | exact GlobalTheory.CoreRowLat.jA_mem_latCore_iff | (intros; apply GlobalTheory.CoreRowLat.jA_mem_latCore_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainWeilDatumExtendsToStepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenRankThetaChain_weilDatum_extends_to_step : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, StepEx D := by
  first | exact @GlobalTheory.EvenOnto.StepExists.stepEx | exact GlobalTheory.EvenOnto.StepExists.stepEx | (intros; apply GlobalTheory.EvenOnto.StepExists.stepEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchOperatorUnitaryWSeesawStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archOperator_unitaryW_seesaw : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ h ∈ UAt σ G.W (evI F),
    ∃ T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')), ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, h)) f (T f) := by
  first | exact @GlobalTheory.ArchFactor.exists_archOperator | exact GlobalTheory.ArchFactor.exists_archOperator | (intros; apply GlobalTheory.ArchFactor.exists_archOperator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDownArrowRealIntertwinerWithAdjointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_downArrow_realIntertwiner_with_adjoint : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∀ (ω : GlobalTheory.Grid.WRep (G.P (i + 1)).V (G.P i).V) (f : WO (G.P (i + 1)).V (G.P i).V → ℂ), GlobalTheory.Grid.IsWeil R.ψ true (G.P (i + 1)).V (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ω → GlobalTheory.Grid.IsVac R.ψ R.θ true (G.P (i + 1)) (G.P i) f → ∃ (It : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ[ℂ] SmT (G.P (i + 1)).M →ₗ[ℂ] SmT (G.P i).M) (U : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ⋆[ℂ] SmT (G.P i).M →ₗ[ℂ] SmT (G.P (i + 1)).M), GlobalTheory.Grid.IsIntw R.θ (G.P i).M (G.P (i + 1)).M ω.swap (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) f) It ∧ (⟨ω, f, It⟩ : GlobalTheory.Grid.ArrT (G.P (i + 1)) (G.P i)).IsAdj U := by
  first | exact @GlobalTheory.DownArrow.down_intertwiner_adj | exact GlobalTheory.DownArrow.down_intertwiner_adj | (intros; apply GlobalTheory.DownArrow.down_intertwiner_adj <;> assumption)
end

