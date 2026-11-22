import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0192
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UniformCauchySeqOnHeisenbergWordSobolevCauchy
section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.ThetaDensCauchy

open GlobalTheory.Size

section

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem word_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
    {f f' : WO S T → ℂ} (h : IsThetaFunO ψ S T f) (h' : IsThetaFunO ψ S T f') :
    GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (f + f') =
      GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f + GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons, ih]
    exact GlobalTheory.Size.dRho_add hψ hθ a.1 _ (GlobalTheory.Size.theta_word hψ hθ l h) (GlobalTheory.Size.theta_word hψ hθ l h')

theorem word_mem (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
    {U : AddSubgroup (WO S T)} {f : WO S T → ℂ} (h : f ∈ thetaLevel ψ S T U) :
    GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f ∈ thetaLevel ψ S T U := by
  induction l with
  | nil => exact h
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons]
    exact GlobalTheory.Size.dRho_mem_thetaLevel hψ hθ ih a.1 _

theorem sobO_word_le (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (f : WO S T → ℂ) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) ≤ sobO ψ θ μ 𝓕 (d + l.length) f := by
  induction l generalizing d with
  | nil => exact le_rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons]
    refine (GlobalTheory.Size.sobO_heisDer_le d a).trans ((ih (d + 1)).trans (le_of_eq ?_))
    congr 1
    simp only [List.length_cons]
    omega

end

theorem uniformCauchySeqOn_word : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), UniformCauchySeqOn (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) Filter.atTop Set.univ := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm U hU u hu hC l
  obtain ⟨d₀, C, hb⟩ := GlobalTheory.ThetaDensSup.sup_le_sobO D ψ hψ θ hθ S T μ 𝓕 hm U hU
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hη : (0 : ℝ) < ε / (C + 1) := by positivity
  obtain ⟨J, hJ⟩ := hC (d₀ + l.length) (ENNReal.ofReal (ε / (C + 1))) (ENNReal.ofReal_pos.2 hη)
  refine ⟨J, fun i hi j hj w _ => ?_⟩
  have hd : u i - u j ∈ thetaLevel ψ S T U := Submodule.sub_mem _ (hu i) (hu j)
  have he := word_add hψ hθ l hd.1 (hu j).1
  rw [sub_add_cancel] at he
  have h1 := (hb _ (word_mem hψ hθ l hd) w).trans
    (mul_le_mul_right ((sobO_word_le μ 𝓕 l _ d₀).trans (hJ i hi j hj).le) _)
  rw [dist_eq_norm, he, Pi.add_apply, add_sub_cancel_right]
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  refine h1.trans_lt ?_
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.ThetaDensCauchy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicSplit

open scoped NNReal ENNReal

section General

variable {A B : Type} [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalGroup A] [IsTopologicalGroup B] [LocallyCompactSpace A] [LocallyCompactSpace B]
  [SecondCountableTopology A] [SecondCountableTopology B] [T2Space A] [T2Space B]
  [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B]

theorem rightInv_of_prod (h : ∀ μ : Measure (A × B), μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (ν : Measure B) (hν : ν.IsHaarMeasure) : ν.IsMulRightInvariant := by
  refine ⟨fun b => ?_⟩
  let μA : Measure A := Measure.haar
  haveI := h (μA.prod ν) inferInstance
  set c := Measure.haarScalarFactor (ν.map (· * b)) ν
  have hc : ν.map (· * b) = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have h1 : (μA.prod ν).map (· * ((1 : A), b)) = μA.prod (ν.map (· * b)) := by
    have e : (fun x : A × B => x * ((1 : A), b)) = Prod.map id (· * b) := by
      funext x
      simp [Prod.ext_iff]
    rw [e, ← Measure.map_prod_map _ _ measurable_id (measurable_mul_const b), Measure.map_id]
  have h3 : μA.prod ν = (c : ℝ≥0∞) • μA.prod ν := by
    rw [← Measure.prod_smul_right, ← ENNReal.smul_def, ← hc, ← h1, map_mul_right_eq_self]
  obtain K : TopologicalSpace.PositiveCompacts (A × B) := Classical.arbitrary _
  have hpos : 0 < μA.prod ν K := Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty
  have hfin : μA.prod ν K < ⊤ := K.isCompact.measure_lt_top
  have h4 := congrArg (fun m : Measure (A × B) => m K) h3
  simp only [Measure.smul_apply, smul_eq_mul] at h4
  have h5 : (c : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 (h4.symm.trans (one_mul _).symm)
  rw [hc, ENNReal.smul_def, h5, one_smul]

end General

section Restr

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def restrEquiv (P Q R : Subgroup G) (e : P × Q ≃ₜ* G) (he : ∀ p, e p = p.1.1 * p.2.1)
    (hs : ∀ a ∈ P, ∀ b ∈ Q, a * b ∈ R → a ∈ R ∧ b ∈ R) :
    R.subgroupOf P × R.subgroupOf Q ≃ₜ* R where
  toFun x := ⟨e (x.1.1, x.2.1), by
    rw [he]; exact R.mul_mem (Subgroup.mem_subgroupOf.1 x.1.2) (Subgroup.mem_subgroupOf.1 x.2.2)⟩
  invFun r :=
    have hr : ((e.symm r.1).1 : G) * (e.symm r.1).2 ∈ R := by rw [← he, e.apply_symm_apply]; exact r.2
    (⟨(e.symm r.1).1, Subgroup.mem_subgroupOf.2 (hs _ (e.symm r.1).1.2 _ (e.symm r.1).2.2 hr).1⟩,
     ⟨(e.symm r.1).2, Subgroup.mem_subgroupOf.2 (hs _ (e.symm r.1).1.2 _ (e.symm r.1).2.2 hr).2⟩)
  left_inv x := by
    have h : e.symm (e (x.1.1, x.2.1)) = (x.1.1, x.2.1) := e.symm_apply_apply _
    ext
    · exact congrArg (fun p => (p.1 : G)) h
    · exact congrArg (fun p => (p.2 : G)) h
  right_inv r := Subtype.ext (e.apply_symm_apply r.1)
  map_mul' x y := Subtype.ext (by
    change e ((x * y).1.1, (x * y).2.1) = e (x.1.1, x.2.1) * e (y.1.1, y.2.1)
    rw [← map_mul]; rfl)
  continuous_toFun := by
    refine Continuous.subtype_mk (e.continuous.comp ?_) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have h0 : Continuous fun r : R => e.symm r.1 := e.symm.continuous.comp continuous_subtype_val
    exact (Continuous.subtype_mk (continuous_fst.comp h0) _).prodMk (Continuous.subtype_mk (continuous_snd.comp h0) _)

variable [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem rightInv_restr (P Q R : Subgroup G) (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (hR : IsClosed (R : Set G)) (e : P × Q ≃ₜ* G) (he : ∀ p, e p = p.1.1 * p.2.1)
    (hs : ∀ a ∈ P, ∀ b ∈ Q, a * b ∈ R → a ∈ R ∧ b ∈ R)
    (hu : ∀ μ : Measure R, μ.IsHaarMeasure → μ.IsMulRightInvariant) :
    ∀ ν : Measure (R.subgroupOf Q), ν.IsHaarMeasure → ν.IsMulRightInvariant := by
  haveI : LocallyCompactSpace P := hP.locallyCompactSpace
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : LocallyCompactSpace R := hR.locallyCompactSpace
  have hRP : IsClosed ((R.subgroupOf P : Subgroup P) : Set P) := hR.preimage continuous_subtype_val
  have hRQ : IsClosed ((R.subgroupOf Q : Subgroup Q) : Set Q) := hR.preimage continuous_subtype_val
  haveI : LocallyCompactSpace (R.subgroupOf P) := hRP.locallyCompactSpace
  haveI : LocallyCompactSpace (R.subgroupOf Q) := hRQ.locallyCompactSpace
  intro ν hν
  refine rightInv_of_prod (A := R.subgroupOf P) (fun μ hμ => ?_) ν hν
  haveI := hμ
  exact GlobalTheory.UpqUnimodular.isMulRightInvariant_of_continuousMulEquiv (restrEquiv P Q R e he hs) μ
    (hu _ (ContinuousMulEquiv.isHaarMeasure_map μ (restrEquiv P Q R e he hs)))

end Restr

section Adelic

open GlobalTheory.AdelicU

variable {D : D7}

theorem ofInf_projInf_of_mem (V : HSp D) {a : GA D V} (ha : a ∈ GinfC V) :
    ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram a) = a := by
  have h := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram a
  rwa [mem_infPts.1 ha, map_one, mul_one] at h

theorem ofFin_projFin_of_mem (V : HSp D) {b : GA D V} (hb : b ∈ GfC V) :
    ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram b) = b := by
  have h := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram b
  rwa [mem_finPts.1 hb, map_one, one_mul] at h

theorem commute_GinfC_GfC (V : HSp D) {a b : GA D V} (ha : a ∈ GinfC V) (hb : b ∈ GfC V) : a * b = b * a := by
  rw [← ofInf_projInf_of_mem V ha, ← ofFin_projFin_of_mem V hb]
  exact commute_ofInf_ofFin _ _ _ _

def splitEquiv (V : HSp D) : GinfC V × GfC V ≃ₜ* GA D V where
  toFun p := p.1.1 * p.2.1
  invFun g := (⟨ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g), mem_infPts.2 (by simp)⟩,
    ⟨ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g), mem_finPts.2 (by simp)⟩)
  left_inv p := by
    have h1 : projInf D.sp.cm.sig V.gram p.2.1 = 1 := mem_finPts.1 p.2.2
    have h2 : projFin D.sp.cm.sig V.gram p.1.1 = 1 := mem_infPts.1 p.1.2
    ext
    · change ofInf _ _ (projInf _ _ (p.1.1 * p.2.1)) = p.1.1
      rw [map_mul, h1, mul_one, ofInf_projInf_of_mem V p.1.2]
    · change ofFin _ _ (projFin _ _ (p.1.1 * p.2.1)) = p.2.1
      rw [map_mul, h2, one_mul, ofFin_projFin_of_mem V p.2.2]
  right_inv g := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram g
  map_mul' p q := by
    change p.1.1 * q.1.1 * (p.2.1 * q.2.1) = p.1.1 * p.2.1 * (q.1.1 * q.2.1)
    rw [mul_assoc, ← mul_assoc q.1.1, commute_GinfC_GfC V q.1.2 p.2.2, mul_assoc, mul_assoc]
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun :=
    (((continuous_ofInf _ _).comp (continuous_projInf _ _)).subtype_mk _).prodMk
      (((continuous_ofFin _ _).comp (continuous_projFin _ _)).subtype_mk _)

theorem splitEquiv_apply (V : HSp D) (p : GinfC V × GfC V) : splitEquiv V p = p.1.1 * p.2.1 := rfl

theorem isClosed_GinfC' (V : HSp D) : IsClosed (GinfC V : Set (GA D V)) := isClosed_infPts _ _
theorem isClosed_GfC' (V : HSp D) : IsClosed (GfC V : Set (GA D V)) := isClosed_finPts _ _

end Adelic

theorem adelic_split : ∀ (D : D7) (V : HSp D), IsClosed (GinfC V : Set (GA D V)) ∧ IsClosed (GfC V : Set (GA D V)) ∧ (∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b = b * a) ∧ (∃ e : (GinfC V × GfC V) ≃ₜ GA D V, ∀ p, e p = p.1 * p.2) ∧ (∀ μ : Measure (GfC V), μ.IsHaarMeasure → μ.IsMulRightInvariant) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), ((∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d) ∧ (∀ μ : Measure (jacGrp d), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ μ : Measure ((jacGrp d).subgroupOf (GfC V)), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), (∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o) ∧ (∀ μ : Measure (besGrp d o), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ μ : Measure ((besGrp d o).subgroupOf (GfC V)), μ.IsHaarMeasure → μ.IsInvInvariant := by
  intro D V
  have hi := isClosed_GinfC' V
  have hf := isClosed_GfC' V
  haveI : LocallyCompactSpace (GinfC V) := hi.locallyCompactSpace
  haveI : LocallyCompactSpace (GfC V) := hf.locallyCompactSpace
  refine ⟨hi, hf, fun a ha b hb => commute_GinfC_GfC V ha hb, ⟨(splitEquiv V).toHomeomorph, fun p => rfl⟩,
    fun μ hμ => rightInv_of_prod (A := GinfC V) (fun m hm => ?_) μ hμ, fun V₀ ρ d => ?_⟩
  · haveI := hm
    exact GlobalTheory.UpqUnimodular.isMulRightInvariant_of_continuousMulEquiv (splitEquiv V) m
      (GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V _ inferInstance)
  have hJ := GlobalTheory.jacGrp_isClosed D V V₀ ρ d
  haveI : LocallyCompactSpace (jacGrp d) := hJ.locallyCompactSpace
  refine ⟨⟨GlobalTheory.T.fourierJacobiGroup_split_real_finite D V V₀ ρ d, fun μ hμ => ?_, fun μ hμ => ?_⟩, fun A L o => ?_⟩
  · haveI := hμ
    haveI := GlobalTheory.T.fourierJacobiGroup_haar_isMulRightInvariant D V V₀ ρ d μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  · have hc : IsClosed (((jacGrp d).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hJ.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((jacGrp d).subgroupOf (GfC V)) := hc.locallyCompactSpace
    haveI := hμ
    haveI := rightInv_restr (GinfC V) (GfC V) (jacGrp d) hi hf hJ (splitEquiv V) (splitEquiv_apply V)
      (GlobalTheory.T.fourierJacobiGroup_split_real_finite D V V₀ ρ d) (GlobalTheory.T.fourierJacobiGroup_haar_isMulRightInvariant D V V₀ ρ d) μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  have hB := GlobalTheory.BesClosed.besGrp_isClosed D V V₀ A L ρ d o
  haveI : LocallyCompactSpace (besGrp d o) := hB.locallyCompactSpace
  refine ⟨GlobalTheory.T.besselGroup_split_real_finite D V V₀ A L ρ d o, fun μ hμ => ?_, fun μ hμ => ?_⟩
  · haveI := hμ
    haveI := GlobalTheory.T.besselGroup_haar_isMulRightInvariant D V V₀ A L ρ d o μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  · have hc : IsClosed (((besGrp d o).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hB.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((besGrp d o).subgroupOf (GfC V)) := hc.locallyCompactSpace
    haveI := hμ
    haveI := rightInv_restr (GinfC V) (GfC V) (besGrp d o) hi hf hB (splitEquiv V) (splitEquiv_apply V)
      (GlobalTheory.T.besselGroup_split_real_finite D V V₀ A L ρ d o) (GlobalTheory.T.besselGroup_haar_isMulRightInvariant D V V₀ A L ρ d o) μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ

end GlobalTheory.AdelicSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySupportedSplitPlacesEqProdLocalParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitDecomp

open GlobalTheory.SplitCut GlobalTheory.FinPl

variable {D : D7}

theorem real_idem_mul (y : AE D) (hy : infPart D y = 0) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) * y = 0 := by
  refine key_gen (Module.finBasis D.host.F D.host.E) _ y fun k => ?_
  have h1 : fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) = 0 := by
    rw [← GlobalTheory.InfZeroFinSum.repr_map_id (Module.finBasis D.host.F D.host.E) (fstA D.host.F) y k]
    have : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) y = 0 := hy
    rw [this, map_zero, Finsupp.zero_apply]
  refine baseAdele_ext_infinite_finite ?_ ?_
  · rw [map_mul, h1, mul_zero, map_zero]
  · rw [map_mul, map_zero]
    exact zero_mul _

theorem entry_memAt (V : HSp D) (P : Pl D → Prop) (g : GA D V) (hg : g ∈ grpAt V P) (i j : Fin V.rank) :
    (mt V g - 1) i j ∈ idAt D P := by
  have h := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ idAt D P) => x.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk (idAt D P) (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk (idAt D P) (mt V g i j) =
      Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2

set_option maxHeartbeats 800000 in
open GlobalTheory.LocWeil.PlaceIdem in

theorem prod_of_grpAt : ∀ (D : D7) (V : HSp D) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)), Function.Injective (fun i => (q i).v) → ∀ g ∈ GlobalTheory.FinPl.grpAt V (fun p => ∃ i, p = (q i).v), ∃ h : Fin n → GA D V, (∀ i, SuppAt (q i).e V (h i)) ∧ g = ((List.finRange n).map h).prod := by
  intro D V n k _ _ _ _ q hv g hg
  set E : Fin n → AE D := fun i => algebraMap (AF D.host.F) (AE D) (eFin D.host.F (q i).v) with hEdef
  have hE : ∀ i, (q i).e + cA D (q i).e = E i := fun i => by
    obtain ⟨ε, hε, h⟩ := (q i).above
    rw [h, eFin_of_placeIdem hε]
  have hEE : ∀ i, E i * E i = E i := fun i => by
    simp only [hEdef, ← map_mul, eFin_idem]
  have hEc : ∀ i, cA D (E i) = E i := fun i => cA_algebraMap _
  have hEo : ∀ i i', i ≠ i' → E i * E i' = 0 := fun i i' hii => by
    simp only [hEdef, ← map_mul]
    rw [eFin_mul_eFin _ (fun h => hii (hv h)), map_zero]
  choose h hh using fun i => cut_exists V g (E i) (hEE i) (hEc i)
  set M := mt V g with hM
  refine ⟨h, fun i a b => ?_, ?_⟩
  · rw [hE i, hh i]
    exact idempotent_mul_cut_sub_one_entry _ (hEE i) M a b
  · apply mt_injective
    rw [mt_list_prod V h E M hh hEo _ (List.nodup_finRange n)]
    have hsum : ((List.finRange n).map E).sum = ∑ i, E i := (Fin.sum_univ_def E).symm
    rw [hsum]
    refine exists_widePullback_of_iteratedLine _ M fun a b => ?_
    have hm := entry_memAt V _ g hg a b
    unfold idAt at hm
    obtain ⟨hinf, hoff⟩ := Ideal.mem_inf.mp hm
    rw [Ideal.mem_iInf] at hoff
    have h1 := key (fun i => (q i).v) hv ((M - 1) a b) (fun u hu =>
      (RingHom.mem_ker).mp (hoff ⟨u, fun ⟨i, hi⟩ => hu ⟨i, hi.symm⟩⟩))
    rw [map_sub, map_sub, map_one, map_sum] at h1
    have h2 := real_idem_mul ((M - 1) a b) ((RingHom.mem_ker).mp hinf)
    have h3 : (1 - ∑ i, E i) = (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) - ∑ i, E i) +
        algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) := by ring
    rw [h3, add_mul, h1, h2, add_zero]

end GlobalTheory.SplitDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

namespace GlobalTheory.QVal

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

def places {r : ℕ} (Q : Fin r → QStep S) : GlobalTheory.FinPl.Pl D → Prop := fun v => ∃ i, (Q i).q.v = v

def integrand {r : ℕ} (Q : Fin r → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) (x : GA D S.J.W) (y : GA D S.B'.V) : ℂ :=
  GlobalTheory.PosOne.comb (conv (List.ofFn fun i => (Q i).e₀.mapDomain (Q i).gl₀)) fun a =>
    S.val c₁ c₂ (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₁)) f₁) (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₂)) f₂)
      φ f (g * a) (h₁ * x) (h₂ * y)

def value {r : ℕ} (Q : Fin r → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) : ℂ :=
  (∏ i, (Q i).volJ) * ∑ γ : ∀ i, (Q i).A₁, ∑ β : ∀ i, (Q i).A₂, (∏ i, (Q i).w₁ (γ i) * (Q i).w₂ (β i)) *
    S.val (aconv (c₁ :: List.ofFn fun i => (Q i).d₁ (γ i))) (aconv (c₂ :: List.ofFn fun i => (Q i).d₂ (γ i) (β i))) f₁ f₂ φ
      (trc (conv (List.ofFn fun i => ((Q i).e₂ (β i)).mapDomain (Q i).gl₂)) f) g h₁ h₂

def innerVal {r : ℕ} (Q : Fin (r + 1) → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) (x : GA D S.J.W) (y : GA D S.B'.V) : ℂ :=
  (Q 0).volJ * ∑ γ : (Q 0).A₁, ∑ β : (Q 0).A₂, ((Q 0).w₁ γ * (Q 0).w₂ β) *
    integrand (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ γ]) (aconv [c₂, (Q 0).d₂ γ β]) f₁ f₂ φ
      (trc (((Q 0).e₂ β).mapDomain (Q 0).gl₂) f) g h₁ h₂ x y

def Hyps {r : ℕ} (Q : Fin r → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) : Prop :=
  (∀ i, (Q i).Away c₁ ∧ (Q i).Away c₂) ∧ IsThetaFunO ψ _ _ f₁ ∧ IsThetaFunO ψ _ _ f₂ ∧ (∀ i, (Q i).Vac f₁ f₂) ∧
    IsContAut S.B.A φ ∧ IsContAut S.B'.V f ∧ (∀ i, (Q i).Typed f) ∧ g ∈ GlobalTheory.FinPl.grpOff S.B.V (places Q) ∧
    h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (places Q) ∧ h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (places Q)

def Norm {r : ℕ} (Q : Fin r → QStep S) (μ₁ : Measure (GlobalTheory.FinPl.grpAt S.J.W (places Q)))
    (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W (places Q)))) (μ₂ : Measure (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))
    (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))) : Prop :=
  μ₁.IsHaarMeasure ∧ ρ₁.IsHaarMeasure ∧ μ₂.IsHaarMeasure ∧ ρ₂.IsHaarMeasure ∧
    μ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1} = 1 ∧ ρ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1.1} = 1 ∧
    μ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1} = 1 ∧ ρ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1.1} = 1

def LocNorm (Q₀ : QStep S) (m₁ : Measure (GL (Q₀.n₁ ⊕ Fin (Q₀.c + 1 + 1)) Q₀.k)) (s₁ : Measure (RFJ Q₀.k Q₀.n₁ (Q₀.c + 1 + 1) (σ + 1)))
    (m₂ : Measure (GL (Q₀.n₂ ⊕ Fin (Q₀.c + 1)) Q₀.k)) (s₂ : Measure (R Q₀.k Q₀.n₂ (Q₀.c + 1) (σ + 1))) : Prop :=
  m₁.IsHaarMeasure ∧ m₁ (KO Q₀.k (Q₀.n₁ ⊕ Fin (Q₀.c + 1 + 1))) = 1 ∧ s₁.IsHaarMeasure ∧
    s₁ {x | x.1 ∈ KO Q₀.k (Q₀.n₁ ⊕ Fin (Q₀.c + 1 + 1))} = 1 ∧ m₂.IsHaarMeasure ∧ m₂ (KO Q₀.k (Q₀.n₂ ⊕ Fin (Q₀.c + 1))) = 1 ∧
    s₂.IsHaarMeasure ∧ s₂ {x | x.1 ∈ KO Q₀.k (Q₀.n₂ ⊕ Fin (Q₀.c + 1))} = 1

def levJ {r : ℕ} (Q : Fin r → QStep S) : Subgroup (GlobalTheory.FinPl.grpAt S.J.W (places Q)) :=
  (⨆ i, (Q i).L₁.J.map (Q i).gl₁).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W (places Q))

def levB {r : ℕ} (Q : Fin r → QStep S) : Subgroup (GlobalTheory.FinPl.grpAt S.B'.V (places Q)) :=
  (⨆ i, (Q i).L₂.J.map (Q i).gl₂).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V (places Q))

end GlobalTheory.QVal

namespace GlobalTheory.QVal

def ValQr (D : D7) (r : ℕ) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : Fin r → QStep S),
    Function.Injective (fun i => (Q i).q.v) →
  ∀ (μ₁ : Measure (GlobalTheory.FinPl.grpAt S.J.W (places Q))) (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W (places Q))))
    (μ₂ : Measure (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))
    (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))), Norm Q μ₁ ρ₁ μ₂ ρ₂ →
  ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ →
    Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 y.1) (value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂)

theorem valQ_of_valQr (D : D7) (h : ∀ r, ValQr D r) : ValQ D := by
  intro ψ hψ σ S r Q hinj P hP μ₁ ρ₁ μ₂ ρ₂ a1 a2 a3 a4 a5 a6 a7 a8 c₁ c₂ hc f₁ f₂ t1 t2 hv φ f hφ hf ht g hg h₁ hh₁ h₂ hh₂
  have e : P = places Q := funext fun v => propext (hP v)
  subst e
  exact h r ψ hψ σ S Q hinj μ₁ ρ₁ μ₂ ρ₂ ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ c₁ c₂ f₁ f₂ φ f g h₁ h₂
    ⟨hc, t1, t2, hv, hφ, hf, ht, hg, hh₁, hh₂⟩

end GlobalTheory.QVal

namespace GlobalTheory.QVal
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

def pint {r : ℕ} (Q : Fin (r + 1) → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V)
    (x : GlobalTheory.FinPl.grpAt S.J.W (places fun i => Q i.succ) × GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k)
    (y : GlobalTheory.FinPl.grpAt S.B'.V (places fun i => Q i.succ) × GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k) : ℂ :=
  integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x.1.1 * (Q 0).gl₁ x.2) (y.1.1 * (Q 0).gl₂ y.2)
end GlobalTheory.QVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepLinearModelGLPairApplyMemSchwartzBruhatFu
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitWeil.ValOne

theorem om_val_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a]
    [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) (Φ : SB (Matrix b a k)),
    om μ g h Φ.1 ∈ SB (Matrix b a k) :=
  fun _ _ _ _ _ _ _ _ _ _ _ μ g h Φ => GlobalTheory.SplitWeil.om_mem_SB μ g h Φ.2

end GlobalTheory.SplitWeil.ValOne
end

