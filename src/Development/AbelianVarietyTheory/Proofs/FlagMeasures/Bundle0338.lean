import Mathlib
import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0331
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0016
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealOrbitalIntegralHsNormEqProdLocal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0020
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelevantSetZeroGNotIdentity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStarStableIdealAbsorbingMinors
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0258
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0253
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0255
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0257
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0325
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceFirstFactorLocalFrame
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdSubEqProdFactorial
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.WeylDimU

theorem prod_sub_eq_prod_factorial (k : ℕ) :
    ∏ a : Fin k, ∏ b ∈ Finset.univ.filter (fun b : Fin k => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  rcases k with _ | m
  · simp
  have h := Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) m
  rw [Matrix.det_vandermonde, ← Nat.prod_range_succ_factorial, Nat.cast_prod] at h
  simp only [Finset.filter_lt_eq_Ioi]
  rw [← h]

theorem finrank_space {k : ℕ} (lam : Formalism.BasicNotions.DomWeight k) (u : Fin k → ℝ)
    (hu : ∀ a, (lam.w a : ℝ) = u a - (((k : ℝ) - 1) / 2 - (a : ℕ))) :
    (Module.finrank ℂ (GlobalTheory.DualWeyl.Space lam.natW) : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  have h := Formalism.L2.G.Model.weyl_dualWeyl ℂ k lam.natW (Formalism.BasicNotions.factNatW k lam).1
  have h2 := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [Rat.cast_natCast, Rat.cast_prod] at h2
  refine Eq.trans h2 ?_
  rw [← prod_sub_eq_prod_factorial, vand, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_div_distrib, Finset.prod_filter]
  refine Finset.prod_congr rfl fun b _ => ?_
  split_ifs
  · push_cast
    congr 1
    linarith [hu a, hu b, GlobalTheory.NablaType.natW_add lam a, GlobalTheory.NablaType.natW_add lam b]
  · simp

theorem finrank_eq (k : ℕ) (u : Fin k → ℝ) (hu : IsHCParam u) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (hπ : IsHCTypeU k u π) :
    (Module.finrank ℂ H : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  obtain ⟨hs, hm⟩ := hu
  choose m hm using hm
  have hm' : StrictAnti m := fun a b hab => by
    have := hs hab
    have h2 : (m b : ℝ) < m a := by linarith [hm a, hm b]
    exact_mod_cast h2
  have hL : Antitone fun a : Fin k => m a + (a : ℕ) := by
    rcases k with _ | n
    · exact fun a => a.elim0
    rw [Fin.antitone_iff_succ_le]
    intro i
    have := hm' (Fin.castSucc_lt_succ (i := i))
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  let lam : Formalism.BasicNotions.DomWeight k := ⟨fun a => m a + (a : ℕ), hL⟩
  have hw : ∀ a, (lam.w a : ℝ) = u a - (((k : ℝ) - 1) / 2 - (a : ℕ)) := fun a => by
    simp only [lam]
    push_cast
    linarith [hm a]
  have hK := GlobalTheory.NablaType.isKTypeOf_act lam
  have hT : IsHCTypeU k u (GlobalTheory.NablaType.act lam) := by
    refine ⟨?_, inferInstance, GlobalTheory.NablaType.isURepOn_act lam, ?_⟩
    · obtain ⟨v, -, hv, -⟩ := hK.2.2.2.1
      exact ⟨v, 0, hv⟩
    · convert hK using 1
      funext a
      unfold allPos
      rw [GlobalTheory.DefiniteCheck.lowK_const, hw]
  obtain ⟨A, -⟩ := GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU k u _ _ _ _ hπ hT
  rw [A.finrank_eq]
  exact finrank_space lam u hw

theorem weyl_dimension : ∀ (k : ℕ) (u : Fin k → ℝ), IsHCParam u → (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π → (Module.finrank ℂ H : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ)) ∧ (dimPiU k u : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  intro k u hu
  refine ⟨fun H _ _ π hπ => finrank_eq k u hu H π hπ, ?_⟩
  obtain ⟨H, _, _, π, hπ⟩ := GlobalTheory.CompactDS.exists_isHCTypeU k u hu
  have hne : {d | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π ∧ Module.finrank ℂ H = d}.Nonempty :=
    ⟨_, H, _, _, π, hπ, rfl⟩
  obtain ⟨H', _, _, π', hπ', e⟩ := Nat.sInf_mem hne
  rw [dimPiU, ← e]
  exact finrank_eq k u hu H' π' hπ'

end GlobalTheory.WeylDimU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryFixingActsOnComplementFrameStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unitary_fixing_acts_on_complement_frame : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) → ∃ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm ∧ ∀ j, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i) := by
  first | exact @GlobalTheory.St.unitary_fix_acts_on_complement_frame | exact GlobalTheory.St.unitary_fix_acts_on_complement_frame | (intros; apply GlobalTheory.St.unitary_fix_acts_on_complement_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryFixingMemRationalStabiliserStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unitary_fixing_mem_rationalStabiliser : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ₀ : GL (Fin X.B.I.n) X.B.I.E), γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) → ∃ γ : Gam X u, (∀ v, uMat ((γ : X.B.I.GA).1 v) = (X.B.I.P v)⁻¹ * (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) ∧ X.B.I.fmat (γ : X.B.I.GA).2 = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := by
  first | exact @GlobalTheory.St.rat_unitary_fixing_mem_gam | exact GlobalTheory.St.rat_unitary_fixing_mem_gam | (intros; apply GlobalTheory.St.rat_unitary_fixing_mem_gam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealOrbitalIntegralHsNormEqProdLocalStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realOrbitalIntegral_hsNorm_eq_prod_local : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (ν : Measure X.B.I.Ginf), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v)) (μl v)) → (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) → IsQuotMeasS X.B.I (Measure.pi μl) ν → (∀ v, ∀ s ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v), ∀ x, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (s * x)) (X.Wloc u' v ((γ v)⁻¹ * (s * x))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v x) (X.Wloc u' v ((γ v)⁻¹ * x))) → hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vpi u); Formalism.L2.SG.TermOp.OO ν Set.univ (X.Wu u) (X.Wu u') γ) = ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (γ v)) := by
  first | exact @GlobalTheory.OrbQuotProd.oo_quot | exact GlobalTheory.OrbQuotProd.oo_quot | (intros; apply GlobalTheory.OrbQuotProd.oo_quot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlacesFrameMatrixEqRationalOfRationalStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaces_frameMatrix_eq_rational_of_rational : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ (s : X.B.I.Ginf) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E), (∀ v, uMat (s v) = (X.B.I.P v)⁻¹ * γ₀.map (X.B.I.φ v) * X.B.I.P v) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → sTil X wt s = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (y₀.map X.ιE) := by
  first | exact @GlobalTheory.St.sTil_eq_atInf_of_rational | exact GlobalTheory.St.sTil_eq_atInf_of_rational | (intros; apply GlobalTheory.St.sTil_eq_atInf_of_rational <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermNormsGeOneAndBoundedStatement
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relevantTerm_norms_ge_one_and_bounded : ∀ (Cg cb Cw cT CT C0 CH C' Cl : ℝ), 0 ≤ CH → ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X)
    (u : D.what₂.Word), HostC → NFExC → LabC → TermC → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 →
    ∀ t ∈ relSet Y u, 1 ≤ k2Del D (jT t) (labT t) ∧ 1 ≤ DbL D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 ∧
      DbL D (jT t) (labT t) ≤ (Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2) ^ D.R.rS := by
  first | exact @GlobalTheory.TypeAsm.PairsLab.norms_of_relevant | exact GlobalTheory.TypeAsm.PairsLab.norms_of_relevant | (intros; apply GlobalTheory.TypeAsm.PairsLab.norms_of_relevant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuousStatement
section
open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightRegularRep_unitary_stronglyContinuous : ∀ B : RowsAut, B.R 1 = 1 ∧ (∀ g h, B.R (g * h) = B.R g * B.R h) ∧ (∀ g F, ‖B.R g F‖ = ‖F‖) ∧ (∀ F, Continuous fun g => B.R g F) ∧ ∀ F : B.I.L2 B.μf B.fund, (∀ᵐ y ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, B.I.ext F (γ * y) = B.I.ext F y) ∧ AEStronglyMeasurable (B.I.ext F) (B.I.muA B.μf) := by
  first | exact @GlobalTheory.RightRegFund.rightReg_unitary_continuous | exact GlobalTheory.RightRegFund.rightReg_unitary_continuous | (intros; apply GlobalTheory.RightRegFund.rightReg_unitary_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SkewLatticeInverseDifferentPowCovolume
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.SkewVol
theorem dom_of_basis {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {ι : Type} [Finite ι]
    (b : Module.Basis ι ℝ W) (v : W) :
    ∃! l, l ∈ (Submodule.span ℤ (Set.range b) : Set W) ∧ v + l ∈ ZSpan.fundamentalDomain b := by
  obtain ⟨⟨l, hl⟩, h1, h2⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b v
  refine ⟨l, ⟨hl, by simpa [Submodule.vadd_def, add_comm] using h1⟩, ?_⟩
  rintro l' ⟨hl', h'⟩
  have := h2 ⟨l', hl'⟩ (by simpa [Submodule.vadd_def, add_comm] using h')
  simpa using congrArg Subtype.val this

theorem dInv_ne_zero (K : Type) [Field K] [NumberField K] (j : ℕ) : dInv K j ≠ 0 := by
  unfold dInv
  refine pow_ne_zero _ (inv_ne_zero ?_)
  exact FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot

theorem skew_covol_dInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t : ℕ) (c : ℝ), 0 < c → HasDom volume (skewLat (σ : E →+* E) (dInv E (2 * t)) c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (1 / 2 - 2 * (t : ℝ)) * c ^ Fintype.card (InfinitePlace E))) := by
  intro F E _ _ _ _ _ σ hCM hU t c hc
  have hTC : IsTotallyComplex E := hCM.2.1
  have hTR : IsTotallyReal F := hCM.1
  have hσw : ∀ (w : InfinitePlace E) (x : E), w.embedding (σ x) = star (w.embedding x) :=
    fun w x => hCM.2.2.2 w.embedding x
  have hre : ∀ x : E, reV (σ x) = reV x := fun x => funext fun w => by simp [reV, hσw]
  have him : ∀ x : E, imV (σ x) = -imV x := fun x => funext fun w => by simp [imV, hσw]
  obtain ⟨e, he, hex⟩ := GlobalTheory.T.exists_mixedSpace_reIm_coords_totallyComplex E hTC
  obtain ⟨ι, _, b, hbs, hbv⟩ := GlobalTheory.T.fractionalIdeal_basis_transport_measurePreserving E volume e he (Units.mk0 (dInv E (2 * t)) (dInv_ne_zero E _))
  obtain ⟨e1, he1, he1x⟩ := GlobalTheory.T.exists_cmExtension_mixedSpace_realCoords F E σ hCM
  obtain ⟨ι1, _, b1, hb1s, hb1v⟩ :=
    GlobalTheory.T.fractionalIdeal_basis_transport_measurePreserving F volume e1 he1 (Units.mk0 (dInv F (2 * t)) (dInv_ne_zero F _))
  simp only [Units.val_mk0] at hbs hbv hb1s hb1v
  set Λ := Submodule.span ℤ (Set.range b) with hΛdef
  have hΛ : ∀ p, p ∈ Λ ↔ ∃ x ∈ dInv E (2 * t), (reV x, imV x) = p := by
    intro p
    rw [← SetLike.mem_coe, hbs]
    simp [hex]
  have hL1 : ∀ a, a ∈ (Submodule.span ℤ (Set.range b1) : Set (InfinitePlace E → ℝ)) ↔
      (a, (0 : InfinitePlace E → ℝ)) ∈ Λ := by
    intro a
    rw [hb1s, hΛ]
    simp only [Set.mem_image, Set.mem_setOf_eq, he1x, Prod.mk.injEq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h := (GlobalTheory.T.mem_inverseDifferentIdealPow_real_iff_unramified_cm F E σ hCM hU (2 * t) (algebraMap F E y)).2 ⟨y, hy, rfl⟩
      exact ⟨_, h.1, rfl, h.2⟩
    · rintro ⟨x, hx, rfl, h0⟩
      obtain ⟨y, hy, rfl⟩ := (GlobalTheory.T.mem_inverseDifferentIdealPow_real_iff_unramified_cm F E σ hCM hU _ _).1 ⟨hx, h0⟩
      exact ⟨y, hy, rfl⟩
  have hD1 : ∀ a, ∃! l, l ∈ {a : InfinitePlace E → ℝ | (a, (0 : InfinitePlace E → ℝ)) ∈ Λ.toAddSubgroup} ∧
      a + l ∈ ZSpan.fundamentalDomain b1 := by
    intro a
    obtain ⟨l, hl, hu⟩ := dom_of_basis b1 a
    exact ⟨l, ⟨(hL1 l).1 hl.1, hl.2⟩, fun l' hl' => hu l' ⟨(hL1 l').2 hl'.1, hl'.2⟩⟩
  have h2 : ∀ a y, (a, y) ∈ Λ → ((0 : InfinitePlace E → ℝ), (2 : ℝ) • y) ∈ Λ := by
    intro a y hay
    obtain ⟨x, hx, hxe⟩ := (hΛ _).1 hay
    rw [Prod.mk.injEq] at hxe
    refine (hΛ _).2 ⟨x - σ x, Submodule.sub_mem (dInv E (2 * t) : Submodule (𝓞 E) E) hx (GlobalTheory.T.cmExtension_conj_mem_inverseDifferentIdealPow F E σ hCM _ x hx), ?_⟩
    have h1 : reV (x - σ x) = reV x - reV (σ x) := funext fun w => by simp [reV]
    have h1' : imV (x - σ x) = imV x - imV (σ x) := funext fun w => by simp [imV]
    rw [h1, h1', hre, him, ← hxe.2]
    refine Prod.ext ?_ ?_
    · simp
    · funext w; simp; ring
  have hsp : Submodule.span ℝ (Λ : Set ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ))) = ⊤ := by
    rw [hΛdef, Submodule.span_span_of_tower, b.span_eq]
  obtain ⟨D2, hD2m, hD2⟩ := GlobalTheory.T.exists_fundamentalDomain_snd_of_two_smul_mem' Λ hsp h2
  have hprod := GlobalTheory.T.existsUnique_prod_fundamentalDomain_of_extension Λ.toAddSubgroup _ D2 hD1 hD2
  have heq := GlobalTheory.T.addFundamentalDomain_measure_eq_of_countable ((volume : Measure (InfinitePlace E → ℝ)).prod (volume : Measure (InfinitePlace E → ℝ))) Λ _ _ ((ZSpan.fundamentalDomain_measurableSet b1).prod hD2m)
    (ZSpan.fundamentalDomain_measurableSet b) hprod (dom_of_basis b)
  rw [Measure.prod_prod, ← Measure.volume_eq_prod, hbv, hb1v] at heq
  have hL2 : ∀ y, (∃ a, (a, y) ∈ Λ) ↔ ∃ x ∈ dInv E (2 * t), imV x = y := by
    intro y
    simp only [hΛ, Prod.mk.injEq]
    constructor
    · rintro ⟨a, x, hx, -, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, x, hx, rfl, rfl⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_integer_add_conj_eq_one_of_formallyUnramified' F E σ hCM hU
  have hfin := GlobalTheory.T.scaledSkewLattice_fundamentalDomain_of_imaginaryParts F E σ hCM (dInv E (2 * t)) (fun x hx => GlobalTheory.T.cmExtension_conj_mem_inverseDifferentIdealPow F E σ hCM _ x hx) θ hθ c hc D2 _
    hD2m (fun y => by simpa only [Set.mem_setOf_eq, hL2] using hD2 y) rfl
  have hd : (1 : ℝ) ≤ |(discr F : ℝ)| := by
    have h := Int.one_le_abs (discr_ne_zero F)
    rw [← Int.cast_abs]
    exact_mod_cast h
  have hnc : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E) := by
    have h := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
    rw [IsTotallyComplex.nrRealPlaces_eq_zero E, zero_add] at h
    exact h.symm
  have hnr : InfinitePlace.nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
  rw [GlobalTheory.T.absNorm_inverseDifferentIdealPow_eq_discr, GlobalTheory.T.absNorm_inverseDifferentIdealPow_eq_discr, GlobalTheory.T.abs_discr_eq_sq_of_unramified_cmExtension F E σ hCM hU, hnc, hnr] at heq
  rw [GlobalTheory.T.covolumeQuotient_ofReal_identity _ c _ t _ hd hc heq.symm] at hfin
  exact hfin

end GlobalTheory.SnMass.SkewVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SlabMeasureSqueeze
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem slab_measure_squeeze : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε (maxK ε ∩ flagM ε W) E → (∀ i, (E i)ᴴ = -E i) → ∀ ν : Measure (Formalism.REAL.UJ ε), ν (maxK ε ∩ flagM ε W)ᶜ = 0 → (∀ l ∈ maxK ε ∩ flagM ε W, ν.map (fun g => g * l) = ν) → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η → ∀ᶠ r in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, u * m * k ∈ hsBall ε r → ν (hsBall ε (r / (1 + η))) ≤ ν {l | l * k ∈ slab ε E ρ r} ∧ ν {l | l * k ∈ slab ε E ρ r} ≤ ν (hsBall ε ((1 + η) * r)) := by
  intro n ε a j W hW d E hcut hskew ν hν hinv ρ η hρ hρ8 hη
  set S := maxK ε ∩ flagM ε W with hS
  obtain ⟨t, ht, hsq⟩ := GlobalTheory.T.iwasawa_slab_squeezed_between_balls n ε S d E hcut ρ η hρ hρ8 hη
  obtain ⟨r0, hr0, hnear⟩ := GlobalTheory.T.iwasawa_near_one_compact_near_levi_intersection n ε a j W hW t ht
  have hmem : Set.Iio (min t r0) ∈ nhds (0 : ℝ) := Iio_mem_nhds (lt_min ht hr0)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem] with r hr hr' u hu m hm k hk hball
  have hrpos : (0 : ℝ) < r := hr
  have hrlt : r < min t r0 := hr'
  have hrt : r < t := lt_of_lt_of_le hrlt (min_le_left _ _)
  have hrr0 : r < r0 := lt_of_lt_of_le hrlt (min_le_right _ _)

  have hb : nrm (uMat (u * m * k) - 1) ≤ r := hball
  obtain ⟨l0, hl0S, hl0⟩ := hnear u hu m hm k hk (le_trans hb hrr0.le)

  obtain ⟨l1, hl1S, hcrd, hmin⟩ := GlobalTheory.T.exists_nearest_point_coset_orthogonal_lieAlgebra n ε S d E hcut (fun x hx => hx.1) hskew k hk
  have hnrm : nrm (uMat (l1 * k) - 1) < t := lt_of_le_of_lt (hmin l0 hl0S) hl0
  have key := fun l (hl : l ∈ S) => hsq r hrpos hrt (l1 * k) hnrm hcrd l hl

  have hA : ν {l | l * k ∈ slab ε E ρ r} = ν {l | l * (l1 * k) ∈ slab ε E ρ r} := by
    calc ν {l | l * k ∈ slab ε E ρ r}
        = (ν.map (fun g => g * l1)) {l | l * k ∈ slab ε E ρ r} := by rw [hinv l1 hl1S]
      _ = ν ((fun g => g * l1) ⁻¹' {l | l * k ∈ slab ε E ρ r}) :=
          (Homeomorph.mulRight l1).toMeasurableEquiv.map_apply _
      _ = ν {l | l * (l1 * k) ∈ slab ε E ρ r} := by
          congr 1
          ext l
          simp only [Set.mem_preimage, Set.mem_setOf_eq, mul_assoc]
  rw [hA]
  constructor
  · calc ν (hsBall ε (r / (1 + η)))
        ≤ ν (hsBall ε (r / (1 + η)) ∩ S ∪ Sᶜ) := by
          apply measure_mono
          intro l hl
          by_cases h : l ∈ S
          · exact Or.inl ⟨hl, h⟩
          · exact Or.inr h
      _ ≤ ν (hsBall ε (r / (1 + η)) ∩ S) + ν Sᶜ := measure_union_le _ _
      _ = ν (hsBall ε (r / (1 + η)) ∩ S) := by rw [hν, add_zero]
      _ ≤ ν {l | l * (l1 * k) ∈ slab ε E ρ r} :=
          measure_mono (fun l hl => (key l hl.2).1 hl.1)
  · calc ν {l | l * (l1 * k) ∈ slab ε E ρ r}
        ≤ ν ({l | l * (l1 * k) ∈ slab ε E ρ r} ∩ S ∪ Sᶜ) := by
          apply measure_mono
          intro l hl
          by_cases h : l ∈ S
          · exact Or.inl ⟨hl, h⟩
          · exact Or.inr h
      _ ≤ ν ({l | l * (l1 * k) ∈ slab ε E ρ r} ∩ S) + ν Sᶜ := measure_union_le _ _
      _ = ν ({l | l * (l1 * k) ∈ slab ε E ρ r} ∩ S) := by rw [hν, add_zero]
      _ ≤ ν (hsBall ε ((1 + η) * r)) :=
          measure_mono (fun l hl => (key l hl.2).2 hl.1)

end GlobalTheory.IwConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceFirstFactorLocalFrameStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_firstFactor_localFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (t : ℕ) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (e : E ⊗[F] v.adicCompletion F), sp e = (1, 0) → ∀ (b bd : Fin n → Fin n → E ⊗[F] v.adicCompletion F), (∀ i, b i ∈ loc v L) → (∀ i, bd i ∈ loc v L) → (∀ i, b i = e • b i) → (∀ i, bd i = sigR cm.sig (v.adicCompletion F) e • bd i) → (∀ i j, ∃ s ∈ intV E v, hR cm.sig J (v.adicCompletion F) (bd i) (b j) - (if i = j then e else 0) = (g : E ⊗[F] v.adicCompletion F) * s) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range b ∪ Set.range bd) y) → ∀ (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * (e * a))) ≠ 1) → ∃ (fr : GL (Fin n) (v.adicCompletion F)) (ψ : AddChar (kv F v) ℂ), ψ ≠ 1 ∧ (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ c, (sp (y c)).1 = x c) ↔ ∀ c, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x c ∈ v.adicCompletionIntegers F) ∧ ∀ y ∈ levelVL cm.sig J v L, ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) ↔ InJ n t n false (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) ∧ ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) → psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * supSum (hR cm.sig J (v.adicCompletion F)) b bd y.1)) = lamJ ψ (fun _ => 1) n t 0 n (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
  first | exact @GlobalTheory.St.G.FirstFactorFrame.local_frame_first_factor | exact GlobalTheory.St.G.FirstFactorFrame.local_frame_first_factor | (intros; apply GlobalTheory.St.G.FirstFactorFrame.local_frame_first_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserUnitaryGroupHasGaugeMeasureStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliser_unitaryGroup_has_gaugeMeasure : PI.RhsWLim.W.GaugeK := by
  first | exact @GlobalTheory.GaugeKExists.gaugeK | exact GlobalTheory.GaugeKExists.gaugeK | (intros; apply GlobalTheory.GaugeKExists.gaugeK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoProdGaugeMeasuresGaugeBodyStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_prod_gaugeMeasures_gaugeBody : ∀ (n : ℕ) (ε : Fin n → Bool) (SN SM MainNotions : Set (Formalism.REAL.UJ ε)), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε SN EN → IsCut ε SM EM → IsCut ε MainNotions EK → (∀ v, gau EN EM EK EL v = 0 → v = 0) → ∀ μN μM μK : Measure (Formalism.REAL.UJ ε), IsGaugeSub SN dN μN → IsGaugeSub SM dM μM → IsGaugeSub MainNotions dK μK → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → Filter.Tendsto (fun r : ℝ => (μN.prod (μM.prod μK)) {x | (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧ gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ r} / ENNReal.ofReal (r ^ (dN + (dM + dK)))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (volume {v | gau EN EM EK EL v ≤ 1})) := by
  first | exact @GlobalTheory.IwConstBox.prod_gauge_body | exact GlobalTheory.IwConstBox.prod_gauge_body | (intros; apply GlobalTheory.IwConstBox.prod_gauge_body <;> assumption)
end

