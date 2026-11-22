import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupportedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceSymplectic_self_zero_splitSupported : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (u : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) u →
    (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∨ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0) →
    ∀ ξ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E,
      symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u = 0 := by
  first | exact @GlobalTheory.VacIso.symp_self_eq_zero | exact GlobalTheory.VacIso.symp_self_eq_zero | (intros; apply GlobalTheory.VacIso.symp_self_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupConjHermitianAutomorphisms
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

noncomputable section

namespace GlobalTheory.SWLink.Conj

variable {D : D7}

def cjG (D : D7) (k : ℕ) : GL (Fin k) (AE D) →* GL (Fin k) (AE D) := Matrix.GeneralLinearGroup.map (cA D)

theorem cjG_val {k : ℕ} (g : GL (Fin k) (AE D)) : (cjG D k g).1 = cj g.1 := rfl

theorem cjG_cjG {k : ℕ} (g : GL (Fin k) (AE D)) : cjG D k (cjG D k g) = g := Units.ext (cj_cj g.1)

theorem continuous_cj {m n : ℕ} : Continuous (cj : Mx D m n → Mx D m n) :=
  continuous_id.matrix_map GlobalTheory.FockCompare.ThetaCont.continuous_conj

theorem continuous_cjG (k : ℕ) : Continuous (cjG D k) := by
  refine Units.continuous_iff.2 ⟨continuous_cj.comp Units.continuous_val, ?_⟩
  exact continuous_cj.comp Units.continuous_coe_inv

theorem mem_iff (V : HSp D) (g : GL (Fin V.rank) (AE D)) :
    g ∈ UG (cAl D) (incM D.host.F (-V.gram)) ↔ cjG D V.rank g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  show (g.1ᵀ * incM D.host.F (-V.gram) * g.1.map (cAl D) : Mx D V.rank V.rank) = incM D.host.F (-V.gram) ↔
    (adj (cj g.1) * rat V.gram * cj g.1 : Mx D V.rank V.rank) = rat V.gram
  rw [map_cAl, incM_eq, rat_neg, adj_eq, cj_cj, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

def conjEquiv (V : HSp D) : UD D (-V.gram) ≃ₜ* GA D V where
  toFun h := (⟨cjG D V.rank h.1, (mem_iff V h.1).1 h.2⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)
  invFun g := ⟨cjG D V.rank (matHom V g), (mem_iff V _).2 (by
    rw [cjG_cjG]; exact (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2)⟩
  left_inv h := Subtype.ext (cjG_cjG h.1)
  right_inv g := Subtype.ext (cjG_cjG (matHom V g))
  map_mul' h h' := Subtype.ext (map_mul (cjG D V.rank) h.1 h'.1)
  continuous_toFun := ((continuous_cjG V.rank).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_cjG V.rank).comp continuous_subtype_val).subtype_mk _

theorem isConjV_conjEquiv (V : HSp D) : IsConjV V (conjEquiv V) := fun _ => rfl

theorem conjEquiv_symm_val (V : HSp D) (g : GA D V) : ((conjEquiv V).symm g).1 = cjG D V.rank (matHom V g) := rfl

theorem mem_ratU_iff (V : HSp D) (h : UD D (-V.gram)) : h ∈ ratU D.sp.cm.sig (-V.gram) ↔ conjEquiv V h ∈ GQ V := by
  constructor
  · rintro ⟨γ, hγ⟩
    rw [mem_GQ_iff]
    refine ⟨γ.1.map D.sp.cm.sig, ?_⟩
    have h1 : (rat γ.1 : Mx D V.rank V.rank) = umat h := congrArg Units.val hγ
    show (rat (γ.1.map D.sp.cm.sig) : Mx D V.rank V.rank) = cj (umat h)
    rw [← h1, cj_rat]
  · rintro ⟨γ, -, hγ⟩
    refine ⟨Matrix.GeneralLinearGroup.map (D.sp.cm.sig : D.host.E →+* D.host.E) γ, Units.ext ?_⟩
    have h1 : (rat γ.1 : Mx D V.rank V.rank) = cj (umat h) := congrArg Units.val hγ
    show (rat (γ.1.map D.sp.cm.sig) : Mx D V.rank V.rank) = umat h
    rw [← cj_rat, h1, cj_cj]

theorem exists_conj : ∀ (D : D7) (V : HSp D), ∃ ι : UD D (-V.gram) ≃ₜ* GA D V, IsConjV V ι ∧ ∀ h, h ∈ ratU D.sp.cm.sig (-V.gram) ↔ ι h ∈ GQ V :=
  fun _ V => ⟨conjEquiv V, isConjV_conjEquiv V, mem_ratU_iff V⟩

end GlobalTheory.SWLink.Conj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacOfMemSchwartzA
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ResAniso.VacSchwartz

open Classical in

theorem realPar_ne_zero (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsCharAF D.host.F ψ) (l : D.what₂.Tau → ℝ) (hl : StdUnn.HasRealPar ψ θ l) (τ₀ : D.what₂.Tau) : l τ₀ ≠ 0 := by
  intro h0
  obtain ⟨a, ha, hinf⟩ := GlobalTheory.AdeleCharConductor.exists_scaling hψ
  have hbij := GlobalTheory.CMTypePlaces.places_bijective D
  let w : D.what₂.Tau → InfinitePlace D.host.F := fun τ =>
    InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))
  have hemb : ∀ τ, (w τ).embedding = (tauE D τ).comp (algebraMap D.host.F D.host.E) := fun τ =>
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))
  have hθ' : ∀ τ (x : Ainf D.host.F), θ τ (x ⊗ₜ[D.host.F] (1 : D.host.E)) =
      InfinitePlace.Completion.extensionEmbedding (w τ) (x (w τ)) := fun τ =>
    congrFun ((InfiniteAdeleRing.denseRange_algebraMap D.host.F).equalizer (hθ τ).2
      ((InfinitePlace.Completion.isometry_extensionEmbedding (w τ)).continuous.comp (continuous_apply (w τ)))
      (funext fun b => by
        show θ τ (algebraMap D.host.F (Ainf D.host.F) b ⊗ₜ[D.host.F] (1 : D.host.E)) = _
        rw [GlobalTheory.StdRat.tmul_one_eq, (hθ τ).1, Function.comp_apply]
        erw [GlobalTheory.AdeleCharConductor.extensionEmbedding_algebraMap (w τ) b, hemb]
        rfl))
  set e : ℝ := ((w τ₀).embedding a).re with he
  have hre : ((w τ₀).embedding a).im = 0 := by
    have hr : NumberField.ComplexEmbedding.IsReal (w τ₀).embedding :=
      InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal _)
    have := congrArg (fun φ : D.host.F →+* ℂ => φ a) hr
    exact Complex.conj_eq_iff_im.1 this
  have he0 : e ≠ 0 := by
    intro h
    apply ha
    have : (w τ₀).embedding a = 0 := Complex.ext (by simpa [he] using h) (by simpa using hre)
    exact (map_eq_zero_iff _ (w τ₀).embedding.injective).1 this
  obtain ⟨x, hx⟩ := GlobalTheory.StdUnn.RealPar.exists_real_point hθ τ₀ (1 / (2 * e))
  have e1 := hl x
  simp only [hx, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, h0, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero] at e1
  have e2 := hinf x
  have hsum : ∑ u : InfinitePlace D.host.F, (u.embedding a).re *
      (InfinitePlace.Completion.extensionEmbedding u (x u)).re = e * (1 / (2 * e)) := by
    rw [← hbij.sum_comp (fun u : InfinitePlace D.host.F => (u.embedding a).re *
      (InfinitePlace.Completion.extensionEmbedding u (x u)).re)]
    have hterm : ∀ τ, ((w τ).embedding a).re * (InfinitePlace.Completion.extensionEmbedding (w τ) (x (w τ))).re =
        if τ = τ₀ then e * (1 / (2 * e)) else 0 := fun τ => by
      rw [← hθ' τ x, hx τ]
      split_ifs with h
      · subst h; simp [he]
      · simp
    refine (Finset.sum_congr rfl fun τ _ => hterm τ).trans ?_
    simp
  rw [hsum, e1] at e2
  have h2 : e * (1 / (2 * e)) = 1 / 2 := by field_simp
  rw [h2] at e2
  have h3 : (2 * Real.pi * Complex.I * (((1 / 2 : ℝ)) : ℂ)) = Real.pi * Complex.I := by push_cast; ring
  rw [h3, Complex.exp_pi_mul_I] at e2
  norm_num at e2

end GlobalTheory.ResAniso.VacSchwartz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumEigenvalueIndependentOfTheta
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacThetaInd

theorem psi_half_symp_theta_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (θ θ' : 𝓞 E), (θ : E) + σ θ = 1 → (θ' : E) + σ θ' = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ' : E)) (incM F X.J) (incM F W.J) γ γ) := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW v θ θ' hθ hθ' γ hγ
  have hσ : ∀ x : E, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hc : ∀ z, cA σ (cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [cA, hσ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hi : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have ht : cA σ (hTens (cA σ) (incM F X.J) (incM F W.J) γ γ) = -hTens (cA σ) (incM F X.J) (incM F W.J) γ γ :=
    GlobalTheory.VacCocycle.conj_hTens (cA σ) hc (fun i j => by simp only [incM, Matrix.map_apply, hi, hX.herm])
      (fun i j => by simp only [incM, Matrix.map_apply, hi, hW.skew, map_neg]) γ γ
  set t := hTens (cA σ) (incM F X.J) (incM F W.J) γ γ with htdef
  have htr : ∀ z, Algebra.trace (AF F) (AE F E) (cA σ z) = Algebra.trace (AF F) (AE F E) z :=
    GlobalTheory.VacCocycle.trace_conj (cA σ) hc
  set a := inclR (F := F) (AF F) (θ : E) with ha
  set a' := inclR (F := F) (AF F) (θ' : E) with ha'
  have hca : cA σ a = 1 - a := by
    rw [ha, hi, eq_sub_of_add_eq' hθ, map_sub, map_one]
  have hca' : cA σ a' = 1 - a' := by
    rw [ha', hi, eq_sub_of_add_eq' hθ', map_sub, map_one]
  set z := (a - a') * t with hz
  have hcz : cA σ z = z := by
    rw [hz, map_mul, map_sub, hca, hca', ht]; ring
  have h2 : Algebra.trace (AF F) (AE F E) z = 2 * Algebra.trace (AF F) (AE F E) (a * z) := by
    have e1 : Algebra.trace (AF F) (AE F E) (cA σ (a * z)) = Algebra.trace (AF F) (AE F E) (a * z) := htr _
    rw [map_mul, hca, hcz, sub_mul, one_mul, map_sub] at e1
    linear_combination e1
  have hmul : inclR (F := F) (AF F) (((θ * (θ - θ') : 𝓞 E)) : E) = a * (a - a') := by
    rw [ha, ha', ← map_sub, ← map_mul]; push_cast; rfl
  have key : symp (R := AF F) (cA σ) a (incM F X.J) (incM F W.J) γ γ =
      symp (R := AF F) (cA σ) a' (incM F X.J) (incM F W.J) γ γ +
        2 * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (((θ * (θ - θ') : 𝓞 E)) : E)) (incM F X.J) (incM F W.J) γ γ := by
    simp only [symp, hmul]
    rw [← htdef, mul_assoc, ← hz, ← h2, hz, sub_mul, map_sub]; ring
  have h1 := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v (θ * (θ - θ')) 1
    (by rw [map_one]; exact one_mem _) γ hγ γ hγ
  rw [key, mul_add, ← mul_assoc, invOf_mul_self, one_mul, AddChar.map_add_eq_mul, ← one_mul (symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (((θ * (θ - θ') : 𝓞 E)) : E)) (incM F X.J) (incM F W.J) γ γ), h1, mul_one]

end GlobalTheory.VacThetaInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfIntegralTrace
section
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped nonZeroDivisors

namespace GlobalTheory.CodiffValPrimeW

theorem valuation_le_one_of_mem_codiff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P →
    ∀ c : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * c))) → w.valuation E c ≤ 1 := by
  intro F E _ _ _ _ _ σ B hB w hw c hc

  have hF : ¬ differentIdeal ℤ (𝓞 F) ≤ (w.under (𝓞 F)).asIdeal :=
    GlobalTheory.DiffCoprimeP.not_le_differentIdeal_of_psiUnr hB.std _ (hB.psiP _ hw)

  have hu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := by
    haveI := hB.unram
    infer_instance
  have hE : ¬ differentIdeal ℤ (𝓞 E) ≤ w.asIdeal := by
    rw [GlobalTheory.SnMass.SkewVol.differentIdeal_eq_map_of_unramified hu]
    intro h
    exact hF (Ideal.map_le_iff_le_comap.1 h)
  obtain ⟨d, hdD, hdw⟩ := Set.not_subset.1 hE

  have hcd : c ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))]
    intro a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hc o)
    refine ⟨n, ?_⟩
    rw [hn, Algebra.traceForm_apply, mul_comm]

  have h1 : c * (d : E) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    have hne : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
      FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))
    have hmul := FractionalIdeal.mul_mem_mul hcd
      ((FractionalIdeal.mem_coeIdeal _).2 ⟨d, hdD, rfl⟩ :
        (d : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E))
    rwa [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), mul_inv_cancel₀ hne] at hmul
  obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).1 h1
  have hvx : w.valuation E (c * (d : E)) ≤ 1 := by
    rw [← hx]
    exact w.valuation_le_one x
  have hvd : w.valuation E (d : E) = 1 :=
    le_antisymm (w.valuation_le_one d) (not_lt.1 fun h => hdw ((w.valuation_lt_one_iff_mem d).1 h))
  rw [map_mul, hvd, mul_one] at hvx
  exact hvx

end GlobalTheory.CodiffValPrimeW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedUnifAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

namespace GlobalTheory.CondLESplit

open ValuativeRel

theorem isEquiv_Fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (valuation (Fv F v)).IsEquiv (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))) := by
  have : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))

theorem valued_unifAt {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) = WithZero.exp (-1 : ℤ) := by
  have he := isEquiv_Fv v
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπ' : Valued.v ((π : F) : Fv F v) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation']; exact hπ
  have hlt : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) < 1 :=
    he.lt_one_iff_lt_one.1 (hϖ ▸ uniformizer_lt_one)
  apply le_antisymm
  · have h0 : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) ≠ 0 := by simp
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega
  · rw [← hπ']
    have hπ1 : valuation (Fv F v) ((π : F) : Fv F v) < 1 := by
      refine he.lt_one_iff_lt_one.2 ?_
      rw [hπ', ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    exact (he _ _).1 (hϖ ▸ le_uniformizer_iff.2 hπ1)

end GlobalTheory.CondLESplit

open GlobalTheory.CondLESplit in
theorem GlobalTheory.CondLESplit.condLE_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) (ρ : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ →* ℂˣ) (n : ℕ),
    GlobalTheory.SplitFlip.CondLE (unifAt v) n (ρ.comp (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom)) ↔
      ∀ x : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ, Formalism.L2.Host.IsUnitAt (GlobalTheory.AdelicU.splitPrime τ) x →
        Valued.v ((x : (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ)) → ρ x = 1 := by
  intro F E _ _ _ _ _ v τ ρ n
  set hw := GlobalTheory.AdelicU.splitPrime_under τ
  set f := GlobalTheory.LFun.complMap hw
  have he := isEquiv_Fv v
  have hval : ∀ a : Fv F v, Valued.v (f a) = Valued.v a := GlobalTheory.LFun.SplitTie.valued_complMap τ hw
  have hbij : Function.Bijective f := GlobalTheory.LFun.SplitTie.complMap_bijective τ hw
  have key : ∀ y : (Fv F v)ˣ, y ∈ GlobalTheory.SplitFlip.unitCong (unifAt v ^ n) ↔
      (Formalism.L2.Host.IsUnitAt (GlobalTheory.AdelicU.splitPrime τ) (Units.map f.toMonoidHom y) ∧
        Valued.v (((Units.map f.toMonoidHom y : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ) :
          (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ))) := by
    intro y
    have h1 : ((Units.map f.toMonoidHom y : ((GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)ˣ) :
        (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E) = f y := rfl
    have hp : Valued.v (((unifAt v ^ n : (Fv F v)ˣ)) : Fv F v) = WithZero.exp (-(n : ℤ)) := by
      rw [Units.val_pow_eq_pow_val, map_pow, valued_unifAt, ← WithZero.exp_nsmul]
      congr 1; simp
    show (ValuativeRel.valuation (Fv F v) (y : Fv F v) = 1 ∧ ValuativeRel.valuation (Fv F v) ((y : Fv F v) - 1) ≤
        ValuativeRel.valuation (Fv F v) (((unifAt v ^ n : (Fv F v)ˣ)) : Fv F v)) ↔ _
    unfold Formalism.L2.Host.IsUnitAt
    rw [h1, he.eq_one_iff_eq_one, he, hp, ← map_one f, ← map_sub, hval, hval]
  constructor
  · intro h x hx1 hx2
    obtain ⟨a, ha⟩ := hbij.2 (x : (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E)
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [map_zero] at ha; exact x.ne_zero ha.symm
    set y := Units.mk0 a ha0
    have hy : Units.map f.toMonoidHom y = x := Units.ext ha
    have := h y ((key y).2 (hy ▸ ⟨hx1, hx2⟩))
    rw [← hy]; exact this
  · intro h y hy
    exact h _ ((key y).1 hy).1 ((key y).1 hy).2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SumSize.TopInt

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def primeUnder (w : PlL D) : ℕ := ringChar (𝓞 D.what₂.LL ⧸ w.asIdeal)

theorem primeUnder_mem (w : PlL D) : ((primeUnder w : ℕ) : 𝓞 D.what₂.LL) ∈ w.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem primeUnder_prime (w : PlL D) : (primeUnder w).Prime := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Finite (𝓞 D.what₂.LL ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  exact CharP.char_is_prime (𝓞 D.what₂.LL ⧸ w.asIdeal) (ringChar (𝓞 D.what₂.LL ⧸ w.asIdeal))

def kerLoss (G : GridData L sc) (δ : ℕ → ℝ) (C1 b : ℝ) (X Y : Node) (l n : ℕ) : ℝ :=
  (((∑ τ, ∑ a, (wt G Y τ).natW a : ℕ) : ℝ) + (D.R.f : ℝ) * (G.V X).rank * (G.V Y).rank) *
      (δ l + (if l = D.host.d then 1 else 0) + n) +
    (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (if (l : ℝ) ≤ C1 * b then Real.logb l (C1 * b) else 0)

def topDl (G : GridData L sc) (δ : ℕ → ℝ) (C1 b : ℝ) (w : PlL D) : ℝ :=
  (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * C1 *
    ∑ j ∈ Finset.range D.R.m, kerLoss G δ C1 b (.top j) (.top (j + 1)) (primeUnder w) (depL G (primeUnder w))

theorem vw_natCast_nonneg (w : PlL D) (n : ℕ) : 0 ≤ vw w ((n : ℕ) : D.what₂.LL) := by
  have e : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) ((n : ℕ) : D.what₂.LL) =
      ((Ideal.span {((n : ℕ) : 𝓞 D.what₂.LL)} : Ideal (𝓞 D.what₂.LL)) : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, map_natCast]
  unfold vw
  rw [e]
  exact FractionalIdeal.count_coe_nonneg _ _ _

theorem kerLoss_nonneg (G : GridData L sc) {δ : ℕ → ℝ} (hδ : ∀ l, 0 ≤ δ l) (C1 b : ℝ) (X Y : Node) {l : ℕ} (hl : l.Prime)
    (n : ℕ) : 0 ≤ kerLoss G δ C1 b X Y l n := by
  unfold kerLoss
  have h1 : 0 ≤ (if l = D.host.d then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have h2 : 0 ≤ (if (l : ℝ) ≤ C1 * b then Real.logb l (C1 * b) else 0) := by
    split_ifs with h
    · exact Real.logb_nonneg (by exact_mod_cast hl.one_lt) (le_trans (by exact_mod_cast hl.one_lt.le) h)
    · exact le_rfl
  have := hδ l
  positivity

theorem kerLoss_mono (G : GridData L sc) (δ : ℕ → ℝ) (C1 b : ℝ) (X Y : Node) (l : ℕ) {n n' : ℕ} (h : n ≤ n') :
    kerLoss G δ C1 b X Y l n ≤ kerLoss G δ C1 b X Y l n' := by
  unfold kerLoss
  have : (n : ℝ) ≤ n' := by exact_mod_cast h
  gcongr

theorem le_topDl (G : GridData L sc) {δ : ℕ → ℝ} (hδ : ∀ l, 0 ≤ δ l) {C1 : ℝ} (hC1 : 0 ≤ C1) (b : ℝ) (w : PlL D) {j : ℕ}
    (hj : j < D.R.m) {n : ℕ} (hn : n ≤ depL G (primeUnder w)) :
    (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * C1 * kerLoss G δ C1 b (.top j) (.top (j + 1)) (primeUnder w) n ≤
      topDl G δ C1 b w := by
  unfold topDl
  have h0 : (0 : ℝ) ≤ (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * C1 :=
    mul_nonneg (by exact_mod_cast vw_natCast_nonneg w _) hC1
  refine mul_le_mul_of_nonneg_left ?_ h0
  refine le_trans (kerLoss_mono G δ C1 b _ _ _ hn) ?_
  exact Finset.single_le_sum (f := fun j => kerLoss G δ C1 b (.top j) (.top (j + 1)) (primeUnder w) (depL G (primeUnder w)))
    (fun j _ => kerLoss_nonneg G hδ C1 b _ _ (primeUnder_prime w) _) (Finset.mem_range.2 hj)

theorem inLat_mono {n : ℕ} {lam : D.what₂.Tau → DomWeight n} {w : PlL D} {a a' : ℝ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {v : VV ℂ lam} (h : InLat lam w a Λ v) (ha : a ≤ a') : InLat lam w a' Λ v := by
  obtain ⟨u, s, h1, h2, h3, h4⟩ := h
  exact ⟨u, s, h1, h2, h3.trans ha, h4⟩

end GlobalTheory.SumSize.TopInt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIntegralPointSkewLatticeUnitVectorSameEigenStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_integralPoint_skewLatticeUnitVector_same_eigen : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (r : GA D a), r ∈ intG D a → ∀ c : ℂ, W.Om r 1 e0 = c • e0 → W.Om r 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0) = c • Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := by
  first | exact @GlobalTheory.FunObj.EigUnit.eig_unit | exact GlobalTheory.FunObj.EigUnit.eig_unit | (intros; apply GlobalTheory.FunObj.EigUnit.eig_unit <;> assumption)
end

