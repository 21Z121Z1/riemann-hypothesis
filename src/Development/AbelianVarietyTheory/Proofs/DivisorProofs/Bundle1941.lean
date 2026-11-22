import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1922
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0413
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0215
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DataBoundOfHalfFlip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffValuationLossLeAddCharNegUnfoldingPhaseStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffValuationLossLe_addChar_neg_unfoldingPhase : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t), ∀ X Y (e : Vars (locGrid ch.G t P)),
    (ch.S.term t Φ β P).datum X Y ≠ 0 →
    moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) (fill one_le_sLen X Y e) ≠ 0 →
    ∀ w : PlL D, LossLe w ((psiAt ch.W P.1 (-phase X e) : Circle) : ℂ) 0 := by
  first | exact @GlobalTheory.UnfoldLoss.lossLe_psi_neg_phase | exact GlobalTheory.UnfoldLoss.lossLe_psi_neg_phase | (intros; apply GlobalTheory.UnfoldLoss.lossLe_psi_neg_phase <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundOfPublishedInputsStatement
section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ArchTens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_bound_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → BigC fun _ ch C _ => CoefAt ch C := by
  first | exact @GlobalTheory.ArchTens.VolSize.coefK | exact GlobalTheory.ArchTens.VolSize.coefK | (intros; apply GlobalTheory.ArchTens.VolSize.coefK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientModelTopClassesMapStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_model_top_classes_map : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b =>
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.top j)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.top (j + 1)))),
    (∀ u, ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ,
      ∃ (ρ' : Qbar →ₐ[ℚ] ℂ) (e0 : VC D (ch.G.V (.top j)).rank (ch.G.V (.top (j + 1))).rank → ℂ)
        (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.V (.top j)).rank → D.host.E))
        (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.V (.top (j + 1))).rank → D.host.E)) (κ : ℂ) (k n : ℕ) (r : Fin n → Qbar)
        (s : Fin n → VC D (ch.G.V (.top j)).rank (ch.G.V (.top (j + 1))).rank),
        Even ((ch.G.V (.top j)).rank * (ch.G.V (.top (j + 1))).rank) ∧
        oddE0 D D.host.ccK ch.S.Z.δ ch.S.Z.t0 _ _ e0 ∧ SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ 0 < k ∧
        (∀ i, k • s i ∈ La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) ∧ (∀ ρ₁ : Qbar →+* ℂ, ∑ i, ‖ρ₁ (r i)‖ ≤ 1) ∧
        lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ) = lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ) ∧
        (∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ)) t) ∧
        Formalism.L2.Ker.JetInVV ℂ (wt ch.G (.top j)) (wt ch.G (.top (j + 1))) (nuEnd ch.G (.top A.μ0 j)) ∧
        ∀ u, GlobalTheory.CoefModel.mapVV σ _ (f u) =
          Formalism.L2.Ker.jetOp (wt ch.G (.top j)) (wt ch.G (.top (j + 1)))
            (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fnConj D Qbar ρ' fun z => κ * ∑ i, (r i : ℂ) *
              U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) (Iop D (tor0 D D.host.ccK ch.S.Z.δ)
                (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) e0) z))
            (nuEnd ch.G (.top A.μ0 j)) (GlobalTheory.CoefModel.mapVV σ _ u) := by
  first | exact @GlobalTheory.KerConjTransport.conj_top_transport | exact GlobalTheory.KerConjTransport.conj_top_transport | (intros; apply GlobalTheory.KerConjTransport.conj_top_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRepresentativesInjectiveDoubleCoset
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RepsInj
open Matrix GlobalTheory.AdLat GlobalTheory.UCls

theorem cc_eq (D : D7) : IsCMField.complexConj D.host.E = GlobalTheory.Member.cF D :=
  AlgEquiv.ext fun x => ((GlobalTheory.Member.latHat_eq_hat_and_gram D D.sp.X').2.2.2.2.2.1 x).symm

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem hermA_single (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    hermA c G (Pi.single i 1) (Pi.single j 1) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G i j := by
  simp [hermA, Pi.single_apply]

theorem hermA_mulVec_single (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)) (i j : Fin n) :
    hermA c G (g *ᵥ Pi.single i 1) (g *ᵥ Pi.single j 1) =
      (gᵀ * G.map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) * g.map (sg (FiniteAdeleRing (𝓞 F) F) c)) i j := by
  simp only [hermA, Matrix.mul_apply, Finset.sum_mul, Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  rfl

theorem transpose_form' {A : Type} [CommRing A] {m : ℕ} (s : A →+* A) (J g : Matrix (Fin m) (Fin m) A) :
    gᵀ * Jᵀ * g.map s = Jᵀ ↔ Formalism.UG.cT s g * J * g = J := by
  rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, ← Matrix.mul_assoc, Formalism.UG.cT]

theorem unitary_of_isUA (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E))
    (h : IsUA c (-Jᵀ) g) :
    Formalism.UG.cT (sigR (FiniteAdeleRing (𝓞 F) F) (c : E →ₐ[F] E)) g * JR (FiniteAdeleRing (𝓞 F) F) J * g =
      JR (FiniteAdeleRing (𝓞 F) F) J := by
  rw [← transpose_form']
  have key : gᵀ * (-Jᵀ).map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) * g.map (sg (FiniteAdeleRing (𝓞 F) F) c) =
      (-Jᵀ).map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) := by
    ext i j
    rw [← hermA_mulVec_single, h.2, hermA_single, Matrix.map_apply]
  have e : (-Jᵀ).map (fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) = -(JR (FiniteAdeleRing (𝓞 F) F) J)ᵀ := by
    ext i j; simp [JR, inclR, TensorProduct.tmul_neg]
  rw [e, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at key
  exact key

theorem af_nontrivial : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  refine ⟨0, 1, fun h => ?_⟩
  have h2 : (0 : v.adicCompletion F) = 1 := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) h
  exact zero_ne_one h2

theorem incl_inj : Function.Injective (inclR (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) :=
  haveI := af_nontrivial (F := F)
  Algebra.TensorProduct.includeRight_injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)).injective

theorem cT_map_inclR (R : Type) [CommRing R] [Algebra F R] (c : E →ₐ[F] E) (γ : Matrix (Fin n) (Fin n) E) :
    (Formalism.UG.cT (c : E →+* E) γ).map (inclR R) = Formalism.UG.cT (sigR R c) (γ.map (inclR R)) := by
  ext i j
  simp [Formalism.UG.cT, sigR, inclR]

theorem rat_unitary (c : E ≃ₐ[F] E) (J γ : Matrix (Fin n) (Fin n) E) (h : IsUA c (-Jᵀ) (ratM F γ)) :
    γ.det ≠ 0 ∧ Formalism.UG.cT ((c : E →ₐ[F] E) : E →+* E) γ * J * γ = J := by
  have hr : ratM F γ = γ.map (inclR (FiniteAdeleRing (𝓞 F) F)) := rfl
  constructor
  · intro h0
    have hu := h.1
    rw [hr, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at hu
    haveI := af_nontrivial (F := F)
    haveI : Nontrivial (RA F E) := (incl_inj (F := F) (E := E)).nontrivial
    exact not_isUnit_zero hu
  · have hu := unitary_of_isUA c J _ h
    apply Matrix.map_injective (incl_inj (F := F) (E := E))
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, cT_map_inclR]
    exact hu

end Gen

theorem gq_of_isUA (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (h : IsUA (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (ratM (maximalRealSubfield D.host.E) γ)) :
    ∃ γ₀ ∈ GQ V, ((finHom V γ₀).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) =
      ratM (maximalRealSubfield D.host.E) γ := by
  rw [cc_eq] at h
  obtain ⟨hd, hu⟩ := rat_unitary _ _ _ h
  let γu : GL (Fin V.rank) D.host.E := ((Matrix.isUnit_iff_isUnit_det γ).2 (Ne.isUnit hd)).unit
  have hU : γu ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := hu
  have hm : Formalism.UG.bc (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) γu ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    show Formalism.UG.cT _ (γ.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))) * JR (AF D.host.F) V.gram * γ.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) =
      JR (AF D.host.F) V.gram
    rw [← cT_map_inclR, JR, ← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun M => M.map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))) hU
  refine ⟨⟨_, hm⟩, ⟨γu, hU, rfl⟩, ?_⟩
  ext i j
  rfl

theorem kf_of_isKM (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (M : ℕ) (Kf : Subgroup (GA D V)) (hK : IsLevelK V M Kf)
    (κ : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
    (h : IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M κ) :
    ∃ κA ∈ Kf, ((finHom V κA).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) = κ := by
  rw [cc_eq] at h
  have hu := unitary_of_isUA _ _ _ h.1
  let κu : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := ((Matrix.isUnit_iff_isUnit_det κ).2 h.1.1).unit
  have hmem : κu ∈ HR (Af D.host.F) D.sp.cm.sig V.gram := hu
  obtain ⟨κA, hG, hf⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).1 κu hmem
  refine ⟨κA, (hK κA).2 ⟨hG, ?_⟩, by rw [hf]; rfl⟩
  intro z hz
  rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1] at hz ⊢
  rw [hf]
  exact h.2.1 z hz

theorem reps_inj : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ) (gA : Comp → GA D V),
    IsLevelK V M Kf → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictIsUnif V dict Kf th rfl →
    (∀ k, (dict (gA k)).1 = k) → ∀ k k',
      GlobalTheory.UCls.UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
        ((finHom V (gA k)).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E))
        ((finHom V (gA k')).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) → k = k' := by
  intro D V Comp X dict Kf th M gA hK _ hD hgA k k' hE
  obtain ⟨γ, hγ, κ, hκ, he⟩ := hE
  obtain ⟨γ₀, hγ₀, hγf⟩ := gq_of_isUA D V γ hγ
  obtain ⟨κA, hκA, hκf⟩ := kf_of_isKM D V M Kf hK κ hκ
  have hfin : finHom V (gA k') = finHom V (γ₀ * gA k * κA) := by
    rw [map_mul, map_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact he.trans (by rw [← hγf, ← hκf])
  have hx : (γ₀ * gA k * κA)⁻¹ * gA k' ∈ GinfC V := by
    show finHom V _ = 1
    rw [map_mul, map_inv, hfin, inv_mul_cancel]
  have hk' : gA k' = γ₀ * gA k * κA * ((γ₀ * gA k * κA)⁻¹ * gA k') := by group
  obtain ⟨h1, h2, ⟨x0, -, h3⟩, -⟩ := hD
  have s3 : (dict (gA k')).1 = (dict (γ₀ * gA k * κA)).1 := by
    obtain ⟨γ', -, e⟩ := h3 (γ₀ * gA k * κA) _ hx
    rw [hk', e]
  have s2 : (dict (γ₀ * gA k * κA)).1 = (dict (γ₀ * gA k)).1 := by
    obtain ⟨γ', -, e⟩ := h2 κA hκA (γ₀ * gA k)
    rw [e]
  have s1 : (dict (γ₀ * gA k)).1 = (dict (gA k)).1 := by
    obtain ⟨γ', -, e⟩ := h1 γ₀ hγ₀ (gA k)
    rw [e]
  rw [← hgA k, ← hgA k', s3, s2, s1]

end GlobalTheory.RepsInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
section
noncomputable section

namespace GlobalTheory.ConeSoB

open MeasureTheory Filter
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d}

variable (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (K : Subgroup (UA σ X.J))
  (μK : Measure K) (μ : Measure (AE F E)ˣ) (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (ν : Chr F E) (z : ℕ)

def coneInt (Φ : Fn F n d) (k : UA σ X.J) (l : (AE F E)ˣ) (y : Fin n₁ × Fin d₁ → AF F) : ℂ :=
  e (M.co.rho B.ψ (u l) (om (k, 1) Φ)) y * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z

def IntOK (Φ : Fn F n d) : Prop :=
  ∀ y, (∀ k : K, Integrable (fun l => coneInt B M om e u ν z Φ k.1 l y) μ) ∧
    Integrable (fun k : K => ∫ l, coneInt B M om e u ν z Φ k.1 l y ∂μ) μK

theorem cone_apply (Φ : Fn F n d) (y : Fin n₁ × Fin d₁ → AF F) :
    cone B M om e K μK μ u ν z Φ y = ∫ k, ∫ l, coneInt B M om e u ν z Φ k.1 l y ∂μ ∂μK := rfl

variable {B M om e K μK μ u ν z}

theorem rho_lin (w : Matrix (Fin n) (Fin d) (AE F E)) (a b : ℂ) (Φ Ψ : Fn F n d) :
    M.co.rho B.ψ w (a • Φ + b • Ψ) = a • M.co.rho B.ψ w Φ + b • M.co.rho B.ψ w Ψ := by
  have hT : IsLinearMap ℂ (M.co.rho B.ψ w) :=
    ⟨fun f g => funext fun x => mul_add _ _ _, fun c f => funext fun x => mul_left_comm _ _ _⟩
  rw [hT.map_add, hT.map_smul, hT.map_smul]

theorem coneInt_lin (a b : ℂ) (Φ Ψ : Fn F n d) (k : UA σ X.J) (l : (AE F E)ˣ) (y : Fin n₁ × Fin d₁ → AF F) :
    coneInt B M om e u ν z (a • Φ + b • Ψ) k l y =
      a * coneInt B M om e u ν z Φ k l y + b * coneInt B M om e u ν z Ψ k l y := by
  simp only [coneInt, map_add, map_smul, rho_lin, LinearMap.map_add, LinearMap.map_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem coneInt_zero (k : UA σ X.J) (l : (AE F E)ˣ) (y : Fin n₁ × Fin d₁ → AF F) :
    coneInt B M om e u ν z 0 k l y = 0 := by
  have h := coneInt_lin (B := B) (M := M) (om := om) (e := e) (u := u) (ν := ν) (z := z) 0 0 0 0 k l y
  simpa using h

theorem intOK_zero : IntOK B M om e K μK μ u ν z 0 := fun y => by
  simp only [coneInt_zero, integral_zero]
  exact ⟨fun _ => integrable_zero _ _ _, integrable_zero _ _ _⟩

theorem intOK_lin (a b : ℂ) {Φ Ψ : Fn F n d} (hΦ : IntOK B M om e K μK μ u ν z Φ) (hΨ : IntOK B M om e K μK μ u ν z Ψ) :
    IntOK B M om e K μK μ u ν z (a • Φ + b • Ψ) ∧
      cone B M om e K μK μ u ν z (a • Φ + b • Ψ) = a • cone B M om e K μK μ u ν z Φ + b • cone B M om e K μK μ u ν z Ψ := by
  have inner : ∀ y (k : K), ∫ l, coneInt B M om e u ν z (a • Φ + b • Ψ) k.1 l y ∂μ =
      a * ∫ l, coneInt B M om e u ν z Φ k.1 l y ∂μ + b * ∫ l, coneInt B M om e u ν z Ψ k.1 l y ∂μ := fun y k => by
    simp only [coneInt_lin]
    rw [integral_add (((hΦ y).1 k).const_mul a) (((hΨ y).1 k).const_mul b), integral_const_mul, integral_const_mul]
  refine ⟨fun y => ⟨fun k => ?_, ?_⟩, ?_⟩
  · simp only [coneInt_lin]
    exact (((hΦ y).1 k).const_mul a).add (((hΨ y).1 k).const_mul b)
  · simp only [inner y]
    exact ((hΦ y).2.const_mul a).add ((hΨ y).2.const_mul b)
  · funext y
    rw [cone_apply]
    simp only [inner y]
    rw [integral_add ((hΦ y).2.const_mul a) ((hΨ y).2.const_mul b), integral_const_mul, integral_const_mul]
    rfl

end GlobalTheory.ConeSoB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjIdealIndicatorUnitBlockTranslateReadsWeilOpeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjIdealIndicator_unitBlockTranslate_reads_weilOperator : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
    D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 →
    ∀ (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsStdLat LS → IsStdLat LT → IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    IsSBHalf (cA D e) (latO S T LS LT fun _ => True) (cosetFn (cA D e) (D.host.conj • modul P c) (0 : WO S T)) →
    ∀ (κ : ℂ) (e0 : VC D a d → ℂ) (vac : WO S T → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) →
    Reads ψ θ hS hT ⊤ δ 1 (κ • e0) vac → IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) vac →
    ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm →
    ∀ (G : VC D a d → ℂ) (o : ℕ), Reads ψ θ hS hT ⊤ δ 1 G (Tm (cosetFn (cA D e) (D.host.conj • modul P c) 0)) →
    ∃ ζ : ℂ, IsRootOne ζ ∧ Reads ψ θ hS hT ⊤ δ 1 (ζ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d)) G)
      (Tm (cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o))) := by
  first | exact @GlobalTheory.BotSmallTransl.reads_transl | exact GlobalTheory.BotSmallTransl.reads_transl | (intros; apply GlobalTheory.BotSmallTransl.reads_transl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHeckeCharacterFinitePartStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_heckeCharacterFinitePart : ∀ {D : D7} {N : ℕ} (c : HeckeU D N), Continuous (GlobalTheory.HeckeUChar.finChar c) := by
  first | exact @GlobalTheory.HeckeUChar.continuous_finChar | exact GlobalTheory.HeckeUChar.continuous_finChar | (intros; apply GlobalTheory.HeckeUChar.continuous_finChar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosineCountOfPublishedInputsStatement
section
open GlobalTheory.SumCount GlobalTheory.SumSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosine_count_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.SumCount.CosK := by
  first | exact @GlobalTheory.CosCount.cosK | exact GlobalTheory.CosCount.cosK | (intros; apply GlobalTheory.CosCount.cosK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxPhaseMulBoxEqHeisenbergTranslatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darbouxPhase_mul_box_eq_heisenbergTranslates : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j), Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e → ∀ (ψ : AddChar (AF D.host.F) ℂ) (F₁ : WO (negSp (spW G i j)) (spV G i j) → ℂ) (F₂ : WO (spV₁ G i j) (spW G i j) → ℂ) (v w : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)), ψ (⅟(2 : AF D.host.F) * ((Γ.M.co.e v).1 ⬝ᵥ (Γ.M.co.e w).2 - (Γ.M.co.e w).1 ⬝ᵥ (Γ.M.co.e v).2)) * (F₁ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e (v + w))ᵀ) * F₂ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e (v + w))) = heisO ψ (negSp (spW G i j)) (spV G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e w)ᵀ) F₁ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e v)ᵀ) * heisO ψ (spV₁ G i j) (spW G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e w) F₂ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e v) := by
  first | exact @GlobalTheory.BoxPhase.phase_box_heis | exact GlobalTheory.BoxPhase.phase_box_heis | (intros; apply GlobalTheory.BoxPhase.phase_box_heis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DataBoundOfHalfFlipStatement
section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ArchTens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.data_bound_of_half_flip : GlobalTheory.FunPr.Hypotheses₂ → BigC fun _ ch C _ => FlipAt ch (C / 2) → DatAt ch C := by
  first | exact @GlobalTheory.ArchTens.Unfold.datK | exact GlobalTheory.ArchTens.Unfold.datK | (intros; apply GlobalTheory.ArchTens.Unfold.datK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteVertexClassesCardLePrincipalCongruence
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.FrameTransport

open GlobalTheory.FrameTransport in

theorem exists_surj_cls {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E)
    (hfr : Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1)
    (u : GfC V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hu : ∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ (finG V u).val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hK : congLev D.sp.cm V.gram Λ 𝔪 ≤ K) :
    ∃ f : GlobalTheory.NormSum.Cls D V.rank (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) → FinCl V K, Function.Surjective f := by
  classical
  obtain ⟨uf, huf_def⟩ : ∃ uf, uf = finG V u := ⟨_, rfl⟩
  rw [← huf_def] at hu
  have hufU : uf ∈ UA D.sp.cm V.gram := by rw [huf_def]; exact GlobalTheory.LevSplit.finE_mem_UA V u.1
  have lift : ∀ h : StandardLatticesGL3.GA D V.rank, ∃ g : GfC V, finG V g = frConj fr h.1 * uf⁻¹ := fun h =>
    GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq V _ (mul_mem (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr h) (inv_mem hufU))
  choose φ hφ using lift

  have hC : ∀ c ∈ GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank, uf * frConj fr c.1 * uf⁻¹ ∈ K := by
    let ρ : StandardLatticesGL3.GA D V.rank →* GL (Fin V.rank) (Lev.EAf D) :=
      (MulAut.conj uf).toMonoidHom.comp ((frConj fr).comp (StandardLatticesGL3.GA D V.rank).subtype)
    have hle : GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank ≤ K.comap ρ := by
      refine (Subgroup.closure_le _).2 fun k hk => ?_
      have hU : uf * frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram :=
        mul_mem (mul_mem hufU (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr k)) (inv_mem hufU)
      exact hK (GlobalTheory.T.frameConjugate_principalCongruence_mem_latticeCongruence V fr uf Λ hu 𝔪 k hk.1 hk.2 hU)
    intro c hc
    exact hle hc
  refine ⟨fun q => DoubleCoset.mk (ratFin V) (K.comap (finG V)) (φ (Quotient.out q)), ?_⟩
  intro p
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (ratFin V) (K.comap (finG V)) x = p := ⟨Quotient.out p, DoubleCoset.out_eq' _ _ p⟩
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_standardUnitary_frameConj_eq V fr hfr (finG V x * uf) (mul_mem (GlobalTheory.LevSplit.finE_mem_UA V x.1) hufU)
  refine ⟨DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h, ?_⟩
  show DoubleCoset.mk (ratFin V) (K.comap (finG V)) (φ (Quotient.out (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h))) = _
  obtain ⟨γ, hγ, c, hc, e⟩ := (DoubleCoset.eq _ _ _ _).1
    (DoubleCoset.out_eq' (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank)
      (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h))
  generalize Quotient.out (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h) = h' at e ⊢
  obtain ⟨q, hq, hqe⟩ := GlobalTheory.T.frameConj_standardRational_mem_unitaryRational V fr hfr γ hγ
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq V (uf * frConj fr c.1 * uf⁻¹)
    (mul_mem (mul_mem hufU (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr c)) (inv_mem hufU))
  refine (DoubleCoset.eq _ _ _ _).2 ⟨q, hq, k, ?_, ?_⟩
  · show finG V k ∈ K
    rw [hk]; exact hC c hc
  · apply finG_injective V
    have e1 : finG V x = frConj fr h.1 * uf⁻¹ := by rw [hh]; group
    have e2 : frConj fr h.1 = frConj fr γ.1 * frConj fr h'.1 * frConj fr c.1 := by
      rw [e]; simp only [Subgroup.coe_mul, map_mul]
    have e3 := hφ h'
    simp only [map_mul, hqe, e3, hk, e1, e2]
    group

theorem finCl_card_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U → ∀ X : Node, DefNode D.R.m X → ∀ 𝔪 : Ideal (𝓞 D.host.E), 𝔪 ≠ ⊥ → ∀ K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D)), congLev D.sp.cm (G.V X).gram (G.Λ X) 𝔪 ≤ K → (Nat.card (FinCl (G.V X) K) : ℝ) ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
  intro D T L sc G U hS X hX 𝔪 h𝔪 K hK
  obtain ⟨f, hf⟩ := exists_surj_cls (G.V X) (hS.fr X) (hS.fr_on X hX) (hS.u X) (G.Λ X) (hS.u_lat X hX) 𝔪 K hK
  obtain ⟨-, hI, hJ⟩ := GlobalTheory.NormSum.cls_finite_card_le D (G.V X).rank
  obtain ⟨hne, hle⟩ := GlobalTheory.congLev_relIndex_le D 𝔪 h𝔪 (G.V X).rank
  obtain ⟨hfin, hcard⟩ := hJ _ (GlobalTheory.FunObj.StdDatum.congLev_le 𝔪 _) hne
  have h1 := Nat.card_le_card_of_surjective f hf
  have hI' : (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.NormSum.intG D (G.V X).rank)) : ℝ) ≤ hBd D (G.V X).rank := hI
  calc (Nat.card (FinCl (G.V X) K) : ℝ)
      ≤ (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 (G.V X).rank)) : ℝ) := by
        exact_mod_cast h1
    _ ≤ (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.NormSum.intG D (G.V X).rank)) : ℝ) *
          ((GlobalTheory.FunObj.StdDatum.congLev D 𝔪 (G.V X).rank).relIndex (GlobalTheory.NormSum.intG D (G.V X).rank) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
        apply mul_le_mul hI' (by exact_mod_cast hle) (by positivity)
        exact le_trans (Nat.cast_nonneg _) hI'

end GlobalTheory.FrameTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzTensorNeZeroStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl F), ∀ φ ∈ SB (κ → Fv F v), φ ≠ 0 →
    ∃ r : (κ → AF F) → ℂ, Rest (evFin F v) φ r ∧ tens (evFin F v) φ r ≠ 0 := by
  first | exact @GlobalTheory.InertSph.exists_rest_tens_ne_zero | exact GlobalTheory.InertSph.exists_rest_tens_ne_zero | (intros; apply GlobalTheory.InertSph.exists_rest_tens_ne_zero <;> assumption)
end

