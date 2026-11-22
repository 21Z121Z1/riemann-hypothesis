import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0471
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0425
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumArchimedeanHeisenbergLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0576
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridGivenPathTensorMemSubfield
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

noncomputable section

namespace GlobalTheory.GivenField

open GlobalTheory.StepData

section Local

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (F : Subfield ℂ)

theorem lam_principal_mem {a : Type*} [Fintype a] [DecidableEq a] (g : (TypeDatum.principal k a).J) :
    (((TypeDatum.principal k a).lam g : ℂˣ) : ℂ) ∈ F := by
  change ((1 : ℂˣ) : ℂ) ∈ F
  rw [Units.val_one]
  exact one_mem F

theorem lam_reindex_mem {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (P : TypeDatum k a)
    (e : a ≃ b) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F) (g : (P.reindex e).J) : (((P.reindex e).lam g : ℂˣ) : ℂ) ∈ F :=
  hP _

theorem lam_step_mem {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] (P : TypeDatum k a)
    (μ : kˣ →* ℂˣ) (hμ : IsTame μ) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F) (hμF : ∀ x, ((μ x : ℂˣ) : ℂ) ∈ F)
    (h : (P.step t μ hμ).J) : (((P.step t μ hμ).lam h : ℂˣ) : ℂ) ∈ F := by
  rw [P.step_lam μ hμ h (P.corner h) (P.corner_val h), Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
  exact mul_mem (mul_mem (hP _) (inv_mem (hμF _))) (hμF _)

theorem lam_iter_mem {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F)
    (hμF : ∀ j x, ((μ j x : ℂˣ) : ℂ) ∈ F) (j : ℕ) : ∀ g, (((P.iter t μ hμ j).lam g : ℂˣ) : ℂ) ∈ F := by
  induction j with
  | zero => exact lam_reindex_mem F P _ hP
  | succ j ih => exact lam_reindex_mem F _ _ (lam_step_mem F _ _ _ ih (hμF _))

theorem Phi_mem {a t : Type*} [Fintype a] [DecidableEq a] (P : TypeDatum k a) (μ : kˣ →* ℂˣ)
    (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F) (hμF : ∀ x, ((μ x : ℂˣ) : ℂ) ∈ F) (x : Matrix (a ⊕ t) a k) :
    P.Phi t μ x ∈ F := by
  by_cases h : P.Phi t μ x = 0
  · rw [h]; exact zero_mem F
  · obtain ⟨⟨g, hg, e⟩, h2⟩ := (P.Phi_ne_zero_iff μ).1 h
    rw [P.Phi_of_mem μ ⟨g, hg⟩ e h2, Units.val_inv_eq_inv_val]
    exact mul_mem (hP _) (inv_mem (hμF _))

theorem iterPhi_mem {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F)
    (hμF : ∀ j x, ((μ j x : ℂˣ) : ℂ) ∈ F) (j : ℕ) (x : Matrix (Ix r t (j + 1)) (Ix r t j) k) :
    P.iterPhi t μ hμ j x ∈ F :=
  Phi_mem F _ _ (lam_iter_mem F P μ hμ hP hμF j) (hμF _) _

theorem parPhi_mem {r s s' : Type*} [Fintype r] [DecidableEq r] (δ : kˣ →* ℂˣ) (hδ : ∀ x, ((δ x : ℂˣ) : ℂ) ∈ F)
    (x : Matrix (r ⊕ s) (r ⊕ s') k) : parPhi δ x ∈ F := by
  by_cases h : parPhi δ x = 0
  · rw [h]; exact zero_mem F
  · obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).1 h
    rw [parPhi_of_mem δ hg e h21 h12 h22, Units.val_inv_eq_inv_val]
    exact inv_mem (hδ _)

theorem indicator_one_mem {X : Type*} (S : Set X) (x : X) : S.indicator (1 : X → ℂ) x ∈ F := by
  classical
  rw [Set.indicator_apply]
  split_ifs
  · exact one_mem F
  · exact zero_mem F

end Local

section Global

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Subfield ℂ) (w : Pl D.host.E)

theorem muBase_mem (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) (c : ℕ) (x : (Kw w)ˣ) :
    (((muBase L c).loc w x : ℂˣ) : ℂ) ∈ F := by
  rcases c with _ | c
  · simp [muBase]
  · simp only [muBase]
    split_ifs with h
    · exact hmu _ _
    · simp

variable {t : T} (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) (hxi : ∀ x, ((L.xiH t).loc w x : ℂ) ∈ F)
include hmu hxi

theorem stepFn_mem (j : ℕ) (x) : stepFn L t w j x ∈ F := by
  unfold stepFn
  split_ifs
  · refine iterPhi_mem F _ _ _ (lam_principal_mem F) (fun c y => ?_) _ _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact inv_mem (muBase_mem F w hmu c y)
  · refine parPhi_mem F _ (fun y => ?_) _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact inv_mem (hxi y)
  · exact indicator_one_mem F _ _

theorem givenDatum_mem (B : Frames G) (Φ : G.Datum) (b : Edge) (x) : givenDatum t w B Φ b x ∈ F := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩
  · rcases i with _ | i
    · simp only [givenDatum]
      exact stepFn_mem F w hmu hxi _ _
    · simp only [givenDatum]
      exact zero_mem F
  · rcases j with _ | j
    · simp only [givenDatum]
      split_ifs
      · exact indicator_one_mem F _ _
      · exact zero_mem F
    · simp only [givenDatum]
      exact zero_mem F

end Global

theorem tensor_givenStage_mem : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Subfield ℂ) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E), (∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) → (∀ x, ((L.xiH t).loc w x : ℂ) ∈ F) → ∀ z : (locGrid G t w).Args, (givenStage t w B Φ).tensor z ∈ F := by
  intro D T L sc G F B t Φ w hmu hxi z
  show ((GlobalTheory.SplitFlip.givenPath D.R.m).map fun b => givenDatum t w B Φ b (z b)).prod ∈ F
  refine list_prod_mem fun y hy => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
  exact givenDatum_mem F w hmu hxi B Φ b _

end GlobalTheory.GivenField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfVectorSymplecticOrthogonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.OrthOff

theorem orthOff : All fun {D} _ _ _ {G} _ _ => ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), ∀ u ∈ latO S T LS LT (fun v => v ∉ G.pl.S0), ∀ y : WO S T, IsHalf e y → symplO S T u y = 0 := by
  intro D _ T L μ0 _ sc G W M _ e he S T' LS LT u hu y hy
  classical
  have hx : FinPl.MxAt (fun p => ∃ PP ∈ G.pl.W0, p = HeightOneSpectrum.under (𝓞 D.host.F) PP) (y.map (cA D)) :=
    GlobalTheory.PlaceModelComb.mxAt_of_idemSum he (Or.inr fun i j => by
      rw [Matrix.map_apply, ← map_mul, hy i j])
  have hu' := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have hoff : ∀ i j, u i j ∈ FinPl.idOff D (fun p => ∃ PP ∈ G.pl.W0, p = HeightOneSpectrum.under (𝓞 D.host.F) PP) := by
    intro i j
    rw [FinPl.idOff, Ideal.mem_iInf]
    rintro ⟨w, PP, hPP, rfl⟩
    have hin : HeightOneSpectrum.under (𝓞 D.host.F) PP ∈ G.pl.S0 := by
      unfold Places.W0 at hPP
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPP
      rw [G.pl.under_w hv]
      exact hv
    have h := hu' i j
    rw [FinPl.idAt, Ideal.mem_inf, Ideal.mem_iInf] at h
    exact h.2 ⟨_, fun h' => h' hin⟩
  have hh : hO S T' u y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h0 : cA D (y c b) * u d a = 0 :=
      GlobalTheory.FinPl.FlatUnitPf.idAt_mul_idOff _ _ _ (hx c b) (hoff d a)
    calc incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T'.gram c d) * u d a
        = incA D (S.gram⁻¹ a b) * incA D (T'.gram c d) * (cA D (y c b) * u d a) := by ring
      _ = 0 := by rw [h0, mul_zero]
  unfold symplO
  rw [hh, mul_zero, map_zero]

end GlobalTheory.OrthOff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumArchimedeanHeisenbergLineStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_thetaSum_archimedeanHeisenbergLine : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → ∀ (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
    ∀ (g g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (Fin n × Fin d → v.adicCompletion F) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) g g₁ →
      ∀ u' : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E),
        HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u' (M.heisLine ψ u t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))))
          (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ))) 0 := by
  first | exact @GlobalTheory.ThetaLinePure.hasDerivAt_thetaSum_heisLine | exact GlobalTheory.ThetaLinePure.hasDerivAt_thetaSum_heisLine | (intros; apply GlobalTheory.ThetaLinePure.hasDerivAt_thetaSum_heisLine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharFiniteIdelesIsAlgebraicOfResEtaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_finiteIdeles_isAlgebraic_of_resEta : ∀ {D : D7} {θ : InfFam D} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ}, IsInfFam θ → IsHeckeChar D χ → ResEta D χ n →
    ∀ x : (Formalism.L2.Theta.AE D)ˣ, infPart D (x : Formalism.L2.Theta.AE D) = 1 → IsAlgebraic ℚ ((χ x : Circle) : ℂ) := by
  first | exact @GlobalTheory.FinValAlg.finite_values_isAlgebraic | exact GlobalTheory.FinValAlg.finite_values_isAlgebraic | (intros; apply GlobalTheory.FinValAlg.finite_values_isAlgebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCommutingOperatorIndependentOfArchimedeanFiber
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.FinFibre

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def fin (x : κ → AF F) : κ → Af F := fun i => (x i).2

def mkv (a : κ → Ainf F) (w : κ → Af F) : κ → AF F := fun i => (a i, w i)

def chi (ψ : AddChar (AF F) ℂ) (q : κ → Af F) (w : κ → Af F) : ℂ := GlobalTheory.HeisSchA.finChar ψ (w ⬝ᵥ q)

variable (κ) in

def alg (ψ : AddChar (AF F) ℂ) : Submodule ℂ ((κ → Af F) → ℂ) := Submodule.span ℂ (Set.range (chi (κ := κ) ψ))

theorem chi_zero (ψ : AddChar (AF F) ℂ) : chi (κ := κ) ψ 0 = 1 := by
  funext w; simp [chi]

theorem chi_add (ψ : AddChar (AF F) ℂ) (q q' : κ → Af F) : chi (κ := κ) ψ (q + q') = chi ψ q * chi ψ q' := by
  funext w; simp [chi, dotProduct_add, AddChar.map_add_eq_mul]

theorem one_mem (ψ : AddChar (AF F) ℂ) : (1 : (κ → Af F) → ℂ) ∈ alg κ ψ :=
  chi_zero (κ := κ) ψ ▸ Submodule.subset_span ⟨0, rfl⟩

theorem mul_mem (ψ : AddChar (AF F) ℂ) {C D : (κ → Af F) → ℂ} (hC : C ∈ alg κ ψ) (hD : D ∈ alg κ ψ) :
    C * D ∈ alg κ ψ := by
  have h := Submodule.mul_mem_mul hC hD
  rw [alg, Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨q, rfl⟩, _, ⟨q', rfl⟩, rfl⟩
  exact ⟨q + q', chi_add ψ q q'⟩

end GlobalTheory.FinFibre

namespace GlobalTheory.FinFibre
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_ne_one (ψ : AddChar (AF F) ℂ) (hψ : ∀ w : Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) {a : Af F}
    (ha : a ≠ 0) : ∃ b : Af F, GlobalTheory.HeisSchA.finChar ψ (a * b) ≠ 1 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, evalV F v a ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (af_ext fun u => by rw [h u, map_zero])
  obtain ⟨t, ht⟩ := hψ v
  refine ⟨singleFin v (t / evalV F v a), ?_⟩
  have e : a * singleFin v (t / evalV F v a) = singleFin v t := by
    apply af_ext
    intro u
    rw [map_mul]
    by_cases hu : u = v
    · subst hu
      rw [evalV_singleFin_self, evalV_singleFin_self]
      field_simp
    · rw [evalV_singleFin_ne hu, evalV_singleFin_ne hu, mul_zero]
  rw [e]
  exact ht

theorem exists_chi_ne_one (ψ : AddChar (AF F) ℂ) (hψ : ∀ w : Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) {d : κ → Af F}
    (hd : d ≠ 0) : ∃ q : κ → Af F, chi ψ q d ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hd
  obtain ⟨b, hb⟩ := exists_ne_one ψ hψ hi
  exact ⟨Pi.single i b, by rw [chi, dotProduct_single]; exact hb⟩

theorem chi_mul_eq_schr (ψ : AddChar (AF F) ℂ) (q : κ → Af F) (Φ : (κ → AF F) → ℂ) :
    (fun x => chi ψ q (fin x) * Φ x) =
      schr ψ ((GlobalTheory.HeisSchA.mk 0 1 : AF F) • (0 : κ → AF F),
        (GlobalTheory.HeisSchA.mk 0 1 : AF F) • fun i => GlobalTheory.HeisSchA.mk 0 (q i)) Φ := by
  funext x
  simp only [schr, smul_zero, zero_dotProduct, mul_zero, add_zero]
  congr 1
  rw [chi, GlobalTheory.HeisSchA.finChar_apply]
  congr 1
  symm
  refine Prod.ext ?_ ?_
  · change GlobalTheory.HeisSchA.p1 (x ⬝ᵥ _) = 0
    rw [RingHom.map_dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    change GlobalTheory.HeisSchA.p1 (x i) * (0 * 0) = 0
    simp
  · change GlobalTheory.HeisSchA.p2 (x ⬝ᵥ _) = _
    rw [RingHom.map_dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (x i).2 * (1 * q i) = (x i).2 * q i
    rw [one_mul]

end GlobalTheory.FinFibre

namespace GlobalTheory.FinFibre
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem comm_alg (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hT : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ))
    {C : (κ → Af F) → ℂ} (hC : C ∈ alg κ ψ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    T (fun x => C (fin x) * Φ x) = fun x => C (fin x) * T Φ x := by
  induction hC using Submodule.span_induction with
  | mem C h =>
    obtain ⟨q, rfl⟩ := h
    have h0 : evI F (GlobalTheory.HeisSchA.mk 0 1 : AF F) = 0 := by
      change InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    rw [chi_mul_eq_schr, chi_mul_eq_schr]
    exact hT _ h0 _ _ Φ hΦ
  | zero =>
    have e : (fun x : κ → AF F => (0 : (κ → Af F) → ℂ) (fin x) * T Φ x) = 0 := by funext x; simp
    have e' : (fun x : κ → AF F => (0 : (κ → Af F) → ℂ) (fin x) * Φ x) = 0 := by funext x; simp
    rw [e, e', map_zero]
  | add C D _ _ hC hD =>
    have e : (fun x : κ → AF F => (C + D) (fin x) * Φ x) =
        (fun x => C (fin x) * Φ x) + fun x => D (fin x) * Φ x := by funext x; simp [add_mul]
    rw [e, map_add, hC, hD]
    funext x; simp [add_mul]
  | smul a C _ hC =>
    have e : (fun x : κ → AF F => (a • C) (fin x) * Φ x) = a • fun x => C (fin x) * Φ x := by
      funext x; simp [mul_assoc]
    rw [e, map_smul, hC]
    funext x; simp [mul_assoc]

theorem exists_sep (ψ : AddChar (AF F) ℂ) (hc : Continuous ψ)
    (hψ : ∀ w : Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) (y₀ : κ → Af F) {S : Set (κ → Af F)} (hS : IsCompact S)
    (hy : y₀ ∉ S) : ∃ C ∈ alg κ ψ, C y₀ = 1 ∧ ∀ w ∈ S, C w = 0 := by
  have hlc := GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hc
  refine hS.induction_on (p := fun t => ∃ C ∈ alg κ ψ, C y₀ = 1 ∧ ∀ w ∈ t, C w = 0) ?_ ?_ ?_ ?_
  · exact ⟨1, one_mem ψ, rfl, fun _ h => h.elim⟩
  · rintro s t hst ⟨C, hC, h1, h0⟩
    exact ⟨C, hC, h1, fun w hw => h0 w (hst hw)⟩
  · rintro s t ⟨C, hC, h1, h0⟩ ⟨D, hD, h1', h0'⟩
    refine ⟨C * D, mul_mem ψ hC hD, by simp [h1, h1'], ?_⟩
    rintro w (hw | hw)
    · simp [h0 w hw]
    · simp [h0' w hw]
  · intro w hw
    have hne : w - y₀ ≠ 0 := sub_ne_zero.mpr fun h => hy (h ▸ hw)
    obtain ⟨q, hq⟩ := exists_chi_ne_one ψ hψ hne
    set ζ := chi ψ q (w - y₀)
    have hζ : 1 - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
    let C : (κ → Af F) → ℂ := (1 - ζ)⁻¹ • (GlobalTheory.HeisSchA.finChar ψ (-(y₀ ⬝ᵥ q)) • chi ψ q - ζ • chi ψ 0)
    have hCv : ∀ w', C w' = (1 - ζ)⁻¹ * (chi ψ q (w' - y₀) - ζ) := by
      intro w'
      simp only [C, chi_zero, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
      congr 2
      rw [chi, chi, sub_dotProduct, sub_eq_neg_add, AddChar.map_add_eq_mul]
    have hCm : C ∈ alg κ ψ := Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)))
    have hcont : Continuous fun w' : κ → Af F => (w' - y₀) ⬝ᵥ q :=
      (continuous_id.sub continuous_const).dotProduct continuous_const
    have hev := (IsLocallyConstant.iff_eventually_eq _).mp (hlc.comp_continuous hcont) w
    refine ⟨{w' | chi ψ q (w' - y₀) = ζ}, mem_nhdsWithin_of_mem_nhds hev, C, hCm, ?_, ?_⟩
    · rw [hCv, sub_self]
      have h1 : chi ψ q 0 = 1 := by simp [chi]
      rw [h1]
      exact inv_mul_cancel₀ hζ
    · intro w' hw'
      rw [hCv, show chi ψ q (w' - y₀) = ζ from hw', sub_self, mul_zero]

end GlobalTheory.FinFibre

namespace GlobalTheory.FinFibre
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem schA_struct {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (∃ K : Set (κ → Af F), IsCompact K ∧ ∀ x, fin x ∉ K → Φ x = 0) ∧
      ∀ w₀ : κ → Af F, ∀ᶠ w in nhds w₀, ∀ a : κ → Ainf F, Φ (mkv a w) = Φ (mkv a w₀) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨⟨tsupport g, hg.2, fun x hx => ?_⟩, fun w₀ => ?_⟩
    · change _ * g (fin x) = 0
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    · filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp hg.1 w₀] with w hw a
      change _ * g w = _ * g w₀
      rw [hw]
      rfl
  | zero => exact ⟨⟨∅, isCompact_empty, fun _ _ => rfl⟩, fun _ => Filter.Eventually.of_forall fun _ _ => rfl⟩
  | add Φ Ψ _ _ hΦ hΨ =>
    obtain ⟨⟨K, hK, h0⟩, h1⟩ := hΦ
    obtain ⟨⟨K', hK', h0'⟩, h1'⟩ := hΨ
    refine ⟨⟨K ∪ K', hK.union hK', fun x hx => ?_⟩, fun w₀ => ?_⟩
    · simp only [Set.mem_union, not_or] at hx
      simp [h0 x hx.1, h0' x hx.2]
    · filter_upwards [h1 w₀, h1' w₀] with w hw hw' a
      simp [hw a, hw' a]
  | smul c Φ _ hΦ =>
    obtain ⟨⟨K, hK, h0⟩, h1⟩ := hΦ
    refine ⟨⟨K, hK, fun x hx => by simp [h0 x hx]⟩, fun w₀ => ?_⟩
    filter_upwards [h1 w₀] with w hw a
    simp [hw a]

theorem main (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)) (hψ : IsStd ψ)
    (hnd : ∀ w : Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1)
    (hT : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ))
    (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (y : κ → AF F) (hy : ∀ z, At (evI F) z → Φ (y + z) = 0) :
    T Φ y = 0 := by
  obtain ⟨⟨K, hK, h0⟩, h1⟩ := schA_struct hΦ
  set U := {w : κ → Af F | ∀ a : κ → Ainf F, Φ (mkv a w) = Φ (mkv a (fin y))}
  have hU : U ∈ nhds (fin y) := h1 (fin y)
  obtain ⟨C, hC, hC1, hC0⟩ := exists_sep ψ hψ.1 hnd (fin y) (hK.diff isOpen_interior)
    (fun h => h.2 (mem_interior_iff_mem_nhds.mpr hU))
  have hzero : (fun x => C (fin x) * Φ x) = 0 := by
    funext x
    by_cases hxK : fin x ∈ K
    · by_cases hxU : fin x ∈ interior U
      · have hx := interior_subset hxU (fun i => (x i).1)
        have e1 : mkv (fun i => (x i).1) (fin x) = x := rfl
        rw [e1] at hx
        have e2 : mkv (fun i => (x i).1) (fin y) = y + fun i => GlobalTheory.HeisSchA.mk ((x i).1 - (y i).1) 0 := by
          funext i
          refine Prod.ext ?_ ?_
          · change (x i).1 = (y i).1 + ((x i).1 - (y i).1)
            abel
          · change (y i).2 = (y i).2 + 0
            rw [add_zero]
        rw [hx, e2, hy _ (fun u hu => funext fun i => GlobalTheory.HeisSchA.at_mk _ u hu)]
        simp
      · simp [hC0 _ ⟨hxK, hxU⟩]
    · simp [h0 x hxK]
  have h := congrFun (comm_alg ψ T hT hC hΦ) y
  rw [hzero, map_zero, hC1, one_mul] at h
  exact h.symm

end GlobalTheory.FinFibre

open GlobalTheory.FinFibre in

theorem GlobalTheory.FinFibre.fibre_zero : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) →
    (∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ, T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) → T Φ y = 0 :=
  fun ψ T hψ _ hT Φ hΦ y hy => main ψ T hψ (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hψ) hT Φ hΦ y hy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsCuspidalOfFunctorialityStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifts_cuspidal_of_functoriality : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal := by
  first | exact @GlobalTheory.PairLift.liftsCuspidal_of_classicalTheorems | exact GlobalTheory.PairLift.liftsCuspidal_of_classicalTheorems | (intros; apply GlobalTheory.PairLift.liftsCuspidal_of_classicalTheorems <;> assumption)
end

