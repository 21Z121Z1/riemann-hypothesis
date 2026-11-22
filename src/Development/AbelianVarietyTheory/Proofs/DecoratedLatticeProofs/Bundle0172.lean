import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralRealUnitaryHaarEqProdUpqHaar
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HaarReal
open Formalism.IndefR.Eqv

theorem continuous_psiT (D : D7) (τ : D.what₂.Tau) : Continuous (psiT D τ) := by
  have hsum : ∀ x : AE D, psiT D τ x = ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D) ((basAF D).repr x c)) *
      psiT D τ (basAF D c) := by
    intro x
    conv_lhs => rw [← (basAF D).sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Algebra.smul_def, map_mul]
  have hc : ∀ c, Continuous fun x : AE D => (basAF D).repr x c := fun c =>
    (continuous_apply c).comp (G5.tensCoordH (basE D) (AF D.host.F)).continuous
  have halg : Continuous fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a) := by
    have e : (fun a : AF D.host.F => psiT D τ (algebraMap (AF D.host.F) (AE D) a)) =
        fun a => thetaC D τ ((fstA D.host.F a) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      funext a
      simp only [psiT, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, infPart,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one]
      rfl
    rw [e]
    exact ((isInfFam_thetaC D) τ).2.comp continuous_fst
  have hfun : (⇑(psiT D τ) : AE D → ℂ) = fun x => ∑ c, psiT D τ (algebraMap (AF D.host.F) (AE D)
      ((basAF D).repr x c)) * psiT D τ (basAF D c) := funext hsum
  rw [hfun]
  exact continuous_finset_sum _ fun c _ => (halg.comp (hc c)).mul continuous_const

end GlobalTheory.HaarReal

namespace GlobalTheory.HaarReal

open Formalism.IndefR.Eqv Formalism.MainNotions.StandardLattice

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem fr_mul_inv (τ : D.what₂.Tau) : M.fr τ * (M.fr τ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

theorem inv_mul_fr (τ : D.what₂.Tau) : (M.fr τ)⁻¹ * M.fr τ = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

def toJ (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  M.fr τ * g * (M.fr τ)⁻¹

theorem ofFr_toJ (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (toJ M τ g) = g := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr toJ
  calc (M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ
      = ((M.fr τ)⁻¹ * M.fr τ) * g * ((M.fr τ)⁻¹ * M.fr τ) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [inv_mul_fr, Matrix.one_mul, Matrix.mul_one]

theorem toJ_ofFr (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    toJ M τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ u) = u := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr toJ
  calc M.fr τ * ((M.fr τ)⁻¹ * u * M.fr τ) * (M.fr τ)⁻¹
      = (M.fr τ * (M.fr τ)⁻¹) * u * (M.fr τ * (M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = u := by rw [fr_mul_inv, Matrix.one_mul, Matrix.mul_one]

theorem toJ_mul (τ : D.what₂.Tau) (g h : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    toJ M τ (g * h) = toJ M τ g * toJ M τ h := by
  unfold toJ
  calc M.fr τ * (g * h) * (M.fr τ)⁻¹ = M.fr τ * g * ((M.fr τ)⁻¹ * M.fr τ) * h * (M.fr τ)⁻¹ := by
        rw [inv_mul_fr, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = M.fr τ * g * (M.fr τ)⁻¹ * (M.fr τ * h * (M.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]

theorem toJ_one (τ : D.what₂.Tau) : toJ M τ 1 = 1 := by
  unfold toJ; rw [Matrix.mul_one, fr_mul_inv]

theorem inUJ_toJ (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) : Formalism.REAL.inUJ (M.ε τ) (toJ M τ g) := by
  have hG := M.fr_gram τ
  have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, fr_mul_inv, Matrix.conjTranspose_one]
  unfold Formalism.REAL.inUJ toJ
  calc (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹)
      = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        rw [hG, hg, ← hG]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (M.ε τ) := by rw [h1, fr_mul_inv, Matrix.one_mul, Matrix.mul_one]

theorem unit_ofFr (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hu : Formalism.REAL.inUJ (M.ε τ) u) :
    (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ u)ᴴ * gramAt D V τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ u = gramAt D V τ := by
  have hG := M.fr_gram τ
  have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, fr_mul_inv, Matrix.conjTranspose_one]
  unfold Formalism.REAL.inUJ at hu
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr
  rw [← hG]
  calc ((M.fr τ)⁻¹ * u * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * ((M.fr τ)⁻¹ * u * M.fr τ)
      = (M.fr τ)ᴴ * uᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * u * M.fr τ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * (uᴴ * Formalism.REAL.Jm (M.ε τ) * u) * M.fr τ := by
        rw [h1, fr_mul_inv, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := by rw [hu]

theorem inUJ_umat {n : ℕ} {ε : Fin n → Bool} (u : Formalism.REAL.UJ ε) : Formalism.REAL.inUJ ε (umat u) := u.2

def uJ (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    Formalism.REAL.UJ (M.ε τ) :=
  ⟨⟨toJ M τ g, toJ M τ (ginv D V τ g), by rw [← toJ_mul, mul_ginv D V τ g hg, toJ_one],
    by rw [← toJ_mul, ginv_mul D V τ g hg, toJ_one]⟩, inUJ_toJ M τ g hg⟩

theorem infMat_mul (τ : D.what₂.Tau) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram (thetaC D τ) (g * h) =
      infMat D.sp.cm.sig V.gram (thetaC D τ) g * infMat D.sp.cm.sig V.gram (thetaC D τ) h := by
  rw [infMat_thetaC, infMat_thetaC, infMat_thetaC, matA_mul, Matrix.map_mul]

def fwd (g : GinfC V) : ∀ τ, Formalism.REAL.UJ (M.ε τ) := fun τ =>
  uJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) (g : GA D V)) (infMat_unitary' D V _ τ)

theorem unitFam_ofFr (us : ∀ τ, Formalism.REAL.UJ (M.ε τ)) :
    IsUnitFam D V fun τ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (us τ)) :=
  fun τ => unit_ofFr M τ _ (inUJ_umat (us τ))

def bwd (us : ∀ τ, Formalism.REAL.UJ (M.ε τ)) : GinfC V :=
  ⟨famH D V (fun τ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (us τ))) (unitFam_ofFr M us),
    famH_mem_GinfC D V _ _⟩

theorem continuous_matA : Continuous (matA D V) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_famM : Continuous (famM D V) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_glueA D _).comp ((continuous_splitInv D).comp (continuous_pi fun τ =>
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))))

theorem continuous_fwd : Continuous (fwd M) := by
  refine continuous_pi fun τ => Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · refine (((continuous_const (y := M.fr τ)).matrix_mul (((continuous_matA).comp continuous_subtype_val).matrix_map
      (continuous_psiT D τ))).matrix_mul (continuous_const (y := (M.fr τ)⁻¹))).congr fun g => ?_
    show M.fr τ * _ * _ = toJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) (g : GA D V))
    rw [toJ, infMat_thetaC]; rfl
  · have c0 : Continuous fun g : GinfC V => (matA D V (g : GA D V)).map (psiT D τ) :=
      ((continuous_matA).comp continuous_subtype_val).matrix_map (continuous_psiT D τ)
    refine (((continuous_const (y := M.fr τ)).matrix_mul (((continuous_const (y := (gramAt D V τ)⁻¹)).matrix_mul
      c0.matrix_conjTranspose).matrix_mul (continuous_const (y := gramAt D V τ)))).matrix_mul
      (continuous_const (y := (M.fr τ)⁻¹))).congr fun g => ?_
    show M.fr τ * _ * _ = toJ M τ (ginv D V τ (infMat D.sp.cm.sig V.gram (thetaC D τ) (g : GA D V)))
    rw [toJ, ginv, infMat_thetaC]

theorem continuous_bwd : Continuous (bwd M) := by
  have hu : ∀ τ, Continuous fun us : (∀ τ, Formalism.REAL.UJ (M.ε τ)) => umat (us τ) := fun τ =>
    (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply τ)
  have hg : Continuous fun us : (∀ τ, Formalism.REAL.UJ (M.ε τ)) => fun τ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (us τ)) :=
    continuous_pi fun τ => (continuous_const.matrix_mul (hu τ)).matrix_mul continuous_const
  refine Continuous.subtype_mk (continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)) _
  · exact continuous_famM.comp hg
  · have hi : Continuous fun us : (∀ τ, Formalism.REAL.UJ (M.ε τ)) =>
        fun τ => ginv D V τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (us τ))) :=
      continuous_pi fun τ => (continuous_const.matrix_mul ((continuous_apply τ).comp hg).matrix_conjTranspose).matrix_mul
        continuous_const
    exact continuous_famM.comp hi

def eqv : GinfC V ≃ₜ* (∀ τ, Formalism.REAL.UJ (M.ε τ)) where
  toFun := fwd M
  invFun := bwd M
  left_inv g := by
    apply Subtype.ext
    refine (famH_unique D V _ (unitFam_ofFr M (fwd M g)) (g : GA D V) g.2 fun τ => ?_).symm
    show _ = GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (toJ M τ _)
    rw [ofFr_toJ]
  right_inv us := by
    funext τ
    refine Subtype.ext (Units.ext ?_)
    show toJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) (famH D V _ (unitFam_ofFr M us))) = umat (us τ)
    rw [infMat_famH, toJ_ofFr]
  map_mul' g h := by
    funext τ
    apply Subtype.ext
    apply Units.ext
    show toJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) ((g : GA D V) * h)) =
      toJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) g) * toJ M τ (infMat D.sp.cm.sig V.gram (thetaC D τ) h)
    rw [infMat_mul, toJ_mul]
  continuous_toFun := continuous_fwd M
  continuous_invFun := continuous_bwd M

theorem ofFr_eqv (g : GinfC V) (τ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (eqv M g τ)) = infMat D.sp.cm.sig V.gram (thetaC D τ) (g : GA D V) :=
  ofFr_toJ M τ _

end GlobalTheory.HaarReal

namespace GlobalTheory.HaarReal

open Formalism.IndefR.Eqv Formalism.MainNotions.StandardLattice

theorem integral_prod_eq : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (mR : Measure (GinfC V)) (μ : ∀ τ, Measure (Formalism.REAL.UJ (M.ε τ))), mR.IsHaarMeasure → (∀ τ, (μ τ).IsHaarMeasure) → ∃ c : ℝ, 0 < c ∧ ∀ F : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ, (∀ τ, Integrable (fun u : Formalism.REAL.UJ (M.ε τ) => F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat u))) (μ τ)) → Integrable (fun g : GinfC V => ∏ τ, F τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) (g : GA D V))) mR ∧ ∫ g : GinfC V, ∏ τ, F τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) (g : GA D V)) ∂mR = (c : ℂ) * ∏ τ, ∫ u : Formalism.REAL.UJ (M.ε τ), F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat u)) ∂μ τ := by
  intro D V S M θ hθ mR μ hmR hμ
  obtain rfl : θ = thetaC D := eq_thetaC D hθ
  set e := eqv M
  haveI : (mR.map e).IsHaarMeasure := e.isHaarMeasure_map mR
  set c := (mR.map e).haarScalarFactor (Measure.pi μ)
  have hc : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have key : mR.map e = c • Measure.pi μ := Measure.isMulLeftInvariant_eq_smul _ _
  set E : GinfC V ≃ᵐ (∀ τ, Formalism.REAL.UJ (M.ε τ)) := e.toHomeomorph.toMeasurableEquiv
  have hmap : mR.map E = c • Measure.pi μ := key
  refine ⟨c, hc, fun F hF => ?_⟩
  set f' : (∀ τ, Formalism.REAL.UJ (M.ε τ)) → ℂ := fun us => ∏ τ, F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat (us τ)))
  have hf : (fun g : GinfC V => ∏ τ, F τ (infMat D.sp.cm.sig V.gram (thetaC D τ) (g : GA D V))) = f' ∘ E := by
    funext g
    simp only [f', Function.comp_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← ofFr_eqv M g τ]
    rfl
  have hpi : Integrable f' (Measure.pi μ) :=
    Integrable.fintype_prod_dep (f := fun τ (u : Formalism.REAL.UJ (M.ε τ)) => F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat u))) hF
  rw [hf]
  refine ⟨(integrable_map_equiv E f').mp (by rw [hmap]; exact hpi.smul_measure_nnreal), ?_⟩
  show ∫ x, f' (E x) ∂mR = _
  rw [← integral_map_equiv E f', hmap, integral_smul_nnreal_measure,
    integral_fintype_prod_eq_prod (f := fun τ (u : Formalism.REAL.UJ (M.ε τ)) => F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat u)))]
  rw [NNReal.smul_def, Complex.real_smul]

end GlobalTheory.HaarReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralUnramifiedOutsideOpenSubsetInsertPlace
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.HaarStep

set_option maxHeartbeats 1000000 in

theorem integral_openOff_insert : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (Sf : Finset (FinPl D)) (v : FinPl D), v ∉ Sf → ∀ μ : Measure (Gv A v), μ.IsHaarMeasure → μ (stabLoc D.sp.cm.sig A.gram L v) = 1 → ∀ (S' : Finset (FinPl D)), (∀ u, u ∈ S' ↔ u = v ∨ u ∈ Sf) → ∀ F : GA D A → ℂ, IntegrableOn F (openOff A L S') m → ∫ g in openOff A L S', F g ∂m = ∫ x in openOff A L Sf, (∫ y, F (x * (emb D.sp.cm.sig A.gram v (proj D.sp.cm.sig A.gram v x))⁻¹ * emb D.sp.cm.sig A.gram v y) ∂μ) ∂m := by
  intro D A L hL m hm Sf v hv μ hμ hK S' hS' F hF
  haveI : Submodule.IsLattice D.host.E L := hL.1
  have hne : ∀ u, u ∉ S' → u ≠ v := fun u hu h => hu ((hS' u).2 (Or.inl h))
  have memU : ∀ x, x ∈ openOff A L Sf ↔ x ∈ openOff A L S' ∧
      proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v := by
    intro x
    constructor
    · intro h
      exact ⟨fun u hu => h u (fun hu' => hu ((hS' u).2 (Or.inr hu'))), h v hv⟩
    · rintro ⟨h1, h2⟩ u hu
      by_cases e : u = v
      · subst e; exact h2
      · exact h1 u (fun h => by rcases (hS' u).1 h with h | h; exact e h; exact hu h)
  have memV : ∀ (y : Gv A v) (x : GA D A), emb D.sp.cm.sig A.gram v y * x ∈ openOff A L S' ↔ x ∈ openOff A L S' := by
    intro y x
    refine forall_congr' fun u => imp_congr_right fun hu => ?_
    rw [map_mul, proj_emb_ne _ _ (hne u hu), one_mul]
  have isOpen_off : ∀ S : Finset (FinPl D), IsOpen (openOff A L S) := by
    intro S
    let H : Subgroup (GA D A) :=
      ⨅ u, ⨅ (_ : u ∉ S), (stabLoc D.sp.cm.sig A.gram L u).comap (proj D.sp.cm.sig A.gram u)
    have eH : (H : Set (GA D A)) = openOff A L S := by
      ext g; simp [H, openOff, Subgroup.mem_iInf]
    rw [← eH]
    refine Subgroup.isOpen_mono (H₁ := levelOpen D.sp.cm.sig A.gram L) ?_ (isOpen_levelOpen _ _ L)
    intro g hg
    simp only [H, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro u _
    exact (mem_levelOpen.1 hg) u
  have hUm : MeasurableSet (openOff A L Sf) := (isOpen_off Sf).measurableSet
  have hVm : MeasurableSet (openOff A L S') := (isOpen_off S').measurableSet
  have hKo : IsOpen (stabLoc D.sp.cm.sig A.gram L v : Set (Gv A v)) := isOpen_stabLoc _ _ L v
  have hright : ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v, μ.map (fun y => y * k) = μ := by
    intro k hk
    rw [GlobalTheory.AdelicUnimod.map_mul_right_eq,
      GlobalTheory.AdelicUnimod.modular_compact _ hKo (isCompact_stabLoc _ _ L v) hk, one_smul]
  have step1 : ∀ x ∈ openOff A L Sf,
      ∫ y, F (x * (emb D.sp.cm.sig A.gram v (proj D.sp.cm.sig A.gram v x))⁻¹ * emb D.sp.cm.sig A.gram v y) ∂μ =
        ∫ y, F (emb D.sp.cm.sig A.gram v y * x) ∂μ := by
    intro x hx
    have hkK : proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v := hx v hv
    set k := proj D.sp.cm.sig A.gram v x with hk
    set x' := x * (emb D.sp.cm.sig A.gram v k)⁻¹ with hx'
    have hx'1 : proj D.sp.cm.sig A.gram v x' = 1 := by
      rw [hx', map_mul, map_inv, proj_emb_self, mul_inv_cancel]
    have hxx : x = x' * emb D.sp.cm.sig A.gram v k := by rw [hx', inv_mul_cancel_right]
    have e : ∀ y, emb D.sp.cm.sig A.gram v y * x = x' * emb D.sp.cm.sig A.gram v (y * k) := by
      intro y
      have hc := (commute_emb D.sp.cm.sig A.gram y hx'1).eq
      calc emb D.sp.cm.sig A.gram v y * x = emb D.sp.cm.sig A.gram v y * x' * emb D.sp.cm.sig A.gram v k := by
            rw [mul_assoc, ← hxx]
        _ = x' * emb D.sp.cm.sig A.gram v y * emb D.sp.cm.sig A.gram v k := by rw [hc]
        _ = x' * emb D.sp.cm.sig A.gram v (y * k) := by rw [map_mul, mul_assoc]
    simp_rw [e]
    have h := integral_map_equiv (μ := μ) (MeasurableEquiv.mulRight k)
      (fun y => F (x' * emb D.sp.cm.sig A.gram v y))
    have hm' : Measure.map (MeasurableEquiv.mulRight k) μ = μ := hright k hkK
    rw [hm'] at h
    exact h
  rw [setIntegral_congr_fun hUm step1]

  have hec : Continuous (emb D.sp.cm.sig A.gram v) := continuous_emb _ _ v
  have hpc : Continuous (proj D.sp.cm.sig A.gram v) := continuous_proj _ _ v
  let Q : Set (GA D A × Gv A v) :=
    {q | (proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ stabLoc D.sp.cm.sig A.gram L v}
  have hQo : IsOpen Q := hKo.preimage (((hpc.comp continuous_fst).inv).mul continuous_snd)
  let f₂ : GA D A × Gv A v → ℂ := Q.indicator (fun q => (openOff A L S').indicator F q.1)
  let T : GA D A × Gv A v → GA D A × Gv A v := fun p => (emb D.sp.cm.sig A.gram v p.2 * p.1, p.2)
  have hT : MeasurePreserving T (m.prod μ) (m.prod μ) := by
    have h1 : MeasurePreserving (fun p : Gv A v × GA D A => (p.1, emb D.sp.cm.sig A.gram v p.1 * p.2))
        (μ.prod m) (μ.prod m) :=
      MeasurePreserving.skew_product (MeasurePreserving.id μ)
        ((hec.comp continuous_fst).mul continuous_snd).measurable
        (Filter.Eventually.of_forall fun y => map_mul_left_eq_self m (emb D.sp.cm.sig A.gram v y))
    have h2 : MeasurePreserving (Prod.swap : GA D A × Gv A v → Gv A v × GA D A) (m.prod μ) (μ.prod m) :=
      Measure.measurePreserving_swap
    have h3 : MeasurePreserving (Prod.swap : Gv A v × GA D A → GA D A × Gv A v) (μ.prod m) (m.prod μ) :=
      Measure.measurePreserving_swap
    have h4 := (h3.comp h1).comp h2
    have e : T = (Prod.swap ∘ (fun p : Gv A v × GA D A => (p.1, emb D.sp.cm.sig A.gram v p.1 * p.2))) ∘ Prod.swap := by
      funext p; rfl
    rw [e]; exact h4
  have hCm : ∀ a : Gv A v, MeasurableSet {y : Gv A v | a⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v} :=
    fun a => (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμC : ∀ a : Gv A v, μ {y : Gv A v | a⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v} = 1 := by
    intro a
    rw [← hK]
    exact measure_preimage_mul μ a⁻¹ _
  have slice : ∀ w, (fun y => f₂ (w, y)) =
      {y : Gv A v | (proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v}.indicator
        (fun _ => (openOff A L S').indicator F w) := by
    intro w; funext y
    rfl
  have hFV : Integrable ((openOff A L S').indicator F) m := (integrable_indicator_iff hVm).2 hF
  have hf₂m : AEStronglyMeasurable f₂ (m.prod μ) :=
    (hFV.aestronglyMeasurable.comp_fst).indicator hQo.measurableSet
  have inner : ∀ w, ∫ y, f₂ (w, y) ∂μ = (openOff A L S').indicator F w := by
    intro w
    rw [slice w, integral_indicator_const _ (hCm _), Measure.real, hμC, ENNReal.toReal_one, one_smul]
  have innerN : ∀ w, ∫ y, ‖f₂ (w, y)‖ ∂μ = ‖(openOff A L S').indicator F w‖ := by
    intro w
    have : (fun y => ‖f₂ (w, y)‖) =
        {y : Gv A v | (proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v}.indicator
          (fun _ => ‖(openOff A L S').indicator F w‖) := by
      rw [show (fun y => ‖f₂ (w, y)‖) = fun y => ‖(fun y => f₂ (w, y)) y‖ from rfl, slice w]
      funext y
      exact norm_indicator_eq_indicator_norm _ y
    rw [this, integral_indicator_const _ (hCm _), Measure.real, hμC, ENNReal.toReal_one, one_smul]
  have hf₂ : Integrable f₂ (m.prod μ) := by
    refine (integrable_prod_iff hf₂m).2 ⟨Filter.Eventually.of_forall fun w => ?_, ?_⟩
    · rw [slice w]
      refine (integrable_indicator_iff (hCm _)).2 ?_
      haveI : IsFiniteMeasure (μ.restrict
          {y : Gv A v | (proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v}) :=
        isFiniteMeasure_restrict.2 (by rw [hμC]; exact ENNReal.one_ne_top)
      exact integrable_const _
    · simp_rw [innerN]
      exact hFV.norm
  have hf₁ : Integrable (f₂ ∘ T) (m.prod μ) := (hT.integrable_comp hf₂m).2 hf₂
  have hI : ∫ p, f₂ (T p) ∂(m.prod μ) = ∫ p, f₂ p ∂(m.prod μ) := by
    rw [← integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hf₂m), hT.map_eq]
  have hT1 : ∀ x y, f₂ (T (x, y)) = (openOff A L Sf).indicator (fun x => F (emb D.sp.cm.sig A.gram v y * x)) x := by
    intro x y
    have hp : (proj D.sp.cm.sig A.gram v (emb D.sp.cm.sig A.gram v y * x))⁻¹ * y =
        (proj D.sp.cm.sig A.gram v x)⁻¹ := by
      rw [map_mul, proj_emb_self, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    have hmem : T (x, y) ∈ Q ↔ proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v := by
      show (proj D.sp.cm.sig A.gram v (emb D.sp.cm.sig A.gram v y * x))⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v ↔ _
      rw [hp, inv_mem_iff]
    by_cases h2 : proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v
    · rw [show f₂ (T (x, y)) = (openOff A L S').indicator F (emb D.sp.cm.sig A.gram v y * x) from
        Set.indicator_of_mem (hmem.2 h2) _]
      by_cases h1 : x ∈ openOff A L S'
      · rw [Set.indicator_of_mem ((memV y x).2 h1), Set.indicator_of_mem ((memU x).2 ⟨h1, h2⟩)]
      · rw [Set.indicator_of_notMem (mt (memV y x).1 h1), Set.indicator_of_notMem (fun h => h1 ((memU x).1 h).1)]
    · rw [show f₂ (T (x, y)) = 0 from Set.indicator_of_notMem (mt hmem.1 h2) _,
        Set.indicator_of_notMem (fun h => h2 ((memU x).1 h).2)]
  calc ∫ g in openOff A L S', F g ∂m = ∫ w, (openOff A L S').indicator F w ∂m := (integral_indicator hVm).symm
    _ = ∫ p, f₂ p ∂(m.prod μ) := by rw [integral_prod f₂ hf₂]; simp_rw [inner]
    _ = ∫ p, f₂ (T p) ∂(m.prod μ) := hI.symm
    _ = ∫ x, ∫ y, f₂ (T (x, y)) ∂μ ∂m := integral_prod (f₂ ∘ T) hf₁
    _ = ∫ x, (openOff A L Sf).indicator (fun x => ∫ y, F (emb D.sp.cm.sig A.gram v y * x) ∂μ) x ∂m := by
      congr 1; funext x
      simp_rw [hT1]
      by_cases h : x ∈ openOff A L Sf <;> simp [h]
    _ = ∫ x in openOff A L Sf, ∫ y, F (emb D.sp.cm.sig A.gram v y * x) ∂μ ∂m := integral_indicator hUm

end GlobalTheory.Core.Rk.HaarStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.RedOne

theorem redFn_eq_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) (PP : Pl D.host.E), Lev.finE V g ∈ Formalism.L2.DIV.St β → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (PP.under (𝓞 D.host.F)) g = 1 → Formalism.L2.DIV.redFn β PP (Lev.finE V g) = 1 := by
  intro D V β g PP hS h1
  classical
  exact GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {PP.under (𝓞 D.host.F)} hS
    (fun v hv => by rw [Finset.mem_singleton] at hv; subst hv; exact h1) (Finset.mem_singleton_self _)

end GlobalTheory.ChainOnto.RedOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowestKTypeMemDiscreteSeriesKFiniteVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowKFin

theorem lowT_mem_kfin (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (v : lowT M τ) : ((v : M.sm τ) : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ := by
  have hv : ((v : M.sm τ) : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := v.2
  refine (sSup_le ?_ : lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) hv
  rintro T hT x hx
  exact Submodule.subset_span ⟨T, hT.1, hx, hT.2.1⟩

example : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (v : lowT M τ), ((v : M.sm τ) : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ := lowT_mem_kfin

end GlobalTheory.LowKFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMultiplicitySpaceLevelOfKFiniteTensors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KFiniteLevel

theorem mem_multT_of_kfin : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), (∀ κ ∈ J, κ ∈ GfC V) → ∀ F ∈ MultT θ M ∅ 1, (∀ w ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}), ∀ κ ∈ J, ∀ g, F w (g * κ) = χ κ * F w g) → F ∈ MultT θ M J χ := by
  intro D V S M θ hθ J χ hJ F hF hk
  rw [mem_multT, GlobalTheory.MultMem.mem_mult_iff] at hF ⊢
  set T : MMap M := PiTensorProduct.lift.symm F with hTdef
  have hT : ∀ v : M.Vec, T v = F (PiTensorProduct.tprod ℂ v) := fun v => by
    rw [hTdef, PiTensorProduct.lift_symm]; rfl
  refine ⟨hF.aut, hF.cusp, fun v κ hκ g => ?_, hF.equiv, hF.cont⟩
  set U : MMap M := heckeOn M {κ} T - χ κ • T with hUdef
  have hU : U ∈ Mult θ M ∅ 1 :=
    sub_mem ((GlobalTheory.MultMem.mem_mult_iff ..).2 (GlobalTheory.SphericalOps.isMultMap_single hF (hJ κ hκ)))
      (Submodule.smul_mem _ _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hF))
  have hUv : ∀ (u : M.Vec) (x : GA D V), U u x = T u (x * κ) - χ κ * T u x := fun u x => by
    simp [hUdef, heckeOn, postOn_apply, heckeLin_apply]
  have h0 : U = 0 := GlobalTheory.KFiniteDetermined.restrInj D θ hθ V S M ∅ 1 U hU fun u hu => by
    funext x
    rw [hUv, hT, Pi.zero_apply, sub_eq_zero]
    exact hk _ (Submodule.subset_span ⟨u, fun τ => Submodule.subset_span (hu τ), rfl⟩) κ hκ x
  have := hUv v g
  rw [h0] at this
  exact (sub_eq_zero.1 this.symm)

end GlobalTheory.KFiniteLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorIntegralCommOfBoundedFiniteMeasureStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_integral_comm_of_bounded_finiteMeasure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (Ω : Type) [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω] (m : Measure Ω) [IsFiniteMeasure m] (F : Ω → WO S T → ℂ) (p : GA D S × GA D T), (∀ a, IsThetaFunO ψ S T (F a)) → (Continuous fun q : Ω × WO S T => F q.1 q.2) → (∃ C : ℝ, ∀ a x, ‖F a x‖ ≤ C) → (Continuous fun q : Ω × WO S T => om p (F q.1) q.2) → (∃ C : ℝ, ∀ a x, ‖om p (F a) x‖ ≤ C) → IsThetaFunO ψ S T (fun x => ∫ a, F a x ∂m) → ∀ x, om p (fun y => ∫ a, F a y ∂m) x = ∫ a, om p (F a) x ∂m := by
  first | exact @GlobalTheory.CommIntBdd.om_integral_comm_bdd | exact GlobalTheory.CommIntBdd.om_integral_comm_bdd | (intros; apply GlobalTheory.CommIntBdd.om_integral_comm_bdd <;> assumption)
end

