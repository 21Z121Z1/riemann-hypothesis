import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0060
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0928
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0123
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0117
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0120
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0121
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0125
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0930
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecEqZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0567
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0931
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2031
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlOrbitalIntegralUnitLiftLastBasisReduce
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.GLift

theorem act_mul' {k : Type} [CommRing k] {n : ℕ} (g h : GL (Fin n) k) (Y : Gl n k) :
    act (g * h) Y = act g (act h Y) := by
  simp only [act, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul]

theorem omega_lift {F : Type} [NontriviallyNormedField F] (r : ℕ) (Z : Gl r F) (μ l : F) :
    omega (GlobalTheory.JR.Step.lift Z μ l) = omega Z := by
  have h := (GlobalTheory.JR.transfer_factor_lemma F (r + 1)).1 (GlobalTheory.JR.Step.lift Z μ l)
  have hc : (Cm (GlobalTheory.JR.Step.lift Z μ l)).det = lastDet Z := rfl
  unfold omega eta
  rw [h, hc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

theorem orbG_lift : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 →
    Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 →
    orbG M (unitG (r + 1) F) (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbG M' (unitG r F) Z := by
  intro F E _ _ _ _ hU r M M' Z μ l hμ hΔ
  haveI := hU.ultraF
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨lc1, sc1⟩ := gl_lc_sc F (r + 1)
  letI := M.mG
  haveI := M.bG
  letI := M'.mG
  haveI := M'.bG
  haveI := M.haarG
  haveI := M'.haarG
  haveI := gl_unimodular F E (r + 1) M
  haveI := gl_unimodular F E r M'
  obtain ⟨hO, hC⟩ := GlobalTheory.T.integralGLSet_isOpen_and_isCompact F (r + 1)
  have hemb := GlobalTheory.T.isClosedEmbedding_diagOneGeneralLinearEmbedding F r
  have key := GlobalTheory.CosetIntegral.integral_eq_of_coset_support (GL (Fin (r + 1)) F) (GL (Fin r) F)
    (GlobalTheory.JR.Step.emb r F) hemb M.μG M'.μG (glOSub (r + 1) F) hO hC M.volG
    (by rw [coe_glOSub, GlobalTheory.T.preimage_diagOneGeneralLinearEmbedding_integralGLSet F r]; exact M'.volG)
    (fun g => unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) * omega (act g (GlobalTheory.JR.Step.lift Z μ l)))
    (fun k hk g => by
      simp only [act_mul', GlobalTheory.T.unitIndicatorGLBlock_glBorderedConjugationAction_integral F (r + 1) k hk, GlobalTheory.T.jacquetRallisTransferFactor_glBorderedConjugationAction_integral F (r + 1) k hk])
    (fun g hg => GlobalTheory.T.exists_integralGL_mul_diagOne_of_unitIndicator_lift_ne_zero F E r Z μ l hμ g (left_ne_zero_of_mul hg))
    ((GlobalTheory.T.hasCompactSupport_jacquetRallisOrbitalIntegrand F (r + 1) _ hΔ).comp_isClosedEmbedding hemb)
  unfold orbG
  rw [key]
  simp only [GlobalTheory.T.borderedConjugation_diagOne_liftBlockMatrix, GlobalTheory.T.unitIndicatorGLBlock_liftBlockMatrixWithLastBasis F r _ μ l hμ.le, omega_lift, mul_assoc]
  exact integral_const_mul _ _

end GlobalTheory.JR.GLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsResOfChrEq
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistResidue

open Formalism.IndefR.Datum

variable {D : D7}

set_option maxHeartbeats 800000 in

theorem isRes_of_chrEq : ∀ (D : D7) (δ : GlobalTheory.ExportSeries.Twist D Circle), δ.Good → ∀ (χ : Formalism.L2.Host.HChar D.host.E),
    ChrEq δ.chi χ → ∀ P ∈ δ.Q, IsRes χ P (δ.resC P) := by
  intro D δ hδ χ hχ P hP a k u hka hu
  have h := hδ.split.isIdemAt hP
  have he : GlobalTheory.ExportSeries.idemAt P * GlobalTheory.ExportSeries.idemAt P = GlobalTheory.ExportSeries.idemAt P := h.1.1
  have e1 := hχ.2 P _ (by obtain ⟨⟨g1, g2, v, ε, hv, hs⟩, g3⟩ := h; exact ⟨g1, ⟨v, ε, hv, Or.inl ⟨g2, hs⟩⟩, g3⟩) k (locU he k) (locU_val he k)
  obtain ⟨hi, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ P h
  have hb : toEAf D (incA D (k : D.host.E)) = ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    rw [hka]; rfl
  have hx0 : ((locU he k : (AE D)ˣ) : AE D) = 1 + GlobalTheory.ExportSeries.idemAt P * (incA D (k : D.host.E) - 1) := rfl
  have hv : toEAf D ((locU he k : (AE D)ˣ) : AE D) =
      ((1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    rw [hx0, GlobalTheory.ConjTwist.map_loc, hb]
    rfl
  have hx : toEAf D ((locU he k : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hv]
    exact Subtype.property _
  have hoff : (1 - GlobalTheory.ExportSeries.idemAt P) * ((locU he k : (AE D)ˣ) : AE D) = 1 - GlobalTheory.ExportSeries.idemAt P := by
    rw [hx0]
    linear_combination (1 - incA D (k : D.host.E)) * he
  have hres : resS D.host.F P ⟨_, hx⟩ = u := by
    have e2 : (⟨_, hx⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) :=
      Subtype.ext hv
    refine (congrArg (resS D.host.F P) e2).trans ?_
    rw [GlobalTheory.ConjTwist.map_loc, h1, resS_oToS, hu]
    ring
  have e3 := hδ.res P hP _ hoff hx u hres
  refine Units.ext ?_
  rw [← e1, e3]
  rfl

end GlobalTheory.TwistResidue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDictionaryFrameMemOpenFramesStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeDictionary_frame_mem_open_frames : ∀ {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} (V : HSp D) (U : Unf Xo c σ V.rank) (dict : GA D V → Σ k, Frame (U.X k).Ψ V.rank)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hσ : GoodEmb c σ) (hA : l.A = 1) (hU : IsUnf U) (hW : ∀ k, ModelW V rfl (U.X k))
    (hD : DictLat U V rfl dict io e F ik φ th x₀) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀), ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom := by
  first | exact @GlobalTheory.DictDom.frame_mem_dom | exact GlobalTheory.DictDom.frame_mem_dom | (intros; apply GlobalTheory.DictDom.frame_mem_dom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFinitePartOfLiftStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_finite_part_of_lift : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C M)) →
    z ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) := by
  first | exact @GlobalTheory.UseLoc.DescHf.descHf | exact GlobalTheory.UseLoc.DescHf.descHf | (intros; apply GlobalTheory.UseLoc.DescHf.descHf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemIntegralFormsOfRationalAndLocalSpansStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralForms_of_rational_and_local_spans : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → CUnit C.cc₂ → ∀ (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom wa n → ∀ (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) (φ : GA D (T.V j σ) → ℂ), φ ∈ Submodule.span C.σ₂.range (C.ratForms wa n) → (∀ la ∈ S, φ ∈ Submodule.span (locRing C.σ₂ la) (C.intForms wa n {la})) → φ ∈ C.intForms wa n S := by
  first | exact @GlobalTheory.LevelSeries.SpanInt.mem_intForms_of_spans | exact GlobalTheory.LevelSeries.SpanInt.mem_intForms_of_spans | (intros; apply GlobalTheory.LevelSeries.SpanInt.mem_intForms_of_spans <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OmegaQEqGaussMulFlatTransform
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000

namespace GlobalTheory.FlatForm

open GlobalTheory.FlatConj

theorem gaussGL_inv {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ) :
    gaussGL ψ⁻¹ ξ⁻¹ r = (starRingEnd ℂ) (gaussGL ψ ξ r) := by
  unfold gaussGL
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, AddChar.inv_apply, AddChar.map_neg_eq_conj]
  congr 1
  set u := Matrix.GeneralLinearGroup.det x
  have h1 : ((ξ u : ℂˣ) : ℂ) ^ Fintype.card kˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  have h2 : ‖((ξ u : ℂˣ) : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h1 Fintype.card_ne_zero
  rw [MonoidHom.inv_apply, inv_inv, Units.val_inv_eq_inv_val, map_inv₀, ← Complex.inv_eq_conj h2, inv_inv]

theorem gaussGL_mul_inv {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ)
    (hψ : ψ.IsPrimitive) (hξ : ξ ≠ 1) :
    gaussGL ψ ξ r * gaussGL ψ⁻¹ ξ⁻¹ r = (Fintype.card k : ℂ) ^ (r ^ 2) := by
  obtain ⟨hnorm, -⟩ := GlobalTheory.T.galois_matrix_gaussSum_eq_char_pow_mul k ψ ξ r hψ hξ (gaussGL ψ ξ r) rfl
  rw [gaussGL_inv, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
  push_cast
  rfl

theorem gaussGL_ne_zero {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ)
    (hψ : ψ.IsPrimitive) (hξ : ξ ≠ 1) : gaussGL ψ ξ r ≠ 0 := fun h => by
  have := gaussGL_mul_inv ψ ξ r hψ hξ
  rw [h, zero_mul] at this
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) this.symm

theorem fourier_flat (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r t : ℕ) (hψ : ψ.IsPrimitive)
    (hξ : ξ ≠ 1) (u : Matrix (Fin (r + t)) (Fin r) k) :
    (∑ y : Matrix (Fin r) (Fin (r + t)) k, (if h : IsUnit (topL r (-y)).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
      ψ (Matrix.trace (y * u))) = ((Fintype.card k : ℂ) ^ ((r + t) * r) * (gaussGL ψ ξ r)⁻¹) *
      (if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) := by
  have hψ' : (ψ⁻¹).IsPrimitive := addChar_inv_isPrimitive_of_isPrimitive ψ hψ
  have hξ' : ξ⁻¹ ≠ 1 := inv_ne_one.mpr hξ
  obtain ⟨hsing, hinv⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ⁻¹ ξ⁻¹ r hψ' hξ'
  have hmul := gaussGL_mul_inv ψ ξ r hψ hξ
  have hne := gaussGL_ne_zero ψ ξ r hψ hξ
  set G : ℂ := ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
    ψ⁻¹ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) with hG
  set q : ℂ := (Fintype.card k : ℂ) with hq
  have hC : q ^ ((r + t) * r) * (gaussGL ψ ξ r)⁻¹ = q ^ (r * t) * G := by
    have hG' : gaussGL ψ⁻¹ ξ⁻¹ r = G := rfl
    rw [hG'] at hmul
    rw [show (r + t) * r = r * t + r ^ 2 by ring, pow_add, ← hmul]
    field_simp
  rw [hC]
  set u₁ := u.submatrix (Fin.castAdd t) id
  set u₂ := u.submatrix (Fin.natAdd r) id
  have hsplit : ∀ p : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k,
      ((if h : IsUnit (-p.1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (p.1 * u₁))) *
        ψ (trace (p.2 * u₂)) =
      (if h : IsUnit (topL r (-(squareAndRectColumnsEquivWideMatrix p))).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (Matrix.trace (squareAndRectColumnsEquivWideMatrix p * u)) := by
    intro p
    have e1 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.castAdd t) = p.1 :=
      congrArg Prod.fst (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    have e2 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.natAdd r) = p.2 :=
      congrArg Prod.snd (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    rw [mul_assoc, ← AddChar.map_add_eq_mul, trace_mul_split_castAdd_natAdd _ u, topLeftBlock_neg_eq_submatrix_castAdd, e1, e2]
  rw [← Fintype.sum_equiv squareAndRectColumnsEquivWideMatrix _ _ hsplit, Fintype.sum_prod_type]
  rw [show (∑ x : Matrix (Fin r) (Fin r) k, ∑ y : Matrix (Fin r) (Fin t) k,
      (if h : IsUnit (-(x, y).1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace ((x, y).1 * u₁)) *
        ψ (trace ((x, y).2 * u₂))) =
      (∑ x : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-x).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (trace (x * u₁))) * ∑ y : Matrix (Fin r) (Fin t) k, ψ (trace (y * u₂)) by
    rw [Finset.sum_mul_sum]]
  rw [sum_GL_character_neg_det_addChar_trace, sum_addChar_trace_rectMatrix_mul ψ hψ u₂]
  by_cases hu2 : u₂ = 0
  swap
  · rw [if_neg hu2, mul_zero, dif_neg (fun h => hu2 ((lowZero_iff_submatrix_natAdd_eq_zero u).mp h.1)), mul_zero]
  rw [if_pos hu2]
  by_cases hdet : IsUnit u₁.det
  swap
  · have h0 : u₁.det = 0 := by
      by_contra h; exact hdet (isUnit_iff_ne_zero.mpr h)
    rw [hsing u₁ h0, zero_mul, dif_neg, mul_zero]
    rintro ⟨-, h⟩
    rw [topLeftBlock_eq_submatrix_castAdd] at h
    exact hdet h
  have hh : LowZero r u ∧ IsUnit (topL r u).det := ⟨(lowZero_iff_submatrix_natAdd_eq_zero u).mpr hu2, by rw [topLeftBlock_eq_submatrix_castAdd]; exact hdet⟩
  rw [dif_pos hh]
  set a : GL (Fin r) k := Matrix.GeneralLinearGroup.mkOfDetNeZero u₁ hdet.ne_zero
  have ha := hinv a
  simp only [Matrix.one_mul] at ha
  have hau : (a : Matrix (Fin r) (Fin r) k) = u₁ := rfl
  rw [hau] at ha
  rw [ha, ← hG]
  have hunit : hh.2.unit = Matrix.GeneralLinearGroup.det a := Units.ext (by simp [hau, topLeftBlock_eq_submatrix_castAdd, u₁])
  rw [hunit, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, _root_.zpow_neg_one]
  ring

theorem gaussP_ne_zero {E : Type} [Field E] [NumberField E] (PP : Pl E) (ψ : AddChar (kP PP) ℂ) (ξ : (kP PP)ˣ →* ℂˣ) (r : ℕ)
    (hψ : ψ.IsPrimitive) (hξ : ξ ≠ 1) : gaussP PP ψ ξ r ≠ 0 :=
  @gaussGL_ne_zero (kP PP) (resField PP) (resFintype PP) ψ ξ r hψ hξ

theorem omegaQ_eq_gauss_mul_flat_transform (D : D7) [inst : ∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E))
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (r n : ℕ) (hrn : r ≤ n)
    (hQ : ∀ PP ∈ Q, (ψP PP).IsPrimitive ∧ ξ PP ≠ 1) (ub : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP)) :
    omegaQ Q r ξ (-1) ub = (∏ PP ∈ Q, ((Nat.card (kP PP) : ℂ) ^ (n * r) * (gaussP PP (ψP PP) (ξ PP) r)⁻¹))⁻¹ *
      ∑ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)),
        omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) *
          ∏ PP : ↥Q, ψP PP.1 (Matrix.trace (y PP * ub PP.1)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  obtain rfl : inst = fun PP => resFintype PP := Subsingleton.elim _ _
  letI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => resFintype PP
  let fl : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin (r + t)) (kP PP) → ℂ := fun PP y =>
    if h : IsUnit (topL r y).det then ((ξ PP h.unit : ℂˣ) : ℂ) else 0
  let fq : ∀ PP : Pl D.host.E, Matrix (Fin (r + t)) (Fin r) (kP PP) → ℂ := fun PP u =>
    if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0
  let C : Pl D.host.E → ℂ := fun PP => (Nat.card (kP PP) : ℂ) ^ ((r + t) * r) * (gaussP PP (ψP PP) (ξ PP) r)⁻¹
  have hC0 : ∀ PP : ↥Q, C PP ≠ 0 := fun PP =>
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
      (inv_ne_zero (gaussP_ne_zero _ _ _ _ (hQ _ PP.2).1 (hQ _ PP.2).2))
  have hCe : ∀ (PP : ↥Q) (u : Matrix (Fin (r + t)) (Fin r) (kP PP.1)),
      (∑ y : Matrix (Fin r) (Fin (r + t)) (kP PP.1), fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * u))) = C PP * fq PP.1 u := by
    intro PP u
    have := @fourier_flat (kP PP.1) (resField PP.1) (resFintype PP.1) (ψP PP.1) (ξ PP.1) r t (hQ _ PP.2).1 (hQ _ PP.2).2 u
    rw [← Nat.card_eq_fintype_card] at this
    exact this
  have hq : omegaQ Q r ξ (-1) ub = ∏ PP : ↥Q, fq PP.1 (ub PP.1) := by
    rw [← Finset.attach_eq_univ]
    unfold omegaQ
    convert GlobalTheory.FlatFourierQ.dite_prod' Q (fun PP => LowZero r (ub PP) ∧ IsUnit (topL r (ub PP)).det)
      (fun PP h => ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ))
  have hf : ∀ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin (r + t)) (kP PP.1)),
      omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) = ∏ PP : ↥Q, fl PP.1 (-(y PP)) := by
    intro y
    have e0 : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin (r + t)) (kP PP),
        omegaFlat Q r ξ Y = ∏ PP ∈ Q.attach, fl PP.1 (Y PP.1) := by
      intro Y
      unfold omegaFlat
      convert GlobalTheory.FlatFourierQ.dite_prod' Q (fun PP => IsUnit (topL r (Y PP)).det) (fun PP h => ((ξ PP h.unit : ℂˣ) : ℂ))
    rw [e0, Finset.attach_eq_univ]
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [dif_pos PP.2, Subtype.coe_eta]
  have hprod : (∏ PP ∈ Q, C PP) = ∏ PP : ↥Q, C PP := (Finset.prod_coe_sort Q C).symm
  show _ = (∏ PP ∈ Q, C PP)⁻¹ * _
  simp only [hf, ← Finset.prod_mul_distrib]
  have hs := Finset.prod_univ_sum (t := fun (PP : ↥Q) => (Finset.univ : Finset (Matrix (Fin r) (Fin (r + t)) (kP PP.1))))
    (f := fun (PP : ↥Q) (y : Matrix (Fin r) (Fin (r + t)) (kP PP.1)) => fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * ub PP.1)))
  rw [Fintype.piFinset_univ] at hs
  rw [← hs]
  simp only [hCe]
  rw [hprod, Finset.prod_mul_distrib (f := fun PP : ↥Q => C PP) (g := fun PP : ↥Q => fq PP.1 (ub PP.1)), hq, ← mul_assoc, inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun PP _ => hC0 PP), one_mul]

end GlobalTheory.FlatForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OnePlaceTwistTrivialOnCongruentUnitsStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.UnivCover

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.onePlaceTwist_trivial_on_congruent_units : ∀ (D : D7) {A : Type} [CommGroup A] (PP : Pl D.host.E) (χ : (AE D)ˣ →* A) (κ : GlobalTheory.ExportSeries.ResChars D A), (⟨{PP}, χ, κ⟩ : GlobalTheory.ExportSeries.Twist D A).Good → ∀ N : ℕ, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1 := by
  first | exact @GlobalTheory.OnePlaceCong.chi_eq_one_of_cong | exact GlobalTheory.OnePlaceCong.chi_eq_one_of_cong | (intros; apply GlobalTheory.OnePlaceCong.chi_eq_one_of_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneTmulMemSupLatticeOfMemLocalUnitBall
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BallSup

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool)
  (j : Fin D.R.m)

theorem nrm_le_one_of_mem_locBall {f : NX.FmK S ((j : ℕ) + 1)} (hf : f ∈ locBall YS fw iC b j)
    (y : (Rl.FW j).Pt (placeC YS iC b)) :
    (Rl.FW j).nrm (placeC YS iC b) y (fw.e j (cuspOf YS fw j f)) ≤ 1 := by
  rw [fw.nrm_eq, Core.nrmM_le_one_iff]
  obtain ⟨q, hq⟩ := (fw.pt j (placeC YS iC b) y).2
  rcases q with ⟨qv, T, io, e, ho, y', hy', eta, heta, rfl⟩
  obtain ⟨k, hk⟩ := ReadExist.exists_isReading (D.ntw.l i) T0.Q.c.F (embC YS iC b) T io e ho hy'
  obtain ⟨z, hz⟩ := PtC.exists_of_reading hk y' hy'
  have h1 := hf z
  rw [hz _ _ _ (cuspOf_mem_sec YS fw j f)] at h1
  obtain ⟨a, ha⟩ := (hk.int _).1 h1
  rw [← hq]
  change 0 ≤ nval T.V e (evI y' _)
  by_cases hx : evI y' (cuspOf YS fw j f : T0.R ((j : ℕ) + 1)) = 0
  · rw [hx, nval_zero]; exact le_top
  · rw [nval_of_ne hx]
    exact EReal.coe_nonneg.2 (div_nonneg (Int.cast_nonneg
      ((GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff _).1 ⟨a, ha⟩)) (Nat.cast_nonneg _))

theorem one_tmul_mem_Bsup_of_mem_locBall
    (hiC : ∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range)
    (f : NX.FmK S ((j : ℕ) + 1)) (hf : f ∈ locBall YS fw iC b j) :
    (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) ∈ NX.Bsup S i ((j : ℕ) + 1) b := by
  obtain ⟨s, hs, hsM⟩ := GlobalTheory.supLattice_localisation_of_unitBall D.what₂.LL T0.Q.c.F _ _ _ (Rl.FW j)
    (GlobalTheory.GoodLat.Obj.mkFull_of_tie fw j).2 (placeC YS iC b) (fw.e j (cuspOf YS fw j f))
    (nrm_le_one_of_mem_locBall YS fw iC b j hf)
  rw [e_cuspOf] at hsM
  set c : S.Ks := (YS.fi j).eK.symm (s : T0.Q.c.F) with hcdef
  have hc : (YS.fi j).e (c • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1) = s • (YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 := by
    rw [← algebraMap_smul D.what₂.LL c, LinearEquiv.map_smul, ← (YS.fi j).eK_LL c, hcdef, RingEquiv.apply_symm_apply,
      algebraMap_smul]
    exact (algebraMap_smul T0.Q.c.F s _)
  have hcM : c • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK := by
    rw [(YS.fi j).mkK, hc]; exact hsM

  have hgen : (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] (c • f)) ∈ NX.Bsup S i ((j : ℕ) + 1) b :=
    Submodule.subset_span ⟨c • f, hcM, rfl⟩
  have heK : eKs YS c = (s : T0.Q.c.F) := by
    apply (algebraMap T0.Q.c.F D.what₂.LL).injective
    rw [eKs_LL, ← (YS.fi j).eK_LL c, hcdef, RingEquiv.apply_symm_apply]
  obtain ⟨x, hx⟩ : ∃ x : FractionRing (D.ntw.O i), x = NX.ιK S i b c := ⟨_, rfl⟩
  have hn1 : ‖iC x‖ = 1 := by
    rw [hx]
    change ‖embS S iC b c‖ = 1
    rw [← embC_eKs YS iC b, heK]
    refine le_antisymm (norm_int_le_one _ s) (not_lt.1 fun h => hs ?_)
    exact (mem_placeAt _ s).2 h
  have hne : x ≠ 0 := fun h => by
    rw [h, map_zero, norm_zero] at hn1; exact zero_ne_one hn1
  obtain ⟨u, hu⟩ := (hiC x⁻¹).1 (by rw [map_inv₀, norm_inv, hn1, inv_one])
  have key : (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) =
      u • (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] (c • f)) := by
    rw [← algebraMap_smul (FractionRing (D.ntw.O i)) u, hu]
    have h1 : (c • (1 : NX.KB S i b)) = (show NX.KB S i b from x) := by
      rw [Algebra.smul_def, mul_one, hx]; rfl
    change (1 : NX.KB S i b) ⊗ₜ[S.Ks] f =
      (show NX.KB S i b from x⁻¹) • ((1 : NX.KB S i b) ⊗ₜ[S.Ks] (c • f) : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1))
    rw [← TensorProduct.smul_tmul, h1, TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    exact (inv_mul_cancel₀ hne).symm
  rw [key]
  exact Submodule.smul_mem _ u hgen

end BallSup

theorem one_tmul_mem_Bsup : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f ∈ locBall YS fw iC b j, (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) ∈ NX.Bsup S i ((j : ℕ) + 1) b := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC hiC b j f hf
  exact one_tmul_mem_Bsup_of_mem_locBall YS fw iC b j hiC f hf

end GlobalTheory.GeoTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OpenKernelIdeleCharacterTrivialFinitePartOneStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.UnivCover

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openKernel_ideleCharacter_trivial_finitePart_one : ∀ (D : D7) {A : Type} [Group A] (χ : (AE D)ˣ →* A), IsOpen (χ.ker : Set (AE D)ˣ) → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → χ x = 1 := by
  first | exact @GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one | exact GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one | (intros; apply GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionAdjointFrameConjHalfTwoPartsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_adjointFrame_conj_half_two_parts : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → IsIntM (frMapAdj S T βS βT x) → (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT (cA D eg • x)) = redM PP (frMapAdj S T βS βT x)) ∧ (∀ PP ∈ Q, redM PP (frMapAdj S T βS βT (cA D eQ • x)) = redM PP (frMapAdj S T βS βT x)) := by
  first | exact @GlobalTheory.TwoStepRed.redM_twoStep | exact GlobalTheory.TwoStepRed.redM_twoStep | (intros; apply GlobalTheory.TwoStepRed.redM_twoStep <;> assumption)
end

