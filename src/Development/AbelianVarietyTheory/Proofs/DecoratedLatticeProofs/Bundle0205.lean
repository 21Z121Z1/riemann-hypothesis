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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesSummableOnCovolumeDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharQuotientUnramifiedAtTwistPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.ChainTw.QuotUnr

theorem loc_eq_of_isRes {D : D7} {H H' : Formalism.L2.Host.HChar D.host.E} {PP : Pl D.host.E} {a : (kP PP)ˣ →* ℂˣ}
    (h : IsRes H PP a) (h' : IsRes H' PP a) (x : (PP.adicCompletion D.host.E)ˣ) (hx : Formalism.L2.Host.IsUnitAt PP x) :
    H.loc PP x = H'.loc PP x := by
  have ht := GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes D H PP a h
  have ht' := GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes D H' PP a h'
  obtain ⟨b, hb⟩ := GlobalTheory.GaussModulus.exists_int_approx PP (x := (x : PP.adicCompletion D.host.E)) (le_of_eq hx) 1
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hbv : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E)) = 1 := by
    have hx1 : Valued.v (x : PP.adicCompletion D.host.E) = 1 := hx
    have e : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E)) = Valued.v (x : PP.adicCompletion D.host.E) :=
      Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap, hx1]; exact lt_of_le_of_lt hb hlt)
    rw [e, hx1]
  have hbP : b ∉ PP.asIdeal := by
    intro hm
    have h1 : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E b) < 1 := (PP.valuation_lt_one_iff_mem b).2 hm
    have h2 : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E b) = 1 := by
      rw [← GlobalTheory.GaussModulus.valued_algebraMap]; exact hbv
    exact (ne_of_lt h1) h2
  have hb0 : (b : D.host.E) ≠ 0 := fun h0 => hbP (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  let kb : D.host.Eˣ := Units.mk0 _ hb0
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  have hu0 : (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := fun h0 => hbP (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  let u : (kP PP)ˣ := Units.mk0 _ hu0
  have e1 := h b kb u rfl rfl
  have e2 := h' b kb u rfl rfl

  obtain ⟨y, hy⟩ : ∃ y : (PP.adicCompletion D.host.E)ˣ, y = x * (Formalism.L2.Host.atFin PP kb)⁻¹ := ⟨_, rfl⟩
  have hkv : Valued.v ((Formalism.L2.Host.atFin PP kb : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) = 1 := hbv
  have hyu : Formalism.L2.Host.IsUnitAt PP y := by
    show Valued.v ((y : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) = 1
    rw [hy, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hkv, inv_one, mul_one]
    exact hx
  have hy1 : Valued.v ((y : PP.adicCompletion D.host.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have hk0 : ((Formalism.L2.Host.atFin PP kb : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) =
        algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E) := rfl
    have e : (y : PP.adicCompletion D.host.E) - 1 =
        ((x : PP.adicCompletion D.host.E) - algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E)) *
          (algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E))⁻¹ := by
      have hne : algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E) ≠ 0 := by
        rw [← hk0]; exact Units.ne_zero _
      rw [hy, Units.val_mul, Units.val_inv_eq_inv_val, hk0, sub_mul, mul_inv_cancel₀ hne]
    rw [e, map_mul, map_inv₀, hbv, inv_one, mul_one]
    exact hb
  have hxy : x = Formalism.L2.Host.atFin PP kb * y := by rw [hy, mul_left_comm, mul_inv_cancel, mul_one]
  rw [hxy, map_mul, map_mul, ht y hyu hy1, ht' y hyu hy1, mul_one, mul_one]
  exact e1.symm.trans e2

end GlobalTheory.ChainTw.QuotUnr

open GlobalTheory.ChainTw.QuotUnr in

theorem GlobalTheory.ChainTw.quot_unrAt_twist : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ PP ∈ w.Q, ∀ i j : ℕ, 1 ≤ i → i ≤ D.R.m → 1 ≤ j → j ≤ D.R.m → GlobalTheory.LFun.UnrAt (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP := by
  intro D c w hw PP hPP i j hi1 him hj1 hjm
  have hPg : PP ∈ c.Pg := by classical rw [hw.union]; exact Finset.mem_union_right _ hPP
  obtain ⟨Hi, hci, hri⟩ := hw.com.res ⟨i - 1, by omega⟩
  obtain ⟨Hj, hcj, hrj⟩ := hw.com.res ⟨j - 1, by omega⟩
  simp only [Nat.sub_add_cancel hi1, Nat.sub_add_cancel hj1] at hci hri hcj hrj
  have ri := hri PP hPg
  have rj := hrj PP hPg
  rw [hw.chiQ i PP hPP] at ri
  rw [hw.chiQ j PP hPP] at rj
  intro x hx
  have li := DFunLike.congr_fun (GlobalTheory.LFun.locChar_eq_of_chrEq hci PP) x
  have lj := DFunLike.congr_fun (GlobalTheory.LFun.locChar_eq_of_chrEq hcj PP) x
  have split : GlobalTheory.LFun.locChar (c.μ i * (c.μ j)⁻¹) PP x =
      GlobalTheory.LFun.locChar (c.μ i) PP x * (GlobalTheory.LFun.locChar (c.μ j) PP x)⁻¹ := by
    simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
  rw [split, li, lj, loc_eq_of_isRes ri rj x hx, mul_inv_cancel]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorMoveAcrossInvariantBilinearStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_operator_move_across_invariant_bilinear : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → CosetSym K → ∀ (U X X' : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X'] (π : Representation ℂ G U) (ρ : Representation ℂ G X) (b : U →ₗ[ℂ] X →ₗ[ℂ] X'), (∀ g u y, b (π g u) (ρ g y) = b u y) → ∀ f ∈ fixed π K, ∀ x ∈ fixed ρ K, ∀ φ ∈ Hecke ℂ K, (fun g => φ g⁻¹) ∈ Hecke ℂ K ∧ b (heckeVec π K φ f) x = b f (heckeVec ρ K (fun g => φ g⁻¹) x) := by
  first | exact @GlobalTheory.ChainOnto.heckeVec_move | exact GlobalTheory.ChainOnto.heckeVec_move | (intros; apply GlobalTheory.ChainOnto.heckeVec_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeisMixSource

theorem heis_mixS : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ x a, d.mixS T ψ v.μ v.𝓕 (heisO ψ S T (d.extX T a) f) x = d.mixS T ψ v.μ v.𝓕 f (x + a)) ∧ (∀ x a, d.mixS T ψ v.μ v.𝓕 (heisO ψ S T (d.extY T a) f) x = ψ (symplO S T (d.extX T x) (d.extY T a)) • d.mixS T ψ v.μ v.𝓕 f x) ∧ (∀ x w, d.mixS T ψ v.μ v.𝓕 (heisO ψ S T (d.ext0 T w) f) x = heisO ψ S₀ T w (d.mixS T ψ v.μ v.𝓕 f x)) ∧ (Continuous fun p : Mx D T.rank ρ × WO S₀ T => d.mixS T ψ v.μ v.𝓕 f p.1 p.2) ∧ ∀ w, HasSum (fun x : Matrix (Fin T.rank) (Fin ρ) D.host.E => d.mixS T ψ v.μ v.𝓕 f (rat x) w) (f (d.ext0 T w)) := by
  intro D ψ hψ S S₀ T ρ d v f hf
  have hψc : Continuous ψ := hψ.1.1
  refine ⟨fun x a => GlobalTheory.MixModel.Check.mixS_heis_extX d v.μ v.𝓕 f a x, fun x a => ?_,
    fun x w => GlobalTheory.MixModel.Check.mixedModelSource_heisenberg_anisotropic_part d v.μ v.𝓕 f w x, ?_, fun w => ?_⟩
  · funext w₀
    rw [GlobalTheory.MixModel.Check.mixS_heis_extY d v.covol hf a x w₀]
    rfl
  · have hX : Continuous (d.extX T) := continuous_id.matrix_mul continuous_const
    have hY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
    have h0 : Continuous (d.ext0 T) := continuous_id.matrix_mul continuous_const
    have K := GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param D T.rank ρ v (Mx D T.rank ρ × WO S₀ T)
      (fun a p => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T p.1) (heisO ψ S T (d.ext0 T p.2) f)) 0) ?_
      (fun γ hγ x p => d.integrandS_periodic hf p.1 p.2 γ hγ x)
    · exact K.2.1
    · have e : (Function.uncurry fun (a : Mx D T.rank ρ) (p : Mx D T.rank ρ × WO S₀ T) =>
          heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T p.1) (heisO ψ S T (d.ext0 T p.2) f)) 0) =
          fun q => ψ (symplOH S T (d.extY T q.1) (d.extX T q.2.1)) *
            f (d.extY T q.1 + d.extX T q.2.1 + d.ext0 T q.2.2) := by
        funext q; exact d.integrandS_eq f q.2.1 q.1 q.2.2
      rw [e]
      exact (hψc.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hY.comp continuous_fst)
        (hX.comp (continuous_fst.comp continuous_snd)))).mul
        (hf.cont.comp (((hY.comp continuous_fst).add (hX.comp (continuous_fst.comp continuous_snd))).add
          (h0.comp (continuous_snd.comp continuous_snd))))
  · have hg0 : heisO ψ S T (d.ext0 T w) f 0 = f (d.ext0 T w) := by
      simp only [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]
    rcases Nat.eq_zero_or_pos ρ with rfl | hρ
    · have hz := (GlobalTheory.T.wittDecomposition_mixedCoords_rank_zero D ψ).1 S S₀ T d v.μ v.𝓕 v.covol f
      haveI : Subsingleton (Matrix (Fin T.rank) (Fin 0) D.host.E) := ⟨fun a b => Matrix.ext fun _ j => j.elim0⟩
      have h1 : ∀ x : Matrix (Fin T.rank) (Fin 0) D.host.E, d.mixS T ψ v.μ v.𝓕 f (rat x) w = f (d.ext0 T w) :=
        fun x => by rw [hz]
      rw [show (fun x : Matrix (Fin T.rank) (Fin 0) D.host.E => d.mixS T ψ v.μ v.𝓕 f (rat x) w) =
        fun _ => f (d.ext0 T w) from funext h1]
      exact hasSum_single (f := fun _ : Matrix (Fin T.rank) (Fin 0) D.host.E => f (d.ext0 T w))
        (0 : Matrix (Fin T.rank) (Fin 0) D.host.E) fun b hb => absurd (Subsingleton.elim b 0) hb
    · obtain ⟨hsplit, hrat, hYe, hXe, -, hres, -, -, -⟩ := GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d
      have hg : IsThetaFunO ψ S T (heisO ψ S T (d.ext0 T w) f) :=
        (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 _ _ hf
      have hcov : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ) v.μ v.𝓕 := hrat ▸ v.covol
      have hG := GlobalTheory.MixModel.gram_conjTranspose S
      have c1 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * S.gram * d.e' = 1 := by
        have h := congrArg Matrix.conjTranspose d.e'e
        rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
          Matrix.conjTranspose_one, ← Matrix.mul_assoc] at h
      have c2 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e' * S.gram * d.e' = 0 := d.e'e'
      have c3 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e' * S.gram * d.i₀ = 0 := by
        have h := congrArg Matrix.conjTranspose d.i₀e'
        rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
          Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at h
      have H := (GlobalTheory.TwFour.value_zero_eq_sum_restrictions D S S₀ T ρ d.e d.e' d.i₀ (hsplit hρ) c1 c2 c3 ψ hψ
        v.μ v.𝓕 hcov _ hg).2
      rw [hg0] at H
      convert H using 1
      funext y
      rw [hXe, ← hres, GlobalTheory.MixModel.Check.mixedModelSource_heisenberg_anisotropic_part]
      simp only [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]
      rfl

end GlobalTheory.HeisMixSource
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalCharacterConjugationInverse
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

theorem secW_cA (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (hc : IsConjAt D.sp.cm.sig h c)
    (z : w.adicCompletion D.host.E) : secW hw h (c z) = cA D (secW hw h z) := by
  obtain ⟨y, rfl⟩ := (GlobalTheory.LFun.InertChart.complEquiv hw h).surjective z
  have e1 : c (GlobalTheory.LFun.InertChart.complEquiv hw h y) =
      GlobalTheory.LFun.InertChart.complEquiv hw h (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig y) := hc y
  rw [e1]
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _) =
    cA D (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _))
  rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  exact (GlobalTheory.EmbChart.sigR_tensAt v _ y).symm

theorem thW_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsConjAt D.sp.cm.sig h c → (∀ z, c (c z) = z) → ∀ z, thW ψ hw h (k * c k) (c z) * thW ψ hw h (k * c k) z = 1 := by
  intro D ψ v w hw h c k hc hcc z
  have h1 : secW hw h (k * c k * c z) = cA D (secW hw h (k * c k * z)) := by
    rw [← secW_cA D hw h c hc]
    congr 1
    rw [map_mul c, map_mul c, hcc, mul_comm k (c k)]
  rw [thW_apply, thW_apply, h1, ← GlobalTheory.DualPairCheck.trace_cA (_ * cA D _), RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA,
    GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg, neg_mul, LinearMap.map_neg,
    ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

end GlobalTheory.InertFrameLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertSupportedPointIntegralFramesMemLattice
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem secW_toCompl_tmul_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (b : Fv D.host.F v) (o m : D.host.E) :
    secW hw h (toCompl h (b ⊗ₜ[D.host.F] o) * algebraMap D.host.E (w.adicCompletion D.host.E) m) =
      pairA D.host.F 0 (singleFin v b) ⊗ₜ[D.host.F] (o * m) := by
  have e : toCompl h (b ⊗ₜ[D.host.F] o) * algebraMap D.host.E (w.adicCompletion D.host.E) m =
      toCompl h (b ⊗ₜ[D.host.F] (o * m)) := by
    rw [toCompl_tmul, toCompl_tmul, map_mul, mul_assoc]
  have e2 : toCompl h (b ⊗ₜ[D.host.F] (o * m)) = GlobalTheory.LFun.InertChart.complEquiv hw h (b ⊗ₜ[D.host.F] (o * m)) := rfl
  rw [e, e2]
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _) = _
  rw [RingEquiv.symm_apply_apply, GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]

theorem secW_rank_one_mem (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    {a : D.host.E} (ha : a ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ frameLat S)
    {t : Fin T.rank → D.host.E} (ht : t ∈ frameLat T) {z : w.adicCompletion D.host.E} (hz : z ∈ Ov D.host.E w) :
    (Matrix.of fun i j => secW hw h (z * algebraMap D.host.E (w.adicCompletion D.host.E)
      (a * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  obtain ⟨y, rfl⟩ := GlobalTheory.LFun.InertChart.toCompl_surjective h z
  have hy := (GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h y).2 hz
  refine intLoc_induction (p := fun y => (Matrix.of fun i j => secW hw h (toCompl h y *
      algebraMap D.host.E (w.adicCompletion D.host.E) (a * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (frameLat S) (frameLat T) (fun u => u = v)) (fun b hb o => ?_) ?_ (fun y y' h1 h2 => ?_)
      (fun y h1 => ?_) hy
  · refine AddSubgroup.subset_closure ⟨singleFin v b, fun u => ?_, fun u hu => evalV_singleFin_ne hu _, a, ha, s, hs,
      o • t, Submodule.smul_mem _ o ht, ?_⟩
    · by_cases e : u = v
      · subst e; rw [evalV_singleFin_self]; exact hb
      · rw [evalV_singleFin_ne e]; exact zero_mem _
    · ext i j
      rw [Matrix.of_apply, Matrix.of_apply, secW_toCompl_tmul_mul]
      congr 1
      rw [Pi.smul_apply, Algebra.smul_def]
      ring
  · convert zero_mem (latO S T (frameLat S) (frameLat T) (fun u => u = v)) using 1
    ext i j
    simp
  · convert add_mem h1 h2 using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, map_add, add_mul]
  · convert neg_mem h1 using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.neg_apply, map_neg, neg_mul]

theorem secW_span_mem (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} (hc : IsConjAt D.sp.cm.sig h c) {S T : HSp D}
    {a : D.host.E} (ha : a ∈ D.host.AA) {p : Fin T.rank → w.adicCompletion D.host.E} (hp : p ∈ latAt w (frameLat T))
    {y : Fin S.rank → w.adicCompletion D.host.E} (hy : y ∈ latAt w (frameLat S)) :
    ∀ z ∈ Ov D.host.E w, (Matrix.of fun i j => secW hw h (z * algebraMap D.host.E (w.adicCompletion D.host.E) a * p i *
      ∑ k, c (y k) * algebraMap D.host.E (w.adicCompletion D.host.E) (S.gram k j)) : WO S T) ∈
      latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  have hst : ∀ x : D.host.E, star x = D.sp.cm.sig x := fun _ => rfl
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t, ht, rfl⟩ := hp
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, hs, rfl⟩ := hy
      intro z hz
      convert secW_rank_one_mem hw h ha hs ht hz using 1
      ext i j
      simp only [Matrix.of_apply, GlobalTheory.LFun.InertChart.conj_algebraMap hc, map_mul, map_sum, hst]
      ring_nf
    | zero =>
      intro z hz
      convert zero_mem (latO S T (frameLat S) (frameLat T) (fun u => u = v)) using 1
      ext i j
      simp
    | add y y' _ _ h1 h2 =>
      intro z hz
      convert add_mem (h1 z hz) (h2 z hz) using 1
      ext i j
      simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    | smul o y _ h1 =>
      intro z hz
      convert h1 (z * c o) (mul_mem hz (GlobalTheory.LFun.InertChart.conj_mem hw hc o.2)) using 1
      ext i j
      have e : ∀ k, c ((o • y) k) * algebraMap D.host.E (w.adicCompletion D.host.E) (S.gram k j) =
          c o * (c (y k) * algebraMap D.host.E (w.adicCompletion D.host.E) (S.gram k j)) := fun k => by
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, mul_assoc]
      simp only [Matrix.of_apply, e, ← Finset.mul_sum]
      congr 1
      ring
  | zero =>
    intro z hz
    convert zero_mem (latO S T (frameLat S) (frameLat T) (fun u => u = v)) using 1
    ext i j
    simp
  | add p p' _ _ h1 h2 =>
    intro z hz
    convert add_mem (h1 z hz) (h2 z hz) using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add, add_mul, mul_add]
  | smul o p _ h1 =>
    intro z hz
    convert h1 (z * o) (mul_mem hz o.2) using 1
    ext i j
    simp only [Matrix.of_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul]
    congr 1
    ring

theorem uPt_mem_latO : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → ∀ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) → uPt hw h k aS aT x ∈ latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  intro D v w hw h S T k aS aT hk haS haT x hx
  obtain ⟨-, ⟨a₀, ha₀, rfl⟩, -⟩ := hk
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt D.sp.cm.sig hw h
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (isCMExt_host D) hw hc
  have hcc : ∀ z, c (c z) = z := hU.1
  set ι := algebraMap D.host.E (w.adicCompletion D.host.E) with hι
  set Gw := S.gram.map ι with hGw
  set Gi := (S.gram⁻¹).map ι with hGi
  have hGG : Gi * Gw = 1 := by
    rw [hGi, hGw, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit S),
      Matrix.map_one _ (map_zero _) (map_one _)]
  set N := (aS⁻¹).1 * Gi with hN
  have hG : ∀ l i, c (ι (S.gram l i)) = ι (S.gram i l) := fun l i => by
    rw [GlobalTheory.LFun.InertChart.conj_algebraMap hc, (GlobalTheory.Doubling.isHermND_gram S).1 i l]
  have hY : ∀ j, (fun l => c (N j l)) ∈ latAt w (frameLat S) := by
    intro j
    rw [GlobalTheory.LFun.InertChart.mem_latAt_iff hw hc (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D S v)]
    intro y hy
    have hu := (haS ((aS⁻¹).1 *ᵥ y)).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]) j
    have e : Formalism.UG.hform c (S.gram.map ι) y (fun l => c (N j l)) = c ((N *ᵥ (Gw *ᵥ y)) j) := by
      simp only [Formalism.UG.hform, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hG, hGw]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e, Matrix.mulVec_mulVec, hN, Matrix.mul_assoc, hGG, Matrix.mul_one]
    exact GlobalTheory.LFun.InertChart.conj_mem hw hc hu
  have hcol : ∀ j l, ∑ m, c (c (N j m)) * ι (S.gram m l) = (aS⁻¹).1 j l := fun j l => by
    simp only [hcc]
    have := congrFun (congrFun (show N * Gw = (aS⁻¹).1 by rw [hN, Matrix.mul_assoc, hGG, Matrix.mul_one]) j) l
    rw [← this, Matrix.mul_apply]
    rfl
  have hT : ∀ i, (fun r => aT.1 r i) ∈ latAt w (frameLat T) := fun i => by
    have := (haT (Pi.single i 1)).1 fun m => by
      by_cases e : m = i
      · subst e; simp
      · simp [e]
    convert this using 1
    funext r
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdec : uPt hw h (ι a₀) aS aT x = ∑ i, ∑ j, (Matrix.of fun r l => secW hw h (x i j * ι a₀ * aT.1 r i *
      ∑ m, c (c (N j m)) * ι (S.gram m l)) : WO S T) := by
    ext r l
    simp only [uPt, Matrix.map_apply, Matrix.sum_apply, Matrix.of_apply, hcol]
    rw [show ∀ f : Fin T.rank → Fin S.rank → w.adicCompletion D.host.E, ∑ i, ∑ j, secW hw h (f i j) =
        secW hw h (∑ i, ∑ j, f i j) from fun f => by simp only [map_sum]]
    congr 1
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hdec]
  exact sum_mem fun i _ => sum_mem fun j _ => secW_span_mem hw h hc ha₀ (hT i) (hY j) (x i j) (hx i j)

end GlobalTheory.InertFrameLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEvenStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_unitary_coset_symmetry_hecke_even : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ n : ℕ, IsCommensurated (KU σ n) ∧ CosetSym (KU σ n) ∧ ∀ φ ∈ Hecke ℂ (KU σ n), ∀ g, φ g⁻¹ = φ g := by
  first | exact @GlobalTheory.ChainOnto.inert_cosetSym_heckeEven | exact GlobalTheory.ChainOnto.inert_cosetSym_heckeEven | (intros; apply GlobalTheory.ChainOnto.inert_cosetSym_heckeEven <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralGLCommensuratedDoubleCosetCardInvSymmStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_GL_commensurated_doubleCosetCardInvSymm : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), IsCommensurated (KGL w n) ∧ CosetSym (KGL w n) := by
  first | exact @GlobalTheory.ChainOnto.kGL_commensurated_cosetSym | exact GlobalTheory.ChainOnto.kGL_commensurated_cosetSym | (intros; apply GlobalTheory.ChainOnto.kGL_commensurated_cosetSym <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralHeisenbergInvariantFormsProportionalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_heisenberg_invariant_forms_proportional : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ l e : M →ₗ[ℂ] ℂ, (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, l (ρ u m) = l m) → (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, e (ρ u m) = e m) → ∀ m, e m * l s = l m * e s := by
  first | exact @GlobalTheory.ChainOnto.heisInv_forms_proportional | exact GlobalTheory.ChainOnto.heisInv_forms_proportional | (intros; apply GlobalTheory.ChainOnto.heisInv_forms_proportional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralNormSqMatrixCoefficientNeZeroDefiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_normSq_matrix_coefficient_ne_zero_definite : ∀ (D : D7) (V : HSp D), V.SigOK → V.IsPosDef → ∀ (c : CoefA V), c.Is → ∀ w : c.W, w ≠ 0 → ∀ mR : Measure (GinfC V), mR.IsHaarMeasure → ∫ b : GinfC V, ‖⟪w, c.ρ (b : GA D V) w⟫_ℂ‖ ^ 2 ∂mR ≠ 0 := by
  first | exact @GlobalTheory.integral_normSq_coef_ne_zero | exact GlobalTheory.integral_normSq_coef_ne_zero | (intros; apply GlobalTheory.integral_normSq_coef_ne_zero <;> assumption)
end

