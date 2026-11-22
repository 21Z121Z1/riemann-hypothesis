import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3359
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0185
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0118
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0088
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0115
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0120
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0166
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0154
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0111
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjBaseOfStepsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjBase_of_ray_class_field_and_seriesRat : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.ConjugateBase := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.conjBase_of_cusp_decay_and_reciprocity | exact _root_.GlobalTheory.BigOn.Exp.conjBase_of_cusp_decay_and_reciprocity | (intros; apply _root_.GlobalTheory.BigOn.Exp.conjBase_of_cusp_decay_and_reciprocity <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IntegralFramePointStalkCompat
section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlatValZero
section Gen
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.FlatCore GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
end Gen
end GlobalTheory.FlatValZero
open GlobalTheory.FlatValZero
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.FlatValZero.flat_val_zero_at_integral_point_stalk : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∀ w : AllWt.Psi p.T.Q.H → ℤ, ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) (GlobalTheory.FlatLine.parWt (dat p i) w) 0), vV T.V (evI y' t.sig) = 0 := by
  intro hP hD _ hF
  have F := _root_.GlobalTheory.CovTop.FlatVal.flat_val_alt hF
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine (hD.and F).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and e2
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY Z TF y T io y' g hg hpt hZ w => ?_⟩
  obtain ⟨-, hB⟩ := hx0 x hx hle ι p hp
  have hFE := (hB i hi Y hY).2.2.1
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.FlatValZero.twisted_section_flat_valuation hP hL hFE Z w
  refine ⟨t, ht T io y' (fun a ha => ?_) hZ⟩
  have ho : ∀ a, io a ∈ (algebraMap T.V T.Fr).range := fun a => by
    letI := io.toAlgebra
    have h1 := ptY_str TF.X y'.1
    rw [hpt, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc] at h1
    obtain ⟨b, hb⟩ := Spec.map_surjective
      (Spec.map (CommRingCat.ofHom g) ≫ ((Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) ≫ flagStr TF.X)
    rw [← hb, ← Spec.map_comp] at h1
    exact ⟨b.hom a, congrArg (fun q => CommRingCat.Hom.hom q a) (Spec.map_injective h1)⟩
  have ha' : io a ≠ 0 := (map_ne_zero io).2 ha
  have h1 := (GlobalTheory.KeyValZero.mem_range_iff T _).1 (ho a)
  have h2 := (GlobalTheory.KeyValZero.mem_range_iff T _).1 (ho a⁻¹)
  have h3 := vV_mul (V := T.V) ha' ((map_ne_zero io).2 (inv_ne_zero ha))
  rw [← map_mul, mul_inv_cancel₀ ha, map_one, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h3
  omega
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_frame_point_stalk_compat_third_place_series : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∀ w : AllWt.Psi p.T.Q.H → ℤ, ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) (GlobalTheory.FlatLine.parWt (dat p i) w) 0), vV T.V (evI y' t.sig) = 0 := by
  first | exact @_root_.GlobalTheory.FlatValZero.flat_val_zero_at_integral_point_stalk | exact _root_.GlobalTheory.FlatValZero.flat_val_zero_at_integral_point_stalk | (intros; apply _root_.GlobalTheory.FlatValZero.flat_val_zero_at_integral_point_stalk <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwOneOfSteps
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwConj
open GlobalTheory.ConjTwist
theorem normAt_alt : _root_.GlobalTheory.BigOn.Exp.TwConj.NormCondition := _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun _ _ _ _ p _ _ _ _ _ B ν ν' ⟨_, c, hc, n, hn, hνn⟩ ⟨_, c', hc', m, hm, hνm⟩ => by
  obtain ⟨k, hk, hkk⟩ := scale_pow_eq p.R p.v₀ B hc hc'
  refine ⟨n * m * k, Nat.mul_ne_zero (Nat.mul_ne_zero hn hm) hk, ?_⟩
  have e1 : ν' ^ (n * m * k) = (ν' ^ m) ^ (n * k) := by rw [← pow_mul]; ring_nf
  have e2 : ν ^ (n * m * k) = (ν ^ n) ^ (m * k) := by rw [← pow_mul]; ring_nf
  have e3 : c' ^ (n * m * k) = c ^ (n * m * k) := by
    rw [show n * m * k = k * (n * m) by ring, pow_mul c', pow_mul c, hkk]
  rw [e1, e2, hνm, hνn, ← pow_mul, ← pow_mul, mul_pow, mul_pow,
    show m * (n * k) = n * m * k by ring, show n * (m * k) = n * m * k by ring, e3]
theorem twOne_of_steps_alt (hA : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt) (hT : _root_.GlobalTheory.BigOn.Exp.TwConj.TupleCondition) (hF : _root_.GlobalTheory.BigOn.Exp.TwConj.FixedPointCondition) (hC : _root_.GlobalTheory.BigOn.Exp.TwConj.CoefficientCondition)
    (hE : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p _ j => ∀ τ : ℂ ≃+* ℂ,
      (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
      ∀ Φ Φ' : GA (Fm.D x i) (Wc (Fm.D x i) j) → ℂ, ConjFun (p.O j) (p.κ j) τ 1 Φ Φ' →
        ∃ (n : ℕ) (b : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
          Φ = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧ ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val = Φ') : _root_.GlobalTheory.BigOn.Exp.TwConj.TwistTrivialCondition := by
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA hT) (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hF (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hC hE))) fun Fm x hx i p hr hm w _ j H => ?_
  obtain ⟨⟨a1, a2⟩, a3, a4, a5⟩ := H
  intro ρ ρ' ν hρ hρ' hp hS hL hAd hN h₀ P hP h hh τ hτ hcc
  obtain ⟨c, u, ξ, hc, hu, hξ, K⟩ := a4 ρ ν hρ hp hN
  obtain ⟨y, hy, hyy⟩ := K h₀ P hP
  obtain ⟨f1, f2⟩ := a3 ρ hρ hp hL τ hτ
  obtain ⟨g1, g2, -⟩ := GlobalTheory.TwistGood.tw_good _ _ _ ρ hρ _ j ((Fm.ex x hx i).nch.sd w) _ _ _ a1.1
  obtain ⟨g3, -, -⟩ := GlobalTheory.TwistGood.tw_good _ _ _ ρ' hρ' _ j ((Fm.ex x hx i).nch.sd w) _ _ _ a1.1
  obtain ⟨ζ, hζ, hcf⟩ := conjFun_gen (Fm.parT x hx i).nV_ge (a2 ρ ρ' hρ hρ' hp hS hAd) (hρ.base _ _ _) (hρ.weil_base _ _ _) g1 g3 g2
    (hcc.1.symm ▸ g2) (root_delta hρ _ _ _) (root_charOf _ _ a1.1.2.2.1) hc hu f1 f2 hcc hh (hyy τ hτ)
  have hcf1 := (GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).2
    (GlobalTheory.ConjGen.cf_one_of (root_ne hζ) ((GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).1 hcf))
  obtain ⟨n, b, g, e1, e2⟩ := a5 τ hτ _ _ hcf1
  have hsm : ∀ ψ, ν • genW (Fm.ex x hx i) w j ρ ψ h P =
      ξ • phs p j • genW (Fm.ex x hx i) w j ρ ψ h (p.R.ioP j (PiTensorProduct.tprod ℂ u) (c y)) := fun ψ =>
    smul_apply_of _ hy
  exact ⟨_, root_mul (root_mul (root_map τ hξ) (root_inv hζ)) (root_inv hξ), n, fun l => ξ * b l, g,
    rescale τ (root_ne hξ) (hsm _) (hsm _) e1 e2⟩
theorem conj_tw_of_prints : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS →
    _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.ConjugateTwist := fun h1 h2 h3 hD hW h4 hA hC =>
  _root_.GlobalTheory.BigOn.Exp.TwConj.conjTw_of_twAdm_latSmallGen_normAt_twOne hA _root_.GlobalTheory.T.latSmallGen' _root_.GlobalTheory.BigOn.Exp.TwConj.normAt_alt (_root_.GlobalTheory.BigOn.Exp.TwConj.twOne_of_steps_alt hA (_root_.GlobalTheory.T.twisted_conj_tuple_at' h1 h2 h3 hD hW hA hC) (_root_.GlobalTheory.T.twisted_conj_fix_at' h3 hA) (_root_.GlobalTheory.T.twisted_conj_coef_at' hA)
    (_root_.GlobalTheory.T.conjTwist_function_eq_sum_evaluations_alt h1 h2 h3 h4))
end GlobalTheory.BigOn.Exp.TwConj
end
end
end

