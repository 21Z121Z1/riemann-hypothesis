import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3081
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0008
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3083
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3089
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3118
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3078
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0005
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3131

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringMinGenusBound
section
section
set_option synthInstance.maxHeartbeats 400000
open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.LevDesc
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
namespace GlobalTheory.CovGminTop
section Abstract
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end Abstract
section Point
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
theorem covering_min_genus_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Gram → DeepGood → Size → Gmin := by
  intro hP hGr hDG hS
  obtain ⟨C, hC, hg⟩ := _root_.GlobalTheory.T.exists_good_cover_at_minimal_level hP
  refine Closed.imp (((GlobalTheory.T.weight_parameter_strict_antitone hS).and (GlobalTheory.T.size_bounds_for_family hS)).and ((_root_.GlobalTheory.T.type_lattice_deep_level_eq hP hGr hDG).and hDG)) ?_
  rintro eps Fm CH - ⟨⟨⟨_, -, h1⟩, _, -, h2⟩, ⟨_, -, h3⟩, _, -, h4⟩
  obtain ⟨x1, h5⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (C + 45)
  obtain ⟨x0, h⟩ := (h1.and h2).and (h3.and h4)
  refine ⟨0, le_rfl, max x0 x1, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := h x hx ((le_max_left _ _).trans hle) ι p hp
  obtain ⟨b1, b2, b3, -⟩ := a1 i hi
  obtain ⟨c1, c2, c3, c4, c5, c6, -, -, c7, c8, -, c9, c10, -⟩ := a2 i hi Y hY
  obtain ⟨fr, ψ, -, d1, d2, d3⟩ := a3 i hi Y hY
  have hL := (h5 x ((le_max_right _ _).trans hle) ι).2.2.1
  have hn : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 4 ≤ (p.κ i).n := by
    rw [WtShape.cols_eq]; exact (Fm.parT x hx ι).nV_ge
  obtain ⟨s, e1, e2, e3⟩ := hg _ p.T c1 _ b1 b2 b3 c2 Y _ _ hY.1 _ c3 c4 c5 c6 le_rfl (wtA (p.κ i)) (p.κ i).n
    (dom_wtA _) (p.κ i).n_even hn (half_lt_laOf p i) (c9.trans (by linarith))
  obtain ⟨k1, k2⟩ := GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm _ p.T c1 _ b1 b2 b3 c2 Y _ _ hY.1 (Gk p i)
    ((Int.even_coe_nat _).2 (p.κ i).n_even)
  refine gminAt_of_gens p i Y (by omega) d1.coprime k1 k2 (a4 i hi Y hY).1 _ _ d2 s e1 e2 _ _ (fun y hy σ => (e3 y hy σ).1)
    (num_step hC (hL.trans ?_) (one_le_kap p i b1) c10 d3)
  have f1 : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.f)
  have f2 : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r)
  exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le f1 f2)
end GlobalTheory.CovGminTop
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_min_genus_eq : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Gram → DeepGood → Size → Gmin := by
  first | exact @_root_.GlobalTheory.CovGminTop.covering_min_genus_bound | exact _root_.GlobalTheory.CovGminTop.covering_min_genus_bound | (intros; apply _root_.GlobalTheory.CovGminTop.covering_min_genus_bound <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.EquivariantLinearizationPullbackCompat
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EqvAct
theorem equivariant_linearization_pullback : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → FnAlgClosed Xo c → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ, UnipAt I (ι γ)) → ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) → ∃ (G' : Over X') (_ : GrpObj G') (ψ : G'.left ⟶ TF.Y.t.G.left) (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)), GlobalTheory.HodgeLin.EqvLin TF.Y.t (φ ≫ (barComp TF.Y Z).ι) ρ' G' ψ act' m := by
  intro hP E _ _ _ H Dw l Xo c TF Z hpq hA hF I g hI hMb Γ _ _ ι ρ hU hAct X' _ φ ℓ ρ' hN hPr hO hj heq
  obtain ⟨m, hm, hmv⟩ := _root_.GlobalTheory.T.equivariant_action_eq_of_agree_on_generators hP E H Dw l Xo c TF Z hpq hA Γ ι ρ hAct X' φ ℓ ρ' hN hPr hO hj heq
  have hT := GlobalTheory.T.torsion_fibre_injects_levelModule E H Dw l Xo c TF Z hpq hA I g hI hMb Γ ι ρ hAct X' φ ℓ ρ' hN hPr hO hj heq m hm hmv
  exact ⟨pullG TF Z φ, inferInstance, pullψ TF Z φ, pullAct TF Z φ, m,
    isGrpPullback_pullψ TF Z φ, pullAct_pullψ TF Z φ, hm.1, hm.2.1, hm.2.2,
    GlobalTheory.T.fibre_action_trivial_of_fixed_point_residue_field E H Dw l Xo c TF Z hpq hA I g hI hMb Γ ι hU X' φ ρ' hN hPr m hm hT⟩
end GlobalTheory.EqvAct
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_linearization_pullback_compat : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → FnAlgClosed Xo c → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ, UnipAt I (ι γ)) → ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) → ∃ (G' : Over X') (_ : GrpObj G') (ψ : G'.left ⟶ TF.Y.t.G.left) (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)), GlobalTheory.HodgeLin.EqvLin TF.Y.t (φ ≫ (barComp TF.Y Z).ι) ρ' G' ψ act' m := by
  first | exact @_root_.GlobalTheory.EqvAct.equivariant_linearization_pullback | exact _root_.GlobalTheory.EqvAct.equivariant_linearization_pullback | (intros; apply _root_.GlobalTheory.EqvAct.equivariant_linearization_pullback <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsConstantCechKodairaSpencerValue
section
section
set_option autoImplicit false
noncomputable section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace
namespace GlobalTheory.CechKS
end GlobalTheory.CechKS
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
theorem GlobalTheory.CechKS.exists_constant_cech_kodaira_spencer_value : _root_.GlobalTheory.CovTop.Hypotheses'' → ∃ s : ℚ, s ≠ 0 ∧ ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A), GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A L ψ → ∀ (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → GlobalTheory.CechKS.IsCechKS A A' i L u θ → ∀ (hb : Fin n → GlobalTheory.DeRham.HdR A), (∀ b, GlobalTheory.DeRham.IsLieImage (hb b) (u b)) → ∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w : epsR K ⟶ A, IsLieComb (fun a => (s : K) * ∑ b, θ a b * ψ f (hb b)) u w → GlobalTheory.DeRham.IsKSValue h f w := by
  intro P
  refine ⟨1, one_ne_zero, ?_⟩
  intro K _ _ A _ A' _ i h g hA hg hA' hg' L hL ψ hψ n u θ hu H hb hhb f hf w hw
  obtain ⟨u', hu', rfl⟩ := hw
  have := GlobalTheory.CechKS.isKSValue_of_isCechKS P.p5 h hA hg hA' hg' L hL ψ hψ u θ hu H hb hhb hf
  convert this using 1
  rw [GlobalTheory.FlagTan.lieComb]
  congr 2
  funext a
  refine Over.OverMorphism.ext ((hu' a).trans ?_)
  simp only [Rat.cast_one, one_mul]
  rfl
end
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_kodaira_spencer_class_constant : _root_.GlobalTheory.CovTop.Hypotheses'' → ∃ s : ℚ, s ≠ 0 ∧ ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A), GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A L ψ → ∀ (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → GlobalTheory.CechKS.IsCechKS A A' i L u θ → ∀ (hb : Fin n → GlobalTheory.DeRham.HdR A), (∀ b, GlobalTheory.DeRham.IsLieImage (hb b) (u b)) → ∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w : epsR K ⟶ A, IsLieComb (fun a => (s : K) * ∑ b, θ a b * ψ f (hb b)) u w → GlobalTheory.DeRham.IsKSValue h f w := by
  first | exact @_root_.GlobalTheory.CechKS.exists_constant_cech_kodaira_spencer_value | exact _root_.GlobalTheory.CechKS.exists_constant_cech_kodaira_spencer_value | (intros; apply _root_.GlobalTheory.CechKS.exists_constant_cech_kodaira_spencer_value <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsThetaRuleValueLeCoverCharZero
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.JetsCharZero
theorem exists_theta_rule_value_le_cover_char_zero : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → letI := p.T.Q.H.starRing; ∀ (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (C : IntegralChartA3 Y.d.Xo₂ Y.d.c₂ T io y') (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G) (φT : ℝ), CharZero (IsLocalRing.ResidueField T.V) → Formalism.MainNotions.ModuliIntegralCharts.H1.FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → P.TorsionIso → GlobalTheory.SlopeRec.HasPhi y' φT → ∃ f ∈ thGen Y.d.Xo₂ Y.d.c₂ nab (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i)), evI y' f ≠ 0 ∧ (vV T.V (evI y' f) : ℝ) ≤ cst * φT := by
  intro h1 h2 h3 h4
  have hA := _root_.GlobalTheory.T.divisor_half_generation_of_cover h1 h2 h3 h4
  have hG := GlobalTheory.LiftGaps.lift_gaps h3
  unfold Covers Lifts Formalism.MainNotions.Closed at hA hG ⊢
  obtain ⟨ε1, hε1, hA⟩ := hA
  obtain ⟨ε2, hε2, hG⟩ := hG
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := hA eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := hG eps he (hle.trans (min_le_right _ _))
  refine ⟨⟨max K1.pre K2.pre, fun l => max (K1.t l) (K2.t l), fun l => max (K1.mid l) (K2.mid l),
    fun l => max (K1.last l) (K2.last l)⟩, fun Fm CH hF hL => ?_⟩
  have hL1 : Fm.Large K1 CH := ⟨fun c hc => (le_max_left _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_left _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_left _ _).trans (hL.2.2.2 c hc)⟩
  have hL2 : Fm.Large K2 CH := ⟨fun c hc => (le_max_right _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_right _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_right _ _).trans (hL.2.2.2 c hc)⟩
  obtain ⟨C1, hC1, hE1⟩ := hK1 Fm CH hF hL1
  obtain ⟨C2, -, hE2⟩ := hK2 Fm CH hF hL2
  refine ⟨C1, hC1, ?_⟩
  obtain ⟨x1, hx1⟩ := hE1.and hE2
  refine ⟨x1, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hAi, hGi⟩ := hx1 x hx hle ι p hp
  obtain ⟨α, hα, hdvd, hMb, hρq⟩ := hAi i hi Y hY
  obtain ⟨hp1, hgap⟩ := hGi i hi Y hY
  intro la hla cst hJ nab hnab T io y' C P φT hch hTr hP hφ
  obtain ⟨hanti, hgp⟩ := hgap la hla
  have hbd : ∀ (τ : AllWt.Psi p.T.Q.H) (k : Fin ((dat p i).p + (dat p i).q)),
      |((la τ k : ℤ) : ℝ)| ≤ ∑ τ' : AllWt.Psi p.T.Q.H, ∑ k' : Fin ((dat p i).p + (dat p i).q), |((la τ' k' : ℤ) : ℝ)| :=
    fun τ k => (Finset.single_le_sum (f := fun k' => |((la τ k' : ℤ) : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)).trans (Finset.single_le_sum (f := fun τ' => ∑ k' : Fin ((dat p i).p + (dat p i).q),
        |((la τ' k' : ℤ) : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  have hEven : Even (GlobalTheory.RefSum.nCol (dat p i)) := by
    unfold GlobalTheory.RefSum.nCol
    exact ⟨4 * ((∑ f : Lt1 (dat p i), 2 * rk f) / 8 + Fintype.card (Lt1 (dat p i)) + 1), by ring⟩
  have hn1 : 1 ≤ GlobalTheory.RefSum.nCol (dat p i) := by unfold GlobalTheory.RefSum.nCol; omega
  obtain ⟨hDom, -⟩ := GlobalTheory.RefSum.thA_dominant_lastPos_degree _ _ (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)) _ hp1 hEven
    hanti hgp hbd
  have hg0 : 2 ≤ (Fm.D x ι).host.g 0 := ((Fm.D x ι).host.g_prime 0).two_le
  have hg1 : 2 ≤ (Fm.D x ι).host.g 1 := ((Fm.D x ι).host.g_prime 1).two_le
  obtain ⟨j1, j2, j3⟩ := hJ 0
  have hle0 : (Fm.D x ι).host.g 0 ≤ (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 := Nat.le_mul_of_pos_right _ (by omega)
  have hle0' : ((Fm.D x ι).host.g 0 : ℝ) ≤ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) := by exact_mod_cast hle0
  have hg0' : (0 : ℝ) < (Fm.D x ι).host.g 0 := by exact_mod_cast (show 0 < (Fm.D x ι).host.g 0 by omega)
  have hN0 : (0 : ℝ) ≤ 2 * ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.m := by positivity
  have hR0 : 0 ≤ GlobalTheory.PtTie.rr0 (Fm.D x ι) := by unfold GlobalTheory.PtTie.rr0; positivity
  exact exists_thRule_value_le _ _ _ _ Y.d.Xo₂ Y.d.c₂ nab hnab T io y' C hTr P hP hch φT hφ α _ hα hdvd hMb _ _ hDom.1
    GlobalTheory.RefSum.sum_le_nCol hn1 (2 * ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.m) cst (by exact_mod_cast hρq) (j1.trans hle0)
    (lt_of_lt_of_le j2 hle0') (num_le _ _ _ _ _ _ _ hR0 hN0 (Nat.cast_nonneg _) hg0' hle0' j3)
end GlobalTheory.JetsCharZero
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
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_jet_value_bound_char_zero : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → letI := p.T.Q.H.starRing; ∀ (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (C : IntegralChartA3 Y.d.Xo₂ Y.d.c₂ T io y') (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G) (φT : ℝ), CharZero (IsLocalRing.ResidueField T.V) → Formalism.MainNotions.ModuliIntegralCharts.H1.FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → P.TorsionIso → GlobalTheory.SlopeRec.HasPhi y' φT → ∃ f ∈ thGen Y.d.Xo₂ Y.d.c₂ nab (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i)), evI y' f ≠ 0 ∧ (vV T.V (evI y' f) : ℝ) ≤ cst * φT := by
  first | exact @_root_.GlobalTheory.JetsCharZero.exists_theta_rule_value_le_cover_char_zero | exact _root_.GlobalTheory.JetsCharZero.exists_theta_rule_value_le_cover_char_zero | (intros; apply _root_.GlobalTheory.JetsCharZero.exists_theta_rule_value_le_cover_char_zero <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsWeightIsAmpleLineBundleComp
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RelAmpleComp
open GlobalTheory.FlagMod (FlagCover FlagModel)
theorem exists_weight_isAmple_lineBundle_comp : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∃ ρ : AllWt.Weight Dw, ∀ A : LB TF.Y.X, A.IsLB → IsAmpleLB A → ∃ n : ℕ, IsAmpleLB (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)) := by
  intro _ _ E _ _ _ H Dw l Xo c TF Z hF
  refine ⟨fun _ k => if (k : ℕ) < Dw.p then ((k : ℕ) : ℤ) - Dw.p else ((k : ℕ) : ℤ) - Dw.p + 1, ?_⟩
  intro A hA hAmp
  set ρ : AllWt.Weight Dw := fun _ k => if (k : ℕ) < Dw.p then ((k : ℕ) : ℤ) - Dw.p else ((k : ℕ) : ℤ) - Dw.p + 1 with hρ
  let e : Ix Dw → ℤ := fun ix => ix.elim 0 fun p => (Dw.mult p.1 : ℤ) - ((p.2 : ℕ) : ℤ)
  have hex : AllWt.exOf Dw ρ 0 = -e := by
    refine GlobalTheory.FlagMod.exOf_ext rfl (fun τ i hi => ?_) (fun τ i hi => ?_)
    · have hm := GlobalTheory.FlagMod.mult_of_mem (Dw := Dw) τ
      have h2 := i.2
      simp only [hρ, e, Pi.neg_apply, Option.elim]
      rw [if_pos (by omega)]
      omega
    · have hm := GlobalTheory.FlagMod.mult_conj (Dw := Dw) τ
      have h2 := i.2
      simp only [hρ, e, Pi.neg_apply, Option.elim]
      rw [if_neg (by omega)]
      push_cast
      omega
  have : IsProper TF.Y.s := projProper _ _ _ TF.Y.proj
  have : CompactSpace TF.Y.X := QuasiCompact.compactSpace_of_compactSpace TF.Y.s
  have : IsProper TF.X.π := TF.X.proper
  have : CompactSpace TF.X.YY := QuasiCompact.compactSpace_of_compactSpace TF.X.π
  have : QuasiSeparatedSpace TF.X.YY := quasiSeparatedSpace_of_quasiSeparated (TF.X.π ≫ TF.Y.s)
  obtain ⟨-, hPj, -⟩ := GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF
  have : IsProper (str₀ TF.X Z) := GlobalTheory.CommonModel.isProper_of_isProjOver hPj
  have : CompactSpace (Y₀ TF.X Z) := QuasiCompact.compactSpace_of_compactSpace (str₀ TF.X Z)
  have hN : (TF.X.F.LL (AllWt.exOf Dw ρ 0)).IsLB := TF.X.F.isLB_LL _
  have hM : (TF.X.F.LL e).IsLB := TF.X.F.isLB_LL _
  have hsum := GlobalTheory.HSApp.cls_common_add (commonLL TF.X) e (AllWt.exOf Dw ρ 0)
  have h0 := GlobalTheory.HSApp.cls_common_add (commonLL TF.X) (0 : Ix Dw → ℤ) 0
  simp only [add_zero] at h0
  have h3 : e + AllWt.exOf Dw ρ 0 = 0 := by rw [hex]; exact add_neg_cancel e
  rw [h3] at hsum
  have hcls : GlobalTheory.CechPic.cls (TF.X.F.LL e) hM = -GlobalTheory.CechPic.cls (TF.X.F.LL (AllWt.exOf Dw ρ 0)) hN := by
    refine eq_neg_of_add_eq_zero_left ?_
    have h4 : GlobalTheory.CechPic.cls (TF.X.F.LL 0) ((commonLL TF.X).isLB 0) = 0 := by
      have := congrArg (· - GlobalTheory.CechPic.cls (TF.X.F.LL 0) ((commonLL TF.X).isLB 0)) h0
      simpa using this.symm
    exact hsum.symm.trans h4
  obtain ⟨n₀, hn⟩ := GlobalTheory.T.isAmple_pullbackPower_div_of_locally_ample TF.X.π A hAmp (TF.X.F.LL (AllWt.exOf Dw ρ 0)) (TF.X.F.LL e) hN hM hcls
    (fun z => GlobalTheory.T.borelWeil_flagModel_detInverse_isAmple_local TF.flag z)
  have h := (hn n₀ le_rfl).pull_of_isOpenImmersion (inc₀ TF.X Z)
  have hAπ := LB.isLB_pull hA TF.X.π
  have hAg := LB.isLB_pull hA (inc₀ TF.X Z ≫ TF.X.π)
  have hP1 := isLB_lbPow hAπ n₀
  have hP2 := isLB_lbPow hAg n₀
  have hD1 := LB.isLB_div hP1 hN
  have hL0 : (L₀ TF.X Z ρ).IsLB := LB.isLB_pull hN _
  have hD2 := LB.isLB_div hP2 hL0
  refine ⟨n₀, IsAmpleLB.of_lbIso h hD2 ((GlobalTheory.CechPic.cls_eq_iff hD2 (LB.isLB_pull hD1 _)).1 ?_)⟩
  rw [GlobalTheory.CechPic.cls_div hP2 hL0, GlobalTheory.CechPic.cls_lbPow hAg, GlobalTheory.CechPic.cls_pull hA _ hAg,
    GlobalTheory.CechPic.cls_pull hD1 _ _, GlobalTheory.CechPic.cls_div hP1 hN hD1, GlobalTheory.CechPic.cls_lbPow hAπ,
    GlobalTheory.CechPic.cls_pull hA _ hAπ, GlobalTheory.CechPic.pull_comp, map_sub, map_nsmul]
  congr 1
end GlobalTheory.RelAmpleComp
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativelyAmple_comp_of_exists_weight : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∃ ρ : AllWt.Weight Dw, ∀ A : LB TF.Y.X, A.IsLB → IsAmpleLB A → ∃ n : ℕ, IsAmpleLB (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)) := by
  first | exact @_root_.GlobalTheory.RelAmpleComp.exists_weight_isAmple_lineBundle_comp | exact _root_.GlobalTheory.RelAmpleComp.exists_weight_isAmple_lineBundle_comp | (intros; apply _root_.GlobalTheory.RelAmpleComp.exists_weight_isAmple_lineBundle_comp <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IsNefHodgeBundleHeadWeight
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefHodge
section Step
open GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM)
open GlobalTheory.QCoh (pullbackSections)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z C : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (g : C ⟶ Z) (σ : E →+* ℂ)
  (f : ∀ M : MChart Y, Fin M.n → Γ(Lie Y.t.G, M.U))
end Step
theorem isNef_hodgeBundle_headWeight : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (τ : Psi H) (k : ℕ), k < Dw.p → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.headWt τ k)) := by
  intro hS _ hN E _ _ _ H Dw l Xo c TF Z _ τ k hk
  rw [NefStep.L₀_headWt TF.X Z τ k hk]
  exact isNef_stepEx hS hN.1 TF.X Z τ.1 (by rw [FlagMod.mult_of_mem τ]; exact hk)
end GlobalTheory.NefHodge
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundle_headWeight_nef : GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (τ : Psi H) (k : ℕ), k < Dw.p → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.headWt τ k)) := by
  first | exact @_root_.GlobalTheory.NefHodge.isNef_hodgeBundle_headWeight | exact _root_.GlobalTheory.NefHodge.isNef_hodgeBundle_headWeight | (intros; apply _root_.GlobalTheory.NefHodge.isNef_hodgeBundle_headWeight <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KodairaSpencerIsoFlagTangentPsiSet
section
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
namespace GlobalTheory.FlagTan
theorem kodaira_spencer_iso_flag_tangent_psi_set : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y hpq
  obtain ⟨X, h1, h2, hks⟩ := _root_.GlobalTheory.T.kodaira_spencer_universal_family hP hG E H Dw l Xo c K y hpq
  refine ⟨X, h1, h2, fun x' hx => ?_⟩
  have key : ∀ M, IsKS (psiSet H) y x' M ↔ x' = spMap (dir c M).toRingHom ≫ X := fun M =>
    ⟨fun k => _root_.GlobalTheory.T.flag_deformations_eq_of_kodaira_spencer_eq hP hG E H Dw l Xo c K y _ _ M hpq hx (isTanX_dir y X h1 h2 M) k (hks M),
      fun e => e ▸ hks M⟩
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.T.exists_kodaira_spencer_flag_tangent hP E H Dw l Xo c K y x' hpq hx
  exact ⟨⟨M, (key M).1 hM, fun M' e => _root_.GlobalTheory.T.flag_tangent_kodaira_spencer_unique hP E H Dw l Xo c K y x' hpq hx M' M ((key M').2 e) hM⟩, key⟩
end GlobalTheory.FlagTan
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_tangent_kodaira_spencer_iso : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y := by
  first | exact @_root_.GlobalTheory.FlagTan.kodaira_spencer_iso_flag_tangent_psi_set | exact _root_.GlobalTheory.FlagTan.kodaira_spencer_iso_flag_tangent_psi_set | (intros; apply _root_.GlobalTheory.FlagTan.kodaira_spencer_iso_flag_tangent_psi_set <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RingOfCoveringDescent
section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.RingStep
set_option maxHeartbeats 1000000 in
theorem ring_of_covering_descent (_hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hG : Gram) (hD : DeepGood) : Ring := by
  have hH := GlobalTheory.CovTop.Sizes.hostN 4
  refine Closed.imp ((hG.and hD).and hH) fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C1, -, h1⟩, ⟨C2, -, h2⟩⟩, ⟨A, -, h3⟩⟩ := h
  refine ⟨0, le_rfl, ?_⟩
  obtain ⟨x0, hx⟩ := (h1.and h2).and h3
  refine ⟨x0, fun x hx' hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨g1, g2⟩, g3⟩ := hx x hx' hle ι p hp
  have gram := g1 i
  have deep := g2 i hi Y hY
  have host := g3 i
  have hB := GlobalTheory.T.cuspFormLattice_slope_sq_goodCover_le_core _ p.T ((i : ℕ) + 1) Y _ _ (wtA (p.κ i)) (p.κ i).n (typeK p.fw p.F.lv2 i) p.fw.laws
    ⟨Nat.succ_pos _, i.2⟩ hY.1 (dom_wtA _) (fun f hf => hf.1) gram.2.2.2 deep.1
  have hrd := (log_rd_le_fieldSz Y.d.c₂.F).trans hY.1.size
  obtain ⟨⟨-, hL10, hLx, -⟩, -, -, -, -, -, -, -, -, hpp, ⟨hA1, hPPx, -⟩, hroom, -⟩ := host
  have hb : 391 * zBase (Fm.L x ι) ^ 2 ≤ (Fm.L x ι).sc.b := by
    have hm1 := (Fm.D x ι).R.two_le_m
    have hm2 := (Fm.D x ι).R.m_add_three_le_k
    have hf : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by have := (Fm.D x ι).R.toFrame.ord_pos; show 1 ≤ 2 * (Fm.D x ι).R.toFrame.ord; omega : 1 ≤ (Fm.D x ι).R.f)
    have hr : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ (Fm.D x ι).R.r)
    have hZ : 1 ≤ zBase (Fm.L x ι) := by
      unfold zBase
      have : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
      nlinarith
    have hX : (Fm.L x ι).sc.x ≤ (Fm.L x ι).sc.x ^ A := by
      calc (Fm.L x ι).sc.x = (Fm.L x ι).sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (Fm.L x ι).sc.x ^ A := Real.rpow_le_rpow_of_exponent_le (by linarith) hA1
    have hX4 : ((Fm.L x ι).sc.x ^ A) ^ (4 : ℝ) = ((Fm.L x ι).sc.x ^ A) ^ (4 : ℕ) := by
      exact_mod_cast Real.rpow_natCast ((Fm.L x ι).sc.x ^ A) 4
    have hZ2 : zBase (Fm.L x ι) ^ 2 ≤ zBase (Fm.L x ι) ^ 12 := pow_le_pow_right₀ hZ (by norm_num)
    have h1 : zBase (Fm.L x ι) ^ 2 ≤ (Fm.L x ι).sc.x ^ A := hZ2.trans (hpp.trans hPPx)
    generalize (Fm.L x ι).sc.x ^ A = X at *
    have hX10 : (10 : ℝ) ≤ X := (hL10.trans hLx).trans hX
    have h3 : (100 : ℝ) ≤ X * X := by nlinarith
    have h4 : (1000 : ℝ) ≤ X * X * X := by nlinarith
    have h2 : 391 * X ≤ X ^ 4 := by nlinarith
    rw [hX4] at hroom
    linarith
  show slope_sq _ (latDeep p i Y) - 2 * (Fm.L x ι).sc.b ≤ muCore p i
  have h2r : 2 * (Real.log |(discr Y.d.c₂.F : ℝ)| / Module.finrank ℚ Y.d.c₂.F) ≤ 2 * (Fm.L x ι).sc.b := by linarith
  exact le_trans (sub_le_sub_left h2r _) hB
end GlobalTheory.CovTop.RingStep
end

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_ring_descent : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Gram → DeepGood → Ring := by
  first | exact @_root_.GlobalTheory.CovTop.RingStep.ring_of_covering_descent | exact _root_.GlobalTheory.CovTop.RingStep.ring_of_covering_descent | (intros; apply _root_.GlobalTheory.CovTop.RingStep.ring_of_covering_descent <;> assumption)
end
end

