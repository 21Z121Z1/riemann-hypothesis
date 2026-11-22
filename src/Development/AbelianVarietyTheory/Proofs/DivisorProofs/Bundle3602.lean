import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3489
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2106
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3535
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3561
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0825
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0430
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0428

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamLocallyFreeHodgeDegenerates
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem abelianHodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham := by
  intro R _ A _ g hA hg
  obtain ⟨hfr, h0, -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hg
  obtain ⟨hO, hW, hB1, -⟩ := GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hg
  have hcl := GlobalTheory.T.abelianScheme_globalOneForms_closed R A g hA hg
  have hs := GlobalTheory.T.de_rham_to_structure_h1_surjective R A g hA hg
  have hH := (GlobalTheory.T.de_rham_h1_rank_primitive R A g hA hg).1
  refine ⟨⟨hH.1, hH.2.1, fun p ↦ (hH.2.2 p).trans (by push_cast; rfl)⟩,
    GlobalTheory.T.hyper_h2_exterior_square_iso R _ (OAff A.hom) hfr h0 hcl hs hW (GlobalTheory.T.cup_self_zero_de_rham_abelian R A g hA hg),
    GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hg, hO, ⟨hcl, ofForm_injective_of_H0Const R _ (OAff A.hom) h0, hs⟩, ?_⟩
  intro R' _ _ X' s' φ h
  obtain ⟨⟨e₁, he₁⟩, e₂, he₂⟩ := GlobalTheory.T.de_rham_global_forms_base_change R A g hA hg R' X' s' φ h
  obtain ⟨e₃, he₃⟩ := hB1 R' X' s' φ h
  refine ⟨⟨e₁, fun c ↦ ?_⟩, ⟨e₂, fun c ↦ ?_⟩, e₃, fun c ↦ ?_⟩
  · rw [he₁]; exact isPull1_pullHH1 h.w c
  · rw [he₂]; exact isPullForm_pullForm h.w c
  · rw [he₃]; exact isPullO_pullHO1 h.w c

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArCalcOfPrincipalisation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem GlobalTheory.MixHt.arCalc_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.ArCalc := fun h =>
  (GlobalTheory.T.arithIntersectionCalculus_cycleHeights_of_analytic (GlobalTheory.T.archLogNormChernIntegrable_of_principalisation h) (GlobalTheory.T.archLogNormReciprocity_of_principalisation h)).1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinomialFlagDimensionDegreeBound
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTop.DgShare

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem antitone_of_gapGe (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) {la : AllWt.Weight Dw} (h : GapGe 1 la) :
    (∀ τ, Antitone (la τ)) ∧ ∀ τ, 1 ≤ gap (la τ) (Dw.p - 1) := by
  refine ⟨fun τ => ?_, fun τ => h τ _ (by omega)⟩
  have key : ∀ (n : ℕ) (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + n → la τ b ≤ la τ a := by
    intro n
    induction n with
    | zero => intro a b e; rw [show b = a from Fin.ext e]
    | succ n ih =>
      intro a b e
      have hb := b.2
      have h1 := ih a ⟨a + n, by omega⟩ rfl
      have h2 := h τ (a + n) (by omega)
      rw [gap_eq (la τ) (i := ⟨a + n, by omega⟩) (j := b) e] at h2
      omega
  intro a b hab
  exact key (b - a) a b (by have : (a : ℕ) ≤ b := hab; omega)

theorem gapGe_of_wtBig {P : WtPar Dw} (h : WtBig P) : GapGe 1 P.u₁ ∧ GapGe 1 P.u₂ ∧ ∀ j, GapGe 1 (P.wt j) := by
  have h3 : GapGe 3 P.u₁ := h.gaps.mono (by
    have : 3 * 1 ≤ (FlagTan.dimFlag Dw + 3) * ((FlagTan.dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + FlagTan.dimFlag Dw + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    exact_mod_cast this)
  have h2 : ∀ τ k, k + 1 < Dw.p + Dw.q → 3 ≤ gap (P.u₂ τ) k := fun τ k hk => by
    have a := h3 τ k hk
    have b := (P.gap_rem τ k).1
    simp only [gap, dif_pos hk, WtPar.u₂, Pi.add_apply] at a b ⊢
    omega
  refine ⟨h3.mono (by norm_num), fun τ k hk => le_trans (by norm_num) (h2 τ k hk), fun j τ k hk => ?_⟩
  have a := h3 τ k hk
  have b := h2 τ k hk
  have c : -2 ≤ gap (FlagTan.kap Dw τ) k := by
    simp only [gap, dif_pos hk, FlagTan.kap]
    split_ifs <;> push_cast <;> omega
  simp only [gap, dif_pos hk, WtPar.wt, WtPar.uc, Pi.add_apply, Pi.smul_apply] at a b c ⊢
  simp only [nsmul_eq_mul]
  have e1 := mul_nonneg (Int.natCast_nonneg (FlagTan.dimFlag Dw)) (le_trans (by norm_num) a)
  have e2 := mul_nonneg (Int.natCast_nonneg j) (le_trans (by norm_num) a)
  nlinarith

end Weights

theorem lifts_and {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
    (_i : Fin (Fm.D x ι).R.m) (_PP _C : ℝ), Prop} (h : Lifts Q) (h' : Lifts Q') :
    Lifts fun Fm x hx ι p i PP _ => (∃ C, Q Fm x hx ι p i PP C) ∧ ∃ C, Q' Fm x hx ι p i PP C :=
  Closed.imp (Closed.and h h') fun _ _ _ ⟨⟨C, _, a⟩, C', _, b⟩ => ⟨0, le_rfl, (a.and b).imp fun _ h x hx hle ι p hp i =>
    ⟨⟨C, (h x hx hle ι p hp).1 i⟩, C', (h x hx hle ι p hp).2 i⟩⟩

theorem lower (hP : Hypotheses2) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hSi : GlobalTheory.Published.SiegelToroidalIntegral) (hFa : GlobalTheory.Published.ToroidalChartsForFan) (hSA : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : CoreJ D}
    (hT : LawsJ T) {j : ℕ} (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (hf : 2 < Module.finrank ℚ D.host.E / 2)
    (hj : InR D j) (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (P : WtPar (T.Q.Dw j)) (hB : WtBig P)
    (Z : Comp Y.d.Xo₂ Y.d.c₂) (hbir : BirOn Y.U Z (wtOf _ P.u₁ 0)) :
    (P.T - 1).choose (CompHt.dimFlag (T.Q.Dw j)) * CompHt.compDeg Y.U Z (wtOf _ P.u₁ 0) ≤
      Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf _ (P.wt P.T) 0)) := by
  have hP1 := GlobalTheory.T.stronger_published_hypotheses_imply hP
  obtain ⟨g1, g2, g3⟩ := gapGe_of_wtBig hB
  have good : ∀ la, GapGe 1 la → _ := fun la h =>
    GlobalTheory.T.good_weight_antitone_gap hP D T hT j hp hq hf hj Y e o hY la (antitone_of_gapGe hp hq h).1
      (antitone_of_gapGe hp hq h).2
  obtain ⟨TF, R, ω, h⟩ := GlobalTheory.T.deep_model_weight_section hP1 hG hQ hP.q15 hP.q16 hSi hFa hSA D T.toCore j Y e o hY hf Z P hB fun i _ => (good _ (g3 i)).1
  obtain ⟨f₁⟩ := nonempty_cuspFrame ((good _ g1).2 Z)
  obtain ⟨f₂⟩ := nonempty_cuspFrame ((good _ g2).2 Z)
  let k : CompHS.Consts := ⟨1, 1, 1, 1, 1, le_rfl, le_rfl, le_rfl⟩
  let th : R.L.Sec := GlobalTheory.CompHS.toSec (R.Δ₁.lift 0)
  obtain ⟨a1, a2⟩ := GlobalTheory.T.choice_free_section_construction hP1 hP.q7 hSi hFa hSA _ _ _ _ _ _ TF Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k hY.geo hB
  have a3 := birational_of_ratGen TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k
    (ratGen_of_birOn TF.X Z Y.U P.u₁ ⟨R.toModif⟩ hbir)
  exact GlobalTheory.HSCore.CompShare.choose_mul_compDeg_le hQ _ _ _ _ _ _ _ _ Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k a1 a2 a3

theorem choose_mul_compDeg_le : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg →
    Covers fun Fm x _ ι p i Y PP _ => ∀ Z, (lenT p i PP - 1).choose (GlobalTheory.CompHt.dimFlag (dat p i)) *
      GlobalTheory.CompHt.compDeg Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ :
        WtPar (dat p i)).u₁ 0) ≤
      Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2,
        lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) := by
  intro hX hP hG hQ hSi hKS hSA _ hS _
  have hFa := hKS.toroidalChartsForFan
  have h4 := GlobalTheory.T.size_bounds_for_family hS
  have h5 := GlobalTheory.T.birational_on_weight_parameters hX hG hQ hSi hP hS
  unfold Covers at h4 h5
  have all := lifts_and (lifts_and (GlobalTheory.T.weight_parameter_strict_antitone hS) wtBig_run) (lifts_and h4 h5)
  clear h4 h5
  refine Closed.imp all fun Fm _ _ ⟨C, hC, x0, h⟩ => ⟨C, hC, x0, fun x hx hle ι p hp i hi Y hY Z => ?_⟩
  obtain ⟨⟨_, ⟨_, hq⟩, _, hB⟩, _, ⟨_, hz⟩, _, hb⟩ := h x hx hle ι p hp i
  obtain ⟨hp1, hq1, hf, -⟩ := hq hi
  obtain ⟨hT, hj, -⟩ := hz hi Y hY
  exact lower hP hG hQ hSi hFa hSA hT hp1 hq1 hf hj Y hY.1 _ (hB hi) Z (hb hi Y hY Z).1

end GlobalTheory.CovTop.DgShare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalDataRigidAlongStratumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_data_rigid_along_stratum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), GlobalTheory.RigChart.IsRigid C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) := by
  first | exact @GlobalTheory.UCanon.isRigid_canon | exact GlobalTheory.UCanon.isRigid_canon | (intros; apply GlobalTheory.UCanon.isRigid_canon <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseInjectionsAgreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalFamily_base_injections_agree : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], GlobalTheory.Mum.Base R' → ∀ θ₁ θ₂ : R →+* R', Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK R = jK R' ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → θ₁.comp (Cn.ψ.comp MvPolynomial.C) = θ₂.comp (Cn.ψ.comp MvPolynomial.C) := by
  first | exact @GlobalTheory.UCanon.injBase | exact GlobalTheory.UCanon.injBase | (intros; apply GlobalTheory.UCanon.injBase <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleVerticalFieldsEqCoboundaryAddLogDeriv
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSCocycle

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.LogKSLin
open GlobalTheory.Points (valR_eq valR_add valR_mul valR_res valR_appLE le_preimage_mono)

theorem resG_resG' {Z : Scheme.{0}} {U V W : Z.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(Z, U)) :
    resG Z h' (resG Z h x) = resG Z (h'.trans h) x :=
  (congrArg (fun k => k.hom x) (Z.presheaf.map_comp (homOfLE h).op (homOfLE h').op)).symm

theorem exists_coboundary_add_dlog : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → (∀ i, W i ≤ t.PP.L.U (j i)) → ∀ (e : J → J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i i', IsField (W i ⊓ W i') (e i i')) → (∀ i i' (h : W i ⊓ W i' ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), e i i' (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') h).hom r) = 0) → (∀ i i' i'' (O : t.G.left.Opens), O ≤ W i ⊓ W i' ⊓ W i'' → ∀ f : Γ(t.G.left, O), e i i' O f + e i' i'' O f = e i i'' O f) → ∃ (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (h : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsField (W i) (h i)) ∧ (∀ i (hW : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), h i (W i) ((t.G.hom.appLE U.1 (W i) hW).hom r) = 0) ∧ ∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, IsTranslate t φ g₀ (v a) (w a)) → valR g₀ O (e i i' O f) = valR g₀ O (h i O f - h i' O f) + ∑ a, ∑ b, φ (Θ a b) * ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) * (valR (w a) O f).snd := by
  intro E _ _ _ H X t hP hA hK U n v hv hb J W j hWa hcov hj e he hev hcoc
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i => (le_iSup W i).trans hcov.le
  choose dd hdF hd0 hdv using fun a => exists_invField U (hv a)
  have hsp := fun i i' => GlobalTheory.T.verticalVectorField_unique_combination_basis E H X t U n v hv hb dd hdF hd0 hdv (W i ⊓ W i') (inf_le_left.trans (hWU i))
    (e i i') (he i i') (fun r => hev i i' _ r)
  choose c hc using fun i i' => (hsp i i').exists
  have hcc : ∀ a i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i' a) +
      resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
        (c i' i'' a) =
      resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'')
        (c i i'' a) := by
    intro a i i' i''
    have h1 : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i' := inf_le_left
    have h2 : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have h3 : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hT : W i ⊓ W i' ⊓ W i'' ≤ t.G.hom ⁻¹ᵁ U.1 := h3.trans (inf_le_left.trans (hWU i))
    have hu := (GlobalTheory.T.verticalVectorField_unique_combination_basis E H X t U n v hv hb dd hdF hd0 hdv (W i ⊓ W i' ⊓ W i'') hT (e i i'')
      (isField_mono h3 (he i i'')) (fun r => ?_)).unique
      (y₁ := fun a => resG _ h1 (c i i' a) + resG _ h2 (c i' i'' a)) (y₂ := fun a => resG _ h3 (c i i'' a)) ?_ ?_
    · exact congrFun hu a
    · rw [← resG_appLE U (inf_le_left.trans (hWU i)) h3 r, (he i i'').2.2 _ _ h3 le_rfl, hev, map_zero]
    · intro O hO f
      rw [← hcoc i i' i'' O hO f, hc i i' O (hO.trans h1) f, hc i' i'' O (hO.trans h2) f]
      simp only [map_add, resG_resG', add_mul, Finset.sum_add_distrib]
    · intro O hO f
      rw [hc i i'' O (hO.trans h3) f]
      simp only [resG_resG']
  choose θ hh hθ using fun a => GlobalTheory.T.cechCocycle_eq_coboundary_add_logDerivatives_affine E H X t hP hA hK U n v hv hb dd hdF hd0 hdv J W j hWa hcov hWU hj
    (fun i i' => c i i' a) (hcc a)
  refine ⟨Matrix.of fun a b => θ a b, fun i O f => ∑ a, smulFld (hh a i) (dd a) O f,
    fun i => isField_sum fun a => isField_smul _ (isField_mono (hWU i) (hdF a)), fun i hW r => ?_,
    fun i i' O hO f S _ φ g₀ w hg hgO hw => ?_⟩
  · simp only [smulFld_of_le le_rfl, hd0, mul_zero, Finset.sum_const_zero]
  · have hO1 : O ≤ W i := hO.trans inf_le_left
    have hO2 : O ≤ W i' := hO.trans inf_le_right
    have hPU : W i ⊓ W i' ≤ t.G.hom ⁻¹ᵁ U.1 := inf_le_left.trans (hWU i)
    have hgP : ⊤ ≤ g₀ ⁻¹ᵁ (W i ⊓ W i') := le_preimage_mono g₀ hO hgO
    have hred := fun a => translate_red (hv a) hg (hw a)
    have key : ∀ a, valR g₀ O (resG t.G.left hO (c i i' a) * dd a O f) =
        valR g₀ (W i) (hh a i) * (valR (w a) O f).snd - valR g₀ (W i') (hh a i') * (valR (w a) O f).snd +
          ∑ b, φ (θ a b) * ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd *
            valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) * (valR (w a) O f).snd := by
      intro a
      rw [valR_mul _ _ hgO, valR_res _ hO hgO, hdv a O (hO.trans hPU) f S φ g₀ (w a) hg hgO (hw a), hθ a i i',
        valR_add _ _ hgP, GlobalTheory.CechInv.valR_sub _ _ hgP, valR_res _ _ hgP, valR_res _ _ hgP, valR_eq _ _ hgP,
        map_sum, add_mul, sub_mul, Finset.sum_mul]
      refine congrArg (_ + ·) (Finset.sum_congr rfl fun b _ => ?_)
      rw [← valR_eq _ _ hgP, valR_mul _ _ hgP, valR_mul _ _ hgP, valR_base U _ hg hgP, valR_res _ _ hgP,
        hdv b _ hPU _ S φ g₀ (w b) hg hgP (hw b),
        valR_res _ _ (GlobalTheory.CechKS.le_preimage_of_red (hred b) hgP)]
    have hsm : ∀ k (hk : O ≤ W k), valR g₀ O (∑ a, smulFld (hh a k) (dd a) O f) =
        ∑ a, valR g₀ (W k) (hh a k) * (valR (w a) O f).snd := by
      intro k hk
      rw [valR_eq _ _ hgO, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← valR_eq _ _ hgO, smulFld_of_le hk, valR_mul _ _ hgO, valR_res _ hk hgO,
        hdv a O (hk.trans (hWU k)) f S φ g₀ (w a) hg hgO (hw a)]
    beta_reduce
    rw [hc i i' O hO f, GlobalTheory.CechInv.valR_sub _ _ hgO, hsm i hO1, hsm i' hO2, valR_eq _ _ hgO, map_sum]
    simp only [← valR_eq _ _ hgO, key, Matrix.of_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]

end GlobalTheory.KSCocycle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainFrameTripleHaarIdentity
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
open MeasureTheory
open scoped TensorProduct
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.DefiniteSmallIrred

theorem lieDeriv : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Ψ ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B,
  GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsDer θ X (fun h => ωB (1, h)) τ Y Ψ Φ' → ∀ h : GA D X,
  HasDerivAt (fun t : ℝ => GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ (h * oneP θ X τ Y t)) (GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' h) 0 := by
  intro hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm τ Y hY Ψ hΨ Φ' hΦ' hder h
  have hw : IsWeilDatumO ψ W₁ X α (α / β) ωB := (GlobalTheory.Grid.isWeil_false ψ W₁ X α (α / β) ωB).1 hm.weilB
  have hthA : ∀ Φ ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, IsThetaFunO ψ W₁ X Φ := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx
  have hth : IsThetaFunO ψ W₁ X Ψ := hthA Ψ hΨ
  have hpos : ∀ τ, (gramAt D W₁ τ).PosDef := fun τ => GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.posDef_of_hasSignature (hs₁ τ)
  obtain ⟨Gn, hGn⟩ := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ W₁ X α (α / β) ωB hw θ hθ τ Y hY
  have hGΨ : ∀ (g : GA D W₁) (k : GA D X),
      HasDerivAt (fun t : ℝ => thetaKO ωB g (k * oneP θ X τ Y t) Ψ) (thetaKO ωB g k Φ') 0 := by
    have hG : Gn Ψ = Φ' := by
      funext z
      have h1 := (hGn Ψ hth).2.2.2 1 z
      simp only [one_mul, map_one, Module.End.one_apply] at h1
      exact h1.unique (hder z)
    intro g k
    have h1 := (hGn Ψ hth).2.2.2 (g, k) 0
    simp only [Prod.mk_mul_mk, mul_one, hG] at h1
    exact h1
  let L : ℂ →ₗ[ℂ] (WO W₁ X → ℂ) := LinearMap.toSpanSingleton ℂ _ Ψ
  have hL : ∀ x, IsThetaFunO ψ W₁ X (L x) := fun x => GlobalTheory.OrientedHeis.theta_smul x hth
  have hL1 : L 1 = Ψ := by simp [L]
  obtain ⟨-, hD⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ W₁ X α (α / β) ωB hw θ hθ hpos ℂ L hL
    (fun _ => 1) continuous_const (fun _ _ _ => rfl) ν₁ 𝓕₁ hν₁.1 hν₁.2
  obtain ⟨L', -, hk, hlift⟩ := hD τ Y hY
  have hkid : ∀ g k, thetaKO ωB g k (L' 1) = thetaKO ωB g k Φ' := by
    intro g k
    have h1 := hk 1 g k
    rw [hL1] at h1
    exact h1.unique (hGΨ g k)
  have h2 := hlift h
  simp only [GlobalTheory.DefLift.lift, hL1, hkid] at h2
  exact h2

theorem vanish_all : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
  GlobalTheory.SquareComm.IsHaarFD W ν 𝓕 → GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, p' Φ' ≠ 0 → GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' = 0 →
  ∀ Φ'' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ'' = 0 := by
  intro hP hTK hLM D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm Φ₁ hΦ₁ hp₁ hz₁ Φ₂ hΦ₂
  have hTA : GlobalTheory.SquareSt.ThetaIntegralsAgree := GlobalTheory.T.theta_integrals_of_minguez hP.minguezThetaGL hP hTK hLM
  set S := GlobalTheory.SquareComm.algF ψ θ false A₁ B with hSdef
  have hint := GlobalTheory.DefIrred.integrable_algF hψ hθ A₁ B hm.weilB hs₁ hν₁
  have tr : ∀ (Φ : WO W₁ X → ℂ) (g : GA D W₁) (h k : GA D X), thetaKO ωB g h (ωB (1, k) Φ) = thetaKO ωB g (h * k) Φ := by
    intro Φ g h k
    show (ωB (g, h) * ωB (1, k)) Φ 0 = _
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
    rfl
  have tsub : ∀ Φ Ψ, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) →
      (∀ h, IntegrableOn (fun g => thetaKO ωB g h Ψ) 𝓕₁ ν₁) →
      GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ (Φ - Ψ) = GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ - GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ := by
    intro Φ Ψ hΦ hΨ; funext h
    have e : (fun g => thetaKO ωB g h (Φ - Ψ)) = fun g => thetaKO ωB g h Φ - thetaKO ωB g h Ψ := by
      funext g; simp [thetaKO, map_sub]
    simp only [GlobalTheory.SquareComm.thetaInt, Pi.sub_apply]
    rw [e]
    exact integral_sub (hΦ h) (hΨ h)
  have tadd : ∀ Φ Ψ, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) →
      (∀ h, IntegrableOn (fun g => thetaKO ωB g h Ψ) 𝓕₁ ν₁) →
      GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ (Φ + Ψ) = GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ + GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ := by
    intro Φ Ψ hΦ hΨ; funext h
    have e : (fun g => thetaKO ωB g h (Φ + Ψ)) = fun g => thetaKO ωB g h Φ + thetaKO ωB g h Ψ := by
      funext g; simp [thetaKO, map_add]
    simp only [GlobalTheory.SquareComm.thetaInt, Pi.add_apply]
    rw [e]
    exact integral_add (hΦ h) (hΨ h)
  have tsmul : ∀ (c : ℂ) Φ, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ (c • Φ) = c • GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ := by
    intro c Φ; funext h
    have e : (fun g => thetaKO ωB g h (c • Φ)) = fun g => c * thetaKO ωB g h Φ := by
      funext g; simp [thetaKO, map_smul]
    simp only [GlobalTheory.SquareComm.thetaInt, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact integral_const_mul c _
  let Kint : Submodule ℂ (WO W₁ X → ℂ) :=
    { carrier := {Φ | (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ) 𝓕₁ ν₁) ∧ GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ = 0}
      add_mem' := fun {a b} ha hb => ⟨fun h => by
          have e : (fun g => thetaKO ωB g h (a + b)) = fun g => thetaKO ωB g h a + thetaKO ωB g h b := by
            funext g; simp [thetaKO, map_add]
          rw [e]; exact (ha.1 h).add (hb.1 h),
        by rw [tadd a b ha.1 hb.1, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨fun h => by simp [thetaKO], by funext h; simp [GlobalTheory.SquareComm.thetaInt, thetaKO]⟩
      smul_mem' := fun c a ha => ⟨fun h => by
          have e : (fun g => thetaKO ωB g h (c • a)) = fun g => c * thetaKO ωB g h a := by
            funext g; simp [thetaKO, map_smul]
          rw [e]; exact (ha.1 h).const_mul c,
        by rw [tsmul, ha.2, smul_zero]⟩ }
  let K : Submodule ℂ (WO W₁ X → ℂ) := S ⊓ Kint
  obtain ⟨c, hc0, hc⟩ := hTA D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm
  have hrel := GlobalTheory.T.theta_integral_finite_relation hP D ψ θ hψ hθ W₁ X A₁ B α (α / β) ωB hm.weilB hs₁ ν₁ 𝓕₁ hν₁
  have kerp' : GlobalTheory.SquareComm.finRel ωB S ≤ LinearMap.ker p' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, Ψ, hΨ, rfl⟩
    simp [map_sub, hm.mapB.invf u hu Ψ hΨ]
  have kill : ∀ Ψ ∈ S, p' Ψ = 0 → GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ = 0 := by
    intro Ψ hΨ hp0
    obtain ⟨Φ₀, hΦ₀, hd, -, hI⟩ := hc Ψ hΨ
    have hp00 : p' Φ₀ = 0 := by
      have := kerp' hd
      rw [LinearMap.mem_ker, map_sub, hp0, zero_sub, neg_eq_zero] at this
      exact this
    have h1 := hI 0 (zero_mem _) (by rw [map_zero, hp00])
    have h2 : GlobalTheory.SquareComm.thetaInt ωA ν 𝓕 0 = 0 := by funext h; simp [GlobalTheory.SquareComm.thetaInt, thetaKO]
    rw [h2] at h1
    have h3 : GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ₀ = 0 := (smul_eq_zero.1 h1.symm).resolve_left hc0
    have h4 := hrel _ hd
    rw [tsub Ψ Φ₀ (hint Ψ hΨ) (hint Φ₀ hΦ₀), h3, sub_zero] at h4
    exact h4
  have stf : ∀ g ∈ GfC X, ∀ x ∈ K.map p', rf g x ∈ K.map p' := by
    rintro g hg _ ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, rfl⟩
    refine ⟨ωB (1, g) Ψ, ⟨hm.mapB.stabX.1 g hg Ψ hΨS, fun h => ?_, ?_⟩, hm.mapB.eqf g hg Ψ hΨS⟩
    · simp only [tr]; exact hΨi (h * g)
    · funext h
      simp only [GlobalTheory.SquareComm.thetaInt, tr]
      exact congrFun hΨ0 (h * g)
  have stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ K.map p', rl τ Y x ∈ K.map p' := by
    rintro τ Y hY _ ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, rfl⟩
    obtain ⟨Φ', hΦ'S, hder⟩ := hm.mapB.stabX.2 τ Y hY Ψ hΨS
    refine ⟨Φ', ⟨hΦ'S, hint Φ' hΦ'S, ?_⟩, hm.mapB.eql τ Y hY Ψ hΨS Φ' hΦ'S hder⟩
    funext h
    have hd := lieDeriv hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT hs₁ ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm τ Y hY Ψ hΨS Φ' hΦ'S hder h
    have e0 : (fun t : ℝ => GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Ψ (h * oneP θ X τ Y t)) = fun _ => (0 : ℂ) := by
      funext t; rw [hΨ0]; rfl
    rw [e0] at hd
    exact hd.unique (hasDerivAt_const 0 0)
  rcases hm.irred.2 (K.map p') stf stl with hbot | htop
  · exfalso
    have : p' Φ₁ ∈ K.map p' := ⟨Φ₁, ⟨hΦ₁, hint Φ₁ hΦ₁, hz₁⟩, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    exact hp₁ this
  · have : p' Φ₂ ∈ K.map p' := by rw [htop]; exact Submodule.mem_top
    obtain ⟨Ψ, ⟨hΨS, hΨi, hΨ0⟩, hΨp⟩ := this
    have h0 := kill (Φ₂ - Ψ) (S.sub_mem hΦ₂ hΨS) (by rw [map_sub, hΨp, sub_self])
    rw [tsub Φ₂ Ψ (hint Φ₂ hΦ₂) hΨi, hΨ0, sub_zero] at h0
    exact h0

end GlobalTheory.DefiniteSmallIrred
end
end

