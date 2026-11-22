import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0125
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductOfSectionsExpandsToConvolution
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelationStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crossRelation_gives_convolution_relation : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (E : EndU U.toUnifPre) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (j j' : ℕ), 1 ≤ j → 1 ≤ j' → ∀ (t₁ t₂ : SecA A F j) (t₁' t₂' : SecA A F j') s₁ s₂ s₁' s₂', U.ExpandsF F j w₀ t₁ s₁ → U.ExpandsF F j w₀ t₂ s₂ → U.ExpandsF F j' w₀ t₁' s₁' → U.ExpandsF F j' w₀ t₂' s₂' → Cross E.aA t₁ t₂ t₁' t₂' → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w : Frm D.toPre F j g'.b) (w' : Frm D.toPre F j' g.b), w.IsGen → w'.IsGen → ∀ α, SumF I F (fun p : {p : D.toPre.X × D.toPre.X // E.h p.1 + p.2 = α} => coef s₁ g' w p.1.1 * coef s₂' g w' p.1.2 - coef s₂ g' w p.1.1 * coef s₁' g w' p.1.2) 0 := by
  first | exact @GlobalTheory.UT.MixedConv.sumF_conv_of_cross | exact GlobalTheory.UT.MixedConv.sumF_conv_of_cross | (intros; apply GlobalTheory.UT.MixedConv.sumF_conv_of_cross <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompatibleGeneratingSectionsAllThickenings
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecTower

theorem exists_veryAmpleBy_pullback {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X} {n : ℕ} {s : Fin (n + 1) → LB.Sec H} (hH : H.IsLB)
    (hs : VeryAmpleBy f H s) :
    ∃ s' : Fin (n + 1) → LB.Sec (H.pull (pullback.fst f (Spec.map (CommRingCat.ofHom g)))),
      VeryAmpleBy (pullback.snd f (Spec.map (CommRingCat.ofHom g)))
        (H.pull (pullback.fst f (Spec.map (CommRingCat.ofHom g)))) s' := by
  have hL := LB.isLB_pull hH (pullback.fst f (Spec.map (CommRingCat.ofHom g)))
  have hw := CubePf.idIsoL_isGen hL
  choose s' hs' using fun j => GlobalTheory.SecPullIso.exists_pull _ H (H.pull _) _ hH hL hw (s j)
  refine ⟨s', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H n s hH hs R' g _ _ _ pullback.condition ?_ _ _ s' hL hw
    hs'⟩
  rw [pullback.lift_fst_snd]
  infer_instance

theorem exists_test_maps {R S : Type} [CommRing R] [CommRing S] (I : Ideal R) (g : R →+* S) (hg : ∀ x ∈ I, g x = 0)
    (Y : Over (Spec (CommRingCat.of R))) :
    ∃ (g' : ∀ e : ℕ, R ⧸ I ^ (e + 1) →+* S)
      (σ : ∀ e : ℕ, pullback Y.hom (Spec.map (CommRingCat.ofHom g)) ⟶ (thickObj R I e Y).left),
      (∀ e, (g' e).comp (Ideal.Quotient.mk _) = g) ∧
      (∀ e, IsPullback (σ e) (pullback.snd _ _) (thickObj R I e Y).hom (Spec.map (CommRingCat.ofHom (g' e)))) ∧
      (∀ e, σ e ≫ pullback.fst Y.hom (thick R I e) = pullback.fst _ _) ∧
      ∀ e, σ e ≫ thickMap R I e Y = σ (e + 1) := by
  let g' : ∀ e : ℕ, R ⧸ I ^ (e + 1) →+* S := fun e =>
    Ideal.Quotient.lift _ g fun x hx => hg x (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
  have hg' : ∀ e, (g' e).comp (Ideal.Quotient.mk _) = g := fun e => RingHom.ext fun x => rfl
  have hc : ∀ e, Spec.map (CommRingCat.ofHom (g' e)) ≫ thick R I e = Spec.map (CommRingCat.ofHom g) := fun e => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg']
  have ht : ∀ e, Spec.map (CommRingCat.ofHom (g' e)) ≫ thickTrans R I e =
      Spec.map (CommRingCat.ofHom (g' (e + 1))) := fun e => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    rfl
  refine ⟨g', fun e => pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (g' e)))
    (by rw [Category.assoc, hc]; exact pullback.condition), hg', fun e => ?_, fun e => pullback.lift_fst _ _ _,
    fun e => ?_⟩
  · refine IsPullback.of_right (h₁₂ := pullback.fst Y.hom (thick R I e)) (h₂₂ := thick R I e)
      (v₁₃ := Y.hom) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [hc, pullback.lift_fst]
    exact IsPullback.of_hasPullback _ _
  · apply pullback.hom_ext
    · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
    · erw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        Category.assoc, ht]

theorem isPullback_thickMap {R : Type} [CommRing R] (I : Ideal R) (Y : Over (Spec (CommRingCat.of R))) (e : ℕ) :
    IsPullback (thickMap R I e Y) (thickObj R I e Y).hom (thickObj R I (e + 1) Y).hom (thickTrans R I e) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst Y.hom (thick R I (e + 1))) (h₂₂ := thick R I (e + 1))
    (v₁₃ := Y.hom) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [thickTrans_comp, pullback.lift_fst, Category.comp_id]
  exact IsPullback.of_hasPullback _ _

theorem exists_tower : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : Over (Spec (CommRingCat.of R))) (H : LB Y.left) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), Smooth Y.hom → H.IsLB → VeryAmpleBy Y.hom H s → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Y.left, (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃ (t : ℤ) (m : ℕ) (u : ∀ e, Fin (m + 1) → LB.Sec (LB.LinComb H (Y := (thickObj R I e Y).left) (K := Fin 2) ![pullback.fst Y.hom (thick R I e), f e] ![t, -1])), (⨆ i, nonzeroLocus (u 0 i) = ⊤) ∧ ∀ e i z J, Good H z J → sval (u (e + 1) i) (thickMap R I e Y) z J = sval (u e i) (𝟙 _) z J := by
  intro R _ _ I Y H n s hsm hH hs f hf
  obtain ⟨S, _, g, hS, hg, hker⟩ := GlobalTheory.exists_graded_ring_kernel_lift R I
  obtain ⟨g', σ, hg', hσ, hσa, hσt⟩ := exists_test_maps I g hg Y
  have hσb : ∀ e, σ e ≫ f e = σ 0 ≫ f 0 := fun e => by
    induction e with
    | zero => rfl
    | succ e ih => rw [← hσt, Category.assoc, hf, ih]
  obtain ⟨sS, hsS⟩ := exists_veryAmpleBy_pullback g Y.hom hH hs
  have hva := fun e : ℕ => exists_veryAmpleBy_pullback (Ideal.Quotient.mk (I ^ (e + 1))) Y.hom hH hs
  obtain ⟨t₁, h₁⟩ := GlobalTheory.T.exists_h1Vanishes_generated_pullbackPow_tensor_dual S _ _ _ H _ (σ 0 ≫ f 0) n sS hH hsS
  obtain ⟨s₀, hs₀⟩ := hva 0
  obtain ⟨t₂, h₂⟩ := GlobalTheory.T.exists_h1Vanishes_generated_pullbackPow_tensor_dual _ _ _ _ H _ (f 0) n s₀ hH hs₀
  obtain ⟨m, u₀, hu₀⟩ := (h₂ (max t₁ t₂) (le_max_right _ _)).2
  have hZ := (h₁ (max t₁ t₂) (le_max_left _ _)).1
  have step : ∀ (e : ℕ) (v : LB.Sec (LB.LinComb H (Y := (thickObj R I e Y).left) (K := Fin 2)
      ![pullback.fst Y.hom (thick R I e), f e] ![max t₁ t₂, -1])),
      ∃ v' : LB.Sec (LB.LinComb H (Y := (thickObj R I (e + 1) Y).left) (K := Fin 2)
        ![pullback.fst Y.hom (thick R I (e + 1)), f (e + 1)] ![max t₁ t₂, -1]),
        ∀ z J, Good H z J → sval v' (thickMap R I e Y) z J = sval v (𝟙 _) z J := fun e v => by
    obtain ⟨s₁, hs₁⟩ := hva (e + 1)
    refine GlobalTheory.T.exists_section_lift_baseChange_h1Vanishing_testRing _ _ S _ (g' (e + 1)) (hker e (g' (e + 1)) (hg' _)) _ _ _ (thickObj R I (e + 1) Y).hom
      (thickObj R I e Y).hom _ (thickMap R I e Y) (σ (e + 1))
      (inferInstanceAs (Smooth (pullback.snd Y.hom (thick R I (e + 1))))) ⟨_, LB.isLB_pull hH _, n, s₁, hs₁⟩
      (isPullback_thickMap I Y e) (hσ (e + 1)) _ H (Fin 2) _ _ _ hH (fun k => ?_)
      (hZ _ (σ (e + 1)) _ _ (hσa _) (hσb _)) v
    fin_cases k
    · exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    · exact hf e
  choose F hF using step
  exact ⟨max t₁ t₂, m, fun e => Nat.rec (motive := fun e => Fin (m + 1) → LB.Sec (LB.LinComb H
      (Y := (thickObj R I e Y).left) (K := Fin 2) ![pullback.fst Y.hom (thick R I e), f e] ![max t₁ t₂, -1]))
    u₀ (fun e v i => F e (v i)) e, hu₀, fun e i => hF e _⟩

end GlobalTheory.SecTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataFunctionalEquationDegreeOn
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.UU

theorem exists_degData_fe_one : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ (D' : DegData V (IsLocalRing.maximalIdeal V)) (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A G), U'.P = U.P ∧ U'.gen = U.gen ∧ U'.FE (Kbar V) 1) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U

  obtain ⟨θ, f, hθ⟩ := GlobalTheory.T.exists_integral_theta_section_with_expansion hL hL2 V hV D A G U
  have hf := (GlobalTheory.T.thetaSection_support_eq_univ hL hL2 V hV D A G U θ f hθ).1

  obtain ⟨ψ, h, hpsi⟩ := GlobalTheory.T.exists_psi_thetaExpansionPsiRelation hL hL2 V D f hf
  obtain ⟨U', hP, hgen, -, hth⟩ := exists_preU_setPsi V D (IsLocalRing.maximalIdeal V) A G U ψ h
  obtain ⟨θ', hθ'⟩ := hth θ f hθ

  have hev := GlobalTheory.T.even_psi_of_thetaExpansionPsiRelation hL hL2 V hV (setPsi D ψ h) A G U' θ' f hθ' hpsi
  have hbi := GlobalTheory.T.bimultiplicative_tau_of_thetaExpansionPsiRelation hL hL2 V hV (setPsi D ψ h) A G U' θ' f hθ' hpsi
  have hfin := GlobalTheory.T.finite_not_psiIn_maximalIdeal_pow V hV (setPsi D ψ h) A G U' θ' f hθ' (hf 0) hpsi
  have hpos := GlobalTheory.psiIn_maximalIdeal_of_ne_zero V hV (setPsi D ψ h) hbi hev (hfin 1)
  have hfe := GlobalTheory.T.thetaExpansion_functionalEquation_degree_one hL hL2 V hV (setPsi D ψ h) A G U' θ' f hθ' hpsi
  exact ⟨{ toPre := setPsi D ψ h, psi_even := hev, tau_bimult := hbi, psi_pos := hpos, psi_tendsto := hfin }, U', hP, hgen, hfe⟩
end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteClosedSubschemeRepresentsKernelAmple
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelRep

theorem exists_finite_closed_kernel : GlobalFnsSt → ∀ (V : Type) [CommRing V] (B : Over (Sp V)) [GrpObj B], IsAbelianScheme B → ∀ L : LB B.left, L.IsLB → RelAmple B L → ∃ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left ∧ IsFinite H.hom ∧ (∀ (T : Over (Sp V)) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) := by
  intro hG V _ B _ hB L hL hA
  have hP : IsProjBy B.hom := (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B L hB hL hA V
    (𝟙 _) B.left (𝟙 _) B.hom IsPullback.of_id_fst).1
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L hL
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hG V B hB hP L (pw L 0) hL hO
  have : IsCommMonObj B := hB.comm
  exact ⟨H, j, hj, GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG V B hB L (pw L 0) hL hO hA H j hj hH,
    fun T x => (hK _ rfl T x).trans (hH T x)⟩

end GlobalTheory.KernelRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveAlgebraisationFormalEmbeddingStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projective_algebraisation_formal_embedding : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e, (∀ j, (∀ z (k : (H (e + 1)).ι) (k' : (H e).ι), (β e) z ∈ (H (e + 1)).U k → z ∈ (H e).U k' → gs (β e) z _ ((s (e + 1) j).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k')))) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ (B : Over (Spec (CommRingCat.of V))) (H' : LB B.left) (s' : Fin (n + 1) → LB.Sec H') (b : ∀ e, (Y e).left ⟶ B.left) (w : ∀ e, LB.Iso (H e) (H'.pull (b e))), H'.IsLB ∧ VeryAmpleBy B.hom H' s' ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (w e).IsGen ∧ (∀ j, (∀ z (k : (H').ι) (k' : (H e).ι), (b e) z ∈ (H').U k → z ∈ (H e).U k' → gs (b e) z _ ((s' j).f k) = (Geo.Tor.gw (w e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k')))) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) V), F.IsHomogeneous t → (∀ e, (∀ k : (H e).ι, MvPolynomial.eval₂Hom (cst ((Y (e)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e)) ((H e).U k)) (fun j => (s e j).f k) (F) = 0)) → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (B.hom) ((H').U k)) (fun j => (s' j).f k) (F) = 0) := by
  first | exact @GlobalTheory.Unif.exists_projective_of_formal_embedding | exact GlobalTheory.Unif.exists_projective_of_formal_embedding | (intros; apply GlobalTheory.Unif.exists_projective_of_formal_embedding <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformisationOfFunctionalEquationDegreeOnStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_of_functionalEquation_degreeOne : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU (IsLocalRing.maximalIdeal V) D.toPre A G), U.FE (Kbar V) 1 → ∃ U' : Unif (IsLocalRing.maximalIdeal V) D A G, Match U U'.toUnifPre := by
  first | exact @GlobalTheory.UU.exists_unif_of_fe_one | exact GlobalTheory.UU.exists_unif_of_fe_one | (intros; apply GlobalTheory.UU.exists_unif_of_fe_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphism
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.PullExp
open GlobalTheory.FieldBaseChange

section Uniq

theorem comb_eq_zero {R K F : Type} [CommRing R] [IsDomain R] [Field K] [Field F] [Algebra K F] [Algebra R K]
    [IsFractionRing R K] {V₀ V V' : Type} [AddCommGroup V₀] [Module R V₀] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module F V'] {J : Type} {P₀ : J → Type} [∀ j, AddCommGroup (P₀ j)] [∀ j, Module R (P₀ j)]
    {P P' : Type} [AddCommGroup P] [Module K P] [AddCommGroup P'] [Module F P'] (X : Submodule R (V₀ × ∀ j, P₀ j))
    (j : J) (ρ : V₀ →ₛₗ[algebraMap R K] V) (ρ' : P₀ j →ₛₗ[algebraMap R K] P)
    (a : V →ₛₗ[algebraMap K F] V') (ha : IsExtension a) (b : P →ₛₗ[algebraMap K F] P') (hb : IsExtension b)
    (hX : ∀ x ∈ X, ρ x.1 = 0 → x.2 j = 0) {T : Type} [Fintype T] (c : T → F) (x : T → V₀ × ∀ j, P₀ j)
    (hx : ∀ i, x i ∈ X) (h : ∑ i, c i • a (ρ (x i).1) = 0) : ∑ i, c i • b (ρ' ((x i).2 j)) = 0 := by
  refine hb.eq_of_coord fun ℓ Λ' hΛ' => ?_
  obtain ⟨Λ, hΛ⟩ := ha.coord ℓ
  obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) (fun i => ℓ (c i))
  choose m hm using hr
  have hr : algebraMap R K r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (nonZeroDivisors.coe_ne_zero r)
  have e₁ : ρ (∑ i, m i • x i).1 = algebraMap R K r • Λ (∑ i, c i • a (ρ (x i).1)) := by
    rw [map_sum, Finset.smul_sum, Prod.fst_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΛ, Prod.smul_fst, map_smulₛₗ, hm, smul_smul, Algebra.smul_def]
  have e₂ : ρ' ((∑ i, m i • x i).2 j) = algebraMap R K r • Λ' (∑ i, c i • b (ρ' ((x i).2 j))) := by
    rw [map_sum, Finset.smul_sum, Prod.snd_sum, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΛ', Prod.smul_snd, Pi.smul_apply, map_smulₛₗ, hm, smul_smul, Algebra.smul_def]
  rw [h, map_zero, smul_zero] at e₁
  rw [hX _ (Submodule.sum_mem _ fun i _ => X.smul_mem _ (hx i)) e₁, map_zero] at e₂
  rw [map_zero]
  exact (smul_eq_zero.1 e₂.symm).resolve_left hr

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem term_eq_zero [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (k : ℕ) (α : D.toPre.X)
    (x : IntSec U k × ∀ α, IntTerm D k α) (hx : x ∈ expansionPairs U k) (h : genericSec U k x.1 = 0) :
    x.2 α = 0 := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have hd := GlobalTheory.ExtUnique.spec_fractionRing R (FractionRing R)
  have : IsSchemeTheoreticallyDominant (jK R) := hd.2
  have : QuasiCompact (jK R) := hd.1
  have h₀ : ∀ j, x.1.f j = 0 := fun j => by
    refine (pullback.fst G.hom (jK R)).app_injective _ (fn_ext fun y hy => ?_)
    have hy' : y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j :=
      mem_wchart.2 fun i => mem_wchart.1 hy i
    refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ ((congrArg _ (map_zero _)).trans (gs_zero' _ y _ hy)).symm)
    exact (gs_pullFn pullback.condition _ _ (𝟙 _) y hy').symm.trans
      ((congrArg (fun s : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))) =>
        gs (𝟙 _) y (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j) (LB.Sec.f s j)) h).trans (gs_zero' _ y _ hy'))
  have := D.toPre.P.isAb.smooth
  have : GeometricallyConnected D.toPre.P.A.hom := D.toPre.P.isAb.geomConnected
  refine SecOver.ext _ _ ((sec_eq_zero_and_hom_eq_of_thickenings R I hI D.toPre.P.A).1 _
    (linComb_isLB _ D.toPre.P.isLB _ _) (x.2 α) fun e j => ?_)
  exact (GlobalTheory.ExtDiv.pG_app_eq_zero_iff (U.gt e) _ _).1 (WeightPf.weightIndep R I D A G U e k x.1 x.2
    (fun j => (congrArg _ (h₀ j)).trans (map_zero _)) (hx e) α j)

theorem secLin_of_expandsG [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (v : GroupSec U F k) (s : Fam D.toPre F k) (hs : U.ExpandsG F k v s)
    (n : ℕ) (c : Fin n → F) (σ : Fin n → IntSec U k) (f : Fin n → ∀ α : D.toPre.X, IntTerm D k α)
    (hf : ∀ i e, U.ExpandsAt e k (σ i) (f i))
    (hv : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (k : ℤ)) v (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c i))) (α : D.toPre.X) :
    GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (D.toPre.famφB α) (DegPre.famε k)
      (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (c i)) := by
  obtain ⟨n', c', x', hx', e₁, e₂⟩ := (expandsG_iff U F k v s).1 hs
  have d₁ := (secLin_iff U.LG.isLB v σ
    (UnifPre.gFK (G := G) F) c (fun i => extendSec U F k (genericSec U k (σ i))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (σ i) q y J) (Category.assoc _ _ _))))).1 hv
  refine (secLin_iff D.toPre.P.isLB
    (famProj D.toPre F k α s) (fun i => f i α) (DegPre.prB D.toPre F).left c
    (fun i => termPull D.toPre (FractionRing R) F k α (genericTerm D k α (f i α))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (f i α) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
          (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing R) F)))))))).2 ?_
  have : TopologicalSpace.NoetherianSpace ((Over.pullback (jK R)).obj G).left := noetherianSpace_generic U
  have H := comb_eq_zero (expansionPairs U k) α (genericSec U k) (genericTerm D k α) (extendSec U F k)
    (isExtension_pullOver (isPullback_groupBase F) U.LG.isLB _ _) (termPull D.toPre (FractionRing R) F k α)
    (isExtension_termPull D.toPre _ F k α) (term_eq_zero U hI k α) (Sum.elim c' fun i => -c i)
    (Sum.elim x' fun i => (σ i, f i)) (by rintro (i | i); exacts [hx' i, hf i]) (by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib]
      rw [← e₁, ← d₁, add_neg_cancel])
  rw [Fintype.sum_sum_type] at H
  simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib] at H
  rw [← e₂ α] at H
  exact add_neg_eq_zero.1 H

end Uniq

section Norm
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

theorem eSec_comp_one : eSec G ≫ (1 : G ⟶ G).left = eSec G :=
  congrArg (fun q => q.left) ((MonObj.comp_one (M := G) η[G]).trans (by
    show toUnit _ ≫ η[G] = η[G]
    rw [toUnit_unit, Category.id_comp]))

theorem exists_normalised (hL : L.IsLB) (a : G ⟶ G) [IsMonHom a] (k' k : ℤ)
    (β : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 _, a.left] ![k', -k])) (hβ : β.IsGen) :
    ∃ ν : LB.Gen (LB.LinComb L (K := Fin 3) ![𝟙 _, a.left, (1 : G ⟶ G).left] ![k', -k, k - k']), ν.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ ν (eSec G)) (LB.oneGen L) := by
  have e : (1 : G ⟶ G).left ≫ a.left = (1 : G ⟶ G).left :=
    congrArg (fun q : G ⟶ G => q.left) (MonObj.one_comp a)
  obtain ⟨ν, hν, hv⟩ := exists_gen hL (K' := Fin 3) (φ' := ![𝟙 _, a.left, (1 : G ⟶ G).left]) (ε' := ![k', -k, k - k'])
    (fun V _ h => by
      rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_three]
      show h (𝟙 _) ^ k' * h a.left ^ (-k) * (h ((1 : G ⟶ G).left ≫ 𝟙 _) ^ (-k') * h ((1 : G ⟶ G).left ≫ a.left) ^ (- -k)) =
        h (𝟙 _) ^ k' * h a.left ^ (-k) * h (1 : G ⟶ G).left ^ (k - k')
      rw [e, Category.comp_id, ← zpow_add, neg_neg, neg_add_eq_sub])
    (LB.mulGen L _ _ _ _ β (LB.invGen L _ _ (LB.pullGen L _ _ β (1 : G ⟶ G).left)))
    (mulGen_isGen _ _ _ _ _ _ _ hβ (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hβ _)))
  refine ⟨ν, hν, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, val_one, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.id_comp, eSec_comp_one,
    mul_inv_cancel]

end Norm

variable {R : Type} [CommRing R] [IsDomain R]

theorem normd_val_eq (hG : GlobalFnsSt) {D : DegPre R} {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)}
    {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb D.P.L φ ε)} (hu : Normd u) (hu' : Normd u') {Z : Scheme.{0}}
    (r : Z ⟶ D.P.A.left) (z : Z) (J) (hJ : Good D.P.L z J) : val u r z J = val u' r z J := by
  refine gen_unique D.P.isLB D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2 hu.1 hu'.1
    (fun y J hJ => ?_) Z r z J hJ
  have a := val_corr hJ hu.2 (𝟙 _)
  have a' := val_corr hJ hu'.2 (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at a a'
  exact a.trans a'.symm

theorem sval_comb {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k n : ℕ} {c : Fin n → F}
    {χ : D.X} {s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε k))} {f : Fin n → D.SecB k χ}
    (h : GeneratorPullback.SecLin D.P.L (DegPre.famφ D F χ) (DegPre.famε k) s (D.famφB χ) (DegPre.famε k) f (DegPre.prB D F).left
      (fun i => scal (fst (TF (R := R) F) D.P.A).left (c i))) (b : TF (R := R) F ⟶ D.P.A) (z) {J}
    (hJ : Good D.P.L z J) :
    sval s (lift (𝟙 (TF (R := R) F)) b).left z J = ∑ i, cst F z (c i) * sval (f i) b.left z J := by
  refine (GlobalTheory.BoxExpansion.secLin_val h _ z hJ).trans (Finset.sum_congr rfl fun i _ => ?_)
  have e₁ : (lift (𝟙 (TF (R := R) F)) b).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    by
    rw [← Over.comp_left, lift_fst]; rfl
  have e₂ : (lift (𝟙 (TF (R := R) F)) b).left ≫ (DegPre.prB D F).left = b.left :=
    by
    rw [← Over.comp_left, lift_snd]
  rw [e₂]
  exact congrArg (· * _) ((gs_scal _ _ z (c i)).trans (congrArg (fun q => constVal q z (c i)) e₁))

theorem main : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (E : EndU U.toUnifPre), Function.Injective E.h → ∀ (k' k : ℕ), 1 ≤ k → 1 ≤ k' → (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen) → (∃ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ) ∧ ∀ (w₀ : W0 U.toUnifPre) (ρ), NormW U.toUnifPre w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') s s', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w' : Frm D.toPre F k' g.b) (w : Frm D.toPre F k g'.b), w'.IsGen → w.IsGen → (∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J) → (∀ χ, coef s' g w' (E.h χ) = coef s g' w χ) ∧ ∀ β, β ∉ Set.range E.h → coef s' g w' β = 0 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ E hh k' k hk hk' ⟨β₀, hβ₀⟩
  have hGF := hL.1.globalFns
  have := hI.1
  have := hI.2.2.2
  have := E.homG
  obtain ⟨β, hβ, hβ'⟩ := exists_normalised U.LG.isLB E.aG k' k β₀ hβ₀
  obtain ⟨κ₀, hκ₀, hrel⟩ := GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization hL R I hI D A G hG U E k' k β hβ hβ'
  refine ⟨⟨κ₀, hκ₀⟩, ?_⟩
  intro w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' s s' ⟨v, hv, n, c, σ, f, h₁, h₂, h₃⟩ ⟨v', hv', hs'⟩ htw κ hκ g g' hg w' w hw' hw₁ hww
  choose σ' f' p₁ p₂ p₃ p₄ using fun i => GlobalTheory.T.pullback_section_endomorphism_expansion R I D A G U.toUnifPre E hh k' k β hβ κ₀ hκ₀.1 hrel (σ i) (f i) (h₁ i)
  have tw := GlobalTheory.T.endU_twist_of_iso hGF R I D A G U.toUnifPre E F k' k β hβ hβ' w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' v v' hv hv' htw
  have H := secLin_of_expandsG U.toUnifPre (IsAdicComplete.le_jacobson_bot I) F k' v' s' hs' n c σ' f' p₁
    ((secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => by
      rw [tw y J hJ, GlobalTheory.BoxExpansion.secLin_val h₂ _ y hJ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e₁ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
        rw [← Over.comp_left, whiskerLeft_fst]
      have e₂ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫ UnifPre.gFK (G := G) F =
          UnifPre.gFK (G := G) F ≫ E.aG.left := by
        rw [UnifPre.gFK, ← Category.assoc, ← Over.comp_left, whiskerLeft_snd, Over.comp_left, Category.assoc,
          Category.assoc]
        exact congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)
      rw [p₂ i _ _ y J hJ, gs_scal, gs_scal, e₁, e₂, Category.id_comp, Category.id_comp, _root_.mul_assoc])
  refine ⟨fun χ => CoefBasic.coef_eq fun z J hJ => ?_, fun b hb => CoefBasic.coef_eq fun z J hJ => ?_⟩
  · have a := CoefBasic.isCoef_coef g' hw₁ χ s z J hJ
    have e : g.b.left ≫ D.toPre.P.A.hom = (TF (R := R) F).hom := Over.w g.b
    have e' : g'.b.left = g.b.left ≫ E.aB.left := congrArg (fun q => q.left) hg.1
    rw [sval_comb (h₃ χ) _ z hJ, hg.2 χ z J hJ, ← hww z J hJ, e', normd_val_eq hGF hκ hκ₀ _ z J hJ] at a
    rw [sval_comb (H (E.h χ)) _ z hJ]
    simp only [p₃ _ χ _ _ z J hJ, e, ← _root_.mul_assoc, ← Finset.sum_mul]
    have e₃ : (rigV D.toPre (TF (R := R) F).hom z J).val ^ k' =
        (rigV D.toPre (TF (R := R) F).hom z J).val ^ k * (rigV D.toPre (TF (R := R) F).hom z J ^ ((k' : ℤ) - k)).val := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_natCast,
        ← zpow_add, add_sub_cancel]
    rw [e₃, ← _root_.mul_assoc, a]
    simp only [Units.val_mul]
    ring
  · rw [sval_comb (H b) _ z hJ, CoefBasic.cst_eq, map_zero, zero_mul, Finset.sum_eq_zero, zero_mul, zero_mul]
    intro i _
    exact (congrArg _ ((congrArg (gs _ z _) (p₄ i b hb _)).trans (gs_zero' _ z _ (hJ.mem _ _)))).trans (mul_zero _)

end GlobalTheory.UT.PullExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductOfSectionsExpandsToConvolutionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_of_sections_expands_to_convolution : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k k' k'' : ℕ), 1 ≤ k → 1 ≤ k' → k'' = k + k' → ∀ (t : SecA A F k) (t' : SecA A F k') (t'' : SecA A F k'') s s' s'', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → U.ExpandsF F k'' w₀ t'' s'' → (∀ z J, Good A.L z J → sA t'' (𝟙 _) z J = sA t (𝟙 _) z J * sA t' (𝟙 _) z J) → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b) (w' : Frm D.toPre F k' g.b) (w'' : Frm D.toPre F k'' g.b), w.IsGen → w'.IsGen → w''.IsGen → (∀ z J, Good D.toPre.P.L z J → val w'' (𝟙 _) z J = val w (𝟙 _) z J * val w' (𝟙 _) z J) → ∀ α, SumF I F (fun χ => coef s g w χ * coef s' g w' (α - χ)) (coef s'' g w'' α) := by
  first | exact @GlobalTheory.UT.ProdConv.main | exact GlobalTheory.UT.ProdConv.main | (intros; apply GlobalTheory.UT.ProdConv.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvrStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_hom_extension_dvr : HomExtSt := by
  first | exact @GlobalTheory.homExtension_semiAbelian_dvr_unconditional | exact GlobalTheory.homExtension_semiAbelian_dvr_unconditional | (intros; apply GlobalTheory.homExtension_semiAbelian_dvr_unconditional <;> assumption)
end

