import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2837
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusFlat
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3190
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3196
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3192
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3166
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3203
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2888
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismUniformisedGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GroupAdjoint

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem exists_adjoint {K : Type} [CommRing K] (Q : PolAV (Sp K)) (f : Q.A ⟶ Q.A) [IsMonHom f] :
    ∃ x : Q.A ⟶ Q.A, IsMonHom x ∧ ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A),
      lam (cls Q.L Q.isLB) (a ≫ f) b = lam (cls Q.L Q.isLB) a (b ≫ x) := by
  have := Q.isAb.comm
  have hd : IsDual Q.A Q.A (abelian₂ Q.A Q.L) := CompanionTheory.PfDual.kTrivDual K Q.A Q.g Q.isAb Q.smoothDim Q.L Q.isLB Q.ktriv
  have hΛ : (abelian₂ Q.A Q.L).IsLB := hd.isLB
  have e : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hΛ a b = lam (cls Q.L Q.isLB) a b := fun Y a b ↦ by
    rw [evc, show cls _ hΛ = lam (cls Q.L Q.isLB) (fst Q.A Q.A) (snd Q.A Q.A) from
      cls_cube_two Q.isLB _ _ hΛ, pull_lam, lift_fst, lift_snd]
  have l₁ : ∀ (Y : Over (Sp K)) (a a' b : Y ⟶ Q.A), evc hΛ (a * a') b = evc hΛ a b + evc hΛ a' b :=
    (isAdditive_iff hΛ).1 hd.additive
  have l₂ : ∀ (Y : Over (Sp K)) (a b b' : Y ⟶ Q.A), evc hΛ a (b * b') = evc hΛ a b + evc hΛ a b' := fun Y a b b' ↦ by
    rw [e, e, e, lam_comm, lam_comm _ a b, lam_comm _ a b', ← e, ← e, ← e]
    exact l₁ _ _ _ _
  have a₂ : IsAdditive (swap (abelian₂ Q.A Q.L)) := (BirigidLift.isAdditive_swap_iff hΛ).2 l₂
  have hM := pull_isLB hΛ (lift (fst Q.A Q.A ≫ f) (snd Q.A Q.A)).left
  have m : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hM a b = evc hΛ (a ≫ f) b := fun Y a b ↦ by
    rw [evc_ev hΛ]
    simp only [lift_fst_assoc, lift_snd]
  obtain ⟨x, hx, ex⟩ := BirigidLift.exists_hom hd a₂ hM
    ((isAdditive_iff hM).2 fun Y u u' t ↦ by rw [m, m, m, MonObj.mul_comp, l₁])
    ((BirigidLift.isAdditive_swap_iff hM).2 fun Y u t t' ↦ by rw [m, m, m, l₂])
  refine ⟨x, hx, fun Y a b ↦ ?_⟩
  rw [← e, ← e, ← m]
  exact BirigidLift.evc_of_cls hd.isLB hM ex a b

theorem exists_adjoint_on_group : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ g : G ⟶ G, IsMonHom g → ∃ g' : G ⟶ G, IsMonHom g' ∧ LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U g hg
  have hN : IsNoetherianRing R := hR.1.1
  have hI : IsIntegrallyClosed R := hR.1.2.2.1
  have := U.gen_hom
  have hL := U.LG.isLB
  have hp := isGrpPullback_pullback G (jK R)
  obtain ⟨x, hx, ex⟩ := exists_adjoint A (U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom)
  have hj : GlobalTheory.IsGenericPointHom (S := Sp R) (jK R) := .fractionField R (FractionRing R)
  obtain ⟨g', ⟨hg', eg'⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.of_isGenericPointHom
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R) hj hG hG (U.gen.hom ≫ x ≫ U.gen.inv)
  refine ⟨g', hg', ?_⟩
  have := hG.smooth
  have := hG.geomConnected
  have := GlobalTheory.smooth_tensorObj_hom G G
  have := GlobalTheory.geometricallyIntegral_tensorObj_hom G G
  have h₁ : (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L).IsLB := LB.isLB_linComb hL _ _
  have h₂ : (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L).IsLB := LB.isLB_linComb hL _ _
  refine GlobalTheory.T.lineBundleIso_of_generic_normal_local_base R (G ⊗ G) (1 : 𝟙_ _ ⟶ G ⊗ G).left (Over.w _) _ _ h₁ h₂ ?_
  refine (cls_eq_iff (pull_isLB h₁ _) (pull_isLB h₂ _)).1 ?_

  have ec : pull U.gen.hom.left (cls A.L A.isLB) = pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) := by
    rw [← cls_pull A.isLB _ (pull_isLB A.isLB _), ← cls_pull hL _ (pull_isLB hL _)]
    exact (cls_eq_iff _ _).2 U.ext
  have key : ∀ a b : G ⊗ G ⟶ G, pull (pullback.fst (G ⊗ G).hom (jK R)) (lam (cls U.LG.L hL) a b) =
      lam (cls A.L A.isLB) ((Over.pullback (jK R)).map a ≫ U.gen.hom) ((Over.pullback (jK R)).map b ≫ U.gen.hom) := by
    intro a b
    rw [← lam_pull, ec, lam_pull_of_isGrpPullback hp]
    refine GlobalTheory.CompanionTheory.DualScheme.pull_lam_of_left (T' := Over.mk (_ ≫ jK R)) _ _ ?_ ?_
    · exact (ExtUnique.pullback_map_left_fst (jK R) a).symm
    · exact (ExtUnique.pullback_map_left_fst (jK R) b).symm
  rw [cls_pull h₁, cls_pull h₂, cls_cube_two hL, cls_cube_two hL, key, key, Functor.map_comp, Functor.map_comp, eg']
  have := ex _ ((Over.pullback (jK R)).map (fst G G) ≫ U.gen.hom) ((Over.pullback (jK R)).map (snd G G) ≫ U.gen.hom)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using this

end GlobalTheory.Mum.GroupAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerLiftOfNonvanishingOnClosed
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.LiftAmple

def chartPullPullPow {X T : Scheme.{0}} (L : LB X) (i : T ⟶ X) (n : ℕ) :
    ChartPull ((lbPow L n).pull i) (lbPow (L.pull i) n) (𝟙 T) where
  idx J := J
  le J y hy := mem_powChart.2 (mem_pull.2 (mem_powChart.1 (mem_pull.1 hy)))
  g y J J' hJ hJ' := by
    let K : PUnit → (L.pull i).ι := J
    let K' : PUnit → (L.pull i).ι := J'
    have h₁ : i y ∈ L.U (J PUnit.unit PUnit.unit) := mem_powChart.1 (mem_pull.1 hJ)
    have h₂ : i y ∈ L.U (J' PUnit.unit PUnit.unit) := mem_powChart.1 (mem_pull.1 hJ')
    have k₁ : (𝟙 T) y ∈ powChart (L.pull i) K := mem_powChart.2 (mem_pull.2 h₁)
    have k₂ : (𝟙 T) y ∈ powChart (L.pull i) K' := mem_powChart.2 (mem_pull.2 h₂)
    refine (gm_pull_g (lbPow L n) i (𝟙 T) y J J' hJ hJ').trans ?_
    refine (gm_lbPow_g n (𝟙 T ≫ i) y (J PUnit.unit) (J' PUnit.unit) (mem_powChart.2 h₁)
      (mem_powChart.2 h₂)).trans ?_
    refine Eq.trans ?_ (gm_lbPow_g (L := L.pull i) n (𝟙 T) y K K' k₁ k₂).symm
    rw [gm_pull_g L i (𝟙 T) y (K PUnit.unit) (K' PUnit.unit) (mem_powChart.1 k₁) (mem_powChart.1 k₂)]

theorem exists_sec_pull_pow {X T : Scheme.{0}} (L : LB X) (i : T ⟶ X) (n : ℕ) (σ : (lbPow (L.pull i) n).Sec) :
    ∃ σ' : ((lbPow L n).pull i).Sec, nonzeroLocus σ' = nonzeroLocus σ :=
  ⟨chartSec (chartPullPullPow L i n) σ, nonzeroLocus_chartSec_id _ σ fun _ J hJ =>
    ⟨J, mem_pull.2 (mem_powChart.2 (mem_pull.1 (mem_powChart.1 hJ)))⟩⟩

end GlobalTheory.LiftAmple

namespace GlobalTheory.LiftAmple

theorem exists_sec_nonzero_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : LB X), IsAmpleLB L → ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i] (n : ℕ)
    (s : (lbPow (L.pull i) n).Sec), 1 ≤ n → ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ →
    ∃ (N : ℕ) (u : (lbPow L N).Sec), 1 ≤ N ∧ Set.range i ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  intro k _ X _ p D hX L hL T i _ n s hn hs
  haveI : Module.Finite ℤ k := hX.finite
  haveI : IsNoetherian ℤ k := inferInstance
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ this
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (GlobalTheory.T.eventually_surjective_toPushforward_ampleLineBundle_pow k X p hX.isProjOver L hL T i)
  have hN : N₀ ≤ n * (N₀ + 1) := by nlinarith
  obtain ⟨σ', hσ'⟩ := exists_sec_pull_pow L i (n * (N₀ + 1)) (secPow s (N₀ + 1))
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_sectionPullback_of_surjective_toPushforward X T i (lbPow L (n * (N₀ + 1))) (isLB_lbPow hL.isLB _) (hN₀ _ hN) σ'
  refine ⟨n * (N₀ + 1), u, by nlinarith, ?_⟩
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ nonzeroLocus (GlobalTheory.secPull u i) := by
    rw [hu, hσ', nonzeroLocus_secPow s (Nat.le_add_left 1 N₀), hs]; trivial
  rw [nonzeroLocus_secPull] at hz
  exact hz

end GlobalTheory.LiftAmple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerSectionNonvanishingOnFinite
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem exists_sec_nonvanishing_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ S : Set X, S.Finite → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, S ⊆ NV P e 0 f := by
  intro k _ X _ p D _ P hA S hS
  obtain ⟨n, hn, s, h₁, -, -⟩ := hA.exists_affine_finite_subset hS (U := ⊤) (Set.subset_univ _)
  obtain ⟨f, hf, e⟩ := (GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci k X p P n).1 s
  refine ⟨n, hn, f, hf, ?_⟩
  rw [e]
  exact h₁

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonCompleteDvrPadicAlgClosureUnitBallsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_complete_dvr_padicAlgClosure_unitBalls : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)], IsAdicComplete (maximalIdeal V) V → IsAdicComplete (maximalIdeal V') V' → (∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ x : FractionRing V', ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V' (FractionRing V'))) → ∀ s : Finset (PadicAlgCl p), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra (FractionRing W) (PadicAlgCl p)), IsAdicComplete (maximalIdeal W) W ∧ (∀ x : FractionRing W, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧ (↑s ⊆ Set.range (algebraMap (FractionRing W) (PadicAlgCl p))) ∧ (∀ z : PadicAlgCl p, ∃ f : Polynomial (FractionRing W), f ≠ 0 ∧ Polynomial.eval₂ (algebraMap (FractionRing W) (PadicAlgCl p)) z f = 0) ∧ (∃ (φ : V →+* W) (φK : FractionRing V →+* FractionRing W), φK.comp (algebraMap V _) = (algebraMap W _).comp φ ∧ (maximalIdeal V).map φ ≤ maximalIdeal W ∧ (algebraMap (FractionRing W) (PadicAlgCl p)).comp φK = algebraMap (FractionRing V) (PadicAlgCl p)) ∧ (∃ (φ : V' →+* W) (φK : FractionRing V' →+* FractionRing W), φK.comp (algebraMap V' _) = (algebraMap W _).comp φ ∧ (maximalIdeal V').map φ ≤ maximalIdeal W ∧ (algebraMap (FractionRing W) (PadicAlgCl p)).comp φK = algebraMap (FractionRing V') (PadicAlgCl p)) := by
  first | exact @GlobalTheory.UnifField.exists_common_ring | exact GlobalTheory.UnifField.exists_common_ring | (intros; apply GlobalTheory.UnifField.exists_common_ring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousPeriodBasisAlongArc
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

namespace GlobalTheory.ShFam.BdArc

theorem exists_period_basis_halfPlane
: ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), GoodEmb c σ → 1 ≤ Dw.p + Dw.q → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ x) s ∉ genBd Z) → ∃ (T₀ : ℝ) (m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ), (∀ w : ℂ, T₀ < w.im → eTwoPi w ∈ Metric.ball (0 : ℂ) r) ∧ ContinuousOn lam {w : ℂ | T₀ < w.im} ∧ (∀ w : ℂ, T₀ < w.im → LinearIndependent ℝ (lam w) ∧ Submodule.span ℝ (Set.range (lam w)) = ⊤) ∧ (∀ w : ℂ, T₀ < w.im → ∀ ex : (Fin g → ℂ) → (Over.mk (spMap (ψ (eTwoPi w)) ≫ x ≫ genι Z) ⟶ Z.t.G), (∀ z z', ex (z + z') = ex z * ex z') → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (ex z).left)) → (∀ j, IsDerivAt0 (fun z => (ex z).left) (Pi.single j 1) (spMap (dualMap (ψ (eTwoPi w))) ≫ fr.v (e j).1 (e j).2)) → ∀ z, ex z = 1 ↔ ∃ n : Fin m → ℤ, z = ∑ j, n j • lam w j) ∧ ∀ R : ℝ, ∃ (C : ℝ) (B : ℕ), ∀ w : ℂ, T₀ < w.im → |w.re| ≤ R → ‖lam w‖ ≤ C * w.im ^ B := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ r g e hσ hpq harc hin
  obtain ⟨g', ρ, e', hρ, hρr, hol, hexp, -⟩ := GlobalTheory.T.exists_semi_abelian_exponential_along_disc Z.X Z.t.G (fun u => spMap (ψ u) ≫ x ≫ genι Z) r
    Z.t.semi harc.1.1 (GlobalTheory.ShFam.BdArc.LatSec.isHolTo_spMap harc.1 _)
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_frameChange_eigenframe_exponentials_holArc E H Dw l Xo c O β Z σ A φ x fr ψ r g e g' ρ e' harc hρ hρr hol hexp
  obtain ⟨ρ₀, m, lamE, hρ₀, hρ₀ρ, hcont, hlat, C, k, hC⟩ :=
    GlobalTheory.T.exists_continuous_period_lattice_basis_arc E H Dw l Xo c O β Z σ A φ x ψ r g' ρ e' hσ hpq harc hin hρ hρr hol hexp
  have hper : ∀ s : ℂ, s.re < 0 → ∀ z, (∃ n : Fin m → ℤ, z = ∑ j, n j • lamE (s + 2 * Real.pi * Complex.I) j) ↔
      ∃ n : Fin m → ℤ, z = ∑ j, n j • lamE s j := by
    intro s hs z
    have hs' : (s + 2 * Real.pi * Complex.I).re < 0 := by simpa using hs
    rw [← (hlat _ hs').2.2, ← (hlat s hs).2.2, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hcb : Metric.closedBall (0 : ℂ) (ρ₀ / 2) ⊆ Metric.ball 0 ρ := Metric.closedBall_subset_ball (by linarith)
  obtain ⟨Ch, hCh⟩ := (isCompact_closedBall (0 : ℂ) (ρ₀ / 2)).exists_bound_of_continuousOn
    (fun u hu => ((hh u (hcb hu)).2.1).continuousWithinAt)
  have hCh0 : 0 ≤ Ch := (norm_nonneg _).trans (hCh 0 (Metric.mem_closedBall_self (by linarith)))
  set T₀ : ℝ := max 1 (Real.log (2 / ρ₀) / (2 * Real.pi)) with hT₀
  let sOf : ℂ → ℂ := fun w => 2 * Real.pi * Complex.I * w - (Real.log ρ₀ : ℂ)
  have hsOf : Continuous sOf := by fun_prop
  have hnorm : ∀ w : ℂ, ‖eTwoPi w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
    intro w
    rw [eTwoPi, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  have hsmall : ∀ w : ℂ, T₀ < w.im → ‖eTwoPi w‖ < ρ₀ / 2 := by
    intro w hw
    have h1 : Real.log (2 / ρ₀) < 2 * Real.pi * w.im := by
      have := (le_max_right _ _).trans_lt hw
      rw [div_lt_iff₀ (by positivity)] at this
      linarith
    rw [hnorm]
    calc Real.exp (-(2 * Real.pi * w.im)) < Real.exp (-Real.log (2 / ρ₀)) := Real.exp_lt_exp.2 (by linarith)
      _ = ρ₀ / 2 := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hueq : ∀ w : ℂ, (ρ₀ : ℂ) * Complex.exp (sOf w) = eTwoPi w := by
    intro w
    simp only [sOf, eTwoPi]
    rw [Complex.exp_sub, ← Complex.ofReal_exp, Real.exp_log hρ₀, mul_div_cancel₀ _ (by exact_mod_cast hρ₀.ne')]
  have hexps : ∀ w : ℂ, ‖Complex.exp (sOf w)‖ = ‖eTwoPi w‖ / ρ₀ := by
    intro w
    rw [← hueq w, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ₀.le, mul_div_cancel_left₀ _ hρ₀.ne']
  have hexp2 : ∀ w : ℂ, T₀ < w.im → ‖Complex.exp (sOf w)‖ ≤ 1 / 2 := by
    intro w hw
    rw [hexps, div_le_iff₀ hρ₀]
    linarith [hsmall w hw]
  have hsre : ∀ w : ℂ, T₀ < w.im → (sOf w).re < 0 := by
    intro w hw
    have h1 := hexp2 w hw
    rw [Complex.norm_exp] at h1
    by_contra hc
    push_neg at hc
    have := Real.one_le_exp hc
    linarith
  have hub : ∀ w : ℂ, T₀ < w.im → eTwoPi w ∈ Metric.closedBall (0 : ℂ) (ρ₀ / 2) := fun w hw =>
    mem_closedBall_zero_iff.2 (hsmall w hw).le
  refine ⟨T₀, m, fun w j => (h (eTwoPi w)).inverse (lamE (sOf w) j), fun w hw => ?_, ?_, fun w hw => ?_,
    fun w hw ex hadd hex hd z => ?_, fun R => ?_⟩
  · exact Metric.ball_subset_ball (hρ₀ρ.le.trans hρr) (Metric.ball_subset_ball (by linarith) (mem_ball_zero_iff.2 (hsmall w hw)))
  · have hopen : IsOpen {w : ℂ | T₀ < w.im} := isOpen_lt continuous_const Complex.continuous_im
    refine fun w hw => ContinuousAt.continuousWithinAt ?_
    have hi : ContinuousAt (fun w => (h (eTwoPi w)).inverse) w :=
      ContinuousAt.comp (f := eTwoPi) (g := fun u => (h u).inverse) ((hh _ (hcb (hub w hw))).2.1)
        (by unfold eTwoPi; fun_prop)
    have hl : ContinuousAt (fun w => lamE (sOf w)) w :=
      ContinuousAt.comp (g := lamE) ((hcont.continuousAt (isOpen_lt Complex.continuous_re continuous_const |>.mem_nhds (hsre w hw))))
        hsOf.continuousAt
    exact continuousAt_pi.2 fun j => hi.clm_apply ((continuous_apply j).continuousAt.comp hl)
  · obtain ⟨L, hL⟩ := (hh _ (hcb (hub w hw))).1
    obtain ⟨hli, hsp, -⟩ := hlat _ (hsre w hw)
    simp only [← hL, ContinuousLinearMap.inverse_equiv]
    refine ⟨hli.map' (L.symm.toLinearEquiv.restrictScalars ℝ).toLinearMap (LinearEquiv.ker _), ?_⟩
    have : (Set.range fun j => (L.symm : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (lamE (sOf w) j)) =
        (L.symm.toLinearEquiv.restrictScalars ℝ).toLinearMap '' Set.range (lamE (sOf w)) := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨L, hL⟩ := (hh _ (hcb (hub w hw))).1
    have h1 := (hlat _ (hsre w hw)).2.2 (h (eTwoPi w) z)
    rw [hueq w] at h1
    rw [(hh _ (hcb (hub w hw))).2.2 ex hadd hex hd z, h1]
    simp only [← hL, ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe]
    refine exists_congr fun n => ?_
    rw [show ∑ j, n j • L.symm (lamE (sOf w) j) = L.symm (∑ j, n j • lamE (sOf w) j) by
        rw [map_sum]; exact Finset.sum_congr rfl fun j _ => (map_zsmul L.symm _ _).symm,
      ContinuousLinearEquiv.eq_symm_apply]
  · obtain ⟨C', hC'⟩ := GlobalTheory.T.polynomial_growth_of_periodic_integral_spans g' m lamE C k hcont (fun s hs => (hlat s hs).1) hper hC (2 * Real.pi * |R|)
    set D : ℝ := 1 + 2 * Real.pi + |Real.log ρ₀| + 2 * Real.pi * |R|
    refine ⟨Ch * max C' 0 * D ^ k, k, fun w hw hR => ?_⟩
    have hw1 : 1 ≤ w.im := (le_max_left _ _).trans hw.le
    have hsim : (sOf w).im = 2 * Real.pi * w.re := by simp [sOf, Complex.mul_re, Complex.mul_im]
    have hsre' : (sOf w).re = -(2 * Real.pi * w.im) - Real.log ρ₀ := by simp [sOf, Complex.mul_re, Complex.mul_im]
    have hsi : |(sOf w).im| ≤ 2 * Real.pi * |R| := by
      rw [hsim, abs_mul, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left (hR.trans (le_abs_self R)) (by positivity)
    have hb := hC' _ (hsre w hw) (hexp2 w hw) hsi
    have hsn : 1 + ‖sOf w‖ ≤ D * w.im := by
      have h2 := Complex.norm_le_abs_re_add_abs_im (sOf w)
      have h3 : |(sOf w).re| ≤ 2 * Real.pi * w.im + |Real.log ρ₀| := by
        rw [hsre']
        refine (abs_sub _ _).trans ?_
        rw [abs_neg, abs_of_pos (by positivity)]
      have h4 : 0 ≤ w.im - 1 := by linarith
      have h5 : 0 ≤ |Real.log ρ₀| + 2 * Real.pi * |R| + 1 := by positivity
      nlinarith [Real.pi_pos]
    have hpow : (1 + ‖sOf w‖) ^ k ≤ D ^ k * w.im ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hsn k
    have hlamn : ‖lamE (sOf w)‖ ≤ max C' 0 * (D ^ k * w.im ^ k) :=
      hb.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hpow (le_max_right _ _)))
    have hCu := hCh _ (hub w hw)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    calc ‖(h (eTwoPi w)).inverse (lamE (sOf w) j)‖ ≤ ‖(h (eTwoPi w)).inverse‖ * ‖lamE (sOf w) j‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ Ch * ‖lamE (sOf w)‖ := mul_le_mul hCu (norm_le_pi_norm _ j) (norm_nonneg _) hCh0
      _ ≤ Ch * (max C' 0 * (D ^ k * w.im ^ k)) := mul_le_mul_of_nonneg_left hlamn hCh0
      _ = Ch * max C' 0 * D ^ k * w.im ^ k := by ring

end GlobalTheory.ShFam.BdArc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveWeightSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

noncomputable section

namespace GlobalTheory.UPel.HT.GenKer

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R' : Type} [CommRing R'] [Algebra ℚ R'] {S : Scheme.{0}}

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (u : Sp B ⟶ Sp A) : ∃ β : A →+* B, u = spMap β :=
  ⟨(Spec.preimage u).hom, by simp [spMap]⟩

theorem charZero_of_hom {k : Type} [Field k] (β : R' →+* k) : CharZero k :=
  charZero_of_injective_ringHom (β.comp (algebraMap ℚ R')).injective

theorem pow_eq_one_geom {gb : GBase D.toG R'} {N : ℕ} {t : S ⟶ Sp R'} (o : GObj gb N t) (e : ℕ)
    (hEF : ∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S)
    (g : Over.mk x₀ ⟶ o.A) (M : ℕ) (hM : 0 < M) (hn : g ^ M = 1)
    (hg : ∃ u : (o.P.pull (lift (snd o.A (Over.mk x₀) ≫ g) (fst o.A (Over.mk x₀))).left).Gen, u.IsGen) :
    g ^ e = 1 := by
  obtain ⟨β, hβ⟩ := exists_spMap (x₀ ≫ t)
  haveI := charZero_of_hom β
  obtain ⟨I, -⟩ := o.geom k x₀ β hβ
  obtain ⟨y, hy⟩ : ∃ y : D.La, I.ev M y = g := (I.onto M hM g).1 hn
  have key : ∀ z : D.La, (M : ℤ) ∣ D.EF y z := by
    intro z
    have hm : 0 < M * 2 := by omega
    have ha : I.ev (M * 2) y ^ 2 = g := by rw [I.tower M 2 hM two_pos y, hy]
    have hc := GlobalTheory.WeilSqKer.weilIs_eq_one S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample k x₀ (M * 2)
      (Nat.cast_ne_zero.2 hm.ne') _ _ ((I.onto _ hm _).2 ⟨y, rfl⟩) ((I.onto _ hm _).2 ⟨z, rfl⟩) (ha ▸ hg) _
      (I.isom _ hm y z)
    have h1 : I.ζ (M * 2) ^ (2 * D.EF y z) = 1 :=
      GlobalTheory.Ex.Specialise.unitOn_bijective.1 (hc.trans (map_one _).symm)
    have h3 := ((I.ζ_prim (M * 2) hm).zpow_eq_one_iff_dvd _).1 h1
    have h4 : (M : ℤ) * 2 ∣ D.EF y z * 2 := by
      rw [mul_comm (D.EF y z)]; exact_mod_cast h3
    exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).1 h4
  let f : D.La →ₗ[ℤ] ℤ :=
    { toFun := fun z => D.EF y z / M
      map_add' := fun u v => by
        rw [map_add, Int.add_ediv_of_dvd_left (key u)]
      map_smul' := fun r u => by
        rw [map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply, Int.mul_ediv_assoc _ (key u)] }
  have hf : ∀ z, (M : ℤ) * f z = D.EF y z := fun z => Int.mul_ediv_cancel' (key z)
  obtain ⟨w, hw⟩ := hEF f
  have hyw : e • y = M • w := by
    apply D.nondeg
    ext z
    have hwz : D.EF w z = e • f z := by rw [hw]; rfl
    simp only [map_nsmul, LinearMap.smul_apply, hwz, nsmul_eq_mul]
    rw [← hf z]; ring
  calc g ^ e = I.ev M y ^ e := by rw [hy]
    _ = I.ev M (e • y) := (KerBy.ev_nsmul (La := D.La) _ (I.add M) e y).symm
    _ = 1 := (I.ker M hM _).2 ⟨w, hyw⟩

theorem exists_coprime_pow_eq_one (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R']
    (gb : GBase D.toG R') (N : ℕ) (_hN : 3 ≤ N) (S : Scheme.{0}) (t : S ⟶ Sp R') (o : GObj gb N t) :
    ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ u : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, u.IsGen) → x ^ e = 1 := by
  obtain ⟨e, he, hEF⟩ := D.perfP
  refine ⟨e, he, fun T x hx => ?_⟩
  apply Over.OverMorphism.ext
  refine T.left.affineCover.hom_ext _ _ fun i => ?_
  obtain ⟨B, ⟨u⟩⟩ : ∃ B : CommRingCat.{0}, Nonempty (T.left.affineCover.X i ≅ Spec B) :=
    ⟨_, ⟨(T.left.affineCover.X i).isoSpec⟩⟩
  rw [← cancel_epi u.inv]
  let a : Sp B ⟶ T.left := u.inv ≫ T.left.affineCover.f i
  let a' : Over.mk (a ≫ T.hom) ⟶ T := Over.homMk a rfl
  have hx' := KerBy.gen_comp S o.A o.P T _ a' x hx
  obtain ⟨M, hM, hxM⟩ := GlobalTheory.T.isTorsion_of_birigidified_bundle_trivial_on_slice S o.A o.P o.ab o.isLB o.rig₁ o.rig₂ o.symm o.ample B (a ≫ T.hom) _ hx'
  have hu : IsUnit ((M : ℕ) : Γ(S, ⊤)) := by
    have h0 : IsUnit ((M : ℕ) : R') := by
      simpa using (IsUnit.mk0 (M : ℚ) (Nat.cast_ne_zero.2 hM.ne')).map (algebraMap ℚ R')
    simpa using (h0.map (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom).map t.appTop.hom
  have h := GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points S o.A o.ab M hu _ _ hxM e fun k _ _ ξ =>
    pow_eq_one_geom o e hEF k _ _ M hM (by rw [← MonObj.comp_pow, hxM, MonObj.comp_one])
      (KerBy.gen_comp S o.A o.P _ _ _ _ hx')
  have h' : a' ≫ x ^ e = a' ≫ 1 := by rw [MonObj.comp_pow, h, MonObj.comp_one]
  have h'' : a ≫ (x ^ e).left = a ≫ (1 : T ⟶ o.A).left := congrArg (fun z => z.left) h'
  exact (Category.assoc _ _ _).symm.trans (h''.trans (Category.assoc _ _ _))

end GlobalTheory.UPel.HT.GenKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqvRational
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_eqv_rational : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E, Eqv D.toPre A (Kb R) N lab E → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, LabExt σ lab lab) → ∃ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N) (E₀ : _), Eqv D.toPre A (Kb R) N lab E₀ ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀) := by
  intro R _ _ _ hB D A N hN lab E hE hlab
  have hc0 : CharZero R := hB.2
  choose E' hE' hT using fun σ => GlobalTheory.T.exists_galoisConjugate_equivariantBijection_twist R hB D A N hN lab E hE hlab σ
  choose c hc using fun σ => GlobalTheory.T.equivariant_bijections_families_sections_differ_by_scalar R (maximalIdeal R) D A (Kb R) N hN lab E (E' σ) hE (hE' σ)
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.exists_common_scaling_descends_to_fractionField R hB A N {q : IntFam (maximalIdeal R) D.toPre N × Fam D.toPre (Kb R) N // q.1.Over q.2}
    (fun i => E i.1.2) c (fun σ i => ⟨E' σ i.1.2, hT σ i.1.1 i.1.2 i.2, hc σ i.1.2⟩)
  obtain ⟨E₀, hE₀, hE₀f⟩ := GlobalTheory.T.thetaFamilySectionEquivariance_smul_of_ne_zero R D.toPre A (Kb R) N lab E hE c₀
  choose Φ hΦ using hc₀
  have hex := fun F₀ => GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ (Kb R)
  refine ⟨fun F₀ => Φ ⟨(F₀, (hex F₀).exists.choose), (hex F₀).exists.choose_spec⟩, E₀, hE₀, fun F₀ s hs => ?_⟩
  obtain rfl : (hex F₀).exists.choose = s := (hex F₀).unique (hex F₀).exists.choose_spec hs
  exact hΦ _ (E₀ _) (hE₀f _)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateTwoTorsionSplitClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_translate_two_torsion_split_closed_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → SplitClosed G → TwoTorsRat G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (P₁ : GlobalTheory.UU.CP G) (A₁ : PolAV (Sp (FractionRing R))) (gen₁ : (Over.pullback (jK R)).obj G ≅ A₁.A), IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G.hom (jK R))) ∧ LBIso (abelian₂ G P₁.L.L) (abelian₂ G P.L.L) ∧ EvenOn P₁ := by
  first | exact @GlobalTheory.Mum.exists_even_translate_split | exact GlobalTheory.Mum.exists_even_translate_split | (intros; apply GlobalTheory.Mum.exists_even_translate_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmBundleExtensionOnFactorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteExtension_symmBundle_extension_on_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ExtLam G (A.L.pull gen.hom.left) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)) (L₁ : LB G₁.left), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β ∧ L₁.IsLB ∧ LBIso (L₁.pull (pullback.fst G₁.hom (jK R'))) ((A.L.pull gen.hom.left).pull κ₁) := by
  first | exact @GlobalTheory.Mum.exists_finExt_lbExt_of_factor | exact GlobalTheory.Mum.exists_finExt_lbExt_of_factor | (intros; apply GlobalTheory.Mum.exists_finExt_lbExt_of_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisationOfTraitUnifStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteExtension_uniformisation_of_trait_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G'), IsGrpPullback G' G (spMap φ) β → LBIso U'.LG.L (P.L.L.pull β) → Nonempty (IsPullDeg φ D.toPre D'.toPre) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β₁ : G₁.left ⟶ G.left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β₁ ∧ LBIso U₁.LG.L (P.L.L.pull β₁) := by
  first | exact @GlobalTheory.Mum.Ident.exists_finExt_unif | exact GlobalTheory.Mum.Ident.exists_finExt_unif | (intros; apply GlobalTheory.Mum.Ident.exists_finExt_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteMarkedLatticePeriodRepresentativesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_markedLattice_period_representatives : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 0 < N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → FineAt F (RingHom.id ℂ) ρ N C → ∃ (n : ℕ) (Di : Fin n → PLat O bar) (t : ∀ i, Λ → (Di i).La), (∀ i, C (Di i) (t i) ∧ ∃ P, IsPeriod (Di i) ρ P) ∧ (∀ D' t', C D' t' → (∃ P, IsPeriod D' ρ P) → ∃ i w, IsMarkedIsom N D' (Di i) t' (t i) w) ∧ ∀ i j w, IsMarkedIsom N (Di i) (Di j) (t i) (t j) w → i = j := by
  first | exact @GlobalTheory.PELU.exists_finite_representatives | exact GlobalTheory.PELU.exists_finite_representatives | (intros; apply GlobalTheory.PELU.exists_finite_representatives <;> assumption)
end

