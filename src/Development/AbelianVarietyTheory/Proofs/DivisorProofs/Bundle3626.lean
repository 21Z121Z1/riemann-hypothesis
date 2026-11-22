import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3622
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3484
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3602
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3624
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3623
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3197

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanSelfIntersectionNonnegStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithKleiman_selfIntersection_nonneg : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D → (∀ (C : HermLB p) (h : X → ℝ), C.IsNef D → C.IsArithHeight h → ∀ z, z ≠ genericPoint X → 0 ≤ h z) → ∀ (C : HermLB p) (c : ℝ), C.IsNef D → C.IsSelfInter c → 0 ≤ c := by
  first | exact @GlobalTheory.KleimanStep.selfInter_nonneg | exact GlobalTheory.KleimanStep.selfInter_nonneg | (intros; apply GlobalTheory.KleimanStep.selfInter_nonneg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadAtFromInputsStatement
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
theorem _root_.GlobalTheory.T.bad_at_from_inputs : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal → Gram → DeepGood → Size → FlatDeg → Deg → Share → Covers fun _ _ _ _ p i _ _ _ => BadAt p i := by
  first | exact @GlobalTheory.BadIndef.bad_rows_indef | exact GlobalTheory.BadIndef.bad_rows_indef | (intros; apply GlobalTheory.BadIndef.bad_rows_indef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyIsPointRigidTautologicalChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem isTautB_of_canon : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), Canon C → (∃ hm : C.m = m, ∀ i, C.s i = bdParam k m e (Fin.cast hm i)) → IsTautB C := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hnsi k _ m e C hC hms
  obtain ⟨hm, hs⟩ := hms
  have hB : GlobalTheory.Mum.Base (ChartRing k m e) := GlobalTheory.ChartQF.base_chartRing C.toFam
  have hR : HasRigidCoords C := GlobalTheory.T.canonicalFamily_has_pointRigid_coordinates Xo c φ (ChartRing k m e) hB C hC
  obtain ⟨hft, hdim⟩ := GlobalTheory.T.canonicalChart_residueField_dimension Xo c φ C hC
  obtain ⟨N, s, ε, τ₀, h1, h2, h3, h4, -⟩ := id hR
  exact ⟨⟨hm, hs, GlobalTheory.T.openPart_classified_monomialBoundaryFamily Xo c φ _ hB C, GlobalTheory.T.canonicalFamily_localInjections_eq_same_point Xo c φ hpq hfan hnsi _ hB C hC,
    ⟨GlobalTheory.T.canonical_data_rigid_along_stratum Xo c φ _ hB C hC, GlobalTheory.T.isPointRigidBoundaryFamily_of_rigidCoordinates Xo c φ _ C hR, hft⟩, ⟨N, s, ε, τ₀, h1, h2, h3, h4⟩, hdim⟩, hR⟩

end GlobalTheory.UCanon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTorsionPointPolarisedFibreImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.ConjFib

theorem isGrpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.Poinc.Sep.ConjFib

open GlobalTheory.Poinc.Sep.ConjFib in

theorem GlobalTheory.Poinc.Sep.conj_fibre_iso : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ') (lam : Sp V ⟶ F'.X) (β : Q.B.left ⟶ F'.univ.A.left) (β₂ : (G2 Q.B).left ⟶ (G2 F'.univ.A).left), 1 ≤ n' → DefOver k₀ (spMap (ev.comp ρ) ≫ lam ≫ F'.s) → IsGrpPullback Q.B F'.univ.A lam β → IsSquare β β₂ → LBIso (abelian₂ Q.B Q.M.L) (F'.univ.P.pull β₂) → ∀ (φ₀₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 F'.univ.A).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ)) ≫ β) φ₀₂ → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∀ (a : Q.X) (p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left → p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = 𝟙 _ → ∃ (x' : Sp K ⟶ F'.X) (φ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ F'.univ.A.left) (φ₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 F'.univ.A).left), x' ≫ F'.s = spMap (ev.comp ρ) ≫ lam ≫ F'.s ∧ IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) F'.univ.A x' φ ∧ IsSquare φ φ₂ ∧ LBIso (F'.univ.P.pull φ₀₂) (F'.univ.P.pull φ₂) ∧ spMap σ.toRingHom ≫ p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) ≫ β = p ≫ φ := by
  intro g l hl hlo W hW
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.polarisedAbelianPart_fibre_conjugate_iso_mumford g l hl hlo W hW
  refine ⟨j₀, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K _ _ ev k₀ hk₀ hu o' _ ζ' g' n' F' lam β β₂ hn' hdef hpb hsq hLB φ₀₂ hsq0 σ hσ a p hpf hps
  obtain ⟨f, f₂, hf, hfs, hfL, hfp⟩ :=
    hj₀ j hj V V₁ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K ev k₀ hk₀ hu σ hσ a p hpf hps
  obtain ⟨hpbσ, φσ₂, hsqσ⟩ := GlobalTheory.T.isGrpPullback_baseChange_with_square F'.univ.A Q.B lam β hpb (spMap (σ.toRingHom.comp (ev.comp ρ)))
  obtain ⟨-, ψ₀, hψ₀⟩ := GlobalTheory.T.isGrpPullback_baseChange_with_square Q.B Q.B (𝟙 _) (𝟙 _) (isGrpPullback_self Q.B) (spMap (ev.comp ρ))
  obtain ⟨-, ψσ, hψσ⟩ := GlobalTheory.T.isGrpPullback_baseChange_with_square Q.B Q.B (𝟙 _) (𝟙 _) (isGrpPullback_self Q.B)
    (spMap (σ.toRingHom.comp (ev.comp ρ)))
  rw [Category.comp_id] at hψ₀ hψσ
  refine ⟨spMap (σ.toRingHom.comp (ev.comp ρ)) ≫ lam, f ≫ pullback.fst Q.B.hom _ ≫ β, f₂ ≫ φσ₂, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨P₀, hP₀⟩ := hdef
    have hk : (σ.toRingHom).comp k₀.subtype = k₀.subtype := by
      ext r; exact hσ r r.2
    have hk' : spMap σ.toRingHom ≫ spMap k₀.subtype = spMap k₀.subtype := by
      rw [← spMap_comp', hk]
    rw [spMap_comp' (ev.comp ρ) σ.toRingHom]
    simp only [Category.assoc]
    rw [← hP₀, ← Category.assoc, hk']
  · simpa only [Category.id_comp] using hf.comp hpbσ
  · exact ⟨by rw [Category.assoc, hsqσ.1, ← Category.assoc, hfs.1, Category.assoc],
      by rw [Category.assoc, hsqσ.2, ← Category.assoc, hfs.2, Category.assoc]⟩
  · have e0 : φ₀₂ = ψ₀ ≫ β₂ := by
      apply pullback.hom_ext
      · change φ₀₂ ≫ (fst F'.univ.A F'.univ.A).left = (ψ₀ ≫ β₂) ≫ (fst F'.univ.A F'.univ.A).left
        rw [hsq0.1, Category.assoc, hsq.1, ← Category.assoc ψ₀, hψ₀.1, Category.assoc]
      · change φ₀₂ ≫ (snd F'.univ.A F'.univ.A).left = (ψ₀ ≫ β₂) ≫ (snd F'.univ.A F'.univ.A).left
        rw [hsq0.2, Category.assoc, hsq.2, ← Category.assoc ψ₀, hψ₀.2, Category.assoc]
    have eσ : φσ₂ = ψσ ≫ β₂ := by
      apply pullback.hom_ext
      · change φσ₂ ≫ (fst F'.univ.A F'.univ.A).left = (ψσ ≫ β₂) ≫ (fst F'.univ.A F'.univ.A).left
        rw [hsqσ.1, Category.assoc, hsq.1, ← Category.assoc ψσ, hψσ.1, Category.assoc]
      · change φσ₂ ≫ (snd F'.univ.A F'.univ.A).left = (ψσ ≫ β₂) ≫ (snd F'.univ.A F'.univ.A).left
        rw [hsqσ.2, Category.assoc, hsq.2, ← Category.assoc ψσ, hψσ.2, Category.assoc]
    have hP := F'.univ.isLB
    have hΛ : (abelian₂ Q.B Q.M.L).IsLB := LB.isLB_linComb (RigLB.isLB Q.M) _ _
    have hA := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hLB ψ₀ (a' := ψ₀ ≫ β₂) rfl
    have hB := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hLB (f₂ ≫ ψσ) (a' := f₂ ≫ φσ₂) (by rw [eσ, Category.assoc])
    rw [e0]
    exact LBIso.trans (pull_isLB hP _) (pull_isLB hΛ _) (pull_isLB hP _) (LBIso.symm hA)
      (LBIso.trans (pull_isLB hΛ _) (pull_isLB hΛ _) (pull_isLB hP _) (hfL ψ₀ ψσ hψ₀ hψσ) hB)
  · have h5 := congrArg (· ≫ β) hfp
    simp only [Category.assoc] at h5
    exact h5.symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataConstantOfFlatHeatOperatorsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationData_constant_of_flat_heatOperators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ c : ℚ, c ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m d) gam ρ (fun i => (c : k) * MvPowerSeries.constantCoeff (q i)) := by
  first | exact @GlobalTheory.KSFlatPer.isConstAlong_of_heat_flat | exact GlobalTheory.KSFlatPer.isConstAlong_of_heat_flat | (intros; apply GlobalTheory.KSFlatPer.isConstAlong_of_heat_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVROfFiniteEtaleBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_of_finite_etale_baseChange : ∀ (A R V : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (ρ : A →+* R) (ψ : A →+* V), IsLocalHom ρ → ρ.Finite → ρ.Etale → IsCN V → IsDiscreteValuationRing V → IsLocalHom ψ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : R →+* V'), IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp ρ = f.comp ψ := by
  first | exact @GlobalTheory.HenselLift.exists_dvr_of_finite_etale | exact GlobalTheory.HenselLift.exists_dvr_of_finite_etale | (intros; apply GlobalTheory.HenselLift.exists_dvr_of_finite_etale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeParametersBoundStatement
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
theorem _root_.GlobalTheory.T.exists_degree_parameters_bound : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, ∃ n Λ β ΛD ΛT J : ℝ, 1 ≤ n ∧ 1 ≤ Λ ∧ 1 ≤ β ∧ 1 ≤ ΛD ∧ 1 ≤ ΛT ∧ Real.log n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ Real.log ΛD ≤ PP * kap p i ∧ Real.log ΛT ≤ PP * kap p i ∧ J ≤ 4 * (CompHt.dimFlag (dat p i) * PP * (kap p i / lenT p i PP + 1) + lenT p i PP * PP) + 2 * PP * (kap p i / lenT p i PP) * CompHt.dimFlag (dat p i) ∧ Formalism.NormVectorIdentities.Items.HSClaimS 26 (lenT p i PP) (CompHt.dimFlag (dat p i)) n 1 Λ β ΛD ΛT J (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.ht (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) (Y.rkC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) (Y.degC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) Z) := by
  first | exact @GlobalTheory.HSShortRun.hsClaim_short | exact GlobalTheory.HSShortRun.hsClaim_short | (intros; apply GlobalTheory.HSShortRun.hsClaim_short <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalStructureOfGenericPolarisationE
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.EvenPackage

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'}

theorem jK_sq (hρ : Function.Injective ρ) : jK R' ≫ spMap ρ =
    spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R := by
  simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp [IsFractionRing.map, IsLocalization.map_eq]

theorem exists_genericMap (hρ : Function.Injective ρ) {G : Over (Sp R)} {G₁ : Over (Sp R')} {β : G₁.left ⟶ G.left}
    (w : β ≫ G.hom = G₁.hom ≫ spMap ρ) : ∃ κ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R),
      κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β := by
  refine ⟨pullback.lift _ (pullback.snd _ _ ≫
    spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) ?_, pullback.lift_fst _ _ _⟩
  rw [Category.assoc, w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, jK_sq hρ]

theorem isGrpPullback_generic (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G] {G₁ : Over (Sp R')} [GrpObj G₁]
    {β : G₁.left ⟶ G.left} {κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)}
    (hβ : IsGrpPullback G₁ G (spMap ρ) β) (hκf : κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β) :
    IsGrpPullback ((Over.pullback (jK R')).obj G₁) ((Over.pullback (jK R)).obj G)
      (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) κ₁ := by
  have hsq := jK_sq hρ
  have hmono : Mono (jK R) := EvenDesc.mono_jK R
  have w : κ₁ ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK R')).obj G₁).hom ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) := by
    apply (cancel_mono (jK R)).1
    rw [Category.assoc, Category.assoc]
    change κ₁ ≫ pullback.snd G.hom (jK R) ≫ jK R = pullback.snd G₁.hom (jK R') ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R
    rw [← pullback.condition, ← Category.assoc, hκf, Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition,
      Category.assoc, hsq]
  exact (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback G₁ (jK R')).comp hβ).congr hsq hκf.symm) w

theorem exists_square_extLam (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {G₁ : Over (Sp R')} [GrpObj G₁] [IsCommMonObj G₁]
    {β : G₁.left ⟶ G.left} {κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)}
    (hβ : IsGrpPullback G₁ G (spMap ρ) β) (hκf : κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β)
    (L : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left) (hL : L.IsLB) (hExt : ExtLam G L PP) :
    ∃ β₂ : (G2 G₁).left ⟶ (G2 G).left, Geo.Tor.IsSquare β β₂ ∧ ExtLam G₁ (L.pull κ₁) (PP.pull β₂) := by
  have hκ := isGrpPullback_generic hρ hβ hκf
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK R')).obj G₁) := Functor.isCommMonObj_obj
  obtain ⟨β₂κ, hsqκ, Hκ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G₁) κ₁ hκ
  obtain ⟨β₂, hsqβ, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G G₁ β hβ
  obtain ⟨g₂, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _ (isGrpPullback_pullback G (jK R))
  refine ⟨β₂, hsqβ, pull_isLB hExt.1 β₂, fun κ₂ hκ₂ => ?_⟩
  have hN := pull_isLB hL κ₁
  have H1 := Hκ L (L.pull κ₁) _ PP g₂ hL hN hExt.1 (GlobalTheory.PolBaseChange.lbIso_refl hN) (hExt.2 g₂ hg₂)
  have e : β₂κ ≫ g₂ = κ₂ ≫ β₂ := by
    apply pullback.hom_ext
    · show (β₂κ ≫ g₂) ≫ (fst G G).left = (κ₂ ≫ β₂) ≫ (fst G G).left
      rw [Category.assoc, hg₂.1, ← Category.assoc, hsqκ.1, Category.assoc, hκf, Category.assoc, hsqβ.1,
        reassoc_of% hκ₂.1]
    · show (β₂κ ≫ g₂) ≫ (snd G G).left = (κ₂ ≫ β₂) ≫ (snd G G).left
      rw [Category.assoc, hg₂.2, ← Category.assoc, hsqκ.2, Category.assoc, hκf, Category.assoc, hsqβ.2,
        reassoc_of% hκ₂.2]
  exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (pull_isLB hExt.1 _) (pull_isLB (pull_isLB hExt.1 _) _) H1
    (LBIso.chartPull (chartPullSame PP _ (fun _ => β₂) _ κ₂ fun _ => e) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hExt.1 β₂)))

theorem exists_generic_pol (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G]
    {G₁ : Over (Sp R')} [GrpObj G₁]
    {β : G₁.left ⟶ G.left} {κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)}
    (hβ : IsGrpPullback G₁ G (spMap ρ) β) (hκf : κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β)
    (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A) (hgen : IsMonHom gen.hom) :
    ∃ (A' : PolAV (Sp (FractionRing R'))) (gen' : (Over.pullback (jK R')).obj G₁ ≅ A'.A), IsMonHom gen'.hom ∧
      LBIso (A'.L.pull gen'.hom.left) ((A.L.pull gen.hom.left).pull κ₁) := by
  have hκ := isGrpPullback_generic hρ hβ hκf
  obtain ⟨A', gA, pA, -, mA, tA⟩ := GlobalTheory.polBaseChange_holds _ _
    (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) gA :=
    ⟨pA, fun T x y x₀ y₀ hx hy => by
      have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
      have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
      rw [e₁, e₂, ← mA]; rfl⟩
  have tA' : LBIso (A.L.pull gA) A'.L := tA
  obtain ⟨e, he, hee⟩ := grpPullback_iso ((hκ.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl) gpA
  refine ⟨A', e, he, ?_⟩
  exact LBIso.trans (pull_isLB A'.isLB _) (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _)
    (GlobalTheory.GenSpread.lbIso_pull_of_lbIso tA'.symm e.hom.left hee.symm)
    (GlobalTheory.GenSpread.lbIso_pull_pull A.isLB κ₁ rfl)

end GlobalTheory.Mum.EvenPackage

set_option maxHeartbeats 1000000 in
open GlobalTheory.Mum.EvenPackage in

theorem GlobalTheory.Mum.exists_even_package_of_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∀ (R₃ : Type) [CommRing R₃] [IsDomain R₃] [IsLocalRing R₃] (ρ₃ : R →+* R₃) (G₃ : Over (Sp R₃)) [GrpObj G₃] [IsCommMonObj G₃] (β₃ : G₃.left ⟶ G.left) (κ₃ : pullback G₃.hom (jK R₃) ⟶ pullback G.hom (jK R)) (L₃ : LB G₃.left), FinExt ρ₃ → IsGrpPullback G₃ G (spMap ρ₃) β₃ → κ₃ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β₃ → L₃.IsLB → LBIso (L₃.pull (pullback.fst G₃.hom (jK R₃))) ((A.L.pull gen.hom.left).pull κ₃) → ∃ (R₉ : Type) (_ : CommRing R₉) (_ : IsDomain R₉) (_ : IsLocalRing R₉) (ρ : R →+* R₉) (G₉ : Over (Sp R₉)) (_ : GrpObj G₉) (_ : IsCommMonObj G₉) (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ ∧ IsGrpPullback G₉ G (spMap ρ) β₉ ∧ Geo.Tor.IsSquare β₉ β₉₂ ∧ IsSemiAbelian G₉ ∧ LBIso (abelian₂ G₉ P.L.L) (PP.pull β₉₂) ∧ EvenOn P ∧ IsMonHom gen₉.hom ∧ LBIso (A₉.L.pull gen₉.hom.left) (P.L.L.pull (pullback.fst G₉.hom (jK R₉))) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP W _ _ _ φ GW _ _ βW DW AW UW κ hW hφi hφl hGW hκ hUW
    R₃ _ _ _ ρ₃ G₃ _ _ β₃ κ₃ L₃ hρ₃ hβ₃ hκ₃ hL₃ hL₃g
  have hR₃ : Base R₃ := by
    haveI := hR.2
    exact ⟨hρ₃.1, charZero_of_injective_ringHom hρ₃.2.1⟩
  have hG₃ : IsSemiAbelian G₃ := EvenDesc.isSemiAbelian_of_isGrpPullback hβ₃ hG
  obtain ⟨R₉, i1, i2, i3, ρ₄, G₉, i4, i5, β₄, X, i6, i7, i8, hρ₄, hβ₄, hTQ⟩ :=
    exists_finExt_tq_closedFibre R₃ hR₃ G₃ hG₃
  have hρ : FinExt (ρ₄.comp ρ₃) := ⟨hρ₄.1, hρ₄.2.1.comp hρ₃.2.1, hρ₄.2.2.comp hρ₃.2.2⟩
  have hβ : IsGrpPullback G₉ G (spMap (ρ₄.comp ρ₃)) (β₄ ≫ β₃) :=
    (hβ₄.comp hβ₃).congr (TraitExt.spMap_comp _ _) rfl
  have hG₉ : IsSemiAbelian G₉ := EvenDesc.isSemiAbelian_of_isGrpPullback hβ hG
  obtain ⟨κ₄, hκ₄⟩ := exists_genericMap hρ₄.2.1 hβ₄.1.w
  have hκ₉ : (κ₄ ≫ κ₃) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β₄ ≫ β₃ := by
    rw [Category.assoc, hκ₃, ← Category.assoc, hκ₄, Category.assoc]
  have hN : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _
  have hL₉ : (L₃.pull β₄).IsLB := pull_isLB hL₃ _
  have hL₉g : LBIso ((L₃.pull β₄).pull (pullback.fst G₉.hom (jK R₉))) ((A.L.pull gen.hom.left).pull (κ₄ ≫ κ₃)) :=
    LBIso.trans (pull_isLB hL₉ _) (pull_isLB hL₃ _) (pull_isLB hN _)
      (GlobalTheory.GenSpread.lbIso_pull_pull hL₃ (pullback.fst G₉.hom (jK R₉)) rfl).symm
      (GlobalTheory.GenSpread.lbIso_pull_comp κ₄ hκ₄.symm rfl hL₃g)
  obtain ⟨A₉, gen₉, hgen₉, hA₉⟩ := exists_generic_pol hρ.2.1 hβ hκ₉ A gen hgen
  have hA₉' : LBIso (A₉.L.pull gen₉.hom.left) ((L₃.pull β₄).pull (pullback.fst G₉.hom (jK R₉))) :=
    LBIso.trans (pull_isLB A₉.isLB _) (pull_isLB hN _) (pull_isLB hL₉ _) hA₉ hL₉g.symm
  have hprop : IsProper (pullback.snd G₉.hom (jK R₉)) := by
    have hi : IsIso gen₉.hom.left := ((Over.forget _).mapIso gen₉).isIso_hom
    have := A₉.isAb.proper
    have hw : pullback.snd G₉.hom (jK R₉) = gen₉.hom.left ≫ A₉.A.hom := (Over.w gen₉.hom).symm
    rw [hw]; infer_instance
  have hsym := GlobalTheory.sym_of_lbIso_pull_hom _ _ _ gen₉.hom hgen₉ _ _ A₉.isLB (pull_isLB hL₉ _) A₉.sym hA₉'
  haveI : IsNoetherianRing R₉ := hρ.1.1
  haveI : IsIntegrallyClosed R₉ := hρ.1.2.2.1
  obtain ⟨P, hP⟩ := GlobalTheory.CubSymPkg.exists_cp_of_generic_sym R₉ G₉ hG₉ hprop _ hL₉ hsym
  obtain ⟨β₂, hsq, hE⟩ := exists_square_extLam hρ.2.1 hβ hκ₉ _ PP hN hPP
  refine ⟨R₉, i1, i2, i3, ρ₄.comp ρ₃, G₉, i4, i5, β₄ ≫ β₃, β₂, P, A₉, gen₉, hρ, hβ, hsq, hG₉, ?_, ?_, hgen₉, ?_⟩
  · rw [hP]
    exact lbIso_lam_of_extLam R₉ G₉ hG₉ _ _ _ hL₉ (pull_isLB hN _) hL₉g.symm hE
  · refine evenOn_of_trait_unif R hR G hG A gen hgen W φ GW βW DW AW UW κ hW hφi hφl hGW hκ hUW R₉ _ G₉ _ _ P hρ hβ hκ₉
      ?_ X hTQ
    rw [hP]; exact hL₉g
  · rw [hP]; exact hA₉'

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeMapHarrisTaylorIntegralModelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_isHeckeMap) | (exact GlobalTheory.UPel.HT.Hecke.exists_isHeckeMap) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_isHeckeMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAffineOpenAbelianPullbackStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kodairaSpencer_affine_open_abelian_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens), U.1 ≤ V → ∀ (t' : SAB H (Sp Γ(X, U.1))), Nonempty (SABMap t' t (chart U)) → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ D : Derivation ℤ Γ(X, U.1) Γ(X, U.1), ∃ Θ, IsKS t V U v D Θ := by
  first | exact @GlobalTheory.KSOpen.exists_isKS_of_pull | exact GlobalTheory.KSOpen.exists_isKS_of_pull | (intros; apply GlobalTheory.KSOpen.exists_isKS_of_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerInteriorAffineOpenStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kodairaSpencer_interior_affine_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (W : Y.X.affineOpens), W.1 ≤ interior Y → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, W.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart W) (v i)) → (∀ w, IsTanAtG Y.t (chart W) w → ∃! cf : Fin n → Γ(Y.X, W.1), IsCombAtG Y.t (chart W) v cf w) → ∀ D : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1), ∃ Θ, IsKS Y.t (interior Y) W v D Θ := by
  first | exact @GlobalTheory.KSInterior.exists_isKS_interior | exact GlobalTheory.KSInterior.exists_isKS_interior | (intros; apply GlobalTheory.KSInterior.exists_isKS_interior <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledCoverUnitaryPELTypeFiniteExt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_odd_prime_isUnit_in_localRing (R : Type) [CommRing R] [IsLocalRing R] :
    ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : R) := by
  have h : IsUnit ((2 : R) * (3 : ℕ) + (-1) * (5 : ℕ)) := by
    have : (2 : R) * (3 : ℕ) + (-1) * (5 : ℕ) = 1 := by push_cast; ring
    rw [this]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, Nat.prime_three, by decide, isUnit_of_mul_isUnit_right h⟩
  · exact ⟨5, Nat.prime_five, by decide, isUnit_of_mul_isUnit_right h⟩

theorem exists_labCover_of_pelOK : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ Nonempty (LabCover D') := by
  intro R _ _ _ hR E _ _ _ H Dm D _ o hX hP
  have := hR.1.1
  have := hR.2
  obtain ⟨n, hn, ho, hu⟩ := exists_odd_prime_isUnit_in_localRing R
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R (maximalIdeal R)
  have hloc : IsLocalHom φ := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ (maximalIdeal V).comap φ := by rw [hc]; exact hna
    exact h1 ha⟩
  obtain ⟨DV, ⟨hDV⟩⟩ := GlobalTheory.MumPull.exists_pull R V φ hφ hloc D
  obtain ⟨_, oV, hPV⟩ := GlobalTheory.Mum.pelOK_of_isPullDeg R hR E H Dm D o hP V φ hφ DV ⟨hDV⟩
  have hXV : Nontrivial DV.toPre.X := hDV.xe.toEquiv.nontrivial
  obtain ⟨V', _, _, _, io, D', G', _, _, A', hV', hio, hfin, hD', hG', hU', hS'⟩ := GlobalTheory.T.exists_mumfordUniformisation_unitaryTypeTrait V hV E H Dm DV oV hXV hPV
  have hioloc : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  obtain ⟨R₁, _, _, _, ρ₁, D₁, A, lab, hf₁, hD₁, hS, h1, h2⟩ := GlobalTheory.T.exists_labelledSemiAbelianCover_finite_extension R hR D n hn ho hu V' hV' (io.comp φ)
    (hio.comp hφ) inferInstance D' G' A'
    (GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R V V' φ io _ _ _ hio ⟨hDV⟩ hD') hG' hU' hS'
  have hR₁ : Base R₁ := ⟨hf₁.1, charZero_of_injective_ringHom hf₁.2.1⟩
  have := hR₁.2
  obtain ⟨R₂, _, _, _, ρ₂, C, a, hf₂, hfib⟩ := GlobalTheory.T.exists_uniformised_cover_finite_ext_of_symmetric R₁ hR₁ A hS
  have hR₂ : Base R₂ := ⟨hf₂.1, charZero_of_injective_ringHom hf₂.2.1⟩
  obtain ⟨D₂, hD₂⟩ := GlobalTheory.MumPull.exists_pull R₁ R₂ ρ₂ hf₂.2.1 (hf₂.2.2.to_isIntegral.isLocalHom hf₂.2.1) D₁
  obtain ⟨lab₂, k1, k2⟩ := GlobalTheory.T.exists_torsionLabels_finiteExtension_galoisEquivariant R₁ hR₁ D₁ A lab n h1 h2 R₂ ρ₂ hf₂ D₂ hD₂ C.A a hfib hn.pos
  have hu₂ : IsUnit (n : R₂) := by simpa using hu.map (ρ₂.comp ρ₁)
  exact ⟨R₂, _, _, _, ρ₂.comp ρ₁, D₂, ⟨hf₂.1, hf₂.2.1.comp hf₁.2.1, hf₂.2.2.comp hf₁.2.2⟩,
    GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R R₁ R₂ ρ₁ ρ₂ _ _ _ hf₂.2.1 hD₁ hD₂,
    GlobalTheory.T.nonempty_labelled_cover_of_odd_prime R₂ hR₂ D₂ C lab₂ n hn ho hu₂ k1 k2⟩

end GlobalTheory.Mum
end
end

