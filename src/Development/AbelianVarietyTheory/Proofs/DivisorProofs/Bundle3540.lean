import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3523
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3491
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3522
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3519
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelTorsionPointOfComesFromBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DivSol

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

def mulPull {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') (n : ℕ) :
    IsPullDeg φ (mulDeg D n) (mulDeg D' n) where
  e := hD.e
  e_hom := hD.e_hom
  w := hD.w
  w_gen := hD.w_gen
  he := hD.he
  w_rig := hD.w_rig
  xe := hD.xe
  c_pr := fun (x : D'.X) => by
    have hx : hD.xe (n • x) = n • hD.xe x := map_nsmul hD.xe n x
    show (D'.c (n • x)).left ≫ _ = specOf φ ≫ (D.c (n • hD.xe x)).left
    rw [← hx]
    exact hD.c_pr (n • x)
  W := hD.W
  psiW := ⟨fun (χ : D.X) => hD.psiW.psi (n • χ), fun (χ : D.X) => hD.psiW.psi_gen (n • χ), fun (χ : D.X) => hD.psiW.psi_eq (n • χ)⟩
  g := hD.g
  g_comm := hD.g_comm
  psi_pr := fun (x : D'.X) => by
    have h := hD.psi_pr (n • x)
    have hx : hD.xe (n • x) = n • hD.xe x := map_nsmul hD.xe n x
    rw [hx] at h
    exact h

theorem mulDeg_psiEven (D : DegPre R) (n : ℕ) (h : D.PsiEven) : (mulDeg D n).PsiEven :=
  fun (a : D.X) => MulDeg.corr_even_degenerationData_negPoint D h (n • a) (n • (-a)) (neg_nsmul a n)

theorem mulDeg_tauBimult (D : DegPre R) (n : ℕ) (h : D.TauBimult) : (mulDeg D n).TauBimult :=
  fun (a a' b : D.X) => MulDeg.corr_bimultiplicative_degenerationData_sums D h (n • a) (n • a') (n • b) (n • (a + a')) (n • (a + a' + b)) (n • (a + b))
    (n • (a' + b)) (nsmul_add _ _ _) (by rw [nsmul_add, nsmul_add]) (nsmul_add _ _ _) (nsmul_add _ _ _)

theorem mulDeg_psiUnitOn (D : DegPre R) (n : ℕ) (h : ∀ y, PsiUnitOn D y Set.univ) :
    ∀ y, PsiUnitOn (mulDeg D n) y Set.univ :=
  fun (y : D.X) => h (n • y)

end GlobalTheory.DivSol

namespace GlobalTheory.DivSol

theorem exists_qkPt_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ y : P.D.toPre.X, ∃ p₀ : QkPt P.D.toPre (FractionRing R) l.M', p₀.y = y := by
  intro E _ _ _ H D' l c L R _ _ _ _hB t P iw I _ s ε e _hbal hs hdf y
  obtain ⟨g, hD, hg, -, -⟩ := hdf
  obtain ⟨DR, hR, -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg polBaseChange_holds L.W R iw L.D ⊤
    (GlobalTheory.ArcPull.nonempty_psiOn_top L.D L.gen) trivial
  have hbiR : DR.TauBimult := GlobalTheory.tauBimult_of_isPullDeg globalFns_holds _ _ iw L.D DR hR L.bimult
  have hunR : ∀ y, PsiUnitOn DR y Set.univ := GlobalTheory.PullDegTop.psiUnitOn_univ hR L.gen
  have hevR : DR.PsiEven := GlobalTheory.PsiEvenPull.psiEven_pull globalFns_holds _ _ iw L.D DR hR L.even
  have hC : IsPullDeg (RingHom.id R) (mulDeg DR l.M') (GlobalTheory.PolDeg.rescale P.D.toPre g) :=
    (GlobalTheory.Mum.isPullDeg_unique_any L.W R iw (mulDeg L.D l.M') _ _ ⟨mulPull hR l.M'⟩ ⟨hD⟩).some
  obtain ⟨T, ib, β, ββ, w, hF⟩ := GlobalTheory.T.exists_tautologicalBase_nsmul_degenerationData (RingHom.id R) DR hbiR hunR l.M'
  let e' : P.D.toPre.X ≃+ (Fin T.r → ℤ) := hC.xe.trans ib
  let x : (Fin T.r → ℤ) ≃+ L.D.X := e'.symm.trans e.toAddEquiv
  have hx : ∀ a, x (e' a) = e a := fun a => by simp [x]
  let ε' : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ) := fun k =>
    LinearMap.mk₂ ℤ (fun u v => ε k (x u) (H.w0 • x v) + ε k (x v) (H.w0 • x u))
      (fun m₁ m₂ n => by simp only [map_add, smul_add, LinearMap.add_apply]; ring)
      (fun c m n => by
        simp only [map_zsmul, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
        rw [smul_comm H.w0 c (x m)]
        simp only [LinearMap.map_smul, smul_eq_mul]; ring)
      (fun m n₁ n₂ => by simp only [map_add, smul_add, LinearMap.add_apply]; ring)
      (fun c m n => by
        simp only [map_zsmul, LinearMap.smul_apply, LinearMap.map_smul, smul_eq_mul]
        rw [smul_comm H.w0 c (x n)]
        simp only [LinearMap.map_smul, smul_eq_mul]; ring)
  have hne : ∀ i, algebraMap R (FractionRing R) (s i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hs i)
  have hgv : ∀ y, ((g y : (FractionRing R)ˣ) : FractionRing R) =
      (∏ k, algebraMap R (FractionRing R) (s k) ^ ((l.M' : ℤ) * ε k (e y) (H.w0 • e y)))⁻¹ := fun y => by
    rw [← hg y, Units.val_inv_eq_inv_val, inv_inv]
  have hcoc : ∀ a a' : P.D.toPre.X, (((g (a + a'))⁻¹ * g a * g a' : (FractionRing R)ˣ) : FractionRing R) =
      ∏ i, algebraMap R (FractionRing R) (s i) ^ ((l.M' : ℤ) * ε' i (e' a) (e' a')) := by
    intro a a'
    rw [Units.val_mul, Units.val_mul, hg (a + a'), hgv a, hgv a', ← Finset.prod_inv_distrib,
      ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ (hne i), ← zpow_add₀ (hne i)]
    congr 1
    simp only [ε', LinearMap.mk₂_apply, hx, map_add, smul_add, LinearMap.add_apply]
    ring
  obtain ⟨β', ββ', w', hF'⟩ := GlobalTheory.T.comesFromTautBase_of_rescaled_pullback_monomial T l.M' (mulDeg DR l.M') (mulDeg_psiEven _ _ hevR)
    (mulDeg_tauBimult _ _ hbiR) (mulDeg_psiUnitOn _ _ hunR) ib β ββ w hF R (RingHom.id R) Function.injective_id
    P.D.toPre g hC s ε' e' (fun _ => rfl) hcoc
  obtain ⟨p, hp, -⟩ := GlobalTheory.TInj.exists_qkPt_tautPt T ε' l.M' R P.D.toPre (RingHom.id R) s e' β' ββ' w'
    P.D.tau_bimult hF' hs (FractionRing R) (e' y)
  exact ⟨p, by rw [hp]; simp⟩

end GlobalTheory.DivSol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspFormStatement
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
theorem _root_.GlobalTheory.T.exists_nonzero_cusp_form : GlobalTheory.Published.ScholzeWeinsteinB → Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → Covers fun Fm x _ ι p i Y _ _ => ∃ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ f ∈ cuspOn Y.U Z (wtOf (dat p i) (uM p i) 0), f ≠ 0 := by
  first | exact @GlobalTheory.CovTop.LowNonzero.exists_cusp_uM | exact GlobalTheory.CovTop.LowNonzero.exists_cusp_uM | (intros; apply GlobalTheory.CovTop.LowNonzero.exists_cusp_uM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupFiniteNormalCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USepCov

theorem exists_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (M : Scheme.{0}) [IsIntegral M] (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)), IsCov C g z₁ ζ → ∃ (S₁ : Scheme.{0}) (_ : IsIntegral S₁) (p₁ : S₁ ⟶ M) (sM : M ⟶ Sp ℤ) (U₁ : S₁.Opens), LocallyOfFiniteType sM ∧ QuasiCompact sM ∧ Flat (p₁ ≫ sM) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S₁ ∧ IsProper p₁ ∧ IsDominant p₁ ∧ FinalTheorems.EffCartier (J.comap (p₁ ≫ g)) ∧ (U₁ : Set S₁).Nonempty ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S₁) (ev : M.presheaf.stalk z₁ →+* K), x ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ → Set.range x ⊆ (U₁ : Set S₁) → ∃ y : Sp K ⟶ Xo.XF c, y ≫ C.iF = spMap ev ≫ ζ) ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] (a : Sp R ⟶ S) (ev : M.presheaf.stalk z₁ →+* R), a ≫ π = spMap ev ≫ ζ → Set.range (jK R ≫ a ≫ π) ⊆ Set.range C.iF → ∃ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (ev' : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev' ≫ a) p = a (closedPoint R)) → GlobalTheory.UChart.DefOver k₀ (spMap ev' ≫ a) → (∀ p, (spMap ev' ≫ ξ₁) p = ξ₁ (closedPoint R)) ∧ GlobalTheory.UChart.DefOver k₀ (spMap ev' ≫ ξ₁) := by
  intro E _ _ _ H Dw _ l Xo c C J hJi S π hNB M _ g z₁ ζ hcov
  obtain ⟨hMn, ⟨U, g', hg'fin, hg'U, hUF⟩, hζ, hgen⟩ := hcov
  haveI := hg'fin
  haveI := C.ft
  haveI : Algebra.FiniteType ℤ (CommRingCat.of C.o) := ‹Algebra.FiniteType ℤ C.o›
  haveI : IsNoetherianRing C.o := Algebra.FiniteType.isNoetherianRing ℤ _
  haveI := C.iF_open
  obtain ⟨Z', b, hB, hBproj, -⟩ := GlobalTheory.ProjBlowup.exists_blowup C.z C.proj J
  haveI : IsProper C.z := by
    obtain ⟨m, e, he, he'⟩ := C.proj
    haveI := he
    have := isProper_str C.o m
    rw [← he']
    infer_instance
  haveI : IsProper (b ≫ C.z) := by
    obtain ⟨m, e, he, he'⟩ := hBproj
    haveI := he
    have := isProper_str C.o m
    rw [← he']
    infer_instance
  haveI : IsProper b := IsProper.of_comp b C.z
  obtain ⟨-, S₀, π₀, ν, -, hB₀, hνπ, -, -, -, -⟩ := hNB
  obtain ⟨ψ₀, hψ₀, -⟩ := hB.2 S₀ (π₀ ≫ pullback.fst C.z (spMap C.b))
    (by rw [Scheme.IdealSheafData.comap_comp]; exact hB₀.1)
  have hψU : Set.range ψ₀ ⊆ Set.range (b ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    show b (ψ₀ s) ∈ U
    rw [← Scheme.Hom.comp_apply, hψ₀, Scheme.Hom.comp_apply]
    exact hUF ⟨_, rfl⟩
  let ψU : S₀ ⟶ (b ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (b ⁻¹ᵁ U).ι ψ₀ hψU
  have hψUf : ψU ≫ (b ⁻¹ᵁ U).ι = ψ₀ := IsOpenImmersion.lift_fac _ _ _
  have hψUb : ψU ≫ (b ∣_ U) ≫ U.ι = π₀ ≫ pullback.fst C.z (spMap C.b) := by
    rw [morphismRestrict_ι, ← Category.assoc, hψUf, hψ₀]
  have hpt : ∀ q : Sp (M.presheaf.stalk z₁), g (M.fromSpecStalk z₁ q) = pullback.fst C.z (spMap C.b) (ζ q) := by
    intro q
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hζ]
  haveI := hMn
  haveI : IsDomain (M.presheaf.stalk z₁) := inferInstance
  let p0 : Sp (M.presheaf.stalk z₁) := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨y0, hy0⟩ := hgen p0 rfl
  let m0 : M := M.fromSpecStalk z₁ p0
  have hm0 : g m0 = C.i y0 := by
    rw [hpt, ← hy0]; rfl
  have hgm : ∀ m, g m ∈ Set.range C.i → (g' ≫ U.ι) m ∉ J.support := by
    intro m ⟨y, hy⟩ hJ
    rw [hg'U] at hJ
    exact hJi _ hJ ⟨y, hy⟩
  have hm0J : (g' ≫ U.ι) m0 ∉ J.support := hgm m0 ⟨y0, hm0.symm⟩
  obtain ⟨S₁, hS₁i, p₁, ν₁, hS₁n, hp₁P, hν₁fin, hcomm, hEff, hrange, hlift⟩ :=
    GlobalTheory.T.exists_normalisation_blowup_pullback_finiteCover (o := CommRingCat.of C.o) C.z b J hB U g' ⟨m0, hm0J⟩
  haveI := hν₁fin

  haveI : IsPreimmersion (spMap C.b) := by
    letI := C.b.toAlgebra
    haveI := C.isFractionRing
    exact IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  obtain ⟨W', hW'o, hW'⟩ := ((IsPreimmersion.isEmbedding (pullback.fst C.z (spMap C.b))).isInducing.isOpen_iff).mp
    C.iF.isOpenMap.isOpen_range
  let sM : M ⟶ Sp ℤ := g ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o))
  obtain ⟨x0, hx0⟩ := hrange m0 hm0J
  haveI hSpecZ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  refine ⟨S₁, hS₁i, p₁, sM, (p₁ ≫ g) ⁻¹ᵁ ⟨W', hW'o⟩, ?_, ?_, ?_, hS₁n, hp₁P, ?_, ?_, ?_, ?_, ?_⟩
  · show LocallyOfFiniteType (g ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)))
    rw [← hg'U]
    infer_instance
  · show QuasiCompact (g ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)))
    haveI : IsLocallyNoetherian C.Z := LocallyOfFiniteType.isLocallyNoetherian (C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)))
    rw [← hg'U]
    infer_instance
  · apply GlobalTheory.T.flat_int_of_integral_scheme_generic_point _ x0
    have eM : C.i ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)) =
        (C.iF ≫ pullback.snd C.z (spMap C.b)) ≫ Spec.map (CommRingCat.ofHom (C.b.comp (algebraMap ℤ C.o))) := by
      simp only [UCompact.i, Category.assoc, pullback.condition_assoc]
      rw [← Spec.map_comp]; rfl
    have e : (p₁ ≫ sM) x0 = Spec.map (CommRingCat.ofHom (C.b.comp (algebraMap ℤ C.o))) ((C.iF ≫ pullback.snd C.z (spMap C.b)) y0) := by
      rw [← Scheme.Hom.comp_apply, ← eM]
      show (C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o))) (g (p₁ x0)) = _
      rw [hx0, hm0]
      rfl
    rw [e]
    show Ideal.comap _ _ = ⊥
    haveI := ((C.iF ≫ pullback.snd C.z (spMap C.b)) y0).isPrime
    rw [Ideal.eq_bot_of_prime (((C.iF ≫ pullback.snd C.z (spMap C.b)) y0).asIdeal), Ideal.comap_bot_of_injective]
    exact fun u v h => Int.cast_injective (α := c.F) (by simpa using h)
  · constructor
    have hVo : IsOpen {m : M | (g' ≫ U.ι) m ∉ J.support} :=
      (g' ≫ U.ι).continuous.isOpen_preimage _ J.support.isClosed.isOpen_compl
    exact (hVo.dense ⟨m0, hm0J⟩).mono fun m hm => hrange m hm
  · rw [← hg'U]; exact hEff
  · refine ⟨x0, ?_⟩
    show g (p₁ x0) ∈ W'
    rw [hx0, hpt]
    show ζ p0 ∈ pullback.fst C.z (spMap C.b) ⁻¹' W'
    rw [hW']; exact ⟨y0, hy0⟩
  · intro K _ x ev hx hxU
    have hr : Set.range (spMap ev ≫ ζ) ⊆ Set.range C.iF := by
      rintro _ ⟨w, rfl⟩
      rw [← hW']
      show pullback.fst C.z (spMap C.b) (ζ (spMap ev w)) ∈ W'
      rw [← hpt, ← Scheme.Hom.comp_apply (spMap ev), ← hx, Scheme.Hom.comp_apply]
      exact hxU ⟨w, rfl⟩
    exact ⟨IsOpenImmersion.lift C.iF _ hr, IsOpenImmersion.lift_fac _ _ _⟩
  · intro R _ _ _ _ a ev ha hgR
    let β : Sp R ⟶ M := spMap ev ≫ M.fromSpecStalk z₁
    have hβg : β ≫ g = a ≫ π ≫ pullback.fst C.z (spMap C.b) := by
      simp only [β, Category.assoc, ← hζ]
      rw [← Category.assoc a π, ha, Category.assoc]
    have hab : (a ≫ ν ≫ ψU) ≫ (b ∣_ U) = β ≫ g' := by
      rw [← cancel_mono U.ι, Category.assoc, Category.assoc, Category.assoc, hψUb, Category.assoc, hg'U, hβg,
        ← hνπ, Category.assoc]
    have hgw : ∀ w, (jK R ≫ β ≫ g' ≫ U.ι) w ∉ J.support := by
      intro w
      have e : jK R ≫ β ≫ g' ≫ U.ι = (jK R ≫ a ≫ π) ≫ pullback.fst C.z (spMap C.b) := by
        rw [hg'U, hβg]; simp only [Category.assoc]
      rw [e]
      obtain ⟨y, hy⟩ := hgR ⟨w, rfl⟩
      intro hJ
      refine hJi _ hJ ⟨y, ?_⟩
      show _ = pullback.fst C.z (spMap C.b) ((jK R ≫ a ≫ π) w)
      rw [← hy]; rfl
    obtain ⟨ξ₁, hξν, hξp⟩ := hlift R (a ≫ ν ≫ ψU) β hab hgw
    refine ⟨ξ₁, hξp, ?_⟩
    intro K _ _ ev' k₀ hk₀ hcl hdef
    refine ⟨fun p => ?_, ?_⟩
    · have e1 : ∀ t, ν₁ (ξ₁ t) = ψU (ν (a t)) := fun t => by
        rw [← Scheme.Hom.comp_apply, hξν]; rfl
      apply GlobalTheory.T.eq_of_specializes_same_fibre_isIntegralHom ν₁
      · exact (IsLocalRing.specializes_closedPoint _).map ξ₁.continuous
      · have e2 := e1 (closedPoint R)
        have e3 : a ((spMap ev') p) = a (closedPoint R) := hcl p
        rw [Scheme.Hom.comp_apply, e1, e3]
        exact e2.symm
    · apply GlobalTheory.T.pointDefinedOverSubfield_of_isIntegralHom ν₁ k₀ hk₀
      obtain ⟨P₀, hP₀⟩ := hdef
      refine ⟨P₀ ≫ ν ≫ ψU, ?_⟩
      simp only [Category.assoc, hξν]
      rw [reassoc_of% hP₀]

end GlobalTheory.USepCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapFixingDescendedPointsSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AutLift

theorem spMap_fix (K : Type) [Field K] (k₀ : Subfield K) (σ : K ≃+* K) (h : ∀ a ∈ k₀, σ a = a) :
    spMap (σ : K →+* K) ≫ spMap k₀.subtype = spMap k₀.subtype := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact h x x.2

theorem eta_nsmul {S : Scheme.{0}} {G : Over S} [GrpObj G] {La : Type} [AddCommGroup La] (f : La → (𝟙_ (Over S) ⟶ G))
    (hf : ∀ a c, f (a + c) = f a * f c) (n : ℕ) (a : La) : f (n • a) = f a ^ n := by
  have h0 : f 0 = 1 := by
    have := hf 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem exists_objMap_fixing_descended_points : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} {Bb : Type} [CommRing Bb] {b : Base l Bb} (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ {s : Sp K ⟶ Sp Bb} (o : Obj D l b s) (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (π : o.t.G.left ⟶ B₀.left), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback o.t.G B₀ (spMap k₀.subtype) π → LBIso o.t.PP.L (M₀.pull π) → ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → ∃ n : ObjMap o o (spMap (σ : K →+* K)), ∀ x : Sp K ⟶ o.t.G.left, x ≫ o.t.G.hom = 𝟙 _ → (∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ π = spMap k₀.subtype ≫ x₀) → x ≫ n.toSABMap.φ = spMap (σ : K →+* K) ≫ x := by
  intro E _ _ _ H D l Bb _ b K _ _ _ k₀ hk₀ s o B₀ _ _ M₀ π hB₀ hM₀ hpb hL σ hσ
  haveI : IsAlgClosed k₀ := hk₀
  have hfix := spMap_fix K k₀ σ hσ
  let st : o.t.G.left ⟶ o.t.G.left := hpb.1.lift π (o.t.G.hom ≫ spMap (σ : K →+* K))
    (by rw [hpb.1.w, Category.assoc, hfix])
  have hst₁ : st ≫ π = π := hpb.1.lift_fst _ _ _
  have hst₂ : st ≫ o.t.G.hom = o.t.G.hom ≫ spMap (σ : K →+* K) := hpb.1.lift_snd _ _ _

  have hpt : ∀ x : Sp K ⟶ o.t.G.left, x ≫ o.t.G.hom = 𝟙 _ →
      (∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ π = spMap k₀.subtype ≫ x₀) → x ≫ st = spMap (σ : K →+* K) ≫ x := by
    rintro x hx ⟨x₀, hx₀⟩
    apply hpb.1.hom_ext
    · rw [Category.assoc, hst₁, Category.assoc, hx₀, ← Category.assoc, hfix]
    · rw [Category.assoc, hst₂, ← Category.assoc, hx, Category.assoc, hx, Category.id_comp, Category.comp_id]

  have hcart : IsGrpPullback o.t.G o.t.G (spMap (σ : K →+* K)) st :=
    hpb.cancel (hpb.congr hfix.symm hst₁.symm) hst₂

  have hact : ∀ a, (o.t.act.act a).left ≫ st = st ≫ (o.t.act.act a).left := by
    intro a
    obtain ⟨f₀, -, hf₀⟩ := GlobalTheory.AlgClosedHomDescent.hom_descends k₀ K k₀.subtype B₀ B₀ o.t.G o.t.G π π hB₀ hB₀ hpb hpb
      (o.t.act.act a) (o.t.act.hom a)
    apply hpb.1.hom_ext
    · rw [Category.assoc, hst₁, Category.assoc, ← hf₀, ← Category.assoc, hst₁, hf₀]
    · rw [Category.assoc, hst₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hst₂]

  have hLB : LBIso o.t.PP.L (o.t.PP.L.pull st) := by
    have h1 : LBIso (o.t.PP.L.pull st) (M₀.pull π) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.t.PP.L st st rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame M₀ _ (fun _ => π) _ st fun _ => hst₁.symm) hL
    exact LBIso.trans o.t.PP.isLB (pull_isLB hM₀ π) (pull_isLB o.t.PP.isLB st) hL (LBIso.symm h1)

  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_sabMap_of_grpPullback_respecting_action_bundle o.t o.t (spMap (σ : K →+* K)) st o.proper hcart hact hLB
  have hφ : m.cm.F = st := hm

  have hun : η[o.t.G].left ≫ π = spMap k₀.subtype ≫ η[B₀].left := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left hpb
  have htor : ∀ (y : 𝟙_ (Over (Sp K)) ⟶ o.t.G) (n : ℕ), 0 < n → y ^ n = 1 →
      y.left ≫ st = spMap (σ : K →+* K) ≫ y.left := by
    intro y n hn hy
    obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.grpPullback_point_descends_algClosed_subfield K k₀ hk₀ B₀ o.t.G π hB₀ hpb n hn y η[B₀].left (by
      rw [hy, ← hun]; simp [Hom.one_def])
    refine hpt y.left ?_ ⟨y₀, hy₀⟩
    simpa using Over.w y
  have hMmem : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) this
  refine ⟨{ m with
    eta := fun a => by
      rw [hφ]
      refine htor (o.eta a) l.M (by have := l.three_le; omega) ?_
      rw [← eta_nsmul o.eta o.eta_add, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
      exact o.eta_ker _ (Submodule.smul_mem_smul hMmem trivial)
    etaA := fun a => by
      rw [hφ]
      refine htor (o.etaA a) l.A l.A_pos ?_
      rw [← eta_nsmul o.etaA o.etaA_add]
      exact o.etaA_ker a }, fun x hx hx₀ => ?_⟩
  show x ≫ m.cm.F = _
  rw [hφ]
  exact hpt x hx hx₀

end GlobalTheory.AutLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsFramesThetaSectionMember
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_points_frames_theta : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1) (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧ (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧ (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ ρ.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪
  have hj : (TFK (R := V) (FractionRing V)).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have gp := 𝔪.cart
  have hsq : ∀ a, (spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ≫ X₁.ρ.P.A.hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    intro a
    rw [Category.assoc, Over.w (X₁.ρ.pt a), hj]
    simp
  let x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) := fun a =>
    Over.homMk (gp.1.lift _ _ (hsq a)) (gp.1.lift_snd _ _ _)
  have hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left := fun a => gp.1.lift_fst _ _ _
  obtain ⟨rig, fr, hrig, -, hfr⟩ := GlobalTheory.exists_frames_move_through (T := baseOver (Sp X₁.S.R))
    (T' := TFK (R := V) (FractionRing V)) (h := spMap 𝔪.yK) gp 𝔪.wl_gen X₁.ρ.rig_gen hx X₁.ρ.fr_tors
  have hτ : (spMap 𝔪.yK : (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left) ≫
      (baseOver (Sp X₁.S.R)).hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    rw [hj]; simp
  obtain ⟨th, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel (T := TFK (R := V) (FractionRing V))
    (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB (a := 1) X₁.ρ.th₁
  refine ⟨x, fr, th, rig, hx, fun a => ⟨(hfr a).1.2.1, fun z J J' hJ hJ' => ?_⟩, fun a => ?_, hrig, fun a => (hfr a).1⟩
  · have e := (hfr a).2 _ (𝟙 _) z J J' hJ hJ'
    rw [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at e
    exact e.symm
  · have hv := GlobalTheory.ThetaPtMove.isValueAt_move (T := TFK (R := V) (FractionRing V))
      (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) X₁.ρ.P.isLB 𝔪.A.isLB (a := 1)
      (x := x a) (x₀ := X₁.ρ.pt a) (hx a).symm (ρ₀ := X₁.ρ.fr a) (ρ := fr a) (hfr a).2 (s₀ := X₁.ρ.th₁) (s := th) hth
      (X₁.ρ.th_val a)
    intro z J hJ
    have e := GlobalTheory.FrameMove.sval_valueAt hv (𝟙 _) hJ
    rw [Category.id_comp] at e
    refine e.trans ?_
    rw [GlobalTheory.FrameMove.val_powFrame, Nat.cast_one, zpow_one]
    congr 1
    exact (gs_pull (𝟙 _) (spMap 𝔪.yK) z ⊤ trivial _).trans
      ((congrArg (fun q => gs q z ⊤ _) (Category.id_comp _)).trans (GlobalTheory.FrameMove.gs_spMap 𝔪.yK z _))

end GlobalTheory.GSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankOneChangeImprovesImageRealPrimeStatement
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rankOneChange_improves_image_real_prime : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  first | exact @GlobalTheory.LowFilt.exists_improves_of_real | exact GlobalTheory.LowFilt.exists_improves_of_real | (intros; apply GlobalTheory.LowFilt.exists_improves_of_real <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothModelNearClosedFibreEmbeddingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_model_near_closedFibre_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∃ (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u ∧ l ≫ E.f = pullback.fst _ _ ≫ fU := by
  first | exact @GlobalTheory.Mum.exists_near | exact GlobalTheory.Mum.exists_near | (intros; apply GlobalTheory.Mum.exists_near <;> assumption)
end

