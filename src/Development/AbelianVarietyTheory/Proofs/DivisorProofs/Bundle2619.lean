import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2499
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2500
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2316
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2294
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityUnramifiedOfJetIntegralit
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleUniqueUpToIso
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

namespace GlobalTheory.CovTest

variable {S T Y B : Scheme.{0}}

theorem pullbackComp_congr_assoc_app (π : Y ⟶ B) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g) (h : S ⟶ T)
    (k : S ⟶ B) (w₂ : h ≫ g = k) (w₃ : (h ≫ g') ≫ π = k) (E : B.Modules) :
    (Scheme.Modules.pullbackComp h g').inv.app ((Scheme.Modules.pullback π).obj E) ≫
      (Scheme.Modules.pullback h).map ((Scheme.Modules.pullbackComp g' π).hom.app E ≫
        (Scheme.Modules.pullbackCongr w).hom.app E) ≫
      (Scheme.Modules.pullbackComp h g).hom.app E ≫ (Scheme.Modules.pullbackCongr w₂).hom.app E =
    (Scheme.Modules.pullbackComp (h ≫ g') π).hom.app E ≫ (Scheme.Modules.pullbackCongr w₃).hom.app E := by
  subst w w₂
  have := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity h g' π) E
  simp [Scheme.Modules.pullbackCongr] at this ⊢
  rw [← cancel_epi ((Scheme.Modules.pullbackComp h (g' ≫ π)).inv.app E ≫
      (Scheme.Modules.pullback h).map ((Scheme.Modules.pullbackComp g' π).inv.app E) ≫
        (Scheme.Modules.pullbackComp h g').hom.app ((Scheme.Modules.pullback π).obj E))]
  simp only [Category.assoc, reassoc_of% this, eqToHom_trans, eqToHom_refl]
  simp [← Functor.map_comp_assoc]

theorem pullbackComp_congr_id_app (π : Y ⟶ B) (w : 𝟙 Y ≫ π = π) (E : B.Modules) :
    (Scheme.Modules.pullbackComp (𝟙 Y) π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E =
      (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback π).obj E) := by
  have := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality π) E
  simp [Scheme.Modules.pullbackCongr] at this ⊢
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom] at this
  rw [this]

theorem flagCompat_comp {ι : Type} {E : ι → B.Modules} {n : ι → ℕ} (π : Y ⟶ B)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (g : T ⟶ B)
    (fl'' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)) (g' : T ⟶ Y) (w : g' ≫ π = g)
    (h₁ : ∀ a i, ∃ e : (Scheme.Modules.pullback g').obj ((fl a).F i) ≅ (fl'' a).F i,
      e.hom ≫ (fl'' a).ι i = (Scheme.Modules.pullback g').map ((fl a).ι i) ≫
        (Scheme.Modules.pullbackComp g' π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a))
    (k : S ⟶ B) (fl''' : ∀ a, Vert.Flag ((Scheme.Modules.pullback k).obj (E a)) (n a)) (h : S ⟶ T)
    (w₂ : h ≫ g = k)
    (h₂ : ∀ a i, ∃ e : (Scheme.Modules.pullback h).obj ((fl'' a).F i) ≅ (fl''' a).F i,
      e.hom ≫ (fl''' a).ι i = (Scheme.Modules.pullback h).map ((fl'' a).ι i) ≫
        (Scheme.Modules.pullbackComp h g).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w₂).hom.app (E a))
    (w₃ : (h ≫ g') ≫ π = k) :
    ∀ a i, ∃ e : (Scheme.Modules.pullback (h ≫ g')).obj ((fl a).F i) ≅ (fl''' a).F i,
      e.hom ≫ (fl''' a).ι i = (Scheme.Modules.pullback (h ≫ g')).map ((fl a).ι i) ≫
        (Scheme.Modules.pullbackComp (h ≫ g') π).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr w₃).hom.app (E a) := by
  intro a i
  obtain ⟨e₁, he₁⟩ := h₁ a i
  obtain ⟨e₂, he₂⟩ := h₂ a i
  refine ⟨(Scheme.Modules.pullbackComp h g').symm.app _ ≪≫ (Scheme.Modules.pullback h).mapIso e₁ ≪≫ e₂, ?_⟩
  rw [← pullbackComp_congr_assoc_app π g' g w h k w₂ w₃ (E a)]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc, he₂]
  rw [← Functor.map_comp_assoc, he₁]
  simp

theorem flagCompat_id {ι : Type} {E : ι → B.Modules} {n : ι → ℕ} (π : Y ⟶ B)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (w : 𝟙 Y ≫ π = π) :
    ∀ a i, ∃ e : (Scheme.Modules.pullback (𝟙 Y)).obj ((fl a).F i) ≅ (fl a).F i,
      e.hom ≫ (fl a).ι i = (Scheme.Modules.pullback (𝟙 Y)).map ((fl a).ι i) ≫
        (Scheme.Modules.pullbackComp (𝟙 Y) π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a) := by
  intro a i
  refine ⟨(Scheme.Modules.pullbackId Y).app _, ?_⟩
  rw [pullbackComp_congr_id_app π w (E a)]
  simp

theorem exists_iso_of_isFlagBundle : ∀ (B Y Y' : Scheme.{0}) (π : Y ⟶ B) (π' : Y' ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (fl' : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π').obj (E a)) (r a)), GlobalTheory.CovTest.IsFlagBundle π E r fl → GlobalTheory.CovTest.IsFlagBundle π' E r fl' → ∃ e : Y ≅ Y', e.hom ≫ π' = π := by
  intro B Y Y' π π' ι E r fl fl' hπ hπ'
  obtain ⟨u, ⟨wu, cu⟩, -⟩ := hπ' Y π fl
  obtain ⟨v, ⟨wv, cv⟩, -⟩ := hπ Y' π' fl'
  have huv : u ≫ v = 𝟙 Y := by
    obtain ⟨z, -, hz⟩ := hπ Y π fl
    have w₃ : (u ≫ v) ≫ π = π := by rw [Category.assoc, wv, wu]
    exact (hz _ ⟨w₃, flagCompat_comp π fl π' fl' v wv cv π fl u wu cu w₃⟩).trans
      (hz _ ⟨Category.id_comp π, flagCompat_id π fl _⟩).symm
  have hvu : v ≫ u = 𝟙 Y' := by
    obtain ⟨z, -, hz⟩ := hπ' Y' π' fl'
    have w₃ : (v ≫ u) ≫ π' = π' := by rw [Category.assoc, wu, wv]
    exact (hz _ ⟨w₃, flagCompat_comp π' fl' π fl u wu cu π' fl' v wv cv w₃⟩).trans
      (hz _ ⟨Category.id_comp π', flagCompat_id π' fl' _⟩).symm
  exact ⟨⟨u, v, huv, hvu⟩, wu⟩

end GlobalTheory.CovTest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsFieldExtensionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_carriesSameFlags_fieldExtension : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)) (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (z : Sp K ⟶ X.YY) (p : Sp K ⟶ C.Y.X), GlobalTheory.VarFlag.Rel X.F C z p → GlobalTheory.VarFlag.Rel X.F C (spMap ι ≫ z) (spMap ι ≫ p) := by
  first | exact @GlobalTheory.VarFlag.rel_baseChange | exact GlobalTheory.VarFlag.rel_baseChange | (intros; apply GlobalTheory.VarFlag.rel_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsSpecialiseValuationRingStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_carriesSameFlags_specialise_valuationRing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ X.YY) (v : Sp A ⟶ C.Y.X), u ≫ X.π = v ≫ C.π ≫ GlobalTheory.Toroidal.genι Y → GlobalTheory.VarFlag.Rel X.F C (spMap (algebraMap A (FractionRing A)) ≫ u) (spMap (algebraMap A (FractionRing A)) ≫ v) → GlobalTheory.VarFlag.Rel X.F C (spMap (IsLocalRing.residue A) ≫ u) (spMap (IsLocalRing.residue A) ≫ v) := by
  first | exact @GlobalTheory.VarFlag.rel_specialise | exact GlobalTheory.VarFlag.rel_specialise | (intros; apply GlobalTheory.VarFlag.rel_specialise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelPointCarriesUniqueFlagBundlePointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_point_carries_unique_flagBundle_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ GlobalTheory.Toroidal.gen Y) (x' : Sp K ⟶ B.X), x' ≫ j = x → x ≫ GlobalTheory.Toroidal.genStr Y = spMap χ → ∀ g : GlobalTheory.ShFam.EigFrame Y χ (x ≫ GlobalTheory.Toroidal.genι Y), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g) → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), ∃! p : Sp K ⟶ C.Y.X, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p := by
  first | exact @GlobalTheory.VarFlag.uniq_rel | exact GlobalTheory.VarFlag.uniq_rel | (intros; apply GlobalTheory.VarFlag.uniq_rel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelToFlagBundleLocallyQuasiFiniteStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_to_flagBundle_locallyQuasiFinite : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagModel Y) (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (Z : Formalism.L2.Pj.Comp Xo c) (h : GlobalTheory.CompHS.Y₀ X.toFlagCover Z ⟶ C.Y.X) [IsProper h], (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X.toFlagCover Z), GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X.toFlagCover Z) (z ≫ h)) → LocallyQuasiFinite h := by
  first | exact @GlobalTheory.VarFlag.locallyQuasiFinite_flag | exact GlobalTheory.VarFlag.locallyQuasiFinite_flag | (intros; apply GlobalTheory.VarFlag.locallyQuasiFinite_flag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagZ
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FlagQ

variable {ι : Type} [Fintype ι] {N : ℕ} {Y : Var ℚ}

def genMat (j : Y.X ⟶ Fl ι N) : ι → GL (Fin N) Y.Fn :=
  (exists_eq_flagPt_of_isLocalRing ι (ι × Fin (N + 1)) N Prod.fst Prod.snd Y.Fn ((ratOf Y).pt ≫ j)).choose

theorem flagPt_genMat (j : Y.X ⟶ Fl ι N) :
    (ratOf Y).pt ≫ j = flagPt Prod.fst Prod.snd (genMat j) :=
  (exists_eq_flagPt_of_isLocalRing ι (ι × Fin (N + 1)) N Prod.fst Prod.snd Y.Fn ((ratOf Y).pt ≫ j)).choose_spec

def genFrame (j : Y.X ⟶ Fl ι N) : Mat (fun _ : ι => N) Y.Fn := fun τ => (genMat j τ).1.transpose

def IsFrame (j : Y.X ⟶ Fl ι N) (y : Y.X) (A : Mat (fun _ : ι => N) Y.Fn) : Prop :=
  Par 0 ((ratOf Y).O y).toSubring A ∧ Par (fun _ => N) ⊤ (A * (genFrame j)⁻¹)

def ptQ : Sp ℚ ⟶ PSpace ℚ 0 :=
  GlobalTheory.ProjSpace.pt (RingHom.id ℚ) (fun _ => 1) (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one)

def toPt (Y : Var ℚ) : Y.X ⟶ (proj ℚ 0).X := Y.str ≫ ptQ ≫ @inv _ _ _ _ (proj ℚ 0).ι (isIso_proj_ι ℚ 0)

def triv (ι : Type) (N : ℕ) : Fr (ratOf (proj ℚ 0)) (fun _ : ι => N) 0 :=
  Fr.ofBasis _ 0 1 fun _ => by simp

end GlobalTheory.FlagQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantAbsLeNine
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.TwistDeg

open GlobalTheory.FlatTw GlobalTheory.FlatLine GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem logSum_bad_le {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) :
    logSum (GlobalTheory.FlatTw.badPrimes H l) ≤ Real.log 2 + Real.log H.d + Real.log |(discr E : ℝ)| + Real.log l.M' := by
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hD : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hd := H.d_prime.ne_zero
  have hne : 2 * H.d * (discr E).natAbs * l.M' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hd) hD) hM
  have h0 : ∀ p ∈ (2 * H.d * (discr E).natAbs * l.M').primeFactors, (p : ℝ) ≠ 0 := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have e : Real.log 2 + Real.log H.d + Real.log |(discr E : ℝ)| + Real.log l.M' =
      Real.log ((2 * H.d * (discr E).natAbs * l.M' : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Nat.cast_natAbs, Int.cast_abs, Nat.cast_ofNat]
  rw [e, logSum, GlobalTheory.FlatTw.badPrimes, ← Real.log_prod h0, ← Nat.cast_prod]
  refine Real.log_le_log ?_ (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Nat.prod_primeFactors_dvd _))
  exact_mod_cast Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

theorem lrd_eq (E : Type) [Field E] [NumberField E] :
    lrd E = Real.log |(discr E : ℝ)| / (Module.finrank ℚ E : ℝ) := by
  have h : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
  rw [lrd, rootDiscr_def, Int.cast_abs, Real.log_rpow h, div_eq_inv_mul]

theorem numeric {f r L q a b s c : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ L) (hq : q ≤ r)
    (hb0 : 0 ≤ b) (hb : b ≤ 3 * L) (hs0 : 0 ≤ s) (hs : s ≤ 6 * f * r) (hc : |a| ≤ 9 * r * L * s)
    (hB : c ≤ 1 + 2 * b + 2 * f * b + 30 * L) : -(120 * (f * r * L) ^ 2) ≤ a - q * b * s - c := by
  have h1 : q * b * s ≤ r * (3 * L) * (6 * f * r) := by gcongr
  have h2 : 9 * r * L * s ≤ 9 * r * L * (6 * f * r) := by gcongr
  have h3 : f * b ≤ f * (3 * L) := by gcongr
  have h4 : f * r ^ 2 * L ≤ (f * r * L) ^ 2 := by
    rw [show (f * r * L) ^ 2 = f * r ^ 2 * L * (f * L) by ring]
    exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hf hL)
  have h5 : f * L ≤ f * r ^ 2 * L := by
    rw [show f * r ^ 2 * L = f * L * r ^ 2 by ring]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hr)
  have h6 : L ≤ f * L := le_mul_of_one_le_left (by positivity) hf
  have h7 := (abs_le.1 hc).1
  nlinarith

theorem deg_twist_ge : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ (la : AllWt.Weight (T.Q.Dw j)) (w : Psi T.Q.H → ℤ) Z, (∀ τ, |w τ| ≤ 3 * (D.R.r : ℤ)) → GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0) → Y.degC la Z - Y.rkC la Z * (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2) ≤ Y.degC (la + GlobalTheory.FlatLine.parWt (T.Q.Dw j) w) Z := by
  intro hP
  refine ⟨120, by norm_num, fun D T hT j hp hq _ hj Y e o hY Lb hL hM hE _ _ c₁ hc hc₁ la w Z hw hG => ?_⟩
  have hn : 1 ≤ D.R.n := D.R.toFrame.ord_pos
  have h1 := D.R.two_le_m
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hrk : (0 : ℝ) ≤ Y.rkC la Z := Nat.cast_nonneg _
  rcases isEmpty_or_nonempty (Psi T.Q.H) with h0 | ⟨⟨τ₀⟩⟩
  · rw [show la + parWt (T.Q.Dw j) w = la from funext fun τ => h0.elim τ]
    exact sub_le_self _ (by positivity)
  obtain ⟨hpq, -, -, -, -, g, ee, F, -⟩ := hY.unf Y.d.c₂.F.val.toRingHom rfl
  have hK := GlobalTheory.KeyCover.nonempty_keySec_of_family _ _ _ _ _ _ Y.d.c₂.F.val.toRingHom rfl ee F (by omega) hY.geo
  obtain ⟨t, ht, -, hd⟩ := (GlobalTheory.FlatTwisting.twSec_of_flat _ _ _ _ _ _ _ Y.U (xiR D) _ hK hY.unf (by omega)
    (GlobalTheory.T.unramified_points_deep_level hP D T j Y e o hT hj hY)).2 ⟨c₁, hc⟩ Z w (hc Z τ₀).1.some.hasPts
  have key := GlobalTheory.FlatTw.degOn_add_rank_mul_degLo_le _ _ _ _ _ _ _ Y.U (xiR D) D (fun _ => D.sp.W j) Y.dict Z _ t _ _ hY.unf
    (AllWt.even_wtOf la 0) badPrimes_prime ht hG
  rw [← wtOf_add'] at key
  refine le_trans ?_ key
  rw [sub_eq_add_neg, ← mul_neg]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_trans ?_ (sub_le_sub_right hd _)) hrk)
  have hdeg : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have hd2 := abs_le.1 (GlobalTheory.abs_lrd_sub_log_d_le_lrd _ T.Q.H)
  have hcard : (Fintype.card (Psi T.Q.H) : ℝ) ≤ 2 * D.R.f := by
    have := Fintype.card_subtype_le fun τ : D.host.E →+* ℂ => τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0
    rw [Embeddings.card, hdeg] at this
    exact_mod_cast (Fintype.card_congr (Equiv.refl _)).le.trans this
  refine numeric hf hr hL (by exact_mod_cast (by omega : (T.Q.Dw j).q ≤ D.R.r)) (by linarith [hd2.1, hd2.2])
    (by rw [lrd_eq]; exact (log_rd_le_fieldSz _).trans hE) (Finset.sum_nonneg fun _ _ => abs_nonneg _) ?_ ?_ ?_
  · refine (Finset.sum_le_card_nsmul _ _ (3 * (D.R.r : ℝ)) fun τ _ => by exact_mod_cast hw τ).trans ?_
    rw [nsmul_eq_mul, Finset.card_univ]
    nlinarith
  · simp only [hc.c1_eq ⟨Z⟩]
    rw [← Finset.sum_mul, abs_mul, mul_comm]
    exact mul_le_mul hc₁ (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _) (by positivity)
  · refine (logSum_bad_le _ _).trans ?_
    have l2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have hM' : Y.d.l₂.M' = Y.d.l₂.M := by rw [Level.M', hY.lev.2, Nat.lcm_one_right]
    have hD : Real.log |(discr D.host.E : ℝ)| = 2 * D.R.f * lrd D.host.E := by
      rw [lrd_eq, hdeg]; push_cast; field_simp
    rw [hM', hD]
    linarith [hd2.1]

end GlobalTheory.TwistDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOverArtinFibreProductIsPushout
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.FlatPinch

theorem surjective_fst_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂}
    {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀} (hP : IsPullback f₁ f₂ g₁ g₂) (hg₂ : Function.Surjective g₂) :
    Function.Surjective f₁ := by
  intro r
  obtain ⟨s, hs⟩ := hg₂ (g₁ r)
  obtain ⟨a, ha, -⟩ := (GlobalTheory.DualOpen.elem_of_isPullback_ring hP).2 r s hs.symm
  exact ⟨a, ha⟩

end GlobalTheory.FlatPinch

namespace GlobalTheory.FlatPinch

theorem resLE_homOfLE {Y' T X : Scheme.{0}} (f' : Y' ⟶ T) {V V' : T.Opens} (h : V' ≤ V) (g : V.toScheme ⟶ X)
    (w : Y' ⟶ X) (hg : f'.resLE V _ le_rfl ≫ g = (f' ⁻¹ᵁ V).ι ≫ w) :
    f'.resLE V' _ le_rfl ≫ T.homOfLE h ≫ g = (f' ⁻¹ᵁ V').ι ≫ w := by
  have e : f'.resLE V' _ le_rfl ≫ T.homOfLE h = Y'.homOfLE (f'.preimage_mono h) ≫ f'.resLE V _ le_rfl := by
    rw [← cancel_mono V.ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]
  rw [reassoc_of% e, hg, Scheme.homOfLE_ι_assoc]

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), Flat Y.hom → IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) → IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ Y₂.hom = Y₀.hom ≫ Spec.map g₂ → IsPushout i₁ i₂ j₁ j₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₁ hg₂ Y Y₁ Y₂ Y₀ j₁ j₂ i₁ i₂ hfl h₁ h₂ h₀ hij hp₂
  have hf₁ : Function.Surjective f₁ := surjective_fst_of_isPullback hP hg₂
  have hf₂ : Function.Surjective f₂ := surjective_fst_of_isPullback hP.flip hg₁
  haveI : IsClosedImmersion j₁ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₁.flip (IsClosedImmersion.spec_of_surjective f₁ hf₁)
  haveI : IsClosedImmersion j₂ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₂.flip (IsClosedImmersion.spec_of_surjective f₂ hf₂)
  obtain ⟨hcov, hpts⟩ := GlobalTheory.T.points_of_scheme_over_artinian_fibre_product _ _ _ _ _ _ _ _ hP hloc hart hg₁ hg₂ _ _ _ _ Y.hom Y₁.hom Y₂.hom Y₀.hom
    j₁ j₂ i₁ i₂ h₁ h₂ h₀ hij
  have hM : GlobalTheory.DualOpen.Milnor (Spec.map f₂) (Spec.map f₁) (Spec.map g₂) (Spec.map g₁) :=
    GlobalTheory.DualOpen.Milnor.of_isPullback hP.flip hg₁
  haveI : Flat Y.hom := hfl
  have SEC := fun W => GlobalTheory.DualOpen.sections_of_squares hM h₂ h₁ h₀ hij.symm hp₂ W
  have hinj : ∀ (W : Y.left.Opens) (a b : Γ(Y.left, W)), j₁.app W a = j₁.app W b → j₂.app W a = j₂.app W b → a = b :=
    fun W a b e1 e2 => (SEC W).1 a b e2 e1
  have uniqV := fun (X : Scheme.{0}) (V : Y.left.Opens) =>
    GlobalTheory.T.scheme_hom_ext_of_jointly_surjective_of_app_injective _ _ _ X _ _ ((GlobalTheory.T.jointCover_sectionDetect_restrict_open _ _ _ j₁ j₂ hcov hinj V).1)
      ((GlobalTheory.T.jointCover_sectionDetect_restrict_open _ _ _ j₁ j₂ hcov hinj V).2)
  have uniq : ∀ (X : Scheme.{0}) (a b : Y.left ⟶ X), j₁ ≫ a = j₁ ≫ b → j₂ ≫ a = j₂ ≫ b → a = b :=
    fun X => GlobalTheory.T.scheme_hom_ext_of_jointly_surjective_of_app_injective _ _ _ X j₁ j₂ hcov hinj
  have key : ∀ (X : Scheme.{0}) (a₁ : Y₁.left ⟶ X) (a₂ : Y₂.left ⟶ X), i₁ ≫ a₁ = i₂ ≫ a₂ →
      ∃ a : Y.left ⟶ X, j₁ ≫ a = a₁ ∧ j₂ ≫ a = a₂ := by
    intro X a₁ a₂ ha
    have hpa : ∀ (y₁ : Y₁.left) (y₂ : Y₂.left), j₁ y₁ = j₂ y₂ → a₁ y₁ = a₂ y₂ := by
      intro y₁ y₂ h
      obtain ⟨y₀, rfl, rfl⟩ := hpts y₁ y₂ h
      have := congrArg (fun q : Y₀.left ⟶ X => q y₀) ha
      simpa using this
    have hloc := GlobalTheory.T.exists_affine_nbhd_preimage_le_of_closed_cover _ _ _ X j₁ j₂ a₁ a₂ hcov hpa
    let Idx := {p : Y.left.Opens × X.affineOpens //
      IsAffineOpen p.1 ∧ j₁ ⁻¹ᵁ p.1 ≤ a₁ ⁻¹ᵁ p.2.1 ∧ j₂ ⁻¹ᵁ p.1 ≤ a₂ ⁻¹ᵁ p.2.1}
    have hcovI : TopologicalSpace.IsOpenCover (fun p : Idx => p.1.1) := by
      rw [TopologicalSpace.IsOpenCover, eq_top_iff]
      intro y _
      obtain ⟨W, U, hW, hy, h1, h2⟩ := hloc y
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(W, U), hW, h1, h2⟩, hy⟩
    have EO : ∀ p : Idx, ∃ g : p.1.1.toScheme ⟶ X, j₁.resLE _ _ le_rfl ≫ g = (j₁ ⁻¹ᵁ p.1.1).ι ≫ a₁ ∧
        j₂.resLE _ _ le_rfl ≫ g = (j₂ ⁻¹ᵁ p.1.1).ι ≫ a₂ := by
      rintro ⟨⟨W, U⟩, hW, hx, hz⟩
      have hW1 : IsAffineOpen (j₁ ⁻¹ᵁ W) := hW.preimage j₁
      have hW2 : IsAffineOpen (j₂ ⁻¹ᵁ W) := hW.preimage j₂
      have hpre : i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ W) = i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ W) := by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hij]
      refine GlobalTheory.Pinch.exists_glue_of_sections j₁ j₂ W hW hW1 hW2 U a₁ a₂ hx hz ?_ ?_
      · intro t₁ t₂ e1 e2
        rw [← Scheme.Hom.app_eq_appLE] at e1 e2
        exact hinj W t₁ t₂ e1 e2
      · intro u
        obtain ⟨t, ht2, ht1⟩ := (SEC W).2 (i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ W)) le_rfl hpre.le le_rfl
          (a₂.appLE U.1 _ hz u) (a₁.appLE U.1 _ hx u) (by
            have e1 := Scheme.Hom.appLE_comp_appLE i₂ a₂ U.1 _ (i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ W)) hz le_rfl
            have e2 := Scheme.Hom.appLE_comp_appLE i₁ a₁ U.1 _ (i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ W)) hx hpre.le
            have e3 := GlobalTheory.Pinch.appLE_congr_hom ha.symm U.1 (i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ W))
              (fun w hw => hz hw) (fun w hw => hx (hpre.le hw))
            have := congrArg (fun q => q.hom u) (e1.trans (e3.trans e2.symm))
            simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
            exact this)
        refine ⟨t, ?_, ?_⟩
        · rw [← Scheme.Hom.app_eq_appLE]; exact ht1
        · rw [← Scheme.Hom.app_eq_appLE]; exact ht2
    let 𝒰 := Y.left.openCoverOfIsOpenCover _ hcovI
    choose g hg using EO
    have hc : ∀ a b : Idx, pullback.fst (𝒰.f a) (𝒰.f b) ≫ g a = pullback.snd (𝒰.f a) (𝒰.f b) ≫ g b := by
      intro a b
      have hPb := isPullback_opens_inf a.1.1 b.1.1
      change pullback.fst a.1.1.ι b.1.1.ι ≫ g a = pullback.snd a.1.1.ι b.1.1.ι ≫ g b
      rw [← cancel_epi hPb.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_snd_assoc]
      refine uniqV X (a.1.1 ⊓ b.1.1) _ _ ?_ ?_
      · rw [resLE_homOfLE j₁ _ _ a₁ (hg a).1, resLE_homOfLE j₁ _ _ a₁ (hg b).1]
      · rw [resLE_homOfLE j₂ _ _ a₂ (hg a).2, resLE_homOfLE j₂ _ _ a₂ (hg b).2]
    let z₀ := 𝒰.glueMorphisms g hc
    have hz₀ : ∀ a : Idx, a.1.1.ι ≫ z₀ = g a := fun a => 𝒰.ι_glueMorphisms g hc a
    refine ⟨z₀, ?_, ?_⟩
    · have hcov1 : TopologicalSpace.IsOpenCover (fun p : Idx => j₁ ⁻¹ᵁ p.1.1) := by
        rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, hcovI, Scheme.Hom.preimage_top]
      refine Scheme.Cover.hom_ext (Y₁.left.openCoverOfIsOpenCover _ hcov1) _ _ fun a => ?_
      change (j₁ ⁻¹ᵁ a.1.1).ι ≫ j₁ ≫ z₀ = (j₁ ⁻¹ᵁ a.1.1).ι ≫ a₁
      rw [← (hg a).1, ← hz₀ a, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι j₁ (le_rfl), Category.assoc]
    · have hcov2 : TopologicalSpace.IsOpenCover (fun p : Idx => j₂ ⁻¹ᵁ p.1.1) := by
        rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, hcovI, Scheme.Hom.preimage_top]
      refine Scheme.Cover.hom_ext (Y₂.left.openCoverOfIsOpenCover _ hcov2) _ _ fun a => ?_
      change (j₂ ⁻¹ᵁ a.1.1).ι ≫ j₂ ≫ z₀ = (j₂ ⁻¹ᵁ a.1.1).ι ≫ a₂
      rw [← (hg a).2, ← hz₀ a, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι j₂ (le_rfl), Category.assoc]
  refine IsPushout.of_isColimit (c := PushoutCocone.mk j₁ j₂ hij)
    (PushoutCocone.IsColimit.mk _ (fun s => Classical.choose (key _ s.inl s.inr s.condition))
      (fun s => (Classical.choose_spec (key _ s.inl s.inr s.condition)).1)
      (fun s => (Classical.choose_spec (key _ s.inl s.inr s.condition)).2)
      (fun s m e1 e2 => uniq _ _ _ (e1.trans (Classical.choose_spec (key _ s.inl s.inr s.condition)).1.symm)
        (e2.trans (Classical.choose_spec (key _ s.inl s.inr s.condition)).2.symm)))

end GlobalTheory.FlatPinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdEqMultOfIsCartierDivisorOfRationalFormStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formOrd_eq_mult_of_isCartierDivisorOfRationalForm : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ K : CartierDiv Y, IsDivOfForm K η → ∀ (E : DivOver q) (w : Y), E.IsAt w → E.formOrd η = K.mult w := by
  first | exact @GlobalTheory.Discrepancy.DivOver.formOrd_eq_mult_of_isDivOfForm | exact GlobalTheory.Discrepancy.DivOver.formOrd_eq_mult_of_isDivOfForm | (intros; apply GlobalTheory.Discrepancy.DivOver.formOrd_eq_mult_of_isDivOfForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseClosedImmersion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem alg_of_isClosedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (i : W' ⟶ W), IsSeparated f → IsClosedImmersion i → Alg f I →
    Alg (i ≫ f) I := by
  intro R _ I W W' f i hf hi hA t ht hp
  obtain ⟨hs, hsp, hc⟩ := GlobalTheory.T.compatibleReductionSystem_map_immersion R I W W' f i hf inferInstance t ht hp
  obtain ⟨T, hT, hred⟩ := hA _ hs hsp
  refine ⟨T.comap i, ?_, fun e => ?_⟩
  · have h1 : (T.comap i).subschemeι ≫ i ≫ f =
        (T.comapIso i).hom ≫ pullback.snd i T.subschemeι ≫ T.subschemeι ≫ f := by
      rw [← T.comapIso_hom_fst_assoc i, pullback.condition_assoc]
    rw [h1]
    infer_instance
  · rw [← (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1 R W W' f i, ← Scheme.IdealSheafData.comap_sup, hred e]
    exact hc e

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingEqUniformiserZpowMulUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionRing_eq_uniformiser_zpow_mul_unit : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}, Irreducible ϖ → ∀ (y : FractionRing V), y ≠ 0 → ∃ (v : ℤ) (w : Vˣ), y = algebraMap V (FractionRing V) ϖ ^ v * algebraMap V (FractionRing V) (w : V) := by
  first | exact @GlobalTheory.DVR.fractionRing_eq_zpow_mul_unit | exact GlobalTheory.DVR.fractionRing_eq_zpow_mul_unit | (intros; apply GlobalTheory.DVR.fractionRing_eq_zpow_mul_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityUnramifiedOfJetIntegralitStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeValueIntegrality_unramified_of_jetIntegrality : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → JetInt → LatIntUnr := by
  first | exact @GlobalTheory.LatValUnr.latIntUnr | exact GlobalTheory.LatValUnr.latIntUnr | (intros; apply GlobalTheory.LatValUnr.latIntUnr <;> assumption)
end

