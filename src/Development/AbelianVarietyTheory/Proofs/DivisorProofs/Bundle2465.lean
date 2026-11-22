import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveCartierLocalEquation
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.IdealDiv

theorem unitAt_div_of_ideal_eq {Y : Scheme.{0}} [IsIntegral Y] (J : Y.IdealSheafData) {y : Y}
    {U V : Y.affineOpens} {f : Γ(Y, U.1)} {f' : Γ(Y, V.1)} (hU : y ∈ U.1) (hV : y ∈ V.1)
    (hf : J.ideal U = Ideal.span {f}) (hf' : J.ideal V = Ideal.span {f'})
    (h0 : fnOf U.1 (gen_mem hU) f ≠ 0) :
    UnitAt y (fnOf V.1 (gen_mem hV) f' / fnOf U.1 (gen_mem hU) f) := by
  obtain ⟨h, hhW, hxh⟩ := U.2.exists_basicOpen_le (V := U.1 ⊓ V.1) ⟨_, ⟨hU, hV⟩⟩ hU
  let Wa : Y.affineOpens := ⟨Y.basicOpen h, U.2.basicOpen h⟩
  have hWU : Wa.1 ≤ U.1 := hhW.trans inf_le_left
  have hWV : Wa.1 ≤ V.1 := hhW.trans inf_le_right
  haveI : Nonempty Wa.1 := ⟨⟨_, hxh⟩⟩
  have e1 : J.ideal Wa = Ideal.span {resG Y hWU f} := by
    rw [← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := U) hWU, hf, Ideal.map_span, Set.image_singleton]
    rfl
  have e2 : J.ideal Wa = Ideal.span {resG Y hWV f'} := by
    rw [← Scheme.IdealSheafData.map_ideal _ (U := Wa) (V := V) hWV, hf', Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 (e1.symm.trans e2)
  have hg := gen_mem (U := Wa.1) hxh
  have e := congrArg (fnOf Wa.1 hg) hu
  rw [map_mul, fnOf_resG, fnOf_resG] at e
  rw [← e, mul_div_cancel_left₀ _ h0]
  exact unitAt_fnOf hxh hg u

theorem exists_cartierDiv_of_effCartier : ∀ (Y : Scheme.{0}) [IsIntegral Y] (J : Y.IdealSheafData),
    FinalTheorems.EffCartier J → ∃ E : CartierDiv Y, E.Eff ∧ E.supp = J.support ∧
      ∀ (y : Y) (U : Y.affineOpens) (f : Γ(Y, U.1)) (hy : y ∈ U.1) (hf : fnOf U.1 (gen_mem hy) f ≠ 0),
        J.ideal U = Ideal.span {f} → E.IsEqn y (Units.mk0 _ hf) := by
  intro Y _ J hJ
  choose U f hyU hnzd hid using hJ
  have hne : ∀ y, fnOf (U y).1 (gen_mem (hyU y)) (f y) ≠ 0 := by
    intro y h
    haveI : Nonempty (U y).1 := ⟨⟨y, hyU y⟩⟩
    have h0 : f y = 0 := fnOf_injective _ _ (h.trans (map_zero _).symm)
    exact nonZeroDivisors.ne_zero (hnzd y) h0
  let v : ∀ y : Y, Y.functionFieldˣ := fun y => Units.mk0 _ (hne y)
  let E : CartierDiv Y := show cartierGroup Y from ⟨fun y => germOf y (v y), fun x =>
    ⟨(U x).1, hyU x, v x, fun y hy =>
      germOf_eq_iff.2 (unitAt_div_of_ideal_eq J (hyU y) hy (hid y) (hid x) (hne y))⟩⟩
  have hE : ∀ y, E.IsEqn y (v y) := fun y => rfl
  refine ⟨E, fun x => ⟨v x, hE x, by rw [one_mul]; exact regAt_fnOf (hyU x) _ _⟩, ?_, ?_⟩
  · ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, (hE x).mem_supp_iff, Units.val_mk0, unitAt_fnOf_iff (hyU x),
      Scheme.IdealSheafData.mem_support_iff_of_mem (U := U x) (hyU x), hid x, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton]
    rfl
  · intro y V g hy hg hV
    exact (hE y).iff_unitAt.2 (unitAt_div_of_ideal_eq J (hyU y) hy (hid y) hV (hne y))

end GlobalTheory.Cartier.IdealDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameCoordinatesLocallyConstantUpToUnits
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

namespace GlobalTheory.FrameSpread

open GlobalTheory.Toroidal (gen genι genStr)
open GlobalTheory.ShFam

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem isMap_trans {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {F : EigFrame Z φ x}
    {F' : EigFrame Z φ' x'} {F'' : EigFrame Z φ'' x''} {a : R →+* R'} {b : R' →+* R''} (h1 : F.IsMap a F')
    (h2 : F.IsMap (b.comp a) F'') : F'.IsMap b F'' := fun τ i => by
  rw [h2 τ i, h1 τ i, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp]

end

theorem unitAt_det_co : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι)), (X₀ TF.Y Z).fromSpecStalk x ≫ s₀ TF.Y Z = spMap φ → ∃ U : (X₀ TF.Y Z).Opens, x ∈ U ∧ ∀ y ∈ U, ∀ (φ' : c.F →+* (X₀ TF.Y Z).presheaf.stalk y) (f' : GlobalTheory.ShFam.EigFrame TF.Y φ' ((X₀ TF.Y Z).fromSpecStalk y ≫ (barComp TF.Y Z).ι)) (φK : c.F →+* (X₀ TF.Y Z).functionField) (fK fK' : GlobalTheory.ShFam.EigFrame TF.Y φK ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)), (X₀ TF.Y Z).fromSpecStalk y ≫ s₀ TF.Y Z = spMap φ' → (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ s₀ TF.Y Z = spMap φK → f.IsMap (algebraMap _ (X₀ TF.Y Z).functionField) fK → f'.IsMap (algebraMap _ (X₀ TF.Y Z).functionField) fK' → ∀ τ, UnitAt y (fK'.co fK τ).det := by
  intro E _ _ _ H Dw l Xo c TF Z _ x φ f hφ
  haveI : IsIso (genι TF.Y) := GlobalTheory.VarFlag.isIso_genι
  let e : X₀ TF.Y Z ⟶ gen TF.Y := (barComp TF.Y Z).ι ≫ inv (genι TF.Y)
  have he : e ≫ genι TF.Y = (barComp TF.Y Z).ι := by simp [e]
  have hstrY : genStr TF.Y = genι TF.Y ≫ TF.Y.s := by
    have h0 : genι TF.Y ≫ TF.Y.s = genStr TF.Y ≫ spMap (RingHom.id c.F) := pullback.condition
    have h1 : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
    rw [h1, Category.comp_id] at h0
    exact h0.symm
  obtain ⟨U, hU, φU, F, hxU, hUstr, -⟩ :=
    GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) TF.Y (e x)
  let ψ : ∀ p : X₀ TF.Y Z, e p ∈ U → (Γ(gen TF.Y, U) →+* (X₀ TF.Y Z).presheaf.stalk p) := fun p hp =>
    (e.stalkMap p).hom.comp ((gen TF.Y).presheaf.germ U (e p) hp).hom
  have hψ : ∀ p hp, (X₀ TF.Y Z).fromSpecStalk p ≫ e = spMap (ψ p hp) ≫ hU.fromSpec := by
    intro p hp
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← hU.fromSpecStalk_eq_fromSpecStalk hp, IsAffineOpen.fromSpecStalk,
      ← Category.assoc, ← Spec.map_comp]
    rfl
  have hmono : ∀ {R : Type} [CommRing R] (a b : Γ(gen TF.Y, U) →+* R),
      spMap a ≫ hU.fromSpec = spMap b ≫ hU.fromSpec → a = b := fun a b h =>
    GlobalTheory.ShFam.EigLoc.spMap_inj ((cancel_mono hU.fromSpec).1 h)
  have hring : ∀ {R : Type} [CommRing R] (q : Sp R ⟶ X₀ TF.Y Z) (ρ : c.F →+* R) (a : Γ(gen TF.Y, U) →+* R),
      q ≫ s₀ TF.Y Z = spMap ρ → q ≫ e = spMap a ≫ hU.fromSpec → ρ = a.comp φU := by
    intro R _ q ρ a h1 h2
    apply GlobalTheory.ShFam.EigLoc.spMap_inj
    rw [← h1, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hUstr, ← Category.assoc (spMap a), ← h2, hstrY]
    simp only [Category.assoc]
    rw [← Category.assoc e, he]
  have hpt : ∀ p hp, (X₀ TF.Y Z).fromSpecStalk p ≫ (barComp TF.Y Z).ι = spMap (ψ p hp) ≫ hU.fromSpec ≫ genι TF.Y := by
    intro p hp
    rw [← he, ← Category.assoc, hψ p hp, Category.assoc]
  have hgen : ∀ p : X₀ TF.Y Z, (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) =
      spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk p) (X₀ TF.Y Z).functionField) ≫ (X₀ TF.Y Z).fromSpecStalk p :=
    fun p =>
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec (X₀ TF.Y Z)).specializes (Set.mem_univ p))).symm
  obtain ⟨Fx, hFx⟩ := F.exists_isMap (ψ x hxU) (hring _ φ _ hφ (hψ x hxU)) (hpt x hxU)
  have hWx : ∀ τ, UnitAt x (algebraMap _ (X₀ TF.Y Z).functionField (Fx.co f τ).det) :=
    fun τ => ⟨_, EigFrame.isUnit_det_co Fx f τ, rfl⟩
  choose W hxW hW using fun τ => (hWx τ).exists_nhds
  refine ⟨⟨(e ⁻¹ᵁ U : Set (X₀ TF.Y Z)) ∩ ⋂ τ, (W τ : Set (X₀ TF.Y Z)),
    (e ⁻¹ᵁ U).isOpen.inter (isOpen_iInter_of_finite fun τ => (W τ).isOpen)⟩,
    ⟨hxU, Set.mem_iInter.2 hxW⟩, ?_⟩
  rintro y ⟨hyU, hyW⟩ φ' f' φK fK fK' hφ' hφK hfK hfK' τ
  rw [Set.mem_iInter] at hyW
  have hyU' : e y ∈ U := hyU
  obtain ⟨Fy, hFy⟩ := F.exists_isMap (ψ y hyU') (hring _ φ' _ hφ' (hψ y hyU')) (hpt y hyU')
  have hKp : ∀ p hp, spMap ((algebraMap ((X₀ TF.Y Z).presheaf.stalk p) (X₀ TF.Y Z).functionField).comp (ψ p hp)) ≫
      hU.fromSpec = (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ e := by
    intro p hp
    rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk p) (X₀ TF.Y Z).functionField)
      (ψ p hp), Category.assoc, ← hψ, ← Category.assoc, ← hgen]
  have hK : (algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField).comp (ψ y hyU') =
      (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField).comp (ψ x hxU) :=
    hmono _ _ ((hKp y hyU').trans (hKp x hxU).symm)
  have hKpt := (hKp y hyU').symm
  obtain ⟨FK, hFK⟩ := F.exists_isMap
    ((algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField).comp (ψ y hyU'))
    (x' := (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)
    (hring _ φK _ hφK hKpt) (by rw [← he]; exact (reassoc_of% hKpt) (genι TF.Y))
  have hFyK : Fy.IsMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField) FK :=
    isMap_trans hFy hFK
  have hFxK : Fx.IsMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField) FK :=
    isMap_trans hFx (by rw [← hK]; exact hFK)
  have hy : (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι =
      spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField) ≫ (X₀ TF.Y Z).fromSpecStalk y ≫ (barComp TF.Y Z).ι := by
    rw [hgen y, Category.assoc]
  have hx : (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι =
      spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField) ≫ (X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι := by
    rw [hgen x, Category.assoc]
  have e1 := EigFrame.IsMap.co (τ := τ) hfK' hFyK hy
  have e2 := EigFrame.IsMap.co (τ := τ) hFxK hfK hx
  have dmap : ∀ {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) {n : ℕ} (M : Matrix (Fin n) (Fin n) R),
      (M.map g).det = g M.det := fun g _ M => (RingHom.map_det g M).symm
  rw [← EigFrame.co_mul fK' FK fK τ, Matrix.det_mul, e1, dmap]
  refine UnitAt.mul ⟨_, EigFrame.isUnit_det_co f' Fy τ, rfl⟩ ?_
  convert hW τ y (hyW τ) using 1
  erw [e2]
  exact dmap _ _

end GlobalTheory.FrameSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameTransportCartesianAutomorphism
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

namespace GlobalTheory.EqvTrans

open MonObj GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X Y : Scheme.{0}} {t : SAB H Y} {p : X ⟶ Y} {G' : Over X} [GrpObj G'] {ψ : G'.left ⟶ t.G.left}

theorem spMap_eps_alg {R : Type} [CommRing R] (a : R) :
    spMap (epsMul a) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) := by
  rw [← Spec.map_comp]
  congr 1
  ext r <;> simp [epsMul]

theorem spMap_fst_alg {R : Type} [CommRing R] :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 (Sp R) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl]))

theorem cancel_g_ψ (hψ : IsPullback ψ G'.hom t.G.hom p) {b : X ⟶ X} {g : G'.left ⟶ G'.left}
    (hg : IsPullback g G'.hom G'.hom b) {T : Scheme.{0}} {u₁ u₂ : T ⟶ G'.left}
    (h₁ : u₁ ≫ G'.hom = u₂ ≫ G'.hom) (h₂ : u₁ ≫ g ≫ ψ = u₂ ≫ g ≫ ψ) : u₁ = u₂ :=
  hg.hom_ext (hψ.hom_ext (by simpa using h₂) (by simp only [Category.assoc, hg.w, reassoc_of% h₁])) h₁

variable {R : Type} [CommRing R]

theorem one_g_ψ (hG : IsGrpPullback G' t.G p ψ) {b : X ⟶ X} {g : G'.left ⟶ G'.left} (hgb : IsGrpPullback G' G' b g)
    (q : Sp R ⟶ X) : (1 : Over.mk q ⟶ G').left ≫ g ≫ ψ = (1 : Over.mk ((q ≫ b) ≫ p) ⟶ t.G).left := by
  have h1 := grpPull_one hgb (Over.mk q)
  have h2 := grpPull_one hG (Over.mk (q ≫ b))
  rw [← Category.assoc, ← h1]
  exact h2.symm

theorem isTan_trv (hG : IsGrpPullback G' t.G p ψ) {b : X ⟶ X} {g : G'.left ⟶ G'.left} (hgb : IsGrpPullback G' G' b g)
    (q : Sp R ⟶ X) {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t (q ≫ p) v) :
    IsTanAtG t ((q ≫ b) ≫ p) (trv hG.1 g q v) := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hG.1 q hv.1
  refine ⟨trv_over hG.1 g hgb.1.w q hv.1, ?_⟩
  rw [trv_eq hG.1 g q w hw hw']
  have e : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w = (1 : Over.mk q ⟶ G').left :=
    hG.1.hom_ext (by rw [Category.assoc, hw, hv.2]; exact grpPull_one hG (Over.mk q))
      (by rw [Category.assoc, hw', ← Category.assoc, spMap_fst_alg, Category.id_comp]
          exact (Over.w (1 : Over.mk q ⟶ G')).symm)
  rw [← Category.assoc, e, one_g_ψ hG hgb q]

theorem trv_eig (hψ : IsPullback ψ G'.hom t.G.hom p) {act' : OAct (𝓞 E) G'}
    (hact : ∀ a, (act'.act a).left ≫ ψ = ψ ≫ (t.act.act a).left) {g : G'.left ⟶ G'.left}
    (hgc : ∀ a, (act'.act a).left ≫ g = g ≫ (act'.act a).left) (q : Sp R ⟶ X)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p)
    (a : 𝓞 E) (c : R) (he : v ≫ (t.act.act a).left = spMap (epsMul c) ≫ v) :
    trv hψ g q v ≫ (t.act.act a).left = spMap (epsMul c) ≫ trv hψ g q v := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  have hwa : w ≫ (act'.act a).left = spMap (epsMul c) ≫ w :=
    hψ.hom_ext (by rw [Category.assoc, hact, ← Category.assoc, hw, he, Category.assoc, hw])
      (by rw [Category.assoc, Over.w, hw', Category.assoc, hw', ← Category.assoc, spMap_eps_alg])
  rw [trv_eq hψ g q w hw hw']
  simp only [Category.assoc]
  rw [← hact a, ← reassoc_of% (hgc a), reassoc_of% hwa]

theorem exists_trv_eq (hψ : IsPullback ψ G'.hom t.G.hom p) {b : X ⟶ X} {g : G'.left ⟶ G'.left}
    (hg : IsPullback g G'.hom G'.hom b) (q : Sp R ⟶ X) {w' : Sp (DualNumber R) ⟶ t.G.left}
    (hw' : w' ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ (q ≫ b) ≫ p) :
    ∃ w₀ : Sp (DualNumber R) ⟶ G'.left, w₀ ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q ∧
      w₀ ≫ g ≫ ψ = w' := by
  obtain ⟨w'', h1, h2⟩ := exists_lift hψ (q ≫ b) hw'
  refine ⟨hg.lift w'' (spMap (algebraMap R (DualNumber R)) ≫ q) (by rw [h2, Category.assoc]), hg.lift_snd _ _ _, ?_⟩
  rw [← Category.assoc, hg.lift_fst, h1]

theorem trv_injective (hψ : IsPullback ψ G'.hom t.G.hom p) {b : X ⟶ X} {g : G'.left ⟶ G'.left}
    (hg : IsPullback g G'.hom G'.hom b) (q : Sp R ⟶ X) {v₁ v₂ : Sp (DualNumber R) ⟶ t.G.left}
    (h₁ : v₁ ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p)
    (h₂ : v₂ ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) (h : trv hψ g q v₁ = trv hψ g q v₂) :
    v₁ = v₂ := by
  obtain ⟨w₁, hw₁, hw₁'⟩ := exists_lift hψ q h₁
  obtain ⟨w₂, hw₂, hw₂'⟩ := exists_lift hψ q h₂
  rw [trv_eq hψ g q w₁ hw₁ hw₁', trv_eq hψ g q w₂ hw₂ hw₂'] at h
  rw [← hw₁, ← hw₂, cancel_g_ψ hψ hg (hw₁'.trans hw₂'.symm) h]

end

theorem isCombAtG_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Y : Scheme.{0}} {t : SAB H Y} {R : Type} [CommRing R] {x0 : Sp R ⟶ Y} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {a : Fin m → R} {w₁ w₂ : Sp (DualNumber R) ⟶ t.G.left}
    (h₁ : IsCombAtG t x0 v a w₁) (h₂ : IsCombAtG t x0 v a w₂) : w₁ = w₂ := by
  obtain ⟨u, hu, e⟩ := h₁
  obtain ⟨u', hu', e'⟩ := h₂
  have : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [← e, ← e', this]

open GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections in

theorem trv_eigFrame : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {X' : Scheme.{0}} (p : X' ⟶ Y.X) (G' : Over X') [GrpObj G'] (ψ : G'.left ⟶ Y.t.G.left) (act' : OAct (𝓞 E) G') (b : X' ≅ X') (g : G'.left ⟶ G'.left) (hG : IsGrpPullback G' Y.t.G p ψ), (∀ a, (act'.act a).left ≫ ψ = ψ ≫ (Y.t.act.act a).left) → IsGrpPullback G' G' b.hom g → (∀ a, (act'.act a).left ≫ g = g ≫ (act'.act a).left) → ∀ {R : Type} [CommRing R] (φR : c.F →+* R) (q : Sp R ⟶ X') (x' : Sp R ⟶ Y.X), x' = (q ≫ b.hom) ≫ p → ∀ e : GlobalTheory.ShFam.EigFrame Y φR (q ≫ p), ∃ e' : GlobalTheory.ShFam.EigFrame Y φR x', ∀ τ i, e'.v τ i = GlobalTheory.EqvTrans.trv hG.1 g q (e.v τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Y X' p G' _ ψ act' b g hG hact hgb hgc R _ φR q x' hx' e
  subst hx'
  have hv : ∀ τ i, e.v τ i ≫ Y.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p := fun τ i => (e.tan τ i).1
  refine ⟨{ v := fun τ i => GlobalTheory.EqvTrans.trv hG.1 g q (e.v τ i)
            tan := fun τ i => GlobalTheory.EqvTrans.isTan_trv hG hgb q (e.tan τ i)
            eig := fun τ i a => GlobalTheory.EqvTrans.trv_eig hG.1 hact hgc q (hv τ i) a _ (e.eig τ i a)
            basis := ?_ }, fun τ i => rfl⟩
  intro τ w' hw' heig
  obtain ⟨w₀, hw₀, hw₀g⟩ := GlobalTheory.EqvTrans.exists_trv_eq hG.1 hgb.1 q hw'.1
  have htr : GlobalTheory.EqvTrans.trv hG.1 g q (w₀ ≫ ψ) = w' := (GlobalTheory.EqvTrans.trv_eq hG.1 g q w₀ rfl hw₀).trans hw₀g
  have hone : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w₀ = (1 : Over.mk q ⟶ G').left :=
    GlobalTheory.EqvTrans.cancel_g_ψ hG.1 hgb.1
      (by rw [Category.assoc, hw₀, ← Category.assoc, GlobalTheory.EqvTrans.spMap_fst_alg, Category.id_comp]
          exact (Over.w (1 : Over.mk q ⟶ G')).symm)
      (by rw [Category.assoc, hw₀g, hw'.2, GlobalTheory.EqvTrans.one_g_ψ hG hgb q])
  have hwt : IsTanAtG Y.t (q ≫ p) (w₀ ≫ ψ) :=
    ⟨by rw [Category.assoc, hG.1.w, ← Category.assoc, hw₀, Category.assoc],
      by rw [← Category.assoc, hone]; exact (grpPull_one hG (Over.mk q)).symm⟩
  have hwe : ∀ a : 𝓞 E, (w₀ ≫ ψ) ≫ (Y.t.act.act a).left =
      spMap (epsMul (φR (embK c τ a))) ≫ (w₀ ≫ ψ) := fun a => by
    have h0 : w₀ ≫ (act'.act a).left = spMap (epsMul (φR (embK c τ a))) ≫ w₀ :=
      GlobalTheory.EqvTrans.cancel_g_ψ hG.1 hgb.1
        (by rw [Category.assoc, Over.w, hw₀, Category.assoc, hw₀, ← Category.assoc, GlobalTheory.EqvTrans.spMap_eps_alg])
        (by rw [Category.assoc, reassoc_of% (hgc a), hact a, ← Category.assoc w₀, ← Category.assoc (w₀ ≫ g),
              Category.assoc w₀, hw₀g, heig a, Category.assoc, hw₀g])
    rw [Category.assoc, ← hact a, ← Category.assoc, h0, Category.assoc]
  obtain ⟨a, ha, huniq⟩ := e.basis τ (w₀ ≫ ψ) hwt hwe
  refine ⟨a, ?_, fun a' ha' => ?_⟩
  · have h := GlobalTheory.T.tangentTransport_equivariant_cartesian_preserves_comb Y.t p G' ψ b.hom g hG hgb q (e.v τ) a (w₀ ≫ ψ) (e.tan τ) hwt ha
    rwa [htr] at h
  · obtain ⟨u, hut, huc⟩ : ∃ u : Sp (DualNumber R) ⟶ Y.t.G.left, IsTanAtG Y.t (q ≫ p) u ∧
        IsCombAtG Y.t (q ≫ p) (e.v τ) a' u :=
      ⟨(tv (∑ i, a' i • tanOf (e.tan τ i))).left, isTan_tv _, (isComb_iff (fun i => tanOf (e.tan τ i)) a' _).2 rfl⟩
    have h1 := GlobalTheory.T.tangentTransport_equivariant_cartesian_preserves_comb Y.t p G' ψ b.hom g hG hgb q (e.v τ) a' u (e.tan τ) hut huc
    have h2 : GlobalTheory.EqvTrans.trv hG.1 g q u = w' := GlobalTheory.EqvTrans.isCombAtG_unique h1 ha'
    have h3 : u = w₀ ≫ ψ := GlobalTheory.EqvTrans.trv_injective hG.1 hgb.1 q hut.1 hwt.1 (h2.trans htr.symm)
    exact huniq a' (h3 ▸ huc)

end GlobalTheory.EqvTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCurveLatticePeriodForm
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

open scoped UpperHalfPlane

namespace GlobalTheory.CMModel

theorem j_mul_Δ_eq (F : Type) [Field F] (W : WeierstrassCurve F) [W.IsElliptic] :
    W.j * W.Δ = W.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', mul_comm]
  exact _root_.Units.mul_inv_cancel_left W.Δ' _

theorem exists_upper_of_sq_eq_neg {d : ℕ} {τ : ℂ} (hd : 0 < d) (h : τ ^ 2 = -(d : ℂ)) :
    ∃ τ₀ : ℍ, (τ₀ : ℂ) = τ ∨ (τ₀ : ℂ) = -τ := by
  have him : τ.im ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h
    simp [pow_two, h0] at h1
    have : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg τ.re]
  rcases lt_or_gt_of_ne him with hn | hp
  · exact ⟨⟨-τ, by simpa using hn⟩, Or.inr rfl⟩
  · exact ⟨⟨τ, hp⟩, Or.inl rfl⟩

theorem modularJ_mem_Qb {d : ℕ} {τ₀ : ℍ} (h : (τ₀ : ℂ) ^ 2 = -(d : ℂ)) :
    modularJ τ₀ ∈ algebraicClosure ℚ ℂ := by
  have hi : _root_.IsIntegral ℤ (modularJ τ₀) :=
    isIntegral_modularJ_of_quadratic (a := 1) (b := 0) (c := d) one_ne_zero (by push_cast; rw [h]; ring)
  exact mem_algebraicClosure_iff.2 (hi.tower_top (A := ℚ)).isAlgebraic

end GlobalTheory.CMModel

theorem GlobalTheory.CMModel.exists_curve_lattice :
    ∀ (d : ℕ) (τ : ℂ), 0 < d → τ ^ 2 = -(d : ℂ) →
  ∃ (A₀ : Over (Sp Qb)) (_ : GrpObj A₀) (A : Over (Sp ℂ)) (_ : GrpObj A) (p : A.left ⟶ A₀.left) (L : LB A.left)
    (u : HolUnif A L 1) (c : ℂ), IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension 1 A₀.hom ∧
    IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p ∧ L.IsLB ∧ c ≠ 0 ∧ ∀ z ∈ u.Λ, ∃ a b : ℤ, z 0 = c * (a + b * τ) := by
  classical
  intro d τ hd hτ
  obtain ⟨τ₀, hτ₀⟩ := GlobalTheory.CMModel.exists_upper_of_sq_eq_neg hd hτ
  have hτ₀2 : (τ₀ : ℂ) ^ 2 = -(d : ℂ) := by rcases hτ₀ with e | e <;> rw [e] <;> simp [hτ]
  let j : Qb := ⟨GlobalTheory.modularJ τ₀, GlobalTheory.CMModel.modularJ_mem_Qb hτ₀2⟩
  let W : WeierstrassCurve Qb := WeierstrassCurve.ofJ j
  have hWj : W.j = j := WeierstrassCurve.ofJ_j j
  have hΔ : IsUnit W.Δ := (inferInstance : W.IsElliptic).isUnit
  obtain ⟨P, v, Lf, ⟨hg, hv, -, hU'⟩, hLf⟩ :=
    GlobalTheory.exists_polAV_latticeFamily GlobalTheory.thetaUnifAV_all GlobalTheory.polBaseChange_holds Qb W hΔ
  let s : Qb →+* ℂ := algebraMap Qb ℂ
  obtain ⟨P', φ, h⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.polBaseChange_holds s P
  obtain ⟨v', hv', -⟩ := GlobalTheory.existsUnique_isVecOver h.2.1.1 v
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u, -, -, -, -, -, hd', -⟩ := GlobalTheory.thetaUnifAV_all P' rig hrig
  obtain ⟨w, hw, -⟩ := hd' v' (hv'.isTangent h.2.1 (hv.1 0))
  obtain ⟨hw0, hmem⟩ := hU' s P' φ v' u w h hv' hw
  have hj : s W.j = (GlobalTheory.latticeCurve (GlobalTheory.periodPairOfTau τ₀)).j := by
    rw [hWj, GlobalTheory.latticeCurve_j one_ne_zero (GlobalTheory.mem_lattice_periodPairOfTau τ₀)]
    rfl
  have e1 := congrArg s (GlobalTheory.CMModel.j_mul_Δ_eq Qb W)
  rw [map_mul, map_pow, hj, (hLf s).1, (hLf s).2.2] at e1
  have e2 := GlobalTheory.CMModel.j_mul_Δ_eq ℂ (GlobalTheory.latticeCurve (GlobalTheory.periodPairOfTau τ₀))
  rw [GlobalTheory.latticeCurve_Δ, GlobalTheory.latticeCurve_c₄] at e2
  have key : (GlobalTheory.periodPairOfTau τ₀).g₂ ^ 3 * ((Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) =
      (Lf s).g₂ ^ 3 * ((GlobalTheory.periodPairOfTau τ₀).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ₀).g₃ ^ 2) := by
    linear_combination (((GlobalTheory.periodPairOfTau τ₀).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ₀).g₃ ^ 2) * e1 -
      ((Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) * e2) / 1728
  obtain ⟨c, hc0, hc⟩ := (GlobalTheory.lattice_determined_by_invariants (GlobalTheory.periodPairOfTau τ₀) (Lf s)).2 key
  cases P' with | mk A' isAb' g' sm' L' isLB' rig' sym' amp' kt' => ?_
  have e : g' = 1 := h.1.trans hg
  subst e
  have hw00 : w 0 ≠ 0 := fun h0 => hw0 (funext fun i => by fin_cases i; exact h0)
  refine ⟨P.A, inferInstance, A', inferInstance, φ, L', u, w 0 * c, P.isAb, hg ▸ P.smoothDim, h.2.1,
    isLB', mul_ne_zero hw00 hc0, fun z hz => ?_⟩
  have hz' : z = (z 0 / w 0) • w := funext fun i => by
    fin_cases i
    simp [hw00]
  obtain ⟨x, hx, hxz⟩ := (hc _).1 ((hmem (z 0 / w 0)).2 (hz' ▸ hz))
  obtain ⟨m, n, rfl⟩ := (GlobalTheory.mem_lattice_periodPairOfTau τ₀ x).1 hx
  have hz0 : z 0 = w 0 * c * (1 * (m * (τ₀ : ℂ) + n)) := by
    rw [_root_.mul_assoc, ← hxz]
    field_simp
  rcases hτ₀ with e | e
  · exact ⟨n, m, by rw [hz0, e]; ring⟩
  · exact ⟨n, -m, by rw [hz0, e]; push_cast; ring⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfInvNatSmulMemDiscreteSubmodule
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory

theorem discrete_submodule_inv_smul_eq_zero : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → ∀ d : Fin g → ℂ, (∀ k : ℕ, 0 < k → (k : ℂ)⁻¹ • d ∈ Λ) → d = 0 := by
  intro g Λ hΛ d hd
  have hc1 : Filter.Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℂ))⁻¹) Filter.atTop (nhds 0) := by
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
  have hlim : Filter.Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℂ))⁻¹ • d) Filter.atTop (nhds 0) := by
    simpa using hc1.smul_const d
  let f : ℕ → Λ := fun k => ⟨(((k + 1 : ℕ) : ℂ))⁻¹ • d, hd (k + 1) k.succ_pos⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds 0) := by
    rw [tendsto_subtype_rng]
    simpa [f] using hlim
  rw [nhds_discrete, Filter.tendsto_pure] at hf
  obtain ⟨k, hk⟩ := hf.exists
  have h0 : (((k + 1 : ℕ) : ℂ))⁻¹ • d = 0 := congrArg Subtype.val hk
  rw [smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exfalso
    rw [inv_eq_zero] at h0
    exact (Nat.cast_ne_zero.mpr k.succ_ne_zero) h0
  · exact h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfSqZeroBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.CechPic

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ U) (x : Γ(X, U)ˣ) :
    res h1 (res h2 x) = res (h1.trans h2) x :=
  unit_ext fun y hy => by rw [gm_res _ y _ hy, gm_res _ y _ (h1 hy), gm_res _ y _ hy]

theorem app_restrict {X X₀ : Scheme.{0}} (i : X₀ ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (i.app V).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (X₀.presheaf.map (homOfLE (fun y (hy : y ∈ i ⁻¹ᵁ V) => (h hy : i y ∈ U))).op).hom ((i.app U).hom x) := by
  have e := congrArg (fun q => q.hom x) (i.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

end GlobalTheory.CechPic

namespace GlobalTheory.CechPic

end GlobalTheory.CechPic
end
end

