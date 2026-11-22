import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesAlongThetaTowerRootOfUnityPower
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineIntegralStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_integral : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    (∀ y, 0 ≤ v y ∧ v y ≤ 1) ∧ Continuous v ∧ (hY.atlas σ).SmoothOn Set.univ (fun y => (v y : ℂ)) := by
  first | exact @GlobalTheory.CosSqSmooth.cosSq_smooth | exact GlobalTheory.CosSqSmooth.cosSq_smooth | (intros; apply GlobalTheory.CosSqSmooth.cosSq_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentsBijectModuliComponents
section
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CovHt.Link

theorem exists_equiv_over : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag), ∃ q : s.Comp ≃ Comp s.Xo κ.c, ∀ k, Over Φ k (q k) := by
  intro D A N j S κ s Φ
  obtain ⟨q, hq⟩ := GlobalTheory.ShFam.PtComp.exists_equiv s
  refine ⟨q, fun k => ?_⟩
  letI := (constF κ.e (Φ.C k).Y).toAlgebra
  intro t
  have hx : (GlobalTheory.AllWt.ptF (Φ.C k).y0 ≫ s.T.Z.jQ) t = (Φ.C k).π (genericPt (Φ.C k).Y t) := by
    rw [(Φ.C k).y0_x]; rfl
  have hon : OnComp s k ((Φ.C k).π (genericPt (Φ.C k).Y t)) := by
    obtain ⟨z, hz⟩ : ((s.U κ.σ₀).X k).dom.Nonempty := GlobalTheory.OrbitScalar.exists_mem_dom _
    refine ⟨⟨z, hz⟩, fun pt => ?_⟩
    exact (isPreconnected_range (Φ.C k).π.continuous).subset_connectedComponent ⟨_, rfl⟩
      (Φ.label k ⟨z, hz⟩ pt)
  have e := (hq k _).1 hon
  show GlobalTheory.AllWt.ptF (Φ.C k).y0 t ∈ ((q k : _) : Set _)
  rw [e]
  rw [Set.mem_preimage]
  have : s.T.Z.jQ (GlobalTheory.AllWt.ptF (Φ.C k).y0 t) = (GlobalTheory.AllWt.ptF (Φ.C k).y0 ≫ s.T.Z.jQ) t := rfl
  rw [this, hx]
  exact mem_connectedComponent

end GlobalTheory.CovHt.Link
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagRefinementBundleDimEqBaseAddCardAboveDiagona
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

noncomputable section

namespace GlobalTheory.FlagCell2.Dim

theorem card_low (s : ℕ) : Fintype.card (Low s) = s.choose 2 := by
  have h₁ : Fintype.card (Low s) = ∑ i : Fin s, (Finset.Ioi i).card := by
    rw [← Finset.card_sigma, ← Finset.card_univ]
    refine Finset.card_bij' (fun s _ => ⟨s.1.2, s.1.1⟩) (fun t ht => ⟨(t.2, t.1), by simpa using ht⟩) ?_ ?_ ?_ ?_ <;>
      simp
  rw [h₁, Nat.choose_two_right]
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => s - 1 - i), Finset.sum_range_reflect (fun i => i), Finset.sum_range_id]

theorem dim_eq_of_refines {F : Type} [Field F] [CharZero F] {X Y Y' : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ}
    {E : Fr (ratOf X) m 0} {S : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X}
    {S' : Fr (ratOf Y') m m} {φ' : X.Fn →ₐ[F] Y'.Fn} {f' : Y'.X ⟶ X.X}
    (hR : Refines E S φ f) (hR' : Refines E S' φ' f') : Y.dim = Y'.dim := by
  have R₁ := hR.reps
  have R₂ := hR'.reps
  obtain ⟨ψ, hψ, hG⟩ := exists_fieldMap_coBear_generic F ι m X Y Y' E S φ f S' φ' f' R₁ R₂
  obtain ⟨h, hh⟩ := GlobalTheory.ZH.RatModel.exists_isHom_of_map_O F Y'.Fn (ratOf Y') Y.Fn (ratOf Y) ψ
    (dominates_O F ι m X Y Y' E S φ f S' φ' f' R₁ R₂ ψ hψ hG)
  have hf : h ≫ f' = f := by
    have h1 := R₂.1.comp hh
    rw [hψ] at h1
    exact h1.unique R₁.1
  have hb := CoBear₂ F ι m X Y Y' E S φ f S' φ' f' R₁ R₂ h hf
    (coBear_comp_of_isHom F ι m X Y Y' E S φ f S' φ' f' R₁ R₂ ψ hψ hG h hh)
  change Y.X ⟶ Y'.X at h
  have : IsIso h := GlobalTheory.BijPointsIso.isIso_of_bijective_points F Y Y' h hh.inducedModelMorphism_comp_structureMap fun K _ _ => hb K
  have hd : topologicalKrullDim Y.X = topologicalKrullDim Y'.X :=
    IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso h)).isHomeomorph
  rw [Y.topologicalKrullDim_eq, Y'.topologicalKrullDim_eq] at hd
  exact_mod_cast hd

theorem main : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → Y.dim = X.dim + Fintype.card (Cell m) := by
  intro F _ σ X Y ι _ m E E' φ f _ hR
  have : CharZero F := σ.charZero
  obtain ⟨Y', φ', f', S', hd, hR'⟩ := tower _ (ratOf X) X.dim E (good_ratOf X) (fun _ => Nat.zero_le _) rfl
  rw [dim_eq_of_refines hR hR', hd, Fintype.card_sigma]
  simp only [card_low, Pi.zero_apply, Nat.sub_zero]

end GlobalTheory.FlagCell2.Dim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsConnectedIrreducibleBase
section
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.FlagConnect

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPath

open Scheme.Modules in

theorem coh {X T B : Scheme.{0}} (t : X ⟶ T) (c : T ⟶ X) (s : X ⟶ B) (h : t ≫ c = 𝟙 _) (v : t ≫ c ≫ s = s)
    (E : B.Modules) :
    (pullbackComp t c).hom.app ((pullback s).obj E) ≫
      (pullbackCongr h).hom.app _ ≫ (pullbackId _).hom.app _ =
    (pullback t).map ((pullbackComp c s).hom.app E) ≫
      (pullbackComp t (c ≫ s)).hom.app E ≫ (pullbackCongr v).hom.app E := by
  have assoc := congr_arg (fun φ => φ.app E) (pseudofunctor_associativity t c s)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.rightUnitor_hom_app, Category.id_comp, Category.comp_id, eqToHom_app] at assoc
  have key : ∀ (u : X ⟶ X) (hu : u = 𝟙 X) (w : X ⟶ B) (hw : w = u ≫ s) (v' : w = s)
      (P : (pullback w).obj E = (pullback (u ≫ s)).obj E),
      eqToHom P ≫ (pullbackComp u s).inv.app E ≫ (pullbackCongr hu).hom.app _ ≫ (pullbackId X).hom.app _ =
        (pullbackCongr v').hom.app E := by
    intro u hu w hw v' P
    subst hu hw
    have unit := congr_arg (fun φ => φ.app E) (pseudofunctor_right_unitality s)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Category.comp_id, eqToHom_app] at unit
    simp only [eqToHom_refl, Category.id_comp, pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
    erw [Category.comp_id ((pullbackId X).hom.app ((pullback s).obj E))] at unit
    erw [Category.id_comp ((pullbackId X).hom.app ((pullback s).obj E))]
    erw [unit]
    simp [eqToIso.hom, eqToHom_app]
  have e1 : (pullbackComp t c).hom.app ((pullback s).obj E) =
      (pullback t).map ((pullbackComp c s).hom.app E) ≫ (pullbackComp t (c ≫ s)).hom.app E ≫
        eqToHom (by rw [Category.assoc]) ≫ (pullbackComp (t ≫ c) s).inv.app E := by
    rw [← cancel_epi ((pullbackComp t (c ≫ s)).inv.app E ≫ (pullback t).map ((pullbackComp c s).inv.app E)),
      ← cancel_mono ((pullbackComp (t ≫ c) s).hom.app E)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [assoc]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    simp
  rw [e1]
  simp only [Category.assoc]
  congr 2
  exact key _ h _ (Category.assoc _ _ _).symm v _

open Scheme.Modules in

theorem carries_of {X T B : Scheme.{0}} (s : X ⟶ B) (c : T ⟶ X) (t : X ⟶ T) (h : t ≫ c = 𝟙 X) {ι : Type}
    (E : ι → B.Modules) (r : ι → ℕ) (G₁ G' : ∀ a, Vert.Flag ((pullback s).obj (E a)) (r a))
    (Φ : ∀ a, (pullback c).obj ((pullback s).obj (E a)) ≅ (pullback c).obj ((pullback s).obj (E a)))
    (ψ : ∀ a, (pullback s).obj (E a) ≅ (pullback s).obj (E a))
    (hΦ : ∀ a, (pullback t).map (Φ a).hom ≫ (pullbackComp t c).hom.app _ ≫ (pullbackCongr h).hom.app _ ≫
      (pullbackId X).hom.app _ = ((pullbackComp t c).hom.app _ ≫ (pullbackCongr h).hom.app _ ≫
      (pullbackId X).hom.app _) ≫ (ψ a).hom)
    (hψ : ∀ a i, ∃ e : (G₁ a).F i ≅ (G' a).F i, e.hom ≫ (G' a).ι i = (G₁ a).ι i ≫ (ψ a).hom)
    (v : t ≫ c ≫ s = s) :
    Carries (c ≫ s) E r (fun a => ((G₁ a).pull c).ofIso (Φ a ≪≫ (pullbackComp c s).app (E a))) t s v G' := by
  intro a i
  obtain ⟨e, he⟩ := hψ a i
  refine ⟨(pullbackComp t c).app _ ≪≫ (pullbackCongr h).app _ ≪≫ (pullbackId X).app _ ≪≫ e, ?_⟩
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc, he]
  simp only [Vert.Flag.ofIso, Vert.Flag.pull, Functor.map_comp, Category.assoc, Iso.trans_hom, Iso.app_hom]
  rw [← coh t c s h v (E a)]
  simp only [Category.assoc] at hΦ
  rw [hΦ a, he]
  erw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
  rfl

theorem exists_irreducible_family : ∀ (L : Type) [Field L] (B : Scheme.{0}) (s : Spec (CommRingCat.of L) ⟶ B)
    (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ)
    (G₁ G₂ : ∀ a, Vert.Flag ((Scheme.Modules.pullback s).obj (E a)) (r a)),
    ∃ (T : Scheme.{0}) (g : T ⟶ B) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T)
      (G : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)) (v₁ : t₁ ≫ g = s) (v₂ : t₂ ≫ g = s),
      IrreducibleSpace T ∧ Carries g E r G t₁ s v₁ G₁ ∧ Carries g E r G t₂ s v₂ G₂ := by
  intro L _ B s ι _ E r G₁ G₂
  choose φ hφ using fun a => GlobalTheory.T.field_flags_conjugate_by_automorphism L _ (r a) (G₁ a) (G₂ a)
  obtain ⟨T, c, t₁, t₂, h₁, h₂, Φ, hT, hΦ₁, hΦ₂⟩ := GlobalTheory.T.flags_over_field_irreducible_join L ι
    (fun a => (Scheme.Modules.pullback s).obj (E a)) r (fun a => (G₁ a).isVB_self) φ
  have v₁ : t₁ ≫ c ≫ s = s := by rw [← Category.assoc, h₁, Category.id_comp]
  have v₂ : t₂ ≫ c ≫ s = s := by rw [← Category.assoc, h₂, Category.id_comp]
  refine ⟨T, c ≫ s, t₁, t₂, fun a => ((G₁ a).pull c).ofIso (Φ a ≪≫ (Scheme.Modules.pullbackComp c s).app (E a)),
    v₁, v₂, hT, ?_, ?_⟩
  · exact carries_of s c t₁ h₁ E r G₁ G₁ Φ (fun _ => Iso.refl _) (fun a => by rw [hΦ₁ a]; simp)
      (fun _ _ => ⟨Iso.refl _, by simp⟩) v₁
  · exact carries_of s c t₂ h₂ E r G₁ G₂ Φ φ hΦ₂ hφ v₂

end GlobalTheory.FlagPath

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartComplComplexPointsInOpenEqZero
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2Null

theorem part_compl_ptsIn : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (Y : Var F) (β : (atlas Y σ).Fld) (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ s : ℤˣ, (atlas Y σ).part β s (ptsIn Y.str σ W)ᶜ = 0 := by
  intro F _ σ Y β W hW s
  exact GlueCoverNull.glueMeas_null _ _ (isOpen_ptsIn _).measurableSet.compl fun c =>
    GlobalTheory.Mean4O.CoverInt.volume_image_compl_ptsIn F Y.X Y.str σ σ.injective
      (fun W hW => (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str W).injective) W hW _ c

end GlobalTheory.FlagCell2Null
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartEqLintegralImageInjectiveHolomorphic
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

open Function

namespace GlobalTheory.FlagCell2.ChangeOfVariables

theorem part_eq_lintegral_image : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (β : A.Fld), A.IsForm β → ∀ (Ω : Set M) (Φ : M → V n) (γ : V n → Alt n), IsOpen Ω → Set.InjOn Φ Ω → (∀ x : A.Pt, x.pt ∈ Ω → DifferentiableAt ℂ (Φ ∘ x.ch.symm) x.crd ∧ β x = pull (fderiv ℂ (Φ ∘ x.ch.symm) x.crd) (γ (Φ x.pt))) → ∀ (s : ℤˣ) (T : Set M), MeasurableSet T → T ⊆ Ω → A.part β s T = ∫⁻ v in Φ '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (γ v)).re) := by
  intro M _ _ _ _ _ n A β hβ Ω Φ γ hΩ hinj hloc s T hT hTΩ
  set ρ : A.ι → M → ℝ≥0∞ := fun k y => ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β k (A.e k y))).re) with hρ
  have hp : A.part β s = ChartGlue.glueMeas A.e ρ := rfl
  have hρc : ∀ k l y, y ∈ (A.e k).source → y ∈ (A.e l).source →
      ρ k y = ENNReal.ofReal (‖ChartGlue.transDet (A.e k) (A.e l) y‖ ^ 2) * ρ l y := by
    intro k l y hk hl
    have h1 := A.loc_crd β (⟨(k, y), hk⟩ : A.Pt)
    have h2 := A.loc_crd β (⟨(l, y), hl⟩ : A.Pt)
    have h3 := hβ.compat (⟨(k, y), hk⟩ : A.Pt) ⟨(l, y), hl⟩ rfl
    simp only [hρ]
    erw [h1, h2, h3, dens_pull]
    rw [Complex.re_ofReal_mul, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [ChartGlue.transDet]
    ring

  have chart : ∀ (i : A.ι) (P : Set M), MeasurableSet P → P ⊆ (A.e i).source → P ⊆ Ω →
      MeasurableSet (Φ '' P) ∧ A.part β s P =
        ∫⁻ v in Φ '' P, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (γ v)).re) := by
    intro i P hP hPs hPΩ
    set g : V n → V n := Φ ∘ (A.e i).symm with hg
    have hQ : MeasurableSet (A.e i '' P) := ChartGlue.measurableSet_image (A.e i) hP hPs
    have hder : ∀ v ∈ A.e i '' P, HasFDerivWithinAt g ((fderiv ℂ g v).restrictScalars ℝ) (A.e i '' P) v := by
      rintro _ ⟨y, hy, rfl⟩
      exact ((hloc ⟨(i, y), hPs hy⟩ (hPΩ hy)).1.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    have hinjg : Set.InjOn g (A.e i '' P) := by
      rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hyz
      simp only [hg, Function.comp_apply, (A.e i).left_inv (hPs hy), (A.e i).left_inv (hPs hz)] at hyz
      rw [hinj (hPΩ hy) (hPΩ hz) hyz]
    have himg : Φ '' P = g '' (A.e i '' P) := by
      rw [Set.image_image]
      exact Set.image_congr fun y hy => by simp only [hg, Function.comp_apply, (A.e i).left_inv (hPs hy)]
    refine ⟨himg ▸ measurable_image_of_fderivWithin hQ hder hinjg, ?_⟩
    rw [hp, ChartGlue.glueMeas_apply A.e ρ A.holo hρc i hP hPs, ChartGlue.chartMeas_apply_of_subset _ _ hP hPs, himg,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hQ hder hinjg]
    refine setLIntegral_congr_fun hQ ?_
    rintro _ ⟨y, hy, rfl⟩
    have hx := hloc ⟨(i, y), hPs hy⟩ (hPΩ hy)
    have hl := A.loc_crd β (⟨(i, y), hPs hy⟩ : A.Pt)
    have hdet : ((fderiv ℂ g (A.e i y)).restrictScalars ℝ).det = Algebra.norm ℝ (fderiv ℂ g (A.e i y)).det :=
      LinearMap.det_restrictScalars (f := (fderiv ℂ g (A.e i y) : V n →ₗ[ℂ] V n))
    have hx2 : β ⟨(i, y), hPs hy⟩ = pull (fderiv ℂ g (A.e i y)) (γ (Φ y)) := hx.2
    have hgy : g (A.e i y) = Φ y := by simp only [hg, Function.comp_apply, (A.e i).left_inv (hPs hy)]
    beta_reduce
    rw [hdet, hgy]
    simp only [hρ, (A.e i).left_inv (hPs hy)]
    erw [hl, hx2, dens_pull]
    rw [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity),
      Complex.re_ofReal_mul, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

  rcases Set.eq_empty_or_nonempty T with rfl | ⟨y₀, -⟩
  · simp
  obtain ⟨C, hCc, hCU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun j => (A.e j).source)
    (fun j => (A.e j).open_source)
  obtain ⟨f, hf⟩ := (hCc.insert (A.cover y₀).choose).exists_eq_range (Set.insert_nonempty _ _)
  set U : ℕ → Set M := fun k => (A.e (f k)).source with hU
  have hUo : ∀ k, IsOpen (U k) := fun k => (A.e (f k)).open_source
  set P : ℕ → Set M := fun k => T ∩ disjointed U k with hPdef
  have hPm : ∀ k, MeasurableSet (P k) := fun k =>
    hT.inter (MeasurableSet.disjointed (fun k => (hUo k).measurableSet) k)
  have hPU : ∀ k, P k ⊆ U k := fun k => Set.inter_subset_right.trans (disjointed_subset U k)
  have hPΩ : ∀ k, P k ⊆ Ω := fun k => Set.inter_subset_left.trans hTΩ
  have hPd : Pairwise (Disjoint on P) := (disjoint_disjointed U).mono fun k l h =>
    h.mono Set.inter_subset_right Set.inter_subset_right
  have hTP : T = ⋃ k, P k := by
    rw [← Set.inter_iUnion, iUnion_disjointed, eq_comm, Set.inter_eq_left]
    intro y _
    have hy : y ∈ ⋃ j, (A.e j).source := Set.mem_iUnion.2 (A.cover y)
    rw [← hCU] at hy
    obtain ⟨l, hl, hy⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨k, rfl⟩ := hf.le (Set.mem_insert_of_mem _ hl)
    exact Set.mem_iUnion.2 ⟨k, hy⟩
  have hIm : ∀ k, MeasurableSet (Φ '' P k) := fun k => (chart (f k) (P k) (hPm k) (hPU k) (hPΩ k)).1
  have hId : Pairwise (Disjoint on fun k => Φ '' P k) := by
    intro k l hkl
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have := hinj (hPΩ l hy) (hPΩ k hx) hxy
    subst this
    exact Set.disjoint_left.1 (hPd hkl) hx hy
  rw [hTP, Set.image_iUnion, measure_iUnion hPd hPm, lintegral_iUnion hIm hId]
  exact tsum_congr fun k => (chart (f k) (P k) (hPm k) (hPU k) (hPΩ k)).2

end GlobalTheory.FlagCell2.ChangeOfVariables
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartSubsetChartEqLintegralImage
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FlagCell2

theorem part_subset_chart : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (β : A.Fld), A.IsForm β → ∀ (s : ℤˣ) (i : A.ι) (T : Set M), MeasurableSet T → T ⊆ (A.e i).source → A.part β s T = ∫⁻ v in A.e i '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β i v)).re) := by
  intro M _ _ _ _ _ n A β hβ s i T hT hTi
  set ρ : A.ι → M → ENNReal := fun k y => ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β k (A.e k y))).re) with hρ
  have hp : A.part β s = ChartGlue.glueMeas A.e ρ := rfl
  have hρc : ∀ k l y, y ∈ (A.e k).source → y ∈ (A.e l).source →
      ρ k y = ENNReal.ofReal (‖ChartGlue.transDet (A.e k) (A.e l) y‖ ^ 2) * ρ l y := by
    intro k l y hk hl
    have h1 := A.loc_crd β (⟨(k, y), hk⟩ : A.Pt)
    have h2 := A.loc_crd β (⟨(l, y), hl⟩ : A.Pt)
    have h3 := hβ.compat (⟨(k, y), hk⟩ : A.Pt) ⟨(l, y), hl⟩ rfl
    simp only [hρ]
    erw [h1, h2, h3, dens_pull]
    rw [Complex.re_ofReal_mul, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [ChartGlue.transDet]
    ring
  rw [hp, ChartGlue.glueMeas_apply A.e ρ A.holo hρc i hT hTi, ChartGlue.chartMeas_apply_of_subset _ _ hT hTi]
  refine setLIntegral_congr_fun (ChartGlue.measurableSet_image _ hT hTi) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [hρ, (A.e i).left_inv (hTi hy)]

end GlobalTheory.FlagCell2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalPointsAbelianPartsMultiplyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_points_abelian_parts_multiply : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (h h' : (𝟙_ (Over (Sp V))) ⟶ G) (g g' g'' : GtPt D.toPre (𝟙_ (Over (Sp V)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g → GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h' g' → GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre (h * h') g'' → g''.b = g.b * g'.b := by
  first | exact @GlobalTheory.Poinc.Sep.FormalMul.b_mul | exact GlobalTheory.Poinc.Sep.FormalMul.b_mul | (intros; apply GlobalTheory.Poinc.Sep.FormalMul.b_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemIndexZeroCoefficientApproxStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTermSystem_indexZero_coefficient_approx : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), 3 ≤ N₁ → Φ.Exact N₁ → Φ.abelian₂ → Φ.Four N₁ → (∀ y y', Φ.m y ≠ 1 → Φ.m y' ≠ 1 → y = y') → ∀ (c₀ : Φ.Q) (e : ℕ), ∃ a : A, ∀ y, Φ.ev y a - Φ.u y 0 c₀ ∈ (maximalIdeal A ^ e).map (Φ.ev y) := by
  first | exact @GlobalTheory.Poinc.Sep.coeffZero_approx | exact GlobalTheory.Poinc.Sep.coeffZero_approx | (intros; apply GlobalTheory.Poinc.Sep.coeffZero_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesAlongThetaTowerRootOfUnityPowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_along_theta_tower_root_of_unity_power : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act), ∃ k : X₁.S.Gam → ℕ,
    ∀ (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ)
      (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (X' : Type) [AddCommGroup X'] (m' : ℕ) (t' : Fin m' → V')
      (δ' : Fin m' → LinearMap.BilinForm ℤ X') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X' t' δ') (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left)
      (w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), w.IsGen → 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ →
    ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∃ c : (FractionRing V')ˣ, ∀ b, FrPull w f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b)
      ((c : FractionRing V') * 𝔪₂.yK ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b) := by
  first | exact @GlobalTheory.Poinc.Sep.BaseTerms.frames_along_tower | exact GlobalTheory.Poinc.Sep.BaseTerms.frames_along_tower | (intros; apply GlobalTheory.Poinc.Sep.BaseTerms.frames_along_tower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
section
set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory.PDiv

def frobKerIdeal (p : ℕ) (R H : Type) [CommRing R] [CommRing H] [Bialgebra R H] : Ideal H :=
  Ideal.span ((fun a : H => a ^ p) '' (augIdeal R H : Set H))

theorem pow_mem_frobKerIdeal {p : ℕ} {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H] {a : H}
    (ha : a ∈ augIdeal R H) : a ^ p ∈ frobKerIdeal p R H :=
  Ideal.subset_span ⟨a, ha, rfl⟩

theorem frobKerIdeal_le_augIdeal {p : ℕ} (hp : p ≠ 0) (R H : Type) [CommRing R] [CommRing H]
    [Bialgebra R H] : frobKerIdeal p R H ≤ augIdeal R H :=
  Ideal.span_le.2 fun _ ⟨a, ha, e⟩ => e ▸ Ideal.pow_mem_of_mem _ ha p (Nat.pos_of_ne_zero hp)

end GlobalTheory.PDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFromPageEstimateStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_from_page_estimate : PageSt → GeoSt := by
  first | exact @GlobalTheory.BigOn.geoSt_of_pageSt | exact GlobalTheory.BigOn.geoSt_of_pageSt | (intros; apply GlobalTheory.BigOn.geoSt_of_pageSt <;> assumption)
end

