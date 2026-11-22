import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpacePullbackEigenDeterminantDivisorEqGraded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyLiftUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2725
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2615
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointTautologicalFrame
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res)
open GlobalTheory.Twist (resM resM_resM app_resM resM_self)

namespace GlobalTheory.FlagZ.LocTaut

variable {S T Y Z : Scheme.{0}}

def compIso (j : S ⟶ T) [IsOpenImmersion j] (f : T ⟶ Y) :
    Scheme.Modules.pullback (j ≫ f) ≅ Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor j :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ f)).ofNatIsoRight
      (Scheme.Modules.pushforwardComp j f).symm).leftAdjointUniq
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (Scheme.Modules.restrictAdjunction j))

theorem compIso_app_pullbackSections (j : S ⟶ T) [IsOpenImmersion j] (f : T ⟶ Y) (G : Y.Modules)
    (h : ⊤ ≤ (j ≫ f) ⁻¹ᵁ ⊤) (h' : j ''ᵁ ⊤ ≤ f ⁻¹ᵁ ⊤) (s : Γ(G, ⊤)) :
    ((compIso j f).hom.app G).app ⊤ (pullbackSections (j ≫ f) G h s) = pullbackSections f G h' s := by
  have := Adjunction.unit_leftAdjointUniq_hom_app
    ((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ f)).ofNatIsoRight
      (Scheme.Modules.pushforwardComp j f).symm)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (Scheme.Modules.restrictAdjunction j)) G
  have H := congr(($this).app ⊤ s)
  refine Eq.trans ?_ H
  exact congrArg _ (QCoh.res_self _ le_rfl _)

theorem pullbackComp_hom_app (b : S ⟶ Y) (a : Y ⟶ Z) (E : Z.Modules) {U : Z.Opens} {V : Y.Opens}
    {W : S.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : W ≤ b ⁻¹ᵁ V) (h : W ≤ (b ≫ a) ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a).hom.app E).app W
      (pullbackSections b _ h₂ (pullbackSections a E h₁ s)) = pullbackSections (b ≫ a) E h s := by
  rw [← Vert.DivPull.pullbackComp_inv_app b a E h₁ h₂ h]
  exact congr(($((Scheme.Modules.pullbackComp b a).inv_hom_id_app E)).app W _)

theorem exists_frame_image (j : S ⟶ T) [IsOpenImmersion j] (f : T ⟶ Y) (p : S ⟶ Y) (hp : p = j ≫ f) (q : Y ⟶ Z)
    (E : Z.Modules) (F : Y.Modules) (i : F ⟶ (Scheme.Modules.pullback q).obj E) {κ μ : Type} [Fintype κ] [Fintype μ]
    (e : μ → Γ(E, ⊤)) (c : κ → μ → Γ(S, ⊤)) (s : κ → Γ((Scheme.Modules.pullback p).obj F, ⊤)) (hs : IsFrame s)
    (h₀ : ⊤ ≤ (p ≫ q) ⁻¹ᵁ ⊤)
    (h : ∀ k, ((Scheme.Modules.pullback p).map i ≫ (Scheme.Modules.pullbackComp p q).hom.app E).app ⊤ (s k) =
      ∑ m, c k m • pullbackSections (p ≫ q) E h₀ (e m))
    (V : T.Opens) (hV : V ≤ j ''ᵁ ⊤) (h₁ : V ≤ (f ≫ q) ⁻¹ᵁ ⊤) :
    ∃ t : κ → Γ((Scheme.Modules.pullback f).obj F, V), IsFrame t ∧ ∀ k,
      ((Scheme.Modules.pullback f).map i ≫ (Scheme.Modules.pullbackComp f q).hom.app E).app V (t k) =
        ∑ m, resG T hV ((j.appIso ⊤).inv (c k m)) • pullbackSections (f ≫ q) E h₁ (e m) := by
  subst hp
  let t : κ → Γ((Scheme.Modules.pullback f).obj F, j ''ᵁ ⊤) := fun k => ((compIso j f).hom.app F).app ⊤ (s k)
  have ht : IsFrame t := (isFrame_restrict_iff j t).1 (hs.map_iso ((compIso j f).hom.app F))
  refine ⟨_, ht.res hV, fun k => ?_⟩
  have h2 : ((Scheme.Modules.pullback (j ≫ f)).map i).app ⊤ (s k) =
      ∑ m, c k m • pullbackSections (j ≫ f) _ (V := ⊤) le_top (pullbackSections q E (U := ⊤) le_top (e m)) := by
    refine (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.pullbackComp (j ≫ f) q).hom.app E).app ⊤)).1 ((h k).trans ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Scheme.Modules.Hom.app_smul, pullbackComp_hom_app]
  have h3 : ((Scheme.Modules.pullback f).map i).app (j ''ᵁ ⊤) (t k) =
      ∑ m, (j.appIso ⊤).inv (c k m) • pullbackSections f _ (V := ⊤) le_top (pullbackSections q E (U := ⊤) le_top (e m)) := by
    have hn := congr(($((compIso j f).hom.naturality i)).app ⊤ (s k))
    refine hn.symm.trans ?_
    refine (congrArg (((compIso j f).hom.app _).app ⊤) h2).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Scheme.Modules.Hom.app_smul, compIso_app_pullbackSections j f _ _ le_top]
    rfl
  refine (app_resM _ hV _).trans ?_
  refine (congrArg (fun x => resM _ hV (((Scheme.Modules.pullbackComp f q).hom.app E).app _ x)) h3).trans ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Scheme.Modules.Hom.app_smul, pullbackComp_hom_app f q E _ _ le_top, Twist.resM_smul]
  exact congrArg _ (res_pullbackSections _ _ _ _ _)

theorem exists_frame_pullback_taut : ∀ (ι : Type) [Fintype ι] (N : ℕ)
    (fl : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N)) N), Taut.IsTaut ι N fl →
    ∀ (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (g' : T ⟶ Fl ι N) (w : g' ≫ flStr ι N = g) (V : T.Opens) (hV : IsAffineOpen V)
    (G : ι → GL (Fin N) Γ(T, V)), V.ι ≫ g' = hV.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G →
    ∀ (a : ι) (l : Fin (N + 1)),
    ∃ s : Fin l → Γ((Scheme.Modules.pullback g').obj ((fl a).F l), V), IsFrame s ∧ ∀ j,
      ((Scheme.Modules.pullback g').map ((fl a).ι l) ≫
        (Scheme.Modules.pullbackComp g' (flStr ι N)).hom.app (Taut.stdE N) ≫
          (Scheme.Modules.pullbackCongr w).hom.app (Taut.stdE N)).app V (s j) =
        Loc.colSecOn g V (G a).1 (Fin.castLE l.is_le j) := by
  intro ι _ N fl hfl T g g' w V hV G hG a l
  subst w
  obtain ⟨s, hs, h⟩ := hfl Γ(T, V) G a l
  have hp : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G = hV.fromSpec ≫ g' := by
    rw [IsAffineOpen.fromSpec, Category.assoc, hG]
    exact (hV.isoSpec.inv_hom_id_assoc _).symm
  obtain ⟨t, ht, h'⟩ := exists_frame_image hV.fromSpec g' _ hp (flStr ι N) (Taut.stdE N) _ ((fl a).ι l)
    (freeFrame (Sp ℤ) (Fin N)) _ s hs _ h V (QCoh.fromSpec_image_top hV).ge le_top
  refine ⟨t, ht, fun k => (h' k).trans (Finset.sum_congr rfl fun m _ => ?_)⟩
  congr 1
  have := QCoh.fromSpec_appIso_inv_res hV ⊤ ((G a).1 m (Fin.castLE l.is_le k))
  rw [show ∀ x, (Spec Γ(T, V)).presheaf.map (⊤ : (Spec Γ(T, V)).Opens).leTop.op x = x from
    QCoh.res_self_ring (X := Spec Γ(T, V)) le_rfl] at this
  refine (congrArg (resG T _) this).trans ?_
  exact (LB.resG_resG _ _ _).trans (LB.resG_self _ _)

end GlobalTheory.FlagZ.LocTaut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpacePullbackEigenDeterminantDivisorEqGradedStatement
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
theorem _root_.GlobalTheory.T.flagSpacePullback_eigenDeterminantDivisor_eq_gradedLines : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)) (a : (E →+* ℂ) → ℤ) (D : CartierDiv (X₀ TF.Y Z)), (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ s₀ TF.Y Z = spMap φ₀ → (∀ (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι)) (fK : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)), (X₀ TF.Y Z).fromSpecStalk x ≫ s₀ TF.Y Z = spMap φ → f.IsMap (algebraMap _ (X₀ TF.Y Z).functionField) fK → D.IsEqn x (∏ τ, (fK.isUnit_det_co f₀ τ).unit ^ (-a τ))) → CechPic.pull (π₀ TF.X Z) (cls (toLB D) (isLB_toLB D)) = cls (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1) (LB.isLB_pull (TF.X.F.isLB_LL _) _) := by
  first | exact @GlobalTheory.EigDivPic.pull_toLB_eq | exact GlobalTheory.EigDivPic.pull_toLB_eq | (intros; apply GlobalTheory.EigDivPic.pull_toLB_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStalkColumnSpan
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

noncomputable section

namespace GlobalTheory.FlagZ.Univ

theorem colSpan_le_of_inv_mul {X : Scheme.{0}} {N : ℕ} {x : X} (g h : GL (Fin N) (X.presheaf.stalk x)) (l : ℕ)
    (H : ∀ i j : Fin N, (j : ℕ) < l → l ≤ (i : ℕ) → (g⁻¹ * h).1 i j = 0) :
    colSpan h.1 l ≤ colSpan g.1 l := by
  refine Submodule.span_le.2 ?_
  rintro v ⟨j, hj, rfl⟩
  set b := stalkStd X N x
  set c := (g⁻¹ * h).1 with hc
  have hh : h.1 = g.1 * c := by
    rw [hc, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have e : ∑ i, h.1 i j • b i = ∑ k, c k j • ∑ i, g.1 i k • b i := by
    simp_rw [Finset.smul_sum, smul_smul, hh, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  rw [e]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : (k : ℕ) < l
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
  · rw [H k j hj (not_lt.1 hk), zero_smul]
    exact Submodule.zero_mem _

theorem stalkStep_eq_colSpan : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : ℕ) (y : Fl ι N)
    (g : ι → GL (Fin N) ((Fl ι N).presheaf.stalk y)),
    flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g = (Fl ι N).fromSpecStalk y →
      stalkStep ι N τ l y = colSpan (g τ).1 l := by
  intro ι _ N τ l y g hg
  have key : ∀ g h : ι → GL (Fin N) ((Fl ι N).presheaf.stalk y),
      flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g = flagPt Prod.fst Prod.snd h →
        colSpan (h τ).1 l ≤ colSpan (g τ).1 l := by
    intro g h e
    refine colSpan_le_of_inv_mul _ _ l fun i j hj hi => ?_
    have hlN : l < N + 1 := by omega
    exact (flagPt_eq_iff_below ι (ι × Fin (N + 1)) N Prod.fst Prod.snd _ g h).1 e τ i j
      ⟨(τ, ⟨l, hlN⟩), rfl, hj, hi⟩
  refine le_antisymm (iInf_le_of_le g (iInf_le _ hg)) (le_iInf fun h => le_iInf fun hh => ?_)
  exact key h g (hh.trans hg.symm)

end GlobalTheory.FlagZ.Univ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyLiftUniqueStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_variety_lift_unique : ∀ (ι : Type) [Fintype ι] (N : ℕ) (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (fl' : ι → Vert.Flag ((Scheme.Modules.pullback g).obj (freeModule (Sp ℤ) (Fin N))) N) (g₁ g₂ : T ⟶ Fl ι N), Lifts g fl' g₁ → Lifts g fl' g₂ → g₁ = g₂ := by
  first | exact @GlobalTheory.FlagZ.Univ.Uniq.lifts_unique | exact GlobalTheory.FlagZ.Univ.Uniq.lifts_unique | (intros; apply GlobalTheory.FlagZ.Univ.Uniq.lifts_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDescentSectionsInjectiveEqualizerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_descent_sections_injective_equalizer : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ V : Y.Opens, Function.Injective (p.app V).hom ∧ ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  first | exact @GlobalTheory.descend_of_equalised_fibreSquare | exact GlobalTheory.descend_of_equalised_fibreSquare | (intros; apply GlobalTheory.descend_of_equalised_fibreSquare <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOpenPartGroupSchemeProductMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_openPart_groupScheme_productMap : ∀ (T : Scheme.{0}) (H V : Over T) [GrpObj H] (e : V ⟶ H), IsOpenImmersion e.left → Flat H.hom → Flat ((fst V V ≫ e) * (snd V V ≫ e)).left := by
  first | exact @GlobalTheory.Mum.FlatMul.main | exact GlobalTheory.Mum.FlatMul.main | (intros; apply GlobalTheory.Mum.FlatMul.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorGaloisInjectiveInvariantsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_tensor_galois_injective_invariants : ∀ (R R' O : Type) [CommRing R] [CommRing R'] [Algebra R R'] [CommRing O] [Algebra R O] [Module.Flat R O],
    Function.Injective (algebraMap R R') → GlobalTheory.Mum.IsGal (algebraMap R R') →
    Function.Injective (algebraMap O (TensorProduct R O R')) ∧
    ∀ t : TensorProduct R O R', (∀ σ, GlobalTheory.InvAlg.galTensor O σ t = t) →
      t ∈ Set.range (algebraMap O (TensorProduct R O R')) := by
  first | exact @GlobalTheory.InvAlg.flat_tensor_invariants | exact GlobalTheory.InvAlg.flat_tensor_invariants | (intros; apply GlobalTheory.InvAlg.flat_tensor_invariants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrderWedgeEqOfEtaleTowerHeightOnePrime
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FieldPair

theorem formOrd_append_of_ord_eq : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (P : Place cL) (P0 : Place cK),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → P.IsPrimeOf T → P0.IsPrimeOf R →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = P0.ord (g : K)) →
  P.formOrd (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) = P0.formOrd (dForm cK (fun i => (x i : K))) := by
  intro K L _ _ cK cL n r R T ι ψ τ x P P0 hE hx hP hP0 hord
  have hιinj : Function.Injective ι := fun a b h => by
    have := congrArg ψ h
    rwa [hE.retr, hE.retr] at this
  haveI : IsFractionRing R K := IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hE.base.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, eq_div_of_mul_eq hb0 e⟩
  have hginj : Function.Injective (T.subtype.comp ι) := Subtype.val_injective.comp hιinj
  let j : K →+* L := IsFractionRing.lift hginj
  have hj : ∀ g : R, j (g : K) = (ι g : L) := fun g => IsFractionRing.lift_algebraMap hginj g
  have hordK : ∀ f : K, f ≠ 0 → P.ord (j f) = P0.ord f := by
    intro f hf
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hE.base.frac f
    have ha0 : a ≠ 0 := by rw [← e]; exact mul_ne_zero hf hb0
    have ef : f = a * b⁻¹ := by rw [← e, mul_inv_cancel_right₀ hb0]
    have hjb : j b ≠ 0 := (map_ne_zero j).2 hb0
    have hja : j a ≠ 0 := (map_ne_zero j).2 ha0
    have hga : (⟨a, ha⟩ : R) ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
    have hgb : (⟨b, hb⟩ : R) ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
    have h1 := hord _ hga
    have h2 := hord _ hgb
    rw [← hj] at h1 h2
    rw [ef, map_mul, map_inv₀, P.ord_mul hja (inv_ne_zero hjb), P.ord_inv,
      P0.ord_mul ha0 (inv_ne_zero hb0), P0.ord_inv]
    simp only at h1 h2
    rw [h1, h2]
  have hA : ∀ f ∈ P0.ring, j f ∈ P.ring := by
    intro f hf
    by_cases h0 : f = 0
    · rw [h0, map_zero]; exact P.ring.zero_mem
    · have hj0 : j f ≠ 0 := (map_ne_zero j).2 h0
      rw [← P.ord_nonneg_iff hj0, hordK f h0, P0.ord_nonneg_iff h0]
      exact hf
  have hτ : ∀ i, (τ i : L) ∈ P.ring := fun i => hP.1 _ (τ i).2
  let ρ : P0.ring →+* P.ring := j.restrict P0.ring P.ring hA
  let τ' : Fin r → P.ring := fun i => ⟨τ i, hτ i⟩
  have hc : ρ.comp P0.const = P.const := by
    ext a
    change j (cK a) = cL a
    have := hj ⟨cK a, hE.base.const_mem a⟩
    rw [hE.const a] at this
    exact this
  have hFE := GlobalTheory.T.formallyEtale_polynomialPlace_to_place cK cL r R T ι ψ τ P P0 j hE hP hP0 hj hA hτ

  letI := P0.const.toAlgebra
  letI := cK.toAlgebra
  haveI : IsScalarTower ℂ P0.ring K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType ℂ P0.ring := P0.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ P0.ring
  obtain ⟨t0, ht0⟩ := IsDiscreteValuationRing.exists_irreducible P0.ring
  obtain ⟨m, z, b, -, hb⟩ := exists_basis_kaehler_uniformiser ℂ ht0
  have h1 := trdeg_eq_of_basis_kaehler ℂ K b
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  rw [h1, Cardinal.mk_fin] at h2
  obtain rfl : n = m + 1 := by exact_mod_cast h2
  have hω0 : IsFreeGen P0.ring (dForm P0.const z) := isFreeGen_dForm z b hb
  have hF : IsFreeGen P.ring (dForm P.const (Fin.append τ' (fun i => ρ (z i)))) :=
    GlobalTheory.T.isFreeGen_wedgeForm_of_formallyEtale_mvPolynomial P0.const P.const ρ hc z b hb τ' hFE
  haveI : Algebra.FormallyEtale P0.ring K := .of_isLocalization (nonZeroDivisors P0.ring)
  let bK : Module.Basis (Fin (m + 1)) K (Omega cK) :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ P0.ring K).basis b
  have hbK : ∀ i, bK i = dFun cK (z i : K) := by
    intro i
    simp only [bK, IsBaseChange.basis_apply, hb]
    exact KaehlerDifferential.map_D ℂ ℂ P0.ring K (z i)
  have hrat0 : P0.toRat (m + 1) (dForm P0.const z) = dForm cK (fun i => (z i : K)) :=
    formMap_dForm _ rfl z
  have hratP : P.toRat (r + (m + 1)) (dForm P.const (Fin.append τ' (fun i => ρ (z i)))) =
      dForm cL (Fin.append (fun i => (τ i : L)) (fun i => j (z i : K))) := by
    refine (formMap_dForm _ rfl _).trans (congrArg _ (funext fun k => ?_))
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [Fin.append_left]; rfl
    · simp only [Fin.append_right]; rfl
  obtain ⟨f, hf⟩ := (P0.isFreeGen_toRat hω0).2 (dForm cK (fun i => (x i : K)))
  simp only at hf
  have hxK := isFreeGen_dForm_of_trBasis cK hx
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hf
    exact one_ne_zero (hxK.1 (a₁ := 1) (a₂ := 0) (by simp [← hf]))
  have hK : P0.formOrd (dForm cK (fun i => (x i : K))) = P0.ord f := by
    rw [← hf]; exact P0.formOrd_smul_toRat hω0 hf0
  have key := GlobalTheory.T.kaehlerWedgeForm_map_eq_smul_of_basis cK cL j (RingHom.ext fun a => by
      change j (cK a) = cL a
      have := hj ⟨cK a, hE.base.const_mem a⟩
      rw [hE.const a] at this
      exact this) (fun i => (x i : K)) (fun i => (z i : K)) bK hbK f
    (by rw [← hf, hrat0]) (fun i => (τ i : L))
  have e1 : (fun i => j (x i : K)) = fun i => (ι (x i) : L) := funext fun i => hj (x i)
  rw [e1, ← hratP] at key
  rw [key, P.formOrd_smul_toRat hF ((map_ne_zero j).2 hf0), hordK f hf0, hK]

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormValueOnTangentVectorEqZeroOfGlobalFormZeroStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) (v : epsR R ⟶ A) (f : Form (A.hom ≫ 𝟙 (Sp R))), GlobalTheory.CechDR.cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → tanVal v f = 0 := by
  first | exact @GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero | exact GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero | (intros; apply GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationTower
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem GlobalTheory.FormalAlg.alg_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), Alg f I → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ j : ∀ e, (Y e).left ⟶ W, (∀ e, IsClosedImmersion (j e)) → (∀ e, j e ≫ f = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ j (e + 1) = j e) → ∃ (T : Scheme.{0}) (i : T ⟶ W) (c : ∀ e, (Y e).left ⟶ T), IsClosedImmersion i ∧ IsProper (i ≫ f) ∧ (∀ e, c e ≫ i = j e) ∧ ∀ e, IsPullback (c e) (Y e).hom (i ≫ f) (thick R I e) := by
  intro R _ I W f hA Y β hβ hY j hj hjf hβj
  have hP := (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1
  have key : ∀ e (T : Scheme.{0}) (i : T ⟶ W), IsClosedImmersion i →
      ((∃ b : (Y e).left ⟶ T, b ≫ i = j e ∧ IsPullback b (Y e).hom (i ≫ f) (thick R I e)) ↔
        i.ker ⊔ baseIdeal f (I ^ (e + 1)) = (j e).ker) :=
    fun e T i hi => GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W T (Y e).left f i (j e) (Y e).hom hi (hj e) (hjf e)
  have hsys : IsSystem f I (fun e => (j e).ker) := by
    intro e
    exact ((key e _ (j (e + 1)) (hj (e + 1))).1 ⟨β e, hβj e, by rw [hjf (e + 1)]; exact hP e⟩).symm
  have hprop : ∀ e, IsProper ((j e).ker.subschemeι ≫ f) := by
    intro e
    have h0 : (j e).toImage ≫ ((j e).ker.subschemeι ≫ f) = (Y e).hom ≫ thick R I e := by
      rw [← hjf e, ← Category.assoc]
      exact congrArg (· ≫ f) (Scheme.Hom.toImage_imageι (j e))
    have h1 : (j e).ker.subschemeι ≫ f = inv (j e).toImage ≫ (Y e).hom ≫ thick R I e := by
      rw [← h0, IsIso.inv_hom_id_assoc]
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [h1]
    infer_instance
  obtain ⟨T, hTp, hTr⟩ := hA _ hsys hprop
  have hc : ∀ e, ∃ b : (Y e).left ⟶ T.subscheme, b ≫ T.subschemeι = j e ∧
      IsPullback b (Y e).hom (T.subschemeι ≫ f) (thick R I e) := fun e =>
    (key e _ T.subschemeι inferInstance).2 (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hTr e)
  choose c hc1 hc2 using hc
  exact ⟨T.subscheme, T.subschemeι, c, inferInstance, hTp, hc1, hc2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionFieldMapFiniteOfFiniteInjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionFieldMap_finite_of_finite_injective : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ), ρ.Finite → (fracMap ρ hρ).Finite := by
  first | exact @GlobalTheory.Mum.GenDesc.fracMap_finite | exact GlobalTheory.Mum.GenDesc.fracMap_finite | (intros; apply GlobalTheory.Mum.GenDesc.fracMap_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedAlong
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def FrameAlong {X Y : Scheme.{0}} (L : LB X) (x : Y ⟶ X) (W : Y.Opens) (τ : ∀ k, Γ(Y, W ⊓ x ⁻¹ᵁ L.U k)ˣ) : Prop :=
  ∀ (z : Y) (k k' : L.ι), z ∈ W → x z ∈ L.U k → x z ∈ L.U k' →
    gm (𝟙 Y) z (W ⊓ x ⁻¹ᵁ L.U k) (τ k) =
      gm x z (L.U k ⊓ L.U k') (L.g k k') * gm (𝟙 Y) z (W ⊓ x ⁻¹ᵁ L.U k') (τ k')

def FrameCarriedAlong {X Y : Scheme.{0}} (L : LB X) (x : Y ⟶ X) (W : Y.Opens) (τ : ∀ k, Γ(Y, W ⊓ x ⁻¹ᵁ L.U k)ˣ)
    (f : X ⟶ X) (w : LB.Iso L (L.pull f)) (h : Y ⟶ Y) : Prop :=
  ∀ (z : Y) (j k : L.ι), z ∈ W → h z ∈ W → x z ∈ L.U k → x (h z) ∈ L.U j →
    gm h z (W ⊓ x ⁻¹ᵁ L.U j) (τ j) = gw w x z j k * gm (𝟙 Y) z (W ⊓ x ⁻¹ᵁ L.U k) (τ k)

end GlobalTheory.Mum
end
end

