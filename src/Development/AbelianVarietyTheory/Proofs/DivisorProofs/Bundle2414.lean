import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2346
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsComp
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Obs.isTheta_comp : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) (E E' : Type) [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E'] (a b : B →ₐ[R] E) (θ : Ω[B₀⁄R₀] →+ E), IsTheta I p a b θ → (∀ g : E →ₐ[R] E', IsTheta I p (g.comp a) (g.comp b) ((g : E →+* E').toAddMonoidHom.comp θ)) ∧ ∀ (h : B' →ₐ[R] B) (h₀ : B₀' →ₐ[R₀] B₀), (∀ x, p (h x) = h₀ (p' x)) → IsTheta I p' (a.comp h) (b.comp h) (θ.comp (SemiHom.of_algHom h₀).m1.toAddMonoidHom) := by
  intro R R₀ _ _ I hI π hπ hk B B₀ _ _ _ _ p hs hp hker B' B₀' _ _ _ _ p' hs' hp' hker' E E' _ _ _ _ a b θ hθ
  refine ⟨fun g ↦ ⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h h₀ hh ↦ ⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩⟩
  · change g (θ (p x • w)) = g (a x) * g (θ w)
    rw [hθ.smul, map_mul]
  · change g (θ (KaehlerDifferential.D R₀ B₀ (p x))) = g (a x) - g (b x)
    rw [hθ.der, map_sub]
  · have h1 := Ideal.mem_map_of_mem (g : E →+* E') (hθ.mem w)
    rw [Ideal.map_map, g.comp_algebraMap] at h1
    simpa using h1
  · change θ ((SemiHom.of_algHom h₀).m1 (p' x • w)) = a (h x) * θ ((SemiHom.of_algHom h₀).m1 w)
    rw [SemiHom.oneFormMap_smul_semilinear]
    change θ (h₀ (p' x) • _) = _
    rw [← hh, hθ.smul]
  · change θ ((SemiHom.of_algHom h₀).m1 (KaehlerDifferential.D R₀ B₀' (p' x))) = a (h x) - b (h x)
    rw [SemiHom.m1_D]
    change θ (KaehlerDifferential.D R₀ B₀ (h₀ (p' x))) = _
    rw [← hh, hθ.der]
  · exact hθ.mem _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainSectionsQuotMaximalIdealSmoothConnected
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory

theorem abLawCst_eq_smallExtLiftCst {X : Scheme} {R : Type} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) :
    GlobalTheory.AbLaw.cst f U = GlobalTheory.SmallExtLift.cst f U := by
  ext r
  simp only [GlobalTheory.AbLaw.cst, GlobalTheory.SmallExtLift.cst, GlobalTheory.AbLaw.rs, Scheme.Hom.appLE,
    CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop]
  rfl

theorem isDomain_quot_maximalIdeal_of_smooth :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)), Smooth G.hom →
      GeometricallyConnected G.hom → ∀ (U : G.left.Opens), IsAffineOpen U → ∀ y ∈ U,
        G.hom y = closedPoint R →
          IsDomain (Γ(G.left, U) ⧸ (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U)) := by
  intro R _ _ G hsm hgc U hU y hyU hy
  haveI := hsm
  haveI := hgc
  let f : G.left ⟶ Spec (CommRingCat.of R) := G.hom
  let g : Spec (CommRingCat.of (ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (residue R))
  haveI hI : IsIntegral (pullback f g) := GlobalTheory.isIntegral_specialFibre_of_smooth f
  let q := pullback.fst f g
  have H : IsPullback q (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have hsurj : Function.Surjective (q.app U).hom :=
    GlobalTheory.SmallExtLift.app_surj (residue_surjective) H hU
  have hker : RingHom.ker (q.app U).hom = (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U) := by
    rw [abLawCst_eq_smallExtLiftCst]
    apply le_antisymm
    · intro a ha
      have := GlobalTheory.SmallExtLift.mem_of_app_eq_zero (residue_surjective) H hU a ha
      rwa [ker_residue] at this
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, GlobalTheory.SmallExtLift.app_cst H.w,
        (residue_eq_zero_iff r).2 hr, map_zero]
  have hne : Nonempty (q ⁻¹ᵁ U) := by
    have hpt : f y = g (closedPoint (ResidueField R)) := by
      rw [show f y = G.hom y from rfl, hy]
      exact (IsLocalRing.comap_closedPoint (residue R)).symm
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y _ hpt
    exact ⟨⟨z, show q z ∈ U from hz ▸ hyU⟩⟩
  haveI : IsDomain Γ(pullback f g, q ⁻¹ᵁ U) := inferInstance
  rw [← hker]
  exact (RingHom.quotientKerEquivOfSurjective hsurj).toMulEquiv.isDomain

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfGen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.PullOpen

open GlobalTheory.Cartier.DomPull

theorem isDominant_of_gen {X V : Scheme.{0}} [IsIntegral X] (φ : V ⟶ X) (v : V)
    (hv : φ v = genericPoint X) : IsDominant φ := by
  refine ⟨?_⟩
  have hd : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact (genericPoint_spec X).def
  exact hd.mono (Set.singleton_subset_iff.2 ⟨v, hv⟩)

theorem gp_apply {X : Scheme.{0}} [IsIntegral X] (q : Sp X.functionField) : gp X q = genericPoint X := by
  have h1 : gp X q ⤳ genericPoint X := by
    have : gp X q ∈ Set.range (X.fromSpecStalk (genericPoint X)) := ⟨q, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  exact (h1.antisymm (genericPoint_specializes _)).eq

theorem ffm_comp {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {V : Y.Opens} [IsIntegral V.toScheme]
    [IsDominant V.ι] {φ : V.toScheme ⟶ X} [IsDominant φ] {θ : X.functionField →+* Y.functionField}
    (h : PFF V.ι φ θ) : (GlobalTheory.functionFieldMap V.ι).comp θ = GlobalTheory.functionFieldMap φ := by
  obtain ⟨l, h₁, h₂⟩ := h
  have e1 : Spec.map (CommRingCat.ofHom (GlobalTheory.functionFieldMap V.ι)) ≫ l = genericFieldPoint V.toScheme := by
    rw [← cancel_mono V.ι, Category.assoc, h₁]
    exact GlobalTheory.specMap_functionFieldMap V.ι
  have e2 : Spec.map (CommRingCat.ofHom ((GlobalTheory.functionFieldMap V.ι).comp θ)) ≫ gp X =
      Spec.map (CommRingCat.ofHom (GlobalTheory.functionFieldMap φ)) ≫ gp X := by
    refine Eq.trans ?_ (GlobalTheory.specMap_functionFieldMap φ).symm
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    erw [← h₂]
    rw [← Category.assoc, e1]
  haveI : Mono (gp X) := inferInstanceAs (Mono (X.fromSpecStalk (genericPoint X)))
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e2))

theorem lbIso_pull : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (V : Y.Opens) (φ : V.toScheme ⟶ X)
    (θ : X.functionField →+* Y.functionField) (D : CartierDiv X) (D₁ : CartierDiv Y),
    PFF V.ι φ θ → PPull V.ι φ θ D D₁ → LBIso ((toLB D₁).pull V.ι) ((toLB D).pull φ) := by
  intro X Y _ _ V φ θ D D₁ hF hP
  obtain ⟨l, h₁, h₂⟩ := hF
  obtain ⟨q⟩ : Nonempty (Sp Y.functionField) := inferInstance
  haveI : Nonempty V := ⟨l q⟩
  haveI : IsIntegral V.toScheme := inferInstance
  haveI : IsDominant V.ι := isDominant_of_gen V.ι (l q) (by
    rw [← Scheme.Hom.comp_apply, h₁, gp_apply])
  haveI : IsDominant φ := isDominant_of_gen φ (l q) (by
    rw [← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply, gp_apply])
  have key := ffm_comp (V := V) (φ := φ) ⟨l, h₁, h₂⟩
  have hE : pullback V.ι D₁ = pullback φ D := CartierDiv.ext_of_isEqn fun v => by
    obtain ⟨g, hg⟩ := D.exists_isEqn (φ v)
    refine ⟨unitsMap φ g, ?_, isEqn_pullback φ D hg⟩
    have := isEqn_pullback V.ι D₁ (hP v g hg)
    convert this using 1
    ext
    simp only [unitsMap, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    exact (congrArg (fun f : X.functionField →+* V.toScheme.functionField => f g) key).symm
  exact (presents_pullback V.ι D₁).lbIso (hE ▸ presents_pullback φ D)

end GlobalTheory.Desc.PullOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIsPerfectOfAdditive
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerfectDual

theorem mono_of_isPerfect {S : Scheme.{0}} {A B B' : Over S} [GrpObj A] [GrpObj B] [GrpObj B']
    {P : LB (A ⊗ B).left} {P' : LB (A ⊗ B').left} (h : IsDual A B' P') (hP : IsPerfect A B P) (x : B ⟶ B')
    [IsMonHom x] (hx : LBIso P (ev P' (fst A B) (snd A B ≫ x))) : Mono x := by
  have h' : (ev P' (fst A B) (snd A B ≫ x)).IsLB := pull_isLB h.isLB _
  have hc : cls P hP.isLB = cls _ h' := (cls_eq_iff hP.isLB h').2 hx
  have key : ∀ {Y : Over S} (a : Y ⟶ A) (t : Y ⟶ B), evc hP.isLB a t = evc h.isLB a (t ≫ x) := by
    intro Y a t
    show CechPic.pull (lift a t).left (cls P hP.isLB) = _
    rw [hc, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc]
  refine ⟨fun {T} u v huv ↦ ?_⟩
  have hw : (u * v⁻¹) ≫ x = 1 := by rw [MonObj.mul_comp, GrpObj.inv_comp, huv, mul_inv_cancel]
  have t := hP.ker_right T (u * v⁻¹) ((triv_ev_iff hP.isLB _ _).2 (by
    rw [key, Category.assoc, hw, MonObj.comp_one, evc_one_right h.isLB h.zero]))
  rwa [mul_inv_eq_one] at t

theorem isIso_of_isEmpty {S : Scheme.{0}} (hS : IsEmpty S) {X Y : Over S} (f : X ⟶ Y) : IsIso f := by
  haveI : IsEmpty X.left := ⟨fun p ↦ hS.false (X.hom p)⟩
  haveI : IsEmpty Y.left := ⟨fun p ↦ hS.false (Y.hom p)⟩
  haveI : IsIso f.left := ⟨⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _⟩⟩
  haveI : IsIso ((Over.forget S).map f) := ‹IsIso f.left›
  exact isIso_of_reflects_iso f (Over.forget S)

theorem isDual_of_isPerfect_of_additive (hD : GlobalTheory.Published.DualAbelianScheme) {S : Scheme.{0}} [IsLocallyNoetherian S]
    (A B : Over S) [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {g g' : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) (hg' : SmoothOfRelativeDimension g' B.hom)
    {P : LB (A ⊗ B).left} (hP : IsPerfect A B P) (haddA : IsAdditive P) (haddB : IsAdditive (swap P)) :
    IsDual A B P := by
  obtain ⟨B', _, P', hB', hd', h1, h2⟩ := hD S A hA
  obtain ⟨A'', _, Q, hA'', hdQ, k1, k2⟩ := hD S B hB
  obtain ⟨x, hx, -⟩ := h1.univ B P hP.isLB haddA
  have hs : (swap P).IsLB := pull_isLB hP.isLB _
  obtain ⟨y, hy, -⟩ := k1.univ A (swap P) hs haddB
  have hmx : IsMonHom x := GlobalTheory.AbDual.isMonHom_of_classifying S A B B' P P' h1 h2.additive hP.isLB haddB x hx
  have hss : (swap (swap P)).IsLB := pull_isLB hs _
  have haddSS : IsAdditive (swap (swap P)) := (isAdditive_iff hss).2 fun Y a a' t ↦ by
    rw [evc_swap hs hss, evc_swap hs hss, evc_swap hs hss, evc_swap hP.isLB hs, evc_swap hP.isLB hs,
      evc_swap hP.isLB hs]
    exact (isAdditive_iff hP.isLB).1 haddA Y a a' t
  have hmy : IsMonHom y := GlobalTheory.AbDual.isMonHom_of_classifying S B A A'' (swap P) Q k1 k2.additive hs haddSS y hy
  have mx : Mono x := mono_of_isPerfect h1 hP x hx
  have my : Mono y := mono_of_isPerfect k1 hP.swap y hy
  have ix : IsIso x := by
    rcases le_or_gt g g' with hle | hlt
    · exact GlobalTheory.AbMonoIso.isIso_of_mono S B B' hB hB' g' g hg' (hd' g hg) hle x hmx mx
    · by_cases hS : Nonempty S
      · exfalso
        have iy := GlobalTheory.AbMonoIso.isIso_of_mono S A A'' hA hA'' g g' hg (hdQ g' hg') hlt.le y hmy my
        exact absurd (GlobalTheory.relDim_unique_of_iso_grp S hS A A'' y iy g g' hg (hdQ g' hg')) hlt.ne'
      · exact isIso_of_isEmpty (not_nonempty_iff.1 hS) x
  exact GlobalTheory.AbDual.transport S A B B' P P' h1 hP.isLB x ix hmx hx

theorem isDual_of_isPerfect (hD : GlobalTheory.Published.DualAbelianScheme) {S : Scheme.{0}} [IsLocallyNoetherian S]
    (A B : Over S) [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {g g' : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) (hg' : SmoothOfRelativeDimension g' B.hom)
    {P : LB (A ⊗ B).left} (hP : IsPerfect A B P) : IsDual A B P :=
  isDual_of_isPerfect_of_additive hD A B hA hB hg hg' hP
    (CubeNoeth.isAdditive_of_triv_axes hA hB hP.isLB hP.zero_left hP.zero_right)
    (CubeNoeth.isAdditive_swap_of_triv_axes hA hB hP.isLB hP.zero_left hP.zero_right)

end GlobalTheory.PerfectDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackTangentCombination
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel

theorem eq_one_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'}
    (z : Over.mk (T.hom ≫ f) ⟶ G) (hz : z.left = (1 : T ⟶ G').left ≫ φ) : z = 1 := by
  have e := h.2 T 1 1 z z hz hz
  rw [_root_.mul_one, ← hz] at e
  exact _root_.mul_eq_left.1 (Over.OverMorphism.ext e)

theorem lieTie_lieComb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (S0 : Scheme.{0})
    (t : SAB H S0) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (x0 : Sp ℂ_[p] ⟶ S0)
    (ψ' : P.A.A.left ⟶ t.G.left), IsGrpPullback P.A.A t.G x0 ψ' →
    ∀ (m : ℕ) (xs : Fin m → LieG P.Gt) (us : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → 𝓞_ℂ_[p])
      (u : Sp (DualNumber ℂ_[p]) ⟶ t.G.left), (∀ i, LieTie P ψ' (xs i) (us i)) →
      IsCombAtG t x0 us (fun i => algebraMap 𝓞_ℂ_[p] ℂ_[p] (a i)) u → LieTie P ψ' (lieComb P.Gt a xs) u := by
  intro E _ _ _ H S0 t p _ _ P x0 ψ' hψ m
  induction m with
  | zero =>
    intro xs us a u _ hc
    obtain ⟨w, -, hw⟩ := hc
    rw [List.ofFn_zero, List.prod_nil] at hw
    subst hw
    refine ⟨lieZero P.G, 1, Corr.one, ?_, ?_⟩
    · have e := eq_one_of_isGrpPullback hψ (pushPt hψ.1.w (1 : specO ℂ_[p] (DualNumber ℂ_[p]) ⟶ P.A.A)) rfl
      exact congrArg (fun z => z.left) e
    · let d : Over.mk ((specO ℂ_[p] (DualNumber ℂ_[p])).hom ≫ spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ⟶
          specO 𝓞_ℂ_[p] (DualNumber 𝓞_ℂ_[p]) :=
        Over.homMk (spMap (dualMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]))) (by
          refine (spMap_spMap _ _).trans (Eq.trans (congrArg _ ?_) (spMap_spMap _ _).symm)
          ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
      have e2 := eq_one_of_isGrpPullback P.gen_pull
        (pushPt P.gen_pull.1.w (1 : specO ℂ_[p] (DualNumber ℂ_[p]) ⟶ P.A.A)) rfl
      have e3 : d ≫ (1 : specO 𝓞_ℂ_[p] (DualNumber 𝓞_ℂ_[p]) ⟶ P.G) =
          pushPt P.gen_pull.1.w (1 : specO ℂ_[p] (DualNumber ℂ_[p]) ⟶ P.A.A) := by
        rw [e2, MonObj.comp_one]
      exact (congrArg (fun z => z.left) e3).symm
  | succ m ih =>
    intro xs us a u hx hc
    obtain ⟨w, hw1, hw2⟩ := hc
    rw [List.ofFn_succ, List.prod_cons] at hw2
    subst hw2
    rw [lieComb_succ]
    have h0 : LieTie P ψ' (AvDefs.lieScale P.Gt (a 0) (xs 0)) (w 0).left := by
      rw [hw1 0]; exact (hx 0).scale (a 0)
    have ht := ih (Fin.tail xs) (Fin.tail us) (Fin.tail a) _ (fun i => hx i.succ)
      ⟨fun i => w i.succ, fun i => hw1 i.succ, rfl⟩
    exact TieIndep.lieTie_add hψ h0 ht

end GlobalTheory.FlatModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHorizontalLieDeterminantSectionOfConj
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm
open GlobalTheory.ArchMetricCompare GlobalTheory.ConjUnif GlobalTheory.ConjTransport GlobalTheory.DetLine

namespace GlobalTheory.ConjFlat

theorem isTangent_of_fibre {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {A : Over (Sp ℂ)} [GrpObj A]
    {ψ : A.left ⟶ G.left} (h : IsGrpPullback A G y ψ) {t : epsR ℂ ⟶ A}
    (ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t.left ≫ ψ = (1 : Over.mk y ⟶ G).left) : IsTangent t := by
  refine h.1.hom_ext ?_ ?_
  · refine ((Category.assoc _ _ _).trans ht).trans ?_
    refine Eq.trans ?_ (PolBaseChange.eSec_comm h).symm
    rw [Hom.one_def]
    simp [eSec]
  · have z := congrArg (· ≫ A.hom) (isTangent_zero A)
    rw [← z, Category.assoc, Category.assoc, Over.w, Over.w]

theorem isVecs_conj {S : Scheme.{0}} {G : Over S} [GrpObj G] {y y₁ : Sp ℂ ⟶ S} {A A₁ : Over (Sp ℂ)} [GrpObj A]
    [GrpObj A₁] {L : LB A.left} {L₁ : LB A₁.left} {ψ : A.left ⟶ G.left} (h : IsGrpPullback A G y ψ)
    {ρ : A₁.left ⟶ A.left} (hρ : IsGrpPullback A₁ A cj ρ) {ψ₁ : A₁.left ⟶ G.left} (hψ : ψ₁ = ρ ≫ ψ) {g n : ℕ}
    {u : HolUnif A L g} {u₁ : HolUnif A₁ L₁ g} (hx : ∀ z, u₁.ex z = cjPt hρ (u.ex (star z)))
    {v : Fin n → (epsAt y ⟶ G)} {v₁ : Fin n → (epsAt y₁ ⟶ G)}
    (hv : ∀ i, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (v i).left = (1 : Over.mk y ⟶ G).left)
    (h₁ : ∀ i, (v₁ i).left = spMap (Chart.dualMapR (starRingEnd ℂ)) ≫ (v i).left) {V : Fin n → Fin g → ℂ}
    (hV : IsVecs u ψ v V) : IsVecs u₁ ψ₁ v₁ fun i => star (V i) := by
  intro i
  obtain ⟨t, ht, hd⟩ := hV i
  have tg : IsTangent t := isTangent_of_fibre h (by rw [ht]; exact hv i)
  have w : (spMap (Chart.dualMapR (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left)) ≫ A.hom =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ cj := by
    rw [Category.assoc, show (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ A.hom =
      spMap (algebraMap ℂ (DualNumber ℂ)) from Over.w t, ← DetExtendZero.spMap_comp, ← DetExtendZero.spMap_comp]
    refine congrArg spMap (RingHom.ext fun a => ?_)
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let t₁ : epsR ℂ ⟶ A₁ := Over.homMk (hρ.1.lift _ _ w) (hρ.1.lift_snd _ _ _)
  have e : t₁.left ≫ ρ = spMap (Chart.dualMapR (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) :=
    hρ.1.lift_fst _ _ _
  refine ⟨t₁, ?_, ?_⟩
  · rw [hψ, ← Category.assoc, e, h₁, ← ht]
    exact Category.assoc _ _ _
  · have := cj_isDiff hρ (pullId u) tg e hd
    intro U hU f
    simp only [hx]
    exact this U hU f

theorem herm_conj {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    herm (Hm.map star) (star z) (star w) = star (herm Hm z w) := by
  rw [herm, herm, ← star_form, star_star, star_star]

theorem isWedgeCoord_conj {g p q : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {V : Fin p → Fin g → ℂ} {W : Fin q → Fin g → ℂ}
    {x : Fin q ⊕ Fin p → Fin g → ℂ} {Δ : ℂ} (h : IsWedgeCoord Hm V W x Δ) :
    IsWedgeCoord (Hm.map star) (fun i => star (V i)) (fun j => star (W j)) (fun k => star (x k)) (star Δ) := by
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨fun k i => star (a k i), fun k i => ?_, ?_⟩
  · have e : star (x k) - ∑ m, star (a k m) • star (V m) = star (x k - ∑ m, a k m • V m) := by
      simp [star_sum]
    rw [e, herm_conj, ha, star_zero]
  · refine ((starRingEnd ℂ).map_det _).trans (congrArg Matrix.det ?_)
    ext k (j | i)
    · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Sum.elim_inl, herm_conj]
      simp
    · simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem isTransport_to_conj {B : Type} [CommRing B] {b : Base l B} {s s₁ s' s₁' : Sp ℂ ⟶ Sp B} {o : Obj D l b s}
    {o₁ : Obj D l b s₁} {o' : Obj D l b s'} {o₁' : Obj D l b s₁'}
    (m : ObjMap o₁ o cj) (m' : ObjMap o₁' o' cj) {g g' : ℕ}
    {u : HolUnif o.t.G o.t.PP.L g} {u' : HolUnif o'.t.G o'.t.PP.L g'}
    {u₁ : HolUnif o₁.t.G o₁.t.PP.L g} {u₁' : HolUnif o₁'.t.G o₁'.t.PP.L g'}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ}
    (hΛ : ∀ z, z ∈ u₁.Λ ↔ star z ∈ u.Λ) (hx : ∀ z, u₁.ex z = cjPt m.cart (u.ex (star z)))
    (hΛ' : ∀ z, z ∈ u₁'.Λ ↔ star z ∈ u'.Λ) (hx' : ∀ z, u₁'.ex z = cjPt m'.cart (u'.ex (star z)))
    {φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ)} (h : IsTransport o o' u u' Hm Hm' φ) :
    IsTransport o₁ o₁' u₁ u₁' (Hm.map star) (Hm'.map star) ((conjEquiv g).trans (φ.trans (conjEquiv g'))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : ∀ z, ((conjEquiv g).trans (φ.trans (conjEquiv g'))) z = star (φ (star z)) := fun _ => rfl
  refine ⟨fun z => ?_, fun a z w hw => ?_, fun z w => ?_, fun a z hz => ?_, fun a z hz => ?_⟩
  · rw [e, hΛ', star_star, h1, hΛ]
  · rw [hx, hx, ← cjPt_act] at hw
    rw [e, e, hx', hx', star_star, star_star, ← cjPt_act, h2 a _ _ (cjPt_injective m.cart hw)]
  · rw [e, e, herm_map_star, herm_map_star, star_star, star_star, h3]
  · rw [hx, ← cjPt_eta m] at hz
    rw [e, hx', star_star, h4 a _ (cjPt_injective m.cart hz), cjPt_eta]
  · rw [hx, ← cjPt_etaA m] at hz
    rw [e, hx', star_star, h5 a _ (cjPt_injective m.cart hz), cjPt_etaA]

theorem exists_conj_fibre (Xo : Moduli D l) (c : Coeff l) (y : Sp ℂ ⟶ Xo.XF c)
    (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (n : ObjMap o Xo.univ (y ≫ toX Xo c)) :
    ∃ (o₁ : Obj D l (baseKA l) ((cj ≫ y) ≫ toX Xo c ≫ Xo.s)) (m : ObjMap o₁ o cj)
      (k : ObjMap o₁ Xo.univ ((cj ≫ y) ≫ toX Xo c)), k.toSABMap.φ = m.toSABMap.φ ≫ n.toSABMap.φ := by
  obtain ⟨o₁, ⟨m⟩, -⟩ := exists_conj_obj Xo c y o n
  refine ⟨o₁, m, ?_⟩
  have a : ∀ f : Sp ℂ ⟶ Xo.X, f = cj ≫ y ≫ toX Xo c →
      ∃ k : ObjMap o₁ Xo.univ f, k.toSABMap.φ = m.toSABMap.φ ≫ n.toSABMap.φ := by
    rintro _ rfl
    exact ObjComp.objMap_comp n m
  exact a _ (Category.assoc _ _ _)

end GlobalTheory.ConjFlat

namespace GlobalTheory

open ConjFlat

theorem isFlatAt_of_conj (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c)
    (e : c.F →+* ℂ) (hσ : SecU Xo c U τ σ) (h : IsFlatAt Xo c U τ σ ((starRingEnd ℂ).comp e)) :
    IsFlatAt Xo c U τ σ e := by
  intro y y' v w v' w' hf hf' o o' n n' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' hA hA' hφ hV hW hV' hW' hΔ hΔ'
  obtain ⟨o₁, m, k, hk⟩ := exists_conj_fibre Xo c y o n
  obtain ⟨o₁', m', k', hk'⟩ := exists_conj_fibre Xo c y' o' n'
  obtain ⟨u₁, κ₁, hA₁, hΛ, hx⟩ := exists_unif m u hA
  obtain ⟨u₁', κ₁', hA₁', hΛ', hx'⟩ := exists_unif m' u' hA'
  obtain ⟨v₁, w₁, hf₁, a, b⟩ := exists_pull (starRingEnd ℂ) hf (x' := cj ≫ y) rfl
  obtain ⟨v₁', w₁', hf₁', a', b'⟩ := exists_pull (starRingEnd ℂ) hf' (x' := cj ≫ y') rfl
  have i1 : ∀ z : ℂ, Chart.dualMapR (starRingEnd ℂ) (algebraMap ℂ _ z) = algebraMap ℂ _ (starRingEnd ℂ z) :=
    fun z => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have i2 : Chart.dualMapR (starRingEnd ℂ) DualNumber.eps = DualNumber.eps := by ext <;> simp [Chart.dualMapR]
  have s := hσ.1 ℂ ℂ _ _ _ _ _ _ v w v₁ w₁ i1 i2 hf hf₁ rfl a b
  have s' := hσ.1 ℂ ℂ _ _ _ _ _ _ v' w' v₁' w₁' i1 i2 hf' hf₁' rfl a' b'
  have q := h (cj ≫ y) (cj ≫ y') v₁ w₁ v₁' w₁' hf₁ hf₁' o₁ o₁' k k' g g' u₁ u₁' _ _ κ₁ κ₁' _ _ _ _ _
    (fun i => star (x i)) (star Δ) (star Δ') hA₁ hA₁' (isTransport_to_conj m m' hΛ hx hΛ' hx' hφ)
    (isVecs_conj n.cart m.cart hk hx (fun i => (hf.2.2.1.1 i).1) a hV)
    (isVecs_conj n.cart m.cart hk hx (fun i => (hf.2.2.2.1 i).1) b hW)
    (isVecs_conj n'.cart m'.cart hk' hx' (fun i => (hf'.2.2.1.1 i).1) a' hV')
    (isVecs_conj n'.cart m'.cart hk' hx' (fun i => (hf'.2.2.2.1 i).1) b' hW')
    (isWedgeCoord_conj hΔ) (by
      have := isWedgeCoord_conj hΔ'
      simpa only [LinearEquiv.trans_apply, conjEquiv_apply, star_star] using this)
  rw [s, s'] at q
  refine (starRingEnd ℂ).injective ?_
  rw [map_mul, map_mul]
  exact q

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfPullbackSurjectiveProjectiveStatement
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
theorem _root_.GlobalTheory.T.isNefLineBundle_of_pullback_surjective_projective : ∀ (F : Type) [Field F] [NumberField F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) (p : Y ⟶ Sp F) (L : LB X) (hL : L.IsLB) (L' : LB Y) (hL' : L'.IsLB), π ≫ sX = p → IsProjOver sX → IsProjOver p → Surjective π → CechPic.pull π (cls L hL) = cls L' hL' → (letI := algebraΓOfHom p; IsNef F L') → (letI := algebraΓOfHom sX; IsNef F L) := by
  first | exact @GlobalTheory.NefDescent.isNef_of_pull | exact GlobalTheory.NefDescent.isNef_of_pull | (intros; apply GlobalTheory.NefDescent.isNef_of_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoLiftSmallArtinExtensionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenImmersion_of_mono_lift_smallArtinExtensions : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [Mono f], (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → IsOpenImmersion f := by
  first | exact @GlobalTheory.ArtinOpen.isOpenImmersion_of_lift | exact GlobalTheory.ArtinOpen.isOpenImmersion_of_lift | (intros; apply GlobalTheory.ArtinOpen.isOpenImmersion_of_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionWhiskerLeftRangePreimageSndStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd : ∀ {S : Scheme.{0}} (A : Over S) {B' B : Over S} (j : B' ⟶ B) [IsOpenImmersion j.left], IsOpenImmersion (A ◁ j).left ∧ Set.range (A ◁ j).left = (snd A B).left ⁻¹' Set.range j.left := by
  first | exact @GlobalTheory.DualCon.isOpenImmersion_whiskerLeft_left_and_range | exact GlobalTheory.DualCon.isOpenImmersion_whiskerLeft_left_and_range | (intros; apply GlobalTheory.DualCon.isOpenImmersion_whiskerLeft_left_and_range <;> assumption)
end

