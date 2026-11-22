import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0057

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedHomWithFixedPullbackScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomFixUnr

theorem base_eq {X Y Z Y' Z' : Scheme.{0}} (b : Y ⟶ X) (c : Z ⟶ Y) (b' : Y' ⟶ X) (c' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (e : c' ≫ b' = h ≫ c ≫ b) (y : Z') : b' (c' y) = b (c (h y)) := by
  have := congrArg (fun k => k.base y) e
  simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] using this

def chartPullPullPull {X Y Z Y' Z' : Scheme.{0}} (M : LB X) (b : Y ⟶ X) (c : Z ⟶ Y) (b' : Y' ⟶ X) (c' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (e : c' ≫ b' = h ≫ c ≫ b) : ChartPull ((M.pull b').pull c') ((M.pull b).pull c) h where
  idx J := J
  le J y hy := by
    have h1 := mem_pull.1 (mem_pull.1 hy)
    show h y ∈ ((M.pull b).pull c).U J
    refine mem_pull.2 (mem_pull.2 ?_)
    rw [← base_eq b c b' c' h e y]; exact h1
  g y J J' hj hj' := by
    have hj2 : (𝟙 Z' ≫ c') y ∈ (M.pull b').U (J PUnit.unit) := mem_pull.1 hj
    have hj2' : (𝟙 Z' ≫ c') y ∈ (M.pull b').U (J' PUnit.unit) := mem_pull.1 hj'
    have hk : ∀ K : PUnit → PUnit → M.ι, y ∈ ((M.pull b').pull c').U K → h y ∈ ((M.pull b).pull c).U K := fun K hK =>
      mem_pull.2 (mem_pull.2 (by rw [← base_eq b c b' c' h e y]; exact mem_pull.1 (mem_pull.1 hK)))
    have hk2 : (h ≫ c) y ∈ (M.pull b).U (J PUnit.unit) := by
      have := mem_pull.1 (hk J hj); simpa using this
    have hk2' : (h ≫ c) y ∈ (M.pull b).U (J' PUnit.unit) := by
      have := mem_pull.1 (hk J' hj'); simpa using this
    rw [gm_pull_g (M.pull b') c' (𝟙 Z') y J J' hj hj', gm_pull_g M b' (𝟙 Z' ≫ c') y _ _ hj2 hj2',
      gm_pull_g (M.pull b) c h y J J' (hk J hj) (hk J' hj'), gm_pull_g M b (h ≫ c) y _ _ hk2 hk2']
    have e' : (𝟙 Z' ≫ c') ≫ b' = (h ≫ c) ≫ b := by rw [Category.id_comp, e, Category.assoc]
    rw [e']

theorem lbIso_pull_square {XA XB YA YB ZA ZB : Scheme.{0}} (L : LB XA) (M : LB XB) (φA : YA ⟶ XA) (φB : YB ⟶ XB)
    (Φ : YA ⟶ YB) (ψA : ZA ⟶ XA) (ψB : ZB ⟶ XB) (v : ZA ⟶ ZB) (χA : ZA ⟶ YA) (χB : ZB ⟶ YB)
    (hA : χA ≫ φA = ψA) (hB : χB ≫ φB = ψB) (hv : v ≫ χB = χA ≫ Φ)
    (H : LBIso (L.pull φA) ((M.pull φB).pull Φ)) : LBIso (L.pull ψA) ((M.pull ψB).pull v) :=
  LBIso.chartPull (chartPullSame L (fun _ => ψA) (fun _ => φA) (fun _ => 1) χA fun _ => hA.symm)
    (chartPullPullPull M φB Φ ψB v χA (by rw [← hB, ← Category.assoc, hv, Category.assoc])) H

end GlobalTheory.EndLoc.HomFixUnr

namespace GlobalTheory.EndLoc

open GlobalTheory.EndLoc.HomFixUnr in

theorem formallyUnramified_homFixRep : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B]
    [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (R : HomFixRep A B L M), IsAbelianScheme A → IsAbelianScheme B →
    FormallyUnramified R.π := by
  intro S A B _ _ _ _ L M Rp hA _
  refine FormallyUnramified.of_hom_ext _ fun R R₀ q hq hsq g₁ g₂ hi hg ↦ ?_
  let f : Spec R ⟶ S := g₁ ≫ Rp.π
  let AT : Over (Spec R) := (Over.pullback f).obj A
  let BT : Over (Spec R) := (Over.pullback f).obj B
  let ψA : AT.left ⟶ A.left := pullback.fst A.hom f
  let ψB : BT.left ⟶ B.left := pullback.fst B.hom f
  have hAT : IsGrpPullback AT A f ψA := isGrpPullback_pullback A f
  have hBT : IsGrpPullback BT B f ψB := isGrpPullback_pullback B f
  have hAbT : IsAbelianScheme AT := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have tr : ∀ (g : Spec R ⟶ Rp.H), g ≫ Rp.π = f → ∀ (G : Over S) [GrpObj G] (GH : Over Rp.H) [GrpObj GH]
      (φ : GH.left ⟶ G.left), IsGrpPullback GH G Rp.π φ →
      ∃ e : (Over.pullback f).obj G ≅ (Over.pullback g).obj GH, IsMonHom e.hom ∧
        IsGrpPullback ((Over.pullback f).obj G) GH g (e.hom.left ≫ pullback.fst GH.hom g) ∧
        (e.hom.left ≫ pullback.fst GH.hom g) ≫ φ = pullback.fst G.hom f := by
    intro g hgf G _ GH _ φ hG
    have h' : IsGrpPullback ((Over.pullback g).obj GH) G f (pullback.fst GH.hom g ≫ φ) :=
      ((isGrpPullback_pullback GH g).comp hG).congr hgf rfl
    obtain ⟨e, he, heφ⟩ := grpPullback_iso (isGrpPullback_pullback G f) h'
    haveI := he
    exact ⟨e, he, ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback GH g)).congr (Category.id_comp _) rfl,
      by rw [Category.assoc, heφ]⟩
  have build : ∀ g : Spec R ⟶ Rp.H, g ≫ Rp.π = f → ∃ (v : AT ⟶ BT) (χA : AT.left ⟶ Rp.AH.left)
      (χB : BT.left ⟶ Rp.BH.left), IsMonHom v ∧ IsGrpPullback AT Rp.AH g χA ∧ IsGrpPullback BT Rp.BH g χB ∧
        χA ≫ Rp.φA = ψA ∧ χB ≫ Rp.φB = ψB ∧ v.left ≫ χB = χA ≫ Rp.Φ.left := by
    intro g hgf
    obtain ⟨eA, heA, hpA, hφA⟩ := tr g hgf A Rp.AH Rp.φA Rp.pbA
    obtain ⟨eB, heB, hpB, hφB⟩ := tr g hgf B Rp.BH Rp.φB Rp.pbB
    haveI := heA
    haveI := heB
    haveI := Rp.hom
    have hie : eB.inv.left ≫ eB.hom.left = 𝟙 _ := by rw [← Over.comp_left, eB.inv_hom_id, Over.id_left]
    refine ⟨eA.hom ≫ (Over.pullback g).map Rp.Φ ≫ eB.inv, _, _, inferInstance, hpA, hpB, hφA, hφB, ?_⟩
    have hm : ((Over.pullback g).map Rp.Φ).left ≫ pullback.fst Rp.BH.hom g =
        pullback.fst Rp.AH.hom g ≫ Rp.Φ.left := pullback.lift_fst _ _ _
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% hie, hm]
  obtain ⟨v₁, χA₁, χB₁, hv₁, hpA₁, hpB₁, hχA₁, hχB₁, hχ₁⟩ := build g₁ rfl
  obtain ⟨v₂, χA₂, χB₂, hv₂, hpA₂, hpB₂, hχA₂, hχB₂, hχ₂⟩ := build g₂ hg.symm
  let I : Ideal R := RingHom.ker q.hom
  have hI : IsNilpotent I := ⟨2, hsq⟩
  let j : Sp (R ⧸ I) ⟶ Sp R := spMap (Ideal.Quotient.mk I)
  have hj : j ≫ g₁ = j ≫ g₂ := by
    let ε : (R ⧸ I) ≃+* R₀ := RingHom.quotientKerEquivOfSurjective hq
    have hε : Spec.map q = Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ j := by
      rw [← Spec.map_comp]
      congr 1
    haveI : IsIso (CommRingCat.ofHom ε.toRingHom) := ε.toCommRingCatIso.isIso_hom
    rw [hε, Category.assoc, Category.assoc] at hi
    exact (cancel_epi _).1 hi
  have hχA : pullback.fst AT.hom j ≫ χA₁ = pullback.fst AT.hom j ≫ χA₂ := by
    apply Rp.pbA.1.hom_ext
    · rw [Category.assoc, Category.assoc, hχA₁, hχA₂]
    · rw [Category.assoc, Category.assoc, hpA₁.1.w, hpA₂.1.w, pullback.condition_assoc, pullback.condition_assoc, hj]
  have hv : v₁ = v₂ := by
    refine GlobalTheory.NilRigidity.eq_of_pullback_quotient_eq I hI AT BT hAbT v₁ v₂ ?_
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [show ((Over.pullback j).map v₁).left ≫ pullback.fst BT.hom j =
          pullback.fst AT.hom j ≫ v₁.left from pullback.lift_fst _ _ _,
        show ((Over.pullback j).map v₂).left ≫ pullback.fst BT.hom j =
          pullback.fst AT.hom j ≫ v₂.left from pullback.lift_fst _ _ _]
      apply hBT.1.hom_ext
      · calc (pullback.fst AT.hom j ≫ v₁.left) ≫ ψB
            = pullback.fst AT.hom j ≫ v₁.left ≫ χB₁ ≫ Rp.φB := by rw [hχB₁, Category.assoc]
          _ = pullback.fst AT.hom j ≫ χA₁ ≫ Rp.Φ.left ≫ Rp.φB := by rw [reassoc_of% hχ₁]
          _ = pullback.fst AT.hom j ≫ χA₂ ≫ Rp.Φ.left ≫ Rp.φB := by rw [reassoc_of% hχA]
          _ = pullback.fst AT.hom j ≫ v₂.left ≫ χB₂ ≫ Rp.φB := by rw [reassoc_of% hχ₂]
          _ = (pullback.fst AT.hom j ≫ v₂.left) ≫ ψB := by rw [hχB₂, Category.assoc]
      · rw [Category.assoc, Category.assoc, Over.w v₁, Over.w v₂]
    · rw [show ((Over.pullback j).map v₁).left ≫ pullback.snd BT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _,
        show ((Over.pullback j).map v₂).left ≫ pullback.snd BT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _]
  have hL : LBIso (L.pull ψA) ((M.pull ψB).pull v₁.left) :=
    lbIso_pull_square L M Rp.φA Rp.φB Rp.Φ.left ψA ψB v₁.left χA₁ χB₁ hχA₁ hχB₁ hχ₁ Rp.iso
  obtain ⟨g, -, hg'⟩ := Rp.rep (Spec R) f AT BT ψA ψB v₁ hAT hBT hv₁ hL
  have e1 := hg' g₁ ⟨rfl, χA₁, χB₁, hpA₁, hpB₁, hχA₁, hχB₁, hχ₁⟩
  have e2 := hg' g₂ ⟨hg.symm, χA₂, χB₂, hpA₂, hpB₂, hχA₂, hχB₂, by rw [hv]; exact hχ₂⟩
  rw [e1, e2]

end GlobalTheory.EndLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingAwayEtaleDedekindArtinianReduced
section
namespace GlobalTheory

theorem mem_minimalPrimes_of_disjoint_nonZeroDivisors {R : Type} [CommRing R] [IsReduced R]
    [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] (hp : Disjoint (p : Set R) (nonZeroDivisors R)) :
    p ∈ minimalPrimes R := by
  classical
  have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  have hsub : (p : Set R) ⊆ ⋃ q ∈ hfin.toFinset, (q : Set R) := by
    intro x hx
    have hx' : x ∉ nonZeroDivisors R := Set.disjoint_left.mp hp hx
    rw [mem_nonZeroDivisors_iff_right] at hx'
    push_neg at hx'
    obtain ⟨y, hxy, hy⟩ := hx'
    have hrad : (⊥ : Ideal R).radical = ⊥ := by
      exact nilradical_eq_zero R
    have : x ∈ ⋃ q ∈ (⊥ : Ideal R).minimalPrimes, (q : Set R) := by
      rw [Ideal.iUnion_minimalPrimes]
      refine ⟨y, ?_, ?_⟩
      · rw [hrad]; simpa using hy
      · rw [hrad]; simpa [mul_comm] using hxy
    simpa [Set.Finite.mem_toFinset] using this
  have hprime : ∀ q ∈ hfin.toFinset, q.IsPrime := fun q hq =>
    ((Set.Finite.mem_toFinset hfin).1 hq).isPrime
  obtain ⟨q, hq, hpq⟩ := (Ideal.subset_union_prime (⊥ : Ideal R) ⊥ fun q hq _ _ => hprime q hq).1 hsub
  have hqm : q ∈ minimalPrimes R := (Set.Finite.mem_toFinset hfin).1 hq
  have : q ≤ p := hqm.2 ⟨inferInstance, bot_le⟩ hpq
  exact (le_antisymm hpq this) ▸ hqm

theorem total_fractions_isArtinian_isReduced (R : Type) [CommRing R] [IsReduced R]
    [IsNoetherianRing R] : IsArtinianRing (FractionRing R) ∧ IsReduced (FractionRing R) := by
  have hN : IsNoetherianRing (FractionRing R) :=
    IsLocalization.isNoetherianRing (nonZeroDivisors R) _ inferInstance
  have hRed : IsReduced (FractionRing R) := inferInstance
  refine ⟨?_, hRed⟩
  rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  refine ⟨hN, Ring.krullDimLE_zero_iff.mpr fun P hP => ?_⟩
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
  have key : ∀ (Q : Ideal (FractionRing R)), Q.IsPrime →
      Q.comap (algebraMap R (FractionRing R)) ∈ minimalPrimes R := by
    intro Q hQ
    have h := (IsLocalization.isPrime_iff_isPrime_disjoint (nonZeroDivisors R) (FractionRing R) Q).1 hQ
    haveI := h.1
    exact mem_minimalPrimes_of_disjoint_nonZeroDivisors _ h.2.symm
  have h1 := key P hP
  have h2 := key M hM.isPrime
  have hle : M.comap (algebraMap R (FractionRing R)) ≤ P.comap (algebraMap R (FractionRing R)) :=
    h2.2 ⟨h1.1.1, bot_le⟩ (Ideal.comap_mono hPM)
  have : P = M := by
    rw [← IsLocalization.map_comap (nonZeroDivisors R) (FractionRing R) P,
      ← IsLocalization.map_comap (nonZeroDivisors R) (FractionRing R) M]
    exact congrArg _ (le_antisymm (Ideal.comap_mono hPM) hle)
  exact this ▸ hM

theorem fractionRing_away_etale_isArtinian_isReduced : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsArtinianRing (FractionRing (Localization.Away (algebraMap B A' f))) ∧ IsReduced (FractionRing (Localization.Away (algebraMap B A' f))) := by
  intro B _ _ f A' _ _ _
  have : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing B A'
  have : IsReduced A' := GlobalTheory.isReduced_algebra_of_smooth_of_isNoetherianRing B A'
  have : IsNoetherianRing (Localization.Away (algebraMap B A' f)) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (algebraMap B A' f)) _ inferInstance
  have : IsReduced (Localization.Away (algebraMap B A' f)) := inferInstance
  exact total_fractions_isArtinian_isReduced _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianS
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

open Opposite TopologicalSpace

theorem uConst_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → UConst A.hom := by
  intro R _ A _ hA R' _ _ X' s' φ hpb
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hsm : Smooth s' := MorphismProperty.of_isPullback hpb ‹_›
  have hpr : IsProper s' := MorphismProperty.of_isPullback hpb ‹_›
  have hgc : GeometricallyConnected s' := MorphismProperty.of_isPullback hpb ‹_›
  haveI : GeometricallyIntegral s' :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected X' _ s' hsm hgc
  have hiso : IsIso s'.appTop := GlobalTheory.GlobalFunctions.isIso_app GlobalTheory.FlatFibreInjective.injective_baseChange
    GlobalTheory.exists_noetherian_model_of_smooth s' ⊤
  have hbij := ConcreteCategory.bijective_of_isIso s'.appTop
  intro g hg
  have hc : ∀ (U V : X'.affineOpens) (h : V.1 ≤ U.1),
      X'.presheaf.map (homOfLE h).op (g (op U)) = g (op V) := by
    intro U V h
    have e := congrFun (congrFun (congrFun hg (op U)) (op V)) (homOfLE h).op
    exact (sub_eq_zero.1 e).symm
  obtain ⟨t, ht, htu⟩ := X'.sheaf.existsUnique_gluing' (fun U : X'.affineOpens ↦ U.1) ⊤
    (fun _ ↦ homOfLE le_top) (iSup_affineOpens_eq_top X').ge (fun U ↦ g (op U)) (by
      intro U V
      refine X'.sheaf.eq_of_locally_eq' (fun W : {W : X'.affineOpens // W.1 ≤ U.1 ⊓ V.1} ↦ W.1.1)
        (U.1 ⊓ V.1) (fun W ↦ homOfLE W.2) ?_ _ _ fun W ↦ ?_
      · intro x hx
        obtain ⟨W, hW, hxW, hWUV⟩ := Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens hx
        exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWUV⟩, hxW⟩
      · dsimp only
        have e : ∀ {a b c : Opens X'} (f : b ⟶ a) (f' : c ⟶ b) (x : Γ(X', a)),
            X'.presheaf.map f'.op (X'.presheaf.map f.op x) = X'.presheaf.map (f' ≫ f).op x := by
          intros; simp
        refine (e _ _ _).trans ((hc U W.1 (W.2.trans inf_le_left)).trans
          ((hc V W.1 (W.2.trans inf_le_right)).symm.trans (e _ _ _).symm)))

  have hres : ∀ (r : R') (U : X'.affineOpens),
      X'.presheaf.map (homOfLE le_top).op (s'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv r)) =
        algebraMap R' (Sec s' U.1) r := by
    intro r U
    rfl
  have hres' : ∀ (x : Γ(Sp R', ⊤)) (U : X'.affineOpens),
      X'.presheaf.map (homOfLE le_top).op (s'.appTop x) =
        algebraMap R' (Sec s' U.1) ((Scheme.ΓSpecIso (CommRingCat.of R')).hom x) := by
    intro x U
    have := hres ((Scheme.ΓSpecIso (CommRingCat.of R')).hom x) U
    rw [Iso.hom_inv_id_apply] at this
    exact this
  obtain ⟨r₀, hr₀⟩ := hbij.2 t
  subst hr₀
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R')).hom r₀, ?_, ?_⟩
  · intro U
    exact (ht U.unop).symm.trans (hres' r₀ U.unop)
  · intro r hr
    have h1 : s'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv r) = s'.appTop r₀ := by
      apply htu
      intro U
      exact (hres r U).trans (hr (op U)).symm
    have h2 := hbij.1 h1
    rw [← h2, Iso.inv_hom_id_apply]

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalTwoFormEqSumWedgeGlobalOneForms
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.TwoFormSum

section Alg

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

def coordPair (f g : Module.Dual B Ω[B⁄R]) : Module.Dual B (Om R B 2) :=
  exteriorPower.pairingDual B Ω[B⁄R] 2 (exteriorPower.ιMulti B 2 ![f, g])

theorem coordPair_wedge (f g : Module.Dual B Ω[B⁄R]) (a b : Ω[B⁄R]) :
    coordPair f g (wedge R B a b) = f a * g b - g a * f b := by
  rw [wedge_eq_ιMulti, coordPair, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]
  simp

theorem ιMulti_two (v : Fin 2 → Ω[B⁄R]) : exteriorPower.ιMulti B 2 v = wedge R B (v 0) (v 1) := by
  rw [wedge_eq_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem sum_sum_eq_lt {M : Type} [AddCommGroup M] {n : ℕ} (g : Fin n → Fin n → M) (hg : ∀ i, g i i = 0) :
    ∑ i, ∑ j, g i j = ∑ i, ∑ j, (if i < j then g i j + g j i else 0) := by
  calc ∑ i, ∑ j, g i j
      = ∑ i, ∑ j, ((if i < j then g i j else 0) + (if j < i then g i j else 0)) := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        rcases lt_trichotomy i j with h | h | h
        · simp [h, not_lt.2 h.le]
        · subst h; simp [hg]
        · simp [h, not_lt.2 h.le]
    _ = ∑ i, ∑ j, (if i < j then g i j else 0) + ∑ i, ∑ j, (if j < i then g i j else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_add_distrib
    _ = ∑ i, ∑ j, (if i < j then g i j else 0) + ∑ i, ∑ j, (if i < j then g j i else 0) := by
        rw [Finset.sum_comm (f := fun i j ↦ if j < i then g i j else 0)]
    _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        split_ifs <;> simp

def expand {n : ℕ} (w : Fin n → Ω[B⁄R]) (δ : Fin n → Module.Dual B Ω[B⁄R]) : Om R B 2 →ₗ[B] Om R B 2 :=
  ∑ i, ∑ j, if i < j then (coordPair (δ i) (δ j)).smulRight (wedge R B (w i) (w j)) else 0

theorem expand_apply {n : ℕ} (w : Fin n → Ω[B⁄R]) (δ : Fin n → Module.Dual B Ω[B⁄R]) (x : Om R B 2) :
    expand w δ x = ∑ i, ∑ j, (if i < j then coordPair (δ i) (δ j) x else 0) • wedge R B (w i) (w j) := by
  simp only [expand, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp

theorem eq_expand {n : ℕ} (w : Fin n → Ω[B⁄R]) (δ : Fin n → Module.Dual B Ω[B⁄R])
    (hs : ∀ ω, ω = ∑ i, δ i ω • w i) (x : Om R B 2) :
    x = ∑ i, ∑ j, (if i < j then coordPair (δ i) (δ j) x else 0) • wedge R B (w i) (w j) := by
  rw [← expand_apply]
  have hx : x ∈ Submodule.span B (Set.range (exteriorPower.ιMulti B 2 (M := Ω[B⁄R]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    have hL : wedge R B (v 0) (v 1) = ∑ i, ∑ j, (δ i (v 0) * δ j (v 1)) • wedge R B (w i) (w j) := by
      conv_lhs => rw [hs (v 0), hs (v 1)]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_comm]
    rw [ιMulti_two, expand_apply]
    conv_lhs => rw [hL,
      sum_sum_eq_lt (fun i j ↦ (δ i (v 0) * δ j (v 1)) • wedge R B (w i) (w j)) (fun i ↦ by simp)]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs
    · rw [coordPair_wedge, wedge_swap (w j) (w i), smul_neg, sub_smul]; abel
    · simp
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, ← hy, ← hz]
  | smul c y _ hy => rw [map_smul, ← hy]

end Alg

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem coordPair_nat {n : ℕ} (Φ : Frame F n) (i j : Fin n) ⦃T T' : C⦄ (φ : T ⟶ T') (x : Om R (F.obj T) 2) :
    coordPair (Φ.δ i T') (Φ.δ j T') (pOm F 2 φ x) = mp F φ (coordPair (Φ.δ i T) (Φ.δ j T) x) := by
  have hx : x ∈ Submodule.span (F.obj T) (Set.range (exteriorPower.ιMulti (F.obj T) 2 (M := Ω[F.obj T⁄R]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [ιMulti_two, pOm_wedge, coordPair_wedge, coordPair_wedge, Φ.nat, Φ.nat, Φ.nat, Φ.nat]
    simp only [map_sub, map_mul]
  | zero => simp
  | add y z _ _ hy hz => simp only [map_add, hy, hz]
  | smul c y _ hy => rw [pOm_smul, map_smul, map_smul, hy, smul_eq_mul, smul_eq_mul, map_mul]

end GlobalTheory.AbCoh.TwoFormSum

namespace GlobalTheory.AbCoh

open TwoFormSum in

theorem twoForm_eq_wsum : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → ∀ ζ : W0 F 2, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ζ T' = pOm F 2 φ (ζ T)) →
      ∃ (n : ℕ) (u v : Fin n → Glob1 F), ζ = wsum F u v := by
  intro R _ C _ F ⟨n, ⟨Φ⟩⟩ h0 ζ hζ
  let g : Fin n → Fin n → C0 F := fun i j T ↦ coordPair (Φ.δ i T) (Φ.δ j T) (ζ T)
  have hg : ∀ i j, d0 F (g i j) = 0 := by
    intro i j
    funext T T' φ
    rw [amitsur_d0_apply]
    simp only [g]
    rw [hζ φ, coordPair_nat, sub_self]
    rfl
  choose c hc using fun i j ↦ (h0 (g i j) (hg i j)).exists
  let e : Fin (n * n) ≃ Fin n × Fin n := finProdFinEquiv.symm
  refine ⟨n * n, fun k ↦ (if (e k).1 < (e k).2 then c (e k).1 (e k).2 else 0) • Φ.w (e k).1,
    fun k ↦ Φ.w (e k).2, ?_⟩
  funext T
  simp only [wsum]
  rw [Fintype.sum_equiv e _ (fun p ↦ wedge R (F.obj T)
      (((if p.1 < p.2 then c p.1 p.2 else 0) • Φ.w p.1 : Glob1 F).1 T) ((Φ.w p.2).1 T)) (fun k ↦ rfl),
    Fintype.sum_prod_type]
  conv_lhs => rw [eq_expand (fun i ↦ (Φ.w i).1 T) (fun i ↦ Φ.δ i T) (Φ.sum T) (ζ T)]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Submodule.coe_smul, Pi.smul_apply, wedge_smul_left]
  split_ifs
  · have := hc i j T
    simp only [g] at this
    rw [this, algebraMap_smul]
  · simp

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFrameOfIsBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem hasFrame_of_isBaseChange : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∀ (W : Type) [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Projective R W] (j : W →ₗ[R] Glob1 F), (∀ T : C, ∃ e : W →ₗ[R] Ω[F.obj T⁄R], (∀ w, e w = (j w).1 T) ∧ IsBaseChange (F.obj T) e) → HasFrame F := by
  intro R _ C _ F W _ _ _ _ j h
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin' R W
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property v (LinearMap.id) hv
  have hw : ∀ x : W, x = ∑ i, σ x i • v (Pi.single i 1) := by
    intro x
    have := LinearMap.congr_fun hσ x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
    conv_lhs => rw [← this]
    conv_lhs => rw [show σ x = ∑ i, σ x i • Pi.single i (1 : R) from by
      ext k; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, map_smul]
  choose e he hb using h
  let l : Fin n → W →ₗ[R] R := fun i ↦ LinearMap.proj i ∘ₗ σ
  let δ : Fin n → ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T :=
    fun i T ↦ (hb T).lift (Algebra.linearMap R (F.obj T) ∘ₗ l i)
  have hδ : ∀ i T (x : W), δ i T (e T x) = algebraMap R (F.obj T) (σ x i) := by
    intro i T x
    exact (hb T).lift_eq _ x
  refine ⟨n, ⟨⟨fun i ↦ j (v (Pi.single i 1)), δ, ?_, ?_⟩⟩⟩
  · intro i T T' φ ω
    refine (hb T).inductionOn ω (fun ω ↦ δ i T' (p1 F φ ω) = mp F φ (δ i T ω)) ?_ ?_ ?_ ?_
    · simp
    · intro x
      have h1 : p1 F φ (e T x) = e T' x := by
        rw [he T x, he T' x]; exact ((j x).2 φ).symm
      rw [h1, hδ, hδ]
      exact ((mp F φ).commutes _).symm
    · intro s ω hω
      rw [oneFormsMapOfFunctorMorphism_smul, LinearMap.map_smul, LinearMap.map_smul, hω, smul_eq_mul, smul_eq_mul, map_mul]
    · intro a b ha hb'
      rw [map_add, map_add, map_add, ha, hb', map_add]
  · intro T ω
    refine (hb T).inductionOn ω (fun ω ↦ ω = ∑ i, δ i T ω • (j (v (Pi.single i 1))).1 T) ?_ ?_ ?_ ?_
    · simp
    · intro x
      simp_rw [hδ, ← he T, algebraMap_smul]
      conv_lhs => rw [hw x]
      rw [map_sum]; simp_rw [map_smul]
    · intro s ω hω
      conv_lhs => rw [hω]
      simp_rw [LinearMap.map_smul, Finset.smul_sum, smul_eq_mul, mul_smul]
    · intro a b ha hb'
      conv_lhs => rw [ha, hb']
      simp_rw [map_add, add_smul, Finset.sum_add_distrib]

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfRefinementStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCechOneCoboundary_of_refinement : ∀ {Y : Scheme.{0}} {I J : Type} (Uc : I → Y.Opens) (c : GlobalTheory.KS.C1 Uc), GlobalTheory.KS.IsCoc Uc c → ∀ (V : J → Y.Opens) (σ : J → I), (∀ p, V p ≤ Uc (σ p)) → (⨆ p, V p = ⊤) → ∀ (B : ∀ p, Γ(Y, V p)), (∀ p p', GlobalTheory.KS.rsT (c (σ p) (σ p')) (V p ⊓ V p') = GlobalTheory.KS.rsT (B p') (V p ⊓ V p') - GlobalTheory.KS.rsT (B p) (V p ⊓ V p')) → GlobalTheory.KS.IsCob Uc c := by
  first | exact @GlobalTheory.KS.Refine.isCob_of_refine | exact GlobalTheory.KS.Refine.isCob_of_refine | (intros; apply GlobalTheory.KS.Refine.isCob_of_refine <;> assumption)
end

