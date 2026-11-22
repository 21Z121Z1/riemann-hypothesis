import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TrivOnOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0094
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsE8ThetaStructure
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPicardGlueFiniteDisjointCover
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic

namespace GlobalTheory.CechPic.Glue

def extUnit {X W : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] (V : W.Opens) : Γ(W, V)ˣ →* Γ(X, g ''ᵁ V)ˣ :=
  Units.map (g.appIso V).inv.hom.toMonoidHom

theorem gm_extUnit {X W T : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] (V : W.Opens) (a : Γ(W, V)ˣ)
    (r : T ⟶ W) (t : T) (ht : r t ∈ V) : gm (r ≫ g) t (g ''ᵁ V) (extUnit g V a) = gm r t V a := by
  have hm : r t ∈ g ⁻¹ᵁ (g ''ᵁ V) := ⟨r t, ht, rfl⟩
  have e : pullU g (g ''ᵁ V) (extUnit g V a) = res (g.preimage_image_eq V).le a :=
    Units.ext (congrArg (fun q => q.hom a.val) (g.appIso_inv_app V))
  rw [← gm_pull r g t _ hm, e, gm_res r t _ hm]

theorem image_inf_le {X W : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] (A B : W.Opens) :
    g ''ᵁ A ⊓ g ''ᵁ B ≤ g ''ᵁ (A ⊓ B) := by
  rintro _ ⟨⟨a, ha, rfl⟩, hb⟩
  exact ⟨a, ⟨ha, (g.apply_mem_image_iff).1 hb⟩, rfl⟩

variable {Y : Scheme.{0}} {κ : Type} {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)]
  (L : ∀ i, LB (Z i))

def gT (i : κ) (k k' : (L i).ι) : Γ(Y, (f i) ''ᵁ (L i).U k ⊓ (f i) ''ᵁ (L i).U k')ˣ :=
  res (image_inf_le (f i) _ _) (extUnit (f i) _ ((L i).g k k'))

open Classical in

def gS : ∀ p q : (Σ i, (L i).ι),
    Γ(Y, (f p.1) ''ᵁ (L p.1).U p.2 ⊓ (f q.1) ''ᵁ (L q.1).U q.2)ˣ
  | ⟨i, k⟩, ⟨i', k'⟩ => if h : i = i' then by subst h; exact gT f L i k k' else 1

def glueLB : LB Y where
  ι := Σ i, (L i).ι
  U p := (f p.1) ''ᵁ (L p.1).U p.2
  g := gS f L

theorem glueLB_g (i : κ) (k k' : (L i).ι) : (glueLB f L).g ⟨i, k⟩ ⟨i, k'⟩ = gT f L i k k' := by
  show gS f L ⟨i, k⟩ ⟨i, k'⟩ = _
  simp [gS]

theorem gm_glueLB {T : Scheme.{0}} (i : κ) (r : T ⟶ Z i) (t : T) (k k' : (L i).ι) (hk : r t ∈ (L i).U k)
    (hk' : r t ∈ (L i).U k') :
    gm (r ≫ f i) t ((glueLB f L).U ⟨i, k⟩ ⊓ (glueLB f L).U ⟨i, k'⟩) ((glueLB f L).g ⟨i, k⟩ ⟨i, k'⟩) =
      gm r t ((L i).U k ⊓ (L i).U k') ((L i).g k k') := by
  rw [glueLB_g]
  have hm : (r ≫ f i) t ∈ (f i) ''ᵁ (L i).U k ⊓ (f i) ''ᵁ (L i).U k' :=
    ⟨(f i).apply_mem_image_iff.2 hk, (f i).apply_mem_image_iff.2 hk'⟩
  exact (gm_res _ t _ hm _).trans (gm_extUnit (f i) _ _ r t ⟨hk, hk'⟩)

theorem mem_image {X W : Scheme.{0}} (g : W ⟶ X) [IsOpenImmersion g] {A : W.Opens} {y : X} (h : y ∈ g ''ᵁ A) :
    ∃ z ∈ A, g z = y := h

theorem same_of_mem {i i' : κ} (hd : Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) {y : Y}
    (h : y ∈ (f i).opensRange) (h' : y ∈ (f i').opensRange) : i = i' := by
  by_contra hne
  exact (hd hne).le_bot ⟨h, h'⟩

variable {L} in
theorem isLB_glueLB (hL : ∀ i, (L i).IsLB) (hcov : ⨆ i, (f i).opensRange = ⊤)
    (hd : Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) : (glueLB f L).IsLB where
  cover := by
    refine top_le_iff.1 fun y _ => ?_
    have hy : y ∈ ⨆ i, (f i).opensRange := by rw [hcov]; trivial
    obtain ⟨i, z, rfl⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨k, hk⟩ := exists_chart (hL i) z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, k⟩, (f i).apply_mem_image_iff.2 hk⟩
  g_self := by
    rintro ⟨i, k⟩
    refine unit_ext fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := mem_image (f i) hy
    refine gm_inj (f i) z hy hy ?_
    have e := gm_glueLB f L i (𝟙 _) z k k hz hz
    rw [Category.id_comp] at e
    rw [map_one, gm_res _ z _ hy, e, gm_self (hL i) _ z hz]
  cocycle := by
    rintro ⟨i, k⟩ ⟨i', k'⟩ ⟨i'', k''⟩
    refine unit_ext fun y hy => ?_
    have h1 : y ∈ (f i).opensRange := (f i).image_le_opensRange _ hy.1.1
    have h2 : y ∈ (f i').opensRange := (f i').image_le_opensRange _ hy.1.2
    have h3 : y ∈ (f i'').opensRange := (f i'').image_le_opensRange _ hy.2
    obtain rfl := same_of_mem f hd h1 h2
    obtain rfl := same_of_mem f hd h1 h3
    obtain ⟨z, hz, rfl⟩ := mem_image (f i) hy.1.1
    have hz' : z ∈ (L i).U k' := (f i).apply_mem_image_iff.1 hy.1.2
    have hz'' : z ∈ (L i).U k'' := (f i).apply_mem_image_iff.1 hy.2
    refine gm_inj (f i) z hy hy ?_
    have e1 := gm_glueLB f L i (𝟙 _) z k k' hz hz'
    have e2 := gm_glueLB f L i (𝟙 _) z k' k'' hz' hz''
    have e3 := gm_glueLB f L i (𝟙 _) z k k'' hz hz''
    rw [Category.id_comp] at e1 e2 e3
    rw [map_mul, gm_res _ z _ hy, gm_res _ z _ hy, gm_res _ z _ hy, e1, e2, e3,
      gm_cocycle (hL i) _ z hz hz' hz'']

theorem exists_pic_glue : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y)
    [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) →
    (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) →
    ∀ c : ∀ i, Pic (Z i), ∃ d : Pic Y, ∀ i, GlobalTheory.CechPic.pull (f i) d = c i := by
  intro Y κ _ Z f _ hcov hd c
  choose L hL hc using fun i => cls_surj (c i)
  have hG := isLB_glueLB f hL hcov hd
  refine ⟨cls (glueLB f L) hG, fun i => ?_⟩
  rw [← cls_pull hG (f i) (pull_isLB hG (f i)), ← hc i]
  refine Eq.symm ((cls_eq_iff (hL i) (pull_isLB hG (f i))).2 (iso_of_chart (pull_isLB hG (f i)) ?_))
  exact
    { idx := fun k _ => ⟨i, k⟩
      le := fun k z hz => mem_pull.2 ((f i).apply_mem_image_iff.2 hz)
      g := fun z k k' hk hk' => Eq.symm ((gm_pull_g (glueLB f L) (f i) (𝟙 _) z (fun _ => ⟨i, k⟩) (fun _ => ⟨i, k'⟩)
        (mem_pull.2 ((f i).apply_mem_image_iff.2 hk)) (mem_pull.2 ((f i).apply_mem_image_iff.2 hk'))).trans
        (gm_glueLB f L i (𝟙 _) z k k' hk hk')) }

end GlobalTheory.CechPic.Glue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeAdditiveFamiliesAgree
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DualLocus

theorem exists_ideal_locTriv_noeth (hG : GlobalFnsSt) (R : Type) [CommRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) [GrpObj B] (hB : IsAbelianScheme B) (F : LB B.left) (hF : F.IsLB) :
    ∃ I : Ideal R, ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ B.left)
      (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) →
      ((∀ p : Spec (CommRingCat.of R'), ∃ U : (Spec (CommRingCat.of R')).Opens, p ∈ U ∧
        Triv ((F.pull π).pull (f' ⁻¹ᵁ U).ι)) ↔ I ≤ RingHom.ker g) := by
  haveI := hB.proper
  haveI := hB.geomConnected
  haveI := hB.smooth
  have hP := ProperFinite.nonempty_perf_of_isProper (R := R) B.hom hF
  have hQ := ProperFinite.nonempty_perf_of_isProper (R := R) B.hom (isLB_pw hF (-1))
  have hC := GlobalTheory.TrivLocus.isClosed_trivLocus R _ B.hom F hF hP hQ hB.proper
    (GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected)
  obtain ⟨I, hI⟩ := TrivRep.exists_ideal (TrivRep.TrivOn B.hom F) (TrivRep.TrivOn.comp B.hom F) (fun p => by
    by_cases hp : p ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0})
      (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
        IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) ∧ Triv (F.pull π)}
    · obtain ⟨K, _, g₀, X₀, π₀, f₀, hk, h₀, ht⟩ := hp
      obtain ⟨r, I, hr, -, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R _ B.hom F hF hP inferInstance inferInstance K g₀ X₀ π₀ f₀
        h₀ (CubeOpen.bijective_appTop hG B hB h₀) ht
      exact ⟨r, hk ▸ hr, I, fun S _ g hu => H S g _ _ _ (IsPullback.of_hasPullback _ _) hu⟩
    · obtain ⟨_, ⟨r, rfl⟩, hr, hU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (Set.mem_compl hp) hC.isOpen_compl
      refine ⟨r, hr, ⊤, fun S _ g hu => ⟨fun ht => ?_, fun h => ?_⟩⟩
      · rcases subsingleton_or_nontrivial S with _ | _
        · exact fun a _ => Subsingleton.elim _ _
        obtain ⟨m, hm⟩ := Ideal.exists_maximal S
        letI := Ideal.Quotient.field m
        let g' := (Ideal.Quotient.mk m).comp g
        refine (hU (a := ⟨RingHom.ker g', RingHom.ker_isPrime g'⟩) (hu.map (Ideal.Quotient.mk m)).ne_zero ?_).elim
        exact ⟨S ⧸ m, inferInstance, g', _, _, _, rfl, IsPullback.of_hasPullback _ _, ht.comp B.hom F S g _ _⟩
      · haveI : Subsingleton S := subsingleton_of_zero_eq_one
          ((h (Submodule.mem_top (x := 1))).symm.trans (map_one g))
        exact TrivRep.trivOn_of_subsingleton B.hom F S g)
  refine ⟨I, fun S _ g X' π f' h => ?_⟩
  rw [← hI S g]
  exact forall_congr' fun q => TrivRep.loc_iff B.hom F h q

variable {S : Scheme.{0}} (A : Over S)

theorem isPullback_lift {Y T : Over S} (y : Y ⟶ T) :
    IsPullback (lift (fst A Y) (snd A Y ≫ y)).left (snd A Y).left (snd A T).left y.left := by
  have h₀ : IsPullback (pullback.fst A.hom T.hom) (snd A T).left A.hom T.hom :=
    IsPullback.of_hasPullback A.hom T.hom
  have e₁ : (lift (fst A Y) (snd A Y ≫ y)).left ≫ pullback.fst A.hom T.hom = (fst A Y).left := by
    rw [show pullback.fst A.hom T.hom = (fst A T).left from rfl, ← Over.comp_left, lift_fst]
  have big : IsPullback ((lift (fst A Y) (snd A Y ≫ y)).left ≫ pullback.fst A.hom T.hom) (snd A Y).left A.hom
      (y.left ≫ T.hom) := by
    have := IsPullback.of_hasPullback A.hom Y.hom
    rw [e₁, Over.w y]
    exact this
  exact IsPullback.of_right big (by rw [← Over.comp_left, lift_snd, Over.comp_left]) h₀

theorem exists_closed_locTriv_noeth (hG : GlobalFnsSt) {T : Over S} [GrpObj A] [IsLocallyNoetherian T.left]
    (hA : IsAbelianScheme A) (F : LB (A ⊗ T).left) (hF : F.IsLB) :
    ∃ (G : Over S) (i : G ⟶ T), IsClosedImmersion i.left ∧ ∀ (Y : Over S) (y : Y ⟶ T),
      TrivSubscheme.LocTrivOver (snd A T).left F Y.left y.left ↔ ∃ z : Y ⟶ G, z ≫ i = y := by
  have h₀ : IsPullback (pullback.fst A.hom T.hom) (snd A T).left A.hom T.hom :=
    IsPullback.of_hasPullback A.hom T.hom
  obtain ⟨I, hI⟩ := TrivSubscheme.exists_idealSheaf (TrivSubscheme.LocTrivOver (snd A T).left F)
    TrivSubscheme.LocTrivOver.comp TrivSubscheme.locTrivOver_of_affine (fun U => by
      haveI := IsLocallyNoetherian.component_noetherian U
      let t : Spec (CommRingCat.of Γ(T.left, U)) ⟶ S := U.2.fromSpec ≫ T.hom
      have h₁ : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom (U.2.fromSpec ≫ T.hom) :=
        IsPullback.of_hasPullback _ _
      let φ := h₀.lift _ _ (h₁.w.trans (Category.assoc _ _ _).symm)
      have h₂ : IsPullback φ (pullback.snd A.hom t) (snd A T).left U.2.fromSpec :=
        IsPullback.of_right (by rw [h₀.lift_fst]; exact h₁) (h₀.lift_snd _ _ _) h₀
      obtain ⟨I, hI⟩ := exists_ideal_locTriv_noeth hG Γ(T.left, U) ((Over.pullback t).obj A)
        (CubeGen.isAb_baseChange hA t) (F.pull φ) (LB.isLB_pull hF φ)
      refine ⟨I, fun R g => ?_⟩
      have h₃ := IsPullback.of_hasPullback (pullback.snd A.hom t) (Spec.map g)
      rw [← hI R g.hom _ _ _ h₃, TrivSubscheme.locTrivOver_iff (h₃.paste_horiz h₂)]
      refine forall_congr' fun y => exists_congr fun V => and_congr_right fun _ => ?_
      rw [← Category.assoc]
      exact ((TrivSubscheme.triv_pull_iff _ _ _).trans (TrivSubscheme.triv_pull_iff _ _ _)).symm)
  refine ⟨Over.mk (I.subschemeι ≫ T.hom), Over.homMk I.subschemeι rfl,
    inferInstanceAs (IsClosedImmersion I.subschemeι), fun Y y => ?_⟩
  rw [hI]
  constructor
  · intro h
    have h' : I.subschemeι.ker ≤ y.left.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι y.left h') ?_, ?_⟩
    · exact (IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w y)
    · exact Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  · rintro ⟨z, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp z.left I.subschemeι)

variable {A} [GrpObj A]

theorem same_iff_locTriv (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {T : Over S} {N N' : LB (A ⊗ T).left}
    (hN : Fam A N) (hN' : Fam A N') {F : LB (A ⊗ T).left} (hF : F.IsLB)
    (hc : cls F hF = cls N hN.isLB - cls N' hN'.isLB) (Y : Over S) (y : Y ⟶ T) :
    Same A N N' y y ↔ TrivSubscheme.LocTrivOver (snd A T).left F Y.left y.left := by
  let ψ := (lift (fst A Y) (snd A Y ≫ y)).left
  let p := (snd A Y).left
  let e := (lift (1 : Y ⟶ A) (𝟙 Y)).left
  have he : e ≫ p = 𝟙 Y.left := by
    simp only [e, p]
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have hs : Same A N N' y y ↔ CechPic.pull ψ (cls F hF) = 0 := by
    rw [same_iff hN.isLB hN'.isLB, hc, map_sub, sub_eq_zero]
    rfl
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ Y).left),
      Triv (F.pull (r ≫ ψ)) ↔ CechPic.pull r (CechPic.pull ψ (cls F hF)) = 0 := fun r => by
    rw [← pull_comp, ← cls_pull hF _ (pull_isLB hF _)]
    exact (cls_eq_zero_iff (pull_isLB hF _)).symm
  have z₀ : CechPic.pull (e ≫ ψ) (cls F hF) = 0 := by
    have ee : e ≫ ψ = (lift (1 : Y ⟶ A) y).left := by
      simp only [e, ψ]
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.id_comp]
    rw [ee, hc, map_sub]
    have a := hN.add.evc_one hN.isLB y
    have b := hN'.add.evc_one hN'.isLB y
    simp only [evc] at a b
    rw [a, b, sub_zero]
  rw [TrivSubscheme.locTrivOver_iff (isPullback_lift A y), hs]
  constructor
  · intro h q
    exact ⟨⊤, trivial, (key _).2 (by rw [h, map_zero])⟩
  · intro h
    have cl : ∀ {Z : Scheme.{0}} (φ' : Fin 2 → (Z ⟶ (A ⊗ T).left)),
        Triv (LB.LinComb F φ' ![1, -1]) ↔
          CechPic.pull (φ' 0) (cls F hF) - CechPic.pull (φ' 1) (cls F hF) = 0 := fun φ' => by
      refine (cls_eq_zero_iff (LB.isLB_linComb hF _ _)).symm.trans ?_
      rw [cls_linComb hF, Fin.sum_univ_two]
      simp [sub_eq_add_neg]
    have sec : ∀ {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ Y).left),
        CechPic.pull (r ≫ p ≫ e ≫ ψ) (cls F hF) = 0 := fun r => by
      rw [pull_comp, pull_comp, z₀, map_zero, map_zero]
    have T₀ : Triv (LB.LinComb F ![ψ, p ≫ e ≫ ψ] ![1, -1]) := by
      refine CubeGen.triv_of_local hF _ _ p e he (fun Z b U _ k => ?_) (fun V => ?_) (fun s => ?_)
      · have w : b ≫ e ≫ p ≫ e ≫ ψ = b ≫ e ≫ ψ := by
          rw [reassoc_of% he]
        simp [Fin.prod_univ_two, w]
      · let YV : Over S := Over.mk (V.ι ≫ Y.hom)
        let v : YV ⟶ Y := Over.homMk V.ι rfl
        exact ⟨_, _, (snd A YV).left, isPullback_lift A v, surj_snd hG hA YV⟩
      · obtain ⟨U, hU, ht⟩ := h s
        refine ⟨U, hU, ?_⟩
        unfold CubeGen.TrivAt
        rw [cl]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [sec, sub_zero, pull_comp]
        exact (key _).1 ht
    have := (cl _).1 T₀
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at this
    have s₁ := sec (𝟙 _)
    rw [Category.id_comp] at s₁
    rwa [s₁, sub_zero] at this

theorem exists_closed_same : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left],
    IsAbelianScheme A → ∀ (N N' : LB (A ⊗ T).left), Fam A N → Fam A N' → ∃ (G : Over S) (i : G ⟶ T),
      IsClosedImmersion i.left ∧ ∀ (Y : Over S) (y : Y ⟶ T), Same A N N' y y ↔ ∃ z : Y ⟶ G, z ≫ i = y := by
  intro S A T _ _ hA N N' hN hN'
  obtain ⟨F, hF, hc⟩ := cls_surj (cls N hN.isLB - cls N' hN'.isLB)
  obtain ⟨G, i, hi, hG⟩ := exists_closed_locTriv_noeth A ExpansionTotal.globalFns hA F hF
  exact ⟨G, i, hi, fun Y y => (same_iff_locTriv ExpansionTotal.globalFns hA hN hN' hF hc Y y).trans (hG Y y)⟩

end GlobalTheory.DualLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmPointNonvanishingSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.CovDetect

theorem exists_good_cmPt_frame_ne_zero : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    2 < Module.finrank ℚ D.host.E / 2 → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), GapGe 1 la →
    ∀ [StarRing (𝓞 D.host.E)], (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ F ∈ Y.V (wtOf _ la 0), F ≠ 0 →
    ∃ (z : CMPt Y.d.Xo₂ Y.d.c₂) (La : ℝ) (y : FrPt Y.d.Xo₂ Y.d.c₂ z.K),
      z.Good (Module.finrank ℚ D.host.E / 2) La ∧ y.x = z.x ∧ evR Y.d.Xo₂ Y.d.c₂ F y ≠ 0 := by
  classical
  intro hP D T j Y e o hG hdeg la hgap _ hstar F hF hF0
  have hσ : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom := rfl
  have hU := hG.unf _ hσ
  have hFm := GlobalTheory.AllWt.mem_cuspW.1 hF
  obtain ⟨k, x₁, hx₁, hne₁⟩ := GlobalTheory.T.exists_uniformisationFrame_reading_ne_zero _ _ _ _ _ _ _ _ _ hU _ F hFm.1 hF0
  obtain ⟨Xx, 𝔄, hX, h𝔄, hΛ⟩ := GlobalTheory.T.goodCover_component_extends_to_rankOne_cusp_data D T j Y e o hG _ hσ k
  have hbdd := (Formalism.L2.Pj.abelian₂.holSub_SS ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds _ _ (hFm.2 _ hσ) k).1
  have hr : 0 < D.R.r := by
    have hn : 0 < D.R.ord := D.R.ord_pos
    have hk := D.R.f_le_k
    have ht := D.R.rank_add_five_le
    unfold Ranks.r; omega
  obtain ⟨La, x, lam, hx, hB, hne⟩ := GlobalTheory.CMDetect.exists_cm_frame Xx _ hX hr _ _ hbdd hx₁ hne₁
  obtain ⟨z, σ₁, hz, hzx⟩ := GlobalTheory.LamT.exists_good_cmPt_at_frame _ _ _ _ _ _ hstar _ _ hU hr k ⟨x, hx⟩ Xx hX 𝔄 h𝔄 hΛ
    La lam hB
  have hev : evR Y.d.Xo₂ Y.d.c₂ F ((Y.U _).un k ⟨x, hx⟩) ≠ 0 := by
    intro h0
    apply hne
    change (if h : x ∈ ((Y.U _).X k).dom then toC (evR Y.d.Xo₂ Y.d.c₂ F ((Y.U _).un k ⟨x, h⟩)) else 0) = 0
    rw [dif_pos hx]
    exact h0
  obtain ⟨y, hy, hyne⟩ := GlobalTheory.T.exists_numberFieldFrame_value_ne_zero_of_complex _ _ _ _ _ _ z.K z.y _ F hFm.1 _ σ₁ _ hzx hev
  exact ⟨z, La, y, hz, hy.trans hz.2.2.2.1, hyne⟩

end GlobalTheory.CovDetect
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrCentre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical

namespace GlobalTheory.DvrCentre

theorem exists_complete_dvr_centre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (M : RatModel o Ω) (z : M.Z), ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
    (_ : CharZero V) (ξ : Sp V ⟶ M.Z), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧
    ξ (IsLocalRing.closedPoint V) = z ∧ ∃ w, ξ w = genericPoint M.Z := by
  intro o Ω _ _ _ hA M z
  have hΩ : CharZero Ω := hA.char
  by_cases hz : z = genericPoint M.Z
  · subst hz
    have : CharZero (PowerSeries Ω) := charZero_of_injective_ringHom (PowerSeries.C_injective (R := Ω))
    have hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries Ω)) (PowerSeries Ω) := by
      first
      | infer_instance
      | (rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance)
    refine ⟨PowerSeries Ω, inferInstance, inferInstance, inferInstance, this,
      spMap (PowerSeries.C (R := Ω)) ≫ M.pt, hc, ?_, IsLocalRing.closedPoint _, ?_⟩
    · exact M.pt_apply _
    · exact M.pt_apply _
  · have : IsDedekindDomain o := hA.ded
    have : IsLocallyNoetherian M.Z := by
      have := M.lft
      exact LocallyOfFiniteType.isLocallyNoetherian M.s
    let S := M.Z.presheaf.stalk z
    have hS : CharZero S := (M.stalkHom z).charZero

    have hgen : M.Z.fromSpecStalk z (⊥ : PrimeSpectrum S) = genericPoint M.Z := by
      have h1 : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk z) := by
        rw [Scheme.range_fromSpecStalk]
        exact genericPoint_specializes z
      obtain ⟨q, hq⟩ := h1
      have h2 : (⊥ : PrimeSpectrum S) ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
      have h3 := h2.map (M.Z.fromSpecStalk z).continuous
      rw [hq] at h3
      exact (h3.antisymm (genericPoint_specializes _)).eq
    have hne : (⊥ : Ideal S) ≠ IsLocalRing.maximalIdeal S := by
      intro e
      apply hz
      have : (⊥ : PrimeSpectrum S) = IsLocalRing.closedPoint S := PrimeSpectrum.ext e
      rw [← hgen, this, Scheme.fromSpecStalk_closedPoint]
    obtain ⟨O, _, hO, hO', hO'', φ, h1, h2⟩ :=
      GlobalTheory.exists_complete_discreteValuationRing_ker_eq (S := S) (⊥ : Ideal S) hne
    have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h1
    have : CharZero O := charZero_of_injective_ringHom hφ
    refine ⟨O, inferInstance, hO, hO', this, spMap φ ≫ M.Z.fromSpecStalk z, hO'', ?_, (⊥ : PrimeSpectrum O), ?_⟩
    · refine (Scheme.Hom.comp_apply _ _ _).trans
        (Eq.trans (congrArg (M.Z.fromSpecStalk z) ?_) (Scheme.fromSpecStalk_closedPoint (x := z)))
      exact IsLocalRing.comap_closedPoint φ
    · refine (Scheme.Hom.comp_apply _ _ _).trans (Eq.trans (congrArg (M.Z.fromSpecStalk z) ?_) hgen)
      exact PrimeSpectrum.ext h1

end GlobalTheory.DvrCentre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CycLift

open Polynomial

theorem exists_injective_hom {n : ℕ} (hn : n ≠ 0) {V : Type} [CommRing V] [IsDomain V] [CharZero V]
    {u : V} (hu : IsPrimitiveRoot u n) (hnV : IsUnit (n : V)) :
    ∃ f : cycAway n →+* V, Function.Injective f ∧ f (zetaAway n) = u := by
  have hp := Nat.pos_of_ne_zero hn
  let L := FractionRing V
  have hinj : Function.Injective (algebraMap V L) := IsFractionRing.injective V L
  haveI : CharZero L := charZero_of_injective_algebraMap hinj
  have hz : IsPrimitiveRoot (zetaAway n : ℂ) n := Complex.isPrimitiveRoot_exp n hn
  have hi : IsIntegral ℚ (zetaAway n : ℂ) := (hz.isIntegral hp).tower_top
  let K := IntermediateField.adjoin ℚ {(zetaAway n : ℂ)}
  have hle : cycAway n ≤ K.toSubfield.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | rfl)
    · exact IntermediateField.mem_adjoin_simple_self ℚ _
    · exact K.inv_mem (natCast_mem K n)
  have huL : IsPrimitiveRoot (algebraMap V L u) n := hu.map_of_injective hinj
  have hr : algebraMap V L u ∈ (minpoly ℚ (zetaAway n : ℂ)).aroots L := by
    rw [← cyclotomic_eq_minpoly_rat hz hp, mem_aroots]
    refine ⟨cyclotomic_ne_zero n ℚ, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact huL.isRoot_cyclotomic hp
  let g : K →ₐ[ℚ] L := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hi).symm ⟨_, hr⟩
  have hg : g (IntermediateField.AdjoinSimple.gen ℚ (zetaAway n : ℂ)) = algebraMap V L u :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hi ⟨_, hr⟩
  let f₀ : cycAway n →+* L := g.toRingHom.comp (Subring.inclusion hle)
  have hf₀ : Function.Injective f₀ := g.toRingHom.injective.comp (Subring.inclusion_injective hle)
  have hζ : f₀ (zetaAway n) = algebraMap V L u := hg
  have hmem : ∀ x, f₀ x ∈ (algebraMap V L).range := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨u, hζ.symm⟩
      · refine ⟨↑hnV.unit⁻¹, ?_⟩
        have e : (n : cycAway n) * ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1 :=
          Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0))
        have e₁ := congrArg f₀ e
        rw [map_mul, map_natCast, map_one] at e₁
        have e₂ : (n : L) * algebraMap V L ↑hnV.unit⁻¹ = 1 := by
          rw [← map_natCast (algebraMap V L) n, ← map_mul, hnV.mul_val_inv, map_one]
        exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one e₂) (e₂.trans e₁.symm)
    | zero => exact Set.mem_of_eq_of_mem (map_zero f₀) (zero_mem _)
    | one => exact Set.mem_of_eq_of_mem (map_one f₀) (one_mem _)
    | add x y hx hy ihx ihy => exact (map_add f₀ ⟨x, hx⟩ ⟨y, hy⟩) ▸ add_mem ihx ihy
    | neg x hx ih => exact (map_neg f₀ ⟨x, hx⟩) ▸ neg_mem ih
    | mul x y hx hy ihx ihy => exact (map_mul f₀ ⟨x, hx⟩ ⟨y, hy⟩) ▸ mul_mem ihx ihy
  let e := RingEquiv.ofBijective (algebraMap V L).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  have he : ∀ y, algebraMap V L (e.symm y) = y := fun y => congrArg Subtype.val (e.apply_symm_apply y)
  refine ⟨e.symm.toRingHom.comp (f₀.codRestrict _ hmem),
    e.symm.injective.comp (fun a b h => hf₀ (congrArg Subtype.val h)), hinj ?_⟩
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he]
  exact hζ

end GlobalTheory.CycLift
end

