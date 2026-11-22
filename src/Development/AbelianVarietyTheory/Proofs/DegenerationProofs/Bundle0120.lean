import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0110
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfRelativeDimensionSpreadFromGeneric
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenSpread

theorem isIso_stalkMap_of_flat {X Y : Scheme.{0}} (φ : X ⟶ Y) [Flat φ] [SurjectiveOnStalks φ] (x : X) :
    IsIso (φ.stalkMap x) := by
  have h1 := Flat.stalkMap φ x
  have h2 := φ.stalkMap_surjective x
  algebraize [(φ.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (φ x))
    (B := X.presheaf.stalk x)
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ⟨FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x), h2⟩

theorem mem_smoothLocus_of_isPullback {X X₀ S S₀ : Scheme.{0}} {f : X ⟶ S} {f₀ : X₀ ⟶ S₀}
    {φ : X₀ ⟶ X} {j : S₀ ⟶ S} (h : IsPullback φ f₀ f j) [LocallyOfFinitePresentation f] [Flat j]
    [SurjectiveOnStalks j] [Smooth f₀] (x : X₀) : φ x ∈ f.smoothLocus := by
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  have : SurjectiveOnStalks φ :=
    MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) h.flip inferInstance
  have := isIso_stalkMap_of_flat φ x
  have := isIso_stalkMap_of_flat j (f₀ x)
  have h0 : (f₀.stalkMap x).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (f₀.smoothLocus_eq_top.ge (Set.mem_univ x))
  have h1 : ((f₀ ≫ j).stalkMap x).hom.FormallySmooth := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).2 h0
  rw [← h.w, Scheme.Hom.stalkMap_comp] at h1
  exact Scheme.Hom.mem_smoothLocus.mpr
    ((RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ _).1 h1)

theorem exists_opens_smoothOfRelativeDimension_of_isPullback {X X₀ S S₀ : Scheme.{0}} {f : X ⟶ S}
    {f₀ : X₀ ⟶ S₀} {φ : X₀ ⟶ X} {j : S₀ ⟶ S} (h : IsPullback φ f₀ f j)
    [LocallyOfFinitePresentation f] [Flat j] [SurjectiveOnStalks j] (n : ℕ)
    [SmoothOfRelativeDimension n f₀] (x : X₀) :
    ∃ W : X.Opens, φ x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ f) := by
  have : Smooth f₀ := SmoothOfRelativeDimension.smooth n _
  have hz := mem_smoothLocus_of_isPullback h x
  have : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    simp
  have h1 : SmoothOfRelativeDimension (0 + n) (pullback.snd f j) := by
    rw [← h.isoPullback_inv_snd]
    infer_instance
  have h2 : SmoothOfRelativeDimension (0 + (0 + (0 + n))) (pullback.snd (f.smoothLocus.ι ≫ f) j) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨W, hW, hW'⟩ := GlobalTheory.VeryDenseFibres.exists_opens_smoothOfRelativeDimension
    (f.smoothLocus.ι ≫ f) j n (by simpa using h2) ⟨φ x, hz⟩ (f₀ x) (by
      change f (φ x) = _
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.w])
  let i := W.ι ≫ f.smoothLocus.ι
  refine ⟨i.opensRange, ⟨⟨⟨φ x, hz⟩, hW⟩, rfl⟩, ?_⟩
  have e : i.opensRange.ι ≫ f = i.isoOpensRange.inv ≫ (W.ι ≫ f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc]
  have h3 : SmoothOfRelativeDimension (0 + n)
      (i.isoOpensRange.inv ≫ (W.ι ≫ f.smoothLocus.ι ≫ f)) := inferInstance
  rw [e]
  simpa using h3

theorem exists_smoothOfRelativeDimension :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → IsProper f → SmoothOfRelativeDimension n f₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) → SmoothOfRelativeDimension n f' := by
  intro R K _ _ _ _ _ _ n X X₀ f f₀ φ h hf hf₀
  have : LocallyOfFinitePresentation f := inferInstance
  have : Flat (spMap (algebraMap R K)) := flat_specMap_localization (nonZeroDivisors R) K
  have : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  let U : X.Opens := ⨆ W : {W : X.Opens // SmoothOfRelativeDimension n (W.ι ≫ f)}, W.1
  have hc : IsClosed (f '' (U : Set X)ᶜ) := f.isClosedMap _ U.2.isClosed_compl
  obtain ⟨a, ha, H⟩ := exists_forall_notMem (K := K) hc (by
    rintro w ⟨z, hz, e⟩
    obtain ⟨x, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h z w e
    obtain ⟨W, hW, hW'⟩ := exists_opens_smoothOfRelativeDimension_of_isPullback h n x
    exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩))
  refine ⟨a, ha, fun R' _ g hg X' π f' hp => ?_⟩
  have h1 : SmoothOfRelativeDimension n (pullback.snd f (spMap g)) := by
    refine GlobalTheory.ProperFlatNearFibre.smoothOfRelativeDimension_pullback_snd _ _ n fun z y e => ?_
    have h2 : z ∈ U := by
      by_contra hz
      exact H R' g hg y ⟨z, hz, e⟩
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    exact ⟨W.1, hW, W.2⟩
  have h2 : SmoothOfRelativeDimension (0 + n) (hp.isoPullback.hom ≫ pullback.snd f (spMap g)) :=
    inferInstance
  simpa using h2

end GlobalTheory.GenSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetryHypothesisSpreadFromGenericFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymSpread

variable {S U : Scheme.{0}} {G : Over S} {A : Over U} [GrpObj G] [GrpObj A] {j : U ⟶ S} {a : A.left ⟶ G.left}

theorem isPullback_square (h : IsGrpPullback A G j a) :
    IsPullback (lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))).left (A ⊗ A).hom (G ⊗ G).hom j := by
  let l := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
  have l₁ : l.left ≫ pullback.fst G.hom G.hom = pullback.fst A.hom A.hom ≫ a :=
    congrArg (fun z => z.left) (lift_fst (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A)))
  have l₂ : l.left ≫ pullback.snd G.hom G.hom = pullback.snd A.hom A.hom ≫ a :=
    congrArg (fun z => z.left) (lift_snd (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A)))
  have big : IsPullback (pullback.snd A.hom A.hom ≫ a) (pullback.fst A.hom A.hom) G.hom (A.hom ≫ j) :=
    (IsPullback.of_hasPullback A.hom A.hom).flip.paste_horiz h.1
  have h₁ : IsPullback l.left (pullback.fst A.hom A.hom) (pullback.fst G.hom G.hom) a := by
    refine IsPullback.of_right (h₁₂ := pullback.snd G.hom G.hom) (v₁₃ := G.hom) (h₂₂ := G.hom) ?_
      l₁ (IsPullback.of_hasPullback G.hom G.hom).flip
    rw [l₂, h.1.w]
    exact big
  exact h₁.paste_vert h.1

theorem pushPt_comp (h : IsGrpPullback A G j a) {u' : A ⟶ A} {u : G ⟶ G} (e : a ≫ u.left = u'.left ≫ a)
    {T : Over U} (x : T ⟶ A) : pushPt h.1.w (x ≫ u') = pushPt h.1.w x ≫ u :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ← e, Category.assoc])

variable [IsCommMonObj G] [IsCommMonObj A]

theorem lbIso_cube (h : IsGrpPullback A G j a) {L : LB G.left} {LA : LB A.left} (hL : L.IsLB) (hLA : LA.IsLB)
    (hb : LBIso LA (L.pull a)) {T : Over S} {T' : Over U} {n : ℕ} (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ A))
    (V : Over.mk (T'.hom ≫ j) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = V ≫ x i) :
    LBIso (cubeLB A x' LA) ((cubeLB G x L).pull V.left) :=
  LBIso.trans (DVR.linComb_isLB _ hLA _ _) (DVR.linComb_isLB _ (pull_isLB hL a) _ _)
    (pull_isLB (DVR.linComb_isLB _ hL _ _) _) (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
    (LBIso.chartPull (chartPullLinComb L a _ _ _ V.left fun I => psum_push h _ _ V hx I.down)
      (Geo.Tor.chartPullPull _ V.left V.left rfl) (lbIso_refl (DVR.linComb_isLB _ hL _ _)))

theorem lbIso_sym (h : IsGrpPullback A G j a) {L : LB G.left} {LA : LB A.left} (hL : L.IsLB) (hLA : LA.IsLB)
    (hb : LBIso LA (L.pull a)) {w wd : G ⟶ G} {w' wd' : A ⟶ A}
    (pa : ∀ {T : Over U} (x : T ⟶ A), pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w)
    (pd : ∀ {T : Over U} (x : T ⟶ A), pushPt h.1.w (x ≫ wd') = pushPt h.1.w x ≫ wd) :
    LBIso (cubeLB A ![𝟙 A, w'] LA) ((cubeLB G ![𝟙 G, w] L).pull a) ∧
    LBIso (cubeLB A ![fst A A ≫ w', snd A A] LA) ((cubeLB G ![fst G G ≫ w, snd G G] L).pull
      (lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))).left) ∧
    LBIso (cubeLB A ![fst A A, snd A A ≫ wd'] LA) ((cubeLB G ![fst G G, snd G G ≫ wd] L).pull
      (lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))).left) := by
  refine ⟨?_, lbIso_cube h hL hLA hb _ _ _ fun i => ?_, lbIso_cube h hL hLA hb _ _ _ fun i => ?_⟩
  · let V := pushPt h.1.w (𝟙 A)
    have hV : V.left = a := Category.id_comp _
    have c := lbIso_cube h hL hLA hb ![𝟙 G, w] ![𝟙 A, w'] V (fun i => by
      fin_cases i
      · simp [V]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _))
    rwa [hV] at c
  · fin_cases i
    · exact (pa _).trans (by simp)
    · simp
  · fin_cases i
    · simp
    · exact (pd _).trans (by simp)

theorem exists_forall_hypS : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → ∀ (w wd : G ⟶ G) (w₀ wd₀ : A ⟶ A), φ ≫ w.left = w₀.left ≫ φ → φ ≫ wd.left = wd₀.left ≫ φ → IsMonHom w₀ → IsMonHom wd₀ → w₀ * wd₀ = 𝟙 A → LBIso L₀ (cubeLB A ![𝟙 A, w₀] L₀) → LBIso (cubeLB A ![fst A A ≫ w₀, snd A A] L₀) (cubeLB A ![fst A A, snd A A ≫ wd₀] L₀) → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → HypS G' L' := by
  intro R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ hG h hL hL₀ hb w wd w₀ wd₀ ew ewd hw₀ hwd₀ hs hp ha
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap R K)) ∧ IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) :=
    ExtUnique.spec_fractionRing R K
  have := hG.smooth
  have := hG.proper
  have hw : IsMonHom w := ExtUnique.isMonHom_of_isGrpPullback h h w₀ w ew.symm
  have hwd : IsMonHom wd := ExtUnique.isMonHom_of_isGrpPullback h h wd₀ wd ewd.symm
  have hsum : w * wd = 𝟙 G := by
    refine ExtUnique.over_hom_ext_of_isPullback h.1 ?_
    have b : pushPt h.1.w (w₀ * wd₀) = pushPt h.1.w w₀ * pushPt h.1.w wd₀ := map_mul (pushHom h A) _ _
    have c := pushPt_comp h ew (𝟙 A)
    have d := pushPt_comp h ewd (𝟙 A)
    rw [Category.id_comp] at c d
    rw [c, d, ← MonObj.comp_mul, hs] at b
    have e : 𝟙 A.left ≫ φ = (𝟙 A.left ≫ φ) ≫ (w * wd).left := congrArg (fun z => z.left) b
    simp only [Category.id_comp] at e
    simpa using e.symm
  have cl : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x L).IsLB := fun x => DVR.linComb_isLB _ hL _ _
  have cl₀ : ∀ {T : Over (Sp K)} (x : Fin 2 → (T ⟶ A)), (cubeLB A x L₀).IsLB := fun x => DVR.linComb_isLB _ hL₀ _ _
  obtain ⟨c₁, c₂, c₃⟩ := lbIso_sym h hL hL₀ hb (fun x => pushPt_comp h ew x) (fun x => pushPt_comp h ewd x)
  have : IsProper (G ⊗ G).hom := by
    change IsProper (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  obtain ⟨a₁, ha₁, H₁⟩ := GenSpread.exists_lbIso G.hom h.1 hL (cl _)
    (hb.symm.trans (pull_isLB hL _) hL₀ (pull_isLB (cl _) _) (hp.trans hL₀ (cl₀ _) (pull_isLB (cl _) _) c₁))
  obtain ⟨a₂, ha₂, H₂⟩ := GenSpread.exists_lbIso (G ⊗ G).hom (isPullback_square h) (cl _) (cl _)
    (c₂.symm.trans (pull_isLB (cl _) _) (cl₀ _) (pull_isLB (cl _) _)
      (ha.trans (cl₀ _) (cl₀ _) (pull_isLB (cl _) _) c₃))
  refine ⟨a₁ * a₂, mul_ne_zero ha₁ ha₂, fun R' _ g hg G' _ _ π L' h' hL' hb' => ?_⟩
  rw [map_mul, IsUnit.mul_iff] at hg
  obtain ⟨w', hw', pa⟩ := SymBaseChange.exists_endo h' w
  obtain ⟨wd', hwd', pd⟩ := SymBaseChange.exists_endo h' wd
  have cl' : ∀ {T : Over (Sp R')} (x : Fin 2 → (T ⟶ G')), (cubeLB G' x L').IsLB := fun x =>
    DVR.linComb_isLB _ hL' _ _
  obtain ⟨d₁, d₂, d₃⟩ := lbIso_sym h' hL hL' hb' pa pd
  refine ⟨w', wd', hw', hwd', ?_, ?_, ?_⟩
  · apply SymBaseChange.pushPt_injective h'
    have b : pushPt h'.1.w (w' * wd') = pushPt h'.1.w w' * pushPt h'.1.w wd' := map_mul (pushHom h' G') _ _
    have c := pa (𝟙 G')
    have d := pd (𝟙 G')
    rw [Category.id_comp] at c d
    rw [b, c, d, ← MonObj.comp_mul, hsum, Category.comp_id]
  · exact hb'.trans hL' (pull_isLB hL _) (cl' _)
      ((H₁ R' g hg.1 _ π G'.hom h'.1.w).trans (pull_isLB hL _) (pull_isLB (cl _) _) (cl' _) d₁.symm)
  · exact d₂.trans (cl' _) (pull_isLB (cl _) _) (cl' _)
      ((H₂ R' g hg.2 _ _ (G' ⊗ G').hom (isPullback_square h').w).trans (pull_isLB (cl _) _) (pull_isLB (cl _) _)
        (cl' _) d₃.symm)

end GlobalTheory.SymSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymplecticLevelBaseChangePolarisedAbelianStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLevel_baseChange_polarisedAbelian : Laws → ∀ (S S' : Scheme.{0}) [IsLocallyNoetherian S] [IsLocallyNoetherian S'] (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → P'.g = P.g → ∀ (k : ℕ) (ze : Γ(S, ⊤)ˣ) (ze' : Γ(S', ⊤)ˣ), f.appTop.hom ze.val = ze'.val → IsPrimitiveRoot ze' k → ∀ lev : Out.Level P k ze, ∃ lev' : Out.Level P' k ze', ∀ (i : Fin (2 * P.g)) (i' : Fin (2 * P'.g)), (i : ℕ) = i' → (lev'.pt i').left ≫ φ = f ≫ (lev.pt i).left := by
  first | exact @GlobalTheory.exists_level_baseChange | exact GlobalTheory.exists_level_baseChange | (intros; apply GlobalTheory.exists_level_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoMove
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.FullMove

theorem isThetaPt_iso {S : Scheme.{0}} {P P' : PolAV S} (φ : P.A ≅ P'.A) [IsMonHom φ.hom]
    (hw : LBIso P.L (P'.L.pull φ.hom.left)) {T : Over S} {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)}
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P k x v) :
    IsThetaPt P' k (fun i => x i ≫ φ.hom) v := by
  refine ⟨H.1, H.2.1, fun p => ?_⟩
  obtain ⟨V, hV, Q⟩ := H.2.2 p
  refine ⟨V, hV, ?_⟩
  have hk' : ∀ i, (overResι V ≫ x i) ^ (k ^ 2) = 1 := fun i => by
    rw [← MonObj.comp_pow, hk, MonObj.comp_one]
  have Q' := GlobalTheory.ThetaPtUp.isThetaPtOver_up (T := overRes V) (T₀ := overRes V) (𝟙 (overRes V).left)
    (Geo.Tor.isGrpPullback_of_iso φ) hw ((Category.id_comp _).trans (Category.comp_id _).symm)
    (x₀ := fun i => overResι V ≫ x i ≫ φ.hom)
    (fun i => (Category.id_comp _).trans (by rw [← Category.assoc]; rfl)) hk' Q
  rw [IsIso.inv_id] at Q'
  exact Q'

def tateMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {k : Type} [Field k]
    {Q Q' : Type} [Group Q] [Group Q'] {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'}
    {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop} (I : TateIso D k Q act e) (F : Q ≃* Q')
    (ha : ∀ c x, F (act c x) = act' c (F x))
    (he : ∀ n x y c, x ^ n = 1 → y ^ n = 1 → e n x y c → e' n (F x) (F y) c) : TateIso D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n a := F (I.ev n a)
  add n a b := by rw [I.add, map_mul]
  lin n c a := by rw [I.lin, ha]
  ker n hn a := by rw [F.map_eq_one_iff, I.ker n hn]
  onto n hn x := by
    obtain ⟨y, rfl⟩ := F.surjective x
    rw [← map_pow, F.map_eq_one_iff, I.onto n hn]
    exact exists_congr fun a => F.injective.eq_iff.symm
  tower n m hn hm a := by rw [← map_pow, I.tower n m hn hm]
  isom n hn a b := he n _ _ _ ((I.onto n hn _).2 ⟨a, rfl⟩) ((I.onto n hn _).2 ⟨b, rfl⟩) (I.isom n hn a b)

def ptEquiv {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (φ : A ≅ A') [IsMonHom φ.hom] (T : Over S) :
    (T ⟶ A) ≃* (T ⟶ A') where
  toFun x := x ≫ φ.hom
  invFun y := y ≫ φ.inv
  left_inv x := by simp
  right_inv y := by simp
  map_mul' := map_mul (IsMonHom.monoidHom φ.hom T)

theorem exists_tateIso_move : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (K : Type) [Field K] [IsAlgClosed K] (o o' : Full D K) (φ : o.P.A ≅ o'.P.A), IsPolIso o.P o'.P φ → (letI := H.starRing; ∀ x, o.oa.act x ≫ φ.hom = φ.hom ≫ o'.oa.act x) → ∃ I' : (letI := H.starRing; TateIso D K (baseOver (Sp K) ⟶ o'.P.A) (fun a g => g ≫ o'.oa.act a) (fun n g g' c => WeilIs o'.P.A o'.P.L n g g' (unitOn c))), I'.ζ = o.I.ζ ∧ (∀ M a, I'.ev M a = o.I.ev M a ≫ φ.hom) ∧ ∀ m v, o.Theta m v → Full.Theta { o' with I := I' } m v := by
  intro hL E _ _ _ H D K _ _ o o' φ ⟨hφ, t⟩ hact
  letI := H.starRing
  obtain ⟨w, hw⟩ := LBIso.symm t
  refine ⟨tateMap o.I (ptEquiv φ _) (fun c x => ?_) (fun n x y c hx hy h => ?_), rfl, fun _ _ => rfl, fun m v h => ?_⟩
  · show (x ≫ o.oa.act c) ≫ φ.hom = (x ≫ φ.hom) ≫ o'.oa.act c
    rw [Category.assoc, hact, Category.assoc]
  · exact (weilIs_iso_iff hL.globalFns hL.cube o.P o'.P φ w hw n x y hx hy _).2 h
  · exact isThetaPt_iso φ ⟨w, hw⟩ (fun a => (o.I.onto _ (pow_pos h.1.pos 2) _).2 ⟨a, rfl⟩) h

end GlobalTheory.FullMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSectionNonzeroLocusSpecialFibreIffStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSection_nonzeroLocus_specialFibre_iff : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : Unif (IsLocalRing.maximalIdeal V) D A G) (ϑ : H0 U.LG.L 1), ∃ θ : LB.Sec D.toPre.P.L, ∀ y : (thickObj V (IsLocalRing.maximalIdeal V) 0 G).left, (fstG (IsLocalRing.maximalIdeal V) 0 G).left y ∈ nonzeroLocus ϑ ↔ (U.gt 0).pG.left y ∈ nonzeroLocus θ := by
  first | exact @GlobalTheory.SpecialFibreLocus.exists_sec_nonzeroLocus_iff | exact GlobalTheory.SpecialFibreLocus.exists_sec_nonzeroLocus_iff | (intros; apply GlobalTheory.SpecialFibreLocus.exists_sec_nonzeroLocus_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointSpecialFibreSectionNeZeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionPoint_specialFibre_section_ne_zero : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L → ∀ (N : M.Z.Opens) (σ : Q.SecFam N), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.FibNe N σ → y (cPt p) ∈ N → ∃ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ spMap jV) ⟶ u.G, t ^ (S.r * S.N) = 1 ∧ ∃ j, valF (X := Q.G.left) (t.left ≫ F) _ (σ j) ≠ 0 := by
  first | exact @GlobalTheory.ZH.TorsionNonzero.exists_torsion_valF_ne_zero | exact GlobalTheory.ZH.TorsionNonzero.exists_torsion_valF_ne_zero | (intros; apply GlobalTheory.ZH.TorsionNonzero.exists_torsion_valF_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationDataOfSemiAbelianSymmetryStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisationData_of_semiAbelianSymmetry : Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField V)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj G)) → HypS A.A A.L → ∀ gen : (Over.pullback (jK V)).obj G ≅ A.A, IsMonHom gen.hom → ∃ s : GlobalTheory.UU.HidaSetting V A G, s.gen = gen := by
  first | exact @GlobalTheory.ZH.exists_setting_of_hypS | exact GlobalTheory.ZH.exists_setting_of_hypS | (intros; apply GlobalTheory.ZH.exists_setting_of_hypS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitWeightZeroIntegralCoordsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_weightZero_integral_coords : Out.Laws → Out.Laws2 → ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls), Big g N N' → ∀ (c : Sp (OO p) ⟶ G.left) (w : J → OO p), c ≫ G.hom = spMap j → Crd H σ c w → (∃ i, cls i = 0 ∧ IsUnit (w i)) ∧ ∃ x : m.Φ.Pt, x.left ≫ m.r = rPt p ≫ c ∧ Crd (m.Φ.H 1) m.F x.left (fun i => IsLocalRing.residue (OO p) (w i)) := by
  first | exact @GlobalTheory.ZH.ModPrim.exists_unit_and_residue_point | exact GlobalTheory.ZH.ModPrim.exists_unit_and_residue_point | (intros; apply GlobalTheory.ZH.ModPrim.exists_unit_and_residue_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuationSubringIntegralClosureCompleteDVRStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_integral_closure_completeDVR : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (ϖ : O), GlobalTheory.LN.ArcBase O ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F], ∃ S : ValuationSubring F, ∀ x, x ∈ S ↔ IsIntegral O x := by
  first | exact @GlobalTheory.LN.exists_valuationSubring_isIntegral | exact GlobalTheory.LN.exists_valuationSubring_isIntegral | (intros; apply GlobalTheory.LN.exists_valuationSubring_isIntegral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonvanishingOfInvertiblePushforwardStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
theorem _root_.GlobalTheory.T.fibrewise_nonvanishing_of_invertible_pushforward : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t₀ : SAB H S), PushInvertible t₀.G t₀.PP.L → ∀ (R : Type) [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ S) (t : SAB H (Sp R)) (_ : SABMap t t₀ ξ), ThetaNZ t.G t.PP.L := by
  first | exact @GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible | exact GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible | (intros; apply GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonzeroSectionProdAndBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibrewiseNonzeroSection_prod_and_baseChange : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (A' : PolAV (Sp (FractionRing V))) (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), (ThetaNZ G U.P.L.L → ∃ σ : U.SecGT (𝟙_ _) 1, FibNZ (𝟙_ _ ⊗ G).hom σ) ∧ ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U'.SecGT (𝟙_ _) k), (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J') → FibNZ (𝟙_ _ ⊗ G).hom σ → FibNZ (𝟙_ _ ⊗ G').hom σ' := by
  first | exact @GlobalTheory.fibNZ_prod_and_baseChange | exact GlobalTheory.fibNZ_prod_and_baseChange | (intros; apply GlobalTheory.fibNZ_prod_and_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocusStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_mem_moduli_of_meets_abelian_locus : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), (ξ ⁻¹' abLocus Y.t.G).Nonempty → (∃ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Y.j = jK R ≫ ξ) ∧ PolAt t (jK R) ∧ ξ ⁻¹' abLocus Y.t.G = abLocus t.G := by
  first | exact @GlobalTheory.LN.generic_point_of_meets_abLocus | exact GlobalTheory.LN.generic_point_of_meets_abLocus | (intros; apply GlobalTheory.LN.generic_point_of_meets_abLocus <;> assumption)
end

