import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0084

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleProductAcyclicOfAffineBaseAcyclic
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProductAcyclic

theorem acyclic_of_homology_equiv {R : Type} [CommRing R] {C C' : CochainComplex (ModuleCat.{0} R) ℕ}
    (e : ∀ n, Nonempty (C.homology n ≃ₗ[R] C'.homology n)) (h : C.Acyclic) : C'.Acyclic := by
  intro n
  obtain ⟨e⟩ := e n
  have h₁ := h n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton] at h₁ ⊢
  exact e.symm.injective.subsingleton

theorem exists_cover (X : Scheme.{0}) [CompactSpace X] {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀)
    (O : X.Opens) (h : ∀ x, x ∉ V₀ → x ∈ O) :
    ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens), (∀ j, IsAffineOpen (V j)) ∧ ⨆ j, V j = ⊤ ∧
      V 0 = V₀ ∧ ∀ j, j ≠ 0 → V j ≤ O := by
  have hc : IsCompact (V₀ : Set X)ᶜ := V₀.isOpen.isClosed_compl.isCompact
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover
    (fun W : {W : X.Opens // IsAffineOpen W ∧ W ≤ O} => (W.1 : Set X)) (fun W => W.1.isOpen) (by
      intro x hx
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWo⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (h x hx) O.isOpen
      exact Set.mem_iUnion.2 ⟨⟨W, hW, hWo⟩, hxW⟩)
  refine ⟨s.card, Fin.cons V₀ fun j => (s.equivFin.symm j).1.1, fun j => ?_, ?_, rfl, fun j hj => ?_⟩
  · refine Fin.cases hV₀ (fun j => ?_) j
    exact (s.equivFin.symm j).1.2.1
  · refine top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    by_cases hx : x ∈ V₀
    · exact ⟨0, hx⟩
    · obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.1 (hs hx)
      refine ⟨(s.equivFin ⟨W, hW⟩).succ, ?_⟩
      simpa using hxW
  · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hj
    exact (s.equivFin.symm j).1.2.2

variable {K : Type} [Field K] {Z T X : Scheme.{0}} {p : Z ⟶ T} {g : T ⟶ Spec (CommRingCat.of K)}
  {q : Z ⟶ X} {h : X ⟶ Spec (CommRingCat.of K)} {F : LB Z}

theorem over_affineOpen (sq : IsPullback p q g h) [IsSeparated h] (hF : F.IsLB)
    {R : Type} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ T} [IsOpenImmersion t] {Y : Scheme.{0}}
    {π : Y ⟶ Z} {f : Y ⟶ Spec (CommRingCat.of R)} (H : IsPullback π f p t)
    {V : T.Opens} (hV : t.opensRange = V) {ν : Type} [LinearOrder ν] [Fintype ν]
    (B : ν → X.Opens) (hB : ∀ i, IsAffineOpen (B i)) (hc : ⨆ i, B i = ⊤) :
    (∀ i, IsAffineOpen (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V)) ∧
    ((∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) →
        ⨆ i, D i = ⊤ → (cechLB f (F.pull π) D).Acyclic) ↔
      (cechLB (p ≫ g) F fun i => q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V).Acyclic) := by
  have H' : IsPullback (π ≫ q) f h (t ≫ g) := H.paste_horiz sq.flip
  have : IsOpenImmersion π := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H.flip ‹_›
  have hq : IsAffineHom (π ≫ q) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) H'.flip inferInstance
  have hsep : IsSeparated f := MorphismProperty.of_isPullback (P := @IsSeparated) H' ‹_›
  have hr : π.opensRange = p ⁻¹ᵁ V := by
    subst hV
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, rfl⟩
      exact ⟨f y, by rw [← Scheme.Hom.comp_apply, ← H.w, Scheme.Hom.comp_apply]⟩
    · rintro x ⟨y, hy⟩
      obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback H x y hy.symm
      exact ⟨w, hw⟩
  have hE (i : ν) : π ⁻¹ᵁ (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) = (π ≫ q) ⁻¹ᵁ B i := by
    rw [← hr, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq,
      Scheme.Hom.comp_preimage]
  have hA (i : ν) : IsAffineOpen ((π ≫ q) ⁻¹ᵁ B i) := (hB i).preimage _
  have hA' (i : ν) : IsAffineOpen (π ⁻¹ᵁ (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V)) :=
    (congrArg IsAffineOpen (hE i)).mpr (hA i)
  have hc' : ⨆ i, π ⁻¹ᵁ (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) = ⊤ := by
    simp only [hE]
    rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  obtain ⟨e⟩ := cechLB_pull_iso_of_isOpenImmersion K _ (p ≫ g) F _ π ν
    (fun i => q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) hF fun i => hr ▸ inf_le_right
  refine ⟨fun i => ?_, fun h₁ n => ?_, fun h₁ κ _ _ D hD hDc => ?_⟩
  · have h₁ := (hA i).image_of_isOpenImmersion π
    rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, hr, inf_comm] at h₁
  · exact (MumfordCohom.acyclic_cechLB_of_acyclic _ _ _ _ (h₁ ν _ hA' hc') n).of_iso e
  · exact acyclic_of_homology_equiv (cechLB_homology_equiv_of_affine_covers R Y f _ ν _ κ D
      (LB.isLB_pull hF π) hsep hA' hc' hD hDc)
      (MumfordCohom.acyclic_cechLB_of_acyclic _ _ _ _ fun n => (h₁ n).of_iso e.symm)

theorem isAffineOpen_prod (sq : IsPullback p q g h) [IsSeparated h] (hF : F.IsLB) {V : T.Opens}
    (hV : IsAffineOpen V) {ν : Type} [LinearOrder ν] [Fintype ν]
    (B : ν → X.Opens) (hB : ∀ i, IsAffineOpen (B i)) (hc : ⨆ i, B i = ⊤) (i : ν) :
    IsAffineOpen (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) :=
  (over_affineOpen (R := Γ(T, V)) sq hF (IsPullback.of_hasPullback p hV.fromSpec)
    hV.opensRange_fromSpec B hB hc).1 i

theorem homology_equiv_over (sq : IsPullback p q g h) [IsSeparated g] [IsSeparated h] (hF : F.IsLB)
    {σ : Type} [LinearOrder σ] [Fintype σ] (V : σ → T.Opens) (hV : ∀ j, IsAffineOpen (V j))
    (hVc : ⨆ j, V j = ⊤) (k : σ)
    (H : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z)
      (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t →
      ∀ j, j ≠ k → (∀ y, t y ∈ V j) →
      ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) →
        ⨆ i, D i = ⊤ → (cechLB f (F.pull π) D).Acyclic)
    {ν : Type} [LinearOrder ν] [Fintype ν] (B : ν → X.Opens) (hB : ∀ i, IsAffineOpen (B i))
    (hBc : ⨆ i, B i = ⊤) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → Z.Opens)
    (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤) (n : ℕ) :
    Nonempty ((cechLB (p ≫ g) F D).homology n ≃ₗ[K]
      (cechLB (p ≫ g) F fun i => q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V k).homology n) := by
  have : T.IsSeparated := ⟨by
    rw [← terminal.comp_from g]
    infer_instance⟩
  have : X.IsSeparated := ⟨by
    rw [← terminal.comp_from h]
    infer_instance⟩
  have : IsSeparated p := MorphismProperty.of_isPullback (P := @IsSeparated) sq.flip ‹_›
  obtain ⟨e₁⟩ := cechLB_homology_equiv_trunc₂ K _ (p ≫ g) F κ D _
    (fun i => q ⁻¹ᵁ B i) _ (fun j => p ⁻¹ᵁ V j) hF inferInstance hD hc
    (by rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top])
    (by rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top])
    (fun i _ hW => MumfordCohom.isAffineOpen_preimage_inf _ (hB i) hW)
    (fun j _ hW => MumfordCohom.isAffineOpen_preimage_inf _ (hV j) hW)
    (fun i j => isAffineOpen_prod sq hF (hV j) B hB hBc i) n
  have e₂ := trunc₂HomologyIsoFstSingleton k (secCube (p ≫ g) F fun u : ν ⊕ₗ σ =>
      Sum.elim (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) (ofLex u))
    (fun s hs hs' => by
      have hVs : IsAffineOpen (⨅ j ∈ s, V j) :=
        IsAffineOpen.biInf _ s.finite_toSet hs fun j _ => hV j
      obtain ⟨j, hj, hjk⟩ : ∃ j ∈ s, j ≠ k := by
        by_contra! h₀
        exact hs' (Finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨hs, h₀⟩)
      have H₀ := IsPullback.of_hasPullback p hVs.fromSpec
      have h₁ := (over_affineOpen (R := Γ(T, ⨅ j ∈ s, V j)) sq hF H₀ hVs.opensRange_fromSpec
        B hB hBc).2.1 (H Γ(T, ⨅ j ∈ s, V j) _ _ _ _ H₀ inferInstance j hjk
          fun y => biInf_le V hj (hVs.range_fromSpec.le ⟨y, rfl⟩))
      obtain ⟨i₂⟩ := MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ g) F
        (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) s _ (preimage_biInf V p s)
      exact fun m => (h₁ m).of_iso i₂) n
  obtain ⟨i₂⟩ := MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ g) F
    (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) {k} (p ⁻¹ᵁ V k) (by simp)
  exact ⟨e₁ ≪≫ₗ (e₂ ≪≫ (HomologicalComplex.homologyMapIso i₂ n).symm).toLinearEquiv⟩

theorem acyclic_of_over_affine_and_converse : ∀ (K : Type) [Field K] (Z T : Scheme.{0}) (p : Z ⟶ T) (g : T ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0}) (q : Z ⟶ X) (h : X ⟶ Spec (CommRingCat.of K)), IsPullback p q g h → IsSeparated g → QuasiCompact g → IsSeparated h → QuasiCompact h → ∀ F : LB Z, F.IsLB → ((∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Z).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (p ≫ g) (F) D).Acyclic)) ∧ ∀ t₀ : T, IsClosed ({t₀} : Set T) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ y, t y ≠ t₀) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Z).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (p ≫ g) (F) D).Acyclic) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) := by
  intro K _ Z T p g X q h sq _ _ _ _ F hF
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace g
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace h
  obtain ⟨m, B, hB, hBc, -, -⟩ := exists_cover X (isAffineOpen_bot X) ⊤ fun _ _ => trivial
  refine ⟨fun H κ _ _ D hD hc => ?_, fun t₀ ht₀ H hac R _ t Y π f H₀ ht => ?_⟩
  · obtain ⟨r, V, hV, hVc, -, -⟩ := exists_cover T (isAffineOpen_bot T) ⊤ fun _ _ => trivial
    have H₀ := IsPullback.of_hasPullback p (hV 0).fromSpec
    refine acyclic_of_homology_equiv (fun n => ?_) ((over_affineOpen (R := Γ(T, V 0)) sq hF H₀
      (hV 0).opensRange_fromSpec B hB hBc).2.1 (H Γ(T, V 0) _ _ _ _ H₀ inferInstance))
    exact (homology_equiv_over sq hF V hV hVc 0
      (fun R _ t Y π f H₁ ht _ _ _ => H R t Y π f H₁ ht) B hB hBc D hD hc n).map fun e => e.symm
  · by_cases h₀ : t₀ ∈ t.opensRange
    swap
    · exact H R t Y π f H₀ ht fun y hy => h₀ ⟨y, hy⟩
    obtain ⟨r, V, hV, hVc, hV₀, hV₁⟩ := exists_cover T (isAffineOpen_opensRange t)
      ⟨{t₀}ᶜ, ht₀.isOpen_compl⟩ fun x hx hx' => hx ((show x = t₀ from hx') ▸ h₀)
    let P : Fin (m + 1) ×ₗ Fin (r + 1) → Z.Opens := fun u =>
      q ⁻¹ᵁ B (ofLex u).1 ⊓ p ⁻¹ᵁ V (ofLex u).2
    have hP (u) : IsAffineOpen (P u) := isAffineOpen_prod sq hF (hV _) B hB hBc _
    have hPc : ⨆ u, P u = ⊤ := by
      refine top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hBc.ge (Set.mem_univ (q x)))
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hVc.ge (Set.mem_univ (p x)))
      exact ⟨toLex (i, j), hi, hj⟩
    refine (over_affineOpen sq hF H₀ hV₀.symm B hB hBc).2.2 ?_
    exact acyclic_of_homology_equiv (homology_equiv_over sq hF V hV hVc 0
      (fun R _ t Y π f H₁ ht j hj hy => H R t Y π f H₁ ht fun y e => hV₁ j hj (hy y) e)
      B hB hBc P hP hPc) (hac _ P hP hPc)

end GlobalTheory.ProductAcyclic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCoset
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.ThetaConstVal
open GlobalTheory.TorusExt

theorem le_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (hq : ∀ i, (q : WithTop ℚ) ≤ v (x i)) : (q : WithTop ℚ) ≤ v s := by
  obtain ⟨S, hS⟩ := h q
  have := v.map_le_add (hS S le_rfl) (v.map_le_sum (s := S) (f := x) fun i _ => hq i)
  rwa [sub_add_cancel] at this

theorem eq_zero_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (q0 : 0 < q) (i₀ : Ix) (h₀ : v (x i₀) = 0)
    (hq : ∀ i, i ≠ i₀ → (q : WithTop ℚ) ≤ v (x i)) : v s = 0 := by
  classical
  obtain ⟨S, hS⟩ := h q
  have a := v.map_le_add (hS (insert i₀ S) (Finset.subset_insert _ _))
    (v.map_le_sum (s := (insert i₀ S).erase i₀) (f := x) fun i hi => hq i (Finset.ne_of_mem_erase hi))
  have e : s = x i₀ + (s - ∑ i ∈ insert i₀ S, x i + ∑ i ∈ (insert i₀ S).erase i₀, x i) := by
    rw [← Finset.add_sum_erase _ x (Finset.mem_insert_self i₀ S)]; ring
  have lt : v (x i₀) < v (s - ∑ i ∈ insert i₀ S, x i + ∑ i ∈ (insert i₀ S).erase i₀, x i) := by
    rw [h₀]
    exact lt_of_lt_of_le (by exact_mod_cast q0) a
  rw [e, v.map_add_eq_of_lt_left lt, h₀]

section
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem exists_kap (hM : MulPullSt) [IsNoetherianRing R] (m : ℕ) :
    ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ m) (m ^ 2) 1), Normd κ := by
  obtain ⟨α, hα⟩ := hM _ D.P m
  have o : ∀ f : D.P.A ⟶ D.P.A, f = 𝟙 D.P.A ^ m → (1 : D.P.A ⟶ D.P.A).left ≫ f.left = (1 : D.P.A ⟶ D.P.A).left := by
    rintro _ rfl
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, one_pow]
  obtain ⟨κ, hκ, vκ⟩ := exists_gen D.P.isLB
    (φ' := ![𝟙 _, (𝟙 D.P.A ^ m).left, (1 : D.P.A ⟶ D.P.A).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - (m ^ 2 : ℕ)])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      apply Additive.ofMul.injective
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Category.comp_id,
        Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_zpow, ofMul_one, o _ rfl]
      push_cast
      module)
    (LB.mulGen D.P.L _ _ _ _ α (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ α (1 : D.P.A ⟶ D.P.A).left)))
    (mulGen_isGen _ _ _ _ _ _ _ hα (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hα _)))
  refine ⟨κ, hκ, corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e : eSec D.P.A ≫ (1 : D.P.A ⟶ D.P.A).left = eSec D.P.A := by
    rw [eSec, ← Over.comp_left, MonObj.comp_one, Hom.one_def, toUnit_unit, Category.id_comp]
  rw [val_pull hJ, vκ _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, val_one, Category.id_comp, e, mul_inv_cancel]

theorem exists_frm {F : Type} [Field F] [Algebra (FractionRing R) F] (m : ℕ) (b b' : TF (R := R) F ⟶ D.P.A)
    (hb : b' = b ^ m) (w : Frm D F (m ^ 2) b) (hw : w.IsGen) (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ m) (m ^ 2) 1))
    (hκ : κ.IsGen) : ∃ w' : Frm D F 1 b', w'.IsGen ∧
      ∀ z J, Good D.P.L z J → val w (𝟙 _) z J * val κ b.left z J = val w' (𝟙 _) z J := by
  subst hb
  have o₁ : b.left ≫ (𝟙 D.P.A ^ m).left = (b ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have o₂ : b.left ≫ (1 : D.P.A ⟶ D.P.A).left = (DegPre.zeroF D F).left := by
    rw [← Over.comp_left, MonObj.comp_one]; rfl
  obtain ⟨w', hw', vw⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F (b ^ m)) (ε' := DegPre.lineε 1)
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      apply Additive.ofMul.injective
      simp only [DegPre.lineφ, DegPre.lineε, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Category.comp_id, Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_zpow, ofMul_one, o₁, o₂]
      push_cast
      module)
    (LB.mulGen D.P.L _ _ _ _ w (LB.pullGen D.P.L _ _ κ b.left))
    (mulGen_isGen _ _ _ _ _ _ _ hw (pullGen_isGen _ _ _ _ hκ _))
  refine ⟨w', hw', fun z J hJ => ?_⟩
  rw [vw _ _ z J hJ, val_mul hJ, val_pull hJ, Category.id_comp]

end

attribute [local instance] gtGroup

theorem pow_eq_one_of_nsmul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {M : Type} [Group M] (f : QkPt D F k → M)
    (hf : ∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') (p : QkPt D F k) (hy : p.y = 0) (j : ℕ) (hj : j • p.g = 0) :
    f p ^ j = 1 := by
  have z : ∀ i : ℕ, k • (i • p.g) = iota hB F 0 := fun i => by
    rw [smul_comm, qk_nsmul hB, hy, map_zero, smul_zero]
  let r : ℕ → QkPt D F k := fun i => qkMk hB 0 (i • p.g) (z i)
  have radd : ∀ i i', f (r (i + i')) = f (r i) * f (r i') := fun i i' => by
    rw [← hf _ _ _ (qkAdd_qkAdd hB (r i) (r i'))]
    exact congrArg f (qk_ext (add_zero _).symm (add_smul i i' p.g))
  have r0 : f (r 0) = 1 := mul_eq_left.1 (radd 0 0).symm
  have r1 : r 1 = p := qk_ext hy.symm (one_smul ℕ p.g)
  have rpow : ∀ i, f (r i) = f p ^ i := fun i => by
    induction i with
    | zero => rw [r0, pow_zero]
    | succ i ih => rw [radd, ih, r1, pow_succ]
  rw [← rpow, ← r0]
  exact congrArg f (qk_ext rfl (hj.trans (zero_smul ℕ p.g).symm))

theorem exists_terms : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ (m : ℕ), Odd m → ∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → ThC A ρ m th x t c → ∃ w' : Frm D.toPre F 1 (m • p.g).b, w'.IsGen ∧ SumV v (coef ϑ (m • p.g) w') c ∧ GenV hϖ hv w' ((Q p.y : ℚ) / (m ^ 2 : ℕ)) ∧ GtV hϖ hv (m • p.g) (fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / m) ∧ ∀ χ, (((Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ) : ℚ) : WithTop ℚ) ≤ v (coef ϑ (m • p.g) w' χ) := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP m hm p x t c hx hT
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL V _ hA D F (m ^ 2) hm.pow p).1
  obtain ⟨κ, hκ⟩ := exists_kap D.toPre hL.1.mulPull m
  obtain ⟨w', hw', e⟩ := exists_frm D.toPre m p.g.b (m • p.g).b (nsmul_b m p.g) w hw.1 κ hκ.1
  have hg : GtPtF.IsNsmul m p.g (m • p.g) := (isNsmul_iff_eq _ _ _).2 rfl
  have s := (GlobalTheory.T.thetaConstant_eq_sum_thetaTerms_odd_multiple hL V _ hA D A G hG U F w₀ ρ hN th ϑ hE m hm p x t c hx hT w hw _ hg κ hκ w' hw' e).1
  obtain ⟨a₁, a₂, a₃⟩ := (GlobalTheory.T.valuations_symmetricFrame_and_terms hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv).2 m hm.pos p w hw _ hg κ hκ w' hw' e
  exact ⟨w', hw', (AdicValSum.main V ϖ hϖ F v hv _ _ _ s).1, a₁, a₂, a₃ ϑ hP.1⟩

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ (m : ℕ), Odd m → IsUnit (m : V) → (∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → ThC A ρ m th x t c → (∀ q : ℚ, (∀ χ, q ≤ (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v c) ∧ (v c = 0 → ∃ z, p.y = m • z)) ∧ ∀ n, 2 ≤ n → n ∣ m → ∀ (p : QkPt D.toPre F (m ^ 2)) x, p.y = 0 → QkToAkU U.toUnifPre F (m ^ 2) p x → ∃ (p' : QkPt D.toPre F (m ^ 2)) (x' : _) (t : _) (c : F), p'.y = 0 ∧ QkToAkU U.toUnifPre F (m ^ 2) p' x' ∧ (x' ^ m * (x ^ m)⁻¹) ^ n = 1 ∧ ThC A ρ m th x' t c ∧ v c = 0 := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP m hm hu
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have T := exists_terms hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ hE hP m hm
  have m0 : (0 : ℚ) < (m ^ 2 : ℕ) := by exact_mod_cast pow_pos hm.pos 2
  have q0 : (0 : ℚ) < 1 / (m ^ 2 : ℕ) := one_div_pos.2 m0
  have pos : ∀ χ : D.toPre.X, χ ≠ 0 → (1 : ℚ) / (m ^ 2 : ℕ) ≤ (Q χ : ℚ) / (m ^ 2 : ℕ) := fun χ h =>
    div_le_div_of_nonneg_right (by exact_mod_cast QForm.Q_pos hϖ D hQ h) m0.le
  refine ⟨fun p x t c hx hT => ?_, fun n hn hnm p x hy hx => ?_⟩
  · obtain ⟨w', -, s, -, -, a⟩ := T p x t c hx hT
    have k : ∀ q : ℚ, (∀ χ, q ≤ (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v c := fun q hq =>
      le_of_sumV s fun χ => (WithTop.coe_le_coe.2 (hq χ)).trans (a χ)
    refine ⟨k, fun h0 => by_contra fun hz => ?_⟩
    have := k _ fun χ => pos (m • χ + p.y) fun e => hz ⟨-χ, by rw [smul_neg]; exact eq_neg_of_add_eq_zero_right e⟩
    rw [h0] at this
    exact absurd (by exact_mod_cast this) q0.not_ge
  · have hB := D.tau_bimult
    obtain ⟨d, rfl⟩ := hnm
    obtain ⟨h, o, g₂, ho, hh, hg₂, hv₂⟩ := GlobalTheory.T.exists_nsmul_add_decomp_with_coef_valuation hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv ϑ hP n hn
      (isUnit_of_mul_isUnit_left (by rwa [Nat.cast_mul] at hu)) ((n * d) • p.g) 0
    obtain ⟨h', hh'⟩ := (gt_onto_divisible_kernel hL V _ hA D F).2.1 (n * d) hm.pos h
    rw [isZero_iff_eq] at ho
    rw [isNsmul_iff_eq] at hh hh'
    rw [isAdd_iff_eq] at hg₂
    have z₁ : (n * d * n) • h' = 0 := by rw [_root_.mul_comm (n * d) n, mul_smul, ← hh', ← hh, ho]
    have z₂ : (n * d) ^ 2 • h' = iota hB F 0 := by
      rw [map_zero, show (n * d) ^ 2 = d * (n * d * n) by ring, mul_smul, z₁, smul_zero]
    obtain ⟨f, f₁, -, -, f₄, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F ((n * d) ^ 2) (pow_pos hm.pos 2)
    let r : QkPt D.toPre F ((n * d) ^ 2) := qkMk hB 0 h' z₂
    let p' := qkAdd hB p r
    have y' : p'.y = 0 := (add_zero _).trans hy
    have fp : f p' = x * f r := ((f₁ p x).1 hx).symm ▸ f₄ _ _ _ (qkAdd_qkAdd hB p r)
    have hx' : QkToAkU U.toUnifPre F ((n * d) ^ 2) p' (f p') := (f₁ _ _).2 rfl
    have t' : f p' ^ ((n * d) ^ 2) = 1 := pow_eq_one_of_nsmul hB f f₄ p' y' _ (by rw [qk_nsmul hB, y', map_zero])
    obtain ⟨⟨t, c⟩, hT, -⟩ := GlobalTheory.T.existsUnique_theta_const_of_odd hL V A F ρ hN.2.1 (n * d) hm th (f p') t'
    refine ⟨p', f p', t, c, y', hx', ?_, hT, ?_⟩
    · rw [fp, mul_pow x, mul_inv_cancel_comm, ← pow_mul]
      exact pow_eq_one_of_nsmul hB f f₄ r rfl _ z₁
    · obtain ⟨w', hw', s, a₁, a₂, a⟩ := T p' _ t c hx' hT
      have e : g₂ = (n * d) • p'.g := by
        rw [hg₂, hh']; exact (smul_add _ _ _).symm
      subst e
      refine eq_zero_of_sumV s q0 0 ?_ fun χ hχ => (WithTop.coe_le_coe.2 (pos _ fun e => hχ ?_)).trans (a χ)
      · rw [hv₂ w' _ _ hw' a₂ a₁, y', QForm.Q_zero hϖ D hQ, bOf_zero_left hϖ hQ]
        simp
      · rw [y', add_zero] at e
        by_contra h0
        have b₁ := QForm.Q_pos hϖ D hQ h0
        have b₂ := Q_nsmul hϖ hQ (n * d) χ
        rw [e, QForm.Q_zero hϖ D hQ] at b₂
        have b₃ : (0 : ℤ) < ((n * d : ℕ) : ℤ) ^ 2 := by exact_mod_cast pow_pos hm.pos 2
        exact absurd b₂ (mul_pos b₃ (by omega)).ne

end GlobalTheory.UT.ThetaConstVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionEqOfLaws
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem uTors_of_laws : Laws → Laws2 → Laws3 → Laws4 → Laws5 → GlobalTheory.ZH.UTorsSt := by
  intro h1 h2 h3 h4 h5 V _ _ _ _ hV A G _ _ D U F _ _ _ k hk
  have hB : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  exact GlobalTheory.TorsionIso.torsion_eq ⟨h1, h2, h3, h4, h5⟩ V (maximalIdeal V) hB D A G
    (GlobalTheory.T.isSemiAbelian_of_uniformisation_over_dvr V D A G U.toUnifPre) U F k hk

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairingStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_torsion_identification_with_pairing : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∃ f, Tors U.toUnifPre F k f := by
  first | exact @GlobalTheory.TorsionIso.torsion_eq | exact GlobalTheory.TorsionIso.torsion_eq | (intros; apply GlobalTheory.TorsionIso.torsion_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.LevelCompat

open GlobalTheory.TorusExt
attribute [local instance] gtGroup

noncomputable def qkNsmul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {k : ℕ} (j : ℕ) (p : QkPt D F k) : QkPt D F k :=
  qkMk hB (j • p.y) (j • p.g) (by rw [smul_comm k j, qk_nsmul hB, map_nsmul])

theorem qkAdd_qkNsmul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {k : ℕ} (j : ℕ) (p : QkPt D F k) :
    QkAdd (qkNsmul hB j p) p (qkNsmul hB (j + 1) p) := by
  have e : qkNsmul hB (j + 1) p = qkAdd hB (qkNsmul hB j p) p :=
    qk_ext (succ_nsmul p.y j) (succ_nsmul p.g j)
  rw [e]
  exact qkAdd_qkAdd hB _ _

theorem qkNsmul_one {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {k : ℕ} (p : QkPt D F k) : qkNsmul hB 1 p = p :=
  qk_ext (one_nsmul p.y) (one_nsmul p.g)

theorem qkToAkU_level : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k n N : ℕ), 1 ≤ k → 1 ≤ n → N = k * n → ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N) x, (q.y = n • p.y → q.g = p.g → (QkToAkU U.toUnifPre F k p x ↔ QkToAkU U.toUnifPre F N q x)) ∧ (p.y = q.y → GtPtF.IsNsmul n q.g p.g → QkToAkU U.toUnifPre F N q x → QkToAkU U.toUnifPre F k p (x ^ n)) := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ k n N hk hn hN
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hn
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hI D A G hG U F k hk
  obtain ⟨f', hf', -, -, hadd, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hI D A G hG U F N hN1
  have key : ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N), q.y = n • p.y → q.g = p.g → f p = f' q := by
    intro p q hy hg
    obtain ⟨x₀, h₀⟩ := GlobalTheory.T.exists_inducedTranslation_frobeniusOnSections hL R I hI D A G hG U F k hk p
    have a := (GlobalTheory.UT.indAt_translT_iff hL R I hI D A G hG U F k hk p x₀).1
      (h₀ 1 k le_rfl (Nat.mul_one k).symm p (one_nsmul _).symm rfl)
    have b := (GlobalTheory.UT.indAt_translT_iff hL R I hI D A G hG U F N hN1 q x₀).1 (h₀ n N hn hN q hy hg)
    exact ((hf p x₀).1 a).symm.trans ((hf' q x₀).1 b)
  intro p q x
  refine ⟨fun hy hg => by rw [hf, hf', key p q hy hg], fun hy hg hx => ?_⟩
  have hx' : x = f' q := (hf' q x).1 hx
  have hp : ∀ j : ℕ, f' (qkNsmul D.tau_bimult (j + 1) q) = x ^ (j + 1) := by
    intro j
    induction j with
    | zero => rw [Nat.zero_add, qkNsmul_one, pow_one, hx']
    | succ j ih => rw [hadd _ _ _ (qkAdd_qkNsmul D.tau_bimult (j + 1) q), ih, ← hx', ← pow_succ]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [hf, ← hp j]
  exact (key p _ (by rw [hy]; rfl) ((isNsmul_iff_eq _ _ _).1 hg).symm).symm

end GlobalTheory.LevelCompat
end

