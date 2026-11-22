import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0079
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0082
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.Development
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0080

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOutsideFiniteSet
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

noncomputable section

namespace GlobalTheory.CompanionTheory.PointSurjectivity

theorem exists_acyclic_cechLB_fibre : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (F : Set (Sp k ⟶ T)) (hF : F.Finite)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y → y ∉ F → FibAc a (G.pull σ))
    (htot : FibAc (p ≫ a) G) (y₀ : Sp k ⟶ T) (σ₀ : X ⟶ Z) (hy : y₀ ≫ b = 𝟙 _) (h₁ : σ₀ ≫ p = 𝟙 X)
    (h₂ : σ₀ ≫ q = a ≫ y₀), ∃ (m : ℕ) (D : Fin m → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ ∧ (cechLB a (G.pull σ₀) D).Acyclic := by
  intro k _ _ X T Z a b p q H ha _ _ _ G hG F hF hfib htot y₀ σ₀ hy h₁ h₂
  have hsepa : IsSeparated a := inferInstance
  have hsepb : IsSeparated b := inferInstance
  have hX : X.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  have hT' : T.IsSeparated := ⟨by rw [← terminal.comp_from b]; infer_instance⟩
  have hcX : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have hcT : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace b
  have hpp : IsProper p := MorphismProperty.of_isPullback (P := @IsProper) H.flip inferInstance
  have hcZ : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (p ≫ a)
  have hsepZ : IsSeparated (p ≫ a) := inferInstance
  let q₀ : Sp k := IsLocalRing.closedPoint k
  have huniv : ({q₀} : Set (Sp k)) = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim (α := PrimeSpectrum k) _ _
  have hclosed (y : Sp k ⟶ T) (hy : y ≫ b = 𝟙 _) : IsClosed ({y q₀} : Set T) := by
    have : IsClosedImmersion (y ≫ b) := by rw [hy]; infer_instance
    have : IsClosedImmersion y := IsClosedImmersion.of_comp y b
    rw [← Set.image_singleton]
    refine y.isClosedEmbedding.isClosedMap _ ?_
    rw [huniv]
    exact isClosed_univ
  let F₁ : Set T := (fun y : Sp k ⟶ T => y q₀) '' ({y ∈ F | y ≫ b = 𝟙 _} ∪ {y₀})
  have hF₁ : F₁.Finite := (((hF.subset (Set.sep_subset _ _))).union (Set.finite_singleton _)).image _
  have hF₁c : ∀ x ∈ F₁, IsClosed ({x} : Set T) := by
    rintro _ ⟨y, hyF | rfl, rfl⟩
    · exact hclosed y hyF.2
    · exact hclosed _ hy
  obtain ⟨r, V, hV, hVc, hV₁⟩ := GlobalTheory.T.affine_cover_separating_finite_closed_points T F₁ hF₁ hF₁c
  obtain ⟨m', B, hB, hBc, -⟩ := GlobalTheory.T.affine_cover_separating_finite_closed_points X ∅ Set.finite_empty (by simp)
  obtain ⟨d, D, hD, hDc, -⟩ := GlobalTheory.T.affine_cover_separating_finite_closed_points Z ∅ Set.finite_empty (by simp)
  let U : Fin (m' + 1) → Z.Opens := fun i => p ⁻¹ᵁ B i
  let W : Fin (r + 1) → Z.Opens := fun j => q ⁻¹ᵁ V j
  have hT : ∀ n, Limits.IsZero ((cubeComplex (Cube.trunc₂ (secCube (p ≫ a) G
      fun u : Fin (m' + 1) ⊕ₗ Fin (r + 1) => Sum.elim U W (ofLex u)))).homology (n + 2)) := by
    intro n
    obtain ⟨e⟩ := cechLB_homology_equiv_trunc₂ k Z (p ≫ a) G _ D _ U _ W hG hsepZ hD hDc
      (by simp only [U]; rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top])
      (by simp only [W]; rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top])
      (fun i _ h => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hB i) h)
      (fun j _ h => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hV j) h)
      (fun i j => (GlobalTheory.T.affine_cover_of_product_fibres a b p q H (hV j) B hB hBc G hG).1 i) n
    have hz := ((htot _ D hD hDc) n).isZero_homology
    have := ModuleCat.subsingleton_of_isZero hz
    have := e.symm.toEquiv.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  have hA : ∀ t : Finset (Fin (r + 1)), 2 ≤ t.card → (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst (secCube (p ≫ a) G
      fun u : Fin (m' + 1) ⊕ₗ Fin (r + 1) => Sum.elim U W (ofLex u)) t)).Acyclic := by
    intro t ht
    have hne : t.Nonempty := Finset.card_pos.1 (by omega)
    have hVt : IsAffineOpen (⨅ j ∈ t, V j) :=
      IsAffineOpen.biInf _ t.finite_toSet hne fun j _ => hV j
    obtain ⟨-, Y, π, f, E, Hy, hE, hEc, ⟨i₁⟩⟩ := GlobalTheory.T.affine_cover_of_product_fibres a b p q H hVt B hB hBc G hG
    obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ a) G U W t _
      (preimage_biInf V q t)
    obtain ⟨j₁, hj₁, j₂, hj₂, hne'⟩ := Finset.one_lt_card.1 ht
    have hfac := GlobalTheory.T.fibrewise_acyclicity_base_change a b p q H ha G hG Γ(T, ⨅ j ∈ t, V j) hVt.fromSpec Y π f Hy
      (fun s σ hs hσ₁ hσ₂ => hfib (s ≫ hVt.fromSpec) σ (by simpa using hs) hσ₁ hσ₂ (by
        intro hmem
        have hp : hVt.fromSpec (s q₀) ∈ (⨅ j ∈ t, V j : T.Opens) :=
          hVt.range_fromSpec.le ⟨_, rfl⟩
        have hx : (s ≫ hVt.fromSpec) q₀ ∈ F₁ :=
          ⟨_, Or.inl ⟨hmem, by simpa using hs⟩, rfl⟩
        have hp' : (s ≫ hVt.fromSpec) q₀ ∈ (⨅ j ∈ t, V j : T.Opens) := by simpa using hp
        exact hne' (hV₁ _ hx j₁ j₂ (biInf_le V hj₁ hp') (biInf_le V hj₂ hp'))))
    have h := hfac _ E hE hEc
    exact fun n => (GlobalTheory.MumfordCohom.acyclic_cechLB_of_acyclic f _ _ E h n).of_iso (i₁ ≪≫ i₂)
  obtain ⟨j₀, hj₀⟩ : ∃ j, y₀ q₀ ∈ V j := by
    have : y₀ q₀ ∈ (⨆ j, V j : T.Opens) := hVc ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hcol := GlobalTheory.T.cech_slice_acyclic_of_truncation _ hA hT j₀
  obtain ⟨-, Y, π, f, E, Hy, hE, hEc, ⟨i₁⟩⟩ := GlobalTheory.T.affine_cover_of_product_fibres a b p q H (hV j₀) B hB hBc G hG
  obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ a) G U W {j₀} (q ⁻¹ᵁ V j₀)
    (by simp [W])
  have hac₁ : (cechLB (f ≫ (hV j₀).fromSpec ≫ b) (G.pull π) E).Acyclic :=
    fun n => (hcol n).of_iso (i₁ ≪≫ i₂).symm
  have hac : (cechLB f (G.pull π) E).Acyclic :=
    GlobalTheory.MumfordCohom.acyclic_cechLB_of_acyclic _ f _ E hac₁
  have hrange : Set.range y₀ ⊆ Set.range (hV j₀).fromSpec := by
    rw [(hV j₀).range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have : x = q₀ := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [this]
    exact hj₀
  let s : Sp k ⟶ Spec Γ(T, V j₀) := IsOpenImmersion.lift (hV j₀).fromSpec y₀ hrange
  have hs : s ≫ (hV j₀).fromSpec = y₀ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨D', hD', hD'c, hD'a⟩ := GlobalTheory.T.exists_affine_cover_cechLB_fibre_acyclic a b p q H G hG Γ(T, V j₀) (hV j₀).fromSpec Y π f Hy E hE hEc hac
    s σ₀ (by rw [← Category.assoc, hs]; exact hy) h₁ (by rw [hs]; exact h₂)
  exact ⟨m' + 1, D', hD', hD'c, hD'a⟩

end GlobalTheory.CompanionTheory.PointSurjectivity
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GeneratorCompatibilityCompositePullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigGlue

theorem gm_gen_pull {Y X : Scheme.{0}} {L : LB X} {F : Y ⟶ X} {t : LB.Gen (L.pull F)} (ht : t.IsGen) (x : Y)
    (i i' : L.ι) (hi : F x ∈ L.U i) (hi' : F x ∈ L.U i') :
    gm (𝟙 Y) x ((L.pull F).U fun _ => i) (t.s fun _ => i) =
      gm (𝟙 Y ≫ F) x _ (L.g i i') * gm (𝟙 Y) x ((L.pull F).U fun _ => i') (t.s fun _ => i') := by
  have m₁ : (𝟙 Y : Y ⟶ Y) x ∈ (L.pull F).U (fun _ => i) := mem_pull.2 hi
  have m₂ : (𝟙 Y : Y ⟶ Y) x ∈ (L.pull F).U (fun _ => i') := mem_pull.2 hi'
  have hm : (𝟙 Y : Y ⟶ Y) x ∈ (L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i') := ⟨m₁, m₂⟩
  have e := congrArg (gm (𝟙 Y) x _) (ht (fun _ => i) (fun _ => i'))
  rw [map_mul, gm_res (𝟙 Y) x _ hm, gm_res (𝟙 Y) x _ hm, gm_pull_g L F (𝟙 Y) x _ _ m₁ m₂] at e
  exact e

theorem gm_pull_div_g {Z P Q : Scheme.{0}} (g : Z ⟶ P) (f : P ⟶ Q) (M : LB P) (N : LB Q) (x : Z) (i i' : N.ι) (k k' : M.ι)
    (hi : f (g x) ∈ N.U i) (hi' : f (g x) ∈ N.U i') (hk : g x ∈ M.U k) (hk' : g x ∈ M.U k') :
    gm (𝟙 Z) x (((LB.div (N.pull f) M).pull g).U (fun _ => (fun _ => i, k)) ⊓
        ((LB.div (N.pull f) M).pull g).U (fun _ => (fun _ => i', k')))
      (((LB.div (N.pull f) M).pull g).g (fun _ => (fun _ => i, k)) (fun _ => (fun _ => i', k'))) =
      gm (𝟙 Z ≫ g ≫ f) x _ (N.g i i') * (gm (𝟙 Z ≫ g) x _ (M.g k k'))⁻¹ := by
  have m₁ : (𝟙 Z : Z ⟶ Z) x ∈ ((LB.div (N.pull f) M).pull g).U (fun _ => (fun _ => i, k)) :=
    mem_pull.2 ⟨mem_pull.2 hi, hk⟩
  have m₂ : (𝟙 Z : Z ⟶ Z) x ∈ ((LB.div (N.pull f) M).pull g).U (fun _ => (fun _ => i', k')) :=
    mem_pull.2 ⟨mem_pull.2 hi', hk'⟩
  refine (gm_pull_g (LB.div (N.pull f) M) g (𝟙 Z) x _ _ m₁ m₂).trans ?_
  refine (gm_div_g (L := N) (F := f) (L' := M) (𝟙 Z ≫ g) x i i' k k' hi hi' hk hk').trans ?_
  rw [Category.assoc]

theorem lbIso_of_same_descent : ∀ {Z P Q : Scheme.{0}} (g : Z ⟶ P) (f : P ⟶ Q), Flat g → LocallyOfFinitePresentation g → Surjective g →
    ∀ (M : LB P), M.IsLB → ∀ (N : LB Q), N.IsLB → ∀ (τ : LB.Gen (M.pull g)), τ.IsGen →
    ∀ (T : LB.Gen (N.pull (g ≫ f))), T.IsGen →
      (∀ (W : Scheme.{0}) (a b : W ⟶ Z), a ≫ g = b ≫ g → ∀ (w : W) (i : N.ι) (k : M.ι), f (g (a w)) ∈ N.U i → g (a w) ∈ M.U k →
        gm a w ((N.pull (g ≫ f)).U fun _ => i) (T.s fun _ => i) * (gm a w ((M.pull g).U fun _ => k) (τ.s fun _ => k))⁻¹ =
          gm b w ((N.pull (g ≫ f)).U fun _ => i) (T.s fun _ => i) * (gm b w ((M.pull g).U fun _ => k) (τ.s fun _ => k))⁻¹) →
      LBIso M (N.pull f) := by
  intro Z P Q g f hfl hlf hsu M hM N hN τ hτ T hT hinv
  have hD : (LB.div (N.pull f) M).IsLB := LB.isLB_div (pull_isLB hN f) hM
  have mem₁ : ∀ (J : PUnit → (LB.div (N.pull f) M).ι) (x : Z), x ∈ ((LB.div (N.pull f) M).pull g).U J →
      f (g x) ∈ N.U ((J PUnit.unit).1 PUnit.unit) := fun J x hx => mem_pull.1 (mem_pull.1 hx).1
  have mem₂ : ∀ (J : PUnit → (LB.div (N.pull f) M).ι) (x : Z), x ∈ ((LB.div (N.pull f) M).pull g).U J →
      g x ∈ M.U (J PUnit.unit).2 := fun J x hx => (mem_pull.1 hx).2
  have le₁ : ∀ J : PUnit → (LB.div (N.pull f) M).ι, ((LB.div (N.pull f) M).pull g).U J ≤
      (N.pull (g ≫ f)).U (fun _ => (J PUnit.unit).1 PUnit.unit) := fun J x hx => mem_pull.2 (mem₁ J x hx)
  have le₂ : ∀ J : PUnit → (LB.div (N.pull f) M).ι, ((LB.div (N.pull f) M).pull g).U J ≤
      (M.pull g).U (fun _ => (J PUnit.unit).2) := fun J x hx => mem_pull.2 (mem₂ J x hx)
  let ω : LB.Gen ((LB.div (N.pull f) M).pull g) :=
    ⟨fun J => res (le₁ J) (T.s _) * (res (le₂ J) (τ.s _))⁻¹⟩
  have germ : ∀ (W : Scheme.{0}) (a : W ⟶ Z) (w : W) (J : PUnit → (LB.div (N.pull f) M).ι)
      (h : a w ∈ ((LB.div (N.pull f) M).pull g).U J),
      gm a w _ (ω.s J) = gm a w ((N.pull (g ≫ f)).U fun _ => (J PUnit.unit).1 PUnit.unit) (T.s _) *
        (gm a w ((M.pull g).U fun _ => (J PUnit.unit).2) (τ.s _))⁻¹ := by
    intro W a w J h
    show gm a w _ (res (le₁ J) (T.s _) * (res (le₂ J) (τ.s _))⁻¹) = _
    rw [map_mul, map_inv, gm_res a w _ h, gm_res a w _ h]
  have hω : ω.IsGen := by
    have split : ∀ J : PUnit → (LB.div (N.pull f) M).ι, ∃ (i : N.ι) (k : M.ι), J = fun _ => (fun _ => i, k) :=
      fun J => ⟨(J PUnit.unit).1 PUnit.unit, (J PUnit.unit).2, rfl⟩
    intro J J'
    obtain ⟨i, k, rfl⟩ := split J
    obtain ⟨i', k', rfl⟩ := split J'
    apply unit_ext
    intro x hx
    have h₁ := hx.1
    have h₂ := hx.2
    have i₁ : f (g x) ∈ N.U i := mem₁ _ x h₁
    have i₂ : f (g x) ∈ N.U i' := mem₁ _ x h₂
    have k₁ : g x ∈ M.U k := mem₂ _ x h₁
    have k₂ : g x ∈ M.U k' := mem₂ _ x h₂
    have eT := gm_gen_pull hT x i i' i₁ i₂
    have eτ := gm_gen_pull hτ x k k' k₁ k₂
    refine (gm_res (𝟙 Z) x _ hx _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
    refine Eq.trans ?_ (congrArg₂ (· * ·) (gm_pull_div_g g f M N x i i' k k' i₁ i₂ k₁ k₂).symm
      (gm_res (𝟙 Z) x _ hx _).symm)
    refine (germ _ (𝟙 Z) x _ h₁).trans (Eq.trans ?_ (congrArg (_ * ·) (germ _ (𝟙 Z) x _ h₂).symm))
    show gm (𝟙 Z) x _ (T.s fun _ => i) * (gm (𝟙 Z) x _ (τ.s fun _ => k))⁻¹ =
      _ * (gm (𝟙 Z) x _ (T.s fun _ => i') * (gm (𝟙 Z) x _ (τ.s fun _ => k'))⁻¹)
    rw [eT, eτ, mul_inv, _root_.mul_mul_mul_comm]
  refine GlobalTheory.T.line_bundle_trivial_of_descended_generator g hfl hlf hsu _ hD ω hω ?_
  intro W a b hab w i hi
  have hpt : g (a w) = g (b w) := by
    have := congrArg (fun q : W ⟶ P => q w) hab
    simpa using this
  have ha : a w ∈ ((LB.div (N.pull f) M).pull g).U (fun _ => i) := mem_pull.2 hi
  have hb : b w ∈ ((LB.div (N.pull f) M).pull g).U (fun _ => i) := mem_pull.2 (hpt ▸ hi)
  rw [germ W a w _ ha, germ W b w _ hb]
  exact hinv W a b hab w _ _ (mem₁ _ _ ha) (mem₂ _ _ ha)

end GlobalTheory.CompanionTheory.RigGlue
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharOfScalChar
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhFin

open CompanionTheory.RgExh CompanionTheory.RgExh.Fin
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.D.LK (IsKMod LocFin IsMin)

variable {n : ℕ}

theorem hasChar_path (hS : StepChar) (ss : List (Fin n)) :
    ∀ (X : GMod n) (χ : Fin n → ℂ), HasChar X χ → HasChar (path X χ ss) (pathEnd χ ss) := by
  induction ss with
  | nil => intro X χ h; exact h
  | cons s ss ih => intro X χ h; exact ih _ _ (hS n X χ s h)

theorem hasChar_of_scalChar {X : GMod n} {χ : Fin n → ℂ} (h : ScalChar X χ) : HasChar X χ :=
  ⟨1, fun Y => by rw [pow_one, h Y, sub_self]⟩

theorem capelliPoly_eq_of_perm {χ χ₂ : Fin n → ℂ} (τ τ₂ : Equiv.Perm (Fin n)) (h : ∀ a, χ (τ a) = χ₂ (τ₂ a)) :
    Formalism.QuantumDeterminants.capP χ = Formalism.QuantumDeterminants.capP χ₂ := by
  funext Y
  unfold Formalism.QuantumDeterminants.capP
  rw [← Equiv.prod_comp τ (fun s => Y + χ s), ← Equiv.prod_comp τ₂ (fun s => Y + χ₂ s)]
  exact Finset.prod_congr rfl fun a _ => by rw [h a]

def EndOf (ε : Fin n → Bool) (M : GMod n) (χ : Fin n → ℂ) (ss : List (Fin n))
    (d : Equiv.Perm (Fin n) × (Fin n → ℝ)) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (E : Fin n → Fin n → Module.End ℂ V)
    (hE : GlRel E), IsUnitary ε E ∧ LocFin ε E ∧ IsSimple ⟨V, E, hE⟩ ∧ AlgDS ε ⟨V, E, hE⟩ d.1 d.2 ∧
      Iso (path M χ ss) ⟨V, E, hE⟩

theorem iso_of_ends (hH : Hecke) (hI : IsoFacts) (hU : AlgUniq) {ε : Fin n → Bool} {M M' : GMod n}
    {χ : Fin n → ℂ} {ss : List (Fin n)} {d : Equiv.Perm (Fin n) × (Fin n → ℝ)}
    (hg : GoodPath χ ss) (hM : IsSimple M) (hM' : IsSimple M') (hc : HasChar M χ) (hc' : HasChar M' χ)
    (hs : ScalChar (path M χ ss) (pathEnd χ ss)) (e : EndOf ε M χ ss d) (e' : EndOf ε M' χ ss d) :
    Iso M M' := by
  obtain ⟨V, i1, i2, E, hE, u, l, sm, a, iso⟩ := e
  obtain ⟨V', j1, j2, E', hE', u', l', sm', a', iso'⟩ := e'
  have h := hU n ε V V' E E' hE hE' d.1 d.2 u u' l l' sm sm' a a'
  have h1 := (hI n ε (path M χ ss) ⟨V, E, hE⟩ ⟨V', E', hE'⟩).2.2.1 iso h
  have h2 := (hI n ε (path M' χ ss) ⟨V', E', hE'⟩ (path M' χ ss)).2.1 iso'
  have h3 := (hI n ε (path M χ ss) ⟨V', E', hE'⟩ (path M' χ ss)).2.2.1 h1 h2
  exact (hH n M χ ss hg hM hc hs).2.2 M' hM' hc' h3

theorem finish : StartMod → PathFin → PathExists → PathEndNat → SimpleDistinct → ScalarCharacterOfL2Embedding → UnitarizableOfL2Embedding →
    IsoFacts → CharOfAlgDS → AlgUniq → DataUniq → DSOfArr → DSOfData → KModOf → ArrCount → Finish := by
  intro hSM hPF hPE hPN hSD hSc hUn hI hCh hU hDU hDA hDD hKM hAC hS hH hDec hFR n ε H _ _ σ hσ
  obtain ⟨hcpl, hnt, hur, hir, hsq⟩ := id hσ
  haveI := hcpl
  obtain ⟨D, E, hK⟩ := hKM n ε H σ hur hir
  obtain ⟨hsim, ⟨χ, hχ⟩, hiw⟩ := hSM n ε H σ hur hir hnt D E hK
  obtain ⟨B, hB⟩ := hDec n
  obtain ⟨C, δ, hδ, hP⟩ := hPE n χ B
  obtain ⟨N₀, hN₀⟩ := hFR n C δ hδ
  obtain ⟨ss, N, hN, hg, hfar, hall, hgap, hbd⟩ := hP N₀
  have key : ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (D' : Submodule ℂ H')
      (E' : Fin n → Fin n → Module.End ℂ D') (hK' : IsKMod ε σ' D' E'), GlobalTheory.Dec.IsSqIntIrr ε σ' →
      IsSimple ⟨D', E', hK'.gl⟩ → ScalChar ⟨D', E', hK'.gl⟩ χ → IntWt ⟨D', E', hK'.gl⟩ →
      SimplePath χ ss ∧ ScalChar (path ⟨D', E', hK'.gl⟩ χ ss) (pathEnd χ ss) ∧
        ∃ d : Equiv.Perm (Fin n) × (Fin n → ℝ), EndOf ε ⟨D', E', hK'.gl⟩ χ ss d ∧
          Formalism.QuantumDeterminants.IsHCParam d.2 ∧ (∀ a b, a < b → ε (d.1 a) = ε (d.1 b) → d.1 a < d.1 b) ∧
          ∃ τ : Equiv.Perm (Fin n), ∀ a, ((d.2 a : ℝ) : ℂ) = pathEnd χ ss (τ a) := by
    intro H' _ _ _ σ' D' E' hK' hs' hsm' hsc' hiw'
    obtain ⟨_, _, ur, ir, sq⟩ := id hs'
    have hcX := hasChar_of_scalChar hsc'
    have hL := hB ε H' σ' D' E' hK' χ ss ur ir sq hcX hg hfar
    have hce := hasChar_path hS ss _ χ hcX
    have hse := hSc n ε _ _ hL hce
    obtain ⟨sp, sm, -⟩ := hH n _ χ ss hg hsm' hcX hse
    obtain ⟨V, i1, i2, EV, hEV, hun, iso⟩ := hUn n ε _ hL sm
    have facts := hI n ε (path ⟨D', E', hK'.gl⟩ χ ss) ⟨V, EV, hEV⟩ ⟨V, EV, hEV⟩
    have smV : IsSimple ⟨V, EV, hEV⟩ := (facts.2.2.2.1 iso).1 sm
    have scV : ScalChar ⟨V, EV, hEV⟩ (pathEnd χ ss) := (facts.2.2.2.2.1 iso _).1 hse
    have lfV : LocFin ε EV := (facts.2.2.2.2.2.2.1 iso).1 ((hPF n ε _ χ ss).1 hK'.locFin)
    have iwV : IntWt ⟨V, EV, hEV⟩ := (facts.2.2.2.2.2.2.2.1 iso).1 ((hPF n ε _ χ ss).2 hiw')
    obtain ⟨s', mu', hAlg⟩ := hN₀ ε V EV hEV (pathEnd χ ss) N smV.1 hun lfV iwV scV hN hgap hbd
    obtain ⟨τ, hτ⟩ := hCh n ε V EV hEV (pathEnd χ ss) s' mu' hun lfV scV hAlg
    exact ⟨sp, hse, (s', mu'), ⟨V, i1, i2, EV, hEV, hun, lfV, smV, hAlg, iso⟩, hAlg.1, hAlg.2.1, τ, hτ⟩
  obtain ⟨sp, hse, d₀, e₀, hc₀, ho₀, τ₀, hτ₀⟩ := key H σ D E hK hσ hsim hχ hiw
  have hend : ∀ a, pathEnd χ ss a = ((d₀.2 (τ₀.symm a) : ℝ) : ℂ) := fun a => by
    rw [hτ₀, Equiv.apply_symm_apply]
  have hinj' : Function.Injective (pathEnd χ ss) := fun a b h => by
    rw [hend, hend] at h
    exact τ₀.symm.injective (hc₀.1.injective (Complex.ofReal_injective h))
  have hr' : ∀ a, (pathEnd χ ss a).im = 0 ∧ ∃ m : ℤ, (pathEnd χ ss a).re - ((n : ℝ) - 1) / 2 = m := fun a => by
    rw [hend]
    exact ⟨Complex.ofReal_im _, by simpa using hc₀.2 (τ₀.symm a)⟩
  obtain ⟨m, hm, -⟩ := hPN n χ ss
  have hχa : ∀ a, χ a = pathEnd χ ss a - (m a : ℂ) := fun a => by
    rw [hm]; simp
  have hr : ∀ a, (χ a).im = 0 ∧ ∃ m : ℤ, (χ a).re - ((n : ℝ) - 1) / 2 = m := fun a => by
    obtain ⟨h1, k, h2⟩ := hr' a
    refine ⟨by rw [hχa]; simp [h1], k - m a, ?_⟩
    rw [hχa]
    simp only [Complex.sub_re, Complex.natCast_re]
    push_cast
    linarith
  have hinj := hSD n χ ss sp hall
  obtain ⟨A, A', hcard, hA, hA'⟩ := hAC n ε χ (pathEnd χ ss) hinj hinj' hr hr'
  have per : ∀ d : Equiv.Perm (Fin n) × (Fin n → ℝ), ∃ (M : GMod n) (e : Equiv.Perm (Fin n) × (Fin n → ℝ)),
      d ∈ A → e ∈ A' ∧ IsSimple M ∧ HasChar M χ ∧ ScalChar (path M χ ss) (pathEnd χ ss) ∧
        EndOf ε M χ ss e ∧ AlgDS ε M d.1 d.2 ∧ ConeDS ε M d.1 d.2 := by
    intro d
    by_cases hd : d ∈ A
    · obtain ⟨hhc, hord, τ, hτ⟩ := (hA d).1 hd
      obtain ⟨H', i1, i2, i3, σ', hsi, hall'⟩ := hDA n ε d.1 d.2 hhc hord
      obtain ⟨_, hnt', ur', ir', _⟩ := id hsi
      obtain ⟨D', E', hK'⟩ := hKM n ε H' σ' ur' ir'
      obtain ⟨s1, ⟨χd, hχd⟩, iw⟩ := hSM n ε H' σ' ur' ir' hnt' D' E' hK'
      obtain ⟨hAlg, hCone⟩ := hall' D' E' hK'
      obtain ⟨τ', hτ'⟩ := hCh n ε D' E' hK'.gl χd d.1 d.2 hK'.unit hK'.locFin hχd hAlg
      have hcap : Formalism.QuantumDeterminants.capP χd = Formalism.QuantumDeterminants.capP χ :=
        capelliPoly_eq_of_perm τ' τ fun a => by rw [← hτ', ← hτ]
      have hsc : ScalChar ⟨D', E', hK'.gl⟩ χ := fun Y => by rw [hχd Y, hcap]
      obtain ⟨-, hse', e, he, hce, hoe, τe, hτe⟩ := key H' σ' D' E' hK' hsi s1 hsc iw
      exact ⟨⟨D', E', hK'.gl⟩, e, fun _ => ⟨(hA' e).2 ⟨hce, hoe, τe, hτe⟩, s1, hasChar_of_scalChar hsc, hse', he,
        hAlg, hCone⟩⟩
    · exact ⟨triv n, d, fun h => absurd h hd⟩
  haveI : Nonempty (GMod n) := ⟨triv n⟩
  choose! M e hMe using per
  have hmaps : Set.MapsTo e (A : Set _) (A' : Set _) := fun d hd => (hMe d hd).1
  have hinjA : Set.InjOn e (A : Set _) := by
    intro d₁ h₁ d₂ h₂ heq
    obtain ⟨-, s1, c1, p1, n1, a1, k1⟩ := hMe d₁ h₁
    obtain ⟨-, s2, c2, p2, n2, a2, k2⟩ := hMe d₂ h₂
    rw [← heq] at n2
    have hiso := iso_of_ends hH hI hU hg s1 s2 c1 c2 p1 n1 n2
    have a2' : AlgDS ε (M d₁) d₂.1 d₂.2 :=
      ((hI n ε (M d₁) (M d₂) (M d₁)).2.2.2.2.2.2.2.2.1 hiso _ _).2 a2
    obtain ⟨q1, q2⟩ := hDU n ε (M d₁) _ _ _ _ a1 k1 a2'
    exact Prod.ext q1 q2
  have hsurj := Finset.surjOn_of_injOn_of_card_le e hmaps hinjA hcard.symm.le
  obtain ⟨d, hd, hde⟩ := hsurj ((hA' d₀).2 ⟨hc₀, ho₀, τ₀, hτ₀⟩)
  obtain ⟨-, s2, c2, p2, n2, a2, -⟩ := hMe d hd
  rw [hde] at n2
  have hiso := iso_of_ends hH hI hU hg hsim s2 (hasChar_of_scalChar hχ) c2 hse e₀ n2
  have aX : AlgDS ε ⟨D, E, hK.gl⟩ d.1 d.2 :=
    ((hI n ε ⟨D, E, hK.gl⟩ (M d) ⟨D, E, hK.gl⟩).2.2.2.2.2.2.2.2.1 hiso _ _).2 a2
  obtain ⟨hhc, hord, -⟩ := (hA d).1 hd
  exact ⟨d.1, d.2, hhc, hord, hDD n ε H σ D E hK d.1 d.2 hσ aX⟩

end GlobalTheory.CompanionTheory.RgExhFin
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SeesawTrivialityAbelianScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

variable {S : Scheme.{0}} {A X Y : Over S} [GrpObj A]

theorem val_lift_eq_of_comp_eq (hA : IsAbelianScheme A) (q : X ⟶ Y) {N : LB (A ⊗ Y).left} (hN : N.IsLB)
    (r : LB.Gen (ev N (1 : Y ⟶ A) (𝟙 Y)))
    (t : LB.Gen (ev N (fst A X) (snd A X ≫ q))) (ht : t.IsGen)
    (hn : ∀ (Z : Scheme.{0}) (s : Z ⟶ X.left) (z : Z) (J : (Z ⟶ (A ⊗ Y).left) → N.ι), Good N z J →
      val t (s ≫ (lift (1 : X ⟶ A) (𝟙 X)).left) z J = val r (s ≫ q.left) z J)
    {T : Over S} (α : T ⟶ A) (x x' : T ⟶ X) (h : x ≫ q = x' ≫ q)
    (z : T.left) (J : (T.left ⟶ (A ⊗ Y).left) → N.ι) (hJ : Good N z J) :
    val t (lift α x).left z J = val t (lift α x').left z J := by
  have hc : ∀ x₁ : T ⟶ X, lift (fst A T) (snd A T ≫ x₁) ≫ lift (fst A X) (snd A X ≫ q) =
      lift (fst A T) (snd A T ≫ x₁ ≫ q) := fun x₁ => by
    ext <;> simp
  have hc' : (lift (fst A T) (snd A T ≫ x)).left ≫ (lift (fst A X) (snd A X ≫ q)).left =
      (lift (fst A T) (snd A T ≫ x')).left ≫ (lift (fst A X) (snd A X ≫ q)).left := by
    rw [← Over.comp_left, ← Over.comp_left, hc, hc, h]
  have he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hs : ∀ x₁ : T ⟶ X, (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (lift (fst A T) (snd A T ≫ x₁)).left =
      x₁.left ≫ (lift (1 : X ⟶ A) (𝟙 X)).left := fun x₁ => by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    ext <;> simp
  have hv : ∀ x₁ : T ⟶ X, ∀ (y : T.left) (I : (T.left ⟶ (A ⊗ Y).left) → N.ι), Good N y I →
      val (LB.pullGen N _ _ t (lift (fst A T) (snd A T ≫ x₁)).left) (lift (1 : T ⟶ A) (𝟙 T)).left y I =
        val r (x₁ ≫ q).left y I := fun x₁ y I hI => by
    rw [val_pull hI, hs, hn _ _ _ _ hI, Over.comp_left]
  have key := gen_unique' hN (u := LB.pullGen N _ _ t (lift (fst A T) (snd A T ≫ x)).left)
    (u' := LB.pullGen N _ _ t (lift (fst A T) (snd A T ≫ x')).left)
    (fun U _ k => by simp only [hc']) (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left he
    (surj_snd GlobalTheory.globalFns_holds hA T)
    (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _)
    (fun y I hI => by rw [hv x y I hI, hv x' y I hI, h]) T.left (lift α (𝟙 T)).left z J hJ
  have hl : ∀ x₁ : T ⟶ X, (lift α (𝟙 T)).left ≫ (lift (fst A T) (snd A T ≫ x₁)).left = (lift α x₁).left := fun x₁ => by
    rw [← Over.comp_left]
    congr 1
    ext <;> simp
  rw [val_pull hJ, val_pull hJ, hl, hl] at key
  exact key

end GlobalTheory.CompanionTheory.RigDesc

namespace GlobalTheory.CompanionTheory.RigDesc

theorem triv_of_triv_of_flat_cover : ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ q : X ⟶ Y, Flat q.left →
    LocallyOfFinitePresentation q.left → Surjective q.left →
    ∀ N : LB (A ⊗ Y).left, N.IsLB → Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) → Triv (ev N (fst A X) (snd A X ≫ q)) → Triv N := by
  rintro S A X Y _ hA q hfl hlfp hsj N hN ⟨r, hr⟩ ⟨t₀, ht₀⟩
  obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.T.flat_cover_base_change_product S A X Y hA q hfl hlfp hsj
  have he : (lift (1 : X ⟶ A) (𝟙 X)).left ≫ (snd A X).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hef : (lift (1 : X ⟶ A) (𝟙 X)).left ≫ (lift (fst A X) (snd A X ≫ q)).left =
      q.left ≫ (lift (1 : Y ⟶ A) (𝟙 Y)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    ext <;> simp
  obtain ⟨t, ht, hn⟩ := GlobalTheory.T.linear_combination_generator_section_exists hN (fun _ => (lift (fst A X) (snd A X ≫ q)).left) (fun _ => 1)
    (fun _ => q.left ≫ (lift (1 : Y ⟶ A) (𝟙 Y)).left) (fun _ => 1) (snd A X).left (lift (1 : X ⟶ A) (𝟙 X)).left he
    (fun U _ k => by simp only [hef]) t₀ ht₀ (LB.pullGen N _ _ r q.left) (DVR.pullGen_isGen _ _ _ _ hr _)
  refine GlobalTheory.T.line_bundle_trivial_of_descended_generator _ f₁ f₂ f₃ N hN t ht fun W a b hab w i hi => ?_
  have hw : a ≫ (A ⊗ X).hom = b ≫ (A ⊗ X).hom := by
    have e := congrArg (· ≫ (A ⊗ Y).hom) hab
    simpa only [Category.assoc, Over.w] using e
  let T : Over S := Over.mk (a ≫ (A ⊗ X).hom)
  let a' : T ⟶ A ⊗ X := Over.homMk a rfl
  let b' : T ⟶ A ⊗ X := Over.homMk b hw.symm
  have hab' : a' ≫ lift (fst A X) (snd A X ≫ q) = b' ≫ lift (fst A X) (snd A X ≫ q) := by
    exact Over.OverMorphism.ext hab
  have h₁ : a' ≫ fst A X = b' ≫ fst A X := by
    have e := congrArg (· ≫ fst A Y) hab'
    simpa using e
  have h₂ : (a' ≫ snd A X) ≫ q = (b' ≫ snd A X) ≫ q := by
    have e := congrArg (· ≫ snd A Y) hab'
    simpa using e
  obtain ⟨J, hJ, hJi⟩ := exists_good N hN w (K := PUnit.{1}) (fun _ => a ≫ (lift (fst A X) (snd A X ≫ q)).left)
    (fun _ => i) (fun _ _ _ => rfl) (fun _ => hi)
  have hJi' : J (a ≫ (lift (fst A X) (snd A X ≫ q)).left) = i := hJi PUnit.unit
  have key := val_lift_eq_of_comp_eq hA q hN r t ht (fun Z s z I hI => (hn Z s z I hI).trans (val_pull hI _ _ _))
    (a' ≫ fst A X) (a' ≫ snd A X) (b' ≫ snd A X) h₂ w J hJ
  have ea : (lift (a' ≫ fst A X) (a' ≫ snd A X)).left = a := by
    rw [← comp_lift, lift_fst_snd]; simp [a']
  have eb : (lift (a' ≫ fst A X) (b' ≫ snd A X)).left = b := by
    rw [h₁, ← comp_lift, lift_fst_snd]; simp [b']
  rw [ea, eb, val_of t a w J (fun _ => i) (fun _ => hJi'), val_of t b w J (fun _ => i) (fun _ => by rw [← hab]; exact hJi')] at key
  exact key

end GlobalTheory.CompanionTheory.RigDesc
end

