import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtDatumOfTorusCoords
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib
open GlobalTheory.CoordToExt

section
variable {S : Scheme.{0}}

theorem exists_gtDatum_of_units (E : SplitExt S) {G : Over S} [GrpObj G] (q : G ⟶ E.B) (i : splitTorus S E.X ⟶ G)
    (hq : IsMonHom q) (hi : IsMonHom i) (hf : Flat q.left) (hs : Surjective q.left) (ha : IsAffineHom q.left)
    (hk : IsPullback i (toUnit _) q (η[E.B]))
    (s : ∀ (χ : E.X) (a : (E.O χ).L.ι), Γ(G.left, q.left ⁻¹ᵁ (E.O χ).L.U a)ˣ)
    (h₁ : ∀ (χ : E.X) (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (a a' : (E.O χ).L.ι), q.left (r z) ∈ (E.O χ).L.U a →
      q.left (r z) ∈ (E.O χ).L.U a' →
      gm r z _ (s χ a') = gm (r ≫ q.left) z _ ((E.O χ).L.g a a') * gm r z _ (s χ a))
    (h₂ : ∀ (χ : E.X) (a : (E.O χ).L.ι) (Z : Over S) (t : Z ⟶ splitTorus S E.X) (g : Z ⟶ G) (z : Z.left),
      q.left (g.left z) ∈ (E.O χ).L.U a →
      gm ((t ≫ i) * g).left z _ (s χ a) = gm t.left z ⊤ (charUnit S E.X χ) * gm g.left z _ (s χ a))
    (h₃ : ∀ (χ : E.X) (a : (E.O χ).L.ι) (y : (𝟙_ (Over S)).left), q.left (eSec G y) ∈ (E.O χ).L.U a →
      gm (eSec G) y _ (s χ a) * gm (𝟙 _) y _ ((E.O χ).rig.s fun _ => a) = 1) :
    ∃ d : E.GtDatum G, d.q = q ∧ d.i = i := by
  have hact : ∀ {Z : Over S} (t : Z ⟶ splitTorus S E.X) (g : Z ⟶ G) (z : Z.left),
      q.left (((t ≫ i) * g).left z) = q.left (g.left z) := by
    intro Z t g z
    have e : ((t ≫ i) * g) ≫ q = g ≫ q := by
      rw [MonObj.mul_comp, Category.assoc, hk.w, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
    exact congrArg (fun f => f.left z) e
  let u : ∀ (j : E.ChartIdx) (_k : Module.Free.ChooseBasisIndex ℤ E.X), Γ(G.left, q.left ⁻¹ᵁ E.chart j)ˣ :=
    fun j k => res (Scheme.Hom.preimage_mono q.left (E.chart_le j k)) (s _ (j k))
  have hu : ∀ (j : E.ChartIdx) k {Z : Scheme.{0}} (r : Z ⟶ G.left) (z : Z), q.left (r z) ∈ E.chart j →
      gm r z (q.left ⁻¹ᵁ E.chart j) (u j k) = gm r z _ (s _ (j k)) := fun j k Z r z hz => gm_res r z _ hz _
  refine ⟨{
    q := q, i := i, q_hom := hq, i_hom := hi, q_flat := hf, q_surjective := hs, q_affine := ha, isKernel := hk
    u := u
    coord := fun j V hV h => ?_
    trans := fun j j' k => unit_ext fun y hy => ?_
    act_le := fun j y hy => (congrArg (· ∈ E.chart j) (hact (fst _ _) (snd _ _) y)).mpr hy
    equiv := fun j k => unit_ext fun y hy => ?_
    unit_norm := fun j k => unit_ext fun y hy => ?_ }, rfl, rfl⟩
  · refine bijective_of_basis E.basis q i hq hi hf hs ha hk V hV _ fun k Z t g z hz => ?_
    have hz' : q.left (((t ≫ i) * g).left z) ∈ V := by rw [hact]; exact hz
    rw [gm_res _ z (V := q.left ⁻¹ᵁ V) _ hz', gm_res _ z (V := q.left ⁻¹ᵁ V) _ hz, hu j k _ z (h hz'), hu j k _ z (h hz)]
    exact h₂ _ _ Z t g z (E.chart_le j k (h hz))
  · refine ((gm_res _ y _ hy _).trans ((hu j' k _ y hy.2).trans
      (h₁ _ _ (𝟙 _) y (j k) (j' k) (E.chart_le j k hy.1) (E.chart_le j' k hy.2)))).trans (Eq.symm ?_)
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_pull (𝟙 _) q.left y (E.chart j ⊓ E.chart j') hy _).trans
      (gm_res _ y (V := E.chart j ⊓ E.chart j') _ hy _)) ((gm_res _ y _ hy _).trans (hu j k _ y hy.1)))
  · have hy' : q.left (((fst (splitTorus S E.X) G ≫ i) * snd (splitTorus S E.X) G).left y) ∈ E.chart j :=
      (congrArg (· ∈ E.chart j) (hact (fst _ _) (snd _ _) y)).mpr hy
    have e := h₂ _ (j k) _ (fst _ _) (snd _ _) y (E.chart_le j k hy)
    rw [← hu j k _ y hy, ← hu j k _ y hy'] at e
    refine ((gm_res _ y _ hy _).trans ((gm_pull (𝟙 _) ((fst (splitTorus S E.X) G ≫ i) * snd (splitTorus S E.X) G).left y
      (q.left ⁻¹ᵁ E.chart j) hy' _).trans ?_)).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res (𝟙 _) y _ hy _).trans
        (gm_pull (𝟙 _) (fst (splitTorus S E.X) G).left y ⊤ trivial _))
        (gm_pull (𝟙 _) (snd (splitTorus S E.X) G).left y (q.left ⁻¹ᵁ E.chart j) hy _))).symm
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
    exact e
  · refine Eq.trans ?_ ((h₃ _ (j k) y (E.chart_le j k hy.1)).trans (map_one _).symm)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ y _ hy _).trans
      ((gm_pull (𝟙 _) (eSec G) y (q.left ⁻¹ᵁ E.chart j) hy.1 _).trans ?_)) (gm_res _ y _ hy _))
    rw [Category.id_comp]
    exact hu j k _ y hy.1

end

theorem exists_gtDatum_of_gtCoord : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G), ∃ (E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (xe : E.X ≃+ D.X) (d : E.GtDatum (thickObj R I e G)) (π : E.B.left ⟶ D.P.A.left), IsGrpPullback E.B D.P.A (thick R I e) π ∧ d.q.left ≫ π = g.pG.left ∧ (∀ χ, LBIso (E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) ∧ ∀ χ, UFib.GenWt (G := thickObj R I e G) d.i (g.t (xe χ)) χ := by
  intro R _ _ I D e G _ _ g
  have := g.q_hom
  have he : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) :=
    congrArg (fun f => f.left) (IsMonHom.one_hom g.q)
  choose ρ hρ hρ' using fun χ => exists_rig g.q.left _ _ he (bundle I D e χ) (coordUnit g χ) (coordUnit_trans g χ)
  let E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    { B := thickObj R I e D.P.A
      isAbelian := isAbelianScheme_thick I D e
      X := D.X
      O := fun χ => ⟨bundle I D e χ, ρ χ, DVR.linComb_isLB _ D.P.isLB _ _, hρ χ⟩
      addIso := bundle_add I D e
      zeroTriv := bundle_zero I D e
      primitive := bundle_primitive I D e }
  obtain ⟨d, hq, hi⟩ := exists_gtDatum_of_units E g.q g.i g.q_hom g.i_hom g.q_flat g.q_surj g.q_affine g.isKernel
    (coordUnit g) (coordUnit_trans g) (coordUnit_weight g) hρ'
  refine ⟨E, AddEquiv.refl _, d, (D.prBe I e).left, isGrpPullback_pullback D.P.A (thick R I e), ?_, fun χ => ?_,
    fun χ => ?_⟩
  · rw [hq]
    rfl
  · refine exists_iso D.P.isLB (funext fun k => ?_) Oε
    refine Eq.trans ?_ (WeightPf.Oφ_comp (D.prBe I e) (𝟙 _) χ k).symm
    rw [Category.comp_id]
  · rw [hi]
    intro Z t y z J hJ
    have v := TorusCoord.val_t_act g t y χ (𝟙 _) z J hJ
    have c : splitTorusPointsEquiv _ D.X Z t (Multiplicative.ofAdd χ) = pullU t.left ⊤ (charUnit _ D.X χ) :=
      Units.ext (splitTorusPointsEquiv_val _ _ _ t χ)
    have c' := gm_pull (𝟙 _) t.left z ⊤ trivial (charUnit _ D.X χ)
    rw [Category.id_comp] at c'
    rw [Category.id_comp, Category.id_comp, c] at v
    exact v.trans (congrArg (· * _) c')

end GlobalTheory.ZH.UFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsImage
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.AbelianImage

theorem exists_lift {S : Scheme.{0}} {T N G : Over S} [IsReduced T.left] (ν : N ⟶ G)
    [IsClosedImmersion ν.left] (g : T ⟶ G) (h : Set.range g.left ⊆ Set.range ν.left) :
    ∃ l : T ⟶ N, l ≫ ν = g := by
  let Z : TopologicalSpace.Closeds G.left :=
    ⟨Set.range ν.left, ν.left.isClosedEmbedding.isClosed_range⟩
  have h2 : ν.left.ker ≤ g.left.ker :=
    (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1
      (show Z ≤ ν.left.ker.support from ν.left.range_subset_ker_support)).trans
      (ReducedSubgroup.vanishingIdeal_le_ker g.left Z h)
  have h3 := IsClosedImmersion.lift_fac ν.left g.left h2
  refine ⟨Over.homMk (IsClosedImmersion.lift ν.left g.left h2) ?_, ?_⟩
  · rw [← Over.w ν, ← Category.assoc, h3, Over.w]
  · ext1
    exact h3

theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

theorem relDim_le_of_isDominant {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (p : X ⟶ Y) [IsDominant p] (f : Y ⟶ Spec (.of k)) {a b : ℕ}
    (ha : SmoothOfRelativeDimension a (p ≫ f)) (hb : SmoothOfRelativeDimension b f) : b ≤ a := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨A', j', hj', ⟨y, hy⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := p x) (U := ⊤) trivial
  obtain ⟨A, j, hj, ⟨z, hz⟩, hr⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := x) (U := p ⁻¹ᵁ j'.opensRange) ⟨y, hy⟩
  have hrange : Set.range (j ≫ p) ⊆ Set.range j' := by
    rintro _ ⟨t, rfl⟩
    exact hr ⟨t, rfl⟩
  have hl := IsOpenImmersion.lift_fac j' (j ≫ p) hrange
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift j' (j ≫ p) hrange)
  obtain ⟨α, hα⟩ := Spec.map_surjective (j' ≫ f)
  rw [← hφ] at hl
  have : Nonempty (Spec A) := ⟨z⟩
  have : Nonempty (Spec A') := ⟨y⟩
  have : IsIntegral (Spec A) := isIntegral_of_isOpenImmersion j
  have : IsIntegral (Spec A') := isIntegral_of_isOpenImmersion j'
  have : IsDomain A := (affine_isIntegral_iff A).1 inferInstance
  have : IsDomain A' := (affine_isIntegral_iff A').1 inferInstance
  have : IsDominant j := ⟨j.isOpenEmbedding.isOpen_range.dense ⟨_, z, rfl⟩⟩
  have : IsDominant (Spec.map φ ≫ j') := by rw [hl]; infer_instance
  have hd : IsDominant (Spec.map φ) := IsDominant.of_comp_of_isOpenImmersion _ j'
  have hinj : Function.Injective φ.hom := by
    have h1 := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ.hom).1 hd.1
    rw [nilradical_eq_zero] at h1
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h1)
  letI : Algebra k A' := α.hom.toAlgebra
  letI : Algebra k A := (α ≫ φ).hom.toAlgebra
  have h1 := trdeg_eq_of_smoothOfRelativeDimension k Y f b hb A' j' hj' hα.symm
  have h2 := trdeg_eq_of_smoothOfRelativeDimension k X (p ≫ f) a ha A j hj (by
    rw [← Category.assoc, ← hl, Category.assoc, ← hα, ← Spec.map_comp]; rfl)
  have h3 := trdeg_le_of_injective (R := k) (A := A') (A' := A) ⟨φ.hom, fun _ => rfl⟩ hinj
  rw [h1, h2] at h3
  exact_mod_cast h3

section Cat

variable {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] [BraidedCategory 𝒞]

theorem isCommMonObj_of_mono {N G : 𝒞} [MonObj N] [MonObj G] [IsCommMonObj G] (ν : N ⟶ G)
    [Mono ν] [IsMonHom ν] : IsCommMonObj N := by
  refine ⟨?_⟩
  rw [← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm]

omit [BraidedCategory 𝒞] in

theorem isMonHom_of_comp_mono {M N G : 𝒞} [MonObj M] [MonObj N] [MonObj G] (l : M ⟶ N) (ν : N ⟶ G)
    [Mono ν] [IsMonHom ν] [IsMonHom (l ≫ ν)] : IsMonHom l := by
  refine ⟨?_, ?_⟩
  · rw [← cancel_mono ν, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]

end Cat

open RationalPoint in

theorem exists_image : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ ψ : B ⟶ G, IsMonHom ψ → ∃ (B' : Over (Sp k)) (_ : GrpObj B') (ν : B' ⟶ G) (π : B ⟶ B'), IsAbelianScheme B' ∧ IsMonHom ν ∧ IsClosedImmersion ν.left ∧ π ≫ ν = ψ ∧ (∀ F : G ⟶ G, IsMonHom F → (∀ x : (𝟙_ (Over (Sp k)) ⟶ B), ∃ y : (𝟙_ (Over (Sp k)) ⟶ B), x ≫ ψ ≫ F = y ≫ ψ) → ∃ F' : B' ⟶ B', IsMonHom F' ∧ F' ≫ ν = ν ≫ F) ∧ ∀ a, SmoothOfRelativeDimension a B.hom → ∃ a', a' ≤ a ∧ SmoothOfRelativeDimension a' B'.hom := by
  intro k _ _ G _ hG B _ hB ψ hψ
  obtain ⟨hc, hs, hsep, -, -⟩ := hG
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : IsProper (ψ.left ≫ G.hom) := by rw [Over.w ψ]; infer_instance
  have : IsProper ψ.left := IsProper.of_comp ψ.left G.hom
  have hZ : IsClosed (Set.range ψ.left) := ψ.left.isClosedMap.isClosed_range
  let φ : (𝟙_ (Over (Sp k)) ⟶ B) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ ψ) fun x y => MonObj.mul_comp x y ψ
  have hC : ∀ x, x ∈ φ.range ↔ Set.range x.left ⊆ Set.range ψ.left := fun x => by
    rw [range_left_subset_iff, ← Set.image_univ, pt_mem_image_iff ψ isClosed_univ]
    simp only [Set.mem_univ, true_and]
    rfl
  obtain ⟨N, _, ν, hν, hcl, hsm, hr⟩ := ReducedSubgroup.exists_smooth_closed_subgroup k G
    inferInstance φ.range _ hZ hC
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
  have : IsIntegral B.left := isIntegral_of_smooth_field_of_connectedSpace B.hom
  obtain ⟨π, hπ⟩ := exists_lift ν ψ hr.ge
  have : Surjective π.left := ⟨fun y => by
    obtain ⟨x, hx⟩ := hr.le ⟨y, rfl⟩
    refine ⟨x, ν.left.isClosedEmbedding.injective ?_⟩
    rw [← hx, ← hπ]
    rfl⟩
  have : Mono ν := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))
  have : ConnectedSpace N.left := π.left.surjective.connectedSpace π.left.continuous
  have : IsIntegral N.left := isIntegral_of_smooth_field_of_connectedSpace N.hom
  have hw : π.left ≫ N.hom = B.hom := Over.w π
  have : IsSeparated N.hom := by rw [← Over.w ν]; infer_instance
  have : UniversallyClosed (π.left ≫ N.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed N.hom := UniversallyClosed.of_comp_surjective π.left N.hom
  have : GeometricallyConnected (π.left ≫ N.hom) := by rw [hw]; infer_instance
  have hN : IsAbelianScheme N := ⟨isCommMonObj_of_mono ν, hsm, ⟨⟩,
    geometricallyConnected_of_surjective π.left N.hom⟩
  refine ⟨N, inferInstance, ν, π, hN, hν, hcl, hπ, fun F hF h => ?_, fun a ha => ?_⟩
  · have h1 : Set.range (ψ ≫ F).left ⊆ Set.range ψ.left :=
      ReducedSubgroup.range_subset_of_points (ψ ≫ F) hZ fun x => by
        obtain ⟨y, hy⟩ := h x
        exact (hC _).1 ⟨y, hy.symm⟩
    obtain ⟨F', hF'⟩ := exists_lift ν (ν ≫ F) (by
      rintro _ ⟨t, rfl⟩
      obtain ⟨x, hx⟩ := hr.le ⟨t, rfl⟩
      refine hr.ge (h1 ⟨x, ?_⟩)
      change F.left (ψ.left x) = F.left (ν.left t)
      rw [hx])
    have : IsMonHom (F' ≫ ν) := by rw [hF']; infer_instance
    exact ⟨F', isMonHom_of_comp_mono F' ν, hF'⟩
  · obtain ⟨b, hb⟩ := AbelianDim.exists_relDim k N hN
    exact ⟨b, relDim_le_of_isDominant π.left N.hom (hw ▸ ha) hb, hb⟩

end GlobalTheory.AbelianImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeZeroOfLe
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.OpenPart

theorem le_nonzeroLocus_iff {k K : Type} [CommRing k] [Field K] {X : Scheme.{0}} {p : X ⟶ Sp k} {H : LB X}
    {J : Type} [Fintype J] {s : J → H.Sec} {a : J → k} {φ : H.Sec} (hφ : IsLin p s a φ)
    {x : Sp K ⟶ X} {ψ : k →+* K} (hx : x ≫ p = spMap ψ) {v : J → K} (hv : Crd H s x v) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus φ ↔ ∑ j, ψ (a j) * v j ≠ 0 := by
  have h : Crd H (fun _ : Unit => φ) x (fun _ => ∑ j, ψ (a j) * v j) := by
    obtain ⟨l, c, hl, hv⟩ := hv
    refine ⟨l, c, hl, fun _ => ?_⟩
    beta_reduce
    rw [hφ l, CrdCalc.valR_eq x _ hl, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq,
      GlobalTheory.Points.valR_constFn_of_over p ψ x hx _ hl, hv, mul_left_comm]
  exact (CrdCalc.crd_isUnit_iff () h).symm.trans isUnit_iff_ne_zero

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω}

theorem TT_le_TT {z z' : M.Z} (h : S.supI M z' ⊆ S.supI M z) : S.TT M z ≤ S.TT M z' :=
  fun _ ha b hb => ha b (AddSubgroup.closure_mono h hb)

theorem isOpen_supI_subset (z : M.Z) : IsOpen {z' | S.supI M z ⊆ S.supI M z'} := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : {z' | S.supI M z ⊆ S.supI M z'} = ⋂ a ∈ S.supI M z, {z' | M.Div S.th a z'} := by
    ext z'
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [this]
  exact (Set.toFinite _).isOpen_biInter fun a _ => M.isOpen_setOf_div _ _

theorem supI_subset {U₀ : M.Z.Opens} (h : S.Over₀ M U₀) (z : M.Z) {z' : M.Z} (hz' : z' ∈ U₀) :
    S.supI M z ⊆ S.supI M z' := fun a ha => ⟨ha.1, fun j => by
  rw [div_eq_mul_inv]
  exact RatModel.ringOn_le_O hz' (mul_mem (h.le (S.th_mem j)) (h.th_unit a ha.1))⟩

theorem exists_ne_zero_of_le {T T' : AddSubgroup S.Gam} (h : T' ≤ T) (hT : S.IsoFree T) (hT' : S.IsoFree T')
    {K : Type} [Field K] (ψ : o →+* K) (v : S.J → K) {i : S.J} (hi : ∑ j, ψ (S.proj T 0 j i) * v j ≠ 0) :
    ∃ i, ∑ j, ψ (S.proj T' 0 j i) * v j ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply hi
  rw [← GlobalTheory.ThetaBound.proj_mul_proj S T T' h hT.1 hT' 0 0 fun _ => rfl]
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := congrArg (ψ (S.proj T 0 k i) * ·) (hn k)
  simp only [Finset.mul_sum, mul_zero] at this
  rw [← this]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem le_preimage_G_iff : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (K : Type) [Field K] (x : Sp K ⟶ Q.P.left) (z : M.Z) (ψ : o →+* K) (v : S.J → K), Set.range (x ≫ Q.P.hom) = {z} → (IsClosed ({z} : Set M.Z) ∨ z ∈ U₀) → x ≫ Q.P.hom ≫ M.s = spMap ψ → Crd Q.O1 Q.st x v → (⊤ ≤ x ⁻¹ᵁ Q.G ↔ ∃ i, ∑ j, ψ (S.proj (S.TT M z) 0 j i) * v j ≠ 0) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE hB Q K _ x z ψ v hz hc hψ hv
  have hψ' : x ≫ (Q.P.hom ≫ M.s) = spMap ψ := hψ
  have hxz : Q.P.hom (x (IsLocalRing.closedPoint K)) = z := by
    have : (x ≫ Q.P.hom) (IsLocalRing.closedPoint K) ∈ Set.range (x ≫ Q.P.hom) := ⟨_, rfl⟩
    rw [hz] at this
    exact this
  rw [CrdCalc.top_le_iff]
  simp only [Clos.G, TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨z', -, W, hW, i, φ, hφ, h1, h2⟩
    have h1' : z ∈ W := hxz ▸ h1
    exact exists_ne_zero_of_le (TT_le_TT (hW z h1')) (hB.free _).1 (hB.free _).1 ψ v
      ((le_nonzeroLocus_iff hφ hψ' hv).1 ((CrdCalc.top_le_iff x _).2 h2))
  · intro hi
    obtain ⟨z', hz', hs, hs'⟩ : ∃ z' : M.Z, IsClosed ({z'} : Set M.Z) ∧ S.supI M z' ⊆ S.supI M z ∧
        S.supI M z ⊆ S.supI M z' := by
      rcases hc with hc | hc
      · exact ⟨z, hc, le_rfl, le_rfl⟩
      · have := hB.jac
        obtain ⟨z', h1, h2⟩ := nonempty_inter_closedPoints (Z := (U₀ : Set M.Z)) ⟨z, hc⟩
          U₀.isOpen.isLocallyClosed
        exact ⟨z', h2, supI_subset hB.ov _ hc, supI_subset hB.ov _ h1⟩
    obtain ⟨i, hi⟩ := hi
    obtain ⟨i, hi⟩ := exists_ne_zero_of_le (TT_le_TT hs') (hB.free _).1 (hB.free _).1 ψ v hi
    obtain ⟨φ, hφ, -⟩ := GlobalTheory.SecRatio.existsUnique_isLin (Q.P.hom ≫ M.s) Q.st
      (fun j => S.proj (S.TT M z') 0 j i)
    refine ⟨z', hz', ⟨_, isOpen_supI_subset z'⟩, fun _ h => h, i, φ, hφ, ?_,
      (CrdCalc.top_le_iff x _).1 ((le_nonzeroLocus_iff hφ hψ' hv).2 hi)⟩
    change S.supI M z' ⊆ S.supI M (Q.P.hom (x (IsLocalRing.closedPoint K)))
    rw [hxz]
    exact hs

end GlobalTheory.ZH.OpenPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOperators
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaReal

theorem pt_nsmul {G H : Type} [AddCommGroup G] [Group H] (pt : G → H) (h : ∀ a b, pt (a + b) = pt a * pt b) :
    pt 0 = 1 ∧ ∀ (n : ℕ) a, pt (n • a) = pt a ^ n := by
  have h0 : pt 0 = 1 := by
    have := h 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  refine ⟨h0, fun n a => ?_⟩
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

theorem eStd_nsmul (g M r : ℕ) (a b : Fin g ⊕ Fin g → ZMod M) : eStd g M a (r • b) = r • eStd g M a b := by
  simp only [eStd, Finset.smul_sum, Pi.smul_apply, nsmul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem nsmul_self {κ : Type} (M : ℕ) (a : κ → ZMod M) : M • a = 0 := by
  funext i
  simp

theorem exists_operators (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {g m r N : ℕ}
    (hN : N = m ^ 2) (hm : Odd m) (hu : IsUnit ((r * N : ℕ) : Γ(S, ⊤))) (ze : Γ(S, ⊤)ˣ)
    (pt : (Fin g ⊕ Fin g → ZMod (r * N)) → (baseOver S ⟶ P.A)) (hadd : ∀ a b, pt (a + b) = pt a * pt b)
    (hw : ∀ a b, WeilIs P.A P.L (r * N : ℕ) (pt a) (pt b) (ze ^ (r * N * (eStd g (r * N) a b).val)))
    (U : (Fin g ⊕ Fin g → ZMod (r * N)) → ThetaGrp P.A P.L N (baseOver S))
    (hU : ∀ a, SymLift P.A P.L N N (pt (r • a)) (U a))
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver S) P.A).left, (snd (baseOver S) P.A ^ m).left]
      ![(N : ℤ), -1])} (hα : α.IsGen) {th : LB.Sec (LPow P.A P.L 1 (baseOver S))}
    {s₀ : LB.Sec (LPow P.A P.L N (baseOver S))}
    (hs : IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) N 1 α th s₀) :
    ∃ u : (Fin g ⊕ Fin g → ZMod (r * N)) →
        SecM P.A P.L N (baseOver S) →ₗ[Γ((baseOver S).left, ⊤)] SecM P.A P.L N (baseOver S),
      (∀ a s s', IsActOf P.A P.L N (U a) s s' ↔ u a (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧
      (∀ a, r • a = 0 → ∀ v, u a v = v) ∧
      (∀ a b, ∃ e : ℕ, ∀ v, u a (u b v) = (show Γ((baseOver S).left, ⊤) from ze.val ^ e) • u (a + b) v) ∧
      (∀ a b, r • eStd g _ a b = 0 → ∀ v, u a (u b v) = u (a + b) v) ∧
      ∀ a, (r * m) • a = 0 → u a (SecM.ofSec P.A s₀) = SecM.ofSec P.A s₀ := by
  obtain ⟨ρ, hρ, -⟩ := GlobalTheory.thetaGrp_acts_linearly hL.globalFns S P N (baseOver S)
  obtain ⟨h0, hsm⟩ := pt_nsmul pt hadd
  have hodd : Odd N := hN ▸ hm.pow
  have tors : ∀ a, pt (r • a) ^ N = 1 := fun a => by rw [← hsm, smul_smul, mul_comm N r, nsmul_self, h0]
  have act : ∀ a v, IsActOf P.A P.L N (U a) (SecM.toSec P.A v) (SecM.toSec P.A (ρ (U a) v)) := fun a v =>
    (hρ _ _ _).2 rfl
  have weil : ∀ a b, WeilIs P.A P.L N (pt (r • a)) (pt (r • b))
      (ze ^ (r * N * (r • eStd g (r * N) a b).val)) := fun a b => by
    have h₁ := hw a (r • b)
    rw [eStd_nsmul] at h₁
    have h₂ := (hL.weil S P N (baseOver S)).2.2.2 r (pt a) (pt (r • b))
      (ze ^ (r * N * (r • eStd g (r * N) a b).val)) (by rw [mul_comm]; exact hu)
      (by rw [← hsm, mul_comm N r, nsmul_self, h0]) (tors b)
    rw [hsm r a]
    refine h₂.1 ?_
    rw [← Nat.cast_mul, mul_comm N r]
    exact h₁
  have key : ∀ a b v, ρ (U a) (ρ (U b) v) = (show Γ((baseOver S).left, ⊤) from
      ze.val ^ (r * N * (r • eStd g (r * N) a b).val * ((N + 1) / 2))) • ρ (U (a + b)) v := fun a b v => by
    have := act_act hL.globalFns P.isAb P.isLB hodd (tors b) (hU a) (hU b)
      (by rw [← hadd, ← smul_add, add_comm]; exact hU (a + b)) (weil a b) (act b v) (act a _) (act (a + b) v)
    refine this.trans (congrArg (· • _) ?_)
    rw [pow_mul ze.val]
    exact (Units.val_pow_eq_pow_val _ _).trans (congrArg (· ^ _) (Units.val_pow_eq_pow_val _ _))
  refine ⟨fun a => (ρ (U a)).toLinearMap, fun a => hρ _, fun a ha v => ?_, fun a b => ⟨_, key a b⟩,
    fun a b h v => ?_, fun a ha => (hρ _ _ _).1 ?_⟩
  · have h₁ : SymLift P.A P.L N N 1 (U a) := by
      have := hU a
      rwa [ha, h0] at this
    have := act_act hL.globalFns P.isAb P.isLB hodd (one_pow N) h₁ h₁ (by rw [_root_.mul_one]; exact h₁)
      ((hL.weil S P N (baseOver S)).2.2.1 1 (one_pow N)) (act a v) (act a _) (act a v)
    rw [one_pow, Units.val_one, one_smul] at this
    exact (ρ (U a)).injective this
  · refine (key a b v).trans ?_
    rw [h, ZMod.val_zero, mul_zero, zero_mul, pow_zero]
    exact one_smul _ _
  · obtain ⟨ν, hν⟩ := GlobalTheory.exists_gen_negLB hL.globalFns S P 1 (baseOver S)
    exact isActOf_self hL.globalFns P.isAb P.isLB hν hodd hα hs
      (by rw [← hsm, smul_smul, mul_comm m r, ha, h0]) (tors a) (hU a)

end GlobalTheory.ThetaReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOrderActionDescentFieldExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orderAction_descent_field_extension : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oB : D.P.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oB.act a).left) → ∃ oa : D.OAct O, oa.onB = oB := by
  first | exact @GlobalTheory.exists_oAct_of_field_extension | exact GlobalTheory.exists_oAct_of_field_extension | (intros; apply GlobalTheory.exists_oAct_of_field_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPrimitiveScalingStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_primitive_scaling_alt : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G], IsSemiAbelian G → ∀ (M : LB G.left), M.IsLB → ∀ (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (ψ : pullback G.hom (jK V) ⟶ Y) (w : LB.Iso (M.pull (pullback.fst G.hom (jK V))) (L.pull ψ)), w.IsGen → ∀ θ : LB.Sec L, (∃ z, ψ z ∈ nonzeroLocus θ) → ∃ (ϑ : H0 M 1) (c : FractionRing V), c ≠ 0 ∧ (∃ z ∈ nonzeroLocus ϑ, G.hom z = IsLocalRing.closedPoint V) ∧ ∀ x : Sp (FractionRing V) ⟶ pullback G.hom (jK V), x ≫ pullback.snd G.hom (jK V) = 𝟙 _ → ∀ (i : M.ι) (k : L.ι), ⊤ ≤ (x ≫ pullback.fst G.hom (jK V)) ⁻¹ᵁ M.U i → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U k → valR x _ (w.s (fun _ => k, fun _ => i)).val * valR (x ≫ pullback.fst G.hom (jK V)) _ (ϑ.f (fun _ => i)) = c * valR (x ≫ ψ) _ (θ.f k) := by
  first | exact @GlobalTheory.PrimScale.exists_primitive_scaling | exact GlobalTheory.PrimScale.exists_primitive_scaling | (intros; apply GlobalTheory.PrimScale.exists_primitive_scaling <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MaximalMinorsDualThetaTestLatticeBoundStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
theorem _root_.GlobalTheory.T.maximal_minors_dual_thetaTest_lattice_bound : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → ∀ (n : ℕ) (ρ₀ : ℝ) (g : Fin n → S.J → PadicAlgCl p), 0 < ρ₀ → (∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range g) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ ρ₀) → (∀ k : S.J → Fin n, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ ≤ ρ₀ ^ Fintype.card S.J) ∧ ((∃ k : S.J → Fin n, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ = ρ₀ ^ Fintype.card S.J) ↔ S.perp τ.yy.ker = ⊥) := by
  first | exact @GlobalTheory.ZH.minors_dual_testLattice | exact GlobalTheory.ZH.minors_dual_testLattice | (intros; apply GlobalTheory.ZH.minors_dual_testLattice <;> assumption)
end

