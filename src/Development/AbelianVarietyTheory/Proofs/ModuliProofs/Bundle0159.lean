import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleDescentGaloisCover
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleGlueTwoOpens
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwaySurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleDescentGaloisCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianTriple_descent_galoisCover : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (t : SAB H X) (g : ℕ) (ν : ∀ a, SABMap t t (ρ a)), IsGaloisCover Ga ρ π → IsQProjOver sY → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (ν 1).φ = 𝟙 _ → (∀ a c, (ν (a * c)).φ = (ν a).φ ≫ (ν c).φ) → ∃ (t' : SAB H Y) (m : SABMap t t' π), (∀ a, (ν a).φ ≫ m.φ = m.φ) ∧ IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  first | exact @GlobalTheory.TripleDescent.exists_sab_descent_of_galoisCover | exact GlobalTheory.TripleDescent.exists_sab_descent_of_galoisCover | (intros; apply GlobalTheory.TripleDescent.exists_sab_descent_of_galoisCover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersions
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.TripleGlueMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem nonempty_cast {A B : Scheme.{0}} {t : SAB H A} {t' : SAB H B} {f g : A ⟶ B} (h : f = g)
    (m : SABMap t t' f) : Nonempty (SABMap t t' g) := by
  subst h
  exact ⟨m⟩

theorem exists_transport {A B : Scheme.{0}} (e : A ≅ B) (t : SAB H A) :
    ∃ t' : SAB H B, Nonempty (SABMap t' t e.inv) ∧ Nonempty (SABMap t t' e.hom) := by
  have hp := sabPull Out.CubePf.cubePull e.inv t
  have m := hp.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  obtain ⟨i, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  obtain ⟨i'⟩ := nonempty_cast (by simp) i (g := e.hom ≫ e.inv)
  obtain ⟨k, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m i'
  exact ⟨_, ⟨m⟩, ⟨k⟩⟩

theorem mem_genericPoints_iso {A B : Scheme.{0}} (e : A ≅ B) (x : A) (hx : e.hom x ∈ genericPoints B) :
    x ∈ genericPoints A := by
  have hx' : closure {Scheme.homeoOfIso e x} ∈ irreducibleComponents B := by
    rw [Scheme.coe_homeoOfIso]
    exact hx
  have key := preimage_mem_irreducibleComponents hx' (Scheme.homeoOfIso e).isOpenEmbedding
    ⟨Scheme.homeoOfIso e x, subset_closure rfl, x, rfl⟩
  rw [(Scheme.homeoOfIso e).preimage_closure, ← Set.image_singleton,
    (Scheme.homeoOfIso e).injective.preimage_image] at key
  exact key

theorem generic_transport {A B : Scheme.{0}} (e : A ≅ B) {t : SAB H A} {t' : SAB H B} (m : SABMap t' t e.inv)
    (h : IsReduced A ∧ genericPoints A ⊆ abLocus t.G) : IsReduced B ∧ genericPoints B ⊆ abLocus t'.G := by
  obtain ⟨hr, hg⟩ := h
  refine ⟨@isReduced_of_isOpenImmersion _ _ e.inv _ hr, ?_⟩
  intro y hy
  have hy' : e.inv y ∈ genericPoints A := by
    apply mem_genericPoints_iso e
    have hyy : e.hom (e.inv y) = y := (Scheme.homeoOfIso e).apply_symm_apply y
    rw [hyy]
    exact hy
  have ha := hg hy'
  simp only [abLocus, Set.mem_setOf_eq] at ha ⊢
  intro K _ _ u hu
  have hp : IsProper (pullback.snd t.G.hom (u ≫ e.inv)) := by
    apply ha K (u ≫ e.inv)
    obtain ⟨p, rfl⟩ := hu
    exact ⟨p, rfl⟩
  have sq := (IsPullback.of_hasPullback t'.G.hom u).paste_horiz m.cart.1
  rw [← sq.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback t.G.hom (u ≫ e.inv))]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mpr hp

theorem exists_sab_glue_of_isPullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ X₁ X₂ : Scheme.{0}) (ψ₁ : X₁ ⟶ X) (ψ₂ : X₂ ⟶ X) (φ₁ : X₀ ⟶ X₁) (φ₂ : X₀ ⟶ X₂) (t₀ : SAB H X₀) (t₁ : SAB H X₁) (t₂ : SAB H X₂) (_ : SABMap t₀ t₁ φ₁) (_ : SABMap t₀ t₂ φ₂), IsOpenImmersion ψ₁ → IsOpenImmersion ψ₂ → IsPullback φ₁ φ₂ ψ₁ ψ₂ → (∀ x : X, x ∈ Set.range ψ₁ ∨ x ∈ Set.range ψ₂) → (IsReduced X₁ ∧ genericPoints X₁ ⊆ abLocus t₁.G) → (IsReduced X₂ ∧ genericPoints X₂ ⊆ abLocus t₂.G) → ∃ t : SAB H X, Nonempty (SABMap t₁ t ψ₁) ∧ Nonempty (SABMap t₂ t ψ₂) := by
  intro E _ _ _ H X X₀ X₁ X₂ ψ₁ ψ₂ φ₁ φ₂ t₀ t₁ t₂ m₁ m₂ h₁ h₂ sq hcov g₁ g₂
  obtain ⟨t₁', ⟨a₁⟩, ⟨b₁⟩⟩ := exists_transport ψ₁.isoOpensRange t₁
  obtain ⟨t₂', ⟨a₂⟩, ⟨b₂⟩⟩ := exists_transport ψ₂.isoOpensRange t₂
  have G₁ := generic_transport ψ₁.isoOpensRange a₁ g₁
  have G₂ := generic_transport ψ₂.isoOpensRange a₂ g₂
  have hr : Set.range (pullback.fst ψ₁ ψ₂ ≫ ψ₁) = Set.range (ψ₁.opensRange ⊓ ψ₂.opensRange).ι := by
    rw [IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι]
    simp
  let e₀ : X₀ ≅ (ψ₁.opensRange ⊓ ψ₂.opensRange).toScheme :=
    sq.isoPullback ≪≫ IsOpenImmersion.isoOfRangeEq _ _ hr
  have he₀ : e₀.hom ≫ (ψ₁.opensRange ⊓ ψ₂.opensRange).ι = φ₁ ≫ ψ₁ := by
    simp [e₀]
  obtain ⟨t₀', ⟨a₀⟩, -⟩ := exists_transport e₀ t₀
  obtain ⟨c₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₁ a₀
  obtain ⟨d₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp b₁ c₁
  obtain ⟨c₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₂ a₀
  obtain ⟨d₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp b₂ c₂
  have k₁ : (e₀.inv ≫ φ₁) ≫ ψ₁.isoOpensRange.hom =
      X.homOfLE (inf_le_left : ψ₁.opensRange ⊓ ψ₂.opensRange ≤ ψ₁.opensRange) := by
    rw [← cancel_mono ψ₁.opensRange.ι]
    simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Scheme.homOfLE_ι]
    rw [← he₀, Iso.inv_hom_id_assoc]
  have k₂ : (e₀.inv ≫ φ₂) ≫ ψ₂.isoOpensRange.hom =
      X.homOfLE (inf_le_right : ψ₁.opensRange ⊓ ψ₂.opensRange ≤ ψ₂.opensRange) := by
    rw [← cancel_mono ψ₂.opensRange.ι]
    simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Scheme.homOfLE_ι]
    rw [← sq.w, ← he₀, Iso.inv_hom_id_assoc]
  obtain ⟨M₁⟩ := nonempty_cast k₁ d₁
  obtain ⟨M₂⟩ := nonempty_cast k₂ d₂
  have hUV : ψ₁.opensRange ⊔ ψ₂.opensRange = ⊤ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top, Set.mem_union,
      Scheme.Hom.coe_opensRange, Set.mem_univ, iff_true]
    exact hcov x
  obtain ⟨t, n₁, n₂, -⟩ := GlobalTheory.TripleGlue.exists_sab_glue E H X _ _ t₁' t₂' t₀' M₁ M₂ hUV G₁ G₂
  obtain ⟨p₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₁ b₁
  obtain ⟨p₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₂ b₂
  exact ⟨t, nonempty_cast (Scheme.Hom.isoOpensRange_hom_ι ψ₁) p₁,
    nonempty_cast (Scheme.Hom.isoOpensRange_hom_ι ψ₂) p₂⟩

end GlobalTheory.TripleGlueMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyMorphismFromVeryDenseGraphs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZM.GraphMor

theorem spMap_comp_hom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_chart_two {Y X₁ X₂ : Scheme.{0}} {σ₁ σ₂ : Type} {M₁ : LB X₁} {M₂ : LB X₂} (h₁ : M₁.IsLB) (h₂ : M₂.IsLB)
    (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (a₁ : Y ⟶ X₁) (a₂ : Y ⟶ X₂) (t : Y) :
    ∃ (A : Type) (_ : CommRing A) (y : Sp A ⟶ Y) (_ : IsOpenImmersion y) (v₁ : σ₁ → A) (v₂ : σ₂ → A),
      t ∈ Set.range y ∧ SecCoord M₁ th₁ (y ≫ a₁) v₁ ∧ SecCoord M₂ th₂ (y ≫ a₂) v₂ := by
  obtain ⟨W, hW, j, hj, ht, hc⟩ := RepUniq.exists_affine_secCoord h₁ th₁ a₁ t
  obtain ⟨t', rfl⟩ : t ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact ht
  obtain ⟨W', hW', j', hj', ht', hc'⟩ := RepUniq.exists_affine_secCoord h₂ th₂ (hW.fromSpec ≫ a₂) t'
  obtain ⟨t'', rfl⟩ : t' ∈ Set.range hW'.fromSpec := by rw [hW'.range_fromSpec]; exact ht'
  obtain ⟨β, hβ⟩ := RepUniq.exists_spMap (R := Γ(Y, W)) (A := Γ(Spec Γ(Y, W), W')) hW'.fromSpec
  have hb := Coord.baseChange hc β
  rw [← hβ] at hb
  exact ⟨Γ(Spec Γ(Y, W), W'), inferInstance, hW'.fromSpec ≫ hW.fromSpec,
    (inferInstance : IsOpenImmersion (hW'.fromSpec ≫ hW.fromSpec)), _, _, ⟨t'', rfl⟩, hb, hc'⟩

theorem exists_coord_field {X : Scheme.{0}} {σ : Type} {M : LB X} (h : M.IsLB) (th : σ → M.Sec) {K : Type} [Field K]
    (y : Sp K ⟶ X) : ∃ v, SecCoord M th y v := by
  let t : Sp K := (default : PrimeSpectrum K)
  obtain ⟨j, hj⟩ := LB.mem_of_cover h (y t)
  have hle : (⊤ : (Sp K).Opens) ≤ y ⁻¹ᵁ M.U j := fun t' _ => by
    obtain rfl : t' = t := Subsingleton.elim (α := PrimeSpectrum K) _ _
    exact hj
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((y.appLE _ ⊤ hle).hom ((th i).f j)),
    RepUniq.secCoord_of_frame h ⟨j, hle, 1, isUnit_one, fun i => ?_⟩⟩
  simp [RepUniq.fn]

theorem hom_ext_chart {Y X : Scheme.{0}} (a b : Y ⟶ X)
    (h : ∀ t : Y, ∃ (T : Scheme.{0}) (y : T ⟶ Y) (_ : IsOpenImmersion y), t ∈ Set.range y ∧ y ≫ a = y ≫ b) : a = b := by
  refine Scheme.hom_ext_of_forall _ _ fun t => ?_
  obtain ⟨T, y, _, ht, e⟩ := h t
  refine ⟨y.opensRange, ht, ?_⟩
  rw [← y.isoOpensRange_inv_comp, Category.assoc, Category.assoc, e]

theorem exists_common_field {R K K' : Type} [CommRing R] [Field K] [Field K'] (x : R →+* K) (β : R →+* K')
    (h : RingHom.ker x = RingHom.ker β) :
    ∃ (L : Type) (_ : Field L) (a : K' →+* L) (b : K →+* L), spMap a ≫ spMap β = spMap b ≫ spMap x := by
  let t : Sp K := (default : PrimeSpectrum K)
  let t' : Sp K' := (default : PrimeSpectrum K')
  have e : spMap β t' = spMap x t := PrimeSpectrum.ext (by
    rw [VeryDenseFibres.spMap_apply_asIdeal, VeryDenseFibres.spMap_apply_asIdeal, h])
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := spMap β) (g := spMap x) t' t e
  let L : Type := (pullback (spMap β) (spMap x)).residueField z
  obtain ⟨a, ha⟩ := RepUniq.exists_spMap (R := K') (A := L)
    ((pullback (spMap β) (spMap x)).fromSpecResidueField z ≫ pullback.fst _ _)
  obtain ⟨b, hb⟩ := RepUniq.exists_spMap (R := K) (A := L)
    ((pullback (spMap β) (spMap x)).fromSpecResidueField z ≫ pullback.snd _ _)
  refine ⟨L, inferInstance, a, b, ?_⟩
  rw [← ha, ← hb, Category.assoc, Category.assoc, pullback.condition]

theorem smooth_of_veryDense {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) [IsProper s] [Flat s]
    [LocallyOfFinitePresentation s] {P : Set (Ideal R)} (hP : VeryDense P)
    (h : ∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ Smooth (pullback.snd s (spMap x))) :
    Smooth s := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  refine VeryDenseFibres.eq_top_of_forall_mem s P (fun q hq => ?_) _ fun z hz => ?_
  · obtain ⟨p, h1, h2, h3, -⟩ := hP q 1 hq ((Ideal.ne_top_iff_one _).1 hq.ne_top)
    exact ⟨p, h1, h2, h3⟩
  · obtain ⟨K, _, x, hx, hs⟩ := h _ hz
    let w : Sp K := (default : PrimeSpectrum K)
    have hw : s z = spMap x w := PrimeSpectrum.ext (by rw [VeryDenseFibres.spMap_apply_asIdeal, hx])
    refine VeryDenseFibres.mem_smoothLocus_of_smooth_fiber s z ?_
    rw [hw]
    exact VeryDenseFibres.smooth_fiber_of_smooth_fiber s (spMap x) w
      (inferInstanceAs (Smooth (pullback.snd (pullback.snd s (spMap x)) ((Sp K).fromSpecResidueField w))))

theorem dense_of_veryDense {R : Type} [CommRing R] {P : Set (Ideal R)} (hP : VeryDense P) :
    Dense {q : Sp R | q.asIdeal ∈ P} := by
  refine (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).dense_iff.2 ?_
  rintro _ ⟨f, rfl⟩ ⟨q, hq⟩
  obtain ⟨p, h1, h2, -, h4⟩ := hP q.asIdeal f q.isPrime hq
  exact ⟨⟨p, h2⟩, h4, h1⟩

theorem exists_pair {S Y : Scheme.{0}} (Z₁ Z₂ : Over S) (a₁ : Y ⟶ Z₁.left) (a₂ : Y ⟶ Z₂.left)
    (h : a₁ ≫ Z₁.hom = a₂ ≫ Z₂.hom) :
    ∃ c : Y ⟶ (Z₁ ⊗ Z₂).left, c ≫ (fst Z₁ Z₂).left = a₁ ∧ c ≫ (snd Z₁ Z₂).left = a₂ :=
  ⟨pullback.lift a₁ a₂ h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem mem_of_components {R σ : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {F : MvPolynomial σ R}
    (h : ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) : F ∈ I := by
  rw [← MvPolynomial.sum_homogeneousComponent F]
  exact Ideal.sum_mem _ fun e _ => h e

theorem eval_eq_zero_of_mem_idealOf {R σ : Type} [CommRing R] {Y : Scheme.{0}} {s : Y ⟶ Sp R} {M : LB Y}
    {th : σ → M.Sec} {F : MvPolynomial σ R} (hF : F ∈ idealOf s M th (𝟙 Y)) {T : Type} [CommRing T] {β : R →+* T}
    {y : Sp T ⟶ Y} {v : σ → T} (hy : y ≫ s = spMap β) (hv : SecCoord M th y v) : MvPolynomial.eval₂ β v F = 0 := by
  simp only [idealOf, Ideal.mem_iInf] at hF
  exact hF T inferInstance β y v ⟨hy, by rwa [Category.comp_id]⟩

theorem exists_hom_of_graphs : ∀ (R σ₁ σ₂ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ₁] [Finite σ₂] [Finite Hh] (Z₁ Z₂ : Over (Sp R)) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (p₁ : Hh → σ₁ → R) (p₂ : Hh → σ₂ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z₁.hom (spMap x) ⟶ Z₂.left) → Prop), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsProper Z₁.hom → IsProper Z₂.hom → Smooth Z₁.hom → (∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → f ≫ Z₂.hom = pullback.snd _ _ ≫ spMap x ∧ CutBy (graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ f) Q d (fun h i => x (p₁ h i.1 * p₂ h i.2))) → VeryDense {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (f : _), RingHom.ker x = q ∧ G K x f} → ∃ F : Z₁ ⟶ Z₂, ∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → f = pullback.fst _ _ ≫ F.left := by
  intro R σ₁ σ₂ Hh _ _ _ _ _ _ Z₁ Z₂ I₁ I₂ M₁ M₂ th₁ th₂ p₁ p₂ Q d G h₁ h₂ hp₁ hp₂ hsm hG hP
  obtain ⟨Γ', M, th, hΓ, -, hflat, hlfp, hfib⟩ := GlobalTheory.T.exists_flat_projective_through_points_goodFibres R (σ₁ × σ₂) Hh
    (fun h i => p₁ h i.1 * p₂ h i.2) Q d
    (fun K _ x I => ∃ f, G K x f ∧
      I = graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ f)
    (by
      rintro K _ x _ ⟨f, hf, rfl⟩
      exact ⟨ideals_homogeneous.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.1 h₂.1, (hG K x f hf).2⟩)
    (fun q r hq hr => by
      obtain ⟨p, ⟨K, _, x, f, hx, hf⟩, hp⟩ := hP q r hq hr
      exact ⟨p, ⟨K, _, x, _, hx, f, hf, rfl⟩, hp⟩)
  have hpr : IsProper Γ'.hom := (projRep_projective_ample R _ _ Γ' M th hΓ).2.1

  have good : ∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → ∃ φ : pullback Z₁.hom (spMap x) ⟶ Γ'.left,
      IsPullback φ (pullback.snd _ _) Γ'.hom (spMap x) ∧
      ∀ (T : Type) [CommRing T] (y : Sp T ⟶ pullback Z₁.hom (spMap x)) (v₁ : σ₁ → T) (v₂ : σ₂ → T),
        SecCoord M₁ th₁ (y ≫ pullback.fst _ _) v₁ → SecCoord M₂ th₂ (y ≫ f) v₂ →
        SecCoord M th (y ≫ φ) (fun i => v₁ i.1 * v₂ i.2) := by
    intro K _ x f hf
    obtain ⟨N, ty, hN, hc⟩ := GlobalTheory.T.projRep_graph_segre_coordinates_fibre R K σ₁ σ₂ x I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ _ (pullback.snd _ _)
      (pullback.fst _ _) f h₁ h₂ (IsPullback.of_hasPullback _ _) (hG K x f hf).1
    obtain ⟨φ, hφ, -, hφc⟩ := hfib K x _ _ _ N ty ⟨f, hf, rfl⟩ hN
    exact ⟨φ, hφ, fun T _ y v₁ v₂ e₁ e₂ => (hφc T y _).1 (hc T y v₁ v₂ e₁ e₂)⟩
  have hsmΓ : Smooth Γ'.hom := smooth_of_veryDense Γ'.hom hP (by
    rintro _ ⟨K, _, x, f, rfl, hf⟩
    obtain ⟨φ, hφ, -⟩ := good K x f hf
    refine ⟨K, _, x, rfl, ?_⟩
    rw [← hφ.isoPullback_inv_snd]
    infer_instance)
  have hred : IsReduced Γ'.left := GlobalTheory.isReduced_of_smooth_of_isReduced Γ'.hom
  obtain ⟨I₃, M₃, th₃, h₃', hseg⟩ := SegreCoord.segre_coordinates R σ₁ σ₂ I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ h₁ h₂
  have h₃ := ideals_homogeneous.2.2 R _ _ _ _ _ _ h₃'
  have w₁ : (fst Z₁ Z₂).left ≫ Z₁.hom = (Z₁ ⊗ Z₂).hom := Over.w _
  have w₂ : (snd Z₁ Z₂).left ≫ Z₂.hom = (Z₁ ⊗ Z₂).hom := Over.w _

  have hle : idealOf (Z₁ ⊗ Z₂).hom M₃ th₃ (𝟙 _) ≤ idealOf Γ'.hom M th (𝟙 _) := fun F hF => by
    refine mem_of_components fun e => ?_
    refine DenseFib.mem_idealOf_of_dense R _ _ _ M th _ _ e hred hflat hlfp hΓ.1 (dense_of_veryDense hP)
      (MvPolynomial.homogeneousComponent_isHomogeneous e F) ?_
    intro K' _ _ β y v hy hβ hv
    have hF' := ideals_homogeneous.1 R _ _ _ _ _ _ _ h₃.1 F hF e
    obtain ⟨K, _, x, f, hx, hf⟩ := hβ ⟨(default : PrimeSpectrum K'), rfl⟩
    rw [VeryDenseFibres.spMap_apply_asIdeal] at hx
    obtain ⟨L, _, a, b, hab⟩ := exists_common_field x β hx
    obtain ⟨φ, hφ, hc⟩ := good K x f hf
    have hw : (spMap a ≫ y) ≫ Γ'.hom = spMap b ≫ spMap x := by rw [Category.assoc, hy, hab]
    let z := hφ.lift _ _ hw
    obtain ⟨v₁, hv₁⟩ := exists_coord_field h₁.1 th₁ (z ≫ pullback.fst _ _)
    obtain ⟨v₂, hv₂⟩ := exists_coord_field h₂.1 th₂ (z ≫ f)
    have hz := hc L z v₁ v₂ hv₁ hv₂
    rw [hφ.lift_fst] at hz
    obtain ⟨u, hu⟩ := Coord.unique hΓ.1 hz (Coord.baseChange hv a)
    obtain ⟨c, g₁, g₂⟩ := exists_pair Z₁ Z₂ (pullback.fst _ _) f (pullback.condition.trans (hG K x f hf).1.symm)
    have hs := Coord.scale (hseg L (z ≫ c) v₁ v₂ (by rwa [Category.assoc, g₁]) (by rwa [Category.assoc, g₂])) u
    have hb : (z ≫ c) ≫ (Z₁ ⊗ Z₂).hom = spMap (a.comp β) := by
      rw [spMap_comp_hom, hab, ← w₁, Category.assoc, reassoc_of% g₁, pullback.condition, hφ.lift_snd_assoc]
    have h0 := eval_eq_zero_of_mem_idealOf hF' hb hs
    apply a.injective
    rw [map_zero, MvPolynomial.eval₂_comp_left, ← h0]
    congr 1
    exact funext hu
  obtain ⟨g, hg, -, hgc, -⟩ := RepMap.exists_map_of_coord R _ _ _ _ _ Γ'.hom M₃ M th₃ th h₃ hΓ.1
    (fun T _ β y v hy hv => ⟨(hΓ.2.1 T β y v hy hv).1, fun F hF => eval_eq_zero_of_mem_idealOf (hle hF) hy hv⟩)
  have fib : ∀ (K : Type) [Field K] (x : R →+* K) f, G K x f → ∃ φ : pullback Z₁.hom (spMap x) ⟶ Γ'.left,
      IsPullback φ (pullback.snd _ _) Γ'.hom (spMap x) ∧ φ ≫ g ≫ (fst Z₁ Z₂).left = pullback.fst _ _ ∧
      φ ≫ g ≫ (snd Z₁ Z₂).left = f := by
    intro K _ x f hf
    obtain ⟨φ, hφ, hc⟩ := good K x f hf
    obtain ⟨c, g₁, g₂⟩ := exists_pair Z₁ Z₂ (pullback.fst _ _) f (pullback.condition.trans (hG K x f hf).1.symm)
    have e : φ ≫ g = c := hom_ext_chart _ _ fun t => by
      obtain ⟨A, _, y, hy, v₁, v₂, ht, hv₁, hv₂⟩ := exists_chart_two h₁.1 h₂.1 th₁ th₂ (pullback.fst _ _) f t
      refine ⟨_, y, hy, ht, ?_⟩
      have c₁ := (hgc A _ _).1 (hc A y v₁ v₂ hv₁ hv₂)
      have c₂ := hseg A (y ≫ c) v₁ v₂ (by rwa [Category.assoc, g₁]) (by rwa [Category.assoc, g₂])
      obtain ⟨β, hβ⟩ := RepUniq.exists_spMap ((y ≫ c) ≫ (Z₁ ⊗ Z₂).hom)
      obtain ⟨k₁, k₂⟩ := h₃.2.1 A β _ _ hβ c₂
      rw [← Category.assoc]
      refine (h₃.2.2 A β _ k₁ k₂).unique ⟨?_, c₁⟩ ⟨hβ, c₂⟩
      rw [← hβ, Category.assoc, hg, Category.assoc, hφ.w, Category.assoc, ← w₁, reassoc_of% g₁, pullback.condition]
    exact ⟨φ, hφ, by rw [reassoc_of% e, g₁], by rw [reassoc_of% e, g₂]⟩
  have hπ : (g ≫ (fst Z₁ Z₂).left) ≫ Z₁.hom = Γ'.hom := by rw [Category.assoc, w₁, hg]
  have hππ : IsProper ((g ≫ (fst Z₁ Z₂).left) ≫ Z₁.hom) := hπ ▸ hpr
  have hiso : IsIso (g ≫ (fst Z₁ Z₂).left) := DenseFibreIso.main R _ _ Z₁.hom _ _ hP hp₁ inferInstance
    (IsProper.of_comp _ Z₁.hom) (hπ ▸ hflat) (by
      rintro _ ⟨K, _, x, f, rfl, hf⟩
      obtain ⟨φ, hφ, e₁, -⟩ := fib K x f hf
      refine ⟨K, _, x, rfl, ?_⟩
      have hq : IsPullback φ (𝟙 _) (g ≫ (fst Z₁ Z₂).left) (pullback.fst Z₁.hom (spMap x)) :=
        IsPullback.of_bot (by rwa [Category.id_comp, hπ]) (by rw [e₁, Category.id_comp])
          (IsPullback.of_hasPullback Z₁.hom (spMap x))
      rw [← hq.isoPullback_inv_snd]
      infer_instance)
  refine ⟨Over.homMk (inv (g ≫ (fst Z₁ Z₂).left) ≫ g ≫ (snd Z₁ Z₂).left) ?_, fun K _ x f hf => ?_⟩
  · rw [Category.assoc, Category.assoc, w₂, hg, ← hπ, IsIso.inv_hom_id_assoc]
  · obtain ⟨φ, -, e₁, e₂⟩ := fib K x f hf
    change f = pullback.fst _ _ ≫ inv (g ≫ (fst Z₁ Z₂).left) ≫ g ≫ (snd Z₁ Z₂).left
    rw [← e₁, Category.assoc, IsIso.hom_inv_id_assoc, e₂]

end GlobalTheory.ZM.GraphMor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeometricallyConnectedAwayOfFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ConnSpread

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw ReciprocityTheory.ChartRestriction.G.Out

theorem preconnectedSpace_of_functions (Y : Scheme.{0})
    (H : ∀ s : Γ(Y, ⊤), Y.basicOpen s = ⊥ ∨ Y.basicOpen s = ⊤) : PreconnectedSpace Y := by
  refine ⟨fun U W hU hW hc ⟨u, _, hu⟩ ⟨w, _, hw⟩ => ?_⟩
  by_contra hne
  let O : Bool → Y.Opens := fun i => bif i then ⟨U, hU⟩ else ⟨W, hW⟩
  have hd : O true ⊓ O false = ⊥ := le_bot_iff.1 fun y hy => hne ⟨y, trivial, hy⟩
  have hcov : ⨆ i, O i = ⊤ := top_unique fun y _ => by
    rcases hc (Set.mem_univ y) with h | h
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨true, h⟩
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨false, h⟩
  obtain ⟨s, hs⟩ := TLinPf.glue O hcov (fun i => bif i then 1 else 0) (fun i j => by
    have sub : ∀ T : Y.Opens, T = ⊥ → Subsingleton Γ(Y, T) := fun T hT => by
      subst hT; infer_instance
    cases i <;> cases j
    · exact (map_zero _).trans (map_zero _).symm
    · exact (sub _ ((inf_comm _ _).trans hd)).elim _ _
    · exact (sub _ hd).elim _ _
    · exact (map_one _).trans (map_one _).symm)
  rcases H s with h | h
  · have h₁ : u ∈ Y.basicOpen s := (mem_basicOpen_rs (le_top : O true ≤ ⊤) s hu).1 (by
      rw [show rs Y (le_top : O true ≤ ⊤) s = 1 from hs true]
      exact mem_of_isUnit isUnit_one hu)
    rw [h] at h₁
    exact h₁
  · have h₁ := (mem_basicOpen_rs (le_top : O false ≤ ⊤) s hw).2 (h.ge (Set.mem_univ w))
    rw [show rs Y (le_top : O false ≤ ⊤) s = 0 from hs false, Scheme.basicOpen_zero] at h₁
    exact h₁

variable {X X' : Scheme.{0}}

def fnSec (π : X' ⟶ X) (s : Γ(X', ⊤)) : LB.Sec ((Inh.trivLB X).pull π) where
  f := fun _ => rs X' le_top s
  compat := fun i j => by
    rw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]
    exact (rs_rs _ _ s).trans (rs_rs _ _ s).symm

theorem triv_pull (π : X' ⟶ X) : Triv ((Inh.trivLB X).pull π) :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    erw [Inh.linComb_triv_g, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm⟩

theorem preconnectedSpace_of_line {R F : Type} [CommRing R] [Field F]
    {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (Inh.trivLB X)) {g : R →+* F} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of F)} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (v : Fin P.a → F) (hv : ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : F, w = c • v) :
    PreconnectedSpace X' := by
  obtain ⟨E, hE⟩ := P.sec F g X' π f' h
  have key : ∀ s : Γ(X', ⊤), ∃ c : F, ∀ i,
      rs X' (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s = AbLaw.cst f' _ c * loc P π f' v i := fun s => by
    obtain ⟨w, hw⟩ := E.surjective (fnSec π s)
    obtain ⟨c, hc⟩ := hv w.1 w.2
    refine ⟨c, fun i => ?_⟩
    have e := hE w i
    rw [hw] at e
    refine ((rs_rs _ _ s).symm.trans e).trans ?_
    rw [← loc_smul, ← hc]
    rfl
  obtain ⟨c₁, h₁⟩ := key 1
  have hu : ∀ i, IsUnit (loc P π f' v i) := fun i =>
    isUnit_of_mul_isUnit_right (by rw [← h₁ i, map_one]; exact isUnit_one)
  refine preconnectedSpace_of_functions X' fun s => ?_
  obtain ⟨c, hc⟩ := key s
  by_cases h0 : c = 0
  · refine Or.inl (le_bot_iff.1 fun y hy => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    have := (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).2 hy
    rwa [hc, h0, map_zero, zero_mul, Scheme.basicOpen_zero] at this
  · refine Or.inr (top_unique fun y _ => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    refine (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).1 ?_
    rw [hc]
    exact mem_of_isUnit (((IsUnit.mk0 c h0).map _).mul (hu i)) hi

theorem exists_geometricallyConnected_away_of_fibre : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (K : Type) [Field K] (x : R →+* K), IsProjOver s → Smooth s → GeometricallyConnected (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ GeometricallyConnected (pullback.snd s (spMap (algebraMap R (Localization.Away f)))) := by
  intro R _ _ Z s K _ x hp hs hc
  have hp' : IsProjBy s := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver s).2 hp
  obtain ⟨P⟩ := nonempty_perf_of_smooth_isProjBy R Z s hs hp' _ (Inh.trivLB_isLB _)
  have hpr : IsProper s := isProper_of_isProjBy R Z s hp'
  have h₀ : IsPullback (pullback.fst s (spMap x)) (pullback.snd s (spMap x)) s
      (Spec.map (CommRingCat.ofHom x)) := IsPullback.of_hasPullback _ _
  have hbij := bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected K _
    (pullback.snd s (spMap x)) inferInstance inferInstance hc
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀, -⟩ := (pullback.snd s (spMap x)).surjective (⊥ : PrimeSpectrum K)
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst s (spMap x)) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul K (0 : Fin P.a → K), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector x P.D₀ v hv0 (hline hbij.2)
  let p : PrimeSpectrum R := s ((pullback.fst s (spMap x)) x₀)
  have hpx : ∀ a : R, a ∉ p.asIdeal → x a ≠ 0 := fun a ha h0 => by
    have e : p = Spec.map (CommRingCat.ofHom x) (pullback.snd s (spMap x) x₀) :=
      congrArg (fun t => t x₀) h₀.w
    apply ha
    rw [e]
    change x a ∈ (pullback.snd s (spMap x) x₀).asIdeal
    rw [h0]
    exact zero_mem _
  obtain ⟨_, ⟨ε, rfl⟩, hε, hεs⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ (Set.range s : Set (PrimeSpectrum R)) from ⟨_, rfl⟩) s.isOpenMap.isOpen_range
  refine ⟨δ * ε, by rw [map_mul]; exact mul_ne_zero hδ (hpx ε hε), ?_⟩
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Y fst snd h => ?_⟩
  let g : R →+* F := (algebraMap (Localization.Away (δ * ε)) F).comp (algebraMap R _)
  have hg : IsUnit (g δ * g ε) := by
    rw [← map_mul]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (δ * ε)) (δ * ε)).map
      (algebraMap (Localization.Away (δ * ε)) F)
  have h' : IsPullback (fst ≫ pullback.fst s (spMap (algebraMap R (Localization.Away (δ * ε))))) snd s
      (Spec.map (CommRingCat.ofHom g)) := by
    have := h.paste_horiz (IsPullback.of_hasPullback s _)
    rwa [← Spec.map_comp] at this
  have hmem : Spec.map (CommRingCat.ofHom g) (⊥ : PrimeSpectrum F) ∈ Set.range s :=
    hεs fun h0 : g ε ∈ (⊥ : Ideal F) => (isUnit_of_mul_isUnit_right hg).ne_zero h0
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨y, -⟩ := Scheme.exists_preimage_of_isPullback h' z _ hz
  have := preconnectedSpace_of_line P h' _ (hker F _ (isUnit_of_mul_isUnit_left hg))
  exact ⟨⟨y⟩⟩

end GlobalTheory.ConnSpread
end
end

