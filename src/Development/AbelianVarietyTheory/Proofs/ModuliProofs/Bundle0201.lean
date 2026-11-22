import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0198
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0160
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0199
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0197
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LiftOfUniqueOfSimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.TripleGlue

def DensePart {X X₀ : Scheme.{0}} (j : X₀ ⟶ X) : Prop :=
  (Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) ∧ IsPreimmersion j ∧ Flat j ∧
    IsDominant j ∧ QuasiCompact j

theorem DensePart.restrict {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) (i : Y ⟶ X) [IsOpenImmersion i]
    {k : X₀ ⟶ Y} (hk : k ≫ i = j) : DensePart k := by
  obtain ⟨⟨hn, z, hz₁, hz₂⟩, h₁, h₂, h₃, h₄⟩ := h
  have sq : IsPullback (𝟙 X₀) k j i := IsPullback.of_horiz_isIso_mono ⟨by rw [hk, Category.id_comp]⟩
  refine ⟨⟨fun y => ?_, i ≫ z, inferInstance, inferInstance⟩, MorphismProperty.of_isPullback sq h₁,
    MorphismProperty.of_isPullback sq h₂, ⟨?_⟩, MorphismProperty.of_isPullback sq h₄⟩
  · obtain ⟨_, _⟩ := hn (i y)
    have e := (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  · have e : Set.range k = i ⁻¹' Set.range j := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, by rw [← hk, Scheme.Hom.comp_apply]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, i.isOpenEmbedding.injective (by rw [← hx, ← hk, Scheme.Hom.comp_apply])⟩
    rw [DenseRange, e]
    exact j.denseRange.preimage i.isOpenEmbedding.isOpenMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_cast {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f g : S' ⟶ S} (m : SABMap t' t f) (h : f = g) :
    ∃ n : SABMap t' t g, n.φ = m.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem exists_fac {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} {t₀ : SAB H X₀} {t : SAB H X} (a : SABMap t₀ t j) (i : Y ⟶ X)
    {k : X₀ ⟶ Y} (hk : k ≫ i = j) :
    ∃ (s : SAB H Y) (b : SABMap t₀ s k) (m : SABMap s t i), b.φ ≫ m.φ = a.φ := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull i t
  obtain ⟨a', ha'⟩ := exists_cast a hk.symm
  obtain ⟨b, hb⟩ := ObjMaps.exists_sab_cancel m a'
  exact ⟨_, b, m, hb.symm.trans ha'⟩

theorem DensePart.generic {X X₀ : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) {t₀ : SAB H X₀} {t : SAB H X}
    (a : SABMap t₀ t j) (hp : IsProper t₀.G.hom) : IsReduced X ∧ genericPoints X ⊆ abLocus t.G := by
  obtain ⟨hX, h₁, h₂, h₃, h₄⟩ := h
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (hX.1 x).1
    infer_instance
  exact ⟨isReduced_of_isReduced_stalk X,
    (densePart_basic X X₀ j h₁ h₂ h₃ h₄).1.trans (range_subset_abLocus_of_isProper t.semi a.cart.1)⟩

section

variable (hdvr : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
include hdvr

theorem DensePart.exists_map {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} {k : X₀ ⟶ Y} (h : DensePart k) {i : Y ⟶ X}
    (hk : k ≫ i = j) {t₀ : SAB H X₀} {t : SAB H X} {s : SAB H Y} (a : SABMap t₀ t j) (b : SABMap t₀ s k)
    (hp : IsProper t₀.G.hom) : ∃ n : SABMap s t i, b.φ ≫ n.φ = a.φ := by
  obtain ⟨s', b', m, hm⟩ := exists_fac a i hk
  obtain ⟨c, hc⟩ := exists_sabMap_id_of_common_generic hdvr E H Y X₀ k h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    t₀ s s' b b' hp
  obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp m c
  obtain ⟨n', hn'⟩ := exists_cast n (Category.id_comp i)
  exact ⟨n', by rw [hn', hn, ← Category.assoc, hc, hm]⟩

theorem DensePart.glue_top {X X₀ : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) {U V : X.Opens} (hUV : U ⊔ V = ⊤)
    {jU : X₀ ⟶ U.toScheme} {jV : X₀ ⟶ V.toScheme} (hU : jU ≫ U.ι = j) (hV : jV ≫ V.ι = j) {t₀ : SAB H X₀}
    {t₁ : SAB H U.toScheme} {t₂ : SAB H V.toScheme} (a₁ : SABMap t₀ t₁ jU) (a₂ : SABMap t₀ t₂ jV)
    (hp : IsProper t₀.G.hom) : ∃ t : SAB H X, Nonempty (SABMap t₀ t j) := by
  have hr : Set.range j ⊆ Set.range (U ⊓ V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact ⟨by rw [← hU]; exact (jU x).2, by rw [← hV]; exact (jV x).2⟩
  obtain ⟨k, hk⟩ : ∃ k : X₀ ⟶ (U ⊓ V).toScheme, k ≫ (U ⊓ V).ι = j := ⟨_, IsOpenImmersion.lift_fac _ j hr⟩
  have hkU : k ≫ X.homOfLE inf_le_left = jU := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, hk, hU]
  have hkV : k ≫ X.homOfLE inf_le_right = jV := by
    rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, hk, hV]
  obtain ⟨s, b, m₁, -⟩ := exists_fac a₁ _ hkU
  obtain ⟨m₂, -⟩ := (h.restrict _ hk).exists_map hdvr hkV a₂ b hp
  obtain ⟨t, n₁, -, -⟩ := GlobalTheory.T.exists_triple_glue_two_opens E H X U V t₁ t₂ s m₁ m₂ hUV ((h.restrict _ hU).generic a₁ hp)
    ((h.restrict _ hV).generic a₂ hp)
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp n₁ a₁
  obtain ⟨n', -⟩ := exists_cast n hU
  exact ⟨t, ⟨n'⟩⟩

omit hdvr in

theorem exists_trace {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} (i : Y ⟶ X) {k : X₀ ⟶ Y} (hk : k ≫ i = j) {U : X.Opens}
    {jU : X₀ ⟶ U.toScheme} (hU : jU ≫ U.ι = j) {t₀ : SAB H X₀} {t : SAB H U.toScheme} (a : SABMap t₀ t jU) :
    ∃ (k' : X₀ ⟶ (i ⁻¹ᵁ U).toScheme) (s : SAB H (i ⁻¹ᵁ U).toScheme),
      k' ≫ (i ⁻¹ᵁ U).ι = k ∧ Nonempty (SABMap t₀ s k') := by
  have hr : Set.range k ⊆ Set.range (i ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show i (k x) ∈ U
    rw [← Scheme.Hom.comp_apply, hk, ← hU]
    exact (jU x).2
  obtain ⟨k', hk'⟩ : ∃ k' : X₀ ⟶ (i ⁻¹ᵁ U).toScheme, k' ≫ (i ⁻¹ᵁ U).ι = k := ⟨_, IsOpenImmersion.lift_fac _ k hr⟩
  have e : k' ≫ (i ∣_ U) = jU := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hk', hk, hU]
  obtain ⟨s, b, -, -⟩ := exists_fac a _ e
  exact ⟨k', s, hk', ⟨b⟩⟩

theorem DensePart.glue_sup {X X₀ : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) {t₀ : SAB H X₀} (hp : IsProper t₀.G.hom)
    {U V : X.Opens}
    (hU : ∃ (k : X₀ ⟶ U.toScheme) (s : SAB H U.toScheme), k ≫ U.ι = j ∧ Nonempty (SABMap t₀ s k))
    (hV : ∃ (k : X₀ ⟶ V.toScheme) (s : SAB H V.toScheme), k ≫ V.ι = j ∧ Nonempty (SABMap t₀ s k)) :
    ∃ (k : X₀ ⟶ (U ⊔ V).toScheme) (s : SAB H (U ⊔ V).toScheme), k ≫ (U ⊔ V).ι = j ∧ Nonempty (SABMap t₀ s k) := by
  obtain ⟨jU, t₁, hU, ⟨a₁⟩⟩ := hU
  obtain ⟨jV, t₂, hV, ⟨a₂⟩⟩ := hV
  have hk : (jU ≫ X.homOfLE le_sup_left) ≫ (U ⊔ V).ι = j := by rw [Category.assoc, Scheme.homOfLE_ι, hU]
  obtain ⟨k₁, s₁, hk₁, ⟨b₁⟩⟩ := exists_trace _ hk hU a₁
  obtain ⟨k₂, s₂, hk₂, ⟨b₂⟩⟩ := exists_trace _ hk hV a₂
  have hc : (U ⊔ V).ι ⁻¹ᵁ U ⊔ (U ⊔ V).ι ⁻¹ᵁ V = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, Scheme.Opens.ι_preimage_self]
  obtain ⟨t, ha⟩ := (h.restrict _ hk).glue_top hdvr hc hk₁ hk₂ b₁ b₂ hp
  exact ⟨_, t, hk, ha⟩

end

end GlobalTheory.TripleGlue

theorem GlobalTheory.exists_sab_glue_of_common_generic : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ : Scheme.{0}) (j : X₀ ⟶ X) (t₀ : SAB H X₀) (I : Type) [Finite I] (U : I → X.Opens) (jU : ∀ i, X₀ ⟶ (U i).toScheme) (t : ∀ i, SAB H (U i).toScheme) (a : ∀ i, SABMap t₀ (t i) (jU i)), Nonempty I → (Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsProper t₀.G.hom → ⨆ i, U i = ⊤ → (∀ i, jU i ≫ (U i).ι = j) → ∃ (t' : SAB H X) (a' : SABMap t₀ t' j) (n : ∀ i, SABMap (t i) t' (U i).ι), ∀ i, (a i).φ ≫ (n i).φ = a'.φ := by
  intro hdvr E _ _ _ H X X₀ j t₀ I _ U jU t a hI hX h₁ h₂ h₃ h₄ hp hcov hj
  have h : TripleGlue.DensePart j := ⟨hX, h₁, h₂, h₃, h₄⟩
  have := Fintype.ofFinite I
  have key : ∃ (k : X₀ ⟶ (Finset.univ.sup' Finset.univ_nonempty U).toScheme) (s : SAB H _),
      k ≫ (Finset.univ.sup' Finset.univ_nonempty U).ι = j ∧ Nonempty (SABMap t₀ s k) :=
    Finset.sup'_induction (p := fun W : X.Opens => ∃ (k : X₀ ⟶ W.toScheme) (s : SAB H W.toScheme),
      k ≫ W.ι = j ∧ Nonempty (SABMap t₀ s k)) _ _ (fun _ hU _ hV => h.glue_sup hdvr hp hU hV)
      (fun i _ => ⟨jU i, t i, hj i, ⟨a i⟩⟩)
  rw [Finset.sup'_univ_eq_ciSup, hcov] at key
  obtain ⟨k, s, hk, ⟨b⟩⟩ := key
  have e : j ≫ X.topIso.inv = k := by
    rw [← hk, Category.assoc]
    exact (congrArg (k ≫ ·) X.topIso.hom_inv_id).trans (Category.comp_id _)
  obtain ⟨t', a', -, -⟩ := TripleGlue.exists_fac b _ e
  choose n hn using fun i => (h.restrict _ (hj i)).exists_map hdvr (hj i) a' (a i) hp
  exact ⟨t', a', n, hn⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectOfPolarisedLatticeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaObject_of_polarisedLattice : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), Function.Bijective EF → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∀ j, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q x) = Q (ac j x)) → (∀ x, ac w x + ac w' x = x) → (∀ x y, EF (ac w x) y = EF x (ac w' y)) → (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF (lam i₁) (lam i₂) : ℂ) / ((k : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) → ∃ t : TObj g k J b (spMap em), t.Prim w w' ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  first | exact @GlobalTheory.thetaObject_of_lattice | exact GlobalTheory.thetaObject_of_lattice | (intros; apply GlobalTheory.thetaObject_of_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueMapToThetaFamilyOpenPartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_map_to_thetaFamily_openPart : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (F : WFam n em C Mat κ) (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) → t.FibShape Mat κ → ∃! f : S ⟶ F.U.toScheme, f ≫ F.U.ι ≫ F.Y.s = s' ∧ TMap t F.univ f := by
  first | exact @GlobalTheory.ZM.UnivProp.existsUnique_map_of_wFam | exact GlobalTheory.ZM.UnivProp.existsUnique_map_of_wFam | (intros; apply GlobalTheory.ZM.UnivProp.existsUnique_map_of_wFam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsLocallyNoetherianOfIsQProjOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem isLocallyNoetherian_of_isQProjOver {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}}
    {s : X ⟶ Sp R} (hs : IsQProjOver s) : IsLocallyNoetherian X := by
  obtain ⟨N, i, hi, -, rfl⟩ := hs
  have := isProper_str R N
  exact LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str R N)

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELObjectOfPrimitivePeriodMapUniformisedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPELObject_of_primitive_periodMap_uniformised : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (ty : Fin g → (E →+* ℂ)) (t : TObj g k J b (spMap em)) (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (Q : D'.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), 1 ≤ D.p + D.q → a w = H.w0 → em ρ = H.rt0 → IsTypeFn H D.p D.q ty → (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') → em (b.ζ : o) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) → IsPeriod D' ty Q → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ D'.EF x ((fun j x => a j • x) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i => f k (bas (Pi.single i 1))) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j x => a j • x) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.Prim w w' → PELClass D a bas ρ em t := by
  first | exact @GlobalTheory.PeriodObject.pelClass_of_period | exact GlobalTheory.PeriodObject.pelClass_of_period | (intros; apply GlobalTheory.PeriodObject.pelClass_of_period <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IterateEqIdOfTrivialOnFixedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.StabTame

theorem act_natCast {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (a : OAct O G) (n : ℕ) :
    a.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h := a.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    exact left_eq_mul.1 h
  | succ n ih => rw [Nat.cast_succ, a.add, ih, a.one, pow_succ]

theorem exists_geomPoint (S : Scheme.{0}) [Nonempty S] :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k), Nonempty (Sp k ⟶ S) := by
  obtain ⟨z⟩ : Nonempty S := inferInstance
  exact ⟨AlgebraicClosure (S.residueField z), inferInstance, inferInstance,
    ⟨Spec.map (CommRingCat.ofHom (algebraMap (S.residueField z) _)) ≫ S.fromSpecResidueField z⟩⟩

theorem iterate_modN {V : Type} [AddCommGroup V] (N : ℕ) (e : LinearMap.BilinForm ℤ V) (P : V → Prop) (g : V →+ V)
    (hg : ∀ v w, (N : ℤ) ∣ e (g v) (g w) - e v w) (hP : ∀ v, P v → ∃ c, g v - v = N • c)
    (hco : ∀ v, (∀ w, P w → (N : ℤ) ∣ e v w) → P v) (v : V) : ∃ c, g^[N] v - v = N • c := by
  have h1 : P (g v - v) := by
    refine hco _ fun w hw => ?_
    obtain ⟨c, hc⟩ := hP w hw
    have e1 : e (g v - v) w = (e (g v) (g w) - e v w) - (N : ℤ) * e (g v) c := by
      have : g w = w + N • c := by rw [← hc]; abel
      rw [this]
      simp only [map_sub, map_add, map_nsmul, LinearMap.sub_apply, nsmul_eq_mul]
      ring
    rw [e1]
    exact dvd_sub (hg v w) (dvd_mul_right _ _)
  obtain ⟨d, hd⟩ := hP _ h1
  have key : ∀ n : ℕ, ∃ c, g^[n] v = v + n • (g v - v) + N • c := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨g c + n • d, ?_⟩
      have : g (g v - v) = (g v - v) + N • d := by rw [← hd]; abel
      rw [Function.iterate_succ_apply', hc, map_add, map_add, map_nsmul, map_nsmul, this]
      simp only [nsmul_add, succ_nsmul, smul_comm N n d]
      abel
  obtain ⟨c, hc⟩ := key N
  exact ⟨g v - v + c, by rw [hc, nsmul_add]; abel⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

section

variable {B : Type} [CommRing B] {b : Base l B} {U : Scheme.{0}} {s : U ⟶ Sp B}

theorem modN_of_point_eq (o : Obj D l b s) {k : Type} [Field k] [IsAlgClosed k] (u : Sp k ⟶ U) {a a' : D.La}
    (h : u ≫ (o.etaA a').left = u ≫ (o.etaA a).left) : ∃ c, a' - a = l.A • c := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (u ≫ s)
  obtain ⟨-, I, -, hA, -⟩ := o.geom k u β.hom hβ.symm
  have h1 : I.ev l.A a' = I.ev l.A a := by
    rw [← hA, ← hA]
    exact Over.OverMorphism.ext h
  have h2 := I.add l.A (a' - a) a
  rw [sub_add_cancel, h1] at h2
  exact (I.ker l.A l.A_pos _).1 (right_eq_mul.1 h2)

theorem isometry_modN (o : Obj D l b s) [Nonempty U] (r : U ⟶ U) (ν : SABMap o.t o.t r) (hr : r ≫ s = s)
    {a a' c c' : D.La} (ha : (o.etaA a').left ≫ ν.φ = r ≫ (o.etaA a).left)
    (hc : (o.etaA c').left ≫ ν.φ = r ≫ (o.etaA c).left) : (l.A : ℤ) ∣ D.EF a' c' - D.EF a c := by
  obtain ⟨k, _, _, ⟨u⟩⟩ := exists_geomPoint U
  obtain ⟨β, hβ⟩ := Spec.map_surjective (u ≫ s)
  obtain ⟨-, I, hζ, hA, -⟩ := o.geom k u β.hom hβ.symm
  obtain ⟨-, J, hζ', hA', -⟩ := o.geom k (u ≫ r) β.hom (by rw [Category.assoc, hr]; exact hβ.symm)
  have hz : I.ζ l.A = J.ζ l.A := Units.ext (hζ.trans hζ'.symm)
  have hL : LBIso o.t.PP.L (o.t.PP.L.pull ν.φ) := ν.lin.imp fun _ h => h.1
  have mv : ∀ {x x' : D.La}, (o.etaA x').left ≫ ν.φ = r ≫ (o.etaA x).left →
      (J.ev l.A x).left = (I.ev l.A x').left ≫ ν.φ := by
    intro x x' h
    rw [← hA, ← hA']
    show (u ≫ r) ≫ (o.etaA x).left = (u ≫ (o.etaA x').left) ≫ ν.φ
    rw [Category.assoc, Category.assoc, h]
  have w := (weilIs_grpPullback_of_comm U U o.t.G o.t.G r ν.φ o.t.PP.L o.t.PP.L o.t.PP.isLB o.t.PP.isLB ν.cart hL
    (Over.mk u) l.A _ _ (J.ev l.A a) (J.ev l.A c) _ (mv ha) (mv hc)).1 (I.isom l.A l.A_pos a' c')
  have e := weilIs_unique_fieldPoint U o.t.G o.t.PP.L o.t.PP.isLB k (u ≫ r) l.A _ _ _ _ w (J.isom l.A l.A_pos a c)
  rw [hz] at e
  rw [← (J.ζ_prim l.A l.A_pos).zpow_eq_one_iff_dvd, zpow_sub, e, mul_inv_cancel]

end

theorem modN_of_extends {B : Type} [CommRing B] {b : Base l B} {X U : Scheme.{0}} [IsReduced X] {s : U ⟶ Sp B}
    (j : U ⟶ X) [IsDominant j] (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j) (hN : IsUnit (l.A : Γ(X, ⊤)))
    (r : U ⟶ U) (ν : SABMap o.t o.t r) (ρ : X ⟶ X) (mu : SABMap t t ρ) (hj : j ≫ ρ = r ≫ j)
    (hφ : μ₀.φ ≫ mu.φ = ν.φ ≫ μ₀.φ) {a a' : D.La} (ha : (o.etaA a').left ≫ ν.φ = r ≫ (o.etaA a).left)
    {k : Type} [Field k] (x : Sp k ⟶ X) (hx : x ≫ ρ = x)
    (hfib : pullback.fst t.G.hom x ≫ mu.φ = pullback.fst t.G.hom x)
    (W : X.Opens) (σ : W.toScheme ⟶ t.G.left) (hxW : Set.range x ⊆ W) (hσ : σ ≫ t.G.hom = W.ι)
    (hσj : pullback.fst W.ι j ≫ σ = pullback.snd W.ι j ≫ (o.etaA a).left ≫ μ₀.φ) : ∃ c, a' - a = l.A • c := by
  have pn : IsPullback μ₀.φ o.t.G.hom t.G.hom j := μ₀.cart.1
  have pm : IsPullback mu.φ t.G.hom t.G.hom ρ := mu.cart.1
  have sec : ∀ y : 𝟙_ (Over U) ⟶ o.t.G, y.left ≫ o.t.G.hom = 𝟙 U := fun y => Over.w y
  have ext : ∀ {Z : Scheme.{0}} (w : Z ⟶ W.toScheme) (u : Z ⟶ U), w ≫ W.ι = u ≫ j →
      w ≫ σ = u ≫ (o.etaA a).left ≫ μ₀.φ := by
    intro Z w u h
    have := pullback.lift w u h ≫= hσj
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  let T := pullback W.ι (W.ι ≫ ρ)
  let p₁ : T ⟶ W.toScheme := pullback.fst _ _
  let p₂ : T ⟶ W.toScheme := pullback.snd _ _
  have hp : p₁ ≫ W.ι = p₂ ≫ W.ι ≫ ρ := pullback.condition
  have : IsOpenImmersion p₂ := inferInstanceAs (IsOpenImmersion (pullback.snd W.ι (W.ι ≫ ρ)))
  let i : T ⟶ X := p₂ ≫ W.ι
  have : IsReduced T := isReduced_of_isOpenImmersion i
  have w₂ : (p₁ ≫ σ) ≫ t.G.hom = i ≫ ρ := by rw [Category.assoc, hσ, hp, Category.assoc]
  let σ₁ : T ⟶ t.G.left := p₂ ≫ σ
  let σ₂ : T ⟶ t.G.left := pm.lift (p₁ ≫ σ) i w₂
  have s₁ : σ₁ ≫ t.G.hom = i := by rw [Category.assoc, hσ]
  have s₂ : σ₂ ≫ t.G.hom = i := pm.lift_snd _ _ _
  have s₃ : σ₂ ≫ mu.φ = p₁ ≫ σ := pm.lift_fst _ _ _
  let x₀ : Sp k ⟶ W.toScheme := IsOpenImmersion.lift W.ι x (by rwa [Scheme.Opens.range_ι])
  have hx₀ : x₀ ≫ W.ι = x := IsOpenImmersion.lift_fac _ _ _
  let xT : Sp k ⟶ T := pullback.lift x₀ x₀ (by rw [← Category.assoc, hx₀, hx])
  have x₁ : xT ≫ p₁ = x₀ := pullback.lift_fst _ _ _
  have x₂ : xT ≫ p₂ = x₀ := pullback.lift_snd _ _ _
  have hxT : xT ≫ σ₁ = xT ≫ σ₂ := by
    have w : (xT ≫ σ₂) ≫ t.G.hom = 𝟙 _ ≫ x := by
      rw [Category.assoc, s₂, ← Category.assoc, x₂, hx₀, Category.id_comp]
    have h := pullback.lift (xT ≫ σ₂) (𝟙 _) w ≫= hfib
    rw [pullback.lift_fst_assoc, pullback.lift_fst, Category.assoc, s₃, ← Category.assoc, x₁] at h
    rw [← h, ← Category.assoc, x₂]
  let q₁ := pullback.fst i j
  let q₂ := pullback.snd i j
  have hq : q₁ ≫ i = q₂ ≫ j := pullback.condition
  have : IsDominant q₁ := isDominant_pullback_fst_of_isOpenMap j i i.isOpenEmbedding.isOpenMap
  have v₁ : q₁ ≫ σ₁ = q₂ ≫ (o.etaA a).left ≫ μ₀.φ := by
    rw [← Category.assoc]
    exact ext _ _ (by rw [Category.assoc]; exact hq)
  have v₂ : q₁ ≫ σ₂ = q₂ ≫ (o.etaA a').left ≫ μ₀.φ := by
    refine pm.hom_ext ?_ ?_
    · rw [Category.assoc, s₃, Category.assoc, Category.assoc, hφ, reassoc_of% ha, ← Category.assoc,
        ← Category.assoc q₂ r]
      refine ext _ _ ?_
      rw [Category.assoc, hp, Category.assoc, ← hj, ← Category.assoc q₂, ← hq, Category.assoc, Category.assoc]
    · rw [Category.assoc, s₂, hq, Category.assoc, Category.assoc, pn.w, ← Category.assoc (o.etaA a').left, sec]
      exact congrArg (q₂ ≫ ·) (Category.id_comp j).symm
  have tor : ∀ y : D.La, (o.etaA y).left ≫ μ₀.φ ≫ (t.act.act (l.A : 𝓞 E)).left =
      (1 : 𝟙_ (Over U) ⟶ o.t.G).left ≫ μ₀.φ := by
    intro y
    have h : μ₀.φ ≫ (t.act.act (l.A : 𝓞 E)).left = (o.t.act.act (l.A : 𝓞 E)).left ≫ μ₀.φ := (μ₀.act _).symm
    rw [h, ← Category.assoc, ← Over.comp_left, act_natCast, MonObj.comp_pow, Category.comp_id,
      ← LiftAut.etaA_nsmul, o.etaA_ker]
  have := t.semi.separated
  have := t.semi.smooth
  have : Etale (t.act.act (l.A : 𝓞 E)).left := by
    rw [act_natCast]
    exact GrpTangent.etale_id_pow t.G hN
  have hmul : σ₁ ≫ (t.act.act (l.A : 𝓞 E)).left = σ₂ ≫ (t.act.act (l.A : 𝓞 E)).left := by
    refine ext_of_isDominant_of_isSeparated t.G.hom ?_ q₁ ?_
    · rw [Category.assoc σ₁, Category.assoc σ₂, Over.w, s₁, s₂]
    · rw [reassoc_of% v₁, reassoc_of% v₂, tor, tor]
  have := isOpenImmersion_equalizer_ι_of_unramified _ hmul
  let e := equalizer.ι σ₁ σ₂
  have he : e ≫ σ₁ = e ≫ σ₂ := equalizer.condition _ _
  have : IsDominant (pullback.fst e q₁) := isDominant_pullback_fst_of_isOpenMap q₁ e e.isOpenEmbedding.isOpenMap
  have : Nonempty ↑(equalizer σ₁ σ₂) := ⟨equalizer.lift xT hxT (⊥ : PrimeSpectrum k)⟩
  have : Nonempty ↑(pullback e q₁) := (pullback.fst e q₁).denseRange.nonempty
  obtain ⟨K, _, _, ⟨y⟩⟩ := exists_geomPoint (pullback e q₁)
  refine modN_of_point_eq o (y ≫ pullback.snd e q₁ ≫ q₂) (pn.hom_ext ?_ ?_)
  · simp only [Category.assoc]
    rw [← v₁, ← v₂, ← pullback.condition_assoc, ← pullback.condition_assoc, he]
  · simp only [Category.assoc]
    rw [sec, sec]

theorem exists_sabMap_iterate (Xo : Moduli D l) (r : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r)
    (hr : r ≫ Xo.s = Xo.s) (h : ∀ x, (Xo.univ.eta x).left ≫ ν.φ = r ≫ (Xo.univ.eta x).left) (g : D.La → D.La)
    (hg : ∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r ≫ (Xo.univ.etaA x).left) (n : ℕ) :
    ∃ (f : Xo.X ⟶ Xo.X) (m : SABMap Xo.univ.t Xo.univ.t f), f = (fun f : Xo.X ⟶ Xo.X => f ≫ r)^[n] (𝟙 _) ∧
      f ≫ Xo.s = Xo.s ∧ (∀ x, (Xo.univ.eta x).left ≫ m.φ = f ≫ (Xo.univ.eta x).left) ∧
      ∀ x, (Xo.univ.etaA (g^[n] x)).left ≫ m.φ = f ≫ (Xo.univ.etaA x).left := by
  induction n with
  | zero =>
    obtain ⟨m, hm⟩ := ObjMaps.exists_sab_id Xo.univ.t
    exact ⟨𝟙 _, m, rfl, Category.id_comp _, fun _ => by rw [hm, Category.comp_id, Category.id_comp],
      fun _ => by rw [hm, Category.comp_id, Category.id_comp]; rfl⟩
  | succ n ih =>
    obtain ⟨f, m, hf, hs, h₁, h₂⟩ := ih
    obtain ⟨m', hm⟩ := ObjMaps.exists_sab_comp ν m
    refine ⟨f ≫ r, m', by rw [Function.iterate_succ_apply', ← hf], by rw [Category.assoc, hr, hs], fun x => ?_,
      fun x => ?_⟩
    · rw [hm, reassoc_of% (h₁ x), h, Category.assoc]
    · rw [hm, Function.iterate_succ_apply, reassoc_of% (h₂ (g x)), hg, Category.assoc]

theorem iterate_eq_id_of_fixes_fibre : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom) (ρ : C.X ≅ C.X) (mu : SABMap C.t C.t ρ.hom), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → C.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ → r.hom ≫ Xo.s = Xo.s → (∀ x, (Xo.univ.eta x).left ≫ ν.φ = r.hom ≫ (Xo.univ.eta x).left) → ∀ g : D.La →ₗ[𝓞 E] D.La, (∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ (Xo.univ.etaA x).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → pullback.fst C.t.G.hom x ≫ mu.φ = pullback.fst C.t.G.hom x → (fun f : Xo.X ⟶ Xo.X => f ≫ r.hom)^[l.A] (𝟙 _) = 𝟙 _ := by
  intro h₁ h₂ h₃ E _ _ _ H D l Xo S β C r ν ρ mu hinc hS ⟨e, he⟩ hj hφ hr hη g hg k _ _ x hx hfib
  obtain ⟨⟨_, hded⟩, -, hfrac⟩ := (BaseRing.isDedFrac_RZ E H l S e hS he).2.2 β hinc
  letI := β.toAlgebra
  obtain ⟨hnoeth, -, -, hpre, hflat, hdom, hqc⟩ := genericPart_dense_proOpen (RZ H S l.A) (KA l) C.X Xo.X C.s C.jQ
    C.flat C.proj C.jQ_open C.jQ_dense
  have hd : IsDominant C.j := hdom
  have hred : IsReduced C.X := by
    have := fun y => (C.normal y).1
    exact isReduced_of_isReduced_stalk _
  let t : RZ H S l.A := ⟨(S : ℂ)⁻¹, Subring.subset_closure (by simp)⟩
  have hSu : IsUnit (S : RZ H S l.A) := IsUnit.of_mul_eq_one t (Subtype.ext (by
    have : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
    simp [t, this]))
  have hAu : IsUnit (l.A : RZ H S l.A) := by
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast he) ?_
    rw [Nat.cast_pow]
    exact hSu.pow e
  have hN : IsUnit (l.A : Γ(C.X, ⊤)) := by
    have := (hAu.map (Scheme.ΓSpecIso (CommRingCat.of (RZ H S l.A))).inv.hom).map C.s.appTop.hom
    rwa [map_natCast, map_natCast] at this
  have : Nonempty C.X := ⟨x (⊥ : PrimeSpectrum k)⟩
  have : Nonempty Xo.X := C.j.denseRange.nonempty
  have hmod := iterate_modN l.A D.EF _ g.toAddMonoidHom
    (fun v w => isometry_modN Xo.univ r.hom ν hr (hg v) (hg w))
    (fun v ⟨W, σ, hW, hσ, hσj⟩ =>
      modN_of_extends C.j Xo.univ C.t C.m hN r.hom ν ρ.hom mu hj hφ (hg v) x hx hfib W σ hW hσ hσj)
    (GlobalTheory.T.levelLabel_extends_of_orthogonal_to_extended h₁ h₂ h₃ E H D l (KA l) (baseKA l) C.X Xo.X C.j Xo.s Xo.univ C.t C.m C.normal hpre hflat hdom hqc
      hN k x)
  obtain ⟨f, m, hf, hs, e₁, e₂⟩ := exists_sabMap_iterate Xo r.hom ν hr hη g.toAddMonoidHom hg l.A
  rw [← hf]
  refine LiftAut.eq_id Xo f m hs e₁ fun a => ?_
  rw [← e₂, LiftAut.etaA_congr Xo.univ (hmod a)]

end GlobalTheory.StabTame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyCmModuliOfDeeperLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.ZM

theorem moduli_of_deeper_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l₂) → Nonempty (Moduli D l) := by
  intro L L2 hT E _ _ _ H D l l₂ hD hl ⟨Xo₂⟩
  obtain ⟨Q⟩ := GlobalTheory.T.nonempty_levelQuot_of_level_dvd L L2 hT E H D l l₂ Xo₂ hD hl
  exact ⟨{ X := Q.X, s := Q.s, qproj := Q.qproj, smooth := Q.smooth, univ := Q.univ,
           rep := GlobalTheory.T.levelQuotient_represents_reduced L L2 E H D l l₂ Xo₂ Q hD hl,
           unram := GlobalTheory.T.levelQuotient_unramified_dualNumberPoints L L2 E H D l l₂ Xo₂ Q hD hl }⟩
end GlobalTheory.ZM
end

