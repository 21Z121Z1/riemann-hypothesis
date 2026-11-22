import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0235
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyZOnOfComponents
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0232
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyPelSmoothGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaFamily_pel_smooth_generic_fibre : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∃ (F : ThetaFam n em (PELClass (b := b) D a bas ρ em)) (τ : SAB H F.MM), IsPEL D a bas ρ F.univ τ ∧ SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap o (FractionRing o)))) := by
  first | exact @GlobalTheory.ZM.exists_thetaFam_isPEL_smooth | exact GlobalTheory.ZM.exists_thetaFam_isPEL_smooth | (intros; apply GlobalTheory.ZM.exists_thetaFam_isPEL_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalQuasiProjectiveSiegelFamilyLargeLStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_quasiProjective_siegelFamily_large_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ h n : ℕ, 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily h p ((n ^ j) ^ 2), SiegRep Ag := by
  first | exact @GlobalTheory.ZM.SiegelUniversal.exists_siegelFamily_siegRep | exact GlobalTheory.ZM.SiegelUniversal.exists_siegelFamily_siegRep | (intros; apply GlobalTheory.ZM.SiegelUniversal.exists_siegelFamily_siegRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeNonemptyAtEveryLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduliScheme_nonempty_at_every_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N1ab := by
  first | exact @GlobalTheory.ZM.moduli_nonempty_all_levels | exact GlobalTheory.ZM.moduli_nonempty_all_levels | (intros; apply GlobalTheory.ZM.moduli_nonempty_all_levels <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyAmpleFramedModelPELThetaFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem GlobalTheory.nonempty_zOn_thetaFam : Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n : ℕ), 1 ≤ D.p + D.q → n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → Nonempty (ZOn F.s τ (n ^ k)) := by
  intro h1 h2 h3 h4 h5 h6 E _ _ _ H D n hpq hn hodd
  exact FamilyModel.nonempty_zOn_of_components GlobalTheory.T.exists_model_triple_ampleFrames_component h1 h2 h3 h4 h5 h6 E H D n hpq hn hodd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyHeckeCorrespondenceScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem corr_kerSet_unique {S : Scheme.{0}} {G G' : Over S} [GrpObj G'] {ψ : G ⟶ G'} {K K' : Set G.left}
    (h : KerSet ψ K) (h' : KerSet ψ K') : K = K' := by
  ext g
  obtain ⟨k, _, _, z₀, hz⟩ := exists_geomPt_range_eq G.left g
  let z : Over.mk (z₀ ≫ G.hom) ⟶ G := Over.homMk z₀ rfl
  have h1 := h k _ z
  have h2 := h' k _ z
  have hzl : z.left = z₀ := rfl
  rw [hzl, hz, Set.singleton_subset_iff] at h1 h2
  exact h1.symm.trans h2

theorem corr_heckeSet_kill {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {S : Scheme.{0}} (t : SAB H S) {P : Ideal (𝓞 E)} {p i : ℕ} {K : Set t.G.left} (hpP : (p : 𝓞 E) ∈ P)
    (hK : HeckeSet D t P p i K) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ t.G)
    (hz : Set.range z.left ⊆ K) : z ^ p ^ 2 = 1 := by
  have hnat : ∀ {T : Over S} (x : T ⟶ t.G) (n : ℕ), x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
    intro T x n
    induction n with
    | zero =>
      have h := t.act.add 0 0
      rw [add_zero] at h
      have h0 : t.act.act 0 = 1 := by simpa using h
      rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]
  obtain ⟨C, hC, hH⟩ := hK k x
  have hzC := hH.2.2.1 ((hC z).2 hz)
  have hbar : (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
    rwa [map_natCast] at this
  have h := hzC ((p ^ 2 : ℕ) : 𝓞 E) (by
    rw [Nat.cast_pow, pow_two]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hbar)
  rwa [hnat] at h

theorem corr_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), 1 ≤ D.p + D.q → admitted l 𝔓 p → Nonempty (Corr Xo 𝔓 p i) := by
  intro E _ _ _ H D l Xo P p i hr hA
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_heckeKernelScheme_universal_reduced_bases E H D l Xo P p i hA
  have := Z.et₁
  have := Xo.smooth
  have hXs : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have hs : Smooth (Z.π₁ ≫ Xo.s) := inferInstance
  have hred : IsReduced Z.Hk :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hs).1
  obtain ⟨S', π, o', m, τ, hf, he, hsu, hL⟩ :=
    GlobalTheory.T.hecke_set_etale_level_structure_exists E H D l P p i Z.Hk _ Z.o₁ Z.K hA hZ Z.hecke
  have hH' := ((GlobalTheory.heckeSets_pull E H D P p i _ _ _ _ _ m.toSABMap Z.o₁.proper).2 Z.K).1 Z.hecke
  have hq' := GlobalTheory.T.heckeQuotient_exists_listed_kernels_smooth_base E H D l Xo P p i _ S' _ o' τ _ hr hA inferInstance hL hH'
  obtain ⟨o₂, ψ, hi, hk⟩ := GlobalTheory.T.heckeQuotient_descends_etale_surjective_cover E H D l Xo P p i Z.Hk S' _ π Z.o₁ o' m Z.K hA Z.hecke he hsu
    inferInstance hq'
  obtain ⟨π₂, ⟨hb, ⟨m₂⟩⟩, -⟩ := Xo.rep _ _ hred o₂
  refine ⟨{ toKerScheme := Z, π₂ := π₂, base₂ := hb, o₂ := o₂, m₂ := m₂, ψ := ψ, isog := hi, ker := hk, univ := ?_ }⟩
  intro S s hS o o' ψ' ⟨hi', K', hk', hH⟩
  have := o'.proper
  have het := (etSet_of_kerSet S _ _ ψ' K' inferInstance hi'.1.2.1 hi'.1.2.2.1 hk').1
  obtain ⟨h, ⟨hh, n₁, hn₁⟩, hu⟩ := Z.rep S s hS o K' het hH
  refine ⟨h, ⟨hh, ?_⟩, ?_⟩
  · obtain ⟨o₃, ⟨n₃⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ s h rfl rfl
      (by rw [hh]; simp [spMap]) o₂
    obtain ⟨⟨ψ₃, hψ₃, -⟩, hall⟩ := GlobalTheory.T.exists_isogeny_pullback_heckeModuliObject E H D l p _ _ _ _ h Z.o₁ o₂ o o₃ n₁ n₃ ψ
    obtain ⟨hi₃, hk₃⟩ := hall ψ₃ hψ₃
    have hk₃' := hk₃ Z.K hi.1.1 hk
    rw [← hn₁] at hk₃'
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_iso_quotients_same_kernel_reduced_base E H D l p S s o o' o₃ ψ' ψ₃ K' hA.2.2.1 hA.2.2.2.2 hi' (hi₃ hi) hk' hk₃'
      (corr_heckeSet_kill o.t hA.2.2.2.1 hH)
    have hc := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o₂ o₃ o').2 h (𝟙 S) n₃).1 m
    have hc' : ∀ g : S ⟶ Z.Hk, g = h → (∃ m'' : ObjMap o' o₂ g, m''.toSABMap.φ = m.toSABMap.φ ≫ n₃.toSABMap.φ) →
        ∃ m'' : ObjMap o' o₂ h, m''.toSABMap.φ = m.toSABMap.φ ≫ n₃.toSABMap.φ := by
      rintro g rfl hg
      exact hg
    obtain ⟨n₂, hn₂⟩ := hc' _ (Category.id_comp h) hc
    exact ⟨n₁, n₂, by rw [hn₂, ← Category.assoc, hm, hψ₃]⟩
  · rintro h' ⟨hh', n₁', n₂', e⟩
    have hk₃ := ((GlobalTheory.T.exists_isogeny_pullback_heckeModuliObject E H D l p _ _ _ _ h' Z.o₁ o₂ o o' n₁' n₂' ψ).2 ψ' e).2 Z.K hi.1.1 hk
    exact hu h' ⟨hh', n₁', corr_kerSet_unique hk' hk₃⟩

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamiliesExistStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamilies_exist : N0 := by
  first | exact @GlobalTheory.Moduli.siegelFamilies_closed | exact GlobalTheory.Moduli.siegelFamilies_closed | (intros; apply GlobalTheory.Moduli.siegelFamilies_closed <;> assumption)
end

