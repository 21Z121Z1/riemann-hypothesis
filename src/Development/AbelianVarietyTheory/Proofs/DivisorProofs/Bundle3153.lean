import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3109
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2782
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2787
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3111
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2547
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3131
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesGenerateConnectedLevelsStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinates_generate_connected_levels : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), G.IsConn → ∃ x : ∀ n, Fin (Module.finrank K G.omega) → G.A n, (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := K) (x n i) = 0) ∧ ∀ n, Function.Surjective (MvPolynomial.aeval (R := K) (x n)) := by
  first | exact @GlobalTheory.PDivGroup.exists_coords_generate | exact GlobalTheory.PDivGroup.exists_coords_generate | (intros; apply GlobalTheory.PDivGroup.exists_coords_generate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalStructureDescendedLineBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_cubicalStr_of_descended_bundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∀ (L : LB G.left) (hL : L.IsLB), LBIso U'.LG.L (L.pull β) → ∀ (rig : LB.Gen (L.pull (eSec G))) (hr : rig.IsGen), Nonempty (CubicalStr G (⟨L, rig, hL, hr⟩ : RigLB G)) := by
  intro R _ _ _ hR R' _ _ _ ρ hρ hgal D D' hD A' G' _ _ hG' U' a G _ _ β hG hβ hact L hL _ rig hr
  obtain ⟨A, gen, -, -, -, -⟩ := GlobalTheory.T.polarised_generic_fibre_descends_galois R hR R' ρ hρ hgal D D' hD A' G' hG' U' a G β hG hβ hact
  obtain ⟨⟨hN, -, hIC, -⟩, -⟩ := hR
  have : IsProper (pullback.snd G.hom (jK R)) := by
    have : IsProper A.A.hom := A.isAb.proper
    have : IsIso gen.hom.left := ((Over.forget _).mapIso gen).isIso_hom
    have hw : gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w gen.hom
    rw [← hw]
    infer_instance
  obtain ⟨L₀, c, rfl⟩ := GlobalTheory.RigCube.exists_rigLB_cubicalStr R G hG this L hL
  exact ⟨⟨c.t, c.isGen, c.face, c.cubeSymmetric_swap_first, c.cubeSymmetric_swap_last, c.cocycle⟩⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descentDatum_of_descendedMultiplication : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ φ, N.Datum φ := by
  first | exact @GlobalTheory.Mum.Desc.exists_datum | exact GlobalTheory.Mum.Desc.exists_datum | (intros; apply GlobalTheory.Mum.Desc.exists_datum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentMumfordBundleQuotientStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_mumfordBundle_quotient : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (H : Over (Sp R)) [GrpObj H] (i : H ⟶ A), IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → (∀ (T : Over (Sp R)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ i = x) → ∀ (B : Over (Sp R)) [GrpObj B] (q : A ⟶ B), IsAbelianScheme B → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q → ∃ (P : LB (A ⊗ B).left) (hP : P.IsLB), ∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL) := by
  first | exact @GlobalTheory.QuotDesc.exists_descent_lam | exact GlobalTheory.QuotDesc.exists_descent_lam | (intros; apply GlobalTheory.QuotDesc.exists_descent_lam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfChartsPulledBackFromFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.ChartDescent

theorem key_move : ∀ (B S X : Scheme.{0}) (π : S ⟶ B) (f : X ⟶ S) (Φ : pullback f (pullback.fst π π) ⟶ pullback f (pullback.snd π π)) (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, e j ≫ f = pullback.snd _ _) → (∀ (j : J) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback f (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ e j → z ≫ pullback.snd _ _ = s → z ≫ Φ ≫ pullback.fst _ _ = y₂ ≫ e j) → (∀ (i j : J) (T : Scheme.{0}) (w₁ w₂ h₁ : T ⟶ pullback U.hom π), w₁ ≫ pullback.fst _ _ = w₂ ≫ pullback.fst _ _ → h₁ ≫ e j = w₁ ≫ e i → ∃ h₂ : T ⟶ pullback U.hom π, h₂ ≫ e j = w₂ ≫ e i ∧ h₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _) := by
  intro B S X π f Φ U J e hf hc i j T w₁ w₂ h₁ hw hh
  have hπ : w₁ ≫ pullback.snd U.hom π ≫ π = w₂ ≫ pullback.snd U.hom π ≫ π := by
    rw [← pullback.condition, reassoc_of% hw]
  have hs1 : h₁ ≫ pullback.snd U.hom π = w₁ ≫ pullback.snd U.hom π := by
    simpa only [Category.assoc, hf] using congrArg (· ≫ f) hh
  let s : T ⟶ pullback π π := pullback.lift (w₁ ≫ pullback.snd _ _) (w₂ ≫ pullback.snd _ _)
    (by simpa only [Category.assoc] using hπ)
  have hs₁ : s ≫ pullback.fst π π = w₁ ≫ pullback.snd _ _ := pullback.lift_fst _ _ _
  have hs₂ : s ≫ pullback.snd π π = w₂ ≫ pullback.snd _ _ := pullback.lift_snd _ _ _
  let z : T ⟶ pullback f (pullback.fst π π) := pullback.lift (w₁ ≫ e i) s
    (by rw [hs₁, Category.assoc, hf])
  have hz₁ : z ≫ pullback.fst _ _ = w₁ ≫ e i := pullback.lift_fst _ _ _
  have hz₂ : z ≫ pullback.snd _ _ = s := pullback.lift_snd _ _ _
  have h1 := hc i T w₁ w₂ s hw hs₁.symm hs₂.symm z hz₁ hz₂
  let y₂ : T ⟶ pullback U.hom π := pullback.lift (h₁ ≫ pullback.fst _ _) (w₂ ≫ pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition, reassoc_of% hs1, Category.assoc, hπ])
  have hy₁ : y₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
  have hy₂ : y₂ ≫ pullback.snd _ _ = w₂ ≫ pullback.snd _ _ := pullback.lift_snd _ _ _
  have h2 := hc j T h₁ y₂ s hy₁.symm (hs1.trans hs₁.symm) (hy₂.trans hs₂.symm) z (hz₁.trans hh.symm) hz₂
  exact ⟨y₂, by rw [← h2, h1], hy₁⟩

theorem cocycle_facts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R) (f : X ⟶ S), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → (∀ i, V i i = ⊤) ∧ (∀ i, τ i i = (V i i).ι) ∧ (∀ (i j k : J) (x : (V i j).toScheme), (V i j).ι x ∈ V i k → τ i j x ∈ V j k) ∧ (∀ (i j k : J) (T : Scheme.{0}) (x : T ⟶ (V i j).toScheme) (y : T ⟶ (V i k).toScheme) (w : T ⟶ (V j k).toScheme), x ≫ (V i j).ι = y ≫ (V i k).ι → x ≫ τ i j = w ≫ (V j k).ι → w ≫ τ j k = y ≫ τ i k) ∧ (∀ i j, τ i j ≫ U.hom = (V i j).ι ≫ U.hom) := by
  intro R _ _ _ _ S X π f hπp hπs hS U hU J e he hef V τ hV hτ
  obtain ⟨h1, h2⟩ := GlobalTheory.T.glue_overlap_diagonal_top_and_cocycle (Sp R) S X π hπs U J e he V τ hV hτ
  obtain ⟨h3, h4⟩ := GlobalTheory.T.descent_transition_diagonal_inclusion_over_base R S X π f hπp hπs hS U hU J e he hef V τ hV hτ
  exact ⟨h1, h3, h2, GlobalTheory.T.descended_chart_transitions_cocycle R S X π hπp hπs hS U hU J e he V τ hV hτ, h4⟩

theorem exists_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R) (f : X ⟶ S), IsProper π → Surjective π → IsIntegral S → ∀ (Φ : pullback f (pullback.fst π π) ⟶ pullback f (pullback.snd π π)), Φ ≫ pullback.snd _ _ = pullback.snd _ _ → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ (j : J) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback f (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ e j → z ≫ pullback.snd _ _ = s → z ≫ Φ ≫ pullback.fst _ _ = y₂ ≫ e j) → ∃ (G : Over (Sp R)) (β : X ⟶ G.left) (ψ : J → (U.left ⟶ G.left)), (∀ j, IsOpenImmersion (ψ j) ∧ ψ j ≫ G.hom = U.hom ∧ e j ≫ β = pullback.fst _ _ ≫ ψ j) ∧ (∀ g : G.left, ∃ j, g ∈ Set.range (ψ j)) ∧ IsPullback β f G.hom π ∧ pullback.fst f (pullback.fst π π) ≫ β = Φ ≫ pullback.fst f (pullback.snd π π) ≫ β := by
  intro R _ _ _ _ S X π f hπp hπs hS Φ hΦ U hU J e he hef hcov hc
  have hK := key_move (Sp R) S X π f Φ U J e hef hc
  choose V hV using GlobalTheory.T.chartOverlap_eq_preimage_open_of_fibre_stable (Sp R) S X π U J e hπp hπs he hK
  choose τ hτ using fun i j => GlobalTheory.T.chart_transition_maps_descend_overlaps R S X π hπp hπs hS U hU J e he hK i j (V i j) (hV i j)
  obtain ⟨hVt, hτi, hland, hcoc, hτR⟩ := cocycle_facts R S X π f hπp hπs hS U hU J e he hef V τ hV hτ
  obtain ⟨G₀, ψ, hψo, hψc, hψp, hψd⟩ := GlobalTheory.T.exists_glue_copies_of_scheme_cocycle U.left J V τ hVt hτi hland hcoc
  obtain ⟨F, hF⟩ := hψd (Sp R) (fun _ => U.hom) (fun i j => (hτR i j).symm)
  have hcomp : ∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π), a ≫ e i = b ≫ e j →
      a ≫ pullback.fst _ _ ≫ ψ i = b ≫ pullback.fst _ _ ≫ ψ j := by
    intro i j T a b hab
    have hr : Set.range (a ≫ pullback.fst U.hom π) ⊆ Set.range (V i j).ι := by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
      refine (hV i j (a t)).2 ⟨b t, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hab, Scheme.Hom.comp_apply]
    have hv : IsOpenImmersion.lift (V i j).ι (a ≫ pullback.fst _ _) hr ≫ (V i j).ι =
        a ≫ pullback.fst _ _ := IsOpenImmersion.lift_fac _ _ _
    rw [← Category.assoc, ← hv, Category.assoc, (hψp i j).w, ← Category.assoc,
      hτ i j T a b _ hab hv, Category.assoc]
  obtain ⟨β, hβ, -⟩ := GlobalTheory.T.existsUnique_glue_maps_openCover_same_source X G₀ (pullback U.hom π) J e (fun j => pullback.fst _ _ ≫ ψ j) he hcov hcomp
  have hw : β ≫ F = f ≫ π := by
    obtain ⟨gg, -, hgg⟩ := GlobalTheory.T.existsUnique_glue_maps_openCover_same_source X (Sp R) (pullback U.hom π) J e (fun _ => pullback.snd _ _ ≫ π) he hcov
      (fun i j T a b hab => by
        have h1 : a ≫ pullback.snd U.hom π = b ≫ pullback.snd U.hom π := by
          simpa only [Category.assoc, hef] using congrArg (· ≫ f) hab
        rw [reassoc_of% h1])
    rw [hgg (β ≫ F) (fun j => by rw [reassoc_of% hβ j, hF j, pullback.condition]),
      hgg (f ≫ π) (fun j => by rw [reassoc_of% hef j])]
  refine ⟨Over.mk F, β, ψ, fun j => ⟨hψo j, hF j, hβ j⟩, hψc, ?_, ?_⟩
  · refine GlobalTheory.T.isPullback_of_isPullback_on_openCover_target X G₀ S (Sp R) β f F π hw J (fun _ => U.left) (fun _ => pullback U.hom π) ψ e
      (fun _ => pullback.fst _ _) (fun _ => pullback.snd _ _) hψo hψc he
      (fun j => by rw [hF j]; exact IsPullback.of_hasPullback U.hom π) hβ hef ?_
    rintro j x ⟨y, hy⟩
    obtain ⟨i, a, rfl⟩ := hcov x
    have hxa : β (e i a) = ψ i (pullback.fst U.hom π a) := by
      rw [← Scheme.Hom.comp_apply, hβ, Scheme.Hom.comp_apply]
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (hψp i j) (pullback.fst U.hom π a) y
      (by rw [← hxa, hy])
    have ha : pullback.fst U.hom π a ∈ V i j := by
      have h0 : (V i j).ι z ∈ Set.range (V i j).ι := ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι] at h0; rwa [← hz]
    exact (hV i j a).1 ha
  · exact GlobalTheory.T.descentInvariant_of_chartwise_projection (Sp R) S X G₀ π f Φ U J e ψ β he hcov hef hβ hc

end GlobalTheory.Mum.ChartDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubleSpaceOfGenericFunctionFieldPair
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_dbl_of_genPair : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K),
    GenPair Y ψ₁ ψ₂ → ∃ (W : Dbl Y) (j : W.Z.functionField →+* K), j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  intro F _ Y K _ ψ₁ ψ₂ hg
  obtain ⟨h, hsp⟩ := GlobalTheory.T.genericPair_specializes_diagonal_genericPoint F Y K ψ₁ ψ₂ hg
  obtain ⟨Z, hZi, p₁, p₂, hZ, ζ, hci, hζ₁, hζ₂, hζg⟩ :=
    GlobalTheory.T.exists_reduced_closure_point_fibreSquare F Y K (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h
  haveI := hZi
  have hcomp : ζ ≫ Limits.pullback.lift p₁ p₂ hZ =
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst]; exact hζ₁.trans (Limits.pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Limits.pullback.lift_snd]; exact hζ₂.trans (Limits.pullback.lift_snd _ _ _).symm
  have hmem : Limits.pullback.diagonal Y.str (genericPoint Y.X) ∈ Set.range (Limits.pullback.lift p₁ p₂ hZ) := by
    have hcl : IsClosed (Set.range (Limits.pullback.lift p₁ p₂ hZ)) := hci.base_closed.isClosed_range
    refine hsp.mem_closed hcl ⟨ζ (IsLocalRing.closedPoint K), ?_⟩
    rw [← hcomp]
    first | rfl | exact (Scheme.Hom.comp_apply _ _ _).symm | simp
  obtain ⟨hproj, δ, hδc, hδ₁, hδ₂, hdiag⟩ := GlobalTheory.T.doubleSpace_of_closedImmersion_contains_diagonal F Y Z p₁ p₂ hZ hci hmem
  let W : Dbl Y :=
    { Z := Z, integral := hZi, p₁ := p₁, p₂ := p₂, δ := δ, str_eq := hZ, proj := hproj, closed := hδc,
      δ₁ := hδ₁, δ₂ := hδ₂, diag := hdiag }
  obtain ⟨j, hj₁, hj₂⟩ := GlobalTheory.T.exists_functionField_map_doubleSpace_genericPoint F Y W K ψ₁ ψ₂ ζ hζg hζ₁ hζ₂
  exact ⟨W, j, hj₁, hj₂⟩

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExternalTensorRigidifiedCubicalProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_externalTensor_rigidified_cubical_product : ∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (L₁ : RigLB G₁) (L₂ : RigLB G₂) (c₁ : CubicalStr G₁ L₁) (c₂ : CubicalStr G₂ L₂) (s₁ : SymGen G₁ L₁.L) (s₂ : SymGen G₂ L₂.L), s₁.IsGen → s₂.IsGen → LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s₁ (eSec G₁)) (LB.oneGen L₁.L) → LB.Gen.Corr L₂.L _ _ _ _ (LB.pullGen L₂.L _ _ s₂ (eSec G₂)) (LB.oneGen L₂.L) → ∃ (L : RigLB (G₁ ⊗ G₂)) (c : CubicalStr (G₁ ⊗ G₂) L) (s : SymGen (G₁ ⊗ G₂) L.L) (w : LB.Iso L.L (extLB L₁.L L₂.L (fst G₁ G₂).left (snd G₁ G₂).left)), s.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec (G₁ ⊗ G₂))) (LB.oneGen L.L) ∧ StrBox (fst G₁ G₂) (snd G₁ G₂) w L.rig L₁.rig L₂.rig c.t c₁.t c₂.t s s₁ s₂ := by
  first | exact @GlobalTheory.GrpBox.exists_prod | exact GlobalTheory.GrpBox.exists_prod | (intros; apply GlobalTheory.GrpBox.exists_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorisationThroughAbelianSubvarietyStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factorisation_through_abelianSubvariety : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), ∃ (C : AbVar K) (p : A ⟶ C) (i : C ⟶ B), Surjective p.hom.left ∧ IsClosedImmersion i.hom.left ∧ p ≫ i = f := by
  first | exact @GlobalTheory.AV.AbVar.exists_factor_abelianSubvariety | exact GlobalTheory.AV.AbVar.exists_factor_abelianSubvariety | (intros; apply GlobalTheory.AV.AbVar.exists_factor_abelianSubvariety <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleDeeperLevelSiegelCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_etale_deeper_level_siegel_cover : ∀ (h n N : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (b : TBase B' N) (j : B →+* B') (S : Scheme.{0}) (s' : S ⟶ Sp B') (c : SiegPre h n ζ (s' ≫ spMap j)), 3 ≤ n → Odd N → n ∣ N → j ζ = (b.ζ : B') ^ (N / n) → c.Principal → ∃ (S₁ : Scheme.{0}) (π : S₁ ⟶ S) (C : SiegPre h N (b.ζ : B') (π ≫ s')), IsFinite π ∧ Etale π ∧ Surjective π ∧ SRel C c (N / n) 1 π ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (C' : SiegPre h N (b.ζ : B') (t ≫ s')), SRel C' c (N / n) 1 t → ∃! t₁ : T ⟶ S₁, t₁ ≫ π = t ∧ SiegPB C' C t₁ := by
  first | exact @GlobalTheory.SiegCover.exists_levelCover | exact GlobalTheory.SiegCover.exists_levelCover | (intros; apply GlobalTheory.SiegCover.exists_levelCover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteHomogeneousGeneratorsGradedSubgroup
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmpGen

variable {K : Type} [CommRing K] {D : ℕ}

def twist (x : Fin (D + 1) → K) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial K :=
  MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial K)) (fun l => Polynomial.C (x l) * Polynomial.X)

theorem twist_homog (x : Fin (D + 1) → K) (n : ℕ) (T : MvPolynomial (Fin (D + 1)) ℤ)
    (hT : T.IsHomogeneous n) :
    twist x T = Polynomial.C (aeval x T) * Polynomial.X ^ n := by
  unfold twist
  rw [coe_eval₂Hom, eval₂_eq', aeval_def, eval₂_eq', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have := hT (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, map_mul, map_prod, map_pow]
  simp
  ring

def Good (c : ℕ) (A : ℕ → AddSubgroup K) (p : Polynomial K) : Prop :=
  (∀ b < c, p.coeff b = 0) ∧ ∀ q, p.coeff (q + c) ∈ A q

theorem good_zero (c : ℕ) (A : ℕ → AddSubgroup K) : Good c A 0 :=
  ⟨fun _ _ => by simp, fun q => by simpa using (A q).zero_mem⟩

theorem good_add {c : ℕ} {A : ℕ → AddSubgroup K} {p r : Polynomial K} (hp : Good c A p) (hr : Good c A r) :
    Good c A (p + r) :=
  ⟨fun b hb => by simp [hp.1 b hb, hr.1 b hb], fun q => by simpa using (A q).add_mem (hp.2 q) (hr.2 q)⟩

theorem good_int_mul {c : ℕ} {A : ℕ → AddSubgroup K} {p : Polynomial K} (hp : Good c A p) (a : ℤ) :
    Good c A ((a : Polynomial K) * p) := by
  refine ⟨fun b hb => ?_, fun q => ?_⟩
  · rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, hp.1 b hb, mul_zero]
  · rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, ← zsmul_eq_mul]
    exact zsmul_mem (hp.2 q) a

theorem good_mul_X {c : ℕ} {A : ℕ → AddSubgroup K} {p : Polynomial K} (hp : Good c A p) (a : K)
    (hA : ∀ q, ∀ f ∈ A q, a * f ∈ A (q + 1)) :
    Good c A (Polynomial.C a * Polynomial.X * p) := by
  refine ⟨fun b hb => ?_, fun q => ?_⟩
  · rw [mul_assoc, Polynomial.coeff_C_mul]
    rcases b with _ | b
    · simp
    · rw [Polynomial.coeff_X_mul, hp.1 b (by omega), mul_zero]
  · rw [mul_assoc, Polynomial.coeff_C_mul]
    rcases q with _ | q
    · rcases c with _ | c
      · simp
      · rw [zero_add, Polynomial.coeff_X_mul, hp.1 c (by omega), mul_zero]; exact (A 0).zero_mem
    · rw [show q + 1 + c = (q + c) + 1 by omega, Polynomial.coeff_X_mul]
      exact hA q _ (hp.2 q)

theorem good_twist_mul (x : Fin (D + 1) → K) {c : ℕ} {A : ℕ → AddSubgroup K}
    (hA : ∀ q l, ∀ f ∈ A q, x l * f ∈ A (q + 1)) (r : MvPolynomial (Fin (D + 1)) ℤ) :
    ∀ p : Polynomial K, Good c A p → Good c A (twist x r * p) := by
  induction r using MvPolynomial.induction_on with
  | C a => intro p hp; simpa [twist] using good_int_mul hp a
  | add r s hr hs => intro p hp; rw [map_add, add_mul]; exact good_add (hr p hp) (hs p hp)
  | mul_X r l hr =>
    intro p hp
    have h1 : twist x (r * X l) * p = twist x r * (Polynomial.C (x l) * Polynomial.X * p) := by
      simp [twist]; ring
    rw [h1]
    exact hr _ (good_mul_X hp (x l) (hA · l))

theorem exists_finite_homogeneous_generators : ∀ (K : Type) [CommRing K] (D c : ℕ) (x : Fin (D + 1) → K) (ι : Type) [Fintype ι] (w : ι → K) (Λ : ℕ → AddSubgroup K), (∀ q l, ∀ f ∈ Λ q, x l * f ∈ Λ (q + 1)) → (∀ q, ∀ f ∈ Λ q, ∃ T : ι → MvPolynomial (Fin (D + 1)) ℤ, (∀ i, (T i).IsHomogeneous (q + c)) ∧ f = ∑ i, aeval x (T i) * w i) → ∃ G : Finset (ℕ × K), (∀ g ∈ G, g.2 ∈ Λ g.1) ∧ ∀ q, Λ q ≤ AddSubgroup.closure {f | ∃ g ∈ G, ∃ α : Fin (D + 1) → ℕ, ∑ l, α l + g.1 = q ∧ f = (∏ l, x l ^ α l) * g.2} := by
  intro K _ D c x ι _ w Λ hx hw
  classical
  letI : Module (MvPolynomial (Fin (D + 1)) ℤ) (Polynomial K) := (twist x).toModule
  have hsmul : ∀ (r : MvPolynomial (Fin (D + 1)) ℤ) (p : Polynomial K), r • p = twist x r * p := fun _ _ => rfl
  let S : Set (ℕ × K) := {g | g.2 ∈ Λ g.1}
  let v : ℕ × K → Polynomial K := fun g => Polynomial.C g.2 * Polynomial.X ^ (g.1 + c)
  let M : Submodule (MvPolynomial (Fin (D + 1)) ℤ) (Polynomial K) :=
    Submodule.span (MvPolynomial (Fin (D + 1)) ℤ) (v '' S)
  let ψ : (ι → MvPolynomial (Fin (D + 1)) ℤ) →ₗ[MvPolynomial (Fin (D + 1)) ℤ] Polynomial K :=
    Fintype.linearCombination (MvPolynomial (Fin (D + 1)) ℤ) (fun i => Polynomial.C (w i))
  have hle : M ≤ LinearMap.range ψ := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨q, f⟩, hf, rfl⟩
    obtain ⟨T, hT, rfl⟩ := hw q f hf
    refine ⟨T, ?_⟩
    simp only [ψ, v, Fintype.linearCombination_apply, hsmul, twist_homog x _ _ (hT _), map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul]; ring
  have hfg : M.FG := by
    have h1 : (M.comap ψ).FG := IsNoetherian.noetherian _
    have h2 := h1.map ψ
    rwa [Submodule.map_comap_eq_of_le hle] at h2
  obtain ⟨S0, hS0⟩ := hfg
  have hT : ∀ s ∈ S0, ∃ T : Finset (Polynomial K), ↑T ⊆ v '' S ∧
      s ∈ Submodule.span (MvPolynomial (Fin (D + 1)) ℤ) (T : Set (Polynomial K)) := fun s hs =>
    Submodule.mem_span_finite_of_mem_span (by
      have h := Submodule.subset_span (R := MvPolynomial (Fin (D + 1)) ℤ) (s := (S0 : Set (Polynomial K))) hs
      rw [hS0] at h; exact h)
  choose! Tf hTf hsT using hT
  obtain ⟨G, hGS, hGT⟩ := (Finset.subset_set_image_iff (s := S) (t := S0.biUnion Tf) (f := v)).mp (by
    intro p hp
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe] at hp
    obtain ⟨s, hs, hp⟩ := hp
    exact hTf s hs hp)
  refine ⟨G, fun g hg => hGS hg, ?_⟩
  set A : ℕ → AddSubgroup K := fun q => AddSubgroup.closure
    {f | ∃ g ∈ G, ∃ α : Fin (D + 1) → ℕ, ∑ l, α l + g.1 = q ∧ f = (∏ l, x l ^ α l) * g.2} with hAdef
  have hA : ∀ q l, ∀ f ∈ A q, x l * f ∈ A (q + 1) := by
    intro q l f hf
    induction hf using AddSubgroup.closure_induction with
    | mem f hf =>
      obtain ⟨g, hg, α, hα, rfl⟩ := hf
      refine AddSubgroup.subset_closure ⟨g, hg, α + Pi.single l 1, ?_, ?_⟩
      · simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
        simp; omega
      · have : ∏ i, x i ^ (Pi.single l 1 : Fin (D + 1) → ℕ) i = x l := by
          rw [Finset.prod_eq_single l (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
          simp
        simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, this]; ring
    | zero => simpa using (A (q + 1)).zero_mem
    | add a b _ _ ha hb => rw [mul_add]; exact (A (q + 1)).add_mem ha hb
    | neg a _ ha => rw [mul_neg]; exact (A (q + 1)).neg_mem ha
  have hgood : ∀ p ∈ Submodule.span (MvPolynomial (Fin (D + 1)) ℤ) (v '' (G : Set (ℕ × K))), Good c A p := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨g, hg, rfl⟩ := hp
      refine ⟨fun b hb => ?_, fun q => ?_⟩
      · simp only [v, Polynomial.coeff_C_mul_X_pow]; rw [if_neg (by omega)]
      · simp only [v, Polynomial.coeff_C_mul_X_pow]
        by_cases hq : q = g.1
        · subst hq; rw [if_pos rfl]
          exact AddSubgroup.subset_closure ⟨g, hg, 0, by simp, by simp⟩
        · rw [if_neg (by omega)]; exact (A q).zero_mem
    | zero => exact good_zero c A
    | add a b _ _ ha hb => exact good_add ha hb
    | smul r a _ ha => rw [hsmul]; exact good_twist_mul x hA r a ha
  intro q f hf
  have hmem : v (q, f) ∈ Submodule.span (MvPolynomial (Fin (D + 1)) ℤ) (v '' (G : Set (ℕ × K))) := by
    rw [← Finset.coe_image, hGT]
    have : v (q, f) ∈ M := Submodule.subset_span ⟨(q, f), hf, rfl⟩
    rw [← hS0] at this
    refine Submodule.span_le.mpr ?_ this
    intro s hs
    exact Submodule.span_mono (by
      intro p hp; simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]; exact ⟨s, hs, hp⟩) (hsT s hs)
  have h := (hgood _ hmem).2 q
  simp only [v, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at h
  exact h

end GlobalTheory.HSAmpGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalCoverSymmBundlePowerDecomposit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
noncomputable section

namespace GlobalTheory.CoverDec

theorem exists_cover_sqDec : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ (L M : LB G.left), L.IsLB → M.IsLB → RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → RelAmple ((Over.pullback (jK R)).obj G) (M.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (_ : IsLocalRing R') (ρ : R →+* R') (G' : Over (Sp R')) (_ : GrpObj G') (π : G'.left ⟶ G.left), Function.Injective ρ ∧ ρ.Finite ∧ IsGrpPullback G' G (spMap ρ) π ∧ SqDec G' (L.pull π) (M.pull π) := by
  intro R _ _ _ _ hc G _ hG hAb L M hL hM hAL hAM hSL hSM
  have sL := GlobalTheory.T.symmetric_lineBundle_pullback_baseChange _ _ G (jK R) L hL hSL
  have sM := GlobalTheory.T.symmetric_lineBundle_pullback_baseChange _ _ G (jK R) M hM hSM
  obtain ⟨K', _, _, _, hD⟩ := GlobalTheory.T.exists_squareDecomposition_finiteExtension_ampleBundle (FractionRing R) ((Over.pullback (jK R)).obj G) hAb _ _
    (pull_isLB hL _) (pull_isLB hM _) hAL hAM sL sM
  obtain ⟨R', _, _, _, _, _, ρ, τ, hinj, hfin, hcomp⟩ := GlobalTheory.T.exists_finite_normal_noetherian_cover_fractionFieldExt R hc K'
  obtain ⟨π₀, hP, hLL⟩ := GlobalTheory.T.genericFibre_baseChange_grpPullback_domains R R' ρ (τ.comp (algebraMap (FractionRing R) K')) hcomp G
  have hD' := GlobalTheory.SqDecTransport.transport (FractionRing R) (FractionRing R') K' (FractionRing R')
    (τ.comp (algebraMap (FractionRing R) K')) (algebraMap (FractionRing R) K') (RingHom.id _) τ rfl
    ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) π₀ hP _ _ _ _
    (pull_isLB hL _) (pull_isLB hM _) (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hM _) _)
    (hLL L hL) (hLL M hM) hD
  have h1 := GlobalTheory.T.squareDecomposition_of_baseChange_along_identity _ _ _ _ (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hM _) _) hD'
  have h2 := GlobalTheory.T.squareDecomposition_extends_from_genericFibre_semiAbelian R' ((Over.pullback (spMap ρ)).obj G) (IsSemiAbelian.pullback (spMap ρ) G hG) _ _
    (pull_isLB hL _) (pull_isLB hM _) h1
  exact ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ρ,
    (Over.pullback (spMap ρ)).obj G, inferInstance, pullback.fst G.hom (spMap ρ), hinj, hfin,
    isGrpPullback_pullback G (spMap ρ), h2⟩

end GlobalTheory.CoverDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateEquivariantBijectionTwist
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Mum GlobalTheory.Mum.Conj in

theorem GlobalTheory.Mum.exists_eqv_conj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E, Eqv D.toPre A (Kb R) N lab E → (∀ τ : Kb R →ₐ[FractionRing R] Kb R, LabExt τ lab lab) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ E', Eqv D.toPre A (Kb R) N lab E' ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre N) s, F₀.Over s → SecTw σ (E s) (E' s) := by
  intro R _ _ _ _ D A N _ lab E hE hlab σ
  have hσ : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  let σe : Kb R ≃ₐ[FractionRing R] Kb R := AlgEquiv.ofBijective σ hσ
  let τ : Kb R →ₐ[FractionRing R] Kb R := σe.symm.toAlgHom
  have hστ : σ.comp τ = AlgHom.id _ _ := AlgHom.ext fun x => σe.apply_symm_apply x
  have hστ' : ∀ x, σ (τ x) = x := fun x => σe.apply_symm_apply x
  refine ⟨fun s => secTw A N σ (E (famTw D.toPre N τ s)), ⟨?_, ?_, ?_, hE.onto, hE.frame, hE.lift, ?_⟩, ?_⟩
  · exact (GlobalTheory.T.pullbackThetaSectionsGaloisTwist_bijective R A N σ).comp (hE.bij.comp (GlobalTheory.T.pullbackThetaFamilyGaloisTwist_bijective R D.toPre N τ))
  · intro s s' s'' h j
    exact GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_add R A N σ _ _ _ (hE.add _ _ _ (GlobalTheory.T.pullbackThetaFamilyGaloisTwist_chart_add R D.toPre N τ _ _ _ h)) j
  · intro c s s' h j
    have := GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_semilinear R A N σ (τ c) _ _ (hE.smul (τ c) _ _ (GlobalTheory.T.pullbackThetaFamilyGaloisTwist_semilinear_smul R D.toPre N τ c _ _ h)) j
    rwa [hστ'] at this
  · intro p w θ s s' hw hθ hφ
    obtain ⟨p₀, hp₀⟩ := qkExtExists R D.toPre (Kb R) (Kb R) τ.toRingHom (fun r => τ.commutes r) N p
    have hx := hlab τ p p₀ hp₀
    exact GlobalTheory.T.thetaGroupAction_pullbackThetaSectionsGaloisTwist R A N σ τ hστ θ _ _ (hE.act p₀ (frTw D.toPre τ hp₀ w) (thTw A N τ θ) _ _
      (GlobalTheory.T.isSymmetricFrame_pullbackMumfordFrameGaloisTwist R D.toPre N τ p p₀ hp₀ w hw) (GlobalTheory.T.symmetricLift_galoisTwist_of_conjugatePoint R A N τ _ _ θ hθ hx) (GlobalTheory.T.operator_relation_pullback_galois_automorphism R D.toPre N τ p p₀ hp₀ w s s' hφ))
  · intro F₀ s hs
    show SecTw σ (E s) (secTw A N σ (E (famTw D.toPre N τ s)))
    rw [GlobalTheory.T.pullbackThetaFamilyGaloisTwist_fixes_integralFamily R _ D.toPre N τ F₀ s hs]
    exact GlobalTheory.T.pullbackThetaSectionsGaloisTwist_isConjugate R A N σ (E s)
end

