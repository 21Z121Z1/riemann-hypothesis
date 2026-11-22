import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2922
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2989
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3120
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2972
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2900
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2716
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3121
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2923
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedDescendFiniteEtaleExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

set_option maxHeartbeats 1000000 in

theorem FrameCarried.descend_finiteEtale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁), FinExt ρ₁ → ρ₁.Etale → ∀ (V₀ : G.left.Opens) (y : G.left), y ∈ V₀ → ∀ τ : ∀ k : U'.LG.L.ι, Γ(pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀) ⊓ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ U'.LG.L.U k)ˣ, FrameAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ → (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → ∀ f' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), f' ≫ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ≫ a.act σ → f' ≫ (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) → FrameCarriedAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ _ (Classical.choose hP.lg) f') → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact R₁ _ _ _ ρ₁ hF₁ hE₁ V₀ y hy τ hτ hτc
  have hL : U'.LG.L.IsLB := U'.LG.isLB
  haveI : IsNoetherianRing R := hB.1.1
  have hfl : ρ₁.Flat := (RingHom.Etale.iff_flat_and_formallyUnramified.1 hE₁).1
  obtain ⟨-, -, -, hqs, -, -, -, d, b, hb⟩ := GlobalTheory.finiteFlat_proper_baseChange_facts R R₁ ρ₁ hF₁.2.1 hF₁.2.2 hfl
    G'.left G'.left (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁)) (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁)) (𝟙 _) (𝟙 _)
    (G'.hom ≫ spMap ρ) (pullback.snd _ _) (pullback.fst _ _) (pullback.fst _ _) (IsPullback.of_hasPullback _ _)
    (IsPullback.id_vert _) inferInstance
  have hβf : IsFinite β :=
    MorphismProperty.of_isPullback (P := @IsFinite) hβ.1.flip ((IsFinite.SpecMap_iff _).2 hF.2.2)
  have hβc : IsClosedMap β.base := β.isClosedMap
  have hGfl : Flat G.hom := by haveI := hS.smooth; infer_instance
  obtain ⟨V₁, hV₁a, hyV₁, hV₁⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens) hy
  have hOa : IsAffineOpen (β ⁻¹ᵁ V₁) := IsAffineOpen.preimage hV₁a β
  have hOW : β ⁻¹ᵁ V₁ ≤ β ⁻¹ᵁ V₀ := fun x hx => hV₁ hx
  obtain ⟨s, hs, hdec⟩ := GlobalTheory.T.frame_coefficients_descend_finiteFree_affineOpen R R₁ ρ₁ d b hb G'.left (G'.hom ≫ spMap ρ) U'.LG.L hL (β ⁻¹ᵁ V₀) (β ⁻¹ᵁ V₁) hOW hOa τ hτ
  have hcar : ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre)
      (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U',
      PullOver hD h → ∀ l, SecCarriedOver U'.LG.L (β ⁻¹ᵁ V₁) (s l) _ (Classical.choose hP.lg) := by
    intro σ h bc hbc hP hPO
    refine GlobalTheory.T.carried_section_of_frame_carried_along_lifts R R₁ ρ₁ d b hb G'.left (G'.hom ≫ spMap ρ) U'.LG.L (β ⁻¹ᵁ V₀) (β ⁻¹ᵁ V₁) hOW τ s hdec _
      (Classical.choose hP.lg) ?_ ?_
    · rw [hbc, ← hβ.1.w, ← Category.assoc, hact]
    · intro f' h1 h2
      exact hτc σ h bc hbc hP hPO f' (h1.trans (by rw [hbc])) h2
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      obtain ⟨c, hc, -⟩ := hb 1
      simp at hc
    · exact h0
  have key : ∃ l, ∀ (z : G'.left) (k : U'.LG.L.ι), β z = y → z ∈ U'.LG.L.U k →
      IsUnit (gs (𝟙 G'.left) z (β ⁻¹ᵁ V₁ ⊓ U'.LG.L.U k) (s l k)) := by
    by_cases hne : ∃ z₀, β z₀ = y
    · obtain ⟨z₀, hz₀⟩ := hne
      obtain ⟨z', hz'⟩ := hqs z₀
      have hz'O : (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) z' ∈ β ⁻¹ᵁ V₁ := by
        show β ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)).base z') ∈ V₁
        rw [hz', hz₀]; exact hyV₁
      obtain ⟨l, hl⟩ := GlobalTheory.T.exists_frameCoefficient_unitGerms_finiteFree R R₁ ρ₁ d b G'.left (G'.hom ≫ spMap ρ) U'.LG.L hL (β ⁻¹ᵁ V₀) (β ⁻¹ᵁ V₁) hOW τ s hs
        hdec z' hz'O
      have hl' : ∀ k, z₀ ∈ U'.LG.L.U k → IsUnit (gs (𝟙 G'.left) z₀ (β ⁻¹ᵁ V₁ ⊓ U'.LG.L.U k) (s l k)) := by
        intro k hk
        have := hl k (by show (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)).base z' ∈ _; rw [hz']; exact hk)
        revert this
        show IsUnit (gs (𝟙 G'.left) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)).base z') _ _) → _
        rw [hz']; exact id
      refine ⟨l, fun z k hz hk => ?_⟩
      obtain ⟨σ, hσ⟩ := GlobalTheory.T.galois_acts_transitively_fibres_flat_baseChange R R' ρ hF.2.2 hG G.left G'.left G.hom G'.hom β hGfl hβ.1 a.act
        (fun σ => (a.cart σ).1.w) hact z₀ z (hz₀.trans hz.symm)
      obtain ⟨h, bc, hbc, hP, hPO⟩ := a.unif σ
      obtain ⟨k₀, hk₀⟩ := exists_chart hL z₀
      have hz₀O : z₀ ∈ β ⁻¹ᵁ V₁ := show β z₀ ∈ V₁ from hz₀ ▸ hyV₁
      have hφ : (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ = z := by rw [hbc]; exact hσ
      subst hφ
      have hzO : (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ ∈ β ⁻¹ᵁ V₁ :=
        show β _ ∈ V₁ from hz ▸ hyV₁
      have e := hcar σ h bc hbc hP hPO l z₀ k k₀ hz₀O hzO hk₀ hk
      have hu : IsUnit (gs (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ _ (s l k)) := by
        rw [e]; exact (Units.isUnit _).mul (hl' k₀ hk₀)
      rw [gs_eq_map_gs (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ (β ⁻¹ᵁ V₁ ⊓ U'.LG.L.U k) ⟨hzO, hk⟩] at hu
      exact (isUnit_map_iff _ _).1 hu
    · push_neg at hne
      exact ⟨⟨0, hd⟩, fun z k hz _ => absurd hz (hne z)⟩
  obtain ⟨l, hl⟩ := key
  obtain ⟨V, hyV, -, T, hT, hTc⟩ :=
    GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre G'.left G.left β hβc U'.LG.L hL V₁ (s l) (hs l) y hyV₁ hl
  exact ⟨V, hyV, T, hT, fun σ h bc hbc hP hPO => hTc _ _ (hcar σ h bc hbc hP hPO l)⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedTorsionPoint_torusExtension_eq_of_liesOver : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g g' : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (w' : Frm D.toPre (FractionRing V) 1 g'.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → (∃ o, GtPtF.IsNsmul N g' o ∧ o.IsZero) → w.IsGen → w'.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → LiesOver U.toUnifPre w₀ g' w' x fr → g = g' ∧ ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J := by
  first | exact @GlobalTheory.Poinc.Sep.LiesUniq.eq_of_liesOver | exact GlobalTheory.Poinc.Sep.LiesUniq.eq_of_liesOver | (intros; apply GlobalTheory.Poinc.Sep.LiesUniq.eq_of_liesOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusEndomorphismUnique
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem frob_isFrob_unique : ∀ (K : Type) [Field K] [Fintype K] (A : AbVar K),
    IsFrob (frob A) ∧ ∀ π : End A, IsFrob π → π = frob A := by
  intro K _ _ A
  have hex : ∃ π : End A, IsFrob π := by
    obtain ⟨π, hπ, -⟩ := GlobalTheory.T.exists_frobenius_endomorphism K A
    exact ⟨π, hπ⟩
  have hf : IsFrob (frob A) := by
    unfold frob
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨hf, fun π hπ => ?_⟩
  apply GlobalTheory.AV.AbVar.ext_of_pt_eq
  intro x
  rw [hπ x, hf x]

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelIdealEqKernelRelativeFrobenius
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem frobKerIdeal_le_kerIdeal_relFrob (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) :
    frobKerIdeal p R (G.A n) ≤ kerIdeal ((relFrob h G).app n) := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  have ha' : counit (R := R) a = 0 := ha
  have hb : (frobProj h G).app n a ∈ augIdeal R ((frobTwist h G).A n) := by
    change counit (R := R) ((frobProj h G).app n a) = 0
    rw [SemiBialgHom.counit_map, ha', map_zero]
  show a ^ p ∈ _
  rw [← relFrob_app_frobProj h n a]
  exact Ideal.mem_map_of_mem _ hb

theorem frobKerIdeal_eq_kerIdeal_relFrob (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) :
    frobKerIdeal p R (G.A n) = kerIdeal ((relFrob h G).app n) :=
  le_antisymm (frobKerIdeal_le_kerIdeal_relFrob p R h G n)
    (kerIdeal_relFrob_le_frobKerIdeal p R h G n)

end GlobalTheory.PDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullLevelSelfDualLattice
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop

namespace GlobalTheory.CovTop.MassBridge

theorem mass_bridge : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) μ 𝓕 → letI : IsCMField D.host.E := D.host.isCMField_hostE; ∃ (G : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (Ψ : Finset (D.host.E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ D.R.r) (p0 : Ψ → ℕ) (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)), 2 ≤ D.R.r ∧ GlobalTheory.UCls.Unr D.host.E ∧ GlobalTheory.UCls.SelfDualLat G Λ ∧ (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) ∧ (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) ∧ GlobalTheory.SUVol.IsSReps G (Λ : Set (Fin D.R.r → D.host.E)) 1 s ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f ∧ (letI : MeasurableSpace (GlobalTheory.SUVol.realSU Ψ G) := borel _; haveI : BorelSpace (GlobalTheory.SUVol.realSU Ψ G) := ⟨rfl⟩; ENNReal.ofReal (c ^ (D.R.f * D.R.r ^ 2)) * ∑' j, MeasureTheory.covolume (GlobalTheory.SUVol.inReal Ψ G (GlobalTheory.SUVol.ratStab G (Λ : Set (Fin D.R.r → D.host.E)) (s j))) (GlobalTheory.SUVol.realSU Ψ G) (GlobalTheory.SUVol.riemHaar Ψ G x) ≤ μ 𝓕) := by
  obtain ⟨c, hc0, hc1, hB⟩ := bridge_bound
  refine ⟨c, hc0, hc1, fun D Tu Cl t0 hCl i μ 𝓕 hμ => ?_⟩
  obtain ⟨G, Λ, Ψ, x, p0, J, s, h, hF, hL⟩ := GlobalTheory.MassLink.data_link D Tu Cl t0 hCl i
  exact ⟨G, Λ, Ψ, x, p0, J, s, hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2.1, hF.2.2.2.2.2.2,
    hB D Tu Cl t0 hCl i μ 𝓕 hμ G Λ Ψ x p0 J s h hF hL⟩

end GlobalTheory.CovTop.MassBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisConjQExpansionFamilyDiagOneUnitStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_conj_qExpansion_family_diag_one_unit : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ) (κ κ' : Emb F → ℕ) (y : Fin 2 → ZMod N), ZetaAct g N a → (∀ i j : Emb F, (∀ x : F, g ((i x : ℝ) : ℂ) = ((j x : ℝ) : ℂ)) → κ' j = κ i) → y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QConj g N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) (hfun (2 * s) (twist N L ((α * dg a : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ' (wB N (vmul y (α * dg a)))) := by
  first | exact @GlobalTheory.HilbFam.GalFamily.qConj_family | exact GlobalTheory.HilbFam.GalFamily.qConj_family | (intros; apply GlobalTheory.HilbFam.GalFamily.qConj_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientSmoothBaseChangeIsoClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem quotient_smooth_and_baseChange_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) → ∀ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left) (hX : π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ), IsAffineHom π → Surjective π → (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ x : H.toScheme, spMap ρ (G'.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G'.hom) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap ρ)) := by
  intro R _ _ _ hR R' _ _ _ ρ hρ hΓ D D' hD A' G' _ _ hG U' a H hH _ X π hX hπ _ hinv hfib hsec x hx
  obtain ⟨_, rfl⟩ : ∃ _ : Algebra R R', algebraMap R R' = ρ := ⟨ρ.toAlgebra, rfl⟩
  have hw := fun σ => (a.cart σ).1.w
  obtain ⟨Y, φ, hY, hφ, hsucc, hσ⟩ := @GlobalTheory.FormalModel.exists_model R _ _ _ hR R' _ _ _ _ D D' hD A' G' _ _ U' a
  obtain ⟨V, W, hxV, hV, hW, hVW⟩ := @GlobalTheory.T.galois_descent_open_invariant_subscheme R _ _ _ R' _ _ _ _ hR hρ hΓ G' a.act hw a.act_one a.act_mul H hH X π hX hπ hinv
    hfib hsec Y φ hY hφ hsucc hσ x hx
  obtain ⟨C', _, _, _, _, actC, C, j, l, hj, hl, hlV, hP, hjs, hls, hact, hlin, hC⟩ := @GlobalTheory.T.galoisQuotient_affineOpen_spec_invariants R _ _ _ R' _ _ _ _ hR hρ hΓ G'
    a.act hw a.act_one a.act_mul H hH X π hX hπ hinv hfib hsec V hV
  have hr : Set.range j = π ⁻¹' (V : Set X.left) := by
    rw [← hlV, ← Scheme.Pullback.range_fst π l, ← hP.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, hP.isoPullback.hom.surjective.range_eq, Set.image_univ]
  have hr' : (j ≫ H.ι).opensRange = H.ι ''ᵁ (π ⁻¹ᵁ V) := by
    ext1
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hr]
    rfl
  obtain ⟨O, _, _, i', hO, h₁, h₂, h₃⟩ := @GlobalTheory.T.exists_invariant_maps_affineOpen_smoothModel R _ R' _ _ _ G' a.act Y φ hY hφ hsucc hσ C' _ _ _ _ actC (j ≫ H.ι) _
    (by rw [Category.assoc, hjs]) (fun σ => by rw [hact, Category.assoc]) W hW (by rw [hVW, hr'])
  have : IsNoetherianRing R := hR.1.1
  have : IsNoetherianRing R' := hρ.1.1
  have : Module.Finite R R' := RingHom.finite_algebraMap.1 hρ.2.2
  obtain ⟨i, k₁, k₂, k₃⟩ := @GlobalTheory.T.exists_compatible_maps_mod_pow_maximalIdeal_base_alt R _ _ R' _ _ _ _ _ C' _ _ _ _ _ (fun σ => actC σ) O _ _ i' h₁ h₂ h₃
  have : Algebra.FiniteType R' C' := by
    have := U'.smooth
    have : LocallyOfFiniteType (spMap (algebraMap R' C')) := by rw [← hjs]; infer_instance
    exact RingHom.finiteType_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this)
  obtain ⟨hft, -, f, hf, hf₁, hf₂, hiso⟩ := GlobalTheory.T.invariants_of_trivial_on_thickenings_alt R hR.1 R' hρ.2.1 hΓ C' actC hlin O i k₁ k₂ k₃ C hC
  obtain ⟨p, rfl⟩ : x ∈ Set.range j := by rw [hr]; exact hxV
  let q : Sp C := spMap (algebraMap C C') p
  have hq : l q = π (j p) := by rw [← Scheme.Hom.comp_apply, ← hP.w, Scheme.Hom.comp_apply]
  have hq' : q.asIdeal.comap (algebraMap R C) = maximalIdeal R := by
    have : spMap (algebraMap R C) q = closedPoint R := by
      rw [← hx, ← hls, Scheme.Hom.comp_apply, hq, ← Scheme.Hom.comp_apply, hX]
      simp only [Scheme.Hom.comp_apply]
    exact congrArg PrimeSpectrum.asIdeal this
  obtain ⟨g, hg, hsm⟩ := @GlobalTheory.T.exists_smooth_away_of_quotient_pow_equiv' R _ _ _ O C _ _ _ _ hO hft hiso q.asIdeal q.isPrime hq'
  have hfq : f ∉ q.asIdeal := fun h => q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := q.asIdeal.sub_mem h (Ideal.map_le_iff_le_comap.2 hq'.ge hf)
    rwa [sub_sub_cancel] at this))
  rw [← hq]
  exact @GlobalTheory.T.isIso_baseChange_over_basicOpen_of_tensor_bijective R R' _ _ _ X H.toScheme π (H.ι ≫ G'.hom) (by rw [hX, Category.assoc]) C' _ _ _ _ C j l hl hP hjs hls f g hf₁ hf₂
    hsm q hfq hg

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratesSectionsOfThetaSymmetricFunctionsNeZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generates_sections_of_thetaSymmetricFunctions_ne_zero : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (x : Sp Ω ⟶ S) (θ : SecAt G L x) (e : Fin N → Ω), Odd m → N = m ^ (4 * g) → PolFib G L g x → SymAt G L ρ m x θ e → (∃ j, e j ≠ 0) → IsGenSec G L ((1 : ℕ) : ℤ) θ := by
  first | exact @GlobalTheory.UMin.GenSym.isGenSec_of_symAt | exact GlobalTheory.UMin.GenSym.isGenSec_of_symAt | (intros; apply GlobalTheory.UMin.GenSym.isGenSec_of_symAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreeProjectionFormulaSelfInterPow
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.PullPow

theorem gdeg_pull_and_isSelfInter_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → (∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ L : HermLB p, gdeg (L.pull π hπ) D = (π.residueDegree (genericPoint Y) : ℝ) * gdeg L D) ∧ ∀ (L : HermLB p) (n : ℕ) (a : ℝ), L.IsSelfInter a → (L.pow n).IsSelfInter ((n : ℝ) ^ (D + 1) * a) := by
  intro hC k _ X _ p D hX
  refine ⟨fun Y _ q hY π hπ hη hδ L => GlobalTheory.CovTest.gdegPull k X Y p q D hX hY π hπ hη hδ L, ?_⟩
  intro L n a ha
  exact GlobalTheory.SelfInterPow.isSelfInter_pow hC k X p D hX L a ha n

end GlobalTheory.HSAmp.PullPow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTateLevelConditionDescendsGaloisCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_tate_level_condition_descends_galois_cover : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀) (N : ℕ) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (eta : D.La → (𝟙_ (Over X) ⟶ A)) (eta₀ : D.La → (𝟙_ (Over Y) ⟶ A₀)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ y, (eta y).left ≫ φ = π ≫ (eta₀ y).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A₀) (fun c g => g ≫ act₀.act c) (fun n g g' z => Out.WeilIs A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta₀ y = I.ev N y) := by
  first | exact @GlobalTheory.UPel.HT.geom_descends_galoisCover | exact GlobalTheory.UPel.HT.geom_descends_galoisCover | (intros; apply GlobalTheory.UPel.HT.geom_descends_galoisCover; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedFirstChernSumIndepStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_first_chern_sum_indep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl fl' : Vert.Flag E 2), c1F hX σ (VMetric.grLB fl 0 H) + c1F hX σ (VMetric.grLB fl 1 H) = c1F hX σ (VMetric.grLB fl' 0 H) + c1F hX σ (VMetric.grLB fl' 1 H) := by
  first | exact @GlobalTheory.c1F_grLB_add_grLB_flag_indep | exact GlobalTheory.c1F_grLB_add_grLB_flag_indep | (intros; apply GlobalTheory.c1F_grLB_add_grLB_flag_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedLinePotentialHessianDetOwnRowStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gradedLine_potential_hessian_det_own_row : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m), (G (bsL ε w) x.1).PosDef → MContDiffAt 2 (fun v => G v x.1) (bsL ε w) → Fintype.card {j : Cell m // j.root = x} = m x.1 - 1 - x.2 ∧ (Matrix.of fun a b : {j : Cell m // j.root = x} => -leviForm (cellPot ε G x) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).det = (((G (bsL ε w) x.1).det.re / (leadMinor (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2).re / grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 ^ ((m x.1 - 1 - x.2 : ℕ) + 1) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.FlagCell2.row_levi_det | exact GlobalTheory.FlagCell2.row_levi_det | (intros; apply GlobalTheory.FlagCell2.row_levi_det <;> assumption)
end

