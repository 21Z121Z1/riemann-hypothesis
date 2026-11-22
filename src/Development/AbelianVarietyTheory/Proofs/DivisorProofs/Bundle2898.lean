import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeGeneratorTopFormsTensorLocalizationOrd
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2800
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagSpannedFrameStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_spanned_frame : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (v : Fin m → Γ(F, ⊤)), IsFrame v → ∃ fl : Vert.Flag F m, Spans fl ⊤ v := by
  first | exact @GlobalTheory.FlagCell.exists_flag_spans_of_frame | exact GlobalTheory.FlagCell.exists_flag_spans_of_frame | (intros; apply GlobalTheory.FlagCell.exists_flag_spans_of_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatChartEtaleOfQuasiFiniteAtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flat_chart_etale_of_quasiFiniteAt_alt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → (∃ O : U.left.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x) → ∃ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), Flat h ∧ p ∈ W ∧ pullback.fst τ h p = x ∧ Etale (W.ι ≫ pullback.snd τ h) := by
  first | exact @GlobalTheory.Mum.exists_flat_chart_etale_of_quasiFiniteAt | exact GlobalTheory.Mum.exists_flat_chart_etale_of_quasiFiniteAt | (intros; apply GlobalTheory.Mum.exists_flat_chart_etale_of_quasiFiniteAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameCoefficientUnitGermsFiniteFree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_isUnit_gs_of_frame_eq_sum : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁) (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ l, IsSecOver L O (s l)) → (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ z : (pullback f (spMap ρ₁) : Scheme.{0}), (pullback.fst f (spMap ρ₁)) z ∈ O → ∃ l, ∀ k, (pullback.fst f (spMap ρ₁)) z ∈ L.U k → IsUnit (gs (𝟙 X) ((pullback.fst f (spMap ρ₁)) z) (O ⊓ L.U k) (s l k)) := by
  intro R R₁ _ _ ρ₁ d b X f L hL W O hOW τ s hs hτ z hz
  obtain ⟨k₀, hk₀⟩ := exists_chart hL ((pullback.fst f (spMap ρ₁)) z)
  have hm : (𝟙 (pullback f (spMap ρ₁) : Scheme.{0})) z ∈
      (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k₀ := ⟨hOW hz, hk₀⟩
  have hm' : (pullback.fst f (spMap ρ₁)) z ∈ O ⊓ L.U k₀ := ⟨hz, hk₀⟩
  have hu : IsUnit (gs (𝟙 (pullback f (spMap ρ₁))) z
      ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k₀) (τ k₀).val) := by
    rw [gs_unit _ z _ hm]
    exact Units.isUnit _
  rw [hτ z k₀ hz hk₀] at hu
  obtain ⟨l, -, hl⟩ := IsLocalRing.exists_of_isUnit_sum hu
  have hl2 := isUnit_of_mul_isUnit_right hl
  rw [gs_eq_map_gs _ z _ hm'] at hl2
  have hl3 := (isUnit_map_iff _ _).1 hl2
  refine ⟨l, fun k hk => ?_⟩
  rw [hs l _ k k₀ hz hk hk₀]
  exact (Units.isUnit _).mul hl3

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeGeneratorTopFormsTensorLocalizationOrdStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_freeGenerator_topForms_tensorLocalization_order : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring)
    (hc : ∀ a, algebraMap ℂ L a ∈ locAt (L := L) 𝔭),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' →
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → Irreducible t →
  ∃ (y : Fin (k' + n) → locAt (L := L) 𝔭) (q : locAt (L := L) 𝔭),
    IsFreeGen (locAt (L := L) 𝔭) (dForm ((algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc) y) ∧
    IsUnit q ∧
    dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) =
      ((q : L) * (algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1)) ^ E.formOrd (dForm (algebraMap ℂ K) x)) •
        dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  first | exact @GlobalTheory.GraphLocal.exists_isFreeGen_locAt_formOrd | exact GlobalTheory.GraphLocal.exists_isFreeGen_locAt_formOrd | (intros; apply GlobalTheory.GraphLocal.exists_isFreeGen_locAt_formOrd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctorialLiftsOfObstructionTwoZeroStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functorial_lifts_of_obstructionTwo_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → Module.Projective R₀ (GlobForm s₀) → ∀ L : Pre I π (OAff s₀), (∀ w, L.IsOb2 α w 0) → ∃ L' : Pre I π (OAff s₀), L'.IsFun := by
  first | exact @GlobalTheory.Obs.exists_isFun_of_isOb2_zero | exact GlobalTheory.Obs.exists_isFun_of_isOb2_zero | (intros; apply GlobalTheory.Obs.exists_isFun_of_isOb2_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_aut_conjugate_field_points_cover : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] [IsGalois Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (K : Type) [Field K] [CharZero K] (y y' : Sp K ⟶ M₂.Z), y ≫ q = y' ≫ q → ∃ (σ : Ω₂ ≃ₐ[Ω₁] Ω₂) (s : M₂.Z ⟶ M₂.Z), M₂.pt ≫ s = spMap (σ : Ω₂ →+* Ω₂) ≫ M₂.pt ∧ y ≫ s = y' ∧ ∀ b : Ω₂, M₂.val y' b = M₂.val y (σ b) := by
  first | exact @GlobalTheory.Poinc.FieldConj.exists_aut_eq_of_comp_eq | exact GlobalTheory.Poinc.FieldConj.exists_aut_eq_of_comp_eq | (intros; apply GlobalTheory.Poinc.FieldConj.exists_aut_eq_of_comp_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMovedToCoverSide
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem exists_gen_up : ∀ {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT} (hA : LA.IsLB) (hP : LP.IsLB) (hG : LG.IsLB) (hT : LT.IsLB) {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG} (wA : LB.Iso LA (LP.pull α)) (hwA : wA.IsGen) (ℓ : LB.Iso LG (LP.pull β)) (hℓ : ℓ.IsGen) (w : LB.Iso LT (LG.pull c)) (hw : w.IsGen) (f : Y' ⟶ Y) [IsIso f] (sA mA : Y ⟶ XA) (sT mT : Y' ⟶ XT) (e' : Y' ⟶ Y') (h₁ : f ≫ sA ≫ α = sT ≫ c ≫ β) (h₂ : e' ≫ sT = mT) (h₃ : e' ≫ f ≫ sA = f ≫ mA) (k : ℤ) (u' : LB.Gen (LB.LinComb LT ![sT, mT] ![k, -k])) (hu' : u'.IsGen), ∃ u : LB.Gen (LB.LinComb LA ![sA, mA] ![k, -k]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (z : Z) JP JA JG Jt, Good LP z JP → Good LA z JA → Good LG z JG → Good LT z Jt → val u (q ≫ f) z JA = tf wA ℓ w f sA sT q z JP JA JG Jt ^ k * val u' q z Jt * (tf wA ℓ w f sA sT (q ≫ e') z JP JA JG Jt ^ k)⁻¹ := by
  intro XA XP XG XT Y Y' LA LP LG LT hA hP hG hT α β c wA hwA ℓ hℓ w hw f _ sA mA sT mT e' h₁ h₂ h₃ k u' hu'
  obtain ⟨t1, ht1, v1⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_up ((isGen_iff w).1 hw) hG hT (φ' := ![sT, mT])
    (ε := ![k, -k]) u' hu'
  obtain ⟨t2, ht2, v2⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_up ((isGen_iff ℓ).1 hℓ) hP hG
    (φ' := fun i => ![sT, mT] i ≫ c) (ε := ![k, -k]) t1 ht1
  have ht3 := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen LP _ _ t2 ht2 (inv f)
  have hfe : ∀ i, inv f ≫ (![sT, mT] i ≫ c) ≫ β = ![sA, mA] i ≫ α := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Category.assoc, ← h₁, IsIso.inv_hom_id_assoc]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Category.assoc]
      rw [← h₂, Category.assoc, ← h₁, reassoc_of% h₃, IsIso.inv_hom_id_assoc]
  obtain ⟨t4, ht4, v4⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hP (φ' := fun i => ![sA, mA] i ≫ α) (ε' := ![k, -k])
    (fun U _ h => by simp only [hfe]) _ ht3
  obtain ⟨u, hu, v5⟩ := GlobalTheory.ArcPull.exists_down_om hwA hP hA (φ' := ![sA, mA]) (φ := fun i => ![sA, mA] i ≫ α)
    (𝟙 Y) (fun i => (Category.id_comp _).symm) t4 ht4
  refine ⟨u, hu, fun Z q z JP JA JG Jt gP gA gG gT => ?_⟩
  have e5 := v5 Z (q ≫ f) z JP JA gP gA
  have e4 := v4 Z ((q ≫ f) ≫ 𝟙 Y) z JP gP
  have e3 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull gP t2 (inv f) ((q ≫ f) ≫ 𝟙 Y)
  have hq : ((q ≫ f) ≫ 𝟙 Y) ≫ inv f = q := by simp
  rw [hq] at e3
  have e2 : val t2 q z JP = pw ℓ (fun i => ![sT, mT] i ≫ c) ![k, -k] q z _ _ * val t1 q z JG :=
    v2 Z q z _ _ (gP.mem _ q) (gG.mem _ q)
  have e1 : val t1 q z JG = pw w ![sT, mT] ![k, -k] q z _ _ * val u' q z Jt := v1 Z q z _ _ (gG.mem _ q) (gT.mem _ q)
  have h₄ : f ≫ mA ≫ α = mT ≫ c ≫ β := by rw [← reassoc_of% h₃, h₁, reassoc_of% h₂]
  simp only [pw, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, GlobalTheory.ArcPull.om, tf, Category.assoc, Category.comp_id] at e1 e2 e3 e4 e5 ⊢
  have p₁ : q ≫ f ≫ sA ≫ α = q ≫ sT ≫ c ≫ β := by rw [h₁]
  have p₄ : q ≫ f ≫ mA ≫ α = q ≫ mT ≫ c ≫ β := by rw [h₄]
  have p₃ : q ≫ e' ≫ f ≫ sA = q ≫ f ≫ mA := by rw [h₃]
  have p₂ : q ≫ e' ≫ sT = q ≫ mT := by rw [h₂]
  have p₂' : q ≫ e' ≫ sT ≫ c = q ≫ mT ≫ c := by rw [reassoc_of% h₂]
  have p₂'' : q ≫ e' ≫ sT ≫ c ≫ β = q ≫ mT ≫ c ≫ β := by rw [reassoc_of% h₂]
  rw [e4, e3, e2, e1, p₁, p₄] at e5
  rw [p₃, p₂'', p₂', p₂]
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e5
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at e' ⊢
  linear_combination (norm := module) -e'

end GlobalTheory.ThetaMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMovedToTraitSide
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem exists_down_three {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT}
    (hA : LA.IsLB) (hP : LP.IsLB) (hG : LG.IsLB) (hT : LT.IsLB) {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG}
    (wA : LB.Iso LA (LP.pull α)) (hwA : wA.IsGen) (ℓ : LB.Iso LG (LP.pull β)) (hℓ : ℓ.IsGen)
    (w : LB.Iso LT (LG.pull c)) (hw : w.IsGen) (f : Y' ⟶ Y) (sA mA : Y ⟶ XA) (sT mT : Y' ⟶ XT) (e' : Y' ⟶ Y')
    (h₁ : f ≫ sA ≫ α = sT ≫ c ≫ β) (h₂ : e' ≫ sT = mT) (h₃ : e' ≫ f ≫ sA = f ≫ mA) (k : ℤ)
    (u : LB.Gen (LB.LinComb LA ![sA, mA] ![k, -k])) (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb LT ![sT, mT] ![k, -k]), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (z : Z) JP JA JG Jt,
      Good LP z JP → Good LA z JA → Good LG z JG → Good LT z Jt →
      val u (q ≫ f) z JA = tf wA ℓ w f sA sT q z JP JA JG Jt ^ k * val u' q z Jt *
        (tf wA ℓ w f sA sT (q ≫ e') z JP JA JG Jt ^ k)⁻¹ := by
  have hm : f ≫ mA ≫ α = mT ≫ c ≫ β := by
    rw [← h₂, Category.assoc, ← h₁, ← Category.assoc f mA, ← h₃]
    simp only [Category.assoc]
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up ((isGen_iff wA).1 hwA) hP hA (φ' := ![sA, mA]) (ε := ![k, -k]) u hu
  obtain ⟨t₂, ht₂, v₂⟩ := GlobalTheory.ArcPull.exists_down_om hℓ hP hG (φ' := ![sT ≫ c, mT ≫ c]) f (fun i => by
      fin_cases i
      · simpa using h₁.symm
      · simpa using hm.symm) t₁ ht₁
  obtain ⟨u', hu', v₃⟩ := GlobalTheory.ArcPull.exists_down_om hw hG hT (φ' := ![sT, mT]) (φ := ![sT ≫ c, mT ≫ c]) (𝟙 Y')
    (fun i => by fin_cases i <;> simp) t₂ ht₂
  refine ⟨u', hu', fun Z q z JP JA JG Jt hP' hA' hG' hT' => ?_⟩
  have e₁ : val t₁ (q ≫ f) z JP = pw wA ![sA, mA] ![k, -k] (q ≫ f) z (fun i => JP ((q ≫ f) ≫ ![sA, mA] i ≫ α))
      (fun i => JA ((q ≫ f) ≫ ![sA, mA] i)) * val u (q ≫ f) z JA :=
    v₁ Z (q ≫ f) z _ _ (hP'.mem _ _) (hA'.mem _ _)
  have e₂ := v₂ Z q z JP JG hP' hG'
  have e₃ := v₃ Z q z JG Jt hG' hT'
  rw [Category.comp_id] at e₃
  rw [e₂, e₃] at e₁
  simp only [pw, GlobalTheory.ArcPull.om, tf, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Category.assoc] at e₁ ⊢
  simp only [reassoc_of% h₁, reassoc_of% hm, reassoc_of% h₂, reassoc_of% h₃, h₁, hm, h₂, h₃] at e₁ ⊢
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e₁
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at e' ⊢
  linear_combination (norm := module) -e'

end GlobalTheory.ThetaMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOffClosedFibreDescended
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.OffClosed

theorem nonempty_preimage {S : Scheme.{0}} {G X : Over S} (O : G.left.Opens) (w w' : G ⊗ X ⟶ G)
    (h : lift w' (snd G X) ≫ w = fst G X) (z : (G ⊗ X).left) (hz : (fst G X).left z ∈ O) :
    ((w.left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left).Nonempty := by
  refine ⟨(lift w' (snd G X)).left z, ?_⟩
  rw [← h] at hz
  simpa using hz

theorem exists_section (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (maximalIdeal R) R) (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G)
    (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Sp R) (hx : closedPoint R ∉ Set.range x) (O : G.left.Opens) (pt : Sp Ω)
    (hO : ∃ g ∈ O, G.hom g = x pt) {J : Type} [Finite J] (k : J → (Over.mk x ⟶ G)) :
    ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, ∀ i, (k i * (toUnit (Over.mk x) ≫ a)).left pt ∈ O ∧
      (k i * (toUnit (Over.mk x) ≫ a)⁻¹).left pt ∈ O := by
  have hirr : IrreducibleSpace (pullback G.hom x : Scheme.{0}) := GlobalTheory.T.irreducibleSpace_fibre_semiAbelian_fieldPoint _ G hG Ω x
  obtain ⟨g, hg, hgx⟩ := hO
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := x) g pt hgx
  let X : Over (Sp R) := Over.mk x
  have hz' : (fst G X).left z ∈ O := by
    change pullback.fst G.hom x z ∈ O
    rw [hz]; exact hg
  let w : J × Bool → (G ⊗ X ⟶ G) := fun j =>
    match j.2 with
    | true => (snd G X ≫ k j.1) * fst G X
    | false => (snd G X ≫ k j.1) * (fst G X)⁻¹
  have hw : ∀ j, (((w j).left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left).Nonempty := by
    rintro ⟨i, _ | _⟩
    · refine nonempty_preimage O _ ((fst G X)⁻¹ * (snd G X ≫ k i)) ?_ z hz'
      simp only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst]
      group
    · refine nonempty_preimage O _ ((snd G X ≫ k i)⁻¹ * fst G X) ?_ z hz'
      simp only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst]
      group
  have hirr' : IrreducibleSpace (G ⊗ X).left := hirr
  let U : (G ⊗ X).left.Opens :=
    ⟨⋂ j, (((w j).left ⁻¹ᵁ O : (G ⊗ X).left.Opens) : Set (G ⊗ X).left),
      isOpen_iInter_of_finite fun j => ((w j).left ⁻¹ᵁ O).isOpen⟩
  have hU : (U : Set (G ⊗ X).left).Nonempty := by
    refine ⟨genericPoint (G ⊗ X).left, Set.mem_iInter.2 fun j => ?_⟩
    exact ((genericPoint_spec (G ⊗ X).left).mem_open_set_iff ((w j).left ⁻¹ᵁ O).isOpen).2 (by simpa using hw j)
  obtain ⟨a, aΩ, ha, h1, h2, h3⟩ := GlobalTheory.T.smoothGroup_sections_dense_in_fibres R hR G hG.smooth (η[G]).left (Over.w η[G]) Ω x hx hirr U hU
  let a' : 𝟙_ (Over (Sp R)) ⟶ G := Over.homMk a ha
  let u : X ⟶ G := toUnit X ≫ a'
  have hu : (lift u (𝟙 X)).left = aΩ := by
    apply pullback.hom_ext
    · refine Eq.trans ?_ h1.symm
      have : (lift u (𝟙 X)).left ≫ (fst G X).left = u.left := by rw [← Over.comp_left, lift_fst]
      exact this
    · refine Eq.trans ?_ h2.symm
      have : (lift u (𝟙 X)).left ≫ (snd G X).left = (𝟙 X : X ⟶ X).left := by rw [← Over.comp_left, lift_snd]
      exact this
  have key : ∀ j, (lift u (𝟙 X) ≫ w j).left pt ∈ O := by
    intro j
    have := Set.mem_iInter.1 (h3 ⟨pt, rfl⟩) j
    rw [← hu] at this
    exact this
  refine ⟨a', fun i => ⟨?_, ?_⟩⟩
  · have := key (i, true)
    simp only [w, MonObj.comp_mul, lift_snd_assoc, lift_fst, Category.id_comp] at this
    exact this
  · have := key (i, false)
    simp only [w, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst, Category.id_comp] at this
    exact this

theorem exists_ten (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (maximalIdeal R) R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (O : G.left.Opens) (hO : ∃ g ∈ O, G.hom g = closedPoint R) (y : G.left) (hy : G.hom y ≠ closedPoint R) :
    ∃ a b c : G ⟶ G, ∀ f ∈ cubeTen (𝟙 G) a b c, f.left y ∈ O := by
  have := hG.smooth
  let Ω : Type := G.left.residueField y
  let yy : Sp Ω ⟶ G.left := G.left.fromSpecResidueField y
  let x : Sp Ω ⟶ Sp R := yy ≫ G.hom
  have hyy : ∀ p, yy p = y := fun p => by
    have : yy p ∈ Set.range (G.left.fromSpecResidueField y) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at this
    exact this
  have hx : ∀ p, x p = G.hom y := fun p => congrArg G.hom (hyy p)
  have hx' : closedPoint R ∉ Set.range x := by
    rintro ⟨p, hp⟩
    exact hy ((hx p).symm.trans hp)
  let pt : Sp Ω := closedPoint Ω
  have hO' : ∃ g ∈ O, G.hom g = x pt := by
    obtain ⟨g, hg, hgc⟩ := hO
    have hs : x pt ⤳ G.hom g := by rw [hgc]; exact specializes_closedPoint _
    obtain ⟨g', h1, h2⟩ := Flat.generalizingMap G.hom hs
    exact ⟨g', h1.mem_open O.isOpen hg, h2⟩
  let X : Over (Sp R) := Over.mk x
  let yh : X ⟶ G := Over.homMk yy rfl
  obtain ⟨a, ha⟩ := exists_section R hR G hG Ω x hx' O pt hO' ![(1 : Over.mk x ⟶ G), yh]
  obtain ⟨b, hb⟩ := exists_section R hR G hG Ω x hx' O pt hO' ![(1 : Over.mk x ⟶ G), yh]
  obtain ⟨c, hc⟩ := exists_section R hR G hG Ω x hx' O pt hO'
    ![(1 : Over.mk x ⟶ G), yh, (toUnit X ≫ b)⁻¹, yh * (toUnit X ≫ b)⁻¹]
  refine ⟨toUnit G ≫ a, toUnit G ≫ b, toUnit G ≫ c, fun f hf => ?_⟩
  have e : f.left y = (yh ≫ f).left pt := (congrArg f.left (hyy pt)).symm
  rw [e]
  have ht : ∀ d : 𝟙_ (Over (Sp R)) ⟶ G, yh ≫ toUnit G ≫ d = toUnit X ≫ d := fun d => by
    rw [← Category.assoc, comp_toUnit]
  have a0 := ha 0
  have a1 := ha 1
  have b0 := hb 0
  have b1 := hb 1
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  have c3 := hc 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at a0 a1 b0 b1 c0 c1 c2 c3
  rw [_root_.one_mul, _root_.one_mul] at a0 b0 c0
  simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, ht, mul_inv, ← _root_.mul_assoc]
  exacts [a1.1, a1.2, a0.1, a0.2, b1.1, c1.1, c3.2, b0.1, c0.1, c2.2]

theorem exists_gen_off_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ t : LB.Gen (P'.L.L.pull (β ⁻¹ᵁ V).ι), t.IsGen := by
  intro R _ _ _ hR M G' _ _ _ P' G _ _ β hG hpb θ O hO hθ y hy
  have := hR.1
  have hβ : IsProper β := MorphismProperty.of_isPullback (P := @IsProper) hpb.1.flip M.proper
  let O' : G.left.Opens := ⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩
  have hO' : ∃ g ∈ O', G.hom g = closedPoint R := by
    obtain ⟨g, hg, hgc⟩ := hO
    refine ⟨g, fun g' hg' => ?_, hgc⟩
    subst hg'
    exact TopologicalSpace.Opens.mem_iSup.2 (hθ g' hg hgc)
  obtain ⟨a, b, c, h⟩ := exists_ten R hR.2.2.2 G hG O' hO' y hy
  let V : G.left.Opens := ⟨⋂ f ∈ {f | f ∈ cubeTen (𝟙 G) a b c}, ((f.left ⁻¹ᵁ O' : G.left.Opens) : Set G.left),
    (List.finite_toSet _).isOpen_biInter fun f _ => (f.left ⁻¹ᵁ O').isOpen⟩
  refine ⟨V, Set.mem_iInter₂.2 h, ?_⟩
  obtain ⟨hl, hm⟩ := GlobalTheory.T.grpPullback_points_lift_and_compat_mul_inv _ _ M.π G G' β hpb G' G β hpb.1.w
  obtain ⟨a', ha⟩ := hl a
  obtain ⟨b', hb⟩ := hl b
  obtain ⟨c', hc⟩ := hl c
  have h1 : (𝟙 G' : G' ⟶ G').left ≫ β = β ≫ (𝟙 G : G ⟶ G).left := by simp
  have mul := fun u v u' v' hu hv => (hm u v u' v' hu hv).1
  have inv := fun u u' hu => (hm u u u' u' hu hu).2
  have hten : ∀ f' ∈ cubeTen (𝟙 G') a' b' c', ∃ f ∈ cubeTen (𝟙 G) a b c, f'.left ≫ β = β ≫ f.left := by
    intro f' hf
    simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ ha)⟩
    · exact ⟨_, by simp [cubeTen], ha⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hb⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hc⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ (mul _ _ _ _ hb hc))⟩
    · exact ⟨_, by simp [cubeTen], hb⟩
    · exact ⟨_, by simp [cubeTen], hc⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ (mul _ _ _ _ hb hc)⟩
  have := GlobalTheory.T.exists_generator_of_theoremOfCube_ten_points M.S G' P' θ G' (𝟙 G') a' b' c' (β ⁻¹ᵁ V) (by
    intro f' hf' g hg
    obtain ⟨f, hf, e⟩ := hten f' hf'
    have h2 : f.left (β g) ∈ farSet β θ := Set.mem_iInter₂.1 hg f hf
    refine h2 (f'.left g) ?_
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply])
  have e : (β ⁻¹ᵁ V).ι ≫ (𝟙 G' : G' ⟶ G').left = (β ⁻¹ᵁ V).ι := by simp
  rw [e] at this
  exact this

end GlobalTheory.Mum.OffClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorThetaConstantsFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FibThetaMove

open GlobalTheory.Ex.OneGen GlobalTheory.ThetaPtMove GlobalTheory.ThetaPtUp GlobalTheory.UMin.ThMove

theorem exists_gen_thG_fibre : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K)
  (o : Type) [CommRing o] (g m : ℕ) (J : Type) (b : TBase o (m ^ 2)) (s : Sp K ⟶ Sp o) (t : TObj g (m ^ 2) J b s)
  (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ →
  LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) →
  ∀ v : Ix g (m ^ 2) → K, t.HasTh (𝟙 _) v →
  ∃ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))) (κ : K), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th ∧ κ ≠ 0 ∧
    ∀ a, ∃ y : Over.mk (spMap ev) ⟶ D.P.A, GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L D.rig m th y (GlobalTheory.Ex.fnOf (κ * v a)) := by
  intro V₁ _ _ D K _ _ ev o _ g m J b s t ψ hψ hLB v H
  obtain ⟨w, hw⟩ := hLB
  have := t.ab.comm
  have := D.P.isAb.comm
  let F := (Over.pullback (spMap ev)).obj D.P.A
  have : IsCommMonObj F := Functor.isCommMonObj_obj
  let φF := pullback.fst D.P.A.hom (spMap ev)
  have hpD : IsGrpPullback F D.P.A (spMap ev) φF := isGrpPullback_pullback D.P.A (spMap ev)
  have hLD : D.P.L.IsLB := D.P.isLB
  have hLF : (D.P.L.pull φF).IsLB := pull_isLB hLD φF
  have hLt : t.L.IsLB := t.isLB
  have hw₁ : (idIso (D.P.L.pull φF)).IsGen := idIso_isGen hLF
  obtain ⟨ρF, hρF, hrF⟩ := exists_rigidificationPullbackCompatibleIso (w := idIso (D.P.L.pull φF)) (ρ₀ := D.rig) hpD hw₁ hLD hLF D.rig_gen

  have hE : eSec F ≫ ψ = 𝟙 _ ≫ eSec t.A := by
    have := over_one hψ (T := baseOver _) (T₀ := baseOver _) (𝟙 _) ((Category.comp_id _).trans (Category.id_comp _).symm)
    exact ((Category.id_comp _).symm.trans (Category.assoc _ _ _).symm).trans
      (this.symm.trans (congrArg (𝟙 _ ≫ ·) (Category.id_comp _)))
  obtain ⟨ρt, hρt, hrt'⟩ := exists_gen_up_iso (K := PUnit) (φ' := fun _ => eSec F) (φ := fun _ => eSec t.A)
    (ε := fun _ => 1) (h := 𝟙 _) (χ := 𝟙 _) hw hLt hLF (Category.id_comp _) (Category.id_comp _) (fun _ => hE) ρF hρF
  have hrt : IsRigidificationPullbackCompatibleIso w (𝟙 _) ρF ρt := fun Z r z J J' hJ hJ' =>
    (hrt' Z r z J J' hJ hJ').trans (by rw [Fintype.prod_unique, zpow_one])

  let x : Ix g (m ^ 2) → (baseOver (Sp K) ⟶ t.pol.A) := fun a =>
    (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ baseOver (Sp K)) ≫ t.lab a
  have hx : ∀ a, x a ^ (m ^ 2) = 1 := fun a => by
    show ((Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ baseOver (Sp K)) ≫ t.lab a) ^ (m ^ 2) = 1
    rw [← MonObj.comp_pow, lab_pow, MonObj.comp_one]
  obtain ⟨tht, hgt, hTt⟩ := exists_gen_thG_of_isThetaPt K t.pol ρt hρt m (Ix g (m ^ 2)) x v hx H

  have hτ₁ : 𝟙 (Sp K) ≫ (baseOver (Sp K)).hom = (baseOver (Sp K)).hom ≫ 𝟙 (Sp K) := by simp
  choose xF hxF hnF using fun a => torsion_down hψ (T := baseOver (Sp K)) (T₀ := baseOver (Sp K)) (𝟙 _) hτ₁ (x a) (hx a)
  obtain ⟨thF, hsF⟩ := exists_secRel hψ (T := baseOver (Sp K)) (T₀ := baseOver (Sp K)) (𝟙 _) hτ₁ hw hLt hLF tht
  have hgF := isGenSec_down hψ (𝟙 _) hτ₁ hw hLt hLF hsF hgt
  have hTF := fun a =>
    ThG.move hψ (𝟙 _) hτ₁ hw hLt hLF hrt (hxF a) (hnF a) hsF (hTt a)

  have hτ₂ : 𝟙 (Sp K) ≫ (Over.mk (spMap ev)).hom = (baseOver (Sp K)).hom ≫ spMap ev := by simp
  choose x₀ hx₀ hn₀ using fun a => torsion_up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ (xF a) (hnF a)
  obtain ⟨th₀, hs₀⟩ := exists_secRel_up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ hw₁ hLD hLF thF
  have hg₀ : IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th₀ := isGenSec_up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ hw₁ hLD hLF hs₀ hgF
  refine ⟨th₀, 1, hg₀, one_ne_zero, fun a => ⟨x₀ a, ?_⟩⟩
  have q := ThG.up hpD (T := baseOver (Sp K)) (T₀ := Over.mk (spMap ev)) (𝟙 _) hτ₂ hw₁ hLD hLF hrF (hx₀ a) (hn₀ a) hs₀ (hTF a)
  simpa using q

end GlobalTheory.FibThetaMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glued_commGroupScheme_artinFibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀)) [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left), IsCommMonObj A₁ → IsCommMonObj A₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂ → ∀ (Y : Over (Spec P)) (j₁ : A₁.left ⟶ Y.left) (j₂ : A₂.left ⟶ Y.left), IsPullback j₁ A₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ A₂.hom Y.hom (Spec.map f₂) → Flat Y.hom → IsPushout ψ₁ ψ₂ j₁ j₂ → ∃ _ : GrpObj Y, IsCommMonObj Y ∧ IsGrpPullback A₁ Y (Spec.map f₁) j₁ ∧ IsGrpPullback A₂ Y (Spec.map f₂) j₂ := by
  first | exact @GlobalTheory.GlueGrpLaw.exists_glued_grp | exact GlobalTheory.GlueGrpLaw.exists_glued_grp | (intros; apply GlobalTheory.GlueGrpLaw.exists_glued_grp <;> assumption)
end

