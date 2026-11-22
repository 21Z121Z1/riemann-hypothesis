import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0126
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0121
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0071
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0128
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0112
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingRegularPushStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominating_regular_push : ∀ (X X₀ : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (h : X ⟶ X₀) (i : Ω₀ →+* Ω) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i), IsCptGen ξ → (∀ (p : Cpt ξ) (a : Ω₀), a ∈ regAt ξ₀ (pushCpt hd p) → i a ∈ regAt ξ p) ∧ (∀ (p : Cpt ξ) (a : Ω₀), a ∈ regAt ξ₀ (pushCpt hd p) → unitAt ξ p (i a) → unitAt ξ₀ (pushCpt hd p) a) ∧ (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (a : Ω₀) (r : ℂ), genPt ξ ⤳ centre z → ValAt ξ₀ (z ≫ h) a r → ValAt ξ z (i a) r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.Stalk.regular_along_dominant | exact GlobalTheory.CompanionTheory.Ar.Chg.Stalk.regular_along_dominant | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.Stalk.regular_along_dominant <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameOfUnitDetChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_frame_of_unit_det_change : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (O : Type) [CommRing O] (act : OAct O G) (σ : O →+* R) (n : ℕ) (u v : Fin n → (epsAt x ⟶ G)) (C : Matrix (Fin n) (Fin n) R), IsEigFrame act x σ u → (∀ i, IsComb (C i) u (v i)) → IsUnit C.det → IsEigFrame act x σ v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FrameUnit.isEigFrame_of_isUnit_det | exact GlobalTheory.CompanionTheory.Ar.FrameUnit.isEigFrame_of_isUnit_det | (intros; apply GlobalTheory.CompanionTheory.Ar.FrameUnit.isEigFrame_of_isUnit_det <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFramesInvertibleChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_frames_invertible_change : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] [Nontrivial R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (O : Type) [CommRing O] (act : OAct O G) (σ : O →+* R) (n r : ℕ) (u : Fin n → (epsAt x ⟶ G)) (V : Fin r → (epsAt x ⟶ G)), IsEigFrame act x σ u → IsEigFrame act x σ V → r = n ∧ ∃ C : Matrix (Fin r) (Fin n) R, (∀ i, IsComb (C i) u (V i)) ∧ ∃ C' : Matrix (Fin n) (Fin r) R, C * C' = 1 ∧ C' * C = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change | exact GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange.eigFrame_change <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsChartFamilyOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.ChartHol

open Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt GlobalTheory.HolHom GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

theorem diffOn_div {f g : V → ℂ} {s : Set V} (hf : DifferentiableOn ℂ f s) (hg : DifferentiableOn ℂ g s)
    (h0 : ∀ b ∈ s, g b ≠ 0) : DifferentiableOn ℂ (fun b => f b / g b) s :=
  (hf.mul (hg.inv h0)).congr fun b _ => by simp [div_eq_mul_inv]

theorem holAt_of_isAffineOpen {N : Set V} {c : V → (Sp ℂ ⟶ X)} {A : X.Opens} (hA : IsAffineOpen A) (hN : IsOpen N)
    (hin : ∀ b ∈ N, ⊤ ≤ c b ⁻¹ᵁ A) (hz : ∀ r : Γ(X, A), DifferentiableOn ℂ (fun b => valAt' (c b) A r) N)
    {b₀ : V} (hb₀ : b₀ ∈ N) : HolAt c b₀ := by
  intro U hU
  have hmU : (c b₀) (default : PrimeSpectrum ℂ) ∈ U := (le_preimage_iff _ _).1 hU
  have hmA : (c b₀) (default : PrimeSpectrum ℂ) ∈ A := (le_preimage_iff _ _).1 (hin b₀ hb₀)
  obtain ⟨r, hrU, hr0⟩ := hA.exists_basicOpen_le (V := U) ⟨_, hmU⟩ hmA
  set M := {b ∈ N | valAt' (c b) A r ≠ 0} with hMdef
  have hMo : IsOpen M := (hz r).continuousOn.isOpen_inter_preimage hN isOpen_ne
  have hD : ∀ b ∈ M, ⊤ ≤ c b ⁻¹ᵁ X.basicOpen r := fun b hb =>
    (le_basicOpen_iff (c b) (hin b hb.1) r).2 hb.2
  have hb0M : b₀ ∈ M := ⟨hb₀, (le_basicOpen_iff (c b₀) (hin b₀ hb₀) r).1 ((le_preimage_iff _ _).2 hr0)⟩
  refine ⟨?_, fun f => ?_⟩
  · filter_upwards [hMo.mem_nhds hb0M] with b hb
    exact (hD b hb).trans (Scheme.Hom.preimage_mono _ hrU)
  · haveI := hA.isLocalization_basicOpen r
    obtain ⟨⟨hh, s⟩, hk⟩ := IsLocalization.surj (Submonoid.powers r) (X.presheaf.map (homOfLE hrU).op f)
    obtain ⟨k, hks⟩ := s.2
    dsimp only at hk
    have hval : ∀ b ∈ M, valAt' (c b) U f * valAt' (c b) A r ^ k = valAt' (c b) A hh := by
      intro b hb
      have e := congrArg (valAt' (c b) (X.basicOpen r)) hk
      rw [valAt'_mul, valAt'_res (c b) hrU (hD b hb)] at e
      have e2 : ∀ x : Γ(X, A), valAt' (c b) (X.basicOpen r) (algebraMap Γ(X, A) Γ(X, X.basicOpen r) x) =
          valAt' (c b) A x := fun x => valAt'_res (c b) (X.basicOpen_le r) (hD b hb) x
      rw [e2, e2, ← hks] at e
      have e3 : valAt' (c b) A (r ^ k) = valAt' (c b) A r ^ k := map_pow (valHom (c b) A (hin b hb.1)) r k
      rw [e3] at e
      exact e
    have h1 : DifferentiableOn ℂ (fun b => valAt' (c b) A hh) M := (hz hh).mono fun b (hb : b ∈ M) => hb.1
    have h2 : DifferentiableOn ℂ (fun b => valAt' (c b) A r) M := (hz r).mono fun b (hb : b ∈ M) => hb.1
    have h3 : DifferentiableOn ℂ (fun b => valAt' (c b) A hh / valAt' (c b) A r ^ k) M :=
      diffOn_div h1 (h2.fun_pow k) fun b hb => pow_ne_zero _ hb.2
    refine ((h3.congr fun b hb => ?_).differentiableAt (hMo.mem_nhds hb0M))
    rw [eq_div_iff (pow_ne_zero _ hb.2)]
    exact hval b hb

variable {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

theorem genMap_germ {A : X.Opens} (hg : genPt ξ ∈ A) (q : Cpt ξ) (hq : q.1 ∈ A) (r : Γ(X, A)) :
    genMap ξ q (X.presheaf.germ A q.1 hq r) =
      (X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ).hom r := by
  have h1 := X.presheaf.germ_stalkSpecializes (U := A) (y := q.1) hq q.2
  have h3 : X.presheaf.germ A q.1 hq ≫ (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) =
      X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) h1)
  exact congrArg (fun f => f.hom r) h3

theorem valAt_section (hall : ∀ q : X, genPt ξ ⤳ q) {A : X.Opens} (hg : genPt ξ ∈ A) (r : Γ(X, A))
    {z : Sp ℂ ⟶ X} (hz : ⊤ ≤ z ⁻¹ᵁ A) :
    ValAt ξ z ((X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ).hom r) (valAt' z A r) := by
  have hc : centre z ∈ A := (le_preimage_iff z A).1 hz
  refine ⟨hall _, X.presheaf.germ A (centre z) hc r, genMap_germ hg ⟨centre z, hall _⟩ hc r, ?_⟩
  rw [valAt'_of _ _ hz]
  exact congrArg (fun φ => φ.hom r) (GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap z A hz)

theorem exists_hol_value (hall : ∀ q : X, genPt ξ ⤳ q) {N : Set V} {β : V → (Σ k, J k) → ℂ} {ζ : V → (Sp ℂ ⟶ X)}
    (c : (k : K) → J k) (hβ : ∀ p, DifferentiableOn ℂ (fun b => β b p) N)
    (hco : ∀ b ∈ N, CoordsAt ξ y (ζ b) (β b)) (hne : ∀ b ∈ N, ∀ k, β b ⟨k, c k⟩ ≠ 0) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) :
    ∃ F : V → ℂ, DifferentiableOn ℂ F N ∧ ∀ b ∈ N, ValAt ξ (ζ b) a (F b) := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    refine ⟨fun b => ∏ k, β b ⟨k, j k⟩ / β b ⟨k, c k⟩, ?_, fun b hb => ?_⟩
    · have hS : ∀ S : Finset K, DifferentiableOn ℂ (fun b => ∏ k ∈ S, β b ⟨k, j k⟩ / β b ⟨k, c k⟩) N := by
        classical
        intro S
        induction S using Finset.induction_on with
        | empty => simpa using differentiableOn_const (c := (1 : ℂ))
        | insert k S hk ih =>
          simp only [Finset.prod_insert hk]
          exact (diffOn_div (hβ _) (hβ _) fun b hb => hne b hb k).fun_mul ih
      exact hS _
    · simp only [← Finset.prod_div_distrib]
      have hS : ∀ S : Finset K, ValAt ξ (ζ b) (∏ k ∈ S, y ⟨k, j k⟩ / y ⟨k, c k⟩)
          (∏ k ∈ S, β b ⟨k, j k⟩ / β b ⟨k, c k⟩) := by
        classical
        intro S
        induction S using Finset.induction_on with
        | empty => simpa using val_one (ξ := ξ) (z := ζ b) (hall _)
        | insert k S hk ih =>
          rw [Finset.prod_insert hk, Finset.prod_insert hk]
          refine val_mul ?_ ih
          obtain ⟨r, hr, hr'⟩ := ((hco b hb).2 k (c k) (isUnit_iff_ne_zero.2 (hne b hb k))).2 (j k)
          rwa [hr', mul_div_cancel_right₀ _ (hne b hb k)]
      exact hS _
  | algebraMap n =>
    refine ⟨fun _ => (n : ℂ), differentiableOn_const _, fun b _ => ?_⟩
    exact ⟨hall _, (n : X.presheaf.stalk (centre (ζ b))), by simp, map_intCast _ n⟩
  | add a a' _ _ h h' =>
    obtain ⟨F, hF, hv⟩ := h
    obtain ⟨F', hF', hv'⟩ := h'
    exact ⟨fun b => F b + F' b, hF.fun_add hF', fun b hb => val_add (hv b hb) (hv' b hb)⟩
  | mul a a' _ _ h h' =>
    obtain ⟨F, hF, hv⟩ := h
    obtain ⟨F', hF', hv'⟩ := h'
    exact ⟨fun b => F b * F' b, hF.fun_mul hF', fun b hb => val_mul (hv b hb) (hv' b hb)⟩

theorem isHolTo_of_coordsAt (htie : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hall : ∀ q : X, genPt ξ ⤳ q) {B : Set V} {β : V → (Σ k, J k) → ℂ} {ζ : V → (Sp ℂ ⟶ X)} (hB : IsOpen B)
    (hβ : ∀ p, DifferentiableOn ℂ (fun b => β b p) B) (hco : ∀ b ∈ B, CoordsAt ξ y (ζ b) (β b)) :
    IsHolTo B ζ := by
  refine isHolTo_of_holAt hB fun b₁ hb₁ => ?_
  choose c hc using (hco b₁ hb₁).1
  set N := {b ∈ B | ∀ k, β b ⟨k, c k⟩ ≠ 0} with hNdef
  have hNB : N ⊆ B := fun b hb => hb.1
  have hNo : IsOpen N := by
    refine isOpen_iff_mem_nhds.2 fun b hb => ?_
    have hk : ∀ᶠ t in 𝓝 b, ∀ k, β t ⟨k, c k⟩ ≠ 0 := eventually_all.2 fun k =>
      ((hβ _).continuousOn.continuousAt (hB.mem_nhds hb.1)).eventually_ne (hb.2 k)
    filter_upwards [hB.mem_nhds hb.1, hk] with t h1 h2 using ⟨h1, h2⟩
  have hb₁N : b₁ ∈ N := ⟨hb₁, fun k => (hc k).ne_zero⟩
  have hx0 : (∏ k, y ⟨k, c k⟩) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => ((hco b₁ hb₁).2 k (c k) (hc k)).1
  obtain ⟨A, hA, hAq⟩ := htie.affine c hx0
  have hin : ∀ b ∈ N, ⊤ ≤ ζ b ⁻¹ᵁ A := fun b hb =>
    (le_preimage_iff _ _).2 ((hAq _).2 ⟨hall _, in_chart (hall _) (hco b hb.1) hb.2⟩)
  have hg : genPt ξ ∈ A := (hall _).mem_open A.2 ((le_preimage_iff _ _).1 (hin b₁ hb₁N))
  refine holAt_of_isAffineOpen hA hNo hin (fun r => ?_) hb₁N
  have ha := (htie.ring c hx0 ((X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ).hom r)).2
    fun p hp => ⟨_, genMap_germ hg p ((hAq _).2 ⟨p.2, hp⟩) r⟩
  obtain ⟨F, hF, hFv⟩ := exists_hol_value hall c (fun p => (hβ p).mono hNB) (fun b hb => hco b hb.1)
    (fun b hb => hb.2) ha
  refine hF.congr fun b hb => ?_
  exact val_unique htie.gen (valAt_section hall hg r (hin b hb)) (hFv b hb)

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.ChartHol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCocharacterLieModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusLie

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {R : Type} [CommRing R]

theorem charVal_congr {A : Type} [CommRing A] {a a' : Sp A ⟶ S} (t : Over.mk a ⟶ splitTorus S X)
    (t' : Over.mk a' ⟶ splitTorus S X) (h : t.left = t'.left) (χ : X) : charVal t χ = charVal t' χ := by
  have ha : a = a' := by
    have h1 := Over.w t
    have h2 := Over.w t'
    simp only [Over.mk_hom] at h1 h2
    rw [← h1, ← h2, h]
  subst ha
  have : t = t' := Over.OverMorphism.ext h
  rw [this]

def pullPt {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A') {a : Sp A ⟶ S} {a' : Sp A' ⟶ S}
    (h : a' = spMap g ≫ a) (t : Over.mk a ⟶ splitTorus S X) : Over.mk a' ⟶ splitTorus S X :=
  Over.homMk (spMap g ≫ t.left) (by
    have h1 := Over.w t
    simp only [Over.mk_hom] at h1 ⊢
    rw [Category.assoc, h1, h])

theorem charVal_pullPt {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A') {a : Sp A ⟶ S}
    {a' : Sp A' ⟶ S} (h : a' = spMap g ≫ a) (t : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal (pullPt g h t) χ = g (charVal t χ) := by
  subst h
  exact (GlobalTheory.T.charVal_multiplicative S X A _).2.2.2.2.2 A' g t _ rfl χ

def wOf (δ : X →+ R) : Multiplicative X →* DualNumber R where
  toFun χ := TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ.toAdd)
  map_one' := by
    ext <;> simp
  map_mul' a b := by
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, add_comm]

abbrev evZ (R : Type) [CommRing R] : DualNumber R →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom

theorem base_ev (x : Sp R ⟶ S) :
    x = spMap (evZ R) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x := by
  have : spMap (evZ R) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (evZ R).comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; simp
    rw [this]; simp
  rw [← Category.assoc, this, Category.id_comp]

theorem isTanAt_iff (x : Sp R ⟶ S) (v : epsAt x ⟶ splitTorus S X) :
    IsTanAt (splitTorus S X) x v ↔ ∀ χ, (charVal v χ).fst = 1 := by
  have hT := GlobalTheory.T.charVal_multiplicative S X
  constructor
  · intro hv χ
    have e : pullPt (evZ R) (base_ev x) v = 1 := Over.OverMorphism.ext hv
    have := charVal_pullPt (evZ R) (base_ev x) v χ
    rw [e, (hT R x).2.2.1 χ] at this
    exact this.symm
  · intro hv
    have e : pullPt (evZ R) (base_ev x) v = 1 := by
      refine (hT R x).1 _ _ fun χ => ?_
      rw [charVal_pullPt, (hT R x).2.2.1 χ]
      exact hv χ
    exact congrArg (fun t => t.left) e

def ptOf (x : Sp R ⟶ S) (δ : X →+ R) : epsAt x ⟶ splitTorus S X :=
  ((GlobalTheory.T.charVal_multiplicative S X (DualNumber R) (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x)).2.2.2.2.1
    (wOf δ)).choose

theorem charVal_ptOf (x : Sp R ⟶ S) (δ : X →+ R) (χ : X) :
    charVal (ptOf x δ) χ = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (δ χ) :=
  ((GlobalTheory.T.charVal_multiplicative S X (DualNumber R) (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x)).2.2.2.2.1
    (wOf δ)).choose_spec χ

theorem ptOf_ext (x : Sp R ⟶ S) (v v' : epsAt x ⟶ splitTorus S X) (h : ∀ χ, charVal v χ = charVal v' χ) : v = v' :=
  (GlobalTheory.T.charVal_multiplicative S X (DualNumber R) _).1 v v' h

theorem epsMul_comp_base (c : R) (x : Sp R ⟶ S) :
    Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x =
      spMap (epsMul c) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x := by
  have : spMap (epsMul c) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (epsMul c).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
      ext r <;> simp [epsMul]
    rw [this]
  rw [← Category.assoc, this]

def deltaOf (x : Sp R ⟶ S) (v : epsAt x ⟶ splitTorus S X) (hv : ∀ χ, (charVal v χ).fst = 1) : X →+ R :=
  AddMonoidHom.mk' (fun χ => (charVal v χ).snd) (fun χ χ' => by
    have := ((GlobalTheory.T.charVal_multiplicative S X (DualNumber R) _).2.2.2.1 v).2 χ χ'
    simp [this, TrivSqZeroExt.snd_mul, hv, add_comm])

theorem exists_lieModel_splitTorus : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (R : Type) [CommRing R]
    (x : Sp R ⟶ S), ∃ M : LieModel (splitTorus S X) x (X →+ R), IsCocharLie M := by
  intro S X _ R _ x
  refine ⟨{ pt := ptOf x, tan := ?_, inj := ?_, onto := ?_, add := ?_, smul := ?_ },
    fun δ χ => charVal_ptOf x δ χ⟩
  · intro δ
    refine (isTanAt_iff x _).2 fun χ => ?_
    rw [charVal_ptOf]; simp
  · intro δ δ' h
    ext χ
    have := congrArg TrivSqZeroExt.snd
      ((charVal_ptOf x δ χ).symm.trans ((congrArg (fun t => charVal t χ) h).trans (charVal_ptOf x δ' χ)))
    simpa using this
  · intro v hv
    have hv' := (isTanAt_iff x v).1 hv
    refine ⟨deltaOf x v hv', ptOf_ext x _ _ fun χ => ?_⟩
    rw [charVal_ptOf]
    ext
    · simp [hv']
    · simp [deltaOf]
  · intro δ δ'
    refine ptOf_ext x _ _ fun χ => ?_
    rw [(GlobalTheory.T.charVal_multiplicative S X (DualNumber R) _).2.1, charVal_ptOf, charVal_ptOf, charVal_ptOf]
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, add_comm]
  · intro c δ
    have e : ptOf x (c • δ) = pullPt (epsMul c) (epsMul_comp_base c x) (ptOf x δ) := by
      refine ptOf_ext x _ _ fun χ => ?_
      rw [charVal_pullPt, charVal_ptOf, charVal_ptOf]
      ext <;> simp [epsMul, mul_comm]
    exact congrArg (fun t => t.left) e

end GlobalTheory.CompanionTheory.Ar.TorusLie
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConjugateLogPeriods
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods

open GroundTheory.Heights₂.Heights.Regular

theorem star_mem_logCover {n a : ℕ} (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) :
    star w ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · simpa using hw.1 i
  · simpa using hw.2 k hk

theorem expCover_star {n : ℕ} (a : ℕ) (w : Fin n → ℂ) : expCover a (star w) = star (expCover a w) := by
  funext k
  simp only [expCover, Pi.star_apply]
  split_ifs
  · exact Complex.exp_conj _
  · rfl

theorem isOpen_logCover {n a : ℕ} (h : a ≤ n) : IsOpen (logCover h) := by
  have : logCover h = (⋂ i : Fin a, {w : Fin n → ℂ | (w (Fin.castLE h i)).re < 0}) ∩
      ⋂ k : Fin n, {w : Fin n → ℂ | a ≤ k.val → ‖w k‖ < 1} := by
    ext w; simp [logCover]
  rw [this]
  refine (isOpen_iInter_of_finite fun i => ?_).inter (isOpen_iInter_of_finite fun k => ?_)
  · exact isOpen_lt (Complex.continuous_re.comp (continuous_apply _)) continuous_const
  · by_cases hk : a ≤ k.val
    · simpa [hk] using isOpen_lt (continuous_norm.comp (continuous_apply k)) continuous_const
    · simp [hk]

theorem star_mem_ball {n : ℕ} {z : Fin n → ℂ} (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    star z ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos] at hz ⊢
  intro i
  simpa using hz i

theorem differentiableOn_conj {n g : ℕ} {S : Set (Fin n → ℂ)} (hS : IsOpen S) (hst : ∀ w ∈ S, star w ∈ S)
    {f : (Fin n → ℂ) → Fin g → ℂ} (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (fun w => star (f (star w))) S := by
  intro w hw
  have h1 : DifferentiableAt ℂ f (star w) := hf.differentiableAt (hS.mem_nhds (hst w hw))
  have h2 := h1.star_star
  rw [star_star] at h2
  exact h2.differentiableWithinAt

theorem dot_map_conj {g : ℕ} (x y : Fin g → ℂ) (M : Matrix (Fin g) (Fin g) ℂ) :
    x ⬝ᵥ M.map (starRingEnd ℂ) *ᵥ y = star (star x ⬝ᵥ M *ᵥ star y) := by
  simp [dotProduct, Matrix.mulVec, star_sum]

theorem isHermitian_map_conj {g : ℕ} {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian) :
    (M.map (starRingEnd ℂ)).IsHermitian := by
  ext i j
  have := hM.apply i j
  simp [Matrix.conjTranspose_apply, ← this]

theorem star_single {n : ℕ} (c : Fin n) :
    star (Pi.single c (2 * Real.pi * Complex.I) : Fin n → ℂ) = -Pi.single c (2 * Real.pi * Complex.I) := by
  funext k
  by_cases hk : k = c
  · subst hk
    simp
  · simp [hk]

theorem sub_single_mem_logCover {n a : ℕ} (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) (i : Fin a) :
    w - Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I) ∈ logCover h := by
  refine ⟨fun j => ?_, fun k hk => ?_⟩
  · by_cases hj : Fin.castLE h j = Fin.castLE h i
    · simpa [hj, Pi.single_apply] using (by simpa [hj] using hw.1 j)
    · simpa [Pi.single_apply, hj] using hw.1 j
  · have hki : k ≠ Fin.castLE h i := by
      rintro rfl
      simp at hk
      omega
    simpa [Pi.single_apply, hki] using hw.2 k hk

def conj {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)
    (hT : ∀ i, Function.Bijective (L.T i)) : Flat.LogPeriods n a g Λ where
  a_le := L.a_le
  free := L.free
  fin := L.fin
  rank := L.rank
  E := -L.E
  alt x := by simp [L.alt x]
  unimod := by
    constructor
    · intro x y hxy
      exact L.unimod.1 (neg_injective hxy)
    · intro f
      obtain ⟨x, hx⟩ := L.unimod.2 (-f)
      exact ⟨x, by simp [hx]⟩
  P w := AddMonoidHom.mk' (fun x => star (L.P (star w) x)) (fun x y => by simp)
  hol x := differentiableOn_conj (isOpen_logCover L.a_le) (fun w hw => star_mem_logCover L.a_le hw) (L.hol x)
  H z := (L.H (star z)).map (starRingEnd ℂ)
  herm w hw := by
    rw [← expCover_star]
    exact isHermitian_map_conj (L.herm _ (star_mem_logCover L.a_le hw))
  pos w hw z hz := by
    rw [← expCover_star, dot_map_conj]
    have h := L.pos _ (star_mem_logCover L.a_le hw) (star z) (by simpa using hz)
    simpa using h
  im w hw x y := by
    simp only [AddMonoidHom.mk'_apply]
    rw [← expCover_star, dot_map_conj]
    have h := L.im _ (star_mem_logCover L.a_le hw) x y
    simp [h]
  T i := ((LinearEquiv.ofBijective (L.T i) (hT i)).symm : Λ ≃ₗ[ℤ] Λ).toLinearMap
  mono i w hw x := by
    set e : Fin _ → ℂ := Pi.single (Fin.castLE L.a_le i) (2 * Real.pi * Complex.I) with he
    have hw₁ : star w - e ∈ logCover L.a_le :=
      sub_single_mem_logCover L.a_le (star_mem_logCover L.a_le hw) i
    have hm := L.mono i _ hw₁ ((LinearEquiv.ofBijective (L.T i) (hT i)).symm x)
    have hTT : L.T i ((LinearEquiv.ofBijective (L.T i) (hT i)).symm x) = x :=
      (LinearEquiv.ofBijective (L.T i) (hT i)).apply_symm_apply x
    rw [hTT, ← he, sub_add_cancel] at hm
    have hs : star (w + e) = star w - e := by
      rw [star_add, he, star_single, sub_eq_add_neg]
    simp only [AddMonoidHom.mk'_apply, LinearEquiv.coe_coe]
    rw [hs, hm]
  W := L.W
  coiso x hx := L.coiso x fun y hy => by simpa using hx y hy
  s x z := star (L.s x (star z))
  s_hol x := differentiableOn_conj Metric.isOpen_ball (fun _ hz => star_mem_ball hz) (L.s_hol x)
  s_eq x w hw := by
    simp only [AddMonoidHom.mk'_apply]
    rw [← expCover_star, L.s_eq x _ (star_mem_logCover L.a_le hw)]
  span := by
    rw [eq_top_iff]
    intro v _
    have key : ∀ y ∈ Submodule.span ℂ (Set.range fun x => L.s x 0),
        star y ∈ Submodule.span ℂ (Set.range fun x => star (L.s x (star (0 : Fin _ → ℂ)))) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, rfl⟩ := hy
        exact Submodule.subset_span ⟨x, by simp⟩
      | zero => simp
      | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
      | smul c y _ hy =>
        rw [star_smul]
        exact Submodule.smul_mem _ _ hy
    have := key (star v) (by rw [L.span]; trivial)
    simpa using this

theorem exists_conj_periodGram : ∀ (n a g r : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ), (∀ i, Function.Bijective (L.T i)) →
    ∃ L' : Flat.LogPeriods n a g Λ, ∀ u ∈ Flat.punct n a 1,
      HodgeMetric.periodGram L' (fun k u' => star (U k (star u'))) u =
        (HodgeMetric.periodGram L U (star u)).map (starRingEnd ℂ) := by
  intro n a g r Λ _ L U hT
  refine ⟨conj L hT, fun u _ => ?_⟩
  ext i j
  simp only [HodgeMetric.periodGram, Matrix.of_apply, Matrix.map_apply]
  change _ * (_ ⬝ᵥ ((L.H (star u)).map (starRingEnd ℂ)) *ᵥ _) = _
  rw [dot_map_conj, map_mul, Complex.conj_ofReal]
  simp

end GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods
end
end

