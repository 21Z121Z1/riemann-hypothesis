import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0245
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0080
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0059
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0242
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0165
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0246
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0203
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0243
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0157
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreOpenCoords
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0011
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0057

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeMiddle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet

theorem coordsAt_torusSmul {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X} {w : (Σ k, J k) → ℂ}
    (h : CoordsAt ξ y z w) {a : K → ℂ} (ha : ∀ k, a k ≠ 0) : CoordsAt ξ y z (torusSmul a w) := by
  have hs : ∀ q : Σ k, J k, torusSmul a w q = a q.1 * w q := fun q => rfl
  refine ⟨fun k => ?_, fun k c hc => ?_⟩
  · obtain ⟨c, hc⟩ := h.1 k
    refine ⟨c, ?_⟩
    rw [hs]
    exact (isUnit_iff_ne_zero.2 (ha k)).mul hc
  · have hc' : IsUnit (w ⟨k, c⟩) := by
      rw [hs] at hc
      exact isUnit_of_mul_isUnit_right hc
    obtain ⟨hy, hv⟩ := h.2 k c hc'
    refine ⟨hy, fun i => ?_⟩
    obtain ⟨r, hr, he⟩ := hv i
    refine ⟨r, hr, ?_⟩
    rw [hs, hs]
    show a k * w ⟨k, i⟩ = r * (a k * w ⟨k, c⟩)
    rw [he]
    ring

theorem valAt_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω} {r r' : R}
    (h₁ : ValAt ξ z a r) (h₂ : ValAt ξ z a r') : r = r' := by
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom X Ω ξ R z h hξ
  obtain ⟨_, e₁⟩ := (hφ a r).1 h₁
  obtain ⟨_, e₂⟩ := (hφ a r').1 h₂
  exact e₁.symm.trans e₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {Xo : ∀ l : Tor.Level H, Moduli D l}
  {l : Tor.Level H} {c : Coeff l} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type}
  [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  {S₀ : Finset ℕ}

theorem isCMFam_of_labVal (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X}
    {σ : CMType H → (𝓞 E →+* ℂ)} (hL : Or.𝔐.LabVal z Or.sm σ) : IsCMFam σ := by
  obtain ⟨σ₀, h0, -, -, -, -, hcm⟩ := GlobalTheory.T.cusp_correspondence_bound E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 ℂ z
  have hs : ∀ τ, σ τ = σ₀ (Or.sm τ) := fun τ => RingHom.ext fun a =>
    valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (hL τ a) (h0 (Or.sm τ) a)
  obtain ⟨h1, h2, -⟩ := hcm (RingHom.id ℂ)
  have he : σ = fun τ => σ₀ (Or.sm τ) := funext hs
  rcases Or.side with ⟨-, h, -⟩ | ⟨-, h, -⟩
  · rw [he, h]
    exact h2
  · rw [he, h]
    exact h1

theorem eq_cuspW_of_fibre (Or : CptOrigin Y S₀ Dc Hd) {U : ((Σ k, J k) → ℂ) → ℝ} (hU : Or.𝔐.IsCuspWeight Or.sm U)
    {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ} (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (hz : Or.𝔐.Interior z)
    {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) {σ : CMType H → (𝓞 E →+* ℂ)}
    (hF : FibreLat Or.𝔐.t z R) (hL : Or.𝔐.LabVal z Or.sm σ) : U w = R.cuspW σ := by
  obtain ⟨g', Λ', i₁, i₂, R', σ', hF', hL', he⟩ := hU z w hw hz
  have hσ : σ' = σ := funext fun τ => RingHom.ext fun a =>
    valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (hL' τ a) (hL τ a)
  subst hσ
  obtain ⟨φ, h1, h2, h3, -⟩ := GlobalTheory.T.fibre_lattice_linear_equiv E H Or.𝔐.X Or.𝔐.t z g' g Λ' Λ R' R Empty _ _ _ hF' hF
  rw [he]
  exact (GlobalTheory.T.cusp_weight_invariant_under_isometry E g' Λ' (CMType H) R' σ' g Λ R φ (isCMFam_of_labVal Or hL) h1 h2 h3).1.symm

theorem cuspWeight_torus_and_sheets : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or) (U : ((Σ k, J k) → ℂ) → ℝ), Or.𝔐.IsCuspWeight Or.sm U → (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, U w' = U w) ∧ ∀ m, ∀ t ∈ Q.V m, U (Q.γ m t) = ((Q.F (Q.pc m)).R t).cuspW (Q.F (Q.pc m)).σ := by
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or Q U hU
  refine ⟨fun w hw w' hw' => ?_, fun m t ht => ?_⟩
  · obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).1 hw.1
    have hI : Or.𝔐.Interior z := by
      by_contra hn
      exact hw.2 ((Or.bd z w hz).2 hn)
    obtain ⟨u, hu, a, ha, rfl⟩ := hw'
    rw [show u = w from hu]
    obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, he⟩ := hU z w hz hI
    rw [he]
    exact eq_cuspW_of_fibre Or hU (coordsAt_torusSmul Or.𝔐.ξ hz ha) hI R hF hL
  · obtain ⟨z, hz, hI, hF, hL⟩ := Q.fibre m t ht
    exact eq_cuspW_of_fibre Or hU hz hI _ hF hL

end GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsArchimedeanFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.RigScale

open GlobalTheory GlobalTheory.ArchMetricCompare

theorem eSec_comp_of_cart {S : Scheme.{0}} {G : Over S} [GrpObj G] {z : Sp ℂ ⟶ S} {A : Over (Sp ℂ)} [GrpObj A]
    {φ : A.left ⟶ G.left} (h : IsGrpPullback A G z φ) : eSec A ≫ φ = z ≫ eSec G := by
  have e := congrArg (fun q => q.left) (map_one (pushHom h (𝟙_ (Over (Sp ℂ)))))
  have e₁ : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) = η[A] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def scale (u : HolUnif A L g) (c : ℂ) (hc : c ≠ 0) : HolUnif A L g :=
  { u with
    fr := fun j w => c * u.fr j w
    fr_hol := fun i => (u.fr_hol i).const_mul c
    fr_ne := fun i z h => mul_ne_zero hc (u.fr_ne i z h)
    fr_compat := fun i j z h => by
      rw [u.fr_compat i j z h]
      ring }

theorem scale_isAH {u : HolUnif A L g} {c : ℂ} (hc : c ≠ 0) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) : (scale u c hc).IsAH Hm χ := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun l i z hz => ?_⟩
  show c * u.fr i z = _ * (c * u.fr i (z + (l : Fin g → ℂ)))
  rw [h.2.2.2 l i z hz]
  ring

end GlobalTheory.CompanionTheory.Ar.Sl.RigScale

namespace GlobalTheory.CompanionTheory.Ar.Sl

open GlobalTheory GlobalTheory.ArchMetricCompare RigScale

theorem exists_archFrame_of_isAH : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ G.left) (g : ℕ) (u : HolUnif A (P.L.pull φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), IsGrpPullback A G z φ → u.IsAH Hm χ → Nonempty (ArchFrame P z g) := by
  intro S G _ _ P z A _ φ g u Hm χ cart ah
  have he : (u.ex 0).left ≫ φ = z ≫ eSec G := by
    have := eSec_comp_of_cart cart
    rw [show (u.ex 0).left = eSec A from GlobalTheory.CompanionTheory.Ar.Flat.PerGram.ex_zero_left u]
    exact this
  obtain ⟨i₀, h₀⟩ : ∃ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i :=
    (exists_chart P.isLB (((u.ex 0).left ≫ φ) (default : PrimeSpectrum ℂ))).imp
      fun _ h => (top_le_preimage_iff_mem _ _).2 h

  have hfr : ∀ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i → ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (P.L.pull φ).U (fun _ => i) :=
    fun i h => (le_pull_iff P.L φ _ _).2 h
  have hz : ∀ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i →
      ⊤ ≤ z ⁻¹ᵁ (P.L.pull (eSec G)).U (fun _ => i) := fun i h =>
    (le_pull_iff P.L (eSec G) z _).2 (he ▸ h)
  have hrel : ∀ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i →
      valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i).val =
        valAt' ((u.ex 0).left ≫ φ) (P.L.U i ⊓ P.L.U i₀) (P.L.g i i₀).val *
          valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i₀).val := by
    intro i hi
    have hm : ⊤ ≤ z ⁻¹ᵁ ((P.L.pull (eSec G)).U (fun _ => i) ⊓ (P.L.pull (eSec G)).U (fun _ => i₀)) :=
      (top_le_preimage_inf _ _ _).2 ⟨hz i hi, hz i₀ h₀⟩
    have e := congrArg (fun a => valAt' z _ (Units.val a)) (P.rigGen (fun _ => i) (fun _ => i₀))
    have e2 := (valAt'_res z inf_le_left _ hm).symm.trans (e.trans ((valAt'_mul _ _ _ _).trans
      (congrArg₂ (· * ·) rfl (valAt'_res z inf_le_right _ hm))))
    rw [he]
    rw [← val_pull_g P.L (eSec G) z (fun _ => i) (fun _ => i₀) hm]
    exact e2
  have hn : valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i₀).val ≠ 0 :=
    valAt'_unit_ne_zero z (hz i₀ h₀) _
  have hd := u.fr_ne (fun _ => i₀) 0 (hfr i₀ h₀)
  have hc : valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i₀).val / u.fr (fun _ => i₀) 0 ≠ 0 :=
    div_ne_zero hn hd
  refine ⟨{ A := A, φ := φ, cart := cart, u := scale u _ hc, Hm := Hm, χ := χ, ah := scale_isAH hc ah, rig := ?_ }⟩
  intro i hi
  have hi' : ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i := hi
  show _ / u.fr (fun _ => i₀) 0 * u.fr (fun _ => i) 0 = _
  have hm : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ ((P.L.pull φ).U (fun _ => i) ⊓ (P.L.pull φ).U (fun _ => i₀)) :=
    (top_le_preimage_inf _ _ _).2 ⟨hfr i hi', hfr i₀ h₀⟩
  rw [u.fr_compat (fun _ => i) (fun _ => i₀) 0 hm, val_pull_g P.L φ _ (fun _ => i) (fun _ => i₀) hm, hrel i hi']
  field_simp

end GlobalTheory.CompanionTheory.Ar.Sl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitAnalyticFunction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.Unit

open Matrix

variable {p q : ℕ} {g : ℕ}

theorem det_fromRows_mul_top (A : Matrix (Fin p) (Fin p) ℂ) (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ)
    (F : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) :
    (Matrix.fromRows (A * C) F).det = A.det * (Matrix.fromRows C F).det := by
  have h : Matrix.fromRows (A * C) F = Matrix.fromBlocks A 0 0 1 * Matrix.fromRows C F := by
    ext (a | b) m <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  rw [h, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem det_fromRows_mul_bot (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ)
    (F : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) :
    (Matrix.fromRows C (B * F)).det = B.det * (Matrix.fromRows C F).det := by
  have h : Matrix.fromRows C (B * F) = Matrix.fromBlocks 1 0 0 B * Matrix.fromRows C F := by
    ext (a | b) m <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  rw [h, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem det_chg (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Pe Tc : Fin p ⊕ Fin q → Fin g → ℂ)
    (S : Fin p ⊕ Fin q → Fin p ⊕ Fin q → ℂ) (V V' : Fin p → Fin g → ℂ) (W W' : Fin q → Fin g → ℂ)
    (Fm Fm' B₀ B' : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) (d d' : ℂ)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ)
    (hV : ∀ a, V' a = ∑ b, A a b • V b) (hW : ∀ j, W' j = ∑ k, B j k • W k)
    (hWi : LinearIndependent ℂ W) (hWi' : LinearIndependent ℂ W')
    (k3 : ∀ n, Tc n = ∑ j, B₀ j n • W j) (l3 : ∀ n, Tc n = ∑ j, B' j n • W' j)
    (l4 : ∀ j n, ∑ m, Fm' j m * S m n = B' j n) (hd' : d' ≠ 0)
    (k6 : ∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, ∀ a, T (∑ m, C a m • Pe m) = V a)
    (l7 : ∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • Pe m) = V' a) →
      (Matrix.fromRows C Fm').det = d')
    (hu : ∀ (F₂ : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) (d₂ : ℂ), (∀ j n, ∑ m, F₂ j m * S m n = B₀ j n) → d₂ ≠ 0 →
      (∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • Pe m) = V a) →
        (Matrix.fromRows C F₂).det = d₂) → d₂ = d) :
    d * A.det = d' * B.det := by
  have lift : ∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • Pe m) = V a) →
      ∀ a, T (∑ m, (A * C) a m • Pe m) = V' a := by
    intro C hC a
    have : ∑ m, (A * C) a m • Pe m = ∑ b, A a b • ∑ m, C b m • Pe m := by
      simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
      exact Finset.sum_comm
    rw [this, map_sum, hV a]
    exact Finset.sum_congr rfl fun b _ => by rw [map_smul, hC b]
  obtain ⟨C₀, hC₀⟩ := k6
  have hA : A.det ≠ 0 := by
    intro h0
    have := l7 _ (lift C₀ hC₀)
    rw [det_fromRows_mul_top, h0, zero_mul] at this
    exact hd' this.symm
  have hB : B.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hcB⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hc
    have hz : ∑ j, c j • W' j = 0 := by
      simp only [hW, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [← Finset.sum_smul]
      have := congrFun hcB k
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
      rw [this, zero_smul]
    funext j
    exact Fintype.linearIndependent_iff.1 hWi' c hz j
  have hB₀ : ∀ k n, B₀ k n = ∑ j, B j k * B' j n := by
    intro k n
    have hz : ∑ k, (B₀ k n - ∑ j, B j k * B' j n) • W k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← k3 n]
      rw [sub_eq_zero, l3 n]
      simp only [hW, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [_root_.mul_comm]
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hWi _ hz k)
  have hfin := hu (Bᵀ * Fm') (B.det * d' / A.det) ?_ (div_ne_zero (mul_ne_zero hB hd') hA) ?_
  · rw [← hfin]; field_simp
  · intro j n
    rw [hB₀]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, ← l4]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, _root_.mul_assoc]
  · intro C hC
    have h1 := l7 _ (lift C hC)
    rw [det_fromRows_mul_top] at h1
    rw [det_fromRows_mul_bot, Matrix.det_transpose, ← h1]
    field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.Unit

namespace GlobalTheory.CompanionTheory.Ar.Flat.Unit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l}

theorem isDerivAt0_of_isComb {σK : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σK ty)
    (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (x : Sp ℂ ⟶ Xo.X)
    (hx : x = FU.u i P) {n : ℕ} (a : Fin n → ℂ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G))
    (w : epsAt x ⟶ Xo.univ.t.G) (V : Fin n → Fin g → ℂ)
    (hV : ∀ k, IsDerivAt0 (fun z => (FU.ex i P z).left) (V k) (v k).left) (h : IsComb a v w) :
    IsDerivAt0 (fun z => (FU.ex i P z).left) (∑ k, a k • V k) w.left := by
  subst hx
  exact (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H D l Xo σK g ty FU i P hP n (fun k => (v k).left) V hV a w.left).1
    ((EigDir.isComb_iff_isCombAt _ a v w).1 h)

theorem tauIn_conj {c : Coeff l} {τ τ' : E →+* ℂ} {σ : c.F →+* ℂ}
    (hτ : ∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) (a : 𝓞 E) :
    (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) a = ComplexEmbedding.conjugate τ' (a : E) := by
  have h1 : tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
    apply Subtype.ext
    show ComplexEmbedding.conjugate τ (a : E) = τ ((H.bar a : 𝓞 E) : E)
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
    rfl
  show σ (tauIn c (ComplexEmbedding.conjugate τ) a) = _
  rw [h1, hτ, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

theorem isLinearMap_tyPart {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ) : IsLinearMap ℂ (tyPart ty τ) := by
  constructor
  · intro a b; funext k; simp only [tyPart, Pi.add_apply]; split_ifs <;> simp
  · intro a b; funext k; simp only [tyPart, Pi.smul_apply]; split_ifs <;> simp

theorem chg_of_isFlatAn {c : Coeff l} {τ τ' : E →+* ℂ} {σ : c.F →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    (hT : IsTypeFn H D.p D.q ty) (hrt : τ' (H.rt : E) = H.rt0) (hτ : ∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E))
    (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (he : LinearIndependent (𝓞 E) e)
    (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (y : Sp ℂ ⟶ Xo.XF c)
    (hy : under y = FU.u i P) (v v' : Vecs y D.p) (w w' : Vecs y D.q)
    (A : Matrix (Fin D.p) (Fin D.p) ℂ) (Bm : Matrix (Fin D.q) (Fin D.q) ℂ)
    (hf : IsFramed Set.univ τ σ y v w) (hf' : IsFramed Set.univ τ σ y v' w')
    (hA : ∀ a, IsComb (A a) v (v' a)) (hB : ∀ j, IsComb (Bm j) w (w' j))
    (Φ : CFn Xo c) (ρ : ℂ) (hΦ : IsFlatAn Set.univ τ τ' σ Φ FU i e ρ) :
    Φ y v' w' * A.det = Φ y v w * Bm.det := by
  obtain ⟨⟨V, W, Fm, B₀, d⟩, ⟨k1, k2, k3, k4, k5, ⟨C, hC⟩, k7⟩, hu⟩ :=
    GlobalTheory.T.uniformised_eigen_frame_one E H D l Xo c τ τ' σ g ty FU hT hrt hτ i e P y v w he hP hy hf
  obtain ⟨⟨V', W', Fm', B', d'⟩, ⟨l1, l2, l3, l4, l5, ⟨C', hC'⟩, l7⟩, -⟩ :=
    GlobalTheory.T.uniformised_eigen_frame_one E H D l Xo c τ τ' σ g ty FU hT hrt hτ i e P y v' w' he hP hy hf'
  have f1 : Φ y v w * d = ρ := by
    have := hΦ P y v w V W C Fm B₀ hP hy hf k1 k2 hC k3 k4
    rwa [k7 C hC] at this
  have f2 : Φ y v' w' * d' = ρ := by
    have := hΦ P y v' w' V' W' C' Fm' B' hP hy hf' l1 l2 hC' l3 l4
    rwa [l7 C' hC'] at this
  obtain ⟨V₀, hV₀, -, -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) _ τ' D.p v' hP hy hτ hf'.2.2.1
  obtain ⟨W₀, hW₀, hWi, -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) _
    (ComplexEmbedding.conjugate τ') D.q w hP hy (tauIn_conj hτ) hf.2.2.2
  obtain ⟨W₁, hW₁, hWi', -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y) _
    (ComplexEmbedding.conjugate τ') D.q w' hP hy (tauIn_conj hτ) hf'.2.2.2
  have eW : W = W₀ := funext fun j => (hW₀ j _).1 (k2 j)
  have eW' : W' = W₁ := funext fun j => (hW₁ j _).1 (l2 j)
  have hV : ∀ a, V' a = ∑ b, A a b • V b := fun a =>
    ((hV₀ a _).1 (l1 a)).trans ((hV₀ a _).1 (isDerivAt0_of_isComb FU i P hP _ hy _ v _ V k1 (hA a))).symm
  have hW : ∀ j, W' j = ∑ k, Bm j k • W k := fun j =>
    ((hW₁ j _).1 (l2 j)).trans ((hW₁ j _).1 (isDerivAt0_of_isComb FU i P hP _ hy _ w _ W k2 (hB j))).symm
  have key := det_chg ((isLinearMap_tyPart ty τ').mk' _) (fun m => P (e m))
    (fun n => tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)))
    (fun m n => τ' (sesq (FU.Di i) (e m) (e n))) V V' W W' Fm Fm' B₀ B' d d' A Bm hV hW
    (eW ▸ hWi) (eW' ▸ hWi') k3 l3 l4 l5 ⟨C, hC⟩ l7
    (fun F₂ d₂ h4 h5 h7 => congrArg (fun x => x.2.2.2.2) (hu (V, W, F₂, B₀, d₂) ⟨k1, k2, k3, h4, h5, ⟨C, hC⟩, h7⟩))
  apply mul_right_cancel₀ (mul_ne_zero k5 l5)
  linear_combination (A.det * d) * f2 - (Bm.det * d') * f1 + ρ * key

end GlobalTheory.CompanionTheory.Ar.Flat.Unit

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem anUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∃ Φ : CFn Xo c, IsUnitAn τ σ Φ ∧ ∀ i : Fin FU.n, ∃ (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), ρ ≠ 0 ∧ LinearIndependent (𝓞 E) e ∧ IsFlatAn Set.univ τ τ' σ Φ FU i e ρ := by
  intro E _ _ _ H D l Xo c τ τ' σ g ty FU hT hrt hτ
  have hrank : ∀ i, ∃ e : Fin D.p ⊕ Fin D.q → (FU.Di i).La, LinearIndependent (𝓞 E) e := by
    intro i
    have hr : D.p + D.q ≤ Module.finrank (𝓞 E) (FU.Di i).La := by
      rw [(FU.Di i).rank, (FU.sig i).1, (FU.sig i).2]
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hr
    exact ⟨f ∘ finSumFinEquiv, hf.comp _ finSumFinEquiv.injective⟩
  choose e he using hrank
  choose t ht hN using fun i => GlobalTheory.T.uniformised_eigen_frame_two E H D l Xo c τ τ' σ g ty FU hT hrt hτ i (e i) (he i)
  let ρ : Fin FU.n → ℂ := fun i => (((Real.sqrt (t i))⁻¹ : ℝ) : ℂ)
  have hs : ∀ i, Real.sqrt (t i) ≠ 0 := fun i => (Real.sqrt_pos.2 (ht i)).ne'
  have hρ : ∀ i, ρ i ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (inv_ne_zero (hs i))
  have hρt : ∀ i, ‖ρ i‖ ^ 2 * t i = 1 := by
    intro i
    have h1 : ‖ρ i‖ = (Real.sqrt (t i))⁻¹ := by
      show ‖(((Real.sqrt (t i))⁻¹ : ℝ) : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    rw [h1, inv_pow, Real.sq_sqrt (ht i).le, inv_mul_cancel₀ (ht i).ne']
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.uniformised_eigen_frames_all E H D l Xo c τ τ' σ g ty FU hT hrt hτ e ρ he
  have hloc : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap σ →
      ∃ (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)), IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P := by
    intro y hy
    obtain ⟨i, P, hP, hu⟩ := FU.onto (under y) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
      simp only [spMap, ← Spec.map_comp]
      rfl)
    exact ⟨i, P, hP, hu.symm⟩
  refine ⟨Φ, { ne := ?_, chg := ?_, norm := ?_, hol := ?_ }, fun i => ⟨e i, ρ i, hρ i, he i, hΦ i⟩⟩
  · intro y v w hf h0
    obtain ⟨i, P, hP, hy⟩ := hloc y hf.1
    obtain ⟨⟨V, W, Fm, B₀, d⟩, ⟨k1, k2, k3, k4, k5, ⟨C, hC⟩, k7⟩, -⟩ :=
      GlobalTheory.T.uniformised_eigen_frame_one E H D l Xo c τ τ' σ g ty FU hT hrt hτ i (e i) P y v w (he i) hP hy hf
    have := hΦ i P y v w V W C Fm B₀ hP hy hf k1 k2 hC k3 k4
    rw [h0, zero_mul] at this
    exact hρ i this.symm
  · intro y v w v' w' A B hf hf' hA hB
    obtain ⟨i, P, hP, hy⟩ := hloc y hf.1
    exact Unit.chg_of_isFlatAn FU hT hrt hτ i (e i) (he i) P hP y hy v v' w w' A B hf hf' hA hB Φ (ρ i) (hΦ i)
  · intro y v w Γ Δ hf hΓ hΔ
    obtain ⟨i, P, hP, hy⟩ := hloc y hf.1
    have := hN i (ρ i) Φ (hΦ i) P y v w Γ Δ hP hy hf hΓ hΔ
    rw [this, hρt i, _root_.one_mul]
  · intro R _ x vR wR m B ψ v w h1 h2 h3
    exact GlobalTheory.T.uniformised_eigen_frames_two E H D l Xo c τ τ' σ g ty FU hT hrt hτ e ρ Φ he hΦ R x vR wR m B ψ v w h1 h2 h3

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreOpenCoordsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_open_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (M : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (f : M.X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c) (U : (pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F))).Opens), M.ξ ≫ f = y₀ ≫ Y.j → SmoothGenericFibreM y → Algebra.trdeg ℤ Ω = ((D.dim : ℕ) : Cardinal) → SmoothOfRelativeDimension D.dim (U.ι ≫ pullback.snd (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenSmooth.smooth_genericFibre | exact GlobalTheory.CompanionTheory.Ar.GenSmooth.smooth_genericFibre | (intros; apply GlobalTheory.CompanionTheory.Ar.GenSmooth.smooth_genericFibre <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieNormSquareOfFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.lie_norm_square_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (T : PAT H (Sp R)) (h : D.La → D.La → OK H) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (σ : R →+* ℂ) (κ : OK H →+* ℂ) (r : ℝ) (n : ℕ) (a : Fin n → L) (u : Fin n → (epsAt (spMap σ) ⟶ T.t.G)), IsFam C T h L ψ → κ (wK H) = σ ω → IsLieNormSq C.P C.v σ r → (∀ k, (u k).left = spMap (dualMap σ) ≫ C.v.left ≫ (ψ (a k)).left) → IsHodgeGram T.t.G T.t.PP.L (spMap σ) u (Matrix.of fun k k' => r * κ (h (a k) (a k'))) := by
  first | exact @PositivityTheory.Xgf.lie_norm_square_of_family | exact PositivityTheory.Xgf.lie_norm_square_of_family
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodRiemannLatticeFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_riemann_lattice_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod (FU.Di i) ty P → (∃ R : RiemLat E g (FU.Di i).La, R.form = (FU.Di i).EF ∧ FibreLat Xo.univ.t (FU.u i P) R ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q) ∧ (∃ R : RiemLat E g (FU.Di i).La, R.form = -(FU.Di i).EF ∧ FibreLat Xo.univ.t (spMap (starRingEnd ℂ) ≫ FU.u i P) R ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.q else D.p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.period_lattice_fibre_and_conj | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.period_lattice_fibre_and_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.period_lattice_fibre_and_conj <;> assumption)
end

