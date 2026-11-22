import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0194
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0192
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0193
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0195
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0196

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspCorrespondenceBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_correspondence_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ 𝔐.X), ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* L), 𝔐.LabVal z id σ ∧ (∀ σ', 𝔐.LabVal z id σ' → σ' = σ) ∧ Function.Bijective σ ∧ (∀ s, Function.Injective (σ s)) ∧ 2 * Fintype.card (CMType H) = Module.finrank ℚ E ∧ ∀ e : L →+* ℂ, IsCMFam (fun τ => e.comp (σ (.inl τ))) ∧ IsCMFam (fun τ => e.comp (σ (.inr τ))) ∧ ∀ τ, e.comp (σ (.inr τ)) = (starRingEnd ℂ).comp (e.comp (σ (.inl τ))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LabPt.exists_labVal | exact GlobalTheory.CompanionTheory.Ar.Cusp.LabPt.exists_labVal | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LabPt.exists_labVal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeFlagTensorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_lattice_flag_tensor : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (b₀ : Fin r → V), LinearIndependent Ω b₀ → L.IsFlagVBOn Set.univ b₀ → detLat L b₀ = Lat.tens (fun i => L.gr b₀ i) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.det_lattice_flag_tensor | exact GlobalTheory.CompanionTheory.Relay.det_lattice_flag_tensor | (intros; apply GlobalTheory.CompanionTheory.Relay.det_lattice_flag_tensor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeFrameGenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_lattice_frame_gen : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (b₀ b : Fin r → V) (T : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω b₀ → L.IsFrameAt b p → (∀ k, b k = ∑ k', T k' k • b₀ k') → (detLat L b₀).IsGenAt p T.det := by
  first | exact @GlobalTheory.CompanionTheory.Relay.det_lattice_frame_gen | exact GlobalTheory.CompanionTheory.Relay.det_lattice_frame_gen | (intros; apply GlobalTheory.CompanionTheory.Relay.det_lattice_frame_gen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualBasisHermitianSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_basis_hermitian_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (σ : E →+* ℂ) (κ : OK H →+* ℂ) (n : ℕ) (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (x y : D.La), IsKForm D ε h → κ (wK H) = σ (H.w0 : E) → ∑ k, ∑ k', σ (HT.dualInt E (e k)) * κ (h (RingOfIntegers.basis E (e k) • x) (RingOfIntegers.basis E (e k') • y)) * starRingEnd ℂ (σ (HT.dualInt E (e k'))) = ((ε : ℤ) : ℂ) * σ ((H.rt : E) * sesq D x y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.KForm.sigma_component | exact GlobalTheory.CompanionTheory.Ar.Fl.KForm.sigma_component | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.KForm.sigma_component <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteGroupSchemeSumExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem gm_comp_spMap_unitOn {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (u : Rˣ) {Z : Scheme.{0}}
    (r : Z ⟶ Sp R') (z : Z) :
    gm (r ≫ spMap f) z ⊤ (unitOn u) = gm r z ⊤ (unitOn (Units.map f.toMonoidHom u)) := by
  refine (gm_pull r (spMap f) z ⊤ trivial (unitOn u)).symm.trans (congrArg (gm r z ⊤) ?_)
  apply Units.ext
  exact (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

def FG.scaled {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) (a : FG M Y) (c : Γ(Y, ⊤)ˣ) : FG M Y :=
  ⟨a.K, a.φ, a.ε, scaleGen a.t c, scaleGen_isGen hM a.t a.ht c⟩

theorem FG.v_scaled {X Y Z : Scheme.{0}} {M : LB X} (hM : M.IsLB) (a : FG M Y) (c : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X) → M.ι} (hJ : Good M z J) : (a.scaled hM c).v r z J = gm r z ⊤ c * a.v r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ (hJ.mem a.φ r) _) rfl)

theorem exists_root_in_ext (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 1 ≤ n) (c : Kˣ) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (u : K'ˣ),
      u ^ n = Units.map (algebraMap K K').toMonoidHom c := by
  let P : Polynomial K := Polynomial.X ^ n - Polynomial.C (c : K)
  have hdeg : P.degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C (by omega)]
    exact_mod_cast (by omega : n ≠ 0)
  have : FiniteDimensional ℚ P.SplittingField := Module.Finite.trans K _
  obtain ⟨ρ, hρ⟩ := (Polynomial.IsSplittingField.splits P.SplittingField P).exists_eval_eq_zero
    (by rwa [Polynomial.degree_map])
  have hρn : ρ ^ n = algebraMap K P.SplittingField (c : K) := by
    simpa [P, sub_eq_zero, Polynomial.eval_map] using hρ
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hρn
    exact (map_ne_zero _).2 c.ne_zero hρn.symm
  refine ⟨P.SplittingField, inferInstance, NumberField.mk, inferInstance, Units.mk0 ρ hρ0, Units.ext ?_⟩
  simpa using hρn

theorem exists_gen_normalised {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Field K] [NumberField K] (n : ℕ)
    (hn : 1 ≤ n) (xl : Sp K ⟶ X) (A : FG M (Sp K))
    (hA : ∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), A.sum U h = (h xl ^ n)⁻¹) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (e : FG M (Sp K')),
      (∀ (U : Type) [CommGroup U] (h : (Sp K' ⟶ X) → U), e.sum U h = h (spMap (algebraMap K K') ≫ xl)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp K') (z : Z) (J), Good M z J →
        e.v r z J ^ n * A.v (r ≫ spMap (algebraMap K K')) z J = 1 := by
  obtain ⟨z₀⟩ : Nonempty (Sp K) := inferInstance
  choose d hd using fun χ : Sp K ⟶ X => exists_chart hM (χ z₀)
  have hJ₀ : Good M z₀ d := hd
  obtain ⟨t₀, ht₀, -⟩ := GlobalTheory.ThetaInValues.exists_gen_of_value hM (fun _ : PUnit => xl) (fun _ => (1 : ℤ)) hJ₀ (1 : Kˣ)
  let e₀ : FG M (Sp K) := ⟨PUnit, _, _, t₀, ht₀⟩
  have hs₀ : ∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), e₀.sum U h = h xl := by
    intro U _ h
    show ∏ _k : PUnit, h xl ^ (1 : ℤ) = _
    simp
  have hg : ∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ X) → U), ((e₀.pow n).mul A).sum U h = 1 := by
    intro U _ h
    rw [FG.sum_mul, FG.sum_pow, hs₀, hA]
    exact _root_.mul_inv_cancel _
  obtain ⟨c, hc⟩ := FG.exists_unit hM _ hg
  let c₀ : Kˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c
  have hcc : unitOn c₀ = c := by
    apply Units.ext
    exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of K)) c.val
  obtain ⟨K', iF, iN, iA, u, hu⟩ := exists_root_in_ext K n hn c₀⁻¹
  refine ⟨K', iF, iN, iA, (e₀.pull (spMap (algebraMap K K'))).scaled hM (unitOn u), ?_, ?_⟩
  · intro U _ h
    exact hs₀ U fun q => h (spMap (algebraMap K K') ≫ q)
  · intro Z r z J hJ
    have key : unitOn u ^ n * unitOn (Units.map (algebraMap K K').toMonoidHom c₀) = 1 := by
      have e1 : unitOn u ^ n = unitOn (u ^ n) := (map_pow _ _ _).symm
      have e2 : ∀ a b : K'ˣ, unitOn a * unitOn b = unitOn (a * b) := fun a b => (map_mul _ _ _).symm
      rw [e1, e2, hu, ← map_mul, inv_mul_cancel, map_one]
      exact map_one _
    rw [FG.v_scaled hM _ _ r hJ, FG.v_pull hJ, _root_.mul_pow, _root_.mul_assoc, ← FG.v_pow hJ, ← FG.v_mul hJ,
      hc Z _ z J hJ, ← hcc, gm_comp_spMap_unitOn, ← map_pow, ← map_mul, key, map_one]

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormLocalBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_norm_local_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c), (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t) → ∃ ρ : HeightOneSpectrum (𝓞 c.F) → ℝ, ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm U τ φ p κ (ρ la * Real.log ‖κ π‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.FinPlace.exists_rho | exact GlobalTheory.CompanionTheory.Ar.Br.FinPlace.exists_rho | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.FinPlace.exists_rho <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenOfUnit
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.DetNef

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem uMul {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem uZpow {a : Ω} (ha : unitAt ξ p a) (n : ℤ) : unitAt ξ p (a ^ n) :=
  ⟨zpow_ne_zero _ ha.1, TensDeg.zpow_mem_of_unit _ ha.2.1 ha.2.2 n, by
    rw [← zpow_neg]; exact TensDeg.zpow_mem_of_unit _ ha.2.1 ha.2.2 _⟩

theorem uProd {I : Type} [Fintype I] {f : I → Ω} (h : ∀ i, unitAt ξ p (f i)) : unitAt ξ p (∏ i, f i) :=
  ⟨Finset.prod_ne_zero_iff.2 fun i _ => (h i).1, prod_mem fun i _ => (h i).2.1, by
    rw [← Finset.prod_inv_distrib]; exact prod_mem fun i _ => (h i).2.2⟩

theorem gen_unit {Λ : Lat ξ Ω} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) : unitAt ξ p (s / t) := by
  obtain ⟨u, h1, h2, h3⟩ := TensDeg.exists_unit_of_span_eq (regAt ξ p) ht.1 (hs.2.symm.trans ht.2)
  have : s / t = u := by rw [h3, mul_div_cancel_right₀ _ ht.1]
  exact ⟨div_ne_zero hs.1 ht.1, this ▸ h1, this ▸ h2⟩

theorem gen_of_unit {Λ : Lat ξ Ω} {s t : Ω} (ht : Λ.IsGenAt p t) (hu : unitAt ξ p (s / t)) : Λ.IsGenAt p s := by
  have hs : s ≠ 0 := fun h => hu.1 (by rw [h, zero_div])
  have ht0 := ht.1
  refine ⟨hs, ht.2.trans (le_antisymm ?_ ?_)⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hu.2.2⟩, ?_⟩
    show (s / t)⁻¹ * s = t
    field_simp
  · rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hu.2.1⟩, ?_⟩
    show (s / t) * t = s
    field_simp

theorem gen_untens {Λ : Lat ξ Ω} {σ : ℤ} (hσ : σ * σ = 1) {t : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsGenAt p t) : Λ.IsGenAt p (t ^ σ) := by
  have hex : ∃ s, Λ.IsGenAt p s := by
    by_contra h0
    have h1 : Lat.tens (fun _ : Unit => Λ) (fun _ => σ) p = ⊥ := by
      rw [Lat.tens, Submodule.span_eq_bot]
      rintro _ ⟨s, hs, -⟩
      exact absurd ⟨_, hs ()⟩ h0
    have h2 := h.2
    rw [h1, eq_comm, Submodule.span_singleton_eq_bot] at h2
    exact h.1 h2
  obtain ⟨s, hs⟩ := hex
  have h1 := Flag.tens_gen (fun _ : Unit => Λ) (fun _ => σ) p (fun _ => s) fun _ => hs
  have h2 := uZpow (gen_unit h h1) σ
  refine gen_of_unit hs ?_
  convert h2 using 1
  simp only [Finset.univ_unique, Finset.prod_singleton]
  rw [div_zpow, ← zpow_mul, hσ, zpow_one]

theorem gen_scale {Λ : Lat ξ Ω} {t u : Ω} (hu : u ≠ 0) (h : Λ.IsGenAt p t) : (Λ.scale u).IsGenAt p (u * t) := by
  refine ⟨mul_ne_zero hu h.1, ?_⟩
  show (Λ p).map _ = _
  rw [h.2, Submodule.map_span, Set.image_singleton]
  rfl

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem chart_ne {c : (k : K) → J k} (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    y ⟨k, c k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 h.1 k (Finset.mem_univ k)

theorem chart_ratio {c : (k : K) → J k} (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K)
    (x : J k) : y ⟨k, x⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h1 := h.2 (Function.update c k x)
  dsimp only at h1
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k] at h1
  · simpa using h1
  · intro b _ hb
    rw [Function.update_of_ne hb, div_self (chart_ne h b)]
  · simp

theorem deg_gen {Λ : Lat ξ Ω} {a : K → ℤ} {e : Ω} (h : Λ.IsDegOn Set.univ y a e) {c : (k : K) → J k}
    (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) :
    Λ.IsGenAt p ((∏ k, y ⟨k, c k⟩ ^ a k) * e) :=
  ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_ne hc k)) h.1, h.2 p trivial c hc⟩

theorem deg_untens {Λ : Lat ξ Ω} {σ : ℤ} (hσ : σ * σ = 1) {a : K → ℤ} {e : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => σ).IsDegOn Set.univ y a e) :
    Λ.IsDegOn Set.univ y (σ • a) (e ^ σ) := by
  refine ⟨zpow_ne_zero _ h.1, fun q _ c hc => ?_⟩
  have h1 := (gen_untens hσ (deg_gen h hc)).2
  rw [h1, mul_zpow, ← Finset.prod_zpow]
  simp only [Pi.smul_apply, smul_eq_mul, ← zpow_mul, mul_comm σ]

variable {V : Type} [AddCommGroup V] [Module Ω V] {X' : Scheme.{0}} {Ω' : Type} [Field Ω']
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} {V' : Type} [AddCommGroup V'] [Module Ω' V']
  {j : V →+ V'}

theorem uMap {q : Cpt ξ'} (hreg : ∀ a ∈ regAt ξ p, i a ∈ regAt ξ' q) {a : Ω} (h : unitAt ξ p a) :
    unitAt ξ' q (i a) :=
  ⟨(map_ne_zero i).2 h.1, hreg _ h.2.1, by rw [← map_inv₀]; exact hreg _ h.2.2⟩

theorem frame_pull {L : Lat ξ V} {r : ℕ} {b : Fin r → V} (hj : ∀ (a : Ω) e, j (a • e) = i a • j e)
    (hli : LinearIndependent Ω' fun k => j (b k)) {q : Cpt ξ'} (h : genPt ξ ⤳ f q.1)
    (hreg : ∀ a ∈ regAt ξ ⟨f q.1, h⟩, i a ∈ regAt ξ' q) (hb : L.IsFrameAt b ⟨f q.1, h⟩) :
    (L.pull ξ' f j).IsFrameAt (fun k => j (b k)) q := by
  refine ⟨hli, ?_⟩
  have hL := hb.2
  have key' : ∀ e ∈ Submodule.span (regAt ξ ⟨f q.1, h⟩) (Set.range b),
      j e ∈ Submodule.span (regAt ξ' q) (Set.range fun k => j (b k)) := by
    intro e he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | smul a x _ hx =>
      have e1 : j (a • x) = (⟨i a, hreg a a.2⟩ : regAt ξ' q) • j x := hj a x
      rw [e1]
      exact Submodule.smul_mem _ _ hx
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨h3, e, he, rfl⟩
    exact key' e (by rw [← hL]; exact he)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨h, b k, ?_, rfl⟩
    rw [hL]
    exact Submodule.subset_span ⟨k, rfl⟩

theorem exists_mat {r m : ℕ} {b : Fin r → V} {s : Fin m → V} (h : ∀ k, b k ∈ Submodule.span Ω (Set.range s)) :
    ∃ T : Matrix (Fin m) (Fin r) Ω, ∀ k, b k = ∑ k', T k' k • s k' := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h k)
  exact ⟨fun k' k => c k k', fun k => (hc k).symm⟩

theorem det_pull {L : Lat ξ V} {r m : ℕ} {s : Fin m → V} {U : Submodule Ω V} (hd : Dominates ξ' ξ f i)
    (hj : ∀ (a : Ω) e, j (a • e) = i a • j e)
    (hli : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent Ω b → LinearIndependent Ω' fun k => j (b k))
    (hs : LinearIndependent Ω s) (hsU : Submodule.span Ω (Set.range s) = U) (hL : L.IsVB r U)
    {b₀ : Fin r → V'} (hb₀ : LinearIndependent Ω' b₀) (hF : (L.pull ξ' f j).IsFlagVBOn Set.univ b₀) :
    ∃ u : Ω', u ≠ 0 ∧ ∀ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (detLat L s).IsGenAt ⟨f q.1, h⟩ t ∧
      (detLat (L.pull ξ' f j) b₀).IsGenAt q (u * i t) := by
  let g : Cpt ξ' := ⟨genPt ξ', specializes_rfl⟩
  obtain ⟨hg, hgreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd g
  obtain ⟨U₀, hU₀, b, hb, hfr⟩ := hL ⟨f g.1, hg⟩ trivial
  have hbf := hfr _ trivial hU₀
  have hrm : r = m := by
    have h1 := finrank_span_eq_card hs
    have h2 := finrank_span_eq_card hbf.1
    rw [hsU] at h1
    rw [hb] at h2
    simpa using h2.symm.trans h1
  subst hrm
  have hjb : ∀ k, j (b k) ∈ Submodule.span Ω' (Set.range b₀) := by
    intro k
    obtain ⟨U₁, hU₁, b', hb', hfr'⟩ := hF g trivial
    have e1 : ∀ c : Fin r → V', flagStep Ω' c r = Submodule.span Ω' (Set.range c) := fun c => by
      unfold flagStep
      congr 1
      ext x
      simp
    rw [← e1, ← hb', e1]
    have h1 : j (b k) ∈ (L.pull ξ' f j) g := by
      rw [(frame_pull hj (hli _ _ hbf.1) hg hgreg hbf).2]
      exact Submodule.subset_span ⟨k, rfl⟩
    rw [(hfr' g trivial hU₁).2] at h1
    exact Submodule.span_le_restrictScalars (regAt ξ' g) Ω' _ h1
  have hjs : ∀ k, j (s k) ∈ Submodule.span Ω' (Set.range b₀) := by
    intro k
    obtain ⟨T, hT⟩ := exists_mat (Ω := Ω) (b := s) (s := b) fun k => by
      rw [hb, ← hsU]; exact Submodule.subset_span ⟨k, rfl⟩
    rw [hT k, map_sum]
    exact Submodule.sum_mem _ fun k' _ => by rw [hj]; exact Submodule.smul_mem _ _ (hjb k')
  obtain ⟨T₁, hT₁⟩ := exists_mat hjs
  have main : ∀ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (detLat L s).IsGenAt ⟨f q.1, h⟩ t ∧
      (detLat (L.pull ξ' f j) b₀).IsGenAt q (T₁.det * i t) := by
    intro q h
    obtain ⟨_, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q
    obtain ⟨U₂, hU₂, c, hc, hcf⟩ := hL ⟨f q.1, h⟩ trivial
    have hcf' := hcf _ trivial hU₂
    obtain ⟨T, hT⟩ := exists_mat (Ω := Ω) (b := c) (s := s) fun k => by
      rw [hsU, ← hc]; exact Submodule.subset_span ⟨k, rfl⟩
    refine ⟨T.det, GlobalTheory.CompanionTheory.Relay.det_lattice_frame_gen X Ω ξ V L r s c T _ hs hcf' hT, ?_⟩
    have h2 := GlobalTheory.CompanionTheory.Relay.det_lattice_frame_gen X' Ω' ξ' V' (L.pull ξ' f j) r b₀ (fun k => j (c k)) (T₁ * i.mapMatrix T) q hb₀
      (frame_pull hj (hli _ _ hcf'.1) h hreg hcf') fun k => by
        rw [hT k, map_sum]
        simp only [hj, hT₁, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul, RingHom.mapMatrix_apply,
          Matrix.map_apply]
        rw [Finset.sum_comm]
        simp only [mul_comm]
    rwa [Matrix.det_mul, ← RingHom.map_det] at h2
  obtain ⟨t, -, ht⟩ := main g hg
  exact ⟨T₁.det, left_ne_zero_of_mul ht.1, main⟩

theorem deg_pull {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} {Λ' : I → Lat ξ' Ω'} {u : I → Ω'} (hu : ∀ τ, u τ ≠ 0)
    (hd : Dominates ξ' ξ f i)
    (hcov : ∀ p : Cpt ξ, ∃ c, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p)
    (hΛ : ∀ τ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (Λ τ).IsGenAt ⟨f q.1, h⟩ t ∧ (Λ' τ).IsGenAt q (u τ * i t))
    {K' : Type} [Fintype K'] {J' : K' → Type} {y' : (Σ k, J' k) → Ω'} {bk : K → K'} {bx : ∀ k, J k ≃ J' (bk k)}
    (hbk : Function.Injective bk) (hy : ∀ k x, y' ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) {a : K → ℤ} {a' : K' → ℤ}
    (ha : ∀ k, a' (bk k) = a k) (ha' : ∀ k', k' ∉ Set.range bk → a' k' = 0) {e₀ : Ω}
    (h : (Lat.tens Λ fun _ => -1).IsDegOn Set.univ y a e₀) :
    ((Lat.tens Λ' fun _ => -1).scale (∏ τ, u τ)).IsDegOn Set.univ y' a' (i e₀) := by
  refine ⟨(map_ne_zero i).2 h.1, fun q _ c' hc' => ?_⟩
  obtain ⟨hq, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q
  obtain ⟨c, hc⟩ := hcov ⟨f q.1, hq⟩
  choose t ht ht' using fun τ => hΛ τ q hq
  have g1 := uMap hreg (gen_unit (deg_gen h hc) (Flag.tens_gen Λ (fun _ => -1) _ t ht))
  have g2 := gen_scale (Finset.prod_ne_zero_iff.2 fun τ _ => hu τ : ∏ τ, u τ ≠ 0)
    (Flag.tens_gen Λ' (fun _ => -1) q _ ht')
  have g3 : ∀ k, unitAt ξ' q (y' ⟨bk k, c' (bk k)⟩ / i (y ⟨k, c k⟩)) := fun k => by
    refine ⟨div_ne_zero (chart_ne hc' _) ((map_ne_zero i).2 (chart_ne hc k)), ?_, ?_⟩
    · have := hreg _ (chart_ratio hc k ((bx k).symm (c' (bk k))))
      rwa [map_div₀, ← hy, Equiv.apply_symm_apply] at this
    · rw [inv_div, ← hy]
      exact chart_ratio hc' _ _
  have g4 := uMul (uProd fun k => uZpow (g3 k) (a k)) g1
  have e1 : ∏ k', y' ⟨k', c' k'⟩ ^ a' k' = ∏ k, y' ⟨bk k, c' (bk k)⟩ ^ a k := by
    symm
    refine Fintype.prod_of_injective bk hbk _ _ (fun k' hk' => ?_) fun k => by rw [ha]
    rw [ha' k' hk', zpow_zero]
  have e2 : (∏ τ, u τ) * ∏ τ, (u τ * i (t τ)) ^ (-1 : ℤ) = i (∏ τ, t τ ^ (-1 : ℤ)) := by
    rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have := hu τ
    rw [map_zpow₀, zpow_neg_one, zpow_neg_one, mul_inv, mul_inv_cancel_left₀ this]
  rw [e2] at g2
  refine (gen_of_unit (s := (∏ k', y' ⟨k', c' k'⟩ ^ a' k') * i e₀) g2 ?_).2
  convert g4 using 1
  have e3 : i (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 :=
    (map_ne_zero i).2 (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_ne hc k))
  have e4 : ∏ k, (y' ⟨bk k, c' (bk k)⟩ / i (y ⟨k, c k⟩)) ^ a k =
      (∏ k, y' ⟨bk k, c' (bk k)⟩ ^ a k) / i (∏ k, y ⟨k, c k⟩ ^ a k) := by
    rw [map_prod, ← Finset.prod_div_distrib]
    simp only [div_zpow, map_zpow₀]
  rw [e1, e4, map_div₀, map_mul, ← mul_div_assoc, ← _root_.mul_assoc, div_mul_cancel₀ _ e3]

end GlobalTheory.CompanionTheory.Ar.Cusp.DetNef
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreUniformisedFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_uniformised_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → Z.IsGeom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isGeom_of_period | exact GlobalTheory.CompanionTheory.Ar.Flat.isGeom_of_period | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isGeom_of_period <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricComponentAlgClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_component_alg_closed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Formalism.L2.Pj.Comp Xo c) (Z' : CptOver Y (Z : Set (Xo.XF c))), FracBase β → Formalism.L2.Pj.FnAlgClosed Xo c → Z'.IsGeom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.isGeom_of_fnAlgClosed | exact GlobalTheory.CompanionTheory.Ar.Br.isGeom_of_fnAlgClosed | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.isGeom_of_fnAlgClosed <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedBaseChangeIffFibersStatement
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_baseChange_iff_fibers : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k), GeometricallyConnected (pullback.snd p (spMap (algebraMap k V))) ↔ ∀ x ∈ Set.range (PrimeSpectrum.comap (algebraMap k V)), GeometricallyConnected (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField | exact GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentLabelFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_label_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (lab : CMType H ⊕ CMType H) (r : ℕ) (s : Fin r → 𝔐.Li) (h : genPt 𝔐.ξ ⤳ centre z), (𝔐.V lab).IsFrameAt s ⟨centre z, h⟩ → ∀ i, ∃ v : epsAt z ⟶ 𝔐.t.G, 𝔐.M.ValAt z (s i) v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeVal.frame_valAt | exact GlobalTheory.CompanionTheory.Ar.HodgeVal.frame_valAt | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeVal.frame_valAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicEndomorphismFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_endomorphism_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (ρ : ℝ) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M (Metric.ball 0 ρ) ψ), 0 < ρ → ∃ B : (Fin n → ℂ) → (𝓞 E →+* Module.End ℂ (Fin g → ℂ)), (∀ c x, DifferentiableOn ℂ (fun b => B b c x) (Metric.ball 0 ρ)) ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ c x, e.ex b (B b c x) = e.ex b x ≫ t.act.act c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ActFam.exists_action_family | exact GlobalTheory.CompanionTheory.Ar.Flat.ActFam.exists_action_family | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ActFam.exists_action_family <;> assumption)
end

