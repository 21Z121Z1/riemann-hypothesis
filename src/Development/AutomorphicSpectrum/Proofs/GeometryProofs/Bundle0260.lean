import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0259
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0054
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0051
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0059
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0209
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0181
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0200
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0150
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0085
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0247
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormNotInCoordIdeal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0217
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0084
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0187
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0248
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0252
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0243
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0175
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0121
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0033
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionSupNormFieldExtension
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryPointsClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_points_closed : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (T : Set X) (bd : Ideal (MRing J)), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ centre z ∉ T)) → IsClosed ((↑) ⁻¹' (mcPts (mCoordIdeal y) ∩ mcPts bd) : Set (mcPts (mCoordIdeal y))) ∧ (∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd) ∧ ∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, conjVec z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BdSym.boundary_closed_torus_conj | exact GlobalTheory.CompanionTheory.Ar.BdSym.boundary_closed_torus_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.BdSym.boundary_closed_torus_conj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConjugatePointSameCentreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_point_same_centre : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), centre (spMap (starRingEnd ℂ) ≫ z) = centre z ∧ (CoordsAt ξ y z w → CoordsAt ξ y (spMap (starRingEnd ℂ) ≫ z) (conjVec w)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj | exact GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CptFlatInputsOfPropZ
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptIn

theorem orderAt_of_unit {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Lat ξ Ω} {σ ϖ ϖ' : Ω}
    {M : ℕ} {a : ℤ} {p : Cpt ξ} (h : OrderAt L σ ϖ M a p) (hu : unitAt ξ p (ϖ / ϖ')) : OrderAt L σ ϖ' M a p := by
  obtain ⟨e, c, he, hL, hσ, hc⟩ := h
  refine ⟨e, c, he, hL, hσ, ?_⟩
  have h0 : ϖ ≠ 0 := fun h => hu.1 (by simp [h])
  have h1 : ϖ' ≠ 0 := fun h => hu.1 (by simp [h])
  have hz : ∀ n : ℤ, unitAt ξ p ((ϖ / ϖ') ^ n) := fun n => by
    cases n with
    | ofNat m => simpa using ZUnit.pow hu m
    | negSucc m => simpa using ZUnit.inv (ZUnit.pow hu (m + 1))
  have : c ^ M / ϖ' ^ a = c ^ M / ϖ ^ a * (ϖ / ϖ') ^ a := by
    rw [div_zpow]
    field_simp
  rw [this]
  exact ZUnit.mul hc (hz a)

theorem exists_orders (hZ : PropZ) {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {κ : Type} [Finite κ] {x : κ → Ω} {F' : Type} [Field F'] [NumberField F'] (ψ : F' →+* Ω)
    (hcl : ∀ x : Ω, (∃ f : Polynomial F', f ≠ 0 ∧ f.eval₂ ψ x = 0) → x ∈ Set.range ψ)
    (hall : ∀ q : X, genPt ξ ⤳ q) (ht : CoordTie ℤ ξ x) (hN : NormalCpt ξ) (L : Lat ξ Ω) (σ : Ω)
    (hL : L.IsVB 1 ⊤) (hg : ∀ p ∈ genFibre ℤ ξ, L.IsGenAt p σ)
    (hp : ∀ ℓ : ℕ, ℓ.Prime → TrivMod L (ℓ : Ω) ∨ NumTrivMod L (ℓ : Ω)) :
    ∃ r : HeightOneSpectrum (𝓞 F') →₀ ℚ, ∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'),
      v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * r v ∧ ∀ p : Cpt ξ,
        (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) → OrderAt L σ (ψ π) m k p := by
  classical
  have hchar : CharZero Ω := charZero_of_injective_ringHom ψ.injective
  have hplace : ∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) →
      ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) →
        OrderAt L σ (ψ π) M a p := by
    intro v π hπ
    obtain ⟨O, _, _, _, _, X', ξ', s, g, ϖ, hs, hϖ, hinj, hξs, hξg, hgen', hall', hϖπ, hrange, hreg, hsurj⟩ :=
      GlobalTheory.T.dvr_model_of_number_field_place X Ω ξ κ x F' ψ v π hall ht hN hπ
    obtain ⟨ℓ, hℓ, hℓv⟩ := GlobalTheory.T.exists_prime_dividing_uniformizer F' v π hπ
    obtain ⟨u, hu⟩ : ∃ u : O, algebraMap O Ω u = ψ ((ℓ : F') / π) :=
      (hrange _).2 ⟨_, hℓv, rfl⟩
    have hπ0 : π ≠ 0 := by
      rintro rfl
      simp at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hcc : ConstClosed O Ω := by
      intro a ha
      obtain ⟨f, hf, hfa⟩ := ha
      have hlift : f.map (algebraMap O Ω) ∈ Polynomial.lifts ψ := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        rw [Polynomial.coeff_map]
        obtain ⟨b, -, hb⟩ := (hrange _).1 ⟨f.coeff n, rfl⟩
        exact ⟨b, hb⟩
      obtain ⟨f', hf'⟩ := (Polynomial.mem_lifts _).1 hlift
      have hne : f' ≠ 0 := by
        rintro rfl
        rw [Polynomial.map_zero] at hf'
        exact hf ((Polynomial.map_eq_zero_iff hinj).1 hf'.symm)
      obtain ⟨b, rfl⟩ := hcl a ⟨f', hne, by
        rw [← Polynomial.eval_map, hf', Polynomial.eval_map]
        exact hfa⟩
      by_cases hb : v.valuation F' b ≤ 1
      · obtain ⟨x₀, hx₀⟩ := (hrange (ψ b)).2 ⟨b, hb, rfl⟩
        exact ⟨x₀, 1, one_ne_zero, by rw [map_one, mul_one]; exact hx₀.symm⟩
      · have hb0 : b ≠ 0 := by
          rintro rfl
          simp at hb
        have hb' : v.valuation F' b⁻¹ ≤ 1 := by
          rw [map_inv₀]
          exact inv_le_one_of_one_le₀ (le_of_not_ge hb)
        obtain ⟨y₀, hy₀⟩ := (hrange (ψ b⁻¹)).2 ⟨b⁻¹, hb', rfl⟩
        refine ⟨1, y₀, ?_, ?_⟩
        · rintro rfl
          rw [map_zero] at hy₀
          exact inv_ne_zero hb0 ((map_eq_zero ψ).1 hy₀.symm)
        · rw [hy₀, ← map_mul, mul_inv_cancel₀ hb0, map_one, map_one]
    have hℓu : (ℓ : Ω) = algebraMap O Ω (ϖ * u) := by
      rw [map_mul, hϖπ, hu, ← map_mul, mul_div_cancel₀ _ hπ0, map_natCast]
    obtain ⟨M, a, hM, h⟩ := @GlobalTheory.T.proper_dvr_model_lattice_valuation X X' Ω _ _ ξ ξ' g O _ _ _ _ s hs ϖ L σ ℓ u hZ hϖ hinj hξs hξg ht.gen hgen' hall'
      hN hcc hreg hL hg hℓu (hp ℓ hℓ)
    refine ⟨M, a, hM, fun p hv => ?_⟩
    have := h p (hsurj p hv)
    rwa [hϖπ] at this
  obtain ⟨s, hs1, hs2, hs3⟩ := GlobalTheory.T.finite_type_over_integers_model X Ω ξ κ x hall ht
  obtain ⟨n, hn, hgn⟩ := @GlobalTheory.T.lattice_generator_invert_constant X Ω _ ξ ℤ _ _ _ s _ hs1 hs2 hs3 (Int.cast_injective) ht.gen L Set.univ 1 σ
    one_ne_zero (fun _ _ => trivial) hL hg
  have hn' : ((n : F'))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hn)
  have hfin := HeightOneSpectrum.Support.finite (𝓞 F') ((n : F'))⁻¹
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F') => v.valuation_exists_uniformizer F'
  choose M a hM hord using fun v => hplace v (π v) (hπ v)
  let T := HeightOneSpectrum.Support (𝓞 F') ((n : F'))⁻¹
  let r₀ : HeightOneSpectrum (𝓞 F') → ℚ := fun v => if v ∈ T then (a v : ℚ) / M v else 0
  have hr₀ : (Function.support r₀).Finite := hfin.subset fun v hv => by
    by_contra h
    exact hv (if_neg h)
  refine ⟨Finsupp.ofSupportFinite r₀ hr₀, fun v π' hπ' => ?_⟩
  have hrv : (Finsupp.ofSupportFinite r₀ hr₀) v = r₀ v := rfl
  rw [hrv]
  by_cases hv : v ∈ T
  · have hMv : (M v : ℚ) ≠ 0 := by exact_mod_cast (hM v).ne'
    refine ⟨M v, a v, hM v, by simp only [r₀, if_pos hv]; field_simp, fun p hp => ?_⟩
    refine orderAt_of_unit (hord v p hp) ?_
    have h0 : π' ≠ 0 := by
      rintro rfl
      simp at hπ'
      exact WithZero.exp_ne_zero hπ'.symm
    have h1 : π v ≠ 0 := by
      intro h
      have := hπ v
      rw [h] at this
      simp at this
      exact WithZero.exp_ne_zero this.symm
    have e1 : v.valuation F' (π v / π') = 1 := by
      rw [map_div₀, hπ v, hπ', div_self (WithZero.exp_ne_zero)]
    have e2 : v.valuation F' (π v / π')⁻¹ = 1 := by rw [map_inv₀, e1, inv_one]
    rw [← map_div₀]
    exact ⟨(map_ne_zero ψ).2 (div_ne_zero h1 h0), hp _ e1.le, by rw [← map_inv₀]; exact hp _ e2.le⟩
  · refine ⟨1, 0, one_pos, by simp only [r₀, if_neg hv]; simp, fun p hp => ?_⟩
    have h1 : v.valuation F' (n : F') ≤ 1 := by
      have := v.valuation_le_one (K := F') (n : 𝓞 F')
      simpa using this
    have h2 : v.valuation F' ((n : F'))⁻¹ ≤ 1 := not_lt.1 hv
    have hu : unitAt ξ p (algebraMap ℤ Ω n) := by
      have e : algebraMap ℤ Ω n = ψ (n : F') := by simp
      rw [e]
      exact ⟨(map_ne_zero ψ).2 (by exact_mod_cast hn), hp _ h1, by rw [← map_inv₀]; exact hp _ h2⟩
    have := hgn p hu
    exact orderAt_one_zero.2 this

theorem isCoeffAt_of_smul {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] {A B : Lat ξ V} {p q : ℕ} {a a' : ⋀[Ω]^p V} {b b' : ⋀[Ω]^q V} {x : Cpt ξ}
    {d₁ d₂ : Ω} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (ea : a' = d₁ • a) (eb : b' = d₂ • b)
    (h : IsCoeffAt A B p q a' b' x 1) : IsCoeffAt A B p q a b x (d₁ / d₂)⁻¹ := by
  obtain ⟨α, β, hα, hβ, hA, hB, e⟩ := h
  rw [one_mul] at e
  subst e
  refine ⟨α * d₁, α * d₂, mul_ne_zero hα h₁, mul_ne_zero hα h₂, ?_, ?_, ?_⟩
  · rw [hA, ea, smul_smul]
  · rw [hB, eb, smul_smul]
  · field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.CptIn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemWeightLeft
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx

open GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {Xo : ∀ l : Tor.Level H, Moduli D l}
  {l : Tor.Level H} {c : Coeff l} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type}
  [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  {S₀ : Finset ℕ}

def IsWeightAt (Or : CptOrigin Y S₀ Dc Hd) (z : Sp ℂ ⟶ Or.𝔐.X) (x : ℝ) : Prop :=
  ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (R : RiemLat E g Λ) (σ : CMType H → (𝓞 E →+* ℂ)),
    FibreLat Or.𝔐.t z R ∧ Or.𝔐.LabVal z Or.sm σ ∧ x = R.cuspW σ

theorem IsWeightAt.unique {Or : CptOrigin Y S₀ Dc Hd} {z : Sp ℂ ⟶ Or.𝔐.X} {x x' : ℝ} (h : IsWeightAt Or z x)
    (h' : IsWeightAt Or z x') : x = x' := by
  obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩ := h
  obtain ⟨g', Λ', i₃, i₄, R', σ', hF', hL', rfl⟩ := h'
  have hσ : σ' = σ := funext fun τ => RingHom.ext fun a =>
    valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (hL' τ a) (hL τ a)
  subst hσ
  obtain ⟨φ, h1, h2, h3, -⟩ := GlobalTheory.CompanionTheory.Ar.Cusp.FibreUnique.exists_linearEquiv_of_fibreLatVec E H Or.𝔐.X Or.𝔐.t z g' g Λ' Λ R' R Empty _ _ _ hF' hF
  exact (GlobalTheory.T.cusp_weight_invariant_under_isometry E g' Λ' (CMType H) R' σ' g Λ R φ (isCMFam_of_labVal Or hL) h1 h2 h3).1.symm ▸ rfl

theorem IsWeightAt.nonneg {Or : CptOrigin Y S₀ Dc Hd} {z : Sp ℂ ⟶ Or.𝔐.X} {x : ℝ} (h : IsWeightAt Or z x) : 0 ≤ x := by
  obtain ⟨g, Λ, i₁, i₂, R, σ, -, -, rfl⟩ := h
  exact le_max_left _ _

theorem exists_isWeightAt (hG : Top.Given) (Or : CptOrigin Y S₀ Dc Hd) {z : Sp ℂ ⟶ Or.𝔐.X} (hz : Or.𝔐.Interior z) :
    ∃ x, IsWeightAt Or z x := by
  have hpq : 1 ≤ D.p + D.q := by
    have := Dc.two_le_N
    rw [Or.N_eq] at this
    omega
  obtain ⟨g, Λ, i₁, i₂, R, x, hF, -, -⟩ := GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx.exists_riemLat_of_interior hG.2.2.2.2.1 E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 z hpq hz hG
    Empty (fun i => i.elim) (fun i => i.elim)
  obtain ⟨σ₀, h0, -⟩ := GlobalTheory.T.cusp_correspondence_bound E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 ℂ z
  have hx : x = fun i => i.elim := funext fun i => i.elim
  subst hx
  exact ⟨_, g, Λ, i₁, i₂, R, fun τ => σ₀ (Or.sm τ), hF, fun τ a => h0 (Or.sm τ) a, rfl⟩

theorem IsWeightAt.conj {Or : CptOrigin Y S₀ Dc Hd} {z : Sp ℂ ⟶ Or.𝔐.X} {x : ℝ} (h : IsWeightAt Or z x) :
    IsWeightAt Or (spMap (starRingEnd ℂ) ≫ z) x := by
  obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩ := h
  obtain ⟨-, R', hP, hH, hB, hW⟩ := GlobalTheory.T.cusp_weight_invariant_under_conjugation E g Λ (CMType H) R σ (isCMFam_of_labVal Or hL)
  have hF' : FibreLat Or.𝔐.t (spMap (starRingEnd ℂ) ≫ z) R' :=
    (GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move E H Or.𝔐.X Or.𝔐.X Or.𝔐.t Or.𝔐.t (𝟙 _) g Λ R R' z).2 hP hH
      (fun a x => by simpa using hB a (star x)) hF
  exact ⟨g, Λ, i₁, i₂, R', fun τ => (starRingEnd ℂ).comp (σ τ), hF',
    fun τ a => GlobalTheory.CompanionTheory.Ar.HodgeLine.valAt_conj (hL τ a), hW.symm⟩

def HasWeight (Or : CptOrigin Y S₀ Dc Hd) (w : (Σ k, J k) → ℂ) (x : ℝ) : Prop :=
  ∃ z : Sp ℂ ⟶ Or.𝔐.X, CoordsAt Or.𝔐.ξ Dc.y z w ∧ Or.𝔐.Interior z ∧ IsWeightAt Or z x

theorem HasWeight.unique {Or : CptOrigin Y S₀ Dc Hd} {w : (Σ k, J k) → ℂ} {x x' : ℝ} (h : HasWeight Or w x)
    (h' : HasWeight Or w x') : x = x' := by
  obtain ⟨z, hz, -, hx⟩ := h
  obtain ⟨z', hz', -, hx'⟩ := h'
  have e := GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.point_eq_of_coordsAt _ _ _ K J Dc.y Or.𝔐.tie Or.𝔐.normal Or.𝔐.all z z' w hz hz'
  subst e
  exact hx.unique hx'

theorem HasWeight.torus {Or : CptOrigin Y S₀ Dc Hd} {w : (Σ k, J k) → ℂ} {x : ℝ} (h : HasWeight Or w x) {a : K → ℂ}
    (ha : ∀ k, a k ≠ 0) : HasWeight Or (torusSmul a w) x := by
  obtain ⟨z, hz, hi, hx⟩ := h
  exact ⟨z, coordsAt_torusSmul Or.𝔐.ξ hz ha, hi, hx⟩

theorem HasWeight.conj {Or : CptOrigin Y S₀ Dc Hd} {w : (Σ k, J k) → ℂ} {x : ℝ} (h : HasWeight Or w x) :
    HasWeight Or (conjVec w) x := by
  obtain ⟨z, hz, hi, hx⟩ := h
  have hc := GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y z w
  refine ⟨_, hc.2 hz, ?_, hx.conj⟩
  show centre _ ∈ _
  rw [hc.1]
  exact hi

theorem exists_cuspWeight : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd), ∃ U : ((Σ k, J k) → ℂ) → ℝ, Or.𝔐.IsCuspWeight Or.sm U ∧ (∀ w, 0 ≤ U w) ∧ (∀ w (a : K → ℂ), (∀ k, a k ≠ 0) → U (torusSmul a w) = U w) ∧ (∀ w, U (conjVec w) = U w) ∧ ∀ U', Or.𝔐.IsCuspWeight Or.sm U' → ∀ w ∈ Dc.Xo, U' w = U w := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or
  classical
  let U : ((Σ k, J k) → ℂ) → ℝ := fun w => if h : ∃ x, HasWeight Or w x then h.choose else 0
  have hU : ∀ {w x}, HasWeight Or w x → U w = x := fun {w x} h => by
    have hex : ∃ x, HasWeight Or w x := ⟨x, h⟩
    simp only [U, dif_pos hex]
    exact hex.choose_spec.unique h
  have hU0 : ∀ {w}, (¬ ∃ x, HasWeight Or w x) → U w = 0 := fun {w} h => by
    simp only [U, dif_neg h]
  have hw : ∀ {z : Sp ℂ ⟶ Or.𝔐.X} {w} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ)
      {σ : CMType H → (𝓞 E →+* ℂ)}, CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → FibreLat Or.𝔐.t z R →
      Or.𝔐.LabVal z Or.sm σ → HasWeight Or w (R.cuspW σ) := by
    intro z w g Λ i₁ i₂ R σ hz hi hF hL
    exact ⟨z, hz, hi, g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩
  refine ⟨U, fun z w hz hi => ?_, fun w => ?_, fun w a ha => ?_, fun w => ?_, fun U' hU' w hX => ?_⟩
  · obtain ⟨x, g, Λ, i₁, i₂, R, σ, hF, hL, rfl⟩ := exists_isWeightAt hG Or hi
    exact ⟨g, Λ, i₁, i₂, R, σ, hF, hL, hU (hw R hz hi hF hL)⟩
  · by_cases h : ∃ x, HasWeight Or w x
    · obtain ⟨x, hx⟩ := h
      rw [hU hx]
      obtain ⟨z, -, -, hz⟩ := hx
      exact hz.nonneg
    · rw [hU0 h]
  · by_cases h : ∃ x, HasWeight Or w x
    · obtain ⟨x, hx⟩ := h
      rw [hU hx, hU (hx.torus ha)]
    · have h' : ¬ ∃ x, HasWeight Or (torusSmul a w) x := fun ⟨x, hx⟩ => h ⟨x, by
        have e : torusSmul (fun k => (a k)⁻¹) (torusSmul a w) = w := by
          funext q
          show (a q.1)⁻¹ * (a q.1 * w q) = w q
          rw [inv_mul_cancel_left₀ (ha q.1)]
        have := hx.torus (a := fun k => (a k)⁻¹) fun k => inv_ne_zero (ha k)
        rwa [e] at this⟩
      rw [hU0 h, hU0 h']
  · by_cases h : ∃ x, HasWeight Or w x
    · obtain ⟨x, hx⟩ := h
      rw [hU hx, hU hx.conj]
    · have h' : ¬ ∃ x, HasWeight Or (conjVec w) x := fun ⟨x, hx⟩ => h ⟨x, by
        have e : conjVec (conjVec w) = w := by
          funext q
          exact Complex.conj_conj (w q)
        have := hx.conj
        rwa [e] at this⟩
      rw [hU0 h, hU0 h']
  · obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).1 hX.1
    have hi : Or.𝔐.Interior z := by
      by_contra hn
      exact hX.2 ((Or.bd z w hz).2 hn)
    obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, he⟩ := hU' z w hz hi
    rw [he, hU (hw R hz hi hF hL)]

end GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleFieldExtMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

open GlobalTheory.CompanionTheory.Ar.Sl.ExtTrans

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.PullSec

variable {X X' : Scheme.{0}} {M : LB X} {M' : LB X'} {F : X' ⟶ X}

def IsMoved (w : LB.Iso M' (M.pull F)) (s : M.Sec) (s' : M'.Sec) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : M.ι) (k : M'.ι), F (r z) ∈ M.U j → r z ∈ M'.U k →
    gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k)

theorem IsMoved.mem_nonzeroLocus {w : LB.Iso M' (M.pull F)} (hM : M.IsLB) (hM' : M'.IsLB) {s : M.Sec} {s' : M'.Sec}
    (h : IsMoved w s s') {y : X'} (hy : F y ∈ Out.nonzeroLocus s) : y ∈ Out.nonzeroLocus s' := by
  obtain ⟨j, hj⟩ := exists_chart hM (F y)
  obtain ⟨k, hk⟩ := exists_chart hM' y
  have u := (mem_nonzeroLocus_iff_pull s F y hj).1 hy
  have e := h X' (𝟙 X') y j k hj hk
  rw [Category.id_comp] at e
  rw [e] at u
  exact (mem_nonzeroLocus_iff_isUnit s' hk).2 ((Units.isUnit_units_mul _ _).1 u)

variable {R R' : Type} [CommRing R] [CommRing R'] {p : X ⟶ Sp R} {p' : X' ⟶ Sp R'}

theorem IsMoved.smul {w : LB.Iso M' (M.pull F)} (hM : M.IsLB) (c : R →+* R') (hc : F ≫ p = p' ≫ spMap c) (a : R)
    {s : KeyGen.SecMod p M} {s' t' : KeyGen.SecMod p' M'} (hs : IsMoved w s s') (ht : IsMoved w (a • s : KeyGen.SecMod p M) t') :
    t' = c a • s' := by
  refine KeyGen.SecMod.ext fun k => fn_ext fun y hy => ?_
  obtain ⟨j, hj⟩ := exists_chart hM (F y)
  have e₁ := hs X' (𝟙 X') y j k hj hy
  have e₂ := ht X' (𝟙 X') y j k hj hy
  have hj' : (𝟙 X' ≫ F) y ∈ M.U j := by rwa [Category.id_comp]
  have hy' : (𝟙 X') y ∈ M'.U k := hy
  have ec : cst ((𝟙 X' ≫ F) ≫ p) y a = cst (𝟙 X' ≫ p') y (c a) := by
    rw [Category.assoc, hc, ← Category.assoc, cst_comp]
  rw [KeyGen.smul_f, gs_mul _ y _ hj', gs_constFn p _ _ y hj', ec, e₁, mul_left_comm] at e₂
  rw [KeyGen.smul_f, gs_mul _ y _ hy', gs_constFn p' _ _ y hy']
  exact ((Units.isUnit _).mul_right_inj.1 e₂).symm

theorem exists_moved {w : LB.Iso M' (M.pull F)} (hw : PGen w) (hM : M.IsLB) (hM' : M'.IsLB) (s : M.Sec) :
    ∃ s' : M'.Sec, IsMoved w s s' :=
  sec_pull_down hw hM hM' s

theorem exists_lift {S S' Y Y' : Scheme.{0}} {φ : Y' ⟶ Y} {q' : Y' ⟶ S'} {q : Y ⟶ S} {f : S' ⟶ S}
    (h : IsPullback φ q' q f) (b' : S') (y : Y) (e : q y = f b') : ∃ y' : Y', q' y' = b' ∧ φ y' = y := by
  obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := f) y b' e
  refine ⟨h.isoPullback.inv z, ?_, ?_⟩
  · rw [← hz', ← Scheme.Hom.comp_apply, h.isoPullback_inv_snd]
  · rw [← hz, ← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.PullSec

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

open PullSec

theorem exists_pull_sec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'] (D' : PPData H L') (_ : D.Ext D'), ∃ P : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))) → SecMod D'.t.G.hom (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), (∀ (a : 𝓞 L) s, P (a • s) = algebraMap (𝓞 L) (𝓞 L') a • P s) ∧ ∀ (s : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) (b' : Sp (𝓞 L')) (y : D.t.G.left), D.t.G.hom y = spMap (algebraMap (𝓞 L) (𝓞 L')) b' → y ∈ Out.nonzeroLocus (M := (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) s → ∃ y' : D'.t.G.left, D'.t.G.hom y' = b' ∧ y' ∈ Out.nonzeroLocus (M := (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) (P s) := by
  intro E _ _ _ H L _ _ D L' _ _ _ D' m
  obtain ⟨w, gw, -, -⟩ := (isPullCubical_iff m.cm D.t.cub D'.t.cub).1 m.lin
  have hM : (PowB D.t.PP.L 1).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB D.t.PP.L D.t.PP.isLB _ _
  have hM' : (PowB D'.t.PP.L 1).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB D'.t.PP.L D'.t.PP.isLB _ _
  have hex := fun s : (PowB D.t.PP.L 1).Sec => exists_moved (pGen_powIso gw 1) hM hM' s
  choose P hP using hex
  refine ⟨P, fun a s => ?_, fun s b' y e hy => ?_⟩
  · exact IsMoved.smul (p := D.t.G.hom) (p' := D'.t.G.hom) hM (algebraMap (𝓞 L) (𝓞 L')) m.cart.1.w a (hP s) (hP (a • s))
  · obtain ⟨y', h₁, h₂⟩ := exists_lift m.cart.1 b' y e
    exact ⟨y', h₁, (hP s).mem_nonzeroLocus hM hM' (by rw [h₂]; exact hy)⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionSupNormFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_sup_norm_field_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'] (D' : PPData H L') (_ : D.Ext D') (n : ℕ) (s : Out.H0 D.t.PP.L n), ∃ s' : Out.H0 D'.t.PP.L n, (∀ M : (L →+* ℂ) → ℝ, D.SupLe s M → D'.SupLe s' fun σ' => M (σ'.comp (algebraMap L L'))) ∧ ∀ (σ' : L' →+* ℂ) (a' : D'.Frame σ'), ∃ a : ArchFrame D.t.PP (emb (σ'.comp (algebraMap L L'))) D'.g, a.u.Λ = a'.u.Λ ∧ a.Hm = a'.Hm ∧ ∀ θ, a.IsFn s θ ↔ a'.IsFn s' θ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.ExtTrans.exists_section | exact GlobalTheory.CompanionTheory.Ar.Sl.ExtTrans.exists_section | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.ExtTrans.exists_section <;> assumption)
end

