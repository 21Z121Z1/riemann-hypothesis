import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0024
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0079
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0115
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightParameterMemUnitInterval
import Development.AbelianVarietyTheory.Definitions.Jets.CubWeilOneIffPairOne

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniversalJetCoordinatesPullback
section
noncomputable section

namespace GlobalTheory.UnivJetBaseChange

section General
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.ChartBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback)
attribute [local instance] Over.cartesianMonoidalCategory

variable {R R' : Type} [CommRing R] [CommRing R']

def IsUnivSp (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (κ : Type)
    (x : ∀ m : ℕ, sp (R₀ := R) (JetR R κ m) ⟶ G) : Prop :=
  (∀ m, spMap (jetTruncR R κ m) ≫ x (m + 1) = x m) ∧ (∀ m, spMap (jetAug R κ m) ≫ x m = 1) ∧
  ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), RingHom.ker aug ^ (m + 1) = ⊥ →
    ∀ y : sp (R₀ := R) A ⟶ G, spMap aug ≫ y = 1 →
      ∃! ψ : JetR R κ m →ₐ[R] A, aug.comp ψ = jetAug R κ m ∧ y = spMap ψ ≫ x m

variable [Algebra R R'] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)

theorem isUnivSp_baseChange [IsLocalRing R] {κ : Type} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R κ m) ⟶ G}
    (hx : IsUnivSp G κ x) {x' : ∀ m : ℕ, sp (R₀ := R') (JetR R' κ m) ⟶ G'}
    (hx' : ∀ m, push hπ (x' m) = spMap (jetCoeff R R' κ m) ≫ x m) :
    IsUnivSp G' κ x' := by
  refine ⟨fun m => push_injective hπ ?_, fun m => push_injective hπ ?_, ?_⟩
  · rw [push_spMap, hx', hx', ← hx.1 m, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp]
    congr 2
    refine jet_ext fun j => ?_
    show jetTruncR R' _ m (jetCoeff R R' _ _ (zR _ j)) = jetCoeff R R' _ _ (zR _ j)
    rw [jetCoeff_zR, jetCoeff_zR]
    rfl
  · rw [push_spMap, hx', push_one, ← Category.assoc, spMap_comp]
    have : ((jetAug R' κ m).restrictScalars R).comp (jetCoeff R R' κ m) =
        (Algebra.ofId R R').comp (jetAug R κ m) := by
      refine jet_ext fun j => ?_
      show jetAug R' _ m (jetCoeff R R' _ _ (zR _ j)) = algebraMap R R' (jetAug R _ m (zR m j))
      rw [jetCoeff_zR, jetAug_zR, jetAug_zR, map_zero]
    rw [this, ← spMap_comp, Category.assoc, hx.2.1, MonObj.comp_one]
  intro A _ _ aug m hJ y hy
  letI : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨C⟩ := exists_chart G
  let q : A →ₐ[R] R' := aug.restrictScalars R
  have hq : Function.Surjective q := fun r => ⟨algebraMap R' A r, aug.commutes r⟩
  have hJq : (RingHom.ker q) ^ (m + 1) = ⊥ := hJ
  obtain ⟨h, hh, hqh⟩ := exists_pt_of_aug C q hq hJq (push hπ y) (by
    rw [← push_spMap, hy, push_one])
  obtain ⟨k, hk, hqk⟩ := exists_pt_of_aug C (jetAug R κ m) (fun r => ⟨algebraMap _ _ r, AlgHom.commutes _ r⟩)
    (ker_jetAug_pow _ m) (x m) (hx.2.1 m)
  let h₀ := fibLift q (eps C) h hqh
  obtain ⟨ψ₀, ⟨ha, hψ₀⟩, hu⟩ := hx.2.2 (fib q) (fibFst q) m (fib_ker q hJq) (ReciprocityTheory.ChartRestriction.G.Chart.pt C h₀) (by
    rw [spMap_pt]
    exact pt_eps_self C)
  have hb : ∀ j, fibSnd q (ψ₀ (zR m j)) ∈ RingHom.ker aug := fun j => by
    show q _ = 0
    rw [fib_cond, show fibFst q (ψ₀ (zR m j)) = 0 from (AlgHom.congr_fun ha _).trans (jetAug_zR m j), map_zero]
  refine ⟨jetLift R' (RingHom.ker aug) hJ _ hb, ⟨jet_ext fun j => ?_, push_injective hπ ?_⟩, ?_⟩
  · rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]
    exact hb j
  · have : ((jetLift R' (RingHom.ker aug) hJ _ hb).restrictScalars R).comp (jetCoeff R R' κ m) =
        (fibSnd q).comp ψ₀ := by
      refine jet_ext fun j => ?_
      show jetLift R' (RingHom.ker aug) hJ _ hb (jetCoeff R R' _ _ (zR _ j)) = _
      rw [jetCoeff_zR, jetLift_zR]
      rfl
    rw [push_spMap, hx', ← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, ← hψ₀, spMap_pt, hh]
    rfl
  · rintro ψ ⟨hψa, hψ⟩
    let v := (ψ.restrictScalars R).comp (jetCoeff R R' κ m)
    have hv : q.comp v = (Algebra.ofId R R').comp (jetAug R κ m) := by
      refine jet_ext fun j => ?_
      show aug.comp ψ (jetCoeff R R' _ _ (zR _ j)) = algebraMap R R' (jetAug R _ m (zR m j))
      rw [jetCoeff_zR, hψa, jetAug_zR, jetAug_zR, map_zero]
    have hvk : h = v.comp k := by
      apply pt_injective C
      rw [← hh, hψ, push_spMap, hx', ← Category.assoc, spMap_comp, hk, spMap_pt]
    have e := hu (fibLift q (jetAug R κ m) v hv) ⟨rfl, by
      rw [hk, spMap_pt]
      congr 1
      refine AlgHom.ext fun s => Subtype.ext (Prod.ext ?_ ?_)
      · exact (AlgHom.congr_fun hqk s).symm
      · exact AlgHom.congr_fun hvk s⟩
    refine jet_ext fun j => ?_
    rw [jetLift_zR, ← e]
    show _ = ψ (jetCoeff R R' _ _ (zR _ j))
    rw [jetCoeff_zR]

end General

section Convert
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

variable {V : Type} [CommRing V] {G : Over (Sp V)} {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B]

def toSp (y : overAt (𝟙 (Sp V)) A ⟶ G) : Chart.sp (R₀ := V) A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _))

def ofSp (y : Chart.sp (R₀ := V) A ⟶ G) : overAt (𝟙 (Sp V)) A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _).symm)

theorem toSp_inj {y y' : overAt (𝟙 (Sp V)) A ⟶ G} : toSp y = toSp y' ↔ y = y' :=
  ⟨fun h => Over.OverMorphism.ext (congrArg (fun k => k.left) h), fun h => h ▸ rfl⟩

theorem toSp_one [GrpObj G] : toSp (1 : overAt (𝟙 (Sp V)) A ⟶ G) = 1 := by
  have : toSp (1 : overAt (𝟙 (Sp V)) A ⟶ G) =
      (Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.comp_id _)) :
        Chart.sp (R₀ := V) A ⟶ overAt (𝟙 (Sp V)) A) ≫ (1 : overAt (𝟙 (Sp V)) A ⟶ G) :=
    Over.OverMorphism.ext (Category.id_comp _).symm
  rw [this, MonObj.comp_one]

theorem isUnivJ_iff [GrpObj G] {κ : Type} (z : GlobalTheory.PowGerm.JetPts G κ) :
    GlobalTheory.PowGerm.IsUnivJ G κ z ↔ IsUnivSp G κ (fun m => toSp (z m)) := by
  refine and_congr (forall_congr' fun m => ?_) (and_congr (forall_congr' fun m => ?_) ?_)
  · rw [← toSp_inj]
    exact Iff.rfl
  · rw [← toSp_inj, toSp_one]
    exact Iff.rfl
  · constructor
    · intro H A _ _ aug m hJ y hy
      have := H A aug m hJ (ofSp y) (by rw [← toSp_inj, toSp_one]; exact hy)
      simp only [← toSp_inj] at this
      exact this
    · intro H A _ _ aug m hJ y hy
      have := H A aug m hJ (toSp y) (by rw [← toSp_inj, toSp_one] at hy; exact hy)
      simp only [← toSp_inj]
      exact this

end Convert

end GlobalTheory.UnivJetBaseChange

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem GlobalTheory.UnivJetBaseChange.exists_univ_pullback : ∀ (V V' : Type) [CommRing V] [IsLocalRing V] [CommRing V'] (φ : V →+* V') (G : Over (Sp V)) [GrpObj G] (G' : Over (Sp V')) [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G (spMap φ) F → ∀ (κ : Type) (z : GlobalTheory.PowGerm.JetPts G κ), GlobalTheory.PowGerm.IsUnivJ G κ z → ∃ z' : GlobalTheory.PowGerm.JetPts G' κ, GlobalTheory.PowGerm.IsUnivJ G' κ z' ∧ ∀ m, (z' m).left ≫ F = spMap (jetCoef φ κ m) ≫ (z m).left := by
  intro V V' _ _ _ φ G _ G' _ F hF κ z hz
  letI : Algebra V V' := φ.toAlgebra
  have hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap V V'))) F := hF
  choose x' hx' using fun m => GlobalTheory.ChartBaseChange.push_surjective hπ
    (Chart.spMap (GlobalTheory.ChartBaseChange.jetCoeff V V' κ m) ≫ GlobalTheory.UnivJetBaseChange.toSp (z m))
  refine ⟨fun m => GlobalTheory.UnivJetBaseChange.ofSp (x' m), (GlobalTheory.UnivJetBaseChange.isUnivJ_iff _).2
    (GlobalTheory.UnivJetBaseChange.isUnivSp_baseChange hπ ((GlobalTheory.UnivJetBaseChange.isUnivJ_iff z).1 hz) hx'), fun m => ?_⟩
  have e : (GlobalTheory.ChartBaseChange.jetCoeff V V' κ m).toRingHom = jetCoef φ κ m :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun p => GlobalTheory.ChartBaseChange.jetCoeff_mk m p)
  rw [← e]
  exact congrArg (fun k => k.left) (hx' m)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentRecursion
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomProd

theorem product_moment : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (l ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a, lenA k r z (Matrix.of x) a ^ 2) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1)) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν hnz
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hNum := hS.1
  have hFam := hS.2.1
  have hSide := hS.2.2.1
  have hSF := hS.2.2.2
  have hk : 1 ≤ k := hNum.1
  have hν0 : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) hν
  obtain ⟨Q, hQ⟩ := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).1 hk
  have hQu : IsUnit Q := hQ.1.1
  have hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E, hE⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r _ _ (R ν') (hFam ν' h') Q hQu
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hE
  have hDS := hFam ν hν0
  obtain ⟨w, hw1, -, hwK, hwF⟩ := GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries hK k r _ _ (R ν) hDS Q (E ν) hQ (hE ν hν0).1
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hk hDS Q (E ν) hQ (hE ν hν0).1
  have hLev := GlobalTheory.lev_zero_of_kHighest _ _ _ (E ν) _ w hMod.1 hMod.2.1 hwK hwF
  have hw1' : ‖(w : (R ν).H)‖ = 1 := hw1
  have hwsm : (w : (R ν).H) ∈ (R ν).sm := w.2
  refine ⟨(w : (R ν).H), hwsm, hw1', ?_⟩
  obtain ⟨hG, -, hlen, hmeas⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide
  obtain ⟨hBeL, hdg, -⟩ := hSF ν hν0
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hSide.2.1
  obtain ⟨⟨hb1, hb2, -, -, -⟩, -⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  have hq2 : ∀ q ≤ (r + 1) ^ 2, 0 + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 := by
    intro q hq
    have : (r + 1) ^ 2 ≤ (2 * r + k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hb : (1 : ℝ) ≤ b := by linarith
  have hA : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) := by
    have : 0 ≤ bv := by linarith
    positivity
  have hmain := GlobalTheory.T.product_moment_bound_density_mass_one (Formalism.QuantumDeterminants.Mt k r) νq r (fun a x => lenA k r z (Matrix.of x) a)
    (fun x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)
    (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) (b ^ 2)
    hlen
    (fun a => hG.mono fun x hx => (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.1 a)
    (((hmeas (l ν) hBeL.1 w hwsm).norm.aemeasurable.pow_const 2).const_mul _)
    (fun x => mul_nonneg hdg.le (by positivity))
    (by
      have := ((GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν0).2 hnz).2 w hwsm
      simpa only [one_mul, hw1', one_pow, ENNReal.ofReal_one] using this)
    hA (one_le_pow₀ hb)
    (fun q hq => by
      have := GlobalTheory.T.family_setup_cayley_recursion hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE q ν
        (by omega) 0 (hq2 q hq) w hLev
      simpa only [hw1, one_pow, mul_one] using this)
    (fun a q hq => by
      have := GlobalTheory.T.family_setup_cayley_bound hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν0
        0 q (hq2 q hq) a w hLev
      simpa only [hw1, one_pow, mul_one] using this)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  exact pow_le_pow_left₀ (mul_nonneg hA (by positivity))
    (GlobalTheory.T.numericalFamily_productBound_constant_le k r lam u b bv ga h q0 _ hNum hT) _

end GlobalTheory.MomProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IdempotentEmbeddingsCard
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EmbCount

theorem exists_equiv (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) :
    ∃ Φ : (E →ₐ[ℚ] C) ≃ (𝓞 E →+* O), ∀ σ (y : 𝓞 E), algebraMap O C (Φ σ y) = σ (y : E) := by
  have hinj := hv.hom_inj
  have h1 : ∀ (σ : E →ₐ[ℚ] C) (y : 𝓞 E), ∃ o : O, algebraMap O C o = σ (y : E) := by
    intro σ y
    have hi : IsIntegral ℤ (σ (y : E)) := (y.isIntegral_coe).map (σ.toRingHom.toIntAlgHom)
    have hi' : IsIntegral O (σ (y : E)) := hi.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral hi')
  choose f hf using h1
  let Ψ : (E →ₐ[ℚ] C) → (𝓞 E →+* O) := fun σ =>
    { toFun := f σ
      map_one' := hinj (by simp [hf])
      map_mul' := fun a b => hinj (by simp [hf])
      map_zero' := hinj (by simp [hf])
      map_add' := fun a b => hinj (by simp [hf]) }
  have hΨ : ∀ σ (y : 𝓞 E), algebraMap O C (Ψ σ y) = σ (y : E) := hf
  refine ⟨Equiv.ofBijective Ψ ⟨?_, ?_⟩, hΨ⟩
  · intro σ σ' h
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext y
    have := hΨ σ y
    rw [h, hΨ] at this
    exact this.symm
  · intro τ
    have hu : ∀ y : Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ),
        IsUnit (((algebraMap O C).comp τ) y) := by
      rintro ⟨_, n, hn, rfl⟩
      have : (n : C) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hn
      simpa using this
    refine ⟨(IsLocalization.lift (S := E) hu).toRatAlgHom, ?_⟩
    ext y
    apply hinj
    rw [hΨ]
    exact IsLocalization.lift_eq hu y

theorem trace_eq_sum (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type)
    [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C]
    [Algebra ℤ_[p] O] (Φ : (E →ₐ[ℚ] C) ≃ (𝓞 E →+* O))
    (hΦ : ∀ σ (y : 𝓞 E), algebraMap O C (Φ σ y) = σ (y : E)) (x : ℤ_[p] ⊗[ℤ] 𝓞 E) :
    algebraMap O C (algebraMap ℤ_[p] O (LinearMap.trace ℤ_[p] _ (LinearMap.mulLeft ℤ_[p] x))) =
      ∑ σ : E →ₐ[ℚ] C, algebraMap O C (tauExt (Φ σ) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    have : LinearMap.mulLeft ℤ_[p] (x + y) =
        LinearMap.mulLeft ℤ_[p] x + LinearMap.mulLeft ℤ_[p] y := by
      apply LinearMap.ext; intro z; simp [add_mul]
    simp only [this, map_add, hx, hy, Finset.sum_add_distrib]
  | tmul a y =>
    have h1 : LinearMap.mulLeft ℤ_[p] (a ⊗ₜ[ℤ] y) =
        a • (LinearMap.mulLeft ℤ y).baseChange ℤ_[p] := by
      ext z
      simp [TensorProduct.smul_tmul']
    have h2 : ((Algebra.trace ℤ (𝓞 E) y : ℤ) : ℚ) = Algebra.trace ℚ E (y : E) :=
      Algebra.coe_trace_int y
    have h3 := trace_eq_sum_embeddings C (K := ℚ) (L := E) (x := (y : E))
    have h4 : LinearMap.trace ℤ _ (LinearMap.mulLeft ℤ y) = Algebra.trace ℤ (𝓞 E) y := rfl
    rw [h1, map_smul, LinearMap.trace_baseChange, h4]
    rw [← h2] at h3
    simp only [tauExt, Algebra.TensorProduct.lift_tmul, map_mul, smul_eq_mul, Algebra.ofId_apply]
    rw [← Finset.mul_sum]
    congr 1
    simp only [RingHom.toIntAlgHom_apply, hΦ]
    rw [← h3]
    simp

theorem card_emb : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Algebra ℤ_[p] O] (e : ℤ_[p] ⊗[ℤ] 𝓞 E), e * e = e → Nonempty (Fin (Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] e))) ≃ Emb (O := O) e) ∧ Nat.card (𝓞 E →+* O) = Module.finrank ℚ E := by
  intro E _ _ p _ C _ _ _ v O _ _ hv _ e he
  classical
  obtain ⟨Φ, hΦ⟩ := exists_equiv E C v O hv
  have hinj := hv.hom_inj
  refine ⟨?_, ?_⟩
  · have ht := trace_eq_sum E p C O Φ hΦ e
    have hproj : LinearMap.IsProj (LinearMap.range (LinearMap.mulLeft ℤ_[p] e))
        (LinearMap.mulLeft ℤ_[p] e) :=
      ⟨fun x => ⟨x, rfl⟩, by
        rintro _ ⟨x, rfl⟩
        simp [← mul_assoc, he]⟩
    haveI : Module.Free ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) := inferInstance
    haveI : Module.Finite ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) := inferInstance
    rw [hproj.trace] at ht
    have hterm : ∀ σ : E →ₐ[ℚ] C, algebraMap O C (tauExt (Φ σ) e) =
        if Φ σ ∈ Emb (O := O) e then 1 else 0 := by
      intro σ
      split_ifs with h
      · have h' : tauExt (Φ σ) e = 1 := h
        rw [h', map_one]
      · have hid : IsIdempotentElem (algebraMap O C (tauExt (Φ σ) e)) := by
          unfold IsIdempotentElem
          rw [← map_mul, ← map_mul, he]
        rcases IsIdempotentElem.iff_eq_zero_or_one.mp hid with h0 | h1
        · exact h0
        · exact absurd (hinj (h1.trans (map_one _).symm)) h
    simp only [hterm, map_natCast, Finset.sum_boole, Nat.cast_inj] at ht
    rw [ht]
    refine ⟨(Finset.equivFin _).symm.trans (Φ.subtypeEquiv ?_)⟩
    intro σ
    simp
  · rw [← Nat.card_congr Φ, Nat.card_eq_fintype_card, AlgHom.card]

end GlobalTheory.EmbCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IndexBoundAtLargerField
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem ringOfIntegersAlgebra_eq {F K : Type} [Field F] [Field K] [Algebra F K] (A : Algebra (𝓞 F) (𝓞 K))
    (h : ∀ x : 𝓞 F, ((@algebraMap (𝓞 F) (𝓞 K) _ _ A x : 𝓞 K) : K) = algebraMap F K (x : F)) :
    A = NumberField.inst_ringOfIntegersAlgebra F K := by
  refine Algebra.algebra_ext _ _ fun x => ?_
  apply NumberField.RingOfIntegers.ext
  rw [h x]
  rfl

noncomputable def coordMap {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] {C : Type} [AddCommGroup C]
    [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) : C →ₗ[F] (Fin n → K) :=
  ((z.symm : K ⊗[F] C →ₗ[K] (Fin n → K)).restrictScalars F).comp (TensorProduct.mk F K C 1)

theorem coordMap_linearIndependent {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] {C : Type} [AddCommGroup C]
    [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (m : ℕ) (b : Fin m → C) (hb : LinearIndependent F b) :
    LinearIndependent K fun a => coordMap z (b a) :=
  (Module.Flat.linearIndependent_one_tmul (S := K) hb).map' (z.symm : K ⊗[F] C →ₗ[K] (Fin n → K)) z.symm.ker

theorem coordMap_span {F : Type} [Field F] {K : Type} [Field K] [Algebra F K] {C : Type} [AddCommGroup C]
    [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) : Submodule.span K (Set.range (coordMap z)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := z.symm.surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    have e : a ⊗ₜ[F] f = a • ((1 : K) ⊗ₜ[F] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ (hx trivial) (hy trivial)

theorem index_bound_at_larger_field : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ), 0 < p → WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → Submodule.IsLattice B.KO (B.Mlat j ka) → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt X ka → WeightAlgebra.H2 X (scalOfP B hinj EX p ka wL wF T) ka wL wF → WeightAlgebra.Concl X (scalOfP B hinj EX p ka wL wF T) ka wL wF T nus β → ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] [Algebra (𝓞 B.KO) (𝓞 K)] [Algebra.IsIntegral (𝓞 B.KO) (𝓞 K)], (∀ x : 𝓞 B.KO, ((algebraMap (𝓞 B.KO) (𝓞 K) x : 𝓞 K) : K) = algebraMap B.KO K (x : B.KO)) → ∃ r : HeightOneSpectrum (𝓞 K) → ℝ, (∀ v, 0 ≤ r v) ∧ (∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ v ∈ S', Formalism.DivisionValues.lw v * r v ≤ β) ∧ ∀ (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J) (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka), FormTie X hinj EX p ka wL wF T O v i z act → ∀ e : ℕ, (T : ℝ) * nus (placeBelow (K := B.KO) v) ≤ e → ∀ W : Submodule K (Fin (O.nZ i) → K), (lix v (cut W (O.Ms i)) (cut W (O.Th v i)) : ℝ) ≤ ((ramOver (K := B.KO) v * e : ℕ) : ℝ) * (Module.finrank K W : ℝ) + r v := by
  intro D B P6 j X hinj EX p ka wL wF T nus β _ _ _ _ hM _ _ hC K _ _ _ _ A hint hA
  obtain rfl := ringOfIntegersAlgebra_eq A hA
  let Q : Formalism.MainNotions.Gaps.LocalGlobalPassage.Run D B P6 := ⟨j, X, scalOfP B hinj EX p ka wL wF T, ka, wL, wF, T, nus, β⟩
  obtain ⟨r, h0, h1, h2, h3⟩ := Formalism.MainNotions.Gaps.LocalGlobalPassage.l2 Q (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1 la)
    (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1b la) (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1c la) hM hC
  refine ⟨fun v => (v.asIdeal.ramificationIdx (𝓞 B.KO) : ℝ) * r (v.under (𝓞 B.KO)),
    fun v => mul_nonneg (Nat.cast_nonneg _) (h0 _), fun S' => (Formalism.MainNotions.Gaps.LocalGlobalPassage.l4 r h0 h1 S').trans h2, ?_⟩
  intro Bs Df S P _ _ oc O v i z act ht e he W
  have hpl : placeBelow (K := B.KO) v = v.under (𝓞 B.KO) := rfl
  have hram : ramOver (K := B.KO) v = v.asIdeal.ramificationIdx (𝓞 B.KO) := Formalism.MainNotions.Gaps.LocalGlobalPassage.ram_eq v
  obtain ⟨h4, h5⟩ := h3 (v.under (𝓞 B.KO))
  have hMs : O.Ms i = Formalism.MainNotions.Gaps.LocalGlobalPassage.up (coordMap z) Q.M0 := ht.Ms_eq
  have hTh : Formalism.MainNotions.Gaps.LocalGlobalPassage.up (coordMap z) (Q.M0 ⊓ Q.Th0) ≤ O.Th v i := by
    rw [ht.Th_eq]
    exact Submodule.span_mono (Set.image_mono fun f hf => hf.2)
  rw [hMs]
  exact Formalism.MainNotions.Gaps.LocalGlobalPassage.l5 (coordMap z) (coordMap_linearIndependent z) (coordMap_span z) Q.M0 (Q.M0 ⊓ Q.Th0) hM.fg
    hM.span_eq_top h4 inf_le_left v e (r (v.under (𝓞 B.KO))) (ramOver (K := B.KO) v * e)
    (by rw [hram]; push_cast; rfl) (h5 e (by rw [Int.cast_natCast, ← hpl]; exact he)) (O.Th v i) hTh W

end GlobalTheory.FormTies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegAtOfSabMap
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AlphaPair

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

def cobCube {A U : Type} [CommGroup A] [CommGroup U] (h : A → U) (x x' y : A) : U :=
  h (x * x' * y) * (h (x * x'))⁻¹ * (h (x * y))⁻¹ * (h (x' * y))⁻¹ * h x * h x' * h y * (h 1)⁻¹

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] in
omit [IsCommMonObj G] [IsCommMonObj G'] in

theorem _root_.GlobalTheory.AlphaPair.exists_ptEquiv {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (gp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f F) {Z : Scheme.{0}}
    (a : Z ⟶ S') (b : Z ⟶ S) (hb : b = a ≫ f) :
    ∃ ρ : (Over.mk a ⟶ G') ≃* (Over.mk b ⟶ G), ∀ x, (ρ x).left = x.left ≫ F := by
  subst hb
  have hpb : IsPullback F G'.hom G.hom f := gp.1
  let φ : (Over.mk a ⟶ G') → (Over.mk (a ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ F) (by
      rw [Category.assoc, hpb.w, ← Category.assoc, Over.w x]
      rfl)
  let ψ : (Over.mk (a ≫ f) ⟶ G) → (Over.mk a ⟶ G') := fun y =>
    Over.homMk (hpb.lift y.left a (by simpa using Over.w y)) (by simp)
  refine ⟨{ toFun := φ, invFun := ψ, left_inv := ?_, right_inv := ?_, map_mul' := ?_ },
    fun x => rfl⟩
  · intro x
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · simp [φ, ψ]
    · simp [φ, ψ]
  · intro y
    apply Over.OverMorphism.ext
    simp [φ, ψ]
  · intro x y
    apply Over.OverMorphism.ext
    exact (gp.2 (Over.mk a) x y (φ x) (φ y) rfl rfl).symm

end GlobalTheory.AlphaPair
end
end

