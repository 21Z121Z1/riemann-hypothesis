import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.MulVecEqOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0010
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2145
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsOfPrincipalLevelFieldOfDefinition
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix

namespace GlobalTheory.LevLaws

open GlobalTheory.PrincCore

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eq_one_of_norm_one {E : Type} [Field E] [NumberField E] [IsCMField E] {M : ℕ} (hM : 3 ≤ M) (u : E)
    (hint : IsIntegral ℤ ((u - 1) / M)) (hc : u * IsCMField.complexConj E u = 1) : u = 1 := by
  have hM0 : M ≠ 0 := by omega
  by_contra hne
  have hx : (⟨(u - 1) / M, hint⟩ : 𝓞 E) ≠ 0 := by
    intro h
    have : (u - 1) / (M : E) = 0 := congrArg Subtype.val h
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hM0 (Nat.cast_eq_zero.mp h)
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hx
  have hσ' : 1 ≤ ‖σ ((u - 1) / M)‖ := hσ
  have h1 : ‖σ u‖ = 1 := by
    have := congrArg (fun z => ‖σ z‖) hc
    simp only [map_mul, IsCMField.complexEmbedding_complexConj, norm_mul, map_one, norm_one,
      Complex.norm_conj] at this
    nlinarith [norm_nonneg (σ u)]
  rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast] at hσ'
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h2 : ‖σ u - 1‖ ≤ 2 := by
    have := norm_sub_le (σ u) 1
    rw [h1, norm_one] at this
    linarith
  rw [le_div_iff₀ (by linarith)] at hσ'
  linarith

set_option maxHeartbeats 800000 in

theorem det_eq_one {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (hr0 : 0 < r) {Comp : Type}
    (X : Comp → Data D.host.E r) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (Kf : Subgroup (GA D V)) (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictIsUnif V dict Kf th hr)
    (hmu : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    (M : ℕ) (hM : 3 ≤ M) (hK : IsLevelK V M Kf) (k : Comp) (γ' : GL (Fin r) D.host.E) (hγ' : γ' ∈ (X k).Γ) :
    (γ' : Matrix (Fin r) (Fin r) D.host.E).det = 1 := by
  classical
  subst hr
  obtain ⟨-, -, ⟨x0, hx0, heq⟩, -, -, hfib⟩ := hD
  obtain ⟨hdom, g, hg⟩ := hx0 k
  obtain ⟨-, hrat, -, hsur⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  have hact : ∀ h, ∀ τ, mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ = archM V (th k τ) h * mat (x0 k) τ := by
    intro h τ
    show mat (x0 k) τ * ((mat (x0 k) τ)⁻¹ * Matrix.reindex (finCongr rfl) (finCongr rfl) (archM V (th k τ) h) *
      mat (x0 k) τ) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdom τ).1),
      Matrix.one_mul]
    rfl
  have key : ∀ h ∈ GinfC V, ∃ γ'' ∈ (X k).Γ,
      dict (g * h) = ⟨k, lact γ'' (rmul (x0 k) (archMat V th rfl x0 h k))⟩ := by
    have := heq g
    rw [hg] at this
    exact this
  have hun : ∀ τ : (X k).Ψ, ((γ'.1.map τ.1).map (starRingEnd ℂ))ᵀ * V.gram.map τ.1 *
      γ'.1.map τ.1 = V.gram.map τ.1 := by
    intro τ
    refine unitary_of_first_minor hr0 τ.1 (X k).Gm (X k).Gm_herm _ (mat (x0 k) τ) ?_ ?_ ?_ _ ?_
    · ext a b
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply, HSpace.gram]
      rw [← V.herm.eq (V.frame b) (V.frame a)]
      exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero_iff _ τ.1.injective).2 (gram_det_ne V)
    · intro w hw
      obtain ⟨h, hh, hw'⟩ := hsur (Function.update (fun _ => 1) τ w) (by
        intro τ'
        by_cases e : τ' = τ
        · subst e
          simpa using hw
        · simp [Function.update_of_ne e])
      obtain ⟨γ'', h1, h2⟩ := key h hh
      have h3 := hmu (g * h)
      rw [h2] at h3
      have h4 := h3 τ ⟨1, by omega⟩
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.dmin_lact (X k) h1] at h4
      unfold dmin at h4
      rw [hact, hw', Function.update_self] at h4
      exact h4
    · have hcc : (γ'.1.map τ.1).map (starRingEnd ℂ) =
          (γ'.1.map cc).map τ.1 := by
        ext a b
        exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
      rw [hcc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
        ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.gramE (X k) hγ']
  obtain ⟨h, hh, hw⟩ := hsur _ hun
  obtain ⟨γ'', h1, h2⟩ := key h hh
  obtain ⟨γ₀, hγ₀, κ, hκ, hdc⟩ := hfib g (g * h) (by
    rw [hg]
    refine ⟨γ'' * γ', mul_mem h1 hγ', ?_⟩
    rw [h2]
    congr 1
    funext τ
    show γ''.1.map τ.1 * mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ =
      (γ'' * γ').1.map τ.1 * mat (x0 k) τ
    rw [hact, hw, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc])
  obtain ⟨δ, hδ1, hδ2⟩ := hrat γ₀ hγ₀
  obtain ⟨hκ1, hκ2⟩ := (hK κ⁻¹).1 (inv_mem hκ)
  have hfin : finHom V γ₀ * finHom V g = finHom V g * finHom V κ⁻¹ := by
    have h0 : finHom V h = 1 := hh
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  have hinf : infHom V γ₀ * infHom V g = infHom V g * infHom V h := by
    have h0 : infHom V κ⁻¹ = 1 := hκ1
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  let f : V.V →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := V.frame.equivFun.toLinearMap.restrictScalars _
  have hhat : latHat V = GlobalTheory.AdLat.hat D.host.F (V.L0.map f : Set (Fin V.rank → D.host.E)) := by
    unfold latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, f x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hspan : Submodule.span D.host.E (V.L0.map f : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have : (V.L0.map f : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, ← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  rw [hhat] at hκ2
  obtain ⟨Λ', g1, g2, g3⟩ := exists_lattice_congr D.host.F D.host.E V.rank M (by omega) (V.L0.map f)
    (V.standardTuple_isLattice.fg.map f) hspan (finHom V g) (finHom V κ⁻¹).1 δ.1 hκ2 (by
      rw [← hδ2, ← Units.val_mul, hfin, Units.val_mul])
  obtain ⟨τ⟩ : Nonempty (X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases e : τ ∈ (X k).Ψ
    · exact ⟨⟨τ, e⟩⟩
    · exact ⟨⟨_, not_not.1 (fun e' => e (((X k).cmType τ).2 e'))⟩⟩
  have hm : ∀ a b, archM V (th k τ) (a * b) = archM V (th k τ) a * archM V (th k τ) b := by
    intro a b
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  have h1' : archM V (th k τ) 1 = 1 := by
    unfold archM
    rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hg0 : (archM V (th k τ) g).det ≠ 0 := by
    have := congrArg Matrix.det (hm g⁻¹ g)
    rw [inv_mul_cancel, h1', Matrix.det_one, Matrix.det_mul] at this
    exact right_ne_zero_of_mul_eq_one this.symm
  have hconj : δ.1.map τ.1 * archM V (th k τ) g = archM V (th k τ) g * γ'.1.map τ.1 := by
    rw [← hw τ, ← hδ1 τ, ← hm, ← hm]
    unfold archM
    rw [map_mul, map_mul, hinf]
  have hdd : γ'.1.det = δ.1.det := by
    have := congrArg Matrix.det hconj
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, ← RingHom.map_det] at this
    exact τ.1.injective (mul_left_cancel₀ hg0 this).symm
  refine eq_one_of_norm_one hM _ ?_
    (GlobalTheory.CongruenceDet.det_mul_conj (X k).Gm _ (X k).Gm_det ((X k).Γ_stab γ' hγ').1)
  rw [hdd]
  refine isIntegral_trans (A := 𝓞 D.host.E) _
    (GlobalTheory.CongruenceDet.isIntegral_det_sub_one (by omega) Λ' _ g1 g2 fun v hv => ?_)
  obtain ⟨y, hy, e⟩ := g3 v hv
  exact ⟨y, hy, by rw [← Nat.cast_smul_eq_nsmul D.host.E, ← e, add_sub_cancel]⟩

open Module GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore in
set_option maxHeartbeats 1000000 in

theorem laws_of_level : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, Formalism.L2.Theta.GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → FnAlgClosed Xo c → (∀ p : ℕ, p.Prime → l.GoodAt p) → GlobalTheory.FlatCore.Laws U (xiR D) ∧ GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H := by
  intro D j H Dw l Xo c U dict h hF hg
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  refine ⟨⟨?_, h.levA, hg, h.unf, hF, h.xiAbs, h.chiTriv, fun σ hσ k γ hγ => ?_, fun σ hσ a n ha hp hn => ?_,
    GlobalTheory.RankOneDatum.exists_datum_of_rt D H h.host.2.1 h.host.2.2.1⟩, GlobalTheory.FlatRow.isHostField D H h.host.1⟩
  · have e : D.R.r = Dw.p + Dw.q := (h.unf c.F.val.toRingHom rfl).1
    omega
  · obtain ⟨Kf, th, hrk, hK, hth, hD, hu⟩ := h.dictU σ hσ
    exact det_eq_one _ hrk hr (U σ).X (dict σ) Kf th hth hD hu l.M l.three_le hK k γ hγ
  · obtain ⟨hrk, hM⟩ := h.modelW σ hσ
    obtain ⟨Kf, th, hrk', hK, hth, hD, hu⟩ := h.dictU σ hσ
    have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E H Dw l
      Xo c D.R.r (fun s => Formalism.L2.PjFree.Unf.ofPj (U s)) hr h.levA
      (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf s hs)) σ hσ
      (fun k k' => ⟨(hM k).1.trans (hM k').1.symm, (hM k).2.trans (hM k').2.symm⟩)
      (fun k γ hγ hc0 => by
        have hc : ∀ x ∈ ((U σ).X k).Λ, ∃ y ∈ ((U σ).X k).Λ,
            Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (l.M : D.host.E) • y := by
          intro x hx
          obtain ⟨y, hy, e⟩ := hc0 x hx
          exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
        obtain ⟨γ', hγ', u, m, hm, hum, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
          (Formalism.L2.PjFree.Unf.ofPj (U σ)) (h.unf σ hσ) h.levA hr k γ hγ hc
        have h1 := root_eq_one _ hrk' hr (U σ).X (dict σ) (fun _ => 1) Kf th hth hD
          ⟨fun _ _ => (one_mul _).symm, fun _ => norm_one, fun _ _ => rfl, hu⟩ _ l.three_le hK k γ γ' hγ' hc u m hm hum he
        rw [h1, one_smul] at he
        exact Units.ext he ▸ hγ')
      a n ha (fun τ _ h0 => hp τ _ (by omega)) hn (fun k => h.chiTriv σ hσ a n ha k)
    intro P hP
    exact key ⟨hP.1, hP.2⟩

end GlobalTheory.LevLaws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDefiniteRationalPointDataComponentStatement
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_definiteRationalPointData_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ Z : Comp Xo c, Nonempty (PtData Z) := by
  first | exact @GlobalTheory.DefPt.PtExist.main | exact GlobalTheory.DefPt.PtExist.main | (intros; apply GlobalTheory.DefPt.PtExist.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneIffIntegralAtPadicEmbeddingPlaceStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_one_iff_integral_at_padicEmbedding_place : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l), AtPlace w e0 → ∀ x : K, ‖e0 x‖ ≤ 1 ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ r : 𝓞 K, (s : K) * x = r := by
  first | exact @GlobalTheory.FrameRead.norm_le_one_iff_integral_at | exact GlobalTheory.FrameRead.norm_le_one_iff_integral_at | (intros; apply GlobalTheory.FrameRead.norm_le_one_iff_integral_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictLowerMemClosureTransvectionStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_add_strictLower_mem_closure_transvection' : ∀ (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R), (∀ a b, a ≤ b → c a b = 0) → 1 + c ∈ Submonoid.closure {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  first | exact @GlobalTheory.one_add_strictLower_mem_closure_transvection | exact GlobalTheory.one_add_strictLower_mem_closure_transvection | (intros; apply GlobalTheory.one_add_strictLower_mem_closure_transvection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictUpperMemClosureTransvectionStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_add_strictUpper_mem_closure_transvection : ∀ (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R), (∀ a b, b ≤ a → c a b = 0) → 1 + c ∈ Submonoid.closure {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  first | exact @GlobalTheory.UpperTransvection.upper_mem_closure | exact GlobalTheory.UpperTransvection.upper_mem_closure | (intros; apply GlobalTheory.UpperTransvection.upper_mem_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAtFittedPoints
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Cx
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem out_sum_tw {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) {n : ℕ}
    (f : E →ₗ[ℂ] ℂ) (φ : (Fin n → ℂ) →ₗ[ℂ] Tw s E) (z : Fin n → ℂ) :
    f (Tw.out (φ z)) = ∑ k, cj s (z k) * f (Tw.out (φ (Pi.single k 1))) := by
  let o : Tw s E →+ E := ⟨⟨Tw.out, rfl⟩, Tw.out_add⟩
  have e : z = ∑ k, z k • (Pi.single k 1 : Fin n → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext j; by_cases hj : j = k <;> simp [hj]
  conv_lhs => rw [e, map_sum]
  rw [show Tw.out (∑ k, φ (z k • Pi.single k 1)) = ∑ k, Tw.out (φ (z k • (Pi.single k 1 : Fin n → ℂ))) from
    map_sum o (fun k => φ (z k • (Pi.single k 1 : Fin n → ℂ))) Finset.univ, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Tw.out_smul, map_smul, smul_eq_mul]

theorem twist_conj_base_embedding_eq (p : PtAt ex Csz) (a : D.what₂.LL) :
    cj (twAt D.what₂.embLL p.P.A3.A.v0) (p.P.A3.fam3.base3.v0.embedding a) = D.what₂.embLL a := by
  rw [show p.P.A3.fam3.base3.v0 = p.P.A3.A.v0 from rfl, emb_eq D.what₂.embLL p.P.A3.A.v0 a, cj_cj, sgAt_mk _ p.R.hv0]

theorem mul_eq_one_of_covolume_identity (κ zt z0 ct c0 v : ℂ) (hκ : κ ≠ 0) (hzt : zt ≠ 0) (hz0 : z0 ≠ 0) (hct : ct ≠ 0) (hc0 : c0 ≠ 0) :
    κ⁻¹ * z0 * c0 * (κ * v / (zt * ct)) = (zt / z0 * (ct / c0))⁻¹ * v := by
  field_simp

set_option maxHeartbeats 1600000 in

theorem oneMap_at (p : PtAt ex Csz) (hp : p.Rows) {CF : ℝ} (d : FunIn p CF) (a : SlopeTestRemainingChoices p d.G d.W d.n) (ht : TieAt d a)
    (hwf : (Df p).WF) (hR : ∃ R0 : IndefRows (Df p), R0.toIndefData = p.S false)
    (hQ : (∀ b u, ConvK a.ch b u) ∧ (∀ u, (∀ b, psiK a.ch b u = 0) → u = 0) ∧
      (∀ i j t, SquareNonzero a.ch.W a.ch.S.B a.ch.rm t i j ∧ a.ch.c i j t ≠ 0) ∧
      (a.ch.FieldOK → ∃ κ ze, FormulaAt a.ch κ ze)) :
    ∃ ze : Tup p → D.what₂.LL, ze p.P.A3.fam3.base3.μ0 = 1 ∧ (∀ t, ∃ n : ℕ, 0 < n ∧ ze t ^ n = 1) ∧
      LeafC (p.S false) (d.data ze ∅ fun _ => 0) := by
  classical
  obtain ⟨hL, hI, hC, hF⟩ := hQ
  obtain ⟨κ, ze, hz, hform⟩ := hF ht.ok.field
  obtain ⟨R0, hR0⟩ := hR
  obtain ⟨hinj, hrow⟩ := GlobalTheory.T.injective_iC_rows p hp
  have hzK : ∀ t, ze t ≠ 0 := fun t h => by
    obtain ⟨n, hn, e⟩ := hz t
    rw [h, zero_pow hn.ne'] at e
    exact zero_ne_one e
  have hze : ∀ t, D.what₂.embLL (ze t) ≠ 0 := fun t => (map_ne_zero _).2 (hzK t)
  have hc0 : ∀ t, cTot a.ch t ≠ 0 := fun t => (cTot_ne_zero_iff _ _).2 fun i j => (hC i j t).2

  have key : ∀ t (y : Fin ((Df p).nV t) → D.what₂.LL) (b : Fin d.n),
      D.what₂.embLL (ze t) * cTot a.ch t * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
        (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) =
        κ * D.what₂.embLL ((d.V t).mulVec y b) := by
    intro t y b
    rw [← GlobalTheory.T.theta_eV0_eq_iC_Pq_rows p hp t y, ht.sums t (TieModel.inUse p t) y b]
    exact hform t _ (GlobalTheory.T.eV0_mem_goodF_rows p hp t y) b

  have lin : ∀ (b : Fin d.n) (z : Fin (p.S false).D → D.what₂.LL),
      psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (cpt p.P.A3.fam3.base3.v0.embedding z)) =
        ∑ k, D.what₂.embLL (z k) *
          psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (Pi.single k 1)) := by
    intro b z
    have := out_sum_tw (twAt D.what₂.embLL p.P.A3.A.v0) (psiL a.ch b (hL b))
      ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0) (cpt p.P.A3.fam3.base3.v0.embedding z)
    refine this.trans (Finset.sum_congr rfl fun k _ => ?_)
    exact congrArg (· * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (Pi.single k 1))) (twist_conj_base_embedding_eq p (z k))

  have hκ : κ ≠ 0 := by
    intro hκ0
    have h0 : ∀ y, (p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0
        (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq p.P.A3.fam3.base3.μ0).mulVec y)) = 0 := by
      intro y
      apply hI
      intro b
      have := key p.P.A3.fam3.base3.μ0 y b
      rw [hκ0, zero_mul] at this
      exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero (hze _) (hc0 _))
    have i0 : Fin ((Df p).dQ p.P.A3.fam3.base3.μ0) := ⟨0, R0.pos⟩
    obtain ⟨y, hy⟩ := hwf.Pq_surj p.P.A3.fam3.base3.μ0 (Pi.single i0 1)
    have h1 := h0 y
    rw [hy] at h1
    have h2 := congrFun (hinj (h1.trans (map_zero _).symm)) i0
    simp [cpt] at h2

  let c0 : ℂ := κ⁻¹ * D.what₂.embLL (ze p.P.A3.fam3.base3.μ0) * cTot a.ch p.P.A3.fam3.base3.μ0
  let Ψc : Matrix (Fin d.n) (Fin (p.S false).D) ℂ := Matrix.of fun b k =>
    c0 * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (Pi.single k 1))
  let ze' : Tup p → D.what₂.LL := fun t => ze t / ze p.P.A3.fam3.base3.μ0
  let r : Tup p → D.what₂.LL := fun t => ze' t * ∏ ij, d.rq t ij
  have hmain : ∀ t ∈ (Set.univ : Set (Tup p)),
      Ψc * ((p.S false).ι t * (Df p).Pq t).map D.what₂.embLL = ((r t)⁻¹ • d.V t).map D.what₂.embLL := by
    intro t _
    have H : ∀ y : Fin ((Df p).nV t) → D.what₂.LL, ∀ b,
        (Ψc * ((p.S false).ι t * (Df p).Pq t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b =
          (((r t)⁻¹ • d.V t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b := by
      intro y b
      have e1 : Ψc.mulVec (cpt D.what₂.embLL (((p.S false).ι t).mulVec (((Df p).Pq t).mulVec y))) b =
          c0 * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
            (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) := by
        rw [← hrow, lin, Finset.mul_sum]
        simp only [Matrix.mulVec, dotProduct, Ψc, Matrix.of_apply, cpt]
        exact Finset.sum_congr rfl fun k _ => by ring
      have e3 := (TieModel.ratio_eq ht t).2
      have eL : (Ψc * ((p.S false).ι t * (Df p).Pq t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b =
          c0 * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
            (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) := by
        rw [← Matrix.mulVec_mulVec, ← cpt_mulVec, ← Matrix.mulVec_mulVec]
        exact e1
      have eR : (((r t)⁻¹ • d.V t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b =
          (D.what₂.embLL (ze t) / D.what₂.embLL (ze p.P.A3.fam3.base3.μ0) *
            (cTot a.ch t / cTot a.ch p.P.A3.fam3.base3.μ0))⁻¹ * D.what₂.embLL ((d.V t).mulVec y b) := by
        rw [← cpt_mulVec]
        show D.what₂.embLL ((((r t)⁻¹ • d.V t).mulVec y) b) = _
        rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
        rw [show r t = ze t / ze p.P.A3.fam3.base3.μ0 * ∏ ij, d.rq t ij from rfl, map_mul, map_div₀, e3]
        rfl
      have hP : psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
            (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) =
          κ * D.what₂.embLL ((d.V t).mulVec y b) / (D.what₂.embLL (ze t) * cTot a.ch t) :=
        eq_div_of_mul_eq (mul_ne_zero (hze t) (hc0 t)) (by rw [mul_comm]; exact key t y b)
      rw [eL, eR, hP]
      exact mul_eq_one_of_covolume_identity _ _ _ _ _ _ hκ (hze t) (hze _) (hc0 t) (hc0 _)
    ext b col
    have := H (Pi.single col 1) b
    have hs : cpt D.what₂.embLL (Pi.single col (1 : D.what₂.LL)) = Pi.single col 1 := by
      funext i; by_cases hi : i = col <;> simp [cpt, hi]
    rw [hs, Matrix.mulVec_single, Matrix.mulVec_single] at this
    simpa using this
  have hbij : Function.Bijective ((p.S false).ι p.P.A3.fam3.base3.μ0).mulVec := (hR0 ▸ R0.l1c).1 _
  obtain ⟨⟨Ψ, -, hΨ⟩, -⟩ := GlobalTheory.complex_matrix_descends_of_rational_on_tuple D.what₂.embLL d.n (p.S false).D (Df p).dQ
    (Df p).nV (p.S false).ι (Df p).Pq d.V r Set.univ p.P.A3.fam3.base3.μ0 Ψc trivial hbij
    (hwf.Pq_surj _) hmain
  refine ⟨ze', by simp only [ze']; exact div_self (hzK _), fun t => ?_, Ψ, fun t _ => ?_⟩
  · obtain ⟨n, hn, e⟩ := hz t
    obtain ⟨m, hm, e'⟩ := hz p.P.A3.fam3.base3.μ0
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    show (ze t / ze p.P.A3.fam3.base3.μ0) ^ (n * m) = 1
    rw [div_pow, pow_mul (ze t), e, one_pow, pow_mul' (ze _), e', one_pow, div_one]
  · refine (hΨ t trivial).trans ?_
    show _ = (∏ ij, d.rq t ij)⁻¹ • ((ze' t)⁻¹ • d.V t)
    rw [smul_smul, mul_inv, mul_comm]

theorem oneMap_of_rows (hB : Bundle) (hS : SetAt) (h1 : LinK) (h2 : InjK) (h3 : ConstK) (h4 : Formula2K) : OneMap @Comparison₂ := by
  obtain ⟨CF0, hQ⟩ := hS.atPt (h1.and (h2.and (h3.and h4)))
  refine ⟨CF0, fun CF hCF => (hQ CF hCF).imp fun Fm CH _ e _ => ⟨0, fun C _ => evPt_imp e fun x hx i p hp q d hd => ?_⟩⟩
  obtain ⟨-, a, ht⟩ := hd
  obtain ⟨wf, R0, hR⟩ := hB p hp
  exact oneMap_at p hp d a ht wf ⟨R0, hR⟩ (q d.G d.W d.n a ht.ok)

end GlobalTheory.BigTop.Fun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSquareFittedIdentityStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_square_fitted_identity : SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → (Lf (Fitted @Comparison₂) fun p _ d _ _ => ThA d.G p.P.A3.A.μ0 p.R.mu) → OneSqSt → OneSq @Comparison₂ := by
  first | exact @GlobalTheory.BigTop.Fun.oneSq_tie | exact GlobalTheory.BigTop.Fun.oneSq_tie | (intros; apply GlobalTheory.BigTop.Fun.oneSq_tie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionThirdStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oscillator_model_extension_third : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ O.EquivAt (κ i) (u • cc) ∧ SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1 ∧ OneMapRow (T.Q.Xo ((i : ℕ) + 1)) O.c' (Wc D i) (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (xiR D) (wtA (κ i)) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc D.what₂.embLL.toRatAlgHom.fieldRange (cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank) (u • cc) 1 := by
  first | exact @GlobalTheory.AdTh.exists_ccIs_equivAt_serOf_oneMapRow | exact GlobalTheory.AdTh.exists_ccIs_equivAt_serOf_oneMapRow | (intros; apply GlobalTheory.AdTh.exists_ccIs_equivAt_serOf_oneMapRow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterLargeAllPointsBoundStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_large_all_points_bound : GlobalTheory.BigOn.AtPts fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).Large := by
  first | exact @GlobalTheory.ExpTie.parOf_large | exact GlobalTheory.ExpTie.parOf_large | (intros; apply GlobalTheory.ExpTie.parOf_large <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDepthSumRoundingOscillationStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productDepth_sum_rounding_oscillation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (cx : Lt1 Dw → ℕ), (∀ A B : Lt1 Dw → ℝ, (∀ f, FacBetween Xo la f (cx f) (A f) (B f)) → NuBetween Xo la cx (∑ f, A f) (∑ f, B f) ∧ ∃ n : ℕ, NuBetween Xo la cx n (n + (∑ f, (B f - A f) + 1))) ∧ ∀ b : ℝ, OscLe Xo c p cx b → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Comp Xo c), (letI := H.starRing; eLoc Y Z la cx ≤ (b : EReal)) := by
  first | exact @GlobalTheory.RefSum.nuBetween_sum_and_eLoc_le | exact GlobalTheory.RefSum.nuBetween_sum_and_eLoc_le | (intros; apply GlobalTheory.RefSum.nuBetween_sum_and_eLoc_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingScalarsIntegralStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_ring_embedding_rows : AtFit fun Fm x hx i p w j ρ hρ ν _ => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ (z : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ⊗[(Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)] (Fm.D x i).nexp.Fm ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w)) (n : ℕ) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL) (κ : ℂ) (N : ℕ),
    (∀ k, y k ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _))) → IsUnit ((N : ℕ) : (Fm.ex x hx i).nch.Oe w) → (∃ m : ℕ, IsIntegral ℤ ((N : ℂ) ^ m * κ)) →
    rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = κ • ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) →
    ∃ b : (Fm.ex x hx i).nch.Oe w, rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (b * a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := by
  first | exact @GlobalTheory.BigOn.Exp.scalar_of_reading | exact GlobalTheory.BigOn.Exp.scalar_of_reading | (intros; apply GlobalTheory.BigOn.Exp.scalar_of_reading <;> assumption)
end

