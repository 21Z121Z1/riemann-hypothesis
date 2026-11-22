import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegTestFunctionNearOne
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def hsq (x : Lie E a) : ℝ :=
  ∑ i, ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2

theorem hsq_nonneg (x : Lie E a) : 0 ≤ hsq x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem sq_le_hsq (x : Lie E a) (i j : Fin a) (w : InfinitePlace E) :
    ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤ hsq x := by
  have h1 : ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤
      ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 :=
    Finset.single_le_sum (f := fun w => ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ w)
  have h2 : ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤
      ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)
  have h3 : ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤ hsq x :=
    Finset.single_le_sum (f := fun i => ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
  exact h1.trans (h2.trans h3)

theorem hsq_oneL : hsq (oneL E a) = 0 := by
  simp [hsq, oneL, toL]

theorem dist_oneL_lt {x : Lie E a} {δ : ℝ} (hδ : 0 < δ) (h : hsq x < δ ^ 2) : dist x (oneL E a) < δ := by
  refine (dist_pi_lt_iff hδ).2 fun i => (dist_pi_lt_iff hδ).2 fun j => (dist_pi_lt_iff hδ).2 fun w => ?_
  have h1 := (sq_le_hsq x i j w).trans_lt h
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hδ.le h1

theorem contDiff_hsq : ContDiff ℝ ∞ (hsq : Lie E a → ℝ) := by
  unfold hsq
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ContDiff.sum fun w _ => ContDiff.norm_sq ℝ ?_
  change ContDiff ℝ ∞ fun x : Lie E a => x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w
  fun_prop

theorem ofReal_hsq (x : Lie E a) :
    (hsq x : ℂ) = ∑ w, Matrix.trace ((Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) *
      star (Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E))) w := by
  simp only [hsq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Finset.sum_apply, Pi.mul_apply,
    Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow, Complex.star_def, Complex.mul_conj']
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans ?_ Finset.sum_comm
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => rfl

theorem hsq_conj (k : Kinf E a) (x : Lie E a) : hsq (toL (k.1 * Matrix.of x * star k.1)) = hsq x := by
  apply Complex.ofReal_injective
  rw [ofReal_hsq, ofReal_hsq]
  have hk : k.1 * star k.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k.2
  have hk' : star k.1 * k.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
  set Y : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of x - 1 with hY
  have e1 : (Matrix.of (toL (k.1 * Matrix.of x * star k.1)) - 1 : Matrix (Fin a) (Fin a) (Cinf E)) = k.1 * Y * star k.1 := by
    rw [hY, mul_sub, sub_mul, mul_one, hk]
    rfl
  have e2 : Matrix.trace ((k.1 * Y * star k.1) * star (k.1 * Y * star k.1)) = Matrix.trace (Y * star Y) := by
    have : (k.1 * Y * star k.1) * star (k.1 * Y * star k.1) = k.1 * ((Y * star Y) * star k.1) := by
      simp only [star_mul, star_star]
      calc k.1 * Y * star k.1 * (k.1 * (star Y * star k.1))
          = k.1 * Y * (star k.1 * k.1) * (star Y * star k.1) := by simp only [mul_assoc]
        _ = k.1 * ((Y * star Y) * star k.1) := by rw [hk']; simp only [mul_one, mul_assoc]
    rw [this, Matrix.trace_mul_comm, mul_assoc, hk', mul_one]
  rw [e1, e2]

end GlobalTheory.CompanionTheory.SmoothRep

namespace GlobalTheory.CompanionTheory.SmoothRep

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem val_image_mem_nhds_one {E : Type} [Field E] [NumberField E] {a : ℕ} {N : Set (GL (Fin a) (Cinf E))} (hN : N ∈ 𝓝 1) :
    (Units.val '' N) ∈ 𝓝 (1 : Matrix (Fin a) (Fin a) (Cinf E)) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  exact (Units.isOpenEmbedding_val (R := Matrix (Fin a) (Fin a) (Cinf E))).isOpenMap.image_mem_nhds hN

theorem exists_bump_conjInv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (N : Set (GL (Fin a) (Cinf E))), N ∈ 𝓝 1 → ∃ β₀ : Lie E a → ℝ, 0 ≤ β₀ ∧ 0 < β₀ (oneL E a) ∧
      IsTest (fun x => (β₀ x : ℂ)) ∧ ConjInv (fun x => (β₀ x : ℂ)) ∧ ∀ x, β₀ x ≠ 0 → ∃ y ∈ N, toL y.val = x := by
  intro E _ _ _ a N hN
  have h := val_image_mem_nhds_one hN
  have e : (toL '' (Units.val '' N) : Set (Lie E a)) = Units.val '' N := Set.image_id _
  have hV : (toL '' (Units.val '' N) : Set (Lie E a)) ∈ 𝓝 (oneL E a) := by
    rw [e]; exact h
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.1 hV
  have hδ2 : 0 < δ ^ 2 := by positivity
  let f : ContDiffBump (0 : ℝ) := ⟨δ ^ 2 / 4, δ ^ 2 / 2, by positivity, by linarith⟩
  have hsupp : ∀ x : Lie E a, f (hsq x) ≠ 0 → hsq x < δ ^ 2 / 2 := fun x hx => by
    have : hsq x ∈ Function.support f := hx
    rw [f.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (hsq_nonneg x)] at this
    exact this
  have hmem : ∀ x : Lie E a, hsq x ≤ δ ^ 2 / 2 → ∃ y ∈ N, toL y.val = x := fun x hx => by
    have : x ∈ Metric.ball (oneL E a) δ := dist_oneL_lt hδ (by linarith)
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hb this
    exact ⟨y, hy, rfl⟩
  have hKc : IsClosed {x : Lie E a | hsq x ≤ δ ^ 2 / 2} :=
    isClosed_le contDiff_hsq.continuous continuous_const
  have hts : tsupport (fun x => (f (hsq x) : ℂ)) ⊆ {x : Lie E a | hsq x ≤ δ ^ 2 / 2} :=
    closure_minimal (fun x hx => (hsupp x (fun h0 => hx (by simp [h0]))).le) hKc
  have hKb : {x : Lie E a | hsq x ≤ δ ^ 2 / 2} ⊆ Metric.closedBall (oneL E a) δ := fun x hx =>
    (dist_oneL_lt hδ (by simp only [Set.mem_setOf_eq] at hx; linarith)).le
  refine ⟨fun x => f (hsq x), fun x => f.nonneg, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · show 0 < f (hsq (oneL E a))
    rw [hsq_oneL]
    exact f.pos_of_mem_ball (Metric.mem_ball_self f.rOut_pos)
  · exact Complex.ofRealCLM.contDiff.comp (f.contDiff.comp contDiff_hsq)
  · exact (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hts.trans hKb)
  · intro x hx
    obtain ⟨y, _, rfl⟩ := hmem x (hts hx)
    exact y.isUnit
  · intro k x
    show (f (hsq (toL (k.1 * Matrix.of x * star k.1))) : ℂ) = f (hsq x)
    rw [hsq_conj]
  · exact fun x hx => hmem x (hsupp x hx).le

end GlobalTheory.CompanionTheory.SmoothRep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueComplexPointUnder
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Under

open GlobalTheory.TuplePoint GlobalTheory.Points

theorem spZ_ext (f g : Sp ℂ ⟶ Sp ℤ) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  ext1
  exact Subsingleton.elim _ _

theorem top_ext {s s' : Γ(Sp ℂ, ⊤)} (h : valR (𝟙 (Sp ℂ)) ⊤ s = valR (𝟙 (Sp ℂ)) ⊤ s') : s = s' :=
  ext_of_dense (𝟙 (Sp ℂ)) fun _ => h

theorem hom_eq_of_val {N : ℕ} {φ ψ : Sp ℂ ⟶ PSpace ℤ N} (i : Fin (N + 1))
    (h₁ : ⊤ ≤ φ ⁻¹ᵁ chart ℤ N i) (h₂ : ⊤ ≤ ψ ⁻¹ᵁ chart ℤ N i)
    (h : ∀ j, valR φ (chart ℤ N i) (ratio ℤ N i j) = valR ψ (chart ℤ N i) (ratio ℤ N i j)) : φ = ψ := by
  refine GlobalTheory.ProjSpace.hom_ext (spZ_ext _ _) fun y => ⟨⊤, trivial, i, h₁, h₂, fun j => top_ext ?_⟩
  have e₁ := valR_appLE (𝟙 (Sp ℂ)) φ h₁ le_rfl (ratio ℤ N i j)
  have e₂ := valR_appLE (𝟙 (Sp ℂ)) ψ h₂ le_rfl (ratio ℤ N i j)
  rw [Category.id_comp] at e₁ e₂
  exact e₁.trans ((h j).trans e₂.symm)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev blockVec (z : (Σ k, Bk n k) → ℂ) (k : Fin (m + 1)) : Fin (n k + 1) → ℂ := fun i => z ⟨k, i⟩

theorem blockVec_ne_zero {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : Fin (m + 1)) :
    blockVec z k ≠ 0 := fun h => by
  obtain ⟨i, hi⟩ := hz k
  exact hi (congrFun h i)

theorem isUnder_of_comp {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, blockVec z k ≠ 0) (y : CxPts (mpStr ℤ m n) σ₀)
    (h : ∀ k, y.1 ≫ prB n k = point ℤ (blockVec z k) (hz k)) : IsUnder y z := fun k i => by
  refine ⟨⟨fun hy => ne_zero_of_le (h k) hy le_rfl, fun hi => le_preimage_chart (h k) hi⟩, fun j hy => ?_⟩
  exact valR_pullRatio (h k) hy le_rfl j

theorem comp_of_isUnder {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, blockVec z k ≠ 0) (hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    {y : CxPts (mpStr ℤ m n) σ₀} (H : IsUnder y z) (k : Fin (m + 1)) :
    y.1 ≫ prB n k = point ℤ (blockVec z k) (hz k) := by
  obtain ⟨i, hi⟩ := hz' k
  have hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ((H k i).1).2 hi
  refine hom_eq_of_val i (le_preimage_comp y.1 _ le_rfl hy)
    ((le_point_preimage_iff (o := ℤ) (ht := hz k) i).2 hi) fun j => ?_
  refine (valR_appLE y.1 (prB n k) le_rfl hy (ratio ℤ (n k) i j)).symm.trans ?_
  exact ((H k i).2 j hy).trans (valR_point_ratio (t := blockVec z k) (ht := hz k) hi j).symm

theorem existsUnique_isUnder (m : ℕ) (n : Fin (m + 1) → ℕ) (z : (Σ k, Bk n k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ∃! y : CxPts (mpStr ℤ m n) σ₀, IsUnder y z := by
  have ht := blockVec_ne_zero hz
  let a : ∀ k, Sp ℂ ⟶ PSpace ℤ (n k) := fun k => point ℤ (blockVec z k) (ht k)
  have ha : ∀ k, a k ≫ toSpecBase ℤ (n k) = spMap σ₀ := fun _ => spZ_ext _ _
  let y : CxPts (mpStr ℤ m n) σ₀ := ⟨lift m n (spMap σ₀) a ha, lift_mpStr m n _ a ha⟩
  have hy : ∀ k, y.1 ≫ prB n k = a k := lift_pr m n _ a ha
  refine ⟨y, isUnder_of_comp ht y hy, fun y' H => Subtype.ext ?_⟩
  exact GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k =>
    (comp_of_isUnder ht hz H k).trans (hy k).symm

end GlobalTheory.CompanionTheory.MPDict.Under
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLatticePointsInSiegelSetBound
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt

noncomputable section
namespace GlobalTheory.CompanionTheory.TorusCount

theorem exists_cone_lower (r : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ l : ℝ, 0 < l ∧ ∀ t ∈ cone r c, ∀ i, l ≤ t i := by
  set c' : ℝ := min c 1 with hc'
  have h0 : 0 < c' := lt_min hc one_pos
  have h1 : c' ≤ 1 := min_le_right _ _
  have h2 : c' ≤ c := min_le_left _ _
  have key : ∀ t ∈ cone r c, ∀ (m : ℕ) (i : Fin r), i.val + m + 1 = r → c' ^ (m + 1) ≤ t i := by
    intro t ht m
    induction m with
    | zero =>
      intro i hi
      simpa using h2.trans (ht.2.2 i (by omega))
    | succ m ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have a1 := ih ⟨i.val + 1, hj⟩ (by simp only; omega)
      have a2 := ht.2.1 i ⟨i.val + 1, hj⟩ rfl
      have a3 : 0 < t ⟨i.val + 1, hj⟩ := ht.1 _
      calc c' ^ (m + 1 + 1) = c' * c' ^ (m + 1) := by ring
        _ ≤ c' * t ⟨i.val + 1, hj⟩ := by gcongr
        _ ≤ c * t ⟨i.val + 1, hj⟩ := by gcongr
        _ ≤ t i := a2
  refine ⟨c' ^ r, by positivity, fun t ht i => ?_⟩
  have hi := i.2
  obtain ⟨m, hm⟩ : ∃ m, i.val + m + 1 = r := ⟨r - i.val - 1, by omega⟩
  exact (pow_le_pow_of_le_one h0.le h1 (by omega)).trans (key t ht m i hm)

theorem le_prod_max {r : ℕ} (t : Fin r → ℝ) (i : Fin r) : max (t i) 1 ≤ ∏ k, max (t k) 1 := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact le_mul_of_one_le_right (by positivity) (Finset.one_le_prod fun v _ => le_max_right _ _)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem eq_of_act (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (τ : E →+* ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (u v : Fin r → ℂ)
    (hX : M * X.map τ = X.map τ * diagonal u) (hY : M * Y.map τ = Y.map τ * diagonal v)
    (hZ : ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      M *ᵥ (fun i => τ (z i)) = fun i => τ (z i)) :
    M = X.map τ * diagonal u * (Formalism.UG.cT (σ : E →+* E) Y * J).map τ +
      Y.map τ * diagonal v * (Formalism.UG.cT (σ : E →+* E) X * J).map τ +
      (1 - X * (Formalism.UG.cT (σ : E →+* E) Y * J) - Y * (Formalism.UG.cT (σ : E →+* E) X * J)).map τ := by
  set Ax := Formalism.UG.cT (σ : E →+* E) X * J with hAx
  set Ay := Formalism.UG.cT (σ : E →+* E) Y * J with hAy
  have xx : Ax * X = 0 := hW.xx
  have xy : Ax * Y = 1 := hW.xy
  have yy : Ay * Y = 0 := hW.yy
  have yx : Ay * X = 1 := by
    have e := congrArg (Formalism.UG.cT (σ : E →+* E)) hW.xy
    have cc : ∀ Z : Matrix (Fin n) (Fin r) E, Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) Z) = Z :=
      fun Z => Matrix.ext fun i j => sigma_sigma h _
    have hJ' : Formalism.UG.cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, hJ', Formalism.UG.cT_one, ← Matrix.mul_assoc] at e
  set P := 1 - X * Ay - Y * Ax with hP
  have hxP : Ax * P = 0 := by
    simp only [hP, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, xx, xy, Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hyP : Ay * P = 0 := by
    simp only [hP, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, yx, yy, Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hMP : M * P.map τ = P.map τ := by
    ext i j
    have e := hZ (fun a => P a j) (funext fun k => congrFun (congrFun hxP k) j) (funext fun k => congrFun (congrFun hyP k) j)
    exact congrFun e i
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = X.map τ * Ay.map τ + Y.map τ * Ax.map τ + P.map τ := by
    have : (1 : Matrix (Fin n) (Fin n) E) = X * Ay + Y * Ax + P := by simp [hP]
    have e := congrArg (fun A : Matrix (Fin n) (Fin n) E => A.map τ) this
    simpa [Matrix.map_add, Matrix.map_mul, Matrix.map_one] using e
  calc M = M * 1 := (Matrix.mul_one _).symm
    _ = _ := by
      rw [h1, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX, hY, hMP]

theorem exists_entry_bound (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (τ : E →+* ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (M : Matrix (Fin n) (Fin n) ℂ) (u v : Fin r → ℂ) (S : ℝ), 1 ≤ S → (∀ k, ‖u k‖ ≤ S) →
      (∀ k, ‖v k‖ ≤ S) → M * X.map τ = X.map τ * diagonal u → M * Y.map τ = Y.map τ * diagonal v →
      (∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
        M *ᵥ (fun i => τ (z i)) = fun i => τ (z i)) → ∀ i j, ‖M i j‖ ≤ c * S := by
  set A := X.map τ
  set A' := Y.map τ
  set B := (Formalism.UG.cT (σ : E →+* E) Y * J).map τ
  set B' := (Formalism.UG.cT (σ : E →+* E) X * J).map τ
  set Q := (1 - X * (Formalism.UG.cT (σ : E →+* E) Y * J) - Y * (Formalism.UG.cT (σ : E →+* E) X * J)).map τ
  let f : Fin n → Fin n → ℝ := fun i j => ∑ k, ‖A i k‖ * ‖B k j‖ + ∑ k, ‖A' i k‖ * ‖B' k j‖ + ‖Q i j‖
  have hf : ∀ i j, 0 ≤ f i j := fun i j => by positivity
  refine ⟨∑ i, ∑ j, f i j, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hf i j,
    fun M u v S hS hu hv hX hY hZ i j => ?_⟩
  have hd : ∀ (P : Matrix (Fin n) (Fin r) ℂ) (R : Matrix (Fin r) (Fin n) ℂ) (d : Fin r → ℂ), (∀ k, ‖d k‖ ≤ S) →
      ‖(P * diagonal d * R) i j‖ ≤ (∑ k, ‖P i k‖ * ‖R k j‖) * S := fun P R d hd => by
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [Matrix.mul_diagonal, norm_mul, norm_mul]
    have := hd k
    calc ‖P i k‖ * ‖d k‖ * ‖R k j‖ ≤ ‖P i k‖ * S * ‖R k j‖ := by gcongr
      _ = _ := by ring
  have e := eq_of_act h hJ hW τ M u v hX hY hZ
  have h1 : ‖M i j‖ ≤ f i j * S := by
    rw [e, Matrix.add_apply, Matrix.add_apply]
    refine (norm_add₃_le).trans ?_
    have := hd A B u hu
    have := hd A' B' v hv
    have hq : ‖Q i j‖ ≤ ‖Q i j‖ * S := le_mul_of_one_le_right (norm_nonneg _) hS
    simp only [f, add_mul]
    linarith
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hf i j) (Finset.mem_univ i))
  exact Finset.single_le_sum (fun j _ => hf i j) (Finset.mem_univ j)

theorem exists_torus_bound (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) {w : InfinitePlace F} (τ : EmbOver E w) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (t : Fin r → ℝ) (a : GAd σ J) (S : ℝ), (∀ k, 0 < t k) → 1 ≤ S → (∀ k, t k ≤ S) →
      (∀ k, (t k)⁻¹ ≤ S) → IsTorusElt σ J X Y t a → ∀ i j,
        ‖archMat σ J τ (projArch σ J w a) i j‖ ≤ c * S ∧ ‖archMat σ J τ (projArch σ J w a⁻¹) i j‖ ≤ c * S := by
  obtain ⟨c, hc, hb⟩ := exists_entry_bound h hJ hW τ.1
  refine ⟨c, hc, fun t a S ht hS h1 h2 ha i j => ?_⟩
  obtain ⟨hX, hY, hZ⟩ := ha.2 w τ
  set M := archMat σ J τ (projArch σ J w a) with hM
  set M' := archMat σ J τ (projArch σ J w a⁻¹) with hM'
  have hMM : M' * M = 1 := by
    rw [hM, hM', ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  have hn : ∀ k, ‖(t k : ℂ)‖ ≤ S := fun k => by
    rw [Complex.norm_real, Real.norm_of_nonneg (ht k).le]; exact h1 k
  have hn' : ∀ k, ‖(t k : ℂ)⁻¹‖ ≤ S := fun k => by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (ht k).le]; exact h2 k
  have hD : diagonal (fun i => (t i : ℂ)) * diagonal (fun i => (t i : ℂ)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg _ (funext fun k => mul_inv_cancel₀ (by exact_mod_cast (ht k).ne'))
  have hD' : diagonal (fun i => (t i : ℂ)⁻¹) * diagonal (fun i => (t i : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg _ (funext fun k => inv_mul_cancel₀ (by exact_mod_cast (ht k).ne'))
  have hX' : M' * X.map τ.1 = X.map τ.1 * diagonal (fun i => (t i : ℂ)⁻¹) := by
    calc M' * X.map τ.1 = M' * (X.map τ.1 * (diagonal (fun i => (t i : ℂ)) * diagonal (fun i => (t i : ℂ)⁻¹))) := by
          rw [hD, Matrix.mul_one]
      _ = (M' * M) * X.map τ.1 * diagonal (fun i => (t i : ℂ)⁻¹) := by
          rw [Matrix.mul_assoc M', hX]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hMM, Matrix.one_mul]
  have hY' : M' * Y.map τ.1 = Y.map τ.1 * diagonal (fun i => (t i : ℂ)) := by
    calc M' * Y.map τ.1 = M' * (Y.map τ.1 * (diagonal (fun i => (t i : ℂ)⁻¹) * diagonal (fun i => (t i : ℂ)))) := by
          rw [hD', Matrix.mul_one]
      _ = (M' * M) * Y.map τ.1 * diagonal (fun i => (t i : ℂ)) := by
          rw [Matrix.mul_assoc M', hY]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hMM, Matrix.one_mul]
  have hZ' : ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      M' *ᵥ (fun i => τ.1 (z i)) = fun i => τ.1 (z i) := fun z z1 z2 => by
    conv_lhs => rw [← hZ z z1 z2]
    rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
  exact ⟨hb M _ _ S hS hn hn' hX hY hZ i j, hb M' _ _ S hS hn' hn hX' hY' hZ' i j⟩

theorem torus_count : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ C : Set (GA D V), IsCompact C →
    ∃ (A : ℕ) (B : ℝ), ∀ t ∈ cone r c, ∀ a : GA D V, IsTorusElt D.sp.cm.sig V.gram X Y t a →
      {δ : GF V | a⁻¹ * rat V δ * a ∈ C}.Finite ∧
      (({δ : GF V | a⁻¹ * rat V δ * a ∈ C}.ncard : ℕ) : ℝ) ≤ B * (∏ i, max (t i) 1) ^ A := by
  intro D V r X Y hW c hc C hC
  obtain ⟨hcm, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  let θ : Formalism.IndefR.Datum.InfFam D := fun ρ => infProj (embOverOf D ρ)
  have hθ : IsInfFam θ := isInfFam_infProj D
  obtain ⟨N, hN⟩ := GlobalTheory.RatCount.ncard_rational_le D θ V hθ C hC
  obtain ⟨C₀, hC₀⟩ := hN 1
  obtain ⟨l, hl, hlow⟩ := exists_cone_lower r hc
  choose cb hcb0 hcb using fun ρ => exists_torus_bound hcm (hJ V) hW (embOverOf D ρ)
  set K : ℝ := ∑ ρ, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (cb ρ + cb ρ) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun ρ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    add_nonneg (hcb0 ρ) (hcb0 ρ)
  set L : ℝ := max 1 l⁻¹ with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  refine ⟨N, |C₀| * (K * L) ^ N, fun t ht a ha => ?_⟩
  set T : ℝ := ∏ i, max (t i) 1 with hT
  have hT1 : 1 ≤ T := Finset.one_le_prod fun v _ => le_max_right _ _
  have hS1 : 1 ≤ L * T := one_le_mul_of_one_le_of_one_le hL1 hT1
  have hs1 : ∀ k, t k ≤ L * T := fun k =>
    ((le_max_left _ _).trans (le_prod_max t k)).trans (le_mul_of_one_le_left (by linarith) hL1)
  have hs2 : ∀ k, (t k)⁻¹ ≤ L * T := fun k =>
    ((inv_anti₀ hl (hlow t ht k)).trans (le_max_right _ _)).trans (le_mul_of_one_le_right (by linarith) hT1)
  have hnorm : Formalism.L2.Theta.normInf θ V a ≤ K * (L * T) := by
    unfold Formalism.L2.Theta.normInf
    rw [hK, Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have hb := hcb ρ t a (L * T) ht.1 hS1 hs1 hs2 ha i j
    have e : ∀ g : GA D V, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ ρ) g =
        archMat D.sp.cm.sig V.gram (embOverOf D ρ) (projArch D.sp.cm.sig V.gram (placeOf D ρ) g) := fun g =>
      infMat_infProj V.gram hcm (embOverOf D ρ) g
    rw [e, e, add_mul]
    exact add_le_add hb.1 hb.2
  have h0 := GlobalTheory.RatCount.normInf_nonneg θ V a
  have hsub : rat V '' {δ : GF V | a⁻¹ * rat V δ * a ∈ C} ⊆
      {γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ C, γ * a = 1 * a * o} := by
    rintro _ ⟨δ, hδ, rfl⟩
    refine ⟨?_, _, hδ, by group⟩
    exact (range_ratEmb D.sp.cm.sig V.gram).le ⟨δ, rfl⟩
  obtain ⟨hf, hcard⟩ := hC₀ a ha.1 a
  have hinj : Function.Injective (rat V) := ratEmb_injective _ _
  refine ⟨Set.Finite.of_finite_image (hf.subset hsub) hinj.injOn, ?_⟩
  rw [← Set.ncard_image_of_injective _ hinj]
  calc _ ≤ (({γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ C, γ * a = 1 * a * o}.ncard : ℕ) : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hf
    _ ≤ _ := by simpa using hcard
    _ ≤ |C₀| * Formalism.L2.Theta.normInf θ V a ^ N := by gcongr; exact le_abs_self _
    _ ≤ |C₀| * (K * (L * T)) ^ N := by gcongr
    _ = _ := by rw [mul_assoc, mul_pow, mul_pow]; ring

end GlobalTheory.CompanionTheory.TorusCount

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalAlgebraisationSchemesStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_algebraisation_schemes : GEClosedProj → GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.schemes_of_closedProj | exact GlobalTheory.CompanionTheory.FormalAlg.schemes_of_closedProj | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.schemes_of_closedProj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralCongruenceInvariantStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_integral_congruence_invariant : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (r : ℕ) (φ : Mx D V.rank r → ℂ) (β : HermE D r) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 → IfrB V ν φ (GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a β) = IfrB V ν (pull a φ) β := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Deg.ifrB_congrH | exact GlobalTheory.CompanionTheory.WeilSiegel.Deg.ifrB_congrH | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Deg.ifrB_congrH <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTrivialLineBundle
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem isHermRep_triv : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ), IsHermRep (HermLB.triv (mpStr ℤ m n)) (GlobalTheory.CompanionTheory.Ar.Top.trivLine (Bk n)) := by
  intro m n
  refine ⟨fun _ _ => 1, ?_, ?_, ?_⟩
  · intro i j c
    simp only [map_one, mul_one]
    exact (map_one (Semi.res _)).symm
  · intro i c c'
    simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine]
  · intro i c y z _ hy
    have e : CxPts.ev (mpStr ℤ m n) σ₀ ((HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)
        (((1 : Γ(MP ℤ m n, (HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)ˣ)) :
          Γ(MP ℤ m n, (HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)) y = 1 := by
      rw [CxPts.ev_eq hy, Units.val_one, map_one]
    rw [e]
    simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine, HermLB.triv, Weight.ofFun]

end GlobalTheory.CompanionTheory.MPDict
end
end

