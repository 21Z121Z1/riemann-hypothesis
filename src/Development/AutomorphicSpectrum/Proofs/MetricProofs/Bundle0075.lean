import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0069
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMongeAmpereIntegral
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormIntegralVerticalInvarianceStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_integral_vertical_invariance : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (L L' : Fin D → HermLine ι) (T : Finset ℕ) (α : ℕ → ℝ), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) → (∀ j, L j = L' j ∨ VertClose P T α (L j) (L' j)) → ∀ (Am : HermLine ι) (s : MRing ι), IsSmoothHerm Am → IsSectionOn P Am s → ptsIntegral P (pot L) (logNorm Am s) = ptsIntegral P (pot L') (logNorm Am s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.vert_deg | exact GlobalTheory.CompanionTheory.Ar.PB.vert_deg | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.vert_deg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionMapLocallyAnalyticStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_resolution_map_locally_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (P J : Ideal (MRing ι)) (P' J' : Ideal (MRing ι')) (D D' : ℕ) (R : AnLogRes P J D) (R' : AnLogRes P' J' D') (g : R'.X → R.X), J = ⊤ → (∀ x, ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ R'.lift x x ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts P', ∀ x', SameOrbit z' (R'.lift x' x') → SameOrbit (f z') (R.lift (g x') (g x'))) → HoloMap R'.A R.A g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_of_local_analytic | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_of_local_analytic | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_of_local_analytic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMongeAmpereIntegralStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_sine_monge_ampere_integral : GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ContDiffAt ℝ 2 α y → (∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y))) = 2 * ReciprocityTheory.ChartRestriction.G.AI.kappa k * ∫ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibPt.fibre_integral_any_frame | exact GlobalTheory.CompanionTheory.Ar.PB.FibPt.fibre_integral_any_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibPt.fibre_integral_any_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem minorIJ_map {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S) (A : Matrix (Fin N) (Fin N) R)
    (I J : Finset (Fin N)) : minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]; rfl
  · exact (map_zero f).symm

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem regAt_neg {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {s : Ω} (hs : RegAt x (mCoordIdeal z) s) :
    RegAt x (mCoordIdeal z) (-s) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  refine ⟨d, -g, h, fun m hm k => hg m (by rwa [support_neg] at hm) k, hh, hn, ?_⟩
  rw [map_neg, heq, neg_mul]

def regRing (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : Subring Ω where
  carrier := {s | RegAt x (mCoordIdeal z) s}
  mul_mem' := ValRing.regAt_mul
  one_mem' := ValRing.regAt_one x z
  add_mem' := ValRing.regAt_add
  zero_mem' := ValRing.regAt_zero x z
  neg_mem' := regAt_neg

def regVal (x : (Σ k, ι k) → Ω) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) : regRing x z →+* ℂ where
  toFun s := valAt x s z
  map_one' := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.1
  map_zero' := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.1
  map_mul' s t := ((ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 s t s.2 t.2).2.2.1
  map_add' s t := ((ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 s t s.2 t.2).2.2.2

def valMat {N : ℕ} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (A : Matrix (Fin N) (Fin N) Ω) :
    Matrix (Fin N) (Fin N) ℂ := Matrix.of fun a b => valAt x (A a b) z

variable {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem reg_sum (hz : z ∈ mcPts (mCoordIdeal x)) {σ : Type} (s : Finset σ) (f : σ → Ω)
    (hf : ∀ i ∈ s, RegAt x (mCoordIdeal z) (f i)) :
    RegAt x (mCoordIdeal z) (∑ i ∈ s, f i) ∧ valAt x (∑ i ∈ s, f i) z = ∑ i ∈ s, valAt x (f i) z := by
  revert hf
  refine Finset.induction_on s ?_ (fun a s ha ih hf => ?_)
  · intro _
    simp only [Finset.sum_empty]
    exact ⟨(ValRing.regAt_valAt_ring K ι Ω x z hz).1, (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.1⟩
  · rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hfa := hf a (Finset.mem_insert_self a s)
    obtain ⟨h1, h2⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨-, hadd, -, hval⟩ := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 _ _ hfa h1
    exact ⟨hadd, by rw [hval, h2]⟩

theorem reg_mul (hz : z ∈ mcPts (mCoordIdeal x)) {s t : Ω} (hs : RegAt x (mCoordIdeal z) s)
    (ht : RegAt x (mCoordIdeal z) t) :
    RegAt x (mCoordIdeal z) (s * t) ∧ valAt x (s * t) z = valAt x s z * valAt x t z := by
  obtain ⟨hm, -, hv, -⟩ := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 s t hs ht
  exact ⟨hm, hv⟩

theorem regMat_mul {N : ℕ} (hz : z ∈ mcPts (mCoordIdeal x)) {A B : Matrix (Fin N) (Fin N) Ω}
    (hA : ∀ a b, RegAt x (mCoordIdeal z) (A a b)) (hB : ∀ a b, RegAt x (mCoordIdeal z) (B a b)) :
    (∀ a b, RegAt x (mCoordIdeal z) ((A * B) a b)) ∧ valMat x z (A * B) = valMat x z A * valMat x z B := by
  have key : ∀ a b, RegAt x (mCoordIdeal z) ((A * B) a b) ∧
      valAt x ((A * B) a b) z = ∑ c, valAt x (A a c) z * valAt x (B c b) z := by
    intro a b
    rw [Matrix.mul_apply]
    obtain ⟨h1, h2⟩ := reg_sum hz Finset.univ (fun c => A a c * B c b)
      (fun c _ => (reg_mul hz (hA a c) (hB c b)).1)
    refine ⟨h1, ?_⟩
    rw [h2]
    exact Finset.sum_congr rfl fun c _ => (reg_mul hz (hA a c) (hB c b)).2
  refine ⟨fun a b => (key a b).1, ?_⟩
  ext a b
  simp only [valMat, Matrix.of_apply, Matrix.mul_apply]
  exact (key a b).2

theorem reg_minor {N : ℕ} (hz : z ∈ mcPts (mCoordIdeal x)) {A : Matrix (Fin N) (Fin N) Ω}
    (hA : ∀ a b, RegAt x (mCoordIdeal z) (A a b)) (I J : Finset (Fin N)) :
    RegAt x (mCoordIdeal z) (minorIJ A I J) ∧ valAt x (minorIJ A I J) z = minorIJ (valMat x z A) I J := by
  let A' : Matrix (Fin N) (Fin N) (regRing x z) := fun a b => ⟨A a b, hA a b⟩
  have hmap : A'.map (regRing x z).subtype = A := by
    ext a b
    rfl
  have h1 : minorIJ A I J = ((minorIJ A' I J : regRing x z) : Ω) := by
    have h := minorIJ_map (regRing x z).subtype A' I J
    rw [hmap] at h
    exact h
  have h2 : valMat x z A = A'.map (regVal x hz) := by
    ext a b
    rfl
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact (minorIJ A' I J).2
  · rw [h2, minorIJ_map, h1]
    rfl

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelDyWeights
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy

section Steps

variable {Ψ : Type} {p q : ℕ}

theorem blkF_ne_inl (K₀ : Type) (r : Ψ × Fin (p + q)) (k : K₀) : blkF Ψ p q K₀ r ≠ some (.inl k) := by
  delta blkF
  split_ifs <;> simp

theorem blkF_eq_inr (K₀ : Type) (r : Ψ × Fin (p + q)) (t : StepIx Ψ p q) :
    blkF Ψ p q K₀ r = some (.inr t) ↔ IsProperStep (p + q) p r.2 ∧ stepOf Ψ p q r = t := by
  delta blkF
  split_ifs with hp <;> simp [hp]

theorem stepOf_eq_left (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inl τ'))) :
    stepOf Ψ p q (τ, i) = ⟨.inl τ', a⟩ ↔ τ = τ' ∧ (i : ℕ) = a := by
  delta stepOf
  dsimp only
  split_ifs with hi
  · constructor
    · intro e
      rcases Sigma.mk.inj_iff.mp e with ⟨h1, h2⟩
      cases h1
      exact ⟨rfl, congrArg Fin.val (eq_of_heq h2)⟩
    · rintro ⟨rfl, h2⟩
      exact Sigma.ext rfl (heq_of_eq (Fin.ext h2))
  · constructor
    · intro e
      exact absurd (Sigma.mk.inj_iff.mp e).1 Sum.inr_ne_inl
    · rintro ⟨-, h2⟩
      have ha : (a : ℕ) < p := a.2
      exfalso
      omega

theorem stepOf_eq_right (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inr τ'))) :
    stepOf Ψ p q (τ, i) = ⟨.inr τ', a⟩ ↔ τ = τ' ∧ (i : ℕ) = p + a := by
  delta stepOf
  dsimp only
  split_ifs with hi
  · constructor
    · intro e
      exact absurd (Sigma.mk.inj_iff.mp e).1 Sum.inl_ne_inr
    · rintro ⟨-, h2⟩
      exfalso
      omega
  · constructor
    · intro e
      rcases Sigma.mk.inj_iff.mp e with ⟨h1, h2⟩
      cases h1
      have h3 : (i : ℕ) - p = a := congrArg Fin.val (eq_of_heq h2)
      exact ⟨rfl, by omega⟩
    · rintro ⟨rfl, h2⟩
      exact Sigma.ext rfl (heq_of_eq (Fin.ext (show (i : ℕ) - p = a by omega)))

end Steps

section Main

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {n : Ψ ⊕ Ψ → ℕ}
  {A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω}
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] {x₀ : (Σ k, J₀ k) → Ω} {m : Ψ ⊕ Ψ → ℕ}

open Classical in

theorem dy_apply (h : ModelOK A x₀ m) (r : Ψ × Fin (p + q)) (k : K₀ ⊕ StepIx Ψ p q) :
    (model A x₀ m h).dy r k =
      if ∀ r', blkF Ψ p q K₀ r' ≠ some k then -twist m r k else if blkF Ψ p q K₀ r = some k then 1 else 0 := by
  delta FlagModel.dy
  by_cases hc : ∀ p', (model A x₀ m h).blk p' ≠ some k
  · rw [dif_pos hc, if_pos (show ∀ r' : Ψ × Fin (p + q), blkF Ψ p q K₀ r' ≠ some k from hc)]
    rfl
  · rw [dif_neg hc, if_neg (show ¬ ∀ r' : Ψ × Fin (p + q), blkF Ψ p q K₀ r' ≠ some k from hc)]
    by_cases hb : (model A x₀ m h).blk r = some k
    · rw [if_pos hb, if_pos (show blkF Ψ p q K₀ r = some k from hb)]
    · rw [if_neg hb, if_neg (show ¬ blkF Ψ p q K₀ r = some k from hb)]

open Classical in

theorem twist_left (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inl τ'))) (ha : (a : ℕ) + 1 = p) :
    twist (K₀ := K₀) m (τ, i) (.inr ⟨.inl τ', a⟩) = -(if τ' = τ ∧ p ≤ (i : ℕ) + 1 then 1 else 0) := by
  delta twist
  dsimp only
  rw [if_neg (show ¬ ((Sum.inl τ' : Ψ ⊕ Ψ) = Sum.inr τ ∧ (a : ℕ) + 1 = q ∧ (i : ℕ) + 1 = p + q) from fun hh => Sum.inl_ne_inr hh.1), add_zero]
  by_cases hc : τ' = τ ∧ p ≤ (i : ℕ) + 1
  · rw [if_pos (show (Sum.inl τ' : Ψ ⊕ Ψ) = Sum.inl τ ∧ (a : ℕ) + 1 = p ∧ p ≤ (i : ℕ) + 1 from ⟨congrArg Sum.inl hc.1, ha, hc.2⟩), if_pos hc]
  · rw [if_neg (show ¬ ((Sum.inl τ' : Ψ ⊕ Ψ) = Sum.inl τ ∧ (a : ℕ) + 1 = p ∧ p ≤ (i : ℕ) + 1) from fun hh => hc ⟨Sum.inl_injective hh.1, hh.2.2⟩), if_neg hc]

open Classical in

theorem twist_right (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inr τ'))) (ha : (a : ℕ) + 1 = q) :
    twist (K₀ := K₀) m (τ, i) (.inr ⟨.inr τ', a⟩) = -(if τ' = τ ∧ (i : ℕ) + 1 = p + q then 1 else 0) := by
  delta twist
  dsimp only
  rw [if_neg (show ¬ ((Sum.inr τ' : Ψ ⊕ Ψ) = Sum.inl τ ∧ (a : ℕ) + 1 = p ∧ p ≤ (i : ℕ) + 1) from fun hh => Sum.inr_ne_inl hh.1), zero_add]
  by_cases hc : τ' = τ ∧ (i : ℕ) + 1 = p + q
  · rw [if_pos (show (Sum.inr τ' : Ψ ⊕ Ψ) = Sum.inr τ ∧ (a : ℕ) + 1 = q ∧ (i : ℕ) + 1 = p + q from ⟨congrArg Sum.inr hc.1, ha, hc.2⟩), if_pos hc]
  · rw [if_neg (show ¬ ((Sum.inr τ' : Ψ ⊕ Ψ) = Sum.inr τ ∧ (a : ℕ) + 1 = q ∧ (i : ℕ) + 1 = p + q) from fun hh => hc ⟨Sum.inr_injective hh.1, hh.2.2⟩), if_neg hc]

open Classical in

theorem dy_left (h : ModelOK A x₀ m) (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inl τ'))) :
    (model A x₀ m h).dy (τ, i) (.inr ⟨.inl τ', a⟩) =
      if τ = τ' ∧ ((i : ℕ) = a ∨ ((a : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) then 1 else 0 := by
  have ha : (a : ℕ) < p := a.2
  have key : ∀ r' : Ψ × Fin (p + q), blkF Ψ p q K₀ r' = some (.inr ⟨.inl τ', a⟩) ↔
      r'.1 = τ' ∧ (r'.2 : ℕ) = a ∧ (a : ℕ) + 1 ≠ p := by
    rintro ⟨σ', j⟩
    rw [blkF_eq_inr, stepOf_eq_left]
    dsimp only
    delta IsProperStep
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h3, h4, by omega⟩
    · rintro ⟨h3, h4, h5⟩
      exact ⟨⟨by omega, by omega⟩, h3, h4⟩
  by_cases hp : (a : ℕ) + 1 = p
  · rw [dy_apply h, if_pos (fun r' e => ((key r').1 e).2.2 hp), twist_left τ τ' i a hp, neg_neg]
    rcases eq_or_ne τ' τ with rfl | hne
    · simp only [eq_self_iff_true, true_and]
      split_ifs <;> omega
    · simp [hne, hne.symm]
  · rw [dy_apply h, if_neg (fun H => H (τ', ⟨(a : ℕ), by omega⟩) ((key _).2 ⟨rfl, rfl, hp⟩))]
    simp only [key]
    rcases eq_or_ne τ τ' with rfl | hne
    · simp only [eq_self_iff_true, true_and]
      split_ifs <;> omega
    · simp [hne]

open Classical in

theorem dy_right (h : ModelOK A x₀ m) (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inr τ'))) :
    (model A x₀ m h).dy (τ, i) (.inr ⟨.inr τ', a⟩) = if τ = τ' ∧ (i : ℕ) = p + a then 1 else 0 := by
  have ha : (a : ℕ) < q := a.2
  have key : ∀ r' : Ψ × Fin (p + q), blkF Ψ p q K₀ r' = some (.inr ⟨.inr τ', a⟩) ↔
      r'.1 = τ' ∧ (r'.2 : ℕ) = p + a ∧ (a : ℕ) + 1 ≠ q := by
    rintro ⟨σ', j⟩
    rw [blkF_eq_inr, stepOf_eq_right]
    dsimp only
    delta IsProperStep
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h3, h4, by omega⟩
    · rintro ⟨h3, h4, h5⟩
      exact ⟨⟨by omega, by omega⟩, h3, h4⟩
  by_cases hq : (a : ℕ) + 1 = q
  · rw [dy_apply h, if_pos (fun r' e => ((key r').1 e).2.2 hq), twist_right τ τ' i a hq, neg_neg]
    rcases eq_or_ne τ' τ with rfl | hne
    · simp only [eq_self_iff_true, true_and]
      split_ifs <;> omega
    · simp [hne, hne.symm]
  · rw [dy_apply h, if_neg (fun H => H (τ', ⟨p + (a : ℕ), by omega⟩) ((key _).2 ⟨rfl, rfl, hq⟩))]
    simp only [key]
    rcases eq_or_ne τ τ' with rfl | hne
    · simp only [eq_self_iff_true, true_and]
      split_ifs <;> omega
    · simp [hne]

end Main

open Classical in

theorem dy_flag : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ) (h : ModelOK A x₀ m) (τ : Ψ) (i : Fin (p + q)), (∀ k, (model A x₀ m h).dy (τ, i) (.inl k) = -((rkW i * m (.inl τ) + rkO i * m (.inr τ) : ℕ) : ℤ)) ∧ ∀ t : StepIx Ψ p q, ((t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) → (model A x₀ m h).dy (τ, i) (.inr t) = 1) ∧ (¬ (t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) → (model A x₀ m h).dy (τ, i) (.inr t) = 0) := by
  intro Ψ _ p q Ω _ _ n A K₀ _ J₀ _ x₀ m h τ i
  refine ⟨fun k => ?_, fun t => ?_⟩
  · rw [dy_apply h, if_pos (fun r' => blkF_ne_inl K₀ r' k)]
    rfl
  · obtain ⟨s, a⟩ := t
    cases s with
    | inl τ' =>
      have e := (eq_comm.trans (stepOf_eq_left τ τ' i a) :
        (⟨.inl τ', a⟩ : StepIx Ψ p q) = stepOf Ψ p q (τ, i) ↔ _)
      have hc : ((⟨.inl τ', a⟩ : StepIx Ψ p q) = stepOf Ψ p q (τ, i) ∨
          ((Sum.inl τ' : Ψ ⊕ Ψ) = .inl τ ∧ (a : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) ↔
          (τ = τ' ∧ ((i : ℕ) = a ∨ ((a : ℕ) + 1 = p ∧ p ≤ (i : ℕ)))) := by
        rw [e, Sum.inl.injEq]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
          · exact ⟨h1, Or.inl h2⟩
          · exact ⟨h1.symm, Or.inr ⟨h2, h3⟩⟩
        · rintro ⟨h1, h2 | ⟨h2, h3⟩⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1.symm, h2, h3⟩
      refine ⟨fun hc' => ?_, fun hn => ?_⟩
      · rw [dy_left h, if_pos (hc.1 hc')]
      · rw [dy_left h, if_neg (fun h' => hn (hc.2 h'))]
    | inr τ' =>
      have e := (eq_comm.trans (stepOf_eq_right τ τ' i a) :
        (⟨.inr τ', a⟩ : StepIx Ψ p q) = stepOf Ψ p q (τ, i) ↔ _)
      have hc : ((⟨.inr τ', a⟩ : StepIx Ψ p q) = stepOf Ψ p q (τ, i) ∨
          ((Sum.inr τ' : Ψ ⊕ Ψ) = .inl τ ∧ (a : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) ↔
          (τ = τ' ∧ (i : ℕ) = p + a) := by
        rw [e]
        constructor
        · rintro (h1 | ⟨h1, -⟩)
          · exact h1
          · exact absurd h1 Sum.inr_ne_inl
        · intro h1
          exact Or.inl h1
      refine ⟨fun hc' => ?_, fun hn => ?_⟩
      · rw [dy_right h, if_pos (hc.1 hc')]
      · rw [dy_right h, if_neg (fun h' => hn (hc.2 h'))]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralUniqueEmbedding
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
open GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

noncomputable def conjugateProjection {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) where
  toFun w := star (Ψ (star w))
  map_add' a b := by simp only [star_add, map_add]
  map_smul' c w := by
    simp only [star_smul, map_smul, RingHom.id_apply, star_star]

theorem conjugateProjection_star {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (w : ((k : K) → ι k) → ℂ) : conjugateProjection Ψ (star w) = star (Ψ w) := by
  change star (Ψ (star (star w))) = _
  rw [star_star]

theorem isSectionOn_one_of_degree_zero {P : Ideal (MRing ι)} {d : ℕ} {A : HermLine ι}
    (hP : IsArithVar P d) (hA : A.a = 0) : IsSectionOn P A 1 := by
  refine ⟨0, fun k => by simp [hA], ?_, ?_⟩
  · intro m hm k
    have hm0 : m = 0 := by
      classical
      have := MvPolynomial.support_one (R := ℤ) (σ := Σ k, ι k) ▸ hm
      simpa using this
    simp [hm0]
  · exact (Ideal.ne_top_iff_one P).1 hP.2.1.1.ne_top

open Classical in

theorem logNorm_one_eq_indicator {Ω F : Type} [Field Ω] [Field F] [Algebra F Ω] {y : (Σ k, ι k) → Ω}
    {P : Ideal (MRing ι)} {tg : F →+* ℂ} {B : HermLine ι}
    (huniq : ∀ z ∈ mcPts P, ∃! s : F →+* ℂ, LiesOver y s z)
    (hB : ∀ z ∈ mcPts P, ∀ s : F →+* ℂ, LiesOver y s z → B.h z = if s = tg then Real.exp (-1) else 1) :
    ∀ z ∈ mcPts P, logNorm B 1 z = ({z | LiesOver y tg z}.indicator fun _ => (1 : ℝ)) z := by
  classical
  intro z hz
  obtain ⟨s, hs, hs'⟩ := huniq z hz
  have hone : ‖eval z (map (Int.castRingHom ℂ) (1 : MRing ι))‖ = 1 := by simp
  unfold logNorm
  rw [hone, hB z hz s hs]
  by_cases hst : s = tg
  · subst hst
    rw [Set.indicator_of_mem (show z ∈ {z | LiesOver y s z} from hs), if_pos rfl, one_div,
      Real.log_inv, Real.log_exp, neg_neg]
  · rw [Set.indicator_of_notMem (fun h => hst (hs' tg h).symm), if_neg hst]
    simp

end SlopeTestRemainingChoices

theorem conjugate_pieces_same_mass :
    ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (sg : F →+* ℂ), IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsConjInvariantH (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y (ComplexEmbedding.conjugate sg) z}.indicator fun _ => (1 : ℝ)) = ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  intro hRes K _ ι _ Ω _ F _ _ _ y D L sg hP hL hC huniq
  classical
  have hpos : ∀ tg s : F →+* ℂ, 0 < (if s = tg then Real.exp (-1) else (1 : ℝ)) := by
    intro tg s
    split_ifs
    · exact Real.exp_pos _
    · exact one_pos
  obtain ⟨B, hBa, hBs, hB⟩ := exists_smooth_weight_const_near_embeddings K ι Ω F y
    (fun s => if s = sg then Real.exp (-1) else 1) (hpos sg) huniq
  obtain ⟨B', hBa', hBs', hB'⟩ := exists_smooth_weight_const_near_embeddings K ι Ω F y
    (fun s => if s = ComplexEmbedding.conjugate sg then Real.exp (-1) else 1)
    (hpos (ComplexEmbedding.conjugate sg)) huniq
  have hBv : ∀ z ∈ mcPts (mCoordIdeal y), ∀ s : F →+* ℂ, LiesOver y s z →
      B.h z = if s = sg then Real.exp (-1) else 1 := fun z hz s hs => (hB z hz s hs).self_of_nhds
  have hBv' : ∀ z ∈ mcPts (mCoordIdeal y), ∀ s : F →+* ℂ, LiesOver y s z →
      B'.h z = if s = ComplexEmbedding.conjugate sg then Real.exp (-1) else 1 :=
    fun z hz s hs => (hB' z hz s hs).self_of_nhds
  rw [← GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts (mCoordIdeal y)
      (fun _ _ _ => rfl) (logNorm_one_eq_indicator huniq hBv'),
    ← GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts (mCoordIdeal y)
      (fun _ _ _ => rfl) (logNorm_one_eq_indicator huniq hBv)]
  by_cases hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ), IsGoodProj (mCoordIdeal y) Ψ
  · obtain ⟨Ψ, hΨ⟩ := hex
    have hstar : ∀ z ∈ mcPts (mCoordIdeal y), B'.h (star z) = B.h z := by
      intro z hz
      obtain ⟨s, hs, -⟩ := huniq z hz
      have hzc : star z ∈ mcPts (mCoordIdeal y) := conjVec_mem_mcPts hz
      have hsc : LiesOver y (ComplexEmbedding.conjugate s) (star z) := liesOver_conjVec hs
      have hiff : ComplexEmbedding.conjugate s = ComplexEmbedding.conjugate sg ↔ s = sg :=
        ⟨fun h => by simpa using congrArg ComplexEmbedding.conjugate h, fun h => by rw [h]⟩
      rw [hBv' _ hzc _ hsc, hBv z hz s hs]
      simp only [hiff]
    obtain ⟨hΨ', hI⟩ := GlobalTheory.T.points_integral_conjugation_symmetry K ι (mCoordIdeal y) D Ψ (conjugateProjection Ψ) L B B' hP hΨ
      (conjugateProjection_star Ψ) hL hC hBa hBs hBa' hBs' hstar
    rw [ptsIntegral_eq_at hRes resBridge hP hΨ' hL hBs' (isSectionOn_one_of_degree_zero hP hBa'),
      ptsIntegral_eq_at hRes resBridge hP hΨ hL hBs (isSectionOn_one_of_degree_zero hP hBa), hI]
  · unfold ptsIntegral
    rw [dif_neg hex, dif_neg hex]

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SemicharacterThetaCharacteristicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semicharacter_theta_characteristic : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (χ : Λ → ℂ),
    (∀ l l' : Λ, χ (l + l') = χ l * χ l' * Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) - bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ))) →
    (∀ l, χ l ^ 2 = 1) →
    ∃ a c : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, c i = 0 ∨ c i = 1 / 2) ∧
      ∀ x, χ x = GlobalTheory.CanTh.canMult a c (fun i => bs.repr x (Sum.inl i)) (fun i => bs.repr x (Sum.inr i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Nform.exists_half_canMult | exact GlobalTheory.CompanionTheory.Ar.Nform.exists_half_canMult | (intros; apply GlobalTheory.CompanionTheory.Ar.Nform.exists_half_canMult <;> assumption)
end

