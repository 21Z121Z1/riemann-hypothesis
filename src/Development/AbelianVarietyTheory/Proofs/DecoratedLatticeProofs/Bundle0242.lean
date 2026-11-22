import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0209
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0218
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartz
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.IkSchwartz

open GlobalTheory.SchwartzBruhatTensor GlobalTheory.PartialIntegral

abbrev AEf (D : D7) : Type := Af D.host.F ⊗[D.host.F] D.host.E

theorem exists_split {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (m n : ℕ) :
    ∃ e : Mx D m n ≃ₜ+ (D.what₂.Tau → Fin m → Fin n → ℂ) × (Fin m → Fin n → AEf D),
      ∀ x, e x = (fun τ i j => compAt θ τ x i j, fun i j => finPart D (x i j)) := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨s, hsc, hsf, hsi⟩ := exists_finSection D
  refine ⟨{ toFun := fun x => (fun τ i j => compAt θ τ x i j, fun i j => finPart D (x i j))
            invFun := fun p => s.mapMatrix (Matrix.of p.2) + chartM σ m n p.1
            left_inv := fun x => (decomp hσ hsf hsi x).symm
            right_inv := fun p => Prod.ext ?_ ?_
            map_add' := fun x y => Prod.ext ?_ ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun x => rfl⟩
  · funext τ i j
    show θ τ (infPart D (s (p.2 i j) + σ fun τ => p.1 τ i j)) = p.1 τ i j
    rw [RingHom.map_add, RingHom.map_add, hsi, hσ.comp, RingHom.map_zero, zero_add]
  · funext i j
    show finPart D (s (p.2 i j) + σ fun τ => p.1 τ i j) = p.2 i j
    rw [RingHom.map_add, hsf, hσ.fin, add_zero]
  · funext τ i j
    show θ τ (infPart D (x i j + y i j)) = θ τ (infPart D (x i j)) + θ τ (infPart D (y i j))
    rw [RingHom.map_add, RingHom.map_add]
  · funext i j
    exact (finPart D).map_add _ _
  · exact (continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.FockCompare.continuous_comp hθ τ).comp (continuous_id.matrix_elem i j)).prodMk
      (continuous_pi fun i => continuous_pi fun j =>
        (GlobalTheory.Member.continuous_finPart D).comp (continuous_id.matrix_elem i j))
  · haveI := (lattice_Mx D m n).1
    refine Continuous.add ?_ ((continuous_chartM hσ.cont m n).comp continuous_fst)
    exact continuous_pi fun i => continuous_pi fun j =>
      hsc.comp ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))

def lmul {R : Type} [CommRing R] {m t : ℕ} (n : ℕ) (J : Matrix (Fin m) (Fin t) R) (x : Fin t → Fin n → R) :
    Fin m → Fin n → R := J ⬝ Matrix.of x

theorem continuous_lmul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m t : ℕ} (n : ℕ)
    (J : Matrix (Fin m) (Fin t) R) : Continuous (lmul n J) :=
  Continuous.matrix_mul (A := fun _ => J) (B := fun x : Matrix (Fin t) (Fin n) R => x) continuous_const continuous_id

def lmulC {ι : Type} {m t : ℕ} (n : ℕ) (J : ι → Matrix (Fin m) (Fin t) ℂ) :
    (ι → Fin t → Fin n → ℂ) →ₗ[ℝ] (ι → Fin m → Fin n → ℂ) where
  toFun c τ := lmul n (J τ) (c τ)
  map_add' c c' := funext fun τ => Matrix.mul_add (J τ) (Matrix.of (c τ)) (Matrix.of (c' τ))
  map_smul' r c := funext fun τ => Matrix.mul_smul (J τ) r (Matrix.of (c τ))

variable {D : D7} {T T' : HSp D} {t : ℕ} (d : HypDec T T' t) {R : Type} [CommRing R] (φ : AE D →+* R) {n : ℕ}

theorem map_emb (x : Mx D t n) (a : Mx D T'.rank n) :
    (fun i j => φ ((d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n) i j)) =
      lmul n (d.jX.map φ) (fun i j => φ (x i j)) + lmul n (d.j0.map φ) (fun i j => φ (a i j)) := by
  show (d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n).map φ = d.jX.map φ ⬝ x.map φ + d.j0.map φ ⬝ a.map φ
  rw [Matrix.map_add _ φ.map_add, Matrix.map_mul, Matrix.map_mul]

theorem pX_emb (x : Fin t → Fin n → R) (a : Fin T'.rank → Fin n → R) :
    lmul n (d.pX.map φ) (lmul n (d.jX.map φ) x + lmul n (d.j0.map φ) a) = x := by
  show d.pX.map φ ⬝ (d.jX.map φ ⬝ Matrix.of x + d.j0.map φ ⬝ Matrix.of a) = Matrix.of x
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, d.pX_jX, d.pX_j0,
    Matrix.map_one _ φ.map_zero φ.map_one, Matrix.map_zero _ φ.map_zero, Matrix.one_mul, Matrix.zero_mul, add_zero]

theorem wittHyperbolic_projAnisotropic_leftMul_embedding (x : Fin t → Fin n → R) (a : Fin T'.rank → Fin n → R) :
    lmul n (d.p0.map φ) (lmul n (d.jX.map φ) x + lmul n (d.j0.map φ) a) = a := by
  show d.p0.map φ ⬝ (d.jX.map φ ⬝ Matrix.of x + d.j0.map φ ⬝ Matrix.of a) = Matrix.of a
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, d.p0_jX, d.p0_j0,
    Matrix.map_one _ φ.map_zero φ.map_one, Matrix.map_zero _ φ.map_zero, Matrix.one_mul, Matrix.zero_mul, zero_add]

theorem map_emb_fin (x : Mx D t n) (a : Mx D T'.rank n) :
    (fun i j => finPart D ((d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n) i j)) =
      lmul n (d.jX.map (finPart D)) (fun i j => finPart D (x i j)) +
        lmul n (d.j0.map (finPart D)) (fun i j => finPart D (a i j)) := map_emb d (finPart D) x a

set_option maxHeartbeats 800000 in

theorem pure {θ : InfFam D} (hθ : IsInfFam θ) (μ : Measure (Mx D t n)) [μ.IsAddHaarMeasure]
    (f : SchwartzMap (D.what₂.Tau → Fin T.rank → Fin n → ℂ) ℂ) (g : (Fin T.rank → Fin n → AEf D) → ℂ)
    (hg : g ∈ WeilM.SB (Fin T.rank → Fin n → AEf D)) (Φ : Mx D T.rank n → ℂ)
    (hΦ : Φ = fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) :
    (∀ a : Mx D T'.rank n, Integrable (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) μ) ∧ ikS d μ Φ ∈ schwartzA θ T'.rank n := by
  haveI : IsModuleTopology (Af D.host.F) (AEf D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AEf D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : LocallyCompactSpace (AEf D) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AEf D) := e0.secondCountableTopology
  haveI : T2Space (AEf D) := e0.isEmbedding.t2Space
  letI : MeasurableSpace (Fin t → Fin n → AEf D) := borel _
  haveI : BorelSpace (Fin t → Fin n → AEf D) := ⟨rfl⟩
  haveI : BorelSpace (Mx D t n) := ⟨rfl⟩
  haveI := (lattice_Mx D t n).1
  obtain ⟨e, he⟩ := exists_split hθ t n
  let μr : Measure (D.what₂.Tau → Fin t → Fin n → ℂ) := Measure.addHaar
  let ν : Measure (Fin t → Fin n → AEf D) := Measure.addHaar
  obtain ⟨c, hc⟩ := exists_integral_split e μ μr ν
  let φ : D.what₂.Tau → AE D →+* ℂ := fun τ => (θ τ).comp (infPart D)
  obtain ⟨hf1, h, hh⟩ := schwartz_partial μr f (lmulC n fun τ => d.jX.map (φ τ)) (lmulC n fun τ => d.j0.map (φ τ))
    (fun x a hxa => by
      refine ⟨funext fun τ => ?_, funext fun τ => ?_⟩
      · have h0 : lmul n (d.jX.map (φ τ)) (x τ) + lmul n (d.j0.map (φ τ)) (a τ) = 0 := congrFun hxa τ
        rw [← pX_emb d (φ τ) (x τ) (a τ), h0]
        exact Matrix.mul_zero _
      · have h0 : lmul n (d.jX.map (φ τ)) (x τ) + lmul n (d.j0.map (φ τ)) (a τ) = 0 := congrFun hxa τ
        rw [← wittHyperbolic_projAnisotropic_leftMul_embedding d (φ τ) (x τ) (a τ), h0]
        exact Matrix.mul_zero _)
  obtain ⟨hg1, hg2, hg3⟩ := locallyConstant_partial ν hg.1 hg.2 (continuous_lmul n (d.jX.map (finPart D)))
    (continuous_lmul n (d.j0.map (finPart D))) (continuous_lmul n (d.pX.map (finPart D)))
    (continuous_lmul n (d.p0.map (finPart D))) (pX_emb d (finPart D)) (wittHyperbolic_projAnisotropic_leftMul_embedding d (finPart D))
  have key : ∀ a : Mx D T'.rank n, (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) = fun x =>
      f (lmulC n (fun τ => d.jX.map (φ τ)) (e x).1 + lmulC n (fun τ => d.j0.map (φ τ)) fun τ i j => compAt θ τ a i j) *
      g (lmul n (d.jX.map (finPart D)) (e x).2 + lmul n (d.j0.map (finPart D)) fun i j => finPart D (a i j)) := by
    intro a
    funext x
    have h2 : (fun τ i j => compAt θ τ (d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n) i j) =
        lmulC n (fun τ => d.jX.map (φ τ)) (fun τ i j => compAt θ τ x i j) +
          lmulC n (fun τ => d.j0.map (φ τ)) fun τ i j => compAt θ τ a i j := funext fun τ => map_emb d (φ τ) x a
    rw [hΦ, he]
    exact congrArg₂ (· * ·) (congrArg f h2) (congrArg g (map_emb_fin d x a))
  refine ⟨fun a => by rw [key a]; exact (hc _ _ (hf1 _) (hg1 _)).1, ?_⟩
  have e2 : ikS d μ Φ = c • fun a : Mx D T'.rank n => h (fun τ i j => compAt θ τ a i j) *
      (fun b => ∫ y, g (lmul n (d.jX.map (finPart D)) y + lmul n (d.j0.map (finPart D)) b) ∂ν)
        (fun i j => finPart D (a i j)) := by
    funext a
    refine (congrArg (fun F => ∫ x, F x ∂μ) (key a)).trans ?_
    refine (hc _ _ (hf1 _) (hg1 _)).2.trans ?_
    rw [← hh]
    rfl
  rw [e2]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨h, _, ⟨hg2, hg3⟩, rfl⟩)

theorem ikS_mem_schwartzA : ∀ (D : D7), ∀ θ : InfFam D, IsInfFam θ → ∀ (T T' : HSp D) (t n : ℕ) (d : HypDec T T' t) (μ : Measure (Mx D t n)) (𝓕 : Set (Mx D t n)), IsCovolOne (ratMx D t n) μ 𝓕 → ∀ Φ ∈ schwartzA θ T.rank n, ikS d μ Φ ∈ schwartzA θ T'.rank n := by
  intro D θ hθ T T' t n d μ 𝓕 hμ Φ hΦ
  haveI := hμ.1
  suffices h : (∀ a : Mx D T'.rank n, Integrable (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) μ) ∧ ikS d μ Φ ∈ schwartzA θ T'.rank n from h.2
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, h⟩ := h
    exact pure d hθ μ f g hg Φ h
  | zero =>
    refine ⟨fun a => integrable_zero _ _ _, ?_⟩
    have : ikS d μ (0 : Mx D T.rank n → ℂ) = 0 := funext fun a => integral_zero _ _
    rw [this]
    exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    refine ⟨fun a => (h1.1 a).add (h2.1 a), ?_⟩
    have : ikS d μ (Φ + Ψ) = ikS d μ Φ + ikS d μ Ψ := funext fun a => integral_add (h1.1 a) (h2.1 a)
    rw [this]
    exact Submodule.add_mem _ h1.2 h2.2
  | smul c Φ _ h =>
    refine ⟨fun a => (h.1 a).smul c, ?_⟩
    have : ikS d μ (c • Φ) = c • ikS d μ Φ := funext fun a => integral_smul c _
    rw [this]
    exact Submodule.smul_mem _ c h.2

end GlobalTheory.RegSch.IkSchwartz

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndicatorVac

theorem splitC (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : IsSplitIdem D (cA D q.e) := by
  obtain ⟨h1, h2, v, ε, hv, h3⟩ := q.split
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hv, ?_⟩
  · rw [GlobalTheory.LatVac.cA_cA, mul_comm, h2]
  · rw [GlobalTheory.LatVac.cA_cA, add_comm, h3]

theorem e_eq (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : q.sec 1 = q.e := by
  have := q.sec_pr 1; rw [map_one, mul_one] at this; exact this

theorem mul_e (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (e' : Formalism.L2.Theta.AE D) (he : e' * e' = e') : q.e * e' = 0 ∨ q.e * e' = q.e := by
  have hp : q.pr e' * q.pr e' = q.pr e' := by rw [← map_mul, he]
  rcases (IsIdempotentElem.iff_eq_zero_or_one.1 hp) with h | h
  · left; rw [← q.sec_pr, h, map_zero]
  · right; rw [← q.sec_pr, h, e_eq]

set_option maxHeartbeats 1600000 in
theorem cases (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (e' : Formalism.L2.Theta.AE D) (he' : IsSplitIdem D e') {m n : ℕ} (u : Mx D m n)
    (hsupp : ∀ i j, (q.e + cA D q.e) * u i j = u i j) (hu : IsHalf e' u) :
    u = 0 ∨ IsHalf q.e u ∨ IsHalf (cA D q.e) u := by
  obtain ⟨h1, h2, -⟩ := he'
  have hc1 : cA D e' * cA D e' = cA D e' := by rw [← map_mul, h1]
  have hA := mul_e D k q e' h1
  have hB : cA D q.e * e' = 0 ∨ cA D q.e * e' = cA D q.e := by
    rcases mul_e D k q (cA D e') hc1 with h | h
    · left; have := congrArg (cA D) h; rwa [map_mul, GlobalTheory.LatVac.cA_cA, map_zero] at this
    · right; have := congrArg (cA D) h; rwa [map_mul, GlobalTheory.LatVac.cA_cA] at this
  have hu' : ∀ i j, u i j = q.e * e' * u i j + cA D q.e * e' * u i j := fun i j => by
    rw [mul_assoc, mul_assoc, hu i j, ← add_mul, hsupp i j]
  have hee : q.e * q.e = q.e := q.split.1
  have hce : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, hee]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · left; ext i j; rw [hu' i j, hA, hB]; simp
  · right; right; intro i j; rw [hu' i j, hA, hB, zero_mul, zero_add, ← mul_assoc, hce]
  · right; left; intro i j; rw [hu' i j, hA, hB, zero_mul, add_zero, ← mul_assoc, hee]
  · exfalso
    have hpe : q.pr q.e = 1 := by rw [← e_eq D k q, q.pr_sec]
    have h7 : q.e = 0 := by
      rcases mul_e D k q (cA D e') hc1 with h | h
      · have h5 : cA D q.e * e' = 0 := by
          have := congrArg (cA D) h; rwa [map_mul, GlobalTheory.LatVac.cA_cA, map_zero] at this
        have h6 : cA D q.e = 0 := hB.symm.trans h5
        have := congrArg (cA D) h6; rwa [GlobalTheory.LatVac.cA_cA, map_zero] at this
      · calc q.e = q.e * cA D e' := h.symm
          _ = q.e * e' * cA D e' := by rw [hA]
          _ = 0 := by rw [mul_assoc, h2, mul_zero]
    rw [h7, map_zero] at hpe
    exact zero_ne_one hpe

end GlobalTheory.IndicatorVac

open GlobalTheory.IndicatorVac in

theorem GlobalTheory.LocMod.indicator_vac : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → (∀ Tm O, (ofSplit q).IsModel ψ FS FT Tm → IsOne O → GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) (Tm O)) ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) f → ∃ Tm, (ofSplit q).IsModel ψ FS FT Tm ∧ ∀ O, IsOne O → Tm O = f := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT ψ ψk hψ hc hcond LS LT hS hT hFS hFT
  have hmono : ∀ u, u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v) → u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True :=
    fun u hu => AddSubgroup.closure_mono (fun w hw => by
      obtain ⟨α, h1, _, h3⟩ := hw
      exact ⟨α, h1, fun v hv => absurd trivial hv, h3⟩) hu
  have hsy : ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v),
      ψ (symplO S T ((ofSplit q).up FS FT x) u) = 1 := fun x hx u hu =>
    GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT (hmono _ (GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT x hx)) (hmono _ hu)
  constructor
  · intro Tm O hTm hO
    have hE : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v), IsHalf q.e u → heisO ψ S T u (Tm O) = Tm O := by
      intro u hu he
      obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT u hu he
      refine (hTm.trans x O O fun t => ?_).symm
      rw [hO]
      have hh : (∀ r s, (t + x) r s ∈ 𝒪[k]) ↔ ∀ r s, t r s ∈ 𝒪[k] := by
        refine ⟨fun h r s => ?_, fun h r s => ?_⟩
        · have := sub_mem (h r s) (hx r s); simpa using this
        · exact add_mem (h r s) (hx r s)
      by_cases ht : ∀ r s, t r s ∈ 𝒪[k]
      · rw [Set.indicator_of_mem (show t ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht),
          Set.indicator_of_mem (show t + x ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from hh.2 ht)]
      · rw [Set.indicator_of_notMem (show t ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht),
          Set.indicator_of_notMem (show t + x ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from fun h => ht (hh.1 h))]
    have hC : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v), IsHalf (cA D q.e) u → heisO ψ S T u (Tm O) = Tm O := by
      intro u hu he
      refine (hTm.modul u he O O fun t => ?_).symm
      rw [hO]
      by_cases ht : ∀ r s, t r s ∈ 𝒪[k]
      · rw [hsy t ht u hu, one_mul]
      · rw [Set.indicator_of_notMem (show t ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht), mul_zero]
    refine ⟨hTm.theta O, ?_, ?_⟩
    · intro u hu
      obtain ⟨ha, hsupp⟩ := GlobalTheory.T.completed_hom_lattice_stable_split_idempotent D k q S T LS LT u hu
      set a : WO S T := Matrix.of fun i j => q.e * u i j with ha_def
      have hb : u - a ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v) := sub_mem hu ha
      have hee : q.e * q.e = q.e := q.split.1
      have hce : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, hee]
      have haH0 : IsHalf q.e a := fun i j => by
        simp only [ha_def, Matrix.of_apply]; rw [← mul_assoc, hee]
      have hbH0 : IsHalf (cA D q.e) (u - a) := fun i j => by
        have h1 : (u - a) i j = cA D q.e * u i j := by
          simp only [Matrix.sub_apply, ha_def, Matrix.of_apply]
          have := hsupp i j
          linear_combination -this
        rw [h1, ← mul_assoc, hce]
      have haH : IsHalf q.e (a + a) := fun i j => by rw [Matrix.add_apply, mul_add, haH0 i j]
      have hbH : IsHalf (cA D q.e) ((u - a) + (u - a)) := fun i j => by rw [Matrix.add_apply, mul_add, hbH0 i j]
      have h2 : (2 • u : WO S T) = (a + a) + ((u - a) + (u - a)) := by rw [two_nsmul]; abel
      have key := GlobalTheory.LatVac.heisO_heisO ψ (a + a) ((u - a) + (u - a)) (Tm O)
      rw [hC _ (add_mem hb hb) hbH, hE _ (add_mem ha ha) haH, ← h2] at key
      have hph : ψ (symplOH S T (a + a) ((u - a) + (u - a))) = 1 := by
        obtain ⟨x, hx, hxa⟩ := GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT a ha haH0
        have h3 : symplOH S T (a + a) ((u - a) + (u - a)) = symplO S T a ((u - a) + (u - a)) := by
          rw [symplOH, GlobalTheory.LatVac.symplO_add_left, mul_add, ← add_mul, ← RingHom.map_add, add_halves,
            RingHom.map_one, one_mul]
        rw [h3]
        have := hsy x hx _ (add_mem hb hb)
        rwa [← hxa] at this
      rw [hph, one_smul] at key
      exact key.symm
    · intro e' he' u hu hue
      rcases cases D k q e' he' u (GlobalTheory.T.completed_hom_lattice_stable_split_idempotent D k q S T LS LT u hu).2 hue with h | h | h
      · subst h; exact GlobalTheory.LatVac.heisO_zero ψ _
      · exact hE u hu h
      · exact hC u hu h
  · intro f hf
    have h78 := GlobalTheory.T.heisenberg_frame_half_inverse D k (ofSplit q) Y Y' S T FS FT ψ ψk hc
    have hth : IsThetaFunO ψ S T f := hf.1
    have hlv : IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) (· = q.v)) f := hf.2
    have h1 : ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → heisO ψ S T ((ofSplit q).up FS FT x) f = f :=
      fun x hx => hlv.2 q.e q.split _ (GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT x hx) (h78.1 x).1
    have h2 : ∀ y : WO S T, IsHalf (cA D (ofSplit q).e) y →
        (∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ψ (symplO S T ((ofSplit q).up FS FT x) y) = 1) →
        heisO ψ S T y f = f := fun y hy hann =>
      hlv.2 (cA D q.e) (splitC D k q) y
        (GlobalTheory.T.conjugate_half_annihilator_mem_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT ψ ψk hψ hc hcond y hy hann) hy
    obtain ⟨T₁, hT₁, hT₁O⟩ := (GlobalTheory.T.localSchrodingerModel_uniq_transport_exists D k (ofSplit q) Y Y' S T FS FT ψ hψ).2.2 f hth h1 h2
    exact ⟨T₁, hT₁, fun O hO => hT₁O O hO⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HalfInvariance

theorem integral_translate {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsAddHaarMeasure] (F : G → ℂ) (a : G) :
    ∫ x, F (x + a) ∂ν = ∫ x, F x ∂ν := by
  simp_rw [add_comm _ a]
  exact integral_add_left_eq_self (μ := ν) F a

set_option maxHeartbeats 1000000 in

theorem half_avg_heis_inv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S₀ T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S₀ T f → ℓ₀ (heisO ψ S₀ T u f) = ℓ₀ f) → ∀ H : AddSubgroup (Mx D T.rank ρ), (∀ x, x ∈ H ↔ ∀ i j, cA D e * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure], ∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 (heisO ψ S T u f) x.1) ∂ν = ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 f x.1) ∂ν := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ hℓ₀ H hH _ _ ν _ u hu f hf
  have hee : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA]; exact he.2.1
  have horth : ∀ {x y : WO S T}, IsHalf (cA D e) x → IsHalf (cA D e) y → symplO S T x y = 0 :=
    fun hx hy => GlobalTheory.SplitScalar.symplO_eq_zero S T hee hx hy
  have hhalfR : ∀ {m n k : ℕ} {t : Mx D m n} (M : Matrix (Fin n) (Fin k) (AE D)), IsHalf (cA D e) t →
      IsHalf (cA D e) (HMul.hMul t M : Mx D m k) := fun M ht i j => by
    simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, ht i _]

  set a : Mx D T.rank ρ := (d.coordS T u).1 with ha_def
  set w : WO S₀ T := (d.coordS T u).2.1 with hw_def
  set b : Mx D T.rank ρ := (d.coordS T u).2.2 with hb_def
  have hu_eq : u = d.extX T a + d.ext0 T w + d.extY T b := ((d.coordS T).symm_apply_apply u).symm
  have ha : IsHalf (cA D e) a := hhalfR _ hu
  have hw : IsHalf (cA D e) w := hhalfR _ hu
  have hb : IsHalf (cA D e) b := hhalfR _ hu
  have hXa : IsHalf (cA D e) (d.extX T a) := hhalfR _ ha
  have hYb : IsHalf (cA D e) (d.extY T b) := hhalfR _ hb
  have h0w : IsHalf (cA D e) (d.ext0 T w) := hhalfR _ hw
  have hth : ∀ {g : WO S T → ℂ}, IsThetaFunO ψ S T g → ∀ v, IsThetaFunO ψ S T (heisO ψ S T v g) :=
    fun hg v => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg v
  set g₂ := heisO ψ S T (d.extY T b) f with hg₂
  set g₁ := heisO ψ S T (d.ext0 T w) g₂ with hg₁
  have hg₂t : IsThetaFunO ψ S T g₂ := hth hf _
  have hg₁t : IsThetaFunO ψ S T g₁ := hth hg₂t _
  have hsplit : heisO ψ S T u f = heisO ψ S T (d.extX T a) g₁ := by
    have hsum : IsHalf (cA D e) (d.ext0 T w + d.extY T b) := fun i j => by
      simp only [Matrix.add_apply, mul_add, h0w i j, hYb i j]
    rw [hu_eq, add_assoc, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (horth hXa hsum),
      GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (horth h0w hYb)]
  let v : VolM D T.rank ρ := ⟨μ, 𝓕, hμ⟩
  have key : ∀ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 (heisO ψ S T u f) x.1) = ℓ₀ (d.mixS T ψ μ 𝓕 f (x + ⟨a, (hH a).2 ha⟩).1) := by
    intro x
    have hx : IsHalf (cA D e) x.1 := (hH x.1).1 x.2
    have hxa : IsHalf (cA D e) (x.1 + a) := fun i j => by
      simp only [Matrix.add_apply, mul_add, hx i j, ha i j]
    obtain ⟨c1, -, -, -, -⟩ := GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v g₁ hg₁t
    obtain ⟨-, -, c3, -, -⟩ := GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v g₂ hg₂t
    obtain ⟨-, c2, -, -, -⟩ := GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v f hf
    have e1 : d.mixS T ψ μ 𝓕 (heisO ψ S T u f) x.1 = d.mixS T ψ μ 𝓕 g₁ (x.1 + a) := by
      rw [hsplit]; exact c1 x.1 a
    have e2 : d.mixS T ψ μ 𝓕 g₁ (x.1 + a) = heisO ψ S₀ T w (d.mixS T ψ μ 𝓕 g₂ (x.1 + a)) := c3 (x.1 + a) w
    have e3 : d.mixS T ψ μ 𝓕 g₂ (x.1 + a) = d.mixS T ψ μ 𝓕 f (x.1 + a) := by
      rw [hg₂, c2 (x.1 + a) b, horth (show IsHalf (cA D e) (d.extX T (x.1 + a)) from hhalfR _ hxa) hYb,
        AddChar.map_zero_eq_one, one_smul]
    have hmt : IsThetaFunO ψ S₀ T (d.mixS T ψ μ 𝓕 g₂ (x.1 + a)) :=
      GlobalTheory.MixValues.mixS_theta D ψ hψ S S₀ T ρ d μ 𝓕 hμ g₂ hg₂t (x.1 + a)
    rw [e1, e2, hℓ₀ w hw _ hmt, e3]
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  exact integral_translate ν (fun x : H => ℓ₀ (d.mixS T ψ μ 𝓕 f x.1)) _

end GlobalTheory.HalfInvariance
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntertwiningStabilizerTranslateScalar
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RegSch.IkStab

variable {D : D7}

def mulLeft {t : ℕ} (n : ℕ) (α : GL (Fin t) (AE D)) : Mx D t n ≃ₜ+ Mx D t n where
  toFun x := α.1 ⬝ x
  invFun x := (α⁻¹).1 ⬝ x
  left_inv x := by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  right_inv x := by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  map_add' x y := Matrix.mul_add _ _ _
  continuous_toFun := continuous_const.matrix_mul continuous_id
  continuous_invFun := continuous_const.matrix_mul continuous_id

theorem exists_valuation_adapted_index {T T' : HSp D} {t : ℕ} (d : HypDec T T' t) {p : GA D T} (hp : p ∈ stab d) :
    ∃ (β : Mx D t T'.rank) (g : GA D T'), mt T p ⬝ d.j0 = d.jX ⬝ β + d.j0 ⬝ mt T' g := by
  obtain ⟨α, hα⟩ := hp
  have hu := mt_unitary T p
  have h1 : adj (mt T p ⬝ d.jX) ⬝ (gA T ⬝ (mt T p ⬝ d.j0)) = 0 := by
    rw [adj_mul, Matrix.mul_assoc, cancel₃ hu, d.wittDecomp_gram_X_anisotropic]
  have h2 : d.pY ⬝ (mt T p ⬝ d.j0) = 0 := by
    rw [hα, adj_mul, Matrix.mul_assoc] at h1
    have h3 := congrArg (fun z : Mx D t T'.rank => adj (α⁻¹).1 ⬝ z) h1
    simp only [← Matrix.mul_assoc (adj (α⁻¹).1), ← adj_mul, Units.mul_inv, adj_one, Matrix.one_mul,
      Matrix.mul_zero] at h3
    rw [d.pY_eq, Matrix.mul_assoc, h3]
  have h4 : mt T p ⬝ d.j0 = d.jX ⬝ (d.pX ⬝ (mt T p ⬝ d.j0)) + d.j0 ⬝ (d.p0 ⬝ (mt T p ⬝ d.j0)) := by
    conv_lhs => rw [← Matrix.one_mul (mt T p ⬝ d.j0), ← d.sum_eq_one]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h2, Matrix.mul_zero, add_zero]
  have h5 : adj (mt T p ⬝ d.j0) ⬝ (gA T ⬝ (mt T p ⬝ d.j0)) = gA T' := by
    rw [adj_mul, Matrix.mul_assoc, cancel₃ hu, d.gram_00]
  generalize d.pX ⬝ (mt T p ⬝ d.j0) = β at h4
  generalize d.p0 ⬝ (mt T p ⬝ d.j0) = g at h4
  rw [h4] at h5
  simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, cancel₃ d.gram_XX,
    cancel₃ d.wittDecomp_gram_X_anisotropic, cancel₃ d.gram_0X, cancel₃ d.gram_00, Matrix.zero_mul, Matrix.mul_zero, zero_add,
    add_zero] at h5
  exact ⟨β, ofMat T' g h5, h4⟩

end GlobalTheory.RegSch.IkStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseRowFourierTransformMemSchwartzBruhatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseRowFourierTransform_mem_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψk : AddChar k Circle) (ν : Measure k), Continuous ψk → ψk ≠ 1 → ν.IsAddHaarMeasure → ∀ (C : ℂ) (Φ : Matrix Unit n k → ℂ), Φ ∈ SB (Matrix Unit n k) → GlobalTheory.KappaModel.finv ψk ν C Φ ∈ SB (Matrix n Unit k) := by
  first | exact @GlobalTheory.KappaModel.finv_mem_SB | exact GlobalTheory.KappaModel.finv_mem_SB | (intros; apply GlobalTheory.KappaModel.finv_mem_SB <;> assumption)
end

