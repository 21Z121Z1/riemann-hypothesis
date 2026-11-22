import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0808
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0790
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0780
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0649
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0387
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0393
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0485

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleDualPeriodAlgebraicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_triangle_dual_period_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  first | exact @GlobalTheory.BotAlgI'.classSums'_algebraic | exact GlobalTheory.BotAlgI'.classSums'_algebraic | (intros; apply GlobalTheory.BotAlgI'.classSums'_algebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTrianglePeriodAlgebraic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.BotAlgI

theorem ker_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ dg : D.what₂.Tau →₀ ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (t : T), ∀ x ∈ GfC A, ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A.rank →₀ ℕ,
      Finsupp.mapDomain Prod.fst k = dg → IsAlgebraic ℚ (X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h x / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX dg
  obtain ⟨Ω, hΩ, hjet⟩ := GlobalTheory.T.period_algebraic_fixed_degree hP hI hL hX dg
  refine ⟨Ω, hΩ, fun t x hx h hh k hk => ?_⟩
  obtain ⟨n, c, w, hc, hw, hf⟩ := GlobalTheory.T.theta_kernel_algebraic_expansion hP hI hL hX t
  choose n' c' w' hc' hw' hm using fun p => GlobalTheory.T.finite_adelic_algebraic_expansion hP hI hL hX t x hx h hh (w p) (hw p)
  have hψ := hX.is.isVac.1
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hv : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW X.vac := hX.is.isVac.2.theta
  set φ : PolF D WW.rank A.rank := MvPolynomial.monomial k 1 with hφ
  set pt : (WO (GlobalTheory.Grid.neg A) WW → ℂ) → (WO (GlobalTheory.Grid.neg A) WW → ℂ) := fun f =>
    pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B f φ with hpt
  have comb : ∀ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, (y p).map (infPart D) = 0) →
      pt (∑ p, a p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) X.vac) =
        ∑ p, a p • pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) X.vac) := fun n a y hy => by
    have h1 := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (GlobalTheory.Grid.neg A) WW hψ hθ (fun τ => -X.rA.s τ) X.rW.s
      X.rA.B X.rW.B X.vac hv n a y hy φ).1
    have h2 : ∀ p, heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) (pt X.vac) = pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) X.vac) :=
      fun p => by
        have := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (GlobalTheory.Grid.neg A) WW hψ hθ (fun τ => -X.rA.s τ) X.rW.s
          X.rA.B X.rW.B X.vac hv 1 (fun _ => 1) (fun _ => y p) (fun _ => hy p) φ).1
        simpa using this
    simp only [← h2]
    exact h1.symm
  have e1 : ∀ g, ((X.ω t).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm x, h) g = X.ω t (x, h) g := fun g => rfl
  have move : ∀ g, IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW g → X.ω t (x, h) (pt g) = pt (X.ω t (x, h) g) := fun g hg => by
    rw [← e1, ← e1]
    exact GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ (hX.is.weil t) W.θ hθ ((GlobalTheory.Grid.ofSgn true A).symm x) hx h hh
      (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B g φ hg
  have hval : X.ker W.ψ W.θ t φ h x / Ω =
      ∑ p, c p * ∑ q, c' p q * (pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w' p q) X.vac) 0 / Ω) := by
    have e2 : X.ker W.ψ W.θ t φ h x = X.ω t (x, h) (pt (X.f t)) 0 := rfl
    have e3 : ∀ p, X.ω t (x, h) (pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac)) =
        ∑ q, c' p q • pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w' p q) X.vac) := fun p => by
      rw [move _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv _), hm p, comb _ _ _ (hw' p)]
    rw [e2, hf, comb _ _ _ hw, map_sum]
    simp only [map_smul, e3, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_div, Finset.mul_sum, mul_div_assoc]
  rw [hval, ← mem_algebraicClosure_iff]
  refine sum_mem fun p _ => mul_mem (mem_algebraicClosure_iff.2 (hc p)) (sum_mem fun q _ => mul_mem
    (mem_algebraicClosure_iff.2 (hc' p q)) (mem_algebraicClosure_iff.2 (hjet _ (hw' p q) k hk)))

theorem classSums_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  obtain ⟨v, N, z, w, κ, hv, hz, hw, hκ1, hκ2, hcls⟩ := GlobalTheory.T.exists_weighted_average_haar hP hI hL hX
  obtain ⟨dg, hproj⟩ := GlobalTheory.T.exists_fourier_degree_bound hP hI hL hX
  obtain ⟨Ω, hΩ, hdict⟩ := ker_algebraic hP hI hL hX dg
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  refine ⟨(v : ℂ) * Ω, mul_ne_zero hv' hΩ, fun t h hh k => ?_⟩
  choose m r U hr hU heq using fun l => hproj κ hκ1 hκ2 t (z l) (hz l) h hh k
  have hval : X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h / ((v : ℂ) * Ω) =
      ∑ l, ((w l : ℂ))⁻¹ * ∑ p, r l p * (X.ker W.ψ W.θ t (MvPolynomial.monomial (U l p) 1) h (z l) / Ω) := by
    rw [hcls t _ h hh]
    simp only [heq, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro p _
    field_simp
  rw [hval, ← mem_algebraicClosure_iff]
  refine sum_mem fun l _ => mul_mem (inv_mem ?_) (sum_mem fun p _ => mul_mem ?_ ?_)
  · rw [mem_algebraicClosure_iff]
    simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) ((w l : ℚ)))
  · rw [mem_algebraicClosure_iff]; exact hr l p
  · rw [mem_algebraicClosure_iff]; exact hdict t (z l) (hz l) h hh (U l p) (hU l p)

end GlobalTheory.BotAlgI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPlacesEmbeddingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_places_embedding : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ v ∉ S, Nonempty (E →ₐ[F] Fv F v) →
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v) := by
  first | exact @GlobalTheory.SplitSphLeft.vac_fixed_split_left | exact GlobalTheory.SplitSphLeft.vac_fixed_split_left | (intros; apply GlobalTheory.SplitSphLeft.vac_fixed_split_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorsRowAndColumnPaths
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainHyp

open GlobalTheory.FunObj GlobalTheory.RowChain GlobalTheory.FlipRun GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf

variable {T : Type}

theorem splitFam_zip {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z) (d : (p.comp q).Fam S) (e : (p.comp q).Fam S'),
      splitFam q (Path.Fam.zip φ d e) =
        (Path.Fam.zip φ (splitFam q d).1 (splitFam q e).1, Path.Fam.zip φ (splitFam q d).2 (splitFam q e).2)
  | _, .nil, _, _ => rfl
  | _, .snoc _ q, d, e => by
    show ((splitFam q (Path.Fam.zip φ d.1 e.1)).1, ((splitFam q (Path.Fam.zip φ d.1 e.1)).2, φ _ d.2 e.2)) = _
    rw [splitFam_zip φ q d.1 e.1]
    rfl

theorem getD_zip {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) (t : T) (i : ℕ) :
    ∀ (n : ℕ) (d : (downPath t i n).Fam S) (e : (downPath t i n).Fam S') (j : ℕ) (h : j < n),
      getD t i n (Path.Fam.zip φ d e) j h = φ _ (getD t i n d j h) (getD t i n e j h)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, d, e, j, h => by
    have hs : splitFam (p := Path.one (.down t i n)) (downPath t i n)
        (Path.Fam.zip (p := downPath t i (n + 1)) φ d e) =
        (Path.Fam.zip φ (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).1
          (splitFam (p := Path.one (.down t i n)) (downPath t i n) e).1,
         Path.Fam.zip φ (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).2
          (splitFam (p := Path.one (.down t i n)) (downPath t i n) e).2) :=
      splitFam_zip φ (p := Path.one (.down t i n)) (downPath t i n) d e
    unfold getD
    split_ifs with hj
    · rw [hs]
      exact getD_zip φ t i n _ _ j hj
    · obtain rfl : n = j := by omega
      rw [hs]
      rfl

variable {D : D7} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem vecAll_iff {W : G.Weil} (ρ : RealMatch W) (e : AE D) {X : Node} :
    ∀ {Y : Node} (p : Path T X Y) (φ f : PureT G p), VecAll ρ e p φ f ↔
      Path.Fam.All (fun a (x : Sch G a × Sch G a) => IsLocVec W a.pair e (vacOf ρ a) x.1 x.2)
        (Path.Fam.zip (fun _ u v => (u, v)) φ f)
  | _, .nil, _, _ => Iff.rfl
  | _, .snoc _ p, φ, f => and_congr_left' (vecAll_iff ρ e p φ.1 f.1)

theorem getD_loc {W : G.Weil} (ρ : RealMatch W) (e : AE D) (t : T) (i n : ℕ) (φ f : PureT G (downPath t i n))
    (h : VecAll ρ e (downPath t i n) φ f) (j : ℕ) (hj : j < n) :
    IsLocVec W (Arrow.down t i j).pair e (vacOf ρ (.down t i j)) (getD t i n φ j hj) (getD t i n f j hj) := by
  have := getD_all (fun a (x : Sch G a × Sch G a) => IsLocVec W a.pair e (vacOf ρ a) x.1 x.2) t i n _
    ((vecAll_iff ρ e _ φ f).1 h) j hj
  rwa [getD_zip] at this

theorem row_cusp {W : G.Weil} {M : Vol G} {ρ : RealMatch W} {t : T} (hS : CuspStep W M ρ t) {e : AE D}
    (he : IsIdemSum e (locPl G t)) {F : Fn G (.grid 0 D.R.m)} (hF : IsCuspListed W.θ (.grid 0 D.R.m) F) :
    ∀ n, n ≤ D.R.m → ∀ (φ d : PureT G (rowPath T D.R.m n)) (P : PolT G (rowPath T D.R.m n)),
      VecAll ρ e (rowPath T D.R.m n) φ d →
      IsCuspListed W.θ (.grid n D.R.m)
        (liftP W M (rowPath T D.R.m n) (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) F)
  | 0, _, _, _, _, _ => hF
  | n + 1, hn, φ, d, P, h =>
    (hS (.right n D.R.m) (Or.inl ⟨n, D.R.m, by omega, le_rfl, rfl⟩) e he φ.2 d.2 h.2 P.2 _
      (row_cusp hS he hF n (by omega) φ.1 d.1 P.1 h.1)).2

theorem step_cusp (G : GridData L sc) (Wl : G.Weil) (t : T) {M : Vol G} (hM : M.Is t) {θ : InfFam D} (j : ℕ)
    (hj : j + 1 ≤ D.R.m) {V₀ W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec (G.V (.grid D.R.m j)) V₀ ρ)
    (dW : HypDec (G.V (.grid D.R.m (j + 1))) W₀ σ) (Φ : Sch G (.down t D.R.m j)) (F : Fn G (.grid D.R.m (j + 1)))
    (h : IsCuspListed θ (.grid D.R.m j) (liftA Wl M (.down t D.R.m j) Φ F)) :
    IsCuspListed θ (.grid D.R.m j) ((stepAt G Wl t hM j hj dV dW).lift F Φ) := h

end GlobalTheory.ChainHyp

namespace GlobalTheory.ChainHyp

open GlobalTheory.FunObj GlobalTheory.RowChain GlobalTheory.RowUnf GlobalTheory.FlipRun GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf

variable {T : Type} {D : D7} {L : LevCh D T} {sc : Consts}

theorem last_cusp (G : GridData L sc) (Wl : G.Weil) (t : T) (M : Vol G) {θ : InfFam D} (j : ℕ)
    (f : Sch G (.down t D.R.m (j + 1)))
    (H : ∀ F' : Fn G (.grid D.R.m (j + 1 + 1)), IsCuspListed θ (.grid D.R.m (j + 1 + 1)) F' →
      IsCuspListed θ (.grid D.R.m (j + 1)) (liftA Wl M (.down t D.R.m (j + 1)) f F')) :
    ∀ (n : ℕ) (h : j + 1 + 1 = n) (F : Fn G (.grid D.R.m n)), IsCuspListed θ (.grid D.R.m n) F →
      IsCuspListed θ (.grid D.R.m (j + 1))
        (liftS (castOm G h (Wl.om (.mu t D.R.m (j + 1)))) (M.ν (.grid D.R.m n)) (M.fd (.grid D.R.m n)) F (castSch G h f)) := by
  intro n h
  subst h
  exact H

theorem chain_props (hP : GlobalTheory.Published.CuspRapidDecay) (G : GridData L sc) (Wl : G.Weil) (hθ : IsInfFam Wl.θ) (t : T)
    {M : Vol G} (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsCuspListed Wl.θ (.grid D.R.m D.R.m) F)
    (hst : ∀ k (hk : k < D.R.m) (F' : Fn G (.grid D.R.m (k + 1))), IsCuspListed Wl.θ (.grid D.R.m (k + 1)) F' →
      IsCuspListed Wl.θ (.grid D.R.m k) (liftA Wl M (.down t D.R.m k) (getD t D.R.m D.R.m d k hk) F')) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)),
      IsCuspListed Wl.θ (.grid D.R.m j) ((chainFrom G Wl t hM σ j hj vN).down (dataFrom G Wl t hM d σ j hj vN) F) ∧
      (chainFrom G Wl t hM σ j hj vN).Rapid (dataFrom G Wl t hM d σ j hj vN) F
  | 0, j, hj, vN => by
    refine ⟨?_, trivial⟩
    exact step_cusp G Wl t hM j (by omega) (besDecAt G j 0 hj) (rowJac G (j + 1) (by omega) 0 (by omega)) _ _ (hst j (by omega) _
      (last_cusp G Wl t M j _ (hst (j + 1) (by omega)) D.R.m (by omega) F hF))
  | σ + 1, j, hj, vN => by
    obtain ⟨h1, h2⟩ := chain_props hP G Wl hθ t hM d F hF hst σ (j + 1 + 1) (by omega)
      (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have h3 := step_cusp G Wl t hM (j + 1) (by omega)
      (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
      (getD t D.R.m D.R.m d (j + 1) (by omega)) _ (hst (j + 1) (by omega) _ h1)
    refine ⟨step_cusp G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) _ _
      (hst j (by omega) _ h3), ?_⟩
    exact ⟨rapidDec_of_cuspForm hP hθ h3.1 h3.2.1, rapidDec_of_cuspForm hP hθ h1.1 h1.2.1, h2⟩

end GlobalTheory.ChainHyp

namespace GlobalTheory.ChainHyp

open GlobalTheory.FunObj GlobalTheory.RowChain GlobalTheory.FlipRun GlobalTheory.Grow

end GlobalTheory.ChainHyp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceHorizontalThetaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.path_convergence_horizontal_theta : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (Φ : ch.G.Datum) (M : Vol ch.G), M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = liftP ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) := by
  first | exact @GlobalTheory.RowStart.rowStart | exact GlobalTheory.RowStart.rowStart | (intros; apply GlobalTheory.RowStart.rowStart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRepresentationTriple
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.RealQuot

theorem realQuot : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
    ∃ (Pr : ModuleCat.{0} ℂ) (ρ : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pr)
      (q : PolF D X.rank W.rank →ₗ[ℂ] Pr) (q' : PolF D X.rank W₁.rank →ₗ[ℂ] Pr),
      Function.Surjective q ∧ Function.Surjective q' ∧ Module.rank ℂ Pr ≤ Cardinal.aleph0 ∧
      (∀ N : Submodule ℂ Pr, (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ N, ρ τ Y x ∈ N) → N = ⊥ ∨ N = ⊤) ∧
      ∀ α β, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
        ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
          (∀ f, IsFinF ψ θ true A B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p (fockF ψ θ true A B f P) = φ (q P)) ∧
          ∀ f, IsFinF ψ θ false A₁ B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p' (fockF ψ θ false A₁ B f P) = φ (q' P) := by
  intro hH hP _ _ D ψ θ hψ hθ W W₁ X A A₁ B a b
  classical
  let ρA : LieIx X → Module.End ℂ (PolF D X.rank W.rank) := fun i => actT true A B b i.1.1 i.1.2
  let CA := coinv true A B (fun τ => b τ - a τ)
  let ρB : LieIx X → Module.End ℂ (PolF D X.rank W₁.rank) := fun i => actT false A₁ B a i.1.1 i.1.2
  let CB := coinv false A₁ B (fun τ => a τ - b τ)

  have fam : ∀ α β, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
      let σ : LieIx X → Module.End ℂ Pi := fun i => rl i.1.1 i.1.2
      let βA : {f // IsFinF ψ θ true A B f} → PolF D X.rank W.rank →ₗ[ℂ] Pi := fun f => p ∘ₗ fockF ψ θ true A B f.1
      let βB : {f // IsFinF ψ θ false A₁ B f} → PolF D X.rank W₁.rank →ₗ[ℂ] Pi := fun f => p' ∘ₗ fockF ψ θ false A₁ B f.1
      ((∀ f i, βA f ∘ₗ ρA i = σ i ∘ₗ βA f) ∧ (∀ f, CA ≤ LinearMap.ker (βA f)) ∧
        (∀ (j : {h // h ∈ GfC X}) f, ∃ f', rf j.1 ∘ₗ βA f = βA f') ∧ (⨆ f, LinearMap.range (βA f)) = ⊤) ∧
      ((∀ f i, βB f ∘ₗ ρB i = σ i ∘ₗ βB f) ∧ (∀ f, CB ≤ LinearMap.ker (βB f)) ∧
        (∀ (j : {h // h ∈ GfC X}) f, ∃ f', rf j.1 ∘ₗ βB f = βB f') ∧ (⨆ f, LinearMap.range (βB f)) = ⊤) ∧
      (∀ N : Submodule ℂ Pi, IsStab σ N → IsStab (fun j : {h // h ∈ GfC X} => rf j.1) N → N = ⊥ ∨ N = ⊤) ∧
      HoweCond ρA CA ∧ HoweCond ρB CB ∧ Nontrivial Pi := by
    intro α β htr hexp ωA ωB Pi rf rl p p' hm
    have hexpA : ∀ τ, HasInfExp D β τ (b τ) ∧ HasInfExp D (β / α) τ (b τ - a τ) :=
      fun τ => ⟨(hexp τ).2, hasInfExp_div D α β τ _ _ (hexp τ).1 (hexp τ).2⟩
    have hexpB : ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D (α / β) τ (a τ - b τ) :=
      fun τ => ⟨(hexp τ).1, hasInfExp_div D β α τ _ _ (hexp τ).2 (hexp τ).1⟩
    obtain ⟨oA1, oA2, oA3⟩ := GlobalTheory.T.orientedPair_fockMaps_lie_equivariant D ψ θ hθ true W X A B β (β / α) ωA b (fun τ => b τ - a τ) hm.weilA hexpA Pi rf rl p hm.mapA
    obtain ⟨oB1, oB2, oB3⟩ := GlobalTheory.T.orientedPair_fockMaps_lie_equivariant D ψ θ hθ false W₁ X A₁ B α (α / β) ωB a (fun τ => a τ - b τ) hm.weilB hexpB Pi rf rl p' hm.mapB
    have hspan : ∀ {M : HSp D} {ε : Bool} {A' : Fr M} (pp : (WO M X → ℂ) →ₗ[ℂ] Pi), (algF ψ θ ε A' B).map pp = ⊤ →
        (⨆ f : {f // IsFinF ψ θ ε A' B f}, LinearMap.range (pp ∘ₗ fockF ψ θ ε A' B f.1)) = ⊤ := by
      intro M ε A' pp h
      rw [eq_top_iff, ← h, algF, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨f, P, hf, rfl⟩, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨f, hf⟩ ⟨P, rfl⟩
    refine ⟨⟨fun f i => LinearMap.ext fun P => oA1 f.1 f.2 i.1.1 i.1.2 i.2 P,
        fun f P hP => oA2 f.1 f.2 P hP, fun j f => ?_, hspan p hm.mapA.onto⟩,
      ⟨fun f i => LinearMap.ext fun P => oB1 f.1 f.2 i.1.1 i.1.2 i.2 P,
        fun f P hP => oB2 f.1 f.2 P hP, fun j f => ?_, hspan p' hm.mapB.onto⟩,
      fun N h1 h2 => hm.irred.2 N (fun g hg x hx => h2 ⟨g, hg⟩ x hx) (fun τ Y hY x hx => h1 ⟨(τ, Y), hY⟩ x hx),
      GlobalTheory.T.howe_condition_of_weil hH hP D ψ θ hψ hθ true W X A B β (β / α) ωA b _ hm.weilA hexpA,
      GlobalTheory.T.howe_condition_of_weil hH hP D ψ θ hψ hθ false W₁ X A₁ B α (α / β) ωB a _ hm.weilB hexpB, hm.irred.1⟩
    · obtain ⟨f', hf', e⟩ := oA3 j.1 j.2 f.1 f.2
      exact ⟨⟨f', hf'⟩, LinearMap.ext fun P => e P⟩
    · obtain ⟨f', hf', e⟩ := oB3 j.1 j.2 f.1 f.2
      exact ⟨⟨f', hf'⟩, LinearMap.ext fun P => e P⟩

  by_cases hex : ∃ α β, IsTriple W W₁ X α β ∧ (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) ∧
      ∃ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p'
  swap
  · refine ⟨ModuleCat.of ℂ PUnit, fun _ _ => 0, 0, 0, fun _ => ⟨0, Subsingleton.elim _ _⟩,
      fun _ => ⟨0, Subsingleton.elim _ _⟩, ?_, fun N _ => Or.inl (Submodule.eq_bot_of_subsingleton), ?_⟩
    · show Module.rank ℂ PUnit ≤ _
      simp
    · intro α β htr hexp ωA ωB Pi rf rl p p' hm
      exact absurd ⟨α, β, htr, hexp, ωA, ωB, Pi, rf, rl, p, p', hm⟩ hex
  obtain ⟨α₀, β₀, htr₀, hexp₀, ωA₀, ωB₀, Pi₀, rf₀, rl₀, p₀, p₀', hm₀⟩ := hex
  obtain ⟨⟨iA, kA, cA, sA⟩, ⟨iB, kB, cB, sB⟩, irr₀, hHA, hHB, hnt⟩ := fam α₀ β₀ htr₀ hexp₀ ωA₀ ωB₀ Pi₀ rf₀ rl₀ p₀ p₀' hm₀
  set σ₀ : LieIx X → Module.End ℂ Pi₀ := fun i => rl₀ i.1.1 i.1.2

  have nz : ∀ {Fm Q : Type} [AddCommGroup Q] [Module ℂ Q] (β : Fm → Q →ₗ[ℂ] Pi₀), (⨆ f, LinearMap.range (β f)) = ⊤ →
      ∃ f, β f ≠ 0 := by
    intro Fm Q _ _ β h
    by_contra hc
    push_neg at hc
    have : (⊤ : Submodule ℂ Pi₀) = ⊥ := by
      rw [← h]; exact iSup_eq_bot.2 fun f => by rw [hc f, LinearMap.range_zero]
    exact bot_ne_top this.symm

  have wit : ∀ {Q : Type} [AddCommGroup Q] [Module ℂ Q] (ρ : LieIx X → Module.End ℂ Q) (C : Submodule ℂ Q)
      (β : Q →ₗ[ℂ] Pi₀), (∀ i, β ∘ₗ ρ i = σ₀ i ∘ₗ β) → C ≤ LinearMap.ker β → β ≠ 0 →
      IsStab ρ (LinearMap.ker β) ∧ C ≤ LinearMap.ker β ∧ LinearMap.ker β ≠ ⊤ := by
    intro Q _ _ ρ C β hi hk hne
    refine ⟨fun i x hx => ?_, hk, fun h => hne (LinearMap.ker_eq_top.1 h)⟩
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply, hx, map_zero]
  obtain ⟨fA, hfA⟩ := nz _ sA
  obtain ⟨fB, hfB⟩ := nz _ sB
  obtain ⟨wA1, wA2, wA3⟩ := wit ρA CA _ (iA fA) (kA fA) hfA
  obtain ⟨wB1, wB2, wB3⟩ := wit ρB CB _ (iB fB) (kB fB) hfB
  have radA : rad ρA CA ≠ ⊤ := rad_ne_top _ _ ρA CA _ hHA wA1 wA2 wA3
  have radB : rad ρB CB ≠ ⊤ := rad_ne_top _ _ ρB CB _ hHB wB1 wB2 wB3
  have CleA : CA ≤ rad ρA CA := wA2.trans (le_sSup ⟨wA1, wA2, wA3⟩)
  have CleB : CB ≤ rad ρB CB := wB2.trans (le_sSup ⟨wB1, wB2, wB3⟩)
  have simA : ∀ N, IsStab ρA N → rad ρA CA ≤ N → N = rad ρA CA ∨ N = ⊤ := by
    intro N h1 h2
    by_cases h : N = ⊤
    · exact Or.inr h
    · exact Or.inl (le_antisymm (le_sSup ⟨h1, CleA.trans h2, h⟩) h2)
  have simB : ∀ N, IsStab ρB N → rad ρB CB ≤ N → N = rad ρB CB ∨ N = ⊤ := by
    intro N h1 h2
    by_cases h : N = ⊤
    · exact Or.inr h
    · exact Or.inl (le_antisymm (le_sSup ⟨h1, CleB.trans h2, h⟩) h2)
  have ss₀ := GlobalTheory.T.exists_stable_complement_of_irreducible_span_intertwiners _ _ _ _ _ ρA CA σ₀ (fun j : {h // h ∈ GfC X} => rf₀ j.1) _ hHA iA kA cA sA irr₀
  have killA₀ : ∀ f, rad ρA CA ≤ LinearMap.ker _ := fun f => rad_le_ker _ _ _ ρA CA σ₀ _ (iA f) (kA f) radA ss₀
  have killB₀ := rad_le_ker _ _ _ ρB CB σ₀ _ (iB fB) (kB fB) radB ss₀
  obtain ⟨e, he⟩ := GlobalTheory.T.simple_quotients_iso_of_intertwined_semisimple _ _ _ _ _ ρA CA ρB CB σ₀ _ _ iA (iB fB) killA₀ killB₀ hfB sA simA simB ss₀

  let R := rad ρA CA
  let RB := rad ρB CB
  refine ⟨ModuleCat.of ℂ (PolF D X.rank W.rank ⧸ R),
    fun τ Y => if h : Y ∈ lieAt X τ then radAct ρA CA ⟨(τ, Y), h⟩ else 0,
    R.mkQ, e.symm.toLinearMap ∘ₗ RB.mkQ, R.mkQ_surjective, e.symm.surjective.comp RB.mkQ_surjective, ?_, ?_, ?_⟩
  · show Module.rank ℂ (PolF D X.rank W.rank ⧸ R) ≤ _
    refine (rank_quotient_le R).trans ?_
    rw [← (MvPolynomial.basisMonomials (FVar D X.rank W.rank) ℂ).mk_eq_rank'']
    exact Cardinal.mk_le_aleph0
  · intro N hN
    have hst : IsStab ρA (N.comap R.mkQ) := fun i x hx => by
      have h1 := hN i.1.1 i.1.2 i.2 _ hx
      simp only [dif_pos i.2] at h1
      exact h1
    have hle : R ≤ N.comap R.mkQ := fun x hx => by
      show R.mkQ x ∈ N
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero R).2 hx]
      exact N.zero_mem
    rcases simA _ hst hle with h | h
    · left
      rw [← Submodule.map_comap_eq_of_surjective R.mkQ_surjective N, h, Submodule.mkQ_map_self]
    · right
      rw [← Submodule.map_comap_eq_of_surjective R.mkQ_surjective N, h, Submodule.map_top, Submodule.range_mkQ]
  · intro α β htr hexp ωA ωB Pi rf rl p p' hm
    obtain ⟨⟨iA', kA', cA', sA'⟩, ⟨iB', kB', cB', sB'⟩, irr', -, -, -⟩ := fam α β htr hexp ωA ωB Pi rf rl p p' hm
    have ss' := GlobalTheory.T.exists_stable_complement_of_irreducible_span_intertwiners _ _ _ _ _ ρA CA (fun i : LieIx X => rl i.1.1 i.1.2) (fun j : {h // h ∈ GfC X} => rf j.1) _ hHA
      iA' kA' cA' sA' irr'
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · have hk := rad_le_ker _ _ _ ρA CA _ _ (iA' ⟨f, hf⟩) (kA' ⟨f, hf⟩) radA ss'
      refine ⟨R.liftQ (p ∘ₗ fockF ψ θ true A B f) hk, fun τ Y hY => ?_, fun P => rfl⟩
      simp only [dif_pos hY]
      refine Submodule.linearMap_qext _ (LinearMap.ext fun P => ?_)
      exact LinearMap.congr_fun (iA' ⟨f, hf⟩ ⟨(τ, Y), hY⟩) P
    · have hk := rad_le_ker _ _ _ ρB CB _ _ (iB' ⟨f, hf⟩) (kB' ⟨f, hf⟩) radB ss'
      refine ⟨RB.liftQ (p' ∘ₗ fockF ψ θ false A₁ B f) hk ∘ₗ e.toLinearMap, fun τ Y hY => ?_, fun P => ?_⟩
      · simp only [dif_pos hY]
        refine LinearMap.ext fun x => ?_
        have h1 := LinearMap.congr_fun (he ⟨(τ, Y), hY⟩) x
        simp only [LinearMap.comp_apply] at h1 ⊢
        rw [h1]
        have key : ∀ y, RB.liftQ (p' ∘ₗ fockF ψ θ false A₁ B f) hk (radAct ρB CB ⟨(τ, Y), hY⟩ y) =
            rl τ Y (RB.liftQ (p' ∘ₗ fockF ψ θ false A₁ B f) hk y) := by
          intro y
          obtain ⟨P, rfl⟩ := RB.mkQ_surjective y
          exact LinearMap.congr_fun (iB' ⟨f, hf⟩ ⟨(τ, Y), hY⟩) P
        exact key _
      · simp

end GlobalTheory.RealQuot

end
end

