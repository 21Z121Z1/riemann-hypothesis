import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpan
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0016
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0719
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0701
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0720
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0721
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SuccAboveCastSuccCastSucc
section
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeSM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem qminor_restrict {n m t : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (ι : Fin m → Fin n)
    (hι : Function.Injective ι) (a b : Fin t → Fin m) (w : ℂ) :
    qminor (fun a b => E (ι a) (ι b)) a b w = qminor E (ι ∘ a) (ι ∘ b) w := by
  unfold qminor Tm
  simp only [Function.comp, hι.eq_iff]

theorem tm_of_ne {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (w : ℂ) {a b : Fin n} (h : a ≠ b) :
    Tm E w a b = E a b := by
  unfold Tm
  simp [h]

theorem qdet_eq_qminor {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (r : Fin n → Fin n)
    (hr : Function.Bijective r) (u : ℂ) : qdet E u = qminor E r r u := by
  let τ : Equiv.Perm (Fin n) := Equiv.ofBijective r hr
  have e : r = id ∘ τ := rfl
  have h1 : qdet E u = qminor E id id u := by
    unfold qdet qminor Tm
    simp only [id]
  rw [h1, e, quantumMinorRowSkew_holds, quantumMinorColSkew_holds _ _ _ _ hE, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul,
    Int.units_mul_self]
  simp

theorem sign_apply (k : ℕ) (x : V) :
    ((((-1 : ℤ) ^ k : ℤ) : Module.End ℂ V)) x = ((-1 : ℂ) ^ k) • x := by
  rcases Nat.even_or_odd k with h | h <;> simp [h.neg_one_pow]

theorem succAbove_castSucc_last {N : ℕ} (c : Fin (N + 1)) :
    (Fin.castSucc c).succAbove (Fin.last N) = Fin.last (N + 1) := by
  exact Fin.succAbove_of_le_castSucc _ _ (by
    simpa [Fin.le_def] using Nat.lt_succ_iff.1 c.isLt) |>.trans (by simp)

theorem succAbove_castSucc_castSucc {N : ℕ} (c : Fin (N + 1)) (j : Fin N) :
    (Fin.castSucc c).succAbove (Fin.castSucc j) = Fin.castSucc (c.succAbove j) := by
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp_all

theorem algId : PositivityTheory.RgHe.SM.AlgId := by
  intro V _ _ N E ι z hE hι hz u v
  let r : Fin (N + 2) → Fin (N + 2) := Fin.snoc (α := fun _ => Fin (N + 2)) ι z
  have rc : ∀ a, r (Fin.castSucc a) = ι a := fun a => by simp [r]
  have rl : r (Fin.last (N + 1)) = z := by simp [r]
  have hinj : Function.Injective r := by
    intro a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => intro _; rfl
      | cast b => rw [rl, rc]; exact fun h => absurd h.symm (hz b)
    | cast a =>
      induction b using Fin.lastCases with
      | last => rw [rl, rc]; exact fun h => absurd h (hz a)
      | cast b => rw [rc, rc]; exact fun h => by rw [hι h]
  have hr : Function.Bijective r := Finite.injective_iff_bijective.1 hinj
  have hrc : r ∘ Fin.castSucc = ι := funext rc
  have hcol : ∀ c : Fin (N + 1), qminor E ι (r ∘ (Fin.castSucc c).succAbove) (u - 1) =
      ∑ l : Fin (N + 1), (((-1 : ℤ) ^ (N + (l : ℕ)) : ℤ) : Module.End ℂ V) *
        (qminor E (ι ∘ l.succAbove) (ι ∘ c.succAbove) (u - 1) * E (ι l) z) := by
    intro c
    rw [quantum_minor_column_expansion.2 (Module.End ℂ V) (N + 2) N E ι (r ∘ (Fin.castSucc c).succAbove) (u - 1)]
    refine Finset.sum_congr rfl fun l _ => ?_
    have h1 : (r ∘ (Fin.castSucc c).succAbove) ∘ Fin.castSucc = ι ∘ c.succAbove := by
      funext j
      simp [succAbove_castSucc_castSucc, rc]
    have h2 : (r ∘ (Fin.castSucc c).succAbove) (Fin.last N) = z := by
      simp [succAbove_castSucc_last, rl]
    rw [h1, h2, tm_of_ne E _ (hz l)]
  rw [qdet_eq_qminor E hE r hr u, quantum_minor_row_expansion.2 (Module.End ℂ V) (N + 2) (N + 1) E hE r r u,
    Fin.sum_univ_castSucc, hrc, rl, LinearMap.add_apply, LinearMap.sum_apply]
  have hlast : (((-1 : ℤ) ^ (N + 1 + ((Fin.last (N + 1) : Fin (N + 2)) : ℕ)) : ℤ) : Module.End ℂ V) *
      (qminor E ι (r ∘ (Fin.last (N + 1)).succAbove) (u - 1) * Tm E u z z) =
      qminor E ι ι (u - 1) * Tm E u z z := by
    have : r ∘ (Fin.last (N + 1)).succAbove = ι := by
      rw [Fin.succAbove_last]; exact hrc
    rw [this, Fin.val_last, ← two_mul, pow_mul]
    simp
  have hq : qdet (fun a b => E (ι a) (ι b)) (u - 1) = qminor E ι ι (u - 1) := by
    unfold qdet qminor Tm
    simp only [id, hι.eq_iff]
  rw [hlast, hq, Module.End.mul_apply, add_comm, sub_eq_add_neg ((qminor E ι ι (u - 1)) _), ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [rc, tm_of_ne E _ (hz c).symm, hcol c, Th_apply, Module.End.mul_apply, sign_apply, Module.End.mul_apply,
    LinearMap.sum_apply, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Module.End.mul_apply, sign_apply, Module.End.mul_apply, qminor_restrict E ι hι, smul_smul, ← neg_smul]
  congr 1
  have : ((-1 : ℂ) ^ N) * (-1 : ℂ) ^ N = 1 := by rw [← mul_pow]; simp
  simp only [Fin.val_castSucc, pow_add, pow_one]
  linear_combination (-(-1 : ℂ) ^ (l : ℕ) * (-1 : ℂ) ^ (c : ℕ)) * this

end GlobalTheory.CompanionTheory.RgHeSM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportInducedFunctionClosedStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_induced_function_closed : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q : Subgroup G} (σ : Representation ℂ Q W₁) (f : smoothPart (ind Q σ)), IsClosed {g : G | f.1.1 g ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.isClosed_support_smooth_ind | exact GlobalTheory.CompanionTheory.BZRes.isClosed_support_smooth_ind | (intros; apply GlobalTheory.CompanionTheory.BZRes.isClosed_support_smooth_ind <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveIntertwinerQuotientEquivStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_intertwiner_quotient_equiv : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (τ : Representation ℂ G W) (R : ρ.IntertwiningMap τ), Function.Surjective R → ∃ S : Subrepresentation ρ, S.toSubmodule = LinearMap.ker R.toLinearMap ∧ Nonempty ((subQuot ⊤ S).Equiv τ) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv | exact GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv | (intros; apply GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaRapidDecaySiegelSetStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_rapid_decay_siegel_set : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ {c : ℝ}, 0 < c → ∀ (L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E))), IsCompact L → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ C : ℝ, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ (invPt V a ξ) i 0‖) ^ N)⁻¹ * Set.indicator L (fun _ => (1 : ℝ)) ((invPt V a ξ).map (finPart D))) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (2 * Module.finrank ℚ D.host.F)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilCount.count_main | exact GlobalTheory.CompanionTheory.WeilCount.count_main | (intros; apply GlobalTheory.CompanionTheory.WeilCount.count_main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryKTypeFiniteStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_K_type_finite : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : GL (Fin a) (Cinf E) →* (H →L[ℂ] H)), IsUnitaryRep σ → IsTopIrreducible σ → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), FiniteDimensional ℂ ↥(⨆ (T : W →ₗ[ℂ] H) (_ : ∀ k w, T (ρ k w) = σ (Unitary.toUnits k) (T w)), LinearMap.range T : Submodule ℂ H) := by
  first | exact @GlobalTheory.CompanionTheory.AdmGL.admissible_GL_Cinf | exact GlobalTheory.CompanionTheory.AdmGL.admissible_GL_Cinf | (intros; apply GlobalTheory.CompanionTheory.AdmGL.admissible_GL_Cinf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursProductInterleaveStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_occurs_product_interleave : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (x y : IrrGL k) (u v w : List (IrrGL k)), (∀ c ∈ u, c.IsCusp) → (∀ c ∈ v, c.IsCusp) → Wd x.rep u → Wd y.rep v → Zc.Comb.Interleave u v w → Wd (prod₂ x.rep y.rep) w := by
  first | exact @GlobalTheory.CompanionTheory.WordProd.wd_prod₂_of_interleave | exact GlobalTheory.CompanionTheory.WordProd.wd_prod₂_of_interleave | (intros; apply GlobalTheory.CompanionTheory.WordProd.wd_prod₂_of_interleave <;> assumption)
end

