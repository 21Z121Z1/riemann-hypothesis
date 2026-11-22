import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0257
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0420
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselVertexLatticeSplitsAlongWitt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.MonoBes

variable {D : D7}

theorem colMul_pX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (y : Fin S.rank → AE D) :
    GlobalTheory.FinPl.colMul d.jX i ((d.pX *ᵥ y) i) = rat (fun k l => d.e k i * d.qX i l) *ᵥ y := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, HypDec.jX, HypDec.pX, rat, mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  show (incA D) (d.qX i l) * y l * (incA D) (d.e k i) = (incA D) (d.e k i * d.qX i l) * y l
  rw [map_mul]
  ring

theorem colMul_pY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (y : Fin S.rank → AE D) :
    GlobalTheory.FinPl.colMul d.jY i ((d.pY *ᵥ y) i) = rat (fun k l => d.e' k i * d.qY i l) *ᵥ y := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, HypDec.jY, HypDec.pY, rat, mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  show (incA D) (d.qY i l) * y l * (incA D) (d.e' k i) = (incA D) (d.e' k i * d.qY i l) * y l
  rw [map_mul]
  ring

theorem mulVec_eq_sum_colMul {m n : ℕ} (x : Mx D m n) (w : Fin n → AE D) :
    x *ᵥ w = ∑ i, GlobalTheory.FinPl.colMul x i (w i) := by
  funext k
  simp only [mulVec, dotProduct, GlobalTheory.FinPl.colMul, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem mulVec_eq_sum_col {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) (w : Fin n → D.host.E) :
    x *ᵥ w = ∑ i, fun k => x k i * w i := by
  funext k
  simp only [mulVec, dotProduct, Finset.sum_apply]

theorem rank_one_mulVec {m n k : ℕ} (a : Matrix (Fin m) (Fin k) D.host.E) (b : Matrix (Fin k) (Fin n) D.host.E)
    (i : Fin k) (x : Fin n → D.host.E) : (fun r l => a r i * b i l) *ᵥ x = fun r => a r i * (b *ᵥ x) i := by
  funext r
  simp only [mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem monoAt_of_proj {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S)
    (hX : ∀ i, ∀ x ∈ L, (fun k => d.e k i * (d.qX *ᵥ x) i) ∈ L)
    (hY : ∀ i, ∀ x ∈ L, (fun k => d.e' k i * (d.qY *ᵥ x) i) ∈ L) (v : GlobalTheory.FinPl.Pl D) :
    MonoAt d L (L.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))) v := by
  have h0 : ∀ x ∈ L, d.i₀ *ᵥ (d.q0 *ᵥ x) ∈ L := by
    intro x hx
    have e : d.i₀ *ᵥ (d.q0 *ᵥ x) = x - d.e *ᵥ (d.qX *ᵥ x) - d.e' *ᵥ (d.qY *ᵥ x) := by
      have := congrArg (· *ᵥ x) d.sum_eq_one_rat
      simp only [add_mulVec, one_mulVec, ← mulVec_mulVec] at this
      rw [sub_sub, eq_sub_iff_add_eq]
      calc _ = d.e *ᵥ (d.qX *ᵥ x) + d.i₀ *ᵥ (d.q0 *ᵥ x) + d.e' *ᵥ (d.qY *ᵥ x) := by abel
        _ = x := this
    rw [e, mulVec_eq_sum_col d.e, mulVec_eq_sum_col d.e']
    exact L.sub_mem (L.sub_mem hx (L.sum_mem fun i _ => hX i x hx)) (L.sum_mem fun i _ => hY i x hx)
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · rw [colMul_pX]; exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV _ (fun x hx => by rw [rank_one_mulVec]; exact hX i x hx) hy
    · rw [colMul_pY]; exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV _ (fun x hx => by rw [rank_one_mulVec]; exact hY i x hx) hy
    · exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV d.q0 h0 hy
  · rintro ⟨h1, h2, h3⟩
    have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      have := congrArg (· *ᵥ y) d.sum_eq_one
      simp only [add_mulVec, one_mulVec, ← mulVec_mulVec] at this
      exact this.symm
    rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    refine add_mem (add_mem (AddSubgroup.sum_mem _ fun i _ => h1 i) ?_) (AddSubgroup.sum_mem _ fun i _ => h2 i)
    exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV d.i₀ (fun x hx => hx) h3

section SlopeTestRemainingChoices

variable {A B B₀ : HSp D} {c ρ : ℕ}

theorem antiDiagonalEpsilonGram_mulVec_of_rev_ne (ε : D.host.E) (u : Fin c → D.host.E) (j : Fin c) (hj : j.rev ≠ j) :
    (antiDiagonalSignGramMatrix c ε *ᵥ u) j = u j.rev := by
  simp only [mulVec, dotProduct, antiDiagonalSignGramMatrix]
  rw [Finset.sum_eq_single j.rev]
  · rw [if_pos (by simp only [Fin.val_rev]; omega), if_neg (Ne.symm hj), one_mul]
  · intro b _ hb
    rw [if_neg, zero_mul]
    intro h
    apply hb
    ext
    simp only [Fin.val_rev]
    omega
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mulVec_single_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (j : Fin n) (x : D.host.E) (k : Fin m) :
    (M *ᵥ Pi.single j x) k = M k j * x := by
  simp [mulVec, dotProduct, Pi.single_apply]

theorem auxiliaryVectors_pairing_eq_antiDiagonal_gram (a : HermitianOrthogonalExtensionData A B c (-1)) (y : Fin A.rank → D.host.E) (u : Fin c → D.host.E) :
    (a.aᴴ * B.gram) *ᵥ (frameMat B A a.ι *ᵥ y + a.a *ᵥ u) = antiDiagonalSignGramMatrix c (-1) *ᵥ u := by
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq _ _
  have h1 : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
    have h := congrArg Matrix.conjTranspose a.perp
    change ((frameMat B A a.ι)ᴴ * B.gram * a.a)ᴴ = 0ᴴ at h
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.conjTranspose_zero,
      Matrix.mul_assoc] using h
  have h2 : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1) := a.gram
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h2, zero_mulVec, zero_add]

theorem proj_mem (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ) (hd : IsAuxiliaryVectorWittDec a d) (Λ : Lat A)
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    (∀ i, ∀ x ∈ a.lat Λ 𝔟, (fun k => d.e k i * (d.qX *ᵥ x) i) ∈ a.lat Λ 𝔟) ∧
      (∀ i, ∀ x ∈ a.lat Λ 𝔟, (fun k => d.e' k i * (d.qY *ᵥ x) i) ∈ a.lat Λ 𝔟) := by
  obtain ⟨hc, he, s, he'⟩ := hd
  have hrev : ∀ i : Fin ρ, (Fin.castLE (by omega) i : Fin c).rev ≠ Fin.castLE (by omega) i := by
    intro i h
    have := congrArg Fin.val h
    simp only [Fin.val_rev, Fin.val_castLE] at this
    have := i.2
    omega
  have qX_eq : ∀ x (i : Fin ρ),
      (d.qX *ᵥ x) i = star (s i) * ((a.aᴴ * B.gram) *ᵥ x) (Fin.castLE (by omega) i : Fin c).rev := by
    intro x i
    rw [HypDec.qX, he', ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_apply, colsOf, star_mul']
    ring_nf
  have qY_eq : ∀ x (i : Fin ρ),
      (d.qY *ᵥ x) i = star ((-D.host.xi0) ^ (i.1 + 1)) * ((a.aᴴ * B.gram) *ᵥ x) (Fin.castLE (by omega) i : Fin c) := by
    intro x i
    rw [HypDec.qY, he, ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_apply, colsOf, star_mul']
    ring_nf
  have scal : ∀ i : Fin ρ, star (s i) * (-D.host.xi0) ^ (i.1 + 1) = 1 := by
    intro i
    have h1 : (fun k => d.e k i) =
        frameMat B A a.ι *ᵥ 0 + a.a *ᵥ Pi.single (Fin.castLE (by omega) i : Fin c) ((-D.host.xi0) ^ (i.1 + 1)) := by
      funext k
      show _ = (frameMat B A a.ι *ᵥ 0 + a.a *ᵥ _) k
      rw [he, mulVec_zero, zero_add, mulVec_single_apply]
      simp only [colsOf]
      ring
    have h2 : (d.e'ᴴ * B.gram * d.e) i i = (d.qX *ᵥ fun k => d.e k i) i := rfl
    have h3 := congrFun (congrFun d.e'e i) i
    rw [h2, h1, qX_eq, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ (by rw [Fin.rev_rev]; exact (hrev i).symm), Fin.rev_rev, Pi.single_eq_same,
      Matrix.one_apply_eq] at h3
    exact h3
  refine ⟨fun i x hx => ?_, fun i x hx => ?_⟩
  · obtain ⟨y, hy, u, hu, rfl⟩ := hx
    refine ⟨0, Λ.zero_mem, Pi.single (Fin.castLE (by omega) i : Fin c) (u (Fin.castLE (by omega) i)), fun p => ?_, ?_⟩
    · by_cases hp : p = Fin.castLE (by omega) i
      · subst hp; rw [Pi.single_eq_same]; exact hu _
      · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
    · funext k
      show _ = (frameMat B A a.ι *ᵥ 0 + a.a *ᵥ _) k
      rw [qX_eq, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ (by rw [Fin.rev_rev]; exact (hrev i).symm), Fin.rev_rev, mulVec_zero,
        zero_add, mulVec_single_apply, he]
      simp only [colsOf]
      linear_combination (a.a k (Fin.castLE (by omega) i) * u (Fin.castLE (by omega) i)) * scal i
  · obtain ⟨y, hy, u, hu, rfl⟩ := hx
    refine ⟨0, Λ.zero_mem, Pi.single (Fin.castLE (by omega) i : Fin c).rev (u (Fin.castLE (by omega) i : Fin c).rev),
      fun p => ?_, ?_⟩
    · by_cases hp : p = (Fin.castLE (by omega) i : Fin c).rev
      · subst hp; rw [Pi.single_eq_same]; exact hu _
      · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
    · have hs : s i * star ((-D.host.xi0) ^ (i.1 + 1)) = 1 := by
        have := congrArg star (scal i)
        rw [star_mul', star_star, star_one] at this
        exact this
      funext k
      show _ = (frameMat B A a.ι *ᵥ 0 + a.a *ᵥ _) k
      rw [qY_eq, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ (hrev i), mulVec_zero, zero_add, mulVec_single_apply, he']
      simp only [colsOf]
      linear_combination (a.a k (Fin.castLE (by omega) i : Fin c).rev * u (Fin.castLE (by omega) i : Fin c).rev) * hs

end SlopeTestRemainingChoices

theorem monoAt_bes : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := by
  intro D T L sc G F hF ρ h v
  have hL : G.Λ (.grid (2 * ρ + 2) 0) = (G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := G.sp.colLat _ _ h
  obtain ⟨hX, hY⟩ := proj_mem (G.colDec (2 * ρ + 2) (by omega) h) (F.dB ρ h) (hF.hB ρ h) (G.Λ (.core (2 * ρ + 2)))
    (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1))
  rw [← hL] at hX hY
  exact monoAt_of_proj (F.dB ρ h) _ hX hY v

end GlobalTheory.MonoBes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryIdempotentInIntegralClosure
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.ConjCompl

def clos (D : D7) (I : Ideal (𝓞 D.host.E)) : AddSubgroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E, x ∈ I ∧ y = a ⊗ₜ[D.host.F] (x : D.host.E)}

theorem intAf_mul' {F : Type} [Field F] [NumberField F] {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) :
    a * b ∈ intAf F := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem one_mem_intAf' {F : Type} [Field F] [NumberField F] : (1 : Af F) ∈ intAf F := fun v => by
  rw [map_one]; exact one_mem _

variable {D : D7}

theorem tmul_mem_clos {I : Ideal (𝓞 D.host.E)} {a : Af D.host.F} (ha : a ∈ intAf D.host.F) {x : 𝓞 D.host.E}
    (hx : x ∈ I) : a ⊗ₜ[D.host.F] (x : D.host.E) ∈ clos D I :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem mul_mem_clos {I J : Ideal (𝓞 D.host.E)} {y z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ clos D I) (hz : z ∈ clos D J) : y * z ∈ clos D (I * J) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x', hx', rfl⟩ := hz
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      have e : (x : D.host.E) * (x' : D.host.E) = ((x * x' : 𝓞 D.host.E) : D.host.E) := rfl
      rw [e]
      exact tmul_mem_clos (intAf_mul' ha hb) (Ideal.mul_mem_mul hx hx')
    | zero => rw [zero_mul]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
    | neg _ _ h => rw [neg_mul]; exact neg_mem h
  | zero => rw [mul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg _ _ h => rw [mul_neg]; exact neg_mem h

theorem intAE_eq_clos : intAE D = clos D ⊤ := by
  unfold intAE clos
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Submodule.mem_top, true_and]

theorem one_mem_clos : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ clos D ⊤ := by
  have h := tmul_mem_clos (D := D) (I := ⊤) one_mem_intAf' (Submodule.mem_top (x := (1 : 𝓞 D.host.E)))
  have e : ((1 : 𝓞 D.host.E) : D.host.E) = 1 := rfl
  rwa [e, ← Algebra.TensorProduct.one_def] at h

theorem prod_mem_clos {ι : Type} (s : Finset ι) (f : ι → Af D.host.F ⊗[D.host.F] D.host.E)
    (I : ι → Ideal (𝓞 D.host.E)) (h : ∀ i ∈ s, f i ∈ clos D (I i)) : ∏ i ∈ s, f i ∈ clos D (∏ i ∈ s, I i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top]; exact one_mem_clos
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_mem_clos (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem prod_one_sub {A ι : Type} [CommRing A] (c : ι → A) (s : Finset ι)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → c i * c j = 0) : ∏ i ∈ s, (1 - c i) = 1 - ∑ i ∈ s, c i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ih fun i hi j hj hij => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij]
    have h0 : c a * ∑ i ∈ s, c i = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj =>
        h a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (fun e => ha (e ▸ hj))
    linear_combination h0

theorem exists_pow_eq_span' {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (n : ℕ) (s : 𝓞 F), 0 < n ∧ v.asIdeal ^ n = Ideal.span {s} := by
  classical
  have hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set n := Fintype.card (ClassGroup (𝓞 F)) with hn
  have hvn : v.asIdeal ^ n ∈ nonZeroDivisors (Ideal (𝓞 F)) := pow_mem hv n
  have e : (⟨v.asIdeal ^ n, hvn⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨v.asIdeal, hv⟩ ^ n := Subtype.ext (by simp)
  have h1 : ClassGroup.mk0 ⟨v.asIdeal ^ n, hvn⟩ = 1 := by
    rw [e, map_pow]
    exact pow_card_eq_one
  obtain ⟨s, hs⟩ := ((ClassGroup.mk0_eq_one_iff hvn).1 h1).principal
  exact ⟨n, s, Fintype.card_pos, hs⟩

theorem finPart_es_mem {es : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt es PP)
    (hne : conjI PP.asIdeal ≠ PP.asIdeal) : finPart D es ∈ clos D (conjI PP.asIdeal) := by
  have hmax : (conjI PP.asIdeal).IsMaximal := by
    rw [GlobalTheory.LiftIdeal.conjI_eq_map D]; exact GlobalTheory.LiftIdeal.isMaximal_map D PP
  obtain ⟨s, hs, hsP⟩ : ∃ s ∈ conjI PP.asIdeal, s ∉ PP.asIdeal := by
    by_contra hc
    push_neg at hc
    exact hne (hmax.eq_of_le PP.isPrime.ne_top hc)
  have hs0 : s ≠ 0 := fun e => hsP (e ▸ PP.asIdeal.zero_mem)
  have hsE : (s : D.host.E) ≠ 0 := fun e => hs0 (RingOfIntegers.coe_eq_zero_iff.1 e)
  have hint : finPart D (es * incA D ((s : D.host.E))⁻¹) ∈ intAE D := by
    by_contra hc
    exact hsP ((h.2 s hs0).2 hc)
  rw [intAE_eq_clos] at hint
  have e1 : es = es * incA D ((s : D.host.E))⁻¹ * incA D (s : D.host.E) := by
    rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hsE, map_one, mul_one]
  have hgen : finPart D (incA D (s : D.host.E)) ∈ clos D (conjI PP.asIdeal) := by
    have e2 : finPart D (incA D (s : D.host.E)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (s : D.host.E) := by
      show Algebra.TensorProduct.map _ _ ((1 : AF D.host.F) ⊗ₜ[D.host.F] (s : D.host.E)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
    rw [e2]; exact tmul_mem_clos one_mem_intAf' hs
  rw [e1, map_mul]
  have h3 := mul_mem_clos hint hgen
  rwa [Ideal.top_mul] at h3

theorem one_sub_mem {PP : Formalism.L2.DIV.Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal) {α : Af D.host.F}
    (h1 : evalV D.host.F v α = 1) (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    (1 - α) ⊗ₜ[D.host.F] (1 : D.host.E) ∈ clos D (conjI PP.asIdeal) := by
  obtain ⟨n, t, hn, ht⟩ := exists_pow_eq_span' v
  have htv : t ∈ v.asIdeal := Ideal.pow_le_self hn.ne' (ht ▸ Ideal.mem_span_singleton_self t)
  have htw : ∀ w : HeightOneSpectrum (𝓞 D.host.F), w ≠ v → t ∉ w.asIdeal := fun w hw h => by
    have h2 : v.asIdeal ^ n ≤ w.asIdeal := by rw [ht, Ideal.span_le, Set.singleton_subset_iff]; exact h
    exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top (w.isPrime.le_of_pow_le h2))).symm
  have ht0 : (t : D.host.F) ≠ 0 := by
    intro h0'
    have : t = 0 := by exact_mod_cast h0'
    subst this
    rw [Ideal.span_singleton_eq_bot.2 rfl] at ht
    exact v.ne_bot ((pow_eq_zero_iff hn.ne').1 ht)
  set a : Af D.host.F := algebraMap D.host.F (Af D.host.F) (t : D.host.F)⁻¹ * (1 - α) with ha_def
  have ha : a ∈ intAf D.host.F := by
    intro w
    rw [ha_def, map_mul, AlgHom.commutes, map_sub, map_one]
    by_cases hw : w = v
    · subst hw; rw [h1, sub_self, mul_zero]; exact zero_mem _
    · rw [h0 w hw, sub_zero, mul_one, HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (((((t : D.host.F))⁻¹ : D.host.F) : HeightOneSpectrum.adicCompletion D.host.F w)) ≤ 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
        show ((t : D.host.F)) = algebraMap (𝓞 D.host.F) D.host.F t from rfl,
        (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 (htw w hw), inv_one]
  have ecoe : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (t : D.host.F) := rfl
  have hx : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ conjI PP.asIdeal := by
    apply Ideal.subset_span
    refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, ?_, ?_⟩
    · rw [← Ideal.mem_comap, hv]; exact htv
    · rw [ecoe]
      simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
  have h3 := tmul_mem_clos ha hx
  have e : a ⊗ₜ[D.host.F] ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) =
      (1 - α) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [ecoe, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, ha_def, ← mul_assoc,
      ← map_mul, mul_inv_cancel₀ ht0, map_one, one_mul]
  rwa [e] at h3

theorem finPart_one_sub_cA_mem {es : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt es PP)
    (hne : conjI PP.asIdeal ≠ PP.asIdeal) : finPart D (1 - cA D es) ∈ clos D (conjI PP.asIdeal) := by
  obtain ⟨-, -, v, ε, hε, h3⟩ := h.1
  have hsplit := GlobalTheory.LevelPlaces.splitAt_of h.1 hε h3
  obtain ⟨Q, hQ, hQv⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D v es hsplit
  have hQP : Q = PP := GlobalTheory.PlaceVec.isIdemAt_inj hQ h
  subst hQP
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  have e1 : 1 - cA D es = es + (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) := by
    rw [← h3]; ring
  have e2 : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [e1, map_add, map_sub, map_one, e2, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
  exact add_mem (finPart_es_mem h hne) (one_sub_mem hQv hα1 hα0)

theorem offConj : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) →
    finPart D (1 - cA D e) ∈ AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E,
      x ∈ GlobalTheory.LiftLevel.liftI Pg Q ∧ y = a ⊗ₜ[D.host.F] (x : D.host.E)} := by
  intro D Pg Q e he
  have he' := he
  obtain ⟨⟨es, hes, rfl⟩, h0⟩ := he
  have hz : ∀ i ∈ Pg ∪ Q, ∀ j ∈ Pg ∪ Q, es i * cA D (es j) = 0 := by
    have hsum : ∑ x ∈ (Pg ∪ Q) ×ˢ (Pg ∪ Q), es x.1 * cA D (es x.2) = 0 := by
      rw [Finset.sum_product, ← h0, map_sum, Finset.sum_mul_sum]
    have hall := GlobalTheory.PlaceVec.idem_eq_zero_of_sum (A := AE D) GlobalTheory.PlaceVec.natCast_mul_eq_zero
      (fun x : Formalism.L2.DIV.Pl D.host.E × Formalism.L2.DIV.Pl D.host.E => es x.1 * cA D (es x.2)) ((Pg ∪ Q) ×ˢ (Pg ∪ Q))
      (fun x hx => by
        obtain ⟨h1, h2⟩ := Finset.mem_product.1 hx
        show es x.1 * cA D (es x.2) * (es x.1 * cA D (es x.2)) = es x.1 * cA D (es x.2)
        rw [mul_mul_mul_comm, ← map_mul, (hes _ h1).1.1, (hes _ h2).1.1]) hsum
    exact fun i hi j hj => hall (i, j) (Finset.mem_product.2 ⟨hi, hj⟩)
  have horth : ∀ i ∈ Pg ∪ Q, ∀ j ∈ Pg ∪ Q, i ≠ j → cA D (es i) * cA D (es j) = 0 := by
    intro i hi j hj hij
    rcases GlobalTheory.PlaceVec.splitIdem_eq_or (hes i hi).1 (hes j hj).1 (hz i hi j hj) (hz j hj i hi) with e | e
    · exact absurd (GlobalTheory.PlaceVec.isIdemAt_inj (hes i hi) (by rw [e]; exact hes j hj)) hij
    · rw [← map_mul, e, map_zero]
  show finPart D _ ∈ clos D (GlobalTheory.LiftLevel.liftI Pg Q)
  rw [map_sum, ← prod_one_sub _ _ horth, map_prod]
  exact prod_mem_clos (Pg ∪ Q) _ (fun PP => conjI PP.asIdeal) fun PP hP =>
    finPart_one_sub_cA_mem (hes PP hP) (by rw [GlobalTheory.LiftIdeal.conjI_eq_map D]; exact GlobalTheory.LiftIdeal.map_ne he' hP hP)

end GlobalTheory.ConjCompl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterUnitaryCoordinateAction
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

namespace GlobalTheory.ArchLine

theorem continuous_archAct_line : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ W,
    ∀ v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
      Continuous fun t : ℝ => archAct M (γ (Multiplicative.ofAdd t)) v := by
  intro F E _ _ _ _ _ σ n d X W M γ hγ v
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have hγc : Continuous fun t : ℝ => γ (Multiplicative.ofAdd t) := hγ.1.comp continuous_ofAdd
  have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t)))ᵀ :=
    ((Units.continuous_val.comp continuous_subtype_val).comp hγc).matrix_transpose
  have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hev : Continuous (evI F) := by
    change Continuous fun a : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
    refine Continuous.comp ?_ continuous_fst
    change Continuous fun x : InfiniteAdeleRing F =>
      ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  have hl : Continuous (locV : (Fin n × Fin d → AF F) → _) := continuous_pi fun i => hev.comp (continuous_apply i)
  show Continuous fun t : ℝ =>
    (locV (M.co.e (mat (1 : UA σ X.J) * M.co.e.symm (liftV v.1, liftV v.2) * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1,
     locV (M.co.e (mat (1 : UA σ X.J) * M.co.e.symm (liftV v.1, liftV v.2) * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2)
  exact ((hl.comp continuous_fst).prodMk (hl.comp continuous_snd)).comp
    (he.comp (continuous_const.matrix_mul hm))

end GlobalTheory.ArchLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainLiftSurjectiveOfAdjointNonzeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenRankThetaChainLift_surjective_of_adjoint_nonzero : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ParBound D → StepUp D → OntoAll D := by
  first | exact @GlobalTheory.EvenOnto.ontoAll_of | exact GlobalTheory.EvenOnto.ontoAll_of | (intros; apply GlobalTheory.EvenOnto.ontoAll_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaCellSemisimplificationGLStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricLemma_cell_semisimplification_GL : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.CellSemisimplification k := by
  first | exact @GlobalTheory.SmGL.CellSemis.cellSemisimplification | exact GlobalTheory.SmGL.CellSemis.cellSemisimplification | (intros; apply GlobalTheory.SmGL.CellSemis.cellSemisimplification <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkMapCuspFormsExtendsToSmoothVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gkMapCuspForms_extends_to_smoothVectors : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D := by
  first | exact @GlobalTheory.GKExtensionToSmoothVectors.gkExtension | exact GlobalTheory.GKExtensionToSmoothVectors.gkExtension | (intros; apply GlobalTheory.GKExtensionToSmoothVectors.gkExtension <;> assumption)
end

