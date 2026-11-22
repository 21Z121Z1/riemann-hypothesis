import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0288
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0347
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0349
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.GramTotallyDefinite
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StabilisesColumnBaseLatticeIffFirstFactor
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0346
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackScalarNeZeroLatticeTuplePair
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem pullbackScalar_ne_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std), ∀ j < D.R.m, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → d.sP S j La La' ≠ 0) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj La La' h1 h2
  have hj' : j + 1 ≤ D.R.m := hj
  have key := fun (i : ℕ) (hi : i ≤ D.R.m) (Lb : (sysS H X std).Lt i) (hLb : ((sysS H X std).Pj i).IsLatTup Lb.2) =>
    GlobalTheory.T.adelicCharacters_at_det_rational_isometry_rep_level J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj i hi (clsAt X H i Lb.1 Lb.2) (J.pt std i hi Lb)
      (d.gam i hi Lb) (d.mem i hi Lb) (d.kap i hi Lb) (d.eq i hi Lb hLb)
  have n1 := (key j (Nat.le_of_succ_le hj') La h1).2.2
  have n2 := (key (j + 1) hj' La' h2).2.2
  simp only [Dec.sP, dif_pos hj', Dec.chi]
  exact div_ne_zero (mul_ne_zero n1 (Units.ne_zero _)) (mul_ne_zero n2 (Units.ne_zero _))

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackThenFrameSubstitutionEqChangedFrames
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem sum_pullMat_subBG_reframe : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), e j La * star (e j La) = 1 → e (j + 1) La' * star (e (j + 1) La') = 1 → (∀ v, IsUnit (fd.frM j La v).det ∧ IsUnit (fd.frM (j + 1) La' v).det) → ∀ x y, ∑ z, ι (pullMat (e j La) (e (j + 1) La') x z) * (c * subBG E pos fd j La La' z y) = c * subBG E pos (reframe fd ρ e) j La La' x y := by
  intro D p _ X E pos fd lam ι hι ρ hL e c j La La' he he' hdet x y
  classical
  have hs : ∀ q : D.host.E, star q = D.host.conj q := Formalism.BasicNotions.bridge_star_holds D.R D.host
  have hcc : ∀ q : D.host.E, D.host.conj (D.host.conj q) = q := fun q => D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])
  have hconj : ∀ τ q, TaylorLogMetric.embT D τ (D.host.conj q) = (starRingEnd ℂ) (TaylorLogMetric.embT D τ q) := fun τ q =>
    D.host.conjE_apply (TaylorLogMetric.embT D τ) q
  have hιe : ∀ τ q, ι (TaylorLogMetric.embT D τ q) = twG X E (pos.symm τ).1 (pos.symm τ).2
      (ρ _ (if IsOddPos (pos.symm τ).2 then D.host.conj q else q)) := by
    intro τ q
    have halg : TaylorLogMetric.embT D τ q ∈ TaylorLogMetric.Qbar := mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) q).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
    have h2 := hL (pos.symm τ).1 (pos.symm τ).2 q
    simp only [Sigma.eta, Equiv.apply_symm_apply] at h2
    rw [← h2]; unfold TaylorLogMetric.lamC; rw [dif_pos halg]; exact hι ⟨_, halg⟩
  have hinv : ∀ {n : ℕ} (v : X.Pl) (A : Matrix (Fin n) (Fin n) D.host.E) (M : Matrix (Fin n) (Fin n) (X.G.P.Qq v)),
      A * star A = 1 → ((star A).map (ρ v) * M)⁻¹ = M⁻¹ * A.map (ρ v) := by
    intro n v A M h
    rw [Matrix.mul_inv_rev]
    congr 1
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero (ρ v)) (map_one (ρ v))]
  obtain ⟨τ, b0, a0⟩ := x
  obtain ⟨τ', b1, a1⟩ := y
  by_cases hxy : τ = τ'
  · subst hxy
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
    · rw [Fintype.sum_prod_type]
      simp only [subBG, reframe, pullMat, ↓reduceIte]
      rw [hinv _ _ _ he, hinv _ _ _ he']
      by_cases hodd : IsOddPos (pos.symm τ).2
      · simp only [hodd, ↓reduceIte, map_mul, ← hconj, hιe, Matrix.map_apply, Matrix.mul_apply,
          Matrix.star_apply, hs, map_sum, hcc, Finset.mul_sum, Finset.sum_mul]
        first
          | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
      · simp only [hodd, ↓reduceIte, map_mul, ← hconj, hιe, Matrix.map_apply, Matrix.mul_apply,
          Matrix.star_apply, hs, map_sum, hcc, Finset.mul_sum, Finset.sum_mul]
        first
          | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    · intro τ'' _ hne
      apply Finset.sum_eq_zero
      intro z _
      simp [pullMat, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [show subBG E pos (reframe fd ρ e) j La La' (τ, b0, a0) (τ', b1, a1) = 0 from if_neg hxy, mul_zero]
    apply Finset.sum_eq_zero
    intro z _
    by_cases h1 : τ = z.1
    · have h2 : z.1 ≠ τ' := fun h => hxy (h1.trans h)
      rw [show subBG E pos fd j La La' z (τ', b1, a1) = 0 from if_neg h2, mul_zero, mul_zero]
    · rw [show pullMat (e j La) (e (j + 1) La') (τ, b0, a0) z = 0 from if_neg h1, map_zero, zero_mul]

end GlobalTheory.TwV.DelB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealisingPolynomialBlockwiseHomogeneous
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA.BlockHom

open MvPolynomial

theorem two_zpow_inj {a b : ℤ} (h : (2 : ℂ) ^ a = (2 : ℂ) ^ b) : a = b := by
  have h' := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_zpow, Complex.norm_ofNat] at h'
  exact zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num) h'

theorem eval_aeval_gen {σ κ : Type} (g : κ → ℂ) (φ : σ → MvPolynomial κ ℂ) (Q : MvPolynomial σ ℂ) :
    MvPolynomial.eval g (MvPolynomial.aeval φ Q) = MvPolynomial.eval (fun s => MvPolynomial.eval g (φ s)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p s hp => rw [map_mul, map_mul, aeval_X, map_mul, hp, eval_X]

open Classical in
theorem evFr_scale (D : D7) {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ)
    (hQ : Q ∈ WtPol ℂ ν) (τ₀ : D.what₂.Tau) (t : ℂ) (ht : t ≠ 0) (y : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    GL3Theta.evFr D Q (fun τ => if τ = τ₀ then t • y τ else y τ) = t ^ (∑ r, ν τ₀ r) * GL3Theta.evFr D Q y := by
  set β : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := fun τ => if τ = τ₀ then t • (1 : Matrix (Fin n) (Fin n) ℂ) else 1 with hβ
  have hB : IsBor β := by
    intro τ
    refine ⟨fun r s hsr => ?_, fun r => ?_⟩
    · simp only [hβ]; split_ifs <;> simp [Matrix.one_apply_ne (ne_of_lt hsr).symm]
    · simp only [hβ]; split_ifs <;> simp [ht]
  have h1 := congrArg (MvPolynomial.eval (fun k : GL3Theta.FrV D n => y k.1 k.2.1 k.2.2)) (hQ β hB)
  have hL : MvPolynomial.eval (fun k : GL3Theta.FrV D n => y k.1 k.2.1 k.2.2) (colSub β Q) =
      GL3Theta.evFr D Q (fun τ => if τ = τ₀ then t • y τ else y τ) := by
    unfold colSub GL3Theta.evFr
    rw [eval_aeval_gen]
    apply congrArg (fun F => MvPolynomial.eval F Q)
    funext k
    simp only [map_sum, map_mul, eval_C, eval_X, hβ]
    by_cases hk : k.1 = τ₀
    · simp [hk, Matrix.one_apply, mul_comm]
    · simp [hk, Matrix.one_apply]
  rw [← hL, h1, MvPolynomial.smul_eval]
  unfold GL3Theta.evFr
  congr 1
  rw [Finset.prod_eq_single τ₀]
  · simp [hβ, Finset.prod_pow_eq_pow_sum]
  · intro τ _ hτ
    simp [hβ, hτ]
  · simp

open Classical in
theorem prod_scale {ι : Type} [Fintype ι] (τ₀ : ι) (A B : ι → ℂ) (k : ℂ)
    (hAB : ∀ τ, A τ = if τ = τ₀ then k * B τ else B τ) (e : ι → ℤ) :
    ∏ τ, A τ ^ e τ = k ^ e τ₀ * ∏ τ, B τ ^ e τ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ₀), ← Finset.mul_prod_erase (s := Finset.univ) (fun τ => B τ ^ e τ) (Finset.mem_univ τ₀)]
  rw [hAB τ₀, if_pos rfl, mul_zpow, mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro τ hτ
  rw [hAB τ, if_neg (Finset.ne_of_mem_erase hτ)]

open Classical in
theorem zT_scale {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}
    (f f' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, IsUnit (f τ).det) (τ₀ : D.what₂.Tau) (c : ℂ) (hc : c ≠ 0)
    (hf' : ∀ τ, f' τ = if τ = τ₀ then (if IsOddPos (pos.symm τ₀).2 then c⁻¹ else c) • f τ else f τ) (τ : D.what₂.Tau) :
    zT X D pos f' τ = if τ = τ₀ then c • zT X D pos f τ else zT X D pos f τ := by
  unfold zT
  rw [hf' τ]
  by_cases hτ : τ = τ₀
  · subst hτ
    simp only [if_true]
    by_cases ho : IsOddPos (pos.symm τ).2
    · simp only [ho, if_true]
      rw [show c⁻¹ • f τ = (Units.mk0 c⁻¹ (inv_ne_zero hc)) • f τ from rfl, Matrix.inv_smul' (k := Units.mk0 c⁻¹ (inv_ne_zero hc)) (h := hf τ)]
      ext a b
      simp [Matrix.submatrix_apply, Matrix.transpose_apply, Units.smul_def]
    · simp [ho]
  · simp [hτ]

def dg {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) (τ₀ : D.what₂.Tau)
    (m : Var (X.Pj i) →₀ ℕ) : ℕ :=
  ∑ x : Var (X.Pj i), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀ then m x else 0

open Classical in
theorem valZ_scale {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ}
    (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ) (f f' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, IsUnit (f τ).det)
    (τ₀ : D.what₂.Tau) (hf' : ∀ τ, f' τ = if τ = τ₀ then (if IsOddPos (pos.symm τ₀).2 then (2:ℂ)⁻¹ else 2) • f τ else f τ) :
    valZ X D pos i h R f' = valZ X D pos i h (∑ m ∈ R.support, monomial m (coeff m R * 2 ^ (dg X D pos i τ₀ m))) f := by
  have hg : ∀ x : Var (X.Pj i), zT X D pos f' (posJ X D pos i ⟨x.1, x.2.1⟩) (Fin.cast h x.2.2.1) (Fin.cast h x.2.2.2) =
      (2:ℂ) ^ (if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀ then 1 else 0) *
        zT X D pos f (posJ X D pos i ⟨x.1, x.2.1⟩) (Fin.cast h x.2.2.1) (Fin.cast h x.2.2.2) := by
    intro x
    rw [zT_scale X D pos f f' hf τ₀ 2 two_ne_zero hf']
    by_cases hb : (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀
    · have e : posJ X D pos i ⟨x.1, x.2.1⟩ = τ₀ := by rw [hb]; simp
      simp [e, hb]
    · have e : posJ X D pos i ⟨x.1, x.2.1⟩ ≠ τ₀ := fun e => hb (by rw [← e]; simp)
      simp [e, hb]
  unfold valZ
  rw [MvPolynomial.eval_eq, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have hsum : (∑ x ∈ m.support, (if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀ then 1 else 0) * m x) = dg X D pos i τ₀ m := by
    unfold dg
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).trans ?_
    · intro x _ hx
      have hx0 : m x = 0 := by simpa using hx
      simp [hx0]
    · apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
  simp only [hg, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  rw [hsum, Finset.prod_subset (Finset.subset_univ m.support) (fun x _ hx => by
    have hx0 : m x = 0 := by simpa using hx
    simp [hx0])]
  ring

theorem realises_blockHom : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (a : D.what₂.Tau → ℤ) (ν : D.what₂.Tau → Fin n → ℕ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (R : XR (X.Pj i) ℂ), Q ∈ WtPol ℂ ν → Realises X D pos i h a Q R → ∀ m ∈ R.support, ∀ τ, (∑ x : Var (X.Pj i), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ then (m x : ℤ) else 0) = (if IsOddPos (pos.symm τ).2 then -1 else 1) * ((∑ r, (ν τ r : ℤ)) - n * a τ) - n * eT X D pos i τ := by
  intro p _ X D pos i n h a ν Q R hQ hR m hm τ₀
  classical
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ε = if IsOddPos (pos.symm τ₀).2 then -1 else 1 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℂ, t = if IsOddPos (pos.symm τ₀).2 then (2:ℂ)⁻¹ else 2 := ⟨_, rfl⟩
  have htε : t = (2:ℂ) ^ ε := by
    rw [ht, hε]; split_ifs <;> simp
  have ht0 : t ≠ 0 := by rw [htε]; exact zpow_ne_zero _ two_ne_zero
  obtain ⟨R2, hR2⟩ : ∃ R2 : XR (X.Pj i) ℂ, R2 = ∑ m ∈ R.support, monomial m (coeff m R * 2 ^ (dg X D pos i τ₀ m)) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (((2:ℂ) ^ n) ^ eT X D pos i τ₀)⁻¹ * ((t ^ n) ^ (-(a τ₀)) * t ^ (∑ r, ν τ₀ r)) := ⟨_, rfl⟩
  have key : ∀ f : Fr1 D n, ev1 X D pos i h R2 f = c * ev1 X D pos i h R f := by
    intro f
    have hfu : ∀ τ, IsUnit (f.1 τ).det := f.2
    let f' : Fr1 D n := ⟨fun τ => if τ = τ₀ then t • f.1 τ else f.1 τ, by
      intro τ
      by_cases hτ : τ = τ₀
      · simp only [hτ, if_true, Matrix.det_smul]
        exact (IsUnit.mk0 _ (pow_ne_zero _ ht0)).mul (hfu τ₀)
      · simp only [hτ, if_false]; exact hfu τ⟩
    have hf' : ∀ τ, f'.1 τ = if τ = τ₀ then (if IsOddPos (pos.symm τ₀).2 then (2:ℂ)⁻¹ else 2) • f.1 τ else f.1 τ := by
      intro τ; rw [← ht]
    have e1 := GlobalTheory.T.evalStdFrames_eq_detPower_mul_blockValue X D pos i h R2 f
    have e2 := GlobalTheory.T.evalStdFrames_eq_detPower_mul_blockValue X D pos i h R f'
    have e3 := hR f'
    have e4 := hR f
    have hv : valZ X D pos i h R f'.1 = valZ X D pos i h R2 f.1 := by
      rw [hR2]; exact valZ_scale X D pos i h R f.1 f'.1 hfu τ₀ hf'
    have hdz : ∏ τ, (zT X D pos f'.1 τ).det ^ eT X D pos i τ =
        ((2:ℂ) ^ n) ^ eT X D pos i τ₀ * ∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ := by
      apply prod_scale
      intro τ
      rw [zT_scale X D pos f.1 f'.1 hfu τ₀ 2 two_ne_zero hf' τ]
      split_ifs <;> simp [Matrix.det_smul]
    have hdf : ∏ τ, (f'.1 τ).det ^ (-(a τ)) = (t ^ n) ^ (-(a τ₀)) * ∏ τ, (f.1 τ).det ^ (-(a τ)) := by
      apply prod_scale
      intro τ
      show (if τ = τ₀ then t • f.1 τ else f.1 τ).det = _
      split_ifs <;> simp [Matrix.det_smul]
    have hq : GL3Theta.evFr D Q f'.1 = t ^ (∑ r, ν τ₀ r) * GL3Theta.evFr D Q f.1 := evFr_scale D ν Q hQ τ₀ t ht0 f.1
    have hK : ((2:ℂ) ^ n) ^ eT X D pos i τ₀ ≠ 0 := zpow_ne_zero _ (pow_ne_zero _ two_ne_zero)
    have hE := e2.symm.trans e3
    rw [hv, hdz, hdf, hq] at hE
    rw [e1, e4, hc]
    calc (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ) * valZ X D pos i h R2 f.1
        = (((2:ℂ) ^ n) ^ eT X D pos i τ₀)⁻¹ * (((2:ℂ) ^ n) ^ eT X D pos i τ₀ *
            (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ) * valZ X D pos i h R2 f.1) := by
          field_simp
      _ = _ := by rw [hE]; ring
  have hz : R2 - c • R = 0 := by
    apply GlobalTheory.T.evalModelPolynomialOnStdFrames_injective X D pos i h
    intro f
    rw [map_sub, map_smul]
    simp [key f]
  have hcoef : coeff m R2 = coeff m R * 2 ^ (dg X D pos i τ₀ m) := by
    rw [hR2, coeff_sum]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb
      rw [coeff_monomial, if_neg hb]
    · intro hm'; exact absurd hm hm'
  have hm0 : coeff m R ≠ 0 := (mem_support_iff.mp hm)
  have h2 : (2:ℂ) ^ (dg X D pos i τ₀ m) = c := by
    have := congrArg (coeff m) hz
    rw [coeff_sub, coeff_smul, hcoef, coeff_zero, sub_eq_zero, smul_eq_mul] at this
    exact mul_left_cancel₀ hm0 (by rw [this]; ring)
  have hcz : c = (2:ℂ) ^ (-((n : ℤ) * eT X D pos i τ₀) + (ε * ((n : ℤ) * (-(a τ₀))) + ε * ((∑ r, ν τ₀ r : ℕ) : ℤ))) := by
    have a1 : ((2:ℂ) ^ n) ^ (eT X D pos i τ₀) = (2:ℂ) ^ ((n : ℤ) * eT X D pos i τ₀) := by rw [zpow_mul, zpow_natCast]
    have a2 : (((2:ℂ) ^ ε) ^ n) ^ (-(a τ₀)) = (2:ℂ) ^ (ε * ((n : ℤ) * (-(a τ₀)))) := by rw [zpow_mul, zpow_mul, zpow_natCast]
    have a3 : ((2:ℂ) ^ ε) ^ (∑ r, ν τ₀ r) = (2:ℂ) ^ (ε * ((∑ r, ν τ₀ r : ℕ) : ℤ)) := by rw [zpow_mul, zpow_natCast]
    rw [hc, htε, a1, a2, a3, zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_neg]
  have hfin : ((dg X D pos i τ₀ m : ℕ) : ℤ) = -((n : ℤ) * eT X D pos i τ₀) + (ε * ((n : ℤ) * (-(a τ₀))) + ε * ((∑ r, ν τ₀ r : ℕ) : ℤ)) :=
    two_zpow_inj (by rw [zpow_natCast, h2, hcz])
  unfold dg at hfin
  push_cast at hfin
  rw [hfin, hε]
  ring

end GlobalTheory.TwV.DelA.BlockHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteBaseDatumIntegralOffBadPrimesStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intOff_xi0_of_joint : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), ∀ j La La' z, IntOff (t.O u μ).S (J.xi0 std S.Xi j La La' z) := by
  first | exact @GlobalTheory.TwV.Joint.site_base_datum_integral_off_bad_primes | exact GlobalTheory.TwV.Joint.site_base_datum_integral_off_bad_primes | (intros; apply GlobalTheory.TwV.Joint.site_base_datum_integral_off_bad_primes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFiniteDataLevelPosBadPrimeFactorsStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.site_finite_data_level_pos_bad_prime_factors : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), SNum (t.O u μ).S (t.rd u μ).lev := by
  first | exact @GlobalTheory.TwV.sNum_lev_site | exact GlobalTheory.TwV.sNum_lev_site | (intros; apply GlobalTheory.TwV.sNum_lev_site <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLabelsWithStepZeroClassMap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Port

set_option maxHeartbeats 4000000 in

theorem site_labels_with_stepZero_classMap : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD g.herm u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t), Fl.mm = D.R.m → SiteGood Z → (∀ j, j < D.R.m → (Tw.fm u μ).KRat j) → (D.chTw u μ).DGam ∣ (D.mem u).C.DGam → ∀ (one : OneHyp ((g.forms u).cls0).toChart.lev (lev0At g u w hg).A ((g.forms u).cls0).toChart.y) (e0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0), ∃ X : LabIn (Z.inTw Fl ht Gt), ∀ a (La : (D.gat u w hg).P.Tup), X.c0.cls a La = e0 (levelZeroClass one a La) := by
  intro D Gt c g u w hg Tw μ Z Fl ht hm G rat dgam one e0
  refine ⟨labOf ⟨fun _ _ => rfl, fun j hj => chX_stepInOf hj (Z.Fo j hj) (Z.loc Fl ht j hj) (Gt.gat_pos u w hg) (Z.sameU Fl ht j hj)
    (Z.frRat Fl ht j hj) (hypTJC_site Z Fl ht G.siteGood_prime_torsion j hj), fillOK_of_empty (Z.lv_empty Fl ht)⟩ ht hm
    (clsAt0Of one e0 (fun c => Formalism.L2.G.Triv.card_stab (g.herm.lev0 u) D.host.g_prime D.host.g_ne c) _) rat dgam, fun a La => rfl⟩

end GlobalTheory.Port
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLocalIdentificationsEqStepZero
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Proof.LocOfSite

section Step

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  {cmp : Type} [hcmp : Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}

theorem iw_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) (B0 : GL (Fin D.R.k) D.host.E) (v) :
    (locJ hi t B).iw v = (locAt X u w hg B0).iw v := rfl

theorem pl_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) (B0 : GL (Fin D.R.k) D.host.E) (v) :
    (locJ hi t B).pl v = (locAt X u w hg B0).pl v := rfl

theorem B_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) : (locJ hi t B).B = reGL (rankN D (i + 1) hi) _ B := rfl

theorem splAlg_locJ' (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) : GlobalTheory.TwV.SplAlg (locJ hi t B) :=
  fun _ a => (X.g u w hg).spl_alg _ _ a

end Step

theorem splAlg_locAt {D : D7} (X : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B0 : GL (Fin D.R.k) D.host.E) :
    GlobalTheory.TwV.SplAlg (locAt X u w hg B0) :=
  fun _ a => (X.g u w hg).spl_alg _ _ a

set_option maxHeartbeats 4000000 in

theorem loc_eq_step0 : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD g.herm u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t), (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).iw v = (lev0At g u w hg).A.iw v) ∧ (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).pl v = (lev0At g u w hg).A.pl v) ∧ (∀ j hj β β', (((Z.inTw Fl ht Gt).at' j hj).st.loc β).B = (((Z.inTw Fl ht Gt).at' j hj).st.loc β').B) ∧ (∀ j hj, ((Z.inTw Fl ht Gt).at' j hj).st.pos = Gt.gat_pos u w hg) ∧ (∀ j hj β, GlobalTheory.TwV.SplAlg (((Z.inTw Fl ht Gt).at' j hj).st.loc β)) ∧ GlobalTheory.TwV.SplAlg (lev0At g u w hg).A := by
  intro D Gt c g u w hg Tw μ Z Fl ht
  refine ⟨fun j hj β v => ?_, fun j hj β v => ?_, fun j hj β β' => ?_, fun j hj => rfl, fun j hj β => ?_,
    splAlg_locAt g.herm u w hg g.cmp.B⟩
  · exact iw_locJ (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B g.cmp.B v
  · exact pl_locJ (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B g.cmp.B v
  · exact (B_locJ (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B).trans
      (B_locJ (hcmp := (Z.loc Fl ht j hj).fin β') hj ((Z.loc Fl ht j hj).t β') (Z.loc Fl ht j hj).B).symm
  · exact splAlg_locJ' (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B

end GlobalTheory.Proof.LocOfSite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddingsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.site_place_induces_position_embeddings : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos) := by
  first | exact @GlobalTheory.TwV.pos_at_site | exact GlobalTheory.TwV.pos_at_site | (intros; apply GlobalTheory.TwV.pos_at_site <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteResidueCharNotMemBadPrimesStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.site_residue_char_not_mem_bad_primes : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), D.what₂.places.resChar w ∉ (t.O u μ).S := by
  first | exact @GlobalTheory.TwV.SitePrime.resChar_not_mem_S | exact GlobalTheory.TwV.SitePrime.resChar_not_mem_S | (intros; apply GlobalTheory.TwV.SitePrime.resChar_not_mem_S <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem fills_Pj_m_add_one {p : ℕ} {G : GAtP p} (Fl : Fills G) (j : ℕ) :
    (Fl.Pj j).m + 1 = Formalism.MainNotions.FormalGroupSystem.NN G.P.m Fl.t j := by
  cases j with
  | zero => simp [Fills.Pj, Formalism.MainNotions.FormalGroupSystem.NN]
  | succ j => simp only [Fills.Pj, Places.withWt, Formalism.MainNotions.FormalGroupSystem.NN]; ring

theorem sysS_ranks : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => (sysS H X std).mm = D.R.m ∧ (sysS H X std).t = D.R.t ∧ (∀ j, ((sysS H X std).Pj j).m + 1 = D.R.N j) ∧ ∀ j, RankTie (sysS H X std) D j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  have hk : (D.gat u w hg).P.m + 1 = D.R.N 0 := (lev0At J.Gd u w hg).A.rk
  have ht : (Gl.Fl u w hg).t = D.R.t := X.fl_t
  have hN : ∀ j, D.R.N j = Formalism.MainNotions.FormalGroupSystem.NN (D.gat u w hg).P.m (Gl.Fl u w hg).t j := by
    intro j
    simp only [Formalism.MainNotions.FormalGroupSystem.NN, ht]
    simp only [Formalism.BasicNotions.Ranks.N] at hk ⊢
    omega
  refine ⟨X.fl_m, X.fl_t, fun j => ?_, fun j => ⟨hN j, hN (j + 1)⟩⟩
  exact (fills_Pj_m_add_one (Gl.Fl u w hg) j).trans (hN j).symm

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepBasisSpansLatticeFirstFactorAtP
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.LbB

section Step

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  {cmp : Type} [hcmp : Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}

theorem splAlg_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) : GlobalTheory.TwV.SplAlg (locJ hi t B) := by
  intro v a
  exact (X.g u w hg).spl_alg _ _ a

set_option maxHeartbeats 400000 in

theorem lbAtB_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) (hrat : FrRatJ t B) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E))
    (hL : L = reL (rankN D (i + 1) hi) Lb) : GlobalTheory.TwV.LbAtB (locJ hi t B) L := by
  rw [hL, reL_eq_map]
  exact lbAtB_of _ (locInt_locJ hi t B) (splAlg_locJ hi t B) _
    (frAtB_re (rankN D (i + 1) hi) (locJ hi t B) Lb B rfl (fun v => t.fr _ ((X.g u w hg).pl v).2)
      (fun v tt => t.fr_lat _ _ tt) (fun v => hrat _ _))

end Step

theorem lbAtB_inTw : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) j hj β, GlobalTheory.TwV.LbAtB (((Z.inTw Fl ht Gt).at' j hj).st.loc β) (((Z.inTw Fl ht Gt).at' j hj).st.K β).lev.Lb := by
  intro D X0 u w hg Tw μ Z Fl ht Gt j hj β
  exact lbAtB_locJ (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B (Z.frRat Fl ht j hj β) _
    (reL_symm (rankN D (j + 1) hj) _).symm

end GlobalTheory.TwV.LbB

end
end

