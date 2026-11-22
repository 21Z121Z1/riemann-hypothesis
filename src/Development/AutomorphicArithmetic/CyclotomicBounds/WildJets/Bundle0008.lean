import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0591
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0597
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0605
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0623
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0007
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0002
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LogSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RealTop
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0004

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsTer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.toStd :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ) (X : Node), DefNode D.R.m X → ∀ l : ℕ, l.Prime → ∀ x : FinPt G X,
      ∃ (r : FinPt G X) (U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E), GlobalTheory.RatMoveJets.RatCoord _ (S.N.fr X) r U ∧
        latAt S X (r * x) = SDLat.smulLat U.1 (latAt S X x) ∧ Formalism.MainNotions.TaylorLogMetric.EqAt D l (latAt S X (r * x)) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) := by
  intro D T L sc G W S X hX l hl x
  have erefl : ∀ {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Formalism.MainNotions.TaylorLogMetric.EqAt D l L L := fun L =>
    ⟨1, Nat.coprime_one_left l, fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩
  have esymm : ∀ {N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)},
      Formalism.MainNotions.TaylorLogMetric.EqAt D l L L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D l L₁ L := fun ⟨s, hs, h1, h2⟩ => ⟨s, hs, h2, h1⟩
  have etrans : ∀ {N : ℕ} {L L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)},
      Formalism.MainNotions.TaylorLogMetric.EqAt D l L L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D l L₁ L₂ → Formalism.MainNotions.TaylorLogMetric.EqAt D l L L₂ := by
    intro N L L₁ L₂ h h'
    obtain ⟨s, hs, h1, h2⟩ := h
    obtain ⟨t, ht, h1', h2'⟩ := h'
    refine ⟨t * s, Nat.Coprime.mul_left ht hs, fun x hx => ?_, fun x hx => ?_⟩
    · have := h1' _ (h1 x hx)
      rwa [smul_smul, ← Nat.cast_mul] at this
    · have := h2 _ (h2' x hx)
      rwa [smul_smul, ← Nat.cast_mul, mul_comm] at this
  obtain ⟨r, s, k, hr, hs, hk, e⟩ := GlobalTheory.T.exists_rational_split_stabilizer_decomposition (G.V X) (S.N.fr X) (∏ q ∈ ({l} : Finset ℕ), q)
    (by simpa using hl.pos) (x * S.N.u X)
  have hs' := GlobalTheory.T.mem_splitPlaceFinitePointsOffPrimes_of_supported _ {l} s hs
  have hB := GlobalTheory.T.latticeOf_stabiliser_mul_inv_eq_standardLattice S X hX k hk
  have key : ∀ s' ∈ GlobalTheory.MovedKappaEx.splitOff (G.V X) {l}, ∀ y : FinPt G X,
      Formalism.MainNotions.TaylorLogMetric.EqAt D l (latAt S X (s' * y)) (latAt S X y) := by
    intro s' hs'
    induction hs' using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨e, he, hoff, hsupp⟩ := hg
      exact fun y => GlobalTheory.T.vertexLattice_eqAt_mul_splitSupported S X hX l hl e he (hoff l (Finset.mem_singleton_self l)) g y hsupp
    | one => exact fun y => by rw [one_mul]; exact erefl _
    | mul a b _ _ ha hb => exact fun y => by rw [mul_assoc]; exact etrans (ha (b * y)) (hb y)
    | inv a _ ha =>
      intro y
      have := ha (a⁻¹ * y)
      rw [mul_inv_cancel_left] at this
      exact esymm this
  have h1 := key s hs' (k * (S.N.u X)⁻¹)
  rw [hB] at h1
  have hr' : GlobalTheory.MovedKappaEx.RatFin (G.V X) r⁻¹ := by
    obtain ⟨γ, hγ, hγr⟩ := hr
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [map_inv, hγr, Subgroup.coe_inv, map_inv]
  obtain ⟨U, hU⟩ := GlobalTheory.RatMoveJets.exists_unitary_ratCoord S X hX r⁻¹ hr'
  refine ⟨r⁻¹, U, hU, GlobalTheory.T.vertexLatticeCoords_rationalPoint_mul_eq_coordMatrix S X _ U hU x, ?_⟩
  have hx : r⁻¹ * x = s * (k * (S.N.u X)⁻¹) := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← e, mul_inv_cancel_right]
  rw [hx]
  exact h1
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LossOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem expAdd {S S' : Finset ℕ} {f g : ℕ → ℝ} {a b : ℝ} (h : GlobalTheory.NormSum.Exponents S f a)
    (h' : GlobalTheory.NormSum.Exponents S' g b) : GlobalTheory.NormSum.Exponents (S ∪ S') (fun l => f l + g l) (a + b) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := h'
  refine ⟨fun l hl => (Finset.mem_union.1 hl).elim (h1 l) (g1 l), fun l => add_nonneg (h2 l) (g2 l), fun l hl => ?_, ?_⟩
  · rw [Finset.mem_union, not_or] at hl
    dsimp only
    rw [h3 l hl.1, g3 l hl.2, add_zero]
  · simp only [add_mul, Finset.sum_add_distrib]
    rw [← Finset.sum_subset (Finset.subset_union_left (s₁ := S) (s₂ := S')) (fun l _ hl => by rw [h3 l hl, zero_mul]),
      ← Finset.sum_subset (Finset.subset_union_right (s₁ := S) (s₂ := S')) (fun l _ hl => by rw [g3 l hl, zero_mul])]
    exact add_le_add h4 g4

private theorem expMul {S : Finset ℕ} {f : ℕ → ℝ} {a c : ℝ} (hc : 0 ≤ c) (h : GlobalTheory.NormSum.Exponents S f a) :
    GlobalTheory.NormSum.Exponents S (fun l => c * f l) (c * a) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun l => mul_nonneg hc (h2 l), fun l hl => ?_, ?_⟩
  · dsimp only
    rw [h3 l hl, mul_zero]
  · simp only [mul_assoc, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h4 hc

private theorem expMono {S : Finset ℕ} {f : ℕ → ℝ} {a b : ℝ} (h : GlobalTheory.NormSum.Exponents S f a) (hab : a ≤ b) :
    GlobalTheory.NormSum.Exponents S f b := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans hab⟩

private theorem expOne (d : ℕ) : GlobalTheory.NormSum.Exponents (({d} : Finset ℕ).filter Nat.Prime)
    (fun l => if l.Prime ∧ l = d then 1 else 0) (Real.log d) := by
  refine ⟨fun l hl => (Finset.mem_filter.1 hl).2, fun l => by dsimp only; split_ifs <;> norm_num, fun l hl => ?_, ?_⟩
  · exact if_neg fun h => hl (Finset.mem_filter.2 ⟨Finset.mem_singleton.2 h.2, h.1⟩)
  · rw [Finset.filter_singleton]
    split_ifs with h
    · simp [h]
    · simpa using Real.log_natCast_nonneg d

private theorem expLog {y c : ℝ} (hy : 0 ≤ y) (hc : 0 ≤ c) (hyc : Real.log y ≤ c) :
    GlobalTheory.NormSum.Exponents ((Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime)
    (fun l => if l.Prime ∧ (l : ℝ) ≤ y then Real.logb l y else 0) (y * c) := by
  have hm : ∀ l : ℕ, l ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime ↔ l.Prime ∧ (l : ℝ) ≤ y := fun l => by
    rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hy, and_comm]
  refine ⟨fun l hl => (Finset.mem_filter.1 hl).2, fun l => ?_, fun l hl => if_neg fun h => hl ((hm l).2 h), ?_⟩
  · dsimp only
    split_ifs with h
    · exact Real.logb_nonneg (by exact_mod_cast h.1.one_lt) (le_trans (by exact_mod_cast h.1.one_lt.le) h.2)
    · exact le_rfl
  · dsimp only
    rw [Finset.sum_congr (g := fun l : ℕ => Real.logb l y * Real.log l) rfl fun l hl => by rw [if_pos ((hm l).1 hl)]]
    rcases le_or_gt 1 y with h | h
    · exact (UpperTheory.WildA.logSum y h).trans (mul_le_mul_of_nonneg_left hyc hy)
    · rw [Nat.floor_eq_zero.2 h]
      have e : (Finset.range (0 + 1)).filter Nat.Prime = ∅ := by decide
      rw [e, Finset.sum_empty]
      exact mul_nonneg hy hc

theorem UpperTheory.WildA.lossOne :
    ∀ C1 : ℝ, 0 < C1 → ∃ C0 : ℝ, 0 < C0 ∧ ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → HostHyp D → sc.cGap = 1 →
      ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ → ∃ (S' : Finset ℕ) (h : ℕ → ℝ),
        GlobalTheory.NormSum.Exponents S' h (C0 * D.R.f * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + sig G) * large₂.sc.b) ∧
        ∀ p : GlobalTheory.ChiGrid.Pair T, DefPair D.R.m p → ∀ l : ℕ, l.Prime →
          C1 * GlobalTheory.SumSize.TopInt.kerLoss G δ C1 large₂.sc.b p.small p.big l (depL G l) ≤ h l := by
  intro C1 hC1
  refine ⟨C1 * (26 + C1 * (|Real.log C1| + 1)), by positivity, ?_⟩
  intro D T L sc G large₂ hS hH hc S δ hδ
  obtain ⟨-, -, hN, hf, hm, -, hrd, h12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS
  have hNR : (1 : ℝ) ≤ bigN D := by exact_mod_cast hN
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hb0 : 0 < large₂.sc.b := by linarith
  have hL : 1 ≤ Real.log large₂.sc.b := by
    rw [Real.le_log_iff_exp_le hb0]
    linarith [Real.exp_one_lt_d9]
  have hd : Real.log D.host.d ≤ Real.log large₂.sc.b := by
    have hb := hS.2.2.2.2.2.1
    have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
    have hN1 : 1 ≤ D.R.N D.R.m := by simp only [Formalism.BasicNotions.Ranks.N]; omega
    have hN1R : (1 : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast hN1
    have h1 : (1 : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hfR) (one_le_pow₀ hN1R)
    have h2 : (D.host.d : ℝ) ≤ large₂.sc.b := (le_mul_of_one_le_left (Nat.cast_nonneg _) h1).trans hb
    rcases Nat.eq_zero_or_pos D.host.d with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]
      linarith
    · exact Real.log_le_log (by exact_mod_cast h) h2
  have hsig : 0 ≤ sig G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hy : Real.log (C1 * large₂.sc.b) ≤ (|Real.log C1| + 1) * Real.log large₂.sc.b := by
    rw [Real.log_mul hC1.ne' hb0.ne']
    nlinarith [le_abs_self (Real.log C1), abs_nonneg (Real.log C1)]
  obtain ⟨S2, h2⟩ := UpperTheory.WildA.depSum (G := G)
  have h0 : GlobalTheory.NormSum.Exponents S δ (Real.log D.host.rdE) := ⟨hδ.1, hδ.2.1, hδ.2.2.1, hδ.2.2.2.1⟩
  have h3 := expLog (y := C1 * large₂.sc.b) (by positivity) (by positivity) hy
  have h4 := expMul hC1.le (expAdd
    (expMul (c := 13 * D.R.f * bigN D * large₂.sc.b) (by positivity) (expAdd (expAdd h0 (expOne D.host.d)) h2))
    (expMul (c := (D.R.f : ℝ) * (bigN D : ℝ) ^ 2) (by positivity) h3))
  refine ⟨_, _, expMono h4 ?_, fun p hp l hl => ?_⟩
  · set Lb := Real.log large₂.sc.b
    set K := |Real.log C1| + 1 with hK
    have hK0 : 0 ≤ K := by positivity
    have e1 : (13 * D.R.f * bigN D * large₂.sc.b : ℝ) * (Real.log D.host.rdE + Real.log D.host.d + sig G) ≤
        (13 * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b) * (2 * (Lb + sig G)) := by
      refine (mul_le_mul_of_nonneg_left (b := _) (c := 2 * (Lb + sig G)) (by linarith) (by positivity)).trans ?_
      have : (bigN D : ℝ) ≤ (bigN D : ℝ) ^ 2 := by nlinarith
      gcongr
    have e2 : (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (C1 * large₂.sc.b * (K * Lb)) ≤
        (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (C1 * large₂.sc.b * (K * (Lb + sig G))) := by
      gcongr
      linarith
    refine (mul_le_mul_of_nonneg_left (add_le_add e1 e2) hC1.le).trans (le_of_eq ?_)
    ring
  · refine mul_le_mul_of_nonneg_left ?_ hC1.le
    unfold GlobalTheory.SumSize.TopInt.kerLoss
    simp only [hl, true_and, if_true]
    refine add_le_add (mul_le_mul_of_nonneg_right (UpperTheory.WildA.kerLe (G := G) large₂ hS hH hc p hp) ?_) le_rfl
    have := hδ.2.1 l
    split_ifs <;> positivity
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.MoveTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.moveTop :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U₀ : Set T} {N : Std G U₀} (Z : Normal W N) {μ₀ : T}, L.Is μ₀ → ∀ (t t' : T) (j : ℕ), j + 1 ≤ D.R.m →
      ∀ (d : FinDatum G t (GlobalTheory.ChiGrid.Pair.top t' j)) (x r : FinPt G ((GlobalTheory.ChiGrid.Pair.top t' j)).small) (y r' : FinPt G ((GlobalTheory.ChiGrid.Pair.top t' j)).big)
        (U : Matrix.unitaryGroup (Fin (G.V ((GlobalTheory.ChiGrid.Pair.top t' j)).small).rank) D.host.E) (U' : Matrix.unitaryGroup (Fin (G.V ((GlobalTheory.ChiGrid.Pair.top t' j)).big).rank) D.host.E),
        GlobalTheory.RatMoveJets.RatCoord _ (N.fr ((GlobalTheory.ChiGrid.Pair.top t' j)).small) r U → GlobalTheory.RatMoveJets.RatCoord _ (N.fr ((GlobalTheory.ChiGrid.Pair.top t' j)).big) r' U' →
        Z.kkMap 1 d (r * x) (r' * y) ∘ₗ rhoVr (tauE D) (wt G ((GlobalTheory.ChiGrid.Pair.top t' j)).small) (Unitary.toUnits U) =
          rhoVr (tauE D) (wt G ((GlobalTheory.ChiGrid.Pair.top t' j)).big) (Unitary.toUnits U') ∘ₗ Z.kkMap 1 d x y := by
  intro D T L sc G W U₀ N Z μ₀ hL t t' j hj d x r y r' U U' hU hU'
  have hp : DefPair D.R.m (GlobalTheory.ChiGrid.Pair.top t' j : GlobalTheory.ChiGrid.Pair T) := hj
  have hω := W.om_is (GlobalTheory.ChiGrid.Pair.top t' j) hj
  obtain ⟨a, b, e₁, e₂, ha, hb, he₁, he₂⟩ := UpperTheory.WildA.expEx (G := G) hL _ hp
  obtain ⟨γ, hγ, k, hk, hrk, hρ⟩ := UpperTheory.WildA.ratReal W N.fr _ r U hU
  obtain ⟨γ', hγ', k', hk', hrk', hρ'⟩ := UpperTheory.WildA.ratReal W N.fr _ r' U' hU'
  obtain ⟨h1, h2⟩ := GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum W Z hp d (Z.hasVec_of_defPair hL hp d)
  have hB : ∀ X, DefNode D.R.m X → ∀ τ, (N.frC X τ)ᴴ * gramAt D (G.V X) τ * N.frC X τ = 1 := fun X hX τ =>
    GlobalTheory.FockJetOrigin.frame_map τ (N.fr_on X hX)
  have hF : ∀ Q, IsThetaFunO W.ψ _ _ (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q) := fun Q =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ h1 Q
  have haut : ∀ Q g h, W.ker (GlobalTheory.ChiGrid.Pair.top t' j) (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q) (γ * g) (γ' * h) =
      W.ker (GlobalTheory.ChiGrid.Pair.top t' j) (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q) g h := by
    intro Q g h
    show thetaKO (W.om (.top t' j)) (γ * g) (γ' * h) _ = thetaKO (W.om (.top t' j)) g h _
    have e : ((γ * g, γ' * h) : GA D (G.V (.top j)) × GA D (G.V (.top (j + 1)))) = (γ, γ') * (g, h) := rfl
    unfold thetaKO
    rw [e, map_mul]
    exact hω.om_aut γ hγ γ' hγ' _ (hω.om_pres _ _ (hF Q))
  let ℓ : PolF D (G.pT (GlobalTheory.ChiGrid.Pair.top t' j)).rank (G.pS (GlobalTheory.ChiGrid.Pair.top t' j)).rank →ₗ[ℂ] ℂ :=
    { toFun := fun Q => kerFin W (GlobalTheory.ChiGrid.Pair.top t' j) (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q)
        (x * N.u _) (y * N.u _)
      map_add' := fun P Q => by
        simp only [kerFin, GridData.Weil.ker, thetaKO, map_add, Pi.add_apply]
      map_smul' := fun c Q => by
        simp only [kerFin, GridData.Weil.ker, thetaKO, map_smul, Pi.smul_apply, RingHom.id_apply] }
  have key := UpperTheory.WildA.realTop (W := W) N hL t' j hj a b ha hb e₁ e₂ he₁ he₂ ℓ k hk k' hk'
  have tab : jetTab W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) (r * x * N.u _) (r' * y * N.u _) =
      fun m => GlobalTheory.FockReal.realChar W (GlobalTheory.ChiGrid.Pair.top t' j) e₁ e₂ k k' *
        ℓ (GlobalTheory.FockReal.realSubst W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) k k'
          (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.top t' j))) 1)) := by
    funext m
    rw [jetTab, kerFin, mul_assoc r, mul_assoc r', hrk, hrk', haut]
    exact GlobalTheory.FockReal.ker_fockIn_real hL W N.frC hp hB a b ha hb e₁ e₂ he₁ he₂ _ h1 h2 k hk k' hk' _ _ _
  have hid : GlobalTheory.DefStep.realAct W.θ N.fr (GlobalTheory.ChiGrid.Pair.top t' j : GlobalTheory.ChiGrid.Pair T).small k ∘ₗ
      GlobalTheory.DefStep.realAct W.θ N.fr (GlobalTheory.ChiGrid.Pair.top t' j : GlobalTheory.ChiGrid.Pair T).small k⁻¹ = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [← hρ, ← hρ', Normal.kkMap, Normal.kkMap, fockComp, fockComp, tab, key, LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.comp_assoc, LinearMap.comp_assoc, hid, LinearMap.comp_id]
  rfl
end

