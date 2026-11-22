import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0330
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0473
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0300
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0320
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0318
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnimodularBlockUpperTriangularSymmetricLevels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSplitPlaceProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

noncomputable section

namespace GlobalTheory.SplitSBProd

open Filter Topology

theorem eventually_pow_smul_mem {K M : Type} [Semiring K] [TopologicalSpace K] [AddCommMonoid M] [Module K M]
    [TopologicalSpace M] [ContinuousSMul K M] {c : K} (hc : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0))
    {C U : Set M} (hC : IsCompact C) (hU : U ∈ 𝓝 (0 : M)) : ∀ᶠ n in atTop, ∀ x ∈ C, c ^ n • x ∈ U := by
  have h1 : ∀ᶠ a in 𝓝 (0 : K), ∀ x ∈ C, a • x ∈ U := by
    apply hC.eventually_forall_of_forall_eventually
    intro x _
    have hc' : Continuous fun z : K × M => z.1 • z.2 := continuous_smul
    apply hc'.continuousAt.eventually_mem
    simpa using hU
  exact hc.eventually h1

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nat_pow_tendsto_zero : ∃ p : ℕ, 0 < p ∧ Tendsto (fun n : ℕ => (p : k) ^ n) atTop (𝓝 0) := by
  refine ⟨ringChar 𝓀[k], Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite 𝓀[k] _),
    GlobalTheory.LocalTraceSum.tendsto_pow ?_⟩
  have := (residue_eq_zero_iff_lt ((ringChar 𝓀[k] : ℕ) : 𝒪[k])).1
    (by rw [map_natCast]; exact ringChar.Nat.cast_ringChar)
  simpa using this

end Local

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem down_eq (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : WO S T) :
    (ofSplit q).down FS FT x = FT.γ * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr * FS.β := rfl

theorem down_add (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x y : WO S T) :
    (ofSplit q).down FS FT (x + y) = (ofSplit q).down FS FT x + (ofSplit q).down FS FT y := by
  rw [down_eq, down_eq, down_eq]
  have : ((x + y : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr =
      (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr + (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr := by
    ext i j; simp
  rw [this, Matrix.mul_add, Matrix.add_mul]

theorem down_nsmul (q : GlobalTheory.FinPl.SplitPt D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (n : ℕ) (x : WO S T) :
    (ofSplit q).down FS FT (n • x) = n • (ofSplit q).down FS FT x := by
  rw [down_eq, down_eq]
  have : ((n • x : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr =
      n • (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr := by
    ext i j; simp
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.SplitSBProd

namespace GlobalTheory.SplitSBProd

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {S T : HSp D}

theorem exists_den_pr (q : GlobalTheory.FinPl.SplitPt D k) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : ΛS.FG) (hT : ΛT.FG) :
    ∃ M : ℕ, 0 < M ∧ ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∀ i j, (M : k) * q.pr (u i j) ∈ 𝒪[k] := by
  obtain ⟨M, hM, h⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS hT
  refine ⟨M, hM, fun u hu i j => ?_⟩
  have hfe : finPart D q.e ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, q.split.1])
  have hu' := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ q.e hfe u hu
  have h1 := h _ hu' i j
  have h2 : finPart D (q.e * ((M : AE D) * u i j)) ∈ intAE D := by
    apply GlobalTheory.PlaceDatum.finPart_mem_of_toEAf
    have e1 : q.e * ((M : AE D) * u i j) = (M : AE D) * (q.e • u) i j := by
      rw [Matrix.smul_apply, smul_eq_mul]; ring
    rw [e1, RingHom.map_mul, map_natCast]; exact h1
  have e2 : (M : k) * q.pr (u i j) = q.pr ((M : AE D) * u i j) := by rw [map_mul, map_natCast]
  rw [e2, q.int_iff, q.sec_pr]
  exact h2

theorem toEAf_mem_of_pr (q : GlobalTheory.FinPl.SplitPt D k) {x : AE D} (hx : q.pr x ∈ 𝒪[k]) :
    toEAf D (q.e * x) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  apply GlobalTheory.IdemRes.toEAf_mem_of_finPart
  rw [← q.sec_pr]
  exact (q.int_iff _).1 hx

end GlobalTheory.SplitSBProd

namespace GlobalTheory.SplitSBProd

set_option maxHeartbeats 1600000 in

theorem isSBHalf_splitProd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ e : AE D, e * e = e → q.e * e = q.e → ∀ Ω : WO S T → ℂ, IsSBHalf (e - q.e) (latO S T ΛS ΛT fun _ => True) Ω → ∀ Φ : SB (Matrix Y Y' k), IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T => if IsHalf e x then Φ.1 ((ofSplit q).down FS FT x) * Ω ((1 - q.e) • x) else 0) := by
  intro D k _ _ _ _ q Y Y' _ _ _ _ S T FS FT ΛS ΛT hS hT e he hqe Ω hΩ Φ
  obtain ⟨-, kΩ, hkΩ, hΩinv, hΩsup⟩ := hΩ
  obtain ⟨M, hM, hMden⟩ := exists_den_pr (S := S) (T := T) q hS.fg hT.fg
  obtain ⟨K₀, hK₀, hK₀mem⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO hS hT
  obtain ⟨p, hp, hpt⟩ := exists_nat_pow_tendsto_zero (k := k)
  have hU := GlobalTheory.HalfCoordSB.eventually_invariant Φ.2.1 Φ.2.2
  have hCa : IsCompact ((fun A : Matrix (Fin T.rank) (Fin S.rank) k => FT.γ * A * FS.β) ''
      {A | ∀ i j, A i j ∈ 𝒪[k]}) :=
    GlobalTheory.SplitFlip.isCompact_intMatrix.image (by fun_prop)
  have hCb : IsCompact ((fun z : Matrix Y Y' k => FT.β * z * FS.γ) '' tsupport Φ.1) :=
    Φ.2.2.isCompact.image (by fun_prop)
  obtain ⟨N, hNa, hNb⟩ := ((eventually_pow_smul_mem hpt hCa hU).and
    (eventually_pow_smul_mem hpt hCb (GlobalTheory.SplitFlip.isOpen_intMatrix.mem_nhds fun i j => zero_mem _))).exists
  have hqe1 : e * q.e = q.e := by rw [mul_comm]; exact hqe
  have hqq : q.e * q.e = q.e := q.split.1
  have h1e : finPart D (1 - q.e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by
    rw [← RingHom.map_mul, sub_mul, one_mul, mul_sub, mul_one, hqq, sub_self, sub_zero])

  have hinvΦ : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∀ (j : ℕ) x, Φ.1 (x + j • ((p ^ N * M) • (ofSplit q).down FS FT u)) = Φ.1 x := by
    intro u hu j
    have hw : ∀ y, Φ.1 (y + (p ^ N * M) • (ofSplit q).down FS FT u) = Φ.1 y := by
      have := hNa _ ⟨M • (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr, fun i j => by
        rw [Matrix.smul_apply, Matrix.map_apply, nsmul_eq_mul]; exact hMden u hu i j, rfl⟩
      dsimp only [Set.mem_setOf_eq] at this
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Matrix.mul_smul, Matrix.smul_mul, ← down_eq, ← mul_smul] at this
      exact this
    induction j with
    | zero => intro x; rw [zero_smul, add_zero]
    | succ j ih => intro x; rw [succ_nsmul, ← add_assoc, hw, ih]

  have hsupp : ∀ t : WO S T, Φ.1 ((ofSplit q).down FS FT t) ≠ 0 →
      K₀ • ((p ^ N) • (q.e • t)) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
        (fun _ => True) := by
    intro t hΦt
    have hint := hNb _ ⟨_, subset_tsupport _ hΦt, by
      simp only [down_eq, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
      rw [← Matrix.mul_assoc, FT.βγ, Matrix.one_mul]⟩
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hint
    refine hK₀mem _ (Matrix.ext fun i j => ?_) fun i j => ?_
    · simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast,
        GlobalTheory.SplitScalar.infPart_splitIdem q.split, zero_mul, mul_zero, Matrix.zero_apply]
    · have hx : q.pr ((p ^ N) • t i j) ∈ 𝒪[k] := by
        have := hint i j
        rw [map_nsmul]; exact this
      have e1 : ((p ^ N) • (q.e • t)) i j = q.e * ((p ^ N) • t i j) := by
        change (p ^ N) • (q.e * t i j) = _
        rw [nsmul_eq_mul, nsmul_eq_mul, mul_left_comm]
      rw [e1]
      exact toEAf_mem_of_pr q hx
  refine ⟨fun t ht => ?_, kΩ * K₀ * (p ^ N * M), Nat.mul_pos (Nat.mul_pos hkΩ hK₀) (Nat.mul_pos (pow_pos hp N) hM), fun u hu hue t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (if_neg h)
  · have hKu : IsHalf e ((kΩ * K₀ * (p ^ N * M)) • u) := GlobalTheory.HalfCoordSB.isHalf_nsmul hue _
    dsimp only
    by_cases ht : IsHalf e t
    · rw [if_pos ht, if_pos (GlobalTheory.HalfCoordSB.isHalf_add ht hKu)]
      have hΦe : Φ.1 ((ofSplit q).down FS FT (t + (kΩ * K₀ * (p ^ N * M)) • u)) =
          Φ.1 ((ofSplit q).down FS FT t) := by
        rw [down_add, down_nsmul, mul_smul]
        exact hinvΦ u hu _ _
      set v := (K₀ * (p ^ N * M)) • ((1 - q.e) • u) with hv
      have hvΛ : v ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
        nsmul_mem (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ h1e u hu) _
      have hvh : IsHalf (e - q.e) v := fun i j => by
        rw [hv, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
        have hfac : (e - q.e) * (1 - q.e) = e - q.e := by
          rw [mul_sub, mul_one, sub_mul, hqe1, hqq, sub_self, sub_zero]
        have hx2 : (e - q.e) * u i j = (1 - q.e) * u i j := by rw [sub_mul, sub_mul, one_mul, hue i j]
        rw [mul_left_comm, ← mul_assoc (e - q.e), hfac, hx2]
      have hΩe : Ω ((1 - q.e) • (t + (kΩ * K₀ * (p ^ N * M)) • u)) = Ω ((1 - q.e) • t) := by
        have e2 : (1 - q.e) • (t + (kΩ * K₀ * (p ^ N * M)) • u) = (1 - q.e) • t + kΩ • v := by
          rw [hv, smul_add, smul_comm (1 - q.e) (kΩ * K₀ * (p ^ N * M)) u, mul_assoc kΩ, mul_smul]
        rw [e2]
        exact hΩinv v hvΛ hvh _
      rw [hΦe, hΩe]
    · have hn : ¬ IsHalf e (t + (kΩ * K₀ * (p ^ N * M)) • u) := fun h =>
        ht (by simpa using GlobalTheory.HalfCoordSB.isHalf_sub h hKu)
      rw [if_neg ht, if_neg hn]
  · dsimp only at ht
    have hh : IsHalf e t := by
      by_contra h
      exact ht (if_neg h)
    rw [if_pos hh] at ht
    have hΦt : Φ.1 ((ofSplit q).down FS FT t) ≠ 0 := left_ne_zero_of_mul ht
    have hΩt : Ω ((1 - q.e) • t) ≠ 0 := right_ne_zero_of_mul ht
    have e3 : t = q.e • t + (1 - q.e) • t := by rw [← add_smul, add_sub_cancel, one_smul]
    have e4 : kΩ * K₀ * (p ^ N * M) = (kΩ * M) * (K₀ * p ^ N) := by ring
    have e5 : kΩ * K₀ * (p ^ N * M) = (K₀ * (p ^ N * M)) * kΩ := by ring
    rw [e3, nsmul_add]
    refine add_mem ?_ ?_
    · rw [e4, mul_smul, mul_smul K₀]
      exact nsmul_mem (hsupp t hΦt) _
    · rw [e5, mul_smul]
      exact nsmul_mem (hΩsup _ hΩt) _

end GlobalTheory.SplitSBProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ItOnto
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin maxCpt)
open GlobalTheory.Chain.IoLift

theorem kfin_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ = kFin M τ := Submodule.span_eq (kFin M τ)

theorem span_le_range {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : KSm M) :
    Submodule.span ℂ {w : SmT M | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧
      w = PiTensorProduct.tprod ℂ v} ≤ LinearMap.range (inclK h) := by
  rw [Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨PiTensorProduct.tprod ℂ fun τ => ⟨(v τ : M.H τ), (kfin_eq M τ) ▸ hv τ⟩, ?_⟩
  rw [inclK_tprod]

theorem range_le_span {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : KSm M) (y : KT M) :
    inclK h y ∈ Submodule.span ℂ {w : SmT M | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧
      w = PiTensorProduct.tprod ℂ v} := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    rw [map_smul, inclK_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => (kfin_eq M τ).symm ▸ (u τ).2, rfl⟩)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem kfinSpan_le_span_it : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsInfFam θ → IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It → (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}) ≤ Submodule.span ℂ {w | ∃ P, ∃ v ∈ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v}), w = It P v} := by
  intro hD hH D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt
  choose hs a ha hirr using fun τ => GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible hH D V S M τ
  have h : KSm M := hs
  have h' : KSm M' := fun τ => (GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible hH D W S' M' τ).1
  have hval := GlobalTheory.T.real_intertwiner_values_kFinite D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt
  have inj := inclK_injective h
  obtain ⟨I, hI⟩ : ∃ I : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] KT M,
      ∀ φ y, inclK h (I φ y) = It φ (inclK h' y) := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 inj)
    refine ⟨(It.compl₂ (inclK h')).compr₂ g, fun φ y => ?_⟩
    obtain ⟨z, hz⟩ := span_le_range M h (hval φ (inclK h' y))
    change inclK h (g (It φ (inclK h' y))) = _
    rw [← hz, ← LinearMap.comp_apply g, hg, LinearMap.id_apply]
  obtain ⟨χS, χT, hω, hexp⟩ := hW
  have hL := fun τ => GlobalTheory.T.lieAction_fockOperators_scalars_trace D V W (Fr.ofModel M) (Fr.ofModel M') θ ψ χS χT ω f τ (aS τ) (aT τ) hθ hω
    (hexp τ).1 (hexp τ).2 (isVacF_of_isVacVec hf)
  have hstep : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ, ∃ φ', ∀ y, intersection_update_fsHerm_neg_one τ (a τ X) (I φ y) = I φ' y := by
    intro τ X hX φ
    obtain ⟨φ', hd⟩ : ∃ φ', ∀ v, DerT M τ X (It φ v) (It φ' v) := ⟨_, hIt.eqg τ X hX φ _ ((hL τ).1 X hX φ)⟩
    refine ⟨φ', fun y => inj ?_⟩
    have e := hd (inclK h' y)
    rw [← hI] at e
    rw [hI]
    exact derT_unique ((GlobalTheory.Chain.IoLift.FinTensor.kFinTensor D V S M τ h).2.1 _ (ha τ) X hX _) e
  obtain ⟨N, hNd⟩ : ∃ N : Submodule ℂ (KT M), N = Submodule.span ℂ {x | ∃ φ y, I φ y = x} := ⟨_, rfl⟩
  have hN : ∀ τ (X : lieAt V τ), ∀ x ∈ N, intersection_update_fsHerm_neg_one τ (a τ X) x ∈ N := by
    intro τ X x hx
    rw [hNd] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, y, rfl⟩ := hx
      obtain ⟨φ', hφ'⟩ := hstep τ X X.2 φ
      exact Submodule.subset_span ⟨φ', y, (hφ' y).symm⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have h0 : N ≠ ⊥ := by
    obtain ⟨φ, y, hne⟩ := GlobalTheory.T.exists_realIntertwiner_ne_zero_KFinite_tensor hH D V W S S' M M' θ ω _ It hIt h'
    intro e
    refine hne ?_
    have : I φ y ∈ N := hNd ▸ Submodule.subset_span ⟨φ, y, rfl⟩
    rw [e, Submodule.mem_bot] at this
    rw [← hI, this, map_zero]
  have htop := GlobalTheory.T.piTensor_submodule_eq_top_of_absolutely_irreducible_stable D.what₂.Tau (fun τ => kFin M τ) (fun τ => lieAt V τ) (fun τ X => a τ X) hirr N hN h0
  intro w hw
  obtain ⟨z, rfl⟩ := span_le_range M h hw
  have hz : z ∈ N := htop ▸ Submodule.mem_top
  rw [hNd] at hz
  clear hw
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, y, rfl⟩ := hx
    exact Submodule.subset_span ⟨φ, inclK h' y, range_le_span M' h' y, (hI φ y)⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.ItOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalInvariantIntegralsSymmetricHaarSubgroups
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.HaarR
open scoped ENNReal NNReal

theorem eq_of_mass_one {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] (κ μ : Measure G) [μ.IsHaarMeasure]
    [IsFiniteMeasureOnCompacts κ] [κ.IsMulLeftInvariant] (S : Set G) (hS : μ S = 1) (hκ : κ S = 1) : κ = μ := by
  have h := Measure.isMulLeftInvariant_eq_smul κ μ
  set a := Measure.haarScalarFactor κ μ
  have h1 : (a : ℝ≥0∞) = 1 := by
    rw [h, Measure.smul_apply, hS, ENNReal.smul_def, smul_eq_mul, mul_one] at hκ
    exact hκ
  have : a = 1 := by exact_mod_cast h1
  rw [h, this, one_smul]

theorem quot_int_haar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (m : Measure (GL n k)) (G : Measure (GL (n ⊕ Fin c) k)), m.IsHaarMeasure → G.IsHaarMeasure → m (KO k n) = 1 → (c + 1 = 2 * ρ → ∀ μR : Measure (R k n c ρ), μR.IsHaarMeasure → μR {x | x.1 ∈ KO k (n ⊕ Fin c)} = 1 → μR.IsInvInvariant ∧ ∀ f z, IsQuotInt ν m G ρ f z → IsQuotIntL1 μR G f z) ∧ (1 ≤ ρ → c = 2 * ρ → ∀ μR : Measure (RFJ k n c ρ), μR.IsHaarMeasure → μR {x | x.1 ∈ KO k (n ⊕ Fin c)} = 1 → μR.IsInvInvariant ∧ ∀ f z, IsQuotIntFJ ν m G ρ f z → IsQuotIntL1 μR G f z) := by
  intro k _ _ _ _ _ _ ν hν n _ _ c ρ m G hm hG hmK
  haveI := hν.1
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : BorelSpace (GL n k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  have hKO : ∀ (S : Subgroup (GL (n ⊕ Fin c) k)), MeasurableSet {x : S | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} :=
    fun S => (GlobalTheory.SplitFlip.isOpen_KO.preimage continuous_subtype_val).measurableSet
  have hFint : ∀ F ∈ SB (GL (n ⊕ Fin c) k), Integrable F G := fun F hF => hF.1.continuous.integrable_of_hasCompactSupport hF.2
  have hFS : ∀ (S : Subgroup (GL (n ⊕ Fin c) k)), IsClosed (S : Set (GL (n ⊕ Fin c) k)) → ∀ (μS : Measure S),
      μS.IsHaarMeasure → ∀ F ∈ SB (GL (n ⊕ Fin c) k), ∀ h, Integrable (fun r : S => F (r * h)) μS := by
    intro S hS μS _ F hF h
    exact (hF.1.continuous.comp (continuous_subtype_val.mul continuous_const)).integrable_of_hasCompactSupport
      ((hF.2.comp_homeomorph (Homeomorph.mulRight h)).comp_isClosedEmbedding hS.isClosedEmbedding_subtypeVal)
  refine ⟨fun hc μR hR hRK => ?_, fun h1 hc μR hR hRK => ?_⟩
  · have h1 : 1 ≤ ρ := by omega
    have h2 : ρ ≤ c := by omega
    obtain ⟨hNc, hcl, hNH, -, -⟩ := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c ρ h1 h2 ν
    haveI : LocallyCompactSpace (N k n c ρ) := hNc.locallyCompactSpace
    haveI := hNH
    haveI : LocallyCompactSpace (R k n c ρ) := hcl.locallyCompactSpace
    haveI := hR
    haveI := hm
    haveI := GlobalTheory.T.levyProductMap_haar_isMulLeftInvariant k n c ρ h1 h2 ν hν.1 m hm
    haveI := GlobalTheory.T.levyProductMap_haar_finiteOnCompacts k n c ρ h1 h2 ν hν.1 m hm
    have hmeas : Measurable (prodR (k := k) (n := n) (c := c) ρ) :=
      (Continuous.subtype_mk ((GlobalTheory.RootEx.QuotStep.continuous_embX.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)) _).measurable
    have hκ : (m.prod (volN ν n c ρ)).map (prodR ρ) = μR := by
      refine eq_of_mass_one _ μR _ hRK ((Measure.map_apply hmeas (hKO (R k n c ρ))).trans ?_)
      rw [GlobalTheory.T.levyProductMap_preimage_integralGL, Measure.prod_prod, hmK, GlobalTheory.T.rootExchangeUnipotentHaar_integralPoints_eq_one k n c ρ h1 h2 ν hν, one_mul]
    haveI : μR.IsMulRightInvariant := GlobalTheory.LevelUnimod.unimodular k n c ρ (fun i => i.val + 1)
      (fun i => by simp [Fin.rev]; omega) (R k n c ρ)
      (GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff k n c ρ).1 μR hR
    refine ⟨GlobalTheory.SemiHaar.invInv_of_rightInv μR, ?_⟩
    rintro f z ⟨F, hF, hf, hz⟩
    have hi := hFS _ hcl μR hR F hF
    refine ⟨F, hFint F hF, hi, fun h => ?_, hz⟩
    have hc' : Continuous fun r : R k n c ρ => F (r * h) :=
      hF.1.continuous.comp (continuous_subtype_val.mul continuous_const)
    have hp : Integrable (fun q => F ((prodR (k := k) (n := n) (c := c) ρ q : GL (n ⊕ Fin c) k) * h)) (m.prod (volN ν n c ρ)) := by
      have := hi h
      rw [← hκ] at this
      exact (integrable_map_measure hc'.aestronglyMeasurable hmeas.aemeasurable).1 this
    rw [hf h, ← hκ, integral_map hmeas.aemeasurable hc'.aestronglyMeasurable, integral_prod _ hp]
    rfl
  · have h2 : ρ < c := by omega
    obtain ⟨hNc, -, hNH, -, -⟩ := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c (ρ + 1) (by omega) (by omega) ν
    haveI : LocallyCompactSpace (N k n c (ρ + 1)) := hNc.locallyCompactSpace
    haveI := hNH
    haveI := hm
    haveI := hR
    have hmem := (GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff k n c ρ).2 h1 h2
    have hcl : IsClosed (RFJ k n c ρ : Set (GL (n ⊕ Fin c) k)) := by
      have e : (RFJ k n c ρ : Set (GL (n ⊕ Fin c) k)) = ⋂ r : n ⊕ Fin c, ⋂ s : n ⊕ Fin c,
          {g : GL (n ⊕ Fin c) k | (r.isRight ∨ s.isRight) →
            Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
              Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r →
            g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
        ext g; simp only [SetLike.mem_coe, hmem, Set.mem_iInter, Set.mem_setOf_eq]
      rw [e]
      refine isClosed_iInter fun r => isClosed_iInter fun s => ?_
      by_cases hrs : (r.isRight ∨ s.isRight) ∧ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
          Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r
      · have : {g : GL (n ⊕ Fin c) k | (r.isRight ∨ s.isRight) →
            Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
              Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r →
            g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} =
            {g : GL (n ⊕ Fin c) k | g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
          ext g; simp only [Set.mem_setOf_eq]; exact ⟨fun h => h hrs.1 hrs.2, fun h _ _ => h⟩
        rw [this]
        exact isClosed_eq (GlobalTheory.RootEx.VolN.continuous_entry r s) continuous_const
      · have : {g : GL (n ⊕ Fin c) k | (r.isRight ∨ s.isRight) →
            Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
              Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r →
            g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} = Set.univ := by
          ext g; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact fun a b => absurd ⟨a, b⟩ hrs
        rw [this]; exact isClosed_univ
    haveI : LocallyCompactSpace (RFJ k n c ρ) := hcl.locallyCompactSpace
    haveI := GlobalTheory.T.isMulLeftInvariant_map_levyProductMapToFourierJacobi k n c ρ h1 h2 ν hν.1 m hm
    haveI := GlobalTheory.T.fourierJacobiProductMap_haar_finiteOnCompacts k n c ρ h1 h2 ν hν.1 m hm
    have hmeas : Measurable (prodRFJ (k := k) (n := n) (c := c) ρ) :=
      (Continuous.subtype_mk (((GlobalTheory.RootEx.QuotStep.continuous_embX.comp (continuous_fst.comp continuous_fst)).mul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).mul
        ((GlobalTheory.RootEx.QuotStep.continuous_colE (ρ + 1)).comp continuous_snd)) _).measurable
    have hκ : ((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)).map (prodRFJ ρ) = μR := by
      refine eq_of_mass_one _ μR _ hRK ((Measure.map_apply hmeas (hKO (RFJ k n c ρ))).trans ?_)
      have hpi : {β : n → k | ∀ i, β i ∈ 𝒪[k]} = Set.univ.pi fun _ : n => (𝒪[k] : Set k) := by
        ext β; simp
      rw [GlobalTheory.T.levyProductMapToFourierJacobi_preimage_integralGL k n c ρ h2, Measure.prod_prod, Measure.prod_prod, hmK, GlobalTheory.T.rootExchangeUnipotentHaar_integralPoints_eq_one k n c (ρ + 1) (by omega) (by omega) ν hν, hpi,
        Measure.pi_pi, hν.2]
      simp
    haveI : μR.IsMulRightInvariant := GlobalTheory.LevelUnimod.unimodular k n c (2 * ρ + 1) (fun i => 2 * (i.val + 1))
      (fun i => by simp [Fin.rev]; omega) (RFJ k n c ρ) hmem μR hR
    refine ⟨GlobalTheory.SemiHaar.invInv_of_rightInv μR, ?_⟩
    rintro f z ⟨F, hF, hf, hz⟩
    have hi := hFS _ hcl μR hR F hF
    refine ⟨F, hFint F hF, hi, fun h => ?_, hz⟩
    have hc' : Continuous fun r : RFJ k n c ρ => F (r * h) :=
      hF.1.continuous.comp (continuous_subtype_val.mul continuous_const)
    have hp : Integrable (fun q => F ((prodRFJ (k := k) (n := n) (c := c) ρ q : GL (n ⊕ Fin c) k) * h))
        ((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)) := by
      have := hi h
      rw [← hκ] at this
      exact (integrable_map_measure hc'.aestronglyMeasurable hmeas.aemeasurable).1 this
    rw [hf h, ← hκ, integral_map hmeas.aemeasurable hc'.aestronglyMeasurable, integral_prod _ hp,
      integral_prod _ hp.integral_prod_left]
    rfl

end GlobalTheory.HaarR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalCongruenceRealPointsIntegrationHeightOnStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_realPoints_integration_heightOne : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Formalism.L2.DIV.IsFrame β (frameLat A) → ∀ m : Measure (GA D A), m.IsHaarMeasure → MeasurableSet (prinInf A β Z) ∧ prinInf A β Z ⊆ openOff A (frameLat A) (under Z) ∧ (∀ g ∈ prinInf A β Z, hgtL A (frameLat A) a g = 1) ∧ ∃ mR : Measure (GinfC A), mR.IsHaarMeasure ∧ ∀ F : GA D A → ℂ, Continuous F → (∀ (b : GinfC A), ∀ κ ∈ prin A β Z, F ((b : GA D A) * κ) = F b) → ∫ g in prinInf A β Z, F g ∂m = ∫ b : GinfC A, F b ∂mR := by
  first | exact @GlobalTheory.Core.Rk.PrinMeas.prinInf_props | exact GlobalTheory.Core.Rk.PrinMeas.prinInf_props | (intros; apply GlobalTheory.Core.Rk.PrinMeas.prinInf_props <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualImageAdelicPointWittCoreStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_image_adelicPoint_wittCore : ∀ (D : D7) (S : HSp D) (L : Lat S), IsSelfDualC S L → (∀ g : GA D S, ∃ M : Lat S, IsSelfDualC S M ∧ ∀ P : Pl D → Prop, Moves S g L M P) ∧ ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L₀ M₀ : Lat S₀) (M : Lat S) (γ : GA D S₀) (v : Pl D), MonoAt d L L₀ v → Moves S₀ γ L₀ M₀ (· = v) → Moves S (d.emb0 γ) L M (· = v) → MonoAt d M M₀ v := by
  first | exact @GlobalTheory.FinPl.GlobImage.glob | exact GlobalTheory.FinPl.GlobImage.glob | (intros; apply GlobalTheory.FinPl.GlobImage.glob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatioStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_eq_zero_of_rootOfSUnitRatio : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (w : HeightOneSpectrum (𝓞 K)) (S : ℕ → Prop) (x y : ℂ), GlobalTheory.Fam.UnitRatio S x y → (∀ p : ℕ, p.Prime → S p → (p : 𝓞 K) ∉ w.asIdeal) → ∀ a : K, σ a = x / y → Formalism.DivisionValues.vw w a = 0 := by
  first | exact @GlobalTheory.Fam.vw_eq_zero_of_unitRatio | exact GlobalTheory.Fam.vw_eq_zero_of_unitRatio | (intros; apply GlobalTheory.Fam.vw_eq_zero_of_unitRatio <;> assumption)
end

