import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSplitsHyperbolicPlusCore
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IwaDecomp

variable {D : D7}

theorem intAt_mul' {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact GlobalTheory.HostAdeleIso.intAE_mul_mem D ha.2 hb.2⟩

theorem intAt_zero' {v : Pl D} : (0 : AE D) ∈ intAt D (· = v) :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_add' {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a + b ∈ intAt D (· = v) :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_sum' {v : Pl D} {ι : Type} (s : Finset ι) (f : ι → AE D) (h : ∀ i ∈ s, f i ∈ intAt D (· = v)) :
    ∑ i ∈ s, f i ∈ intAt D (· = v) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact intAt_zero'
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intAt_add' (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem intAt_intCast_mul {v : Pl D} (N : ℤ) {a : AE D} (ha : a ∈ intAt D (· = v)) :
    (N : AE D) * a ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ ha.1, by rw [map_mul, map_intCast, ← zsmul_eq_mul]; exact zsmul_mem ha.2 N⟩

theorem intAt_natCast_mul {v : Pl D} (n : ℕ) {a : AE D} (ha : a ∈ intAt D (· = v)) :
    (n : AE D) * a ∈ intAt D (· = v) := by
  have := intAt_intCast_mul (v := v) (n : ℤ) ha
  rwa [Int.cast_natCast] at this

theorem exists_nat_incA_mul (v : Pl D) (c : D.host.E) :
    ∃ n : ℕ, 0 < n ∧ ∀ a ∈ intAt D (· = v), incA D c * ((n : AE D) * a) ∈ intAt D (· = v) := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨N, hN, hint⟩ := halg.exists_integral_multiple
  refine ⟨N.natAbs * N.natAbs, Nat.mul_pos (Int.natAbs_pos.2 hN) (Int.natAbs_pos.2 hN), fun a ha => ?_⟩
  have key : ∀ b ∈ intAt D (· = v), incA D (N • c) * b ∈ intAt D (· = v) := by
    intro b hb
    refine ⟨Ideal.mul_mem_left _ _ hb.1, ?_⟩
    rw [map_mul]
    have hc : finPart D (incA D (N • c)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (N • c) := rfl
    rw [hc]
    refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ hb.2
    refine AddSubgroup.subset_closure ⟨1, fun w => ?_, ⟨N • c, hint⟩, rfl⟩
    rw [map_one]
    exact one_mem _
  have hcast : ((N.natAbs * N.natAbs : ℕ) : AE D) = (N : AE D) * (N : AE D) := by
    have h1 : ((N.natAbs * N.natAbs : ℕ) : ℤ) = N * N := by rw [Nat.cast_mul]; exact Int.natAbs_mul_self' N
    have h2 : (((N.natAbs * N.natAbs : ℕ) : ℤ) : AE D) = ((N * N : ℤ) : AE D) := by rw [h1]
    rw [Int.cast_natCast] at h2
    rw [h2, Int.cast_mul]
  have e : incA D c * (((N.natAbs * N.natAbs : ℕ) : AE D) * a) = incA D (N • c) * ((N : AE D) * a) := by
    rw [hcast, zsmul_eq_mul, map_mul, map_intCast]
    ring
  rw [e]
  exact key _ (intAt_intCast_mul N ha)

end GlobalTheory.IwaDecomp

namespace GlobalTheory.IwaDecomp

variable {D : D7}

theorem hermAt_smul_left (S : HSp D) (t : AE D) (y x : Fin S.rank → AE D) :
    hermAt S (t • y) x = t * hermAt S y x := by
  simp only [hermAt, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hermAt_eq_dot (S : HSp D) (x y : Fin S.rank → AE D) :
    hermAt S x y = (fun i => cA D (y i)) ⬝ᵥ (gA S *ᵥ x) := by
  simp only [hermAt, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hermAt_colMul (S : HSp D) {ρ : ℕ} (M : Mx D S.rank ρ) (i : Fin ρ) (a : AE D) (z : Fin S.rank → AE D) :
    hermAt S z (colMul M i a) = cA D a * ((adj M ⬝ gA S) *ᵥ z) i := by
  simp only [hermAt, colMul, adj, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem mulVec_eq_sum_colMul {m n : ℕ} (M : Mx D m n) (a : Fin n → AE D) :
    M *ᵥ a = ∑ i, colMul M i (a i) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, colMul, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem wittCoreProjection_conjTranspose_gram_eq {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : adj d.p0 ⬝ gA S₀ = gA S ⬝ d.j0 := by
  rw [d.p0_eq, adj_mul, adj_mul, adj_adj, adj_giA, adj_gA, Matrix.mul_assoc, Matrix.mul_assoc, giA_mul_gA,
    Matrix.mul_one]

theorem adelicHermitianForm_wittCoreInclusion_left {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (y : Fin S₀.rank → AE D) (w : Fin S.rank → AE D) :
    hermAt S (d.j0 *ᵥ y) w = hermAt S₀ y (d.p0 *ᵥ w) := by
  rw [hermAt_eq_dot, hermAt_eq_dot]
  have h1 : (fun i => cA D ((d.p0 *ᵥ w) i)) = d.p0.map (cA D) *ᵥ fun i => cA D (w i) := by
    funext i
    exact RingHom.map_mulVec (cA D) d.p0 w i
  rw [h1]
  conv_rhs => rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose]
  change _ = (fun i => cA D (w i)) ⬝ᵥ (adj d.p0 *ᵥ (gA S₀ *ᵥ y))
  rw [Matrix.mulVec_mulVec, ← wittCoreProjection_conjTranspose_gram_eq, ← Matrix.mulVec_mulVec]

theorem decomp_vec {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (z : Fin S.rank → AE D) :
    z = d.jX *ᵥ (d.pX *ᵥ z) + d.j0 *ᵥ (d.p0 *ᵥ z) + d.jY *ᵥ (d.pY *ᵥ z) := by
  have h := congrArg (· *ᵥ z) d.sum_eq_one
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h
  exact h.symm

end GlobalTheory.IwaDecomp

namespace GlobalTheory.IwaDecomp

variable {D : D7}

def lamZero {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : Pl D) (N : AddSubgroup (Fin S.rank → AE D)) :
    AddSubgroup (Fin S₀.rank → AE D) where
  carrier := {s | (∀ i, s i ∈ idAt D (· = v)) ∧ d.j0 *ᵥ s ∈ N}
  zero_mem' := ⟨fun _ => zero_mem _, by rw [Matrix.mulVec_zero]; exact N.zero_mem⟩
  add_mem' := fun {a b} ha hb => ⟨fun i => add_mem (ha.1 i) (hb.1 i), by
    rw [Matrix.mulVec_add]; exact N.add_mem ha.2 hb.2⟩
  neg_mem' := fun {a} ha => ⟨fun i => neg_mem (ha.1 i), by
    rw [Matrix.mulVec_neg]; exact N.neg_mem ha.2⟩

theorem exists_nat_wittCoreInclusion_integral_at_place {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : Pl D) :
    ∃ n : ℕ, 0 < n ∧ ∀ s : Fin S₀.rank → AE D, (∀ i, s i ∈ intAt D (· = v)) →
      ∀ k, (d.j0 *ᵥ ((n : AE D) • s)) k ∈ intAt D (· = v) := by
  classical
  choose nf hnf hmul using fun kl : Fin S.rank × Fin S₀.rank => exists_nat_incA_mul v (d.i₀ kl.1 kl.2)
  refine ⟨∏ kl, nf kl, Finset.prod_pos fun kl _ => hnf kl, fun s hs k => ?_⟩
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  refine intAt_sum' _ _ fun l _ => ?_
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem nf (Finset.mem_univ (k, l))
  have e : d.j0 k l = incA D (d.i₀ k l) := rfl
  rw [e, hq, Nat.cast_mul, mul_assoc]
  exact hmul (k, l) _ (intAt_natCast_mul q (hs l))

theorem selfDual_split : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε)
    (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a)
    (N : AddSubgroup (Fin S.rank → AE D)) (α β : Fin ρ → AE D), IsSDAt S v N → (∀ i, α i ∈ idAt D (· = v)) →
    (∀ i, β i ∈ idAt D (· = v)) → (∀ i, α i * β i = ε) → (∀ i, colMul d.jX i (α i) ∈ N) →
    (∀ i, colMul d.jY i (cA D (β i)) ∈ N) → ∃ Λ₀ : AddSubgroup (Fin S₀.rank → AE D), IsSDAt S₀ v Λ₀ ∧
      ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) →
        (z ∈ N ↔ (∀ i, (d.pX *ᵥ z) i * β i ∈ intAt D (· = v)) ∧
          (∀ i, (d.pY *ᵥ z) i * cA D (α i) ∈ intAt D (· = v)) ∧ d.p0 *ᵥ z ∈ Λ₀) := by
  intro D S S₀ ρ d v ε _ hεc _ hε N α β hN _ _ hαβ hXα hYβ

  have hsmul : ∀ t ∈ intAt D (· = v), ∀ y ∈ N, t • y ∈ N := by
    intro t ht y hy
    have hys := hN.1 y hy
    refine (hN.2.2 (t • y) fun i => Ideal.mul_mem_left _ t (hys i)).2 fun x hx => ?_
    rw [hermAt_smul_left]
    exact intAt_mul' ht ((hN.2.2 y hys).1 hy x hx)

  have hX : ∀ a : Fin ρ → AE D, (∀ i, a i ∈ idAt D (· = v)) → (∀ i, a i * β i ∈ intAt D (· = v)) →
      d.jX *ᵥ a ∈ N := by
    intro a ha hab
    rw [mulVec_eq_sum_colMul]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have e : colMul d.jX i (a i) = (a i * β i) • colMul d.jX i (α i) := by
      have e1 : a i * β i * α i = a i := by
        rw [mul_assoc, mul_comm (β i), hαβ i, mul_comm, (hε _).1 (ha i)]
      funext k
      simp only [colMul, Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, e1]
    rw [e]
    exact hsmul _ (hab i) _ (hXα i)

  have hY : ∀ b : Fin ρ → AE D, (∀ i, b i ∈ idAt D (· = v)) → (∀ i, b i * cA D (α i) ∈ intAt D (· = v)) →
      d.jY *ᵥ b ∈ N := by
    intro b hb hba
    rw [mulVec_eq_sum_colMul]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have e : colMul d.jY i (b i) = (b i * cA D (α i)) • colMul d.jY i (cA D (β i)) := by
      have e1 : b i * cA D (α i) * cA D (β i) = b i := by
        rw [mul_assoc, ← map_mul, hαβ i, hεc, mul_comm, (hε _).1 (hb i)]
      funext k
      simp only [colMul, Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, e1]
    rw [e]
    exact hsmul _ (hba i) _ (hYβ i)

  have hfwd : ∀ z ∈ N, (∀ i, (d.pX *ᵥ z) i * β i ∈ intAt D (· = v)) ∧
      (∀ i, (d.pY *ᵥ z) i * cA D (α i) ∈ intAt D (· = v)) ∧ d.j0 *ᵥ (d.p0 *ᵥ z) ∈ N := by
    intro z hz
    have hzs := hN.1 z hz
    have hpair := (hN.2.2 z hzs).1 hz
    have h1 : ∀ i, (d.pX *ᵥ z) i * β i ∈ intAt D (· = v) := by
      intro i
      have := hpair _ (hYβ i)
      rwa [hermAt_colMul, ← d.pX_eq, cA_cA, mul_comm] at this
    have h2 : ∀ i, (d.pY *ᵥ z) i * cA D (α i) ∈ intAt D (· = v) := by
      intro i
      have := hpair _ (hXα i)
      rwa [hermAt_colMul, ← d.pY_eq, mul_comm] at this
    refine ⟨h1, h2, ?_⟩
    have hXm := hX _ (mulVec_mem_idAt d.pX hzs) h1
    have hYm := hY _ (mulVec_mem_idAt d.pY hzs) h2
    have key : ∀ X Y Z w : Fin S.rank → AE D, w = X + Z + Y → Z = w - X - Y := fun X Y Z w h => by
      rw [h]; abel
    have e := key _ _ _ _ (decomp_vec d z)
    rw [e]
    exact N.sub_mem (N.sub_mem hz hXm) hYm
  have hmem : ∀ s, s ∈ lamZero d v N ↔ (∀ i, s i ∈ idAt D (· = v)) ∧ d.j0 *ᵥ s ∈ N := fun _ => Iff.rfl
  refine ⟨lamZero d v N, ⟨fun y hy => ((hmem y).1 hy).1, ?_, ?_⟩, ?_⟩
  · obtain ⟨mN, hmN, hNm⟩ := hN.2.1
    obtain ⟨n, hn, hjn⟩ := exists_nat_wittCoreInclusion_integral_at_place d v
    refine ⟨mN * n, Nat.mul_pos hmN hn, fun y hy => (hmem _).2 ⟨fun i => ?_, ?_⟩⟩
    · exact Ideal.mul_mem_left _ _ (hy i).1
    · have e : d.j0 *ᵥ (((mN * n : ℕ) : AE D) • y) = (mN : AE D) • (d.j0 *ᵥ ((n : AE D) • y)) := by
        funext k
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Nat.cast_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [e]
      exact hNm _ (hjn y hy)
  · intro y hy
    have hjs : ∀ i, (d.j0 *ᵥ y) i ∈ idAt D (· = v) := mulVec_mem_idAt d.j0 hy
    constructor
    · intro hyΛ x hx
      have e : hermAt S₀ y x = hermAt S (d.j0 *ᵥ y) (d.j0 *ᵥ x) := by
        rw [adelicHermitianForm_wittCoreInclusion_left, Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]
      rw [e]
      exact (hN.2.2 _ hjs).1 ((hmem y).1 hyΛ).2 _ ((hmem x).1 hx).2
    · intro h
      refine (hmem y).2 ⟨hy, (hN.2.2 _ hjs).2 fun w hw => ?_⟩
      rw [adelicHermitianForm_wittCoreInclusion_left]
      exact h _ ((hmem _).2 ⟨mulVec_mem_idAt d.p0 (hN.1 w hw), (hfwd w hw).2.2⟩)
  · intro z hz
    constructor
    · intro hzN
      obtain ⟨h1, h2, h3⟩ := hfwd z hzN
      exact ⟨h1, h2, (hmem _).2 ⟨mulVec_mem_idAt d.p0 hz, h3⟩⟩
    · rintro ⟨h1, h2, h3⟩
      rw [decomp_vec d z]
      exact N.add_mem (N.add_mem (hX _ (mulVec_mem_idAt d.pX hz) h1) ((hmem _).1 h3).2)
        (hY _ (mulVec_mem_idAt d.pY hz) h2)

end GlobalTheory.IwaDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceStdCharContinuousNontrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitChar

theorem cont_ne_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → IsStdChar D ψ (-1) →
    Continuous χ ∧ χ ≠ 1 := by
  intro D k _ _ _ _ p ψ χ hχ hψ
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have htr : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun a : k => psiE ψ (p.sec a) := hψ.1.1.comp (htr.comp p.cont_sec)
  refine ⟨?_, ?_⟩
  · have h' : Continuous fun a : k => ((χ a : Circle) : ℂ) := by
      have he : (fun a : k => ((χ a : Circle) : ℂ)) = fun a => psiE ψ (p.sec a) := funext hχ
      rw [he]; exact hc
    first
      | exact Circle.isEmbedding_coe.continuous_iff.2 h'
      | exact continuous_induced_rng.2 h'
  · intro h1
    obtain ⟨a, ha⟩ := GlobalTheory.FinPl.CharNontriv.exists_psiE_sec_ne_one D k p ψ hψ
    apply ha
    rw [← hχ a, h1]
    simp

end GlobalTheory.FinPl.SplitChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharAnnihilatorOpenSubgroupFinPartCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.CondBound

open Filter Topology

variable (D : D7)

abbrev line : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1

def o : Fin (line D).rank := ⟨0, Nat.one_pos⟩

theorem sum_line (f : Fin (line D).rank → AE D) : ∑ i, f i = f (o D) := Fin.sum_univ_one f

theorem hO_line (x y : WO (line D) (line D)) :
    hO (line D) (line D) x y = incA D ((line D).gram⁻¹ (o D) (o D)) * cA D (y (o D) (o D)) *
      incA D ((line D).gram (o D) (o D)) * x (o D) (o D) := by
  unfold hO
  simp only [sum_line]

abbrev latL : AddSubgroup (WO (line D) (line D)) :=
  latO (line D) (line D) (GlobalTheory.PlaceModel.latFrame (line D) : Set (Fin (line D).rank → D.host.E))
    (GlobalTheory.PlaceModel.latFrame (line D) : Set (Fin (line D).rank → D.host.E)) fun _ => True

theorem infPart_latL {u : WO (line D) (line D)} (hu : u ∈ latL D) : infPart D (u (o D) (o D)) = 0 := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, -, a, -, s, -, t, -, rfl⟩ := hw
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    exact TensorProduct.zero_tmul _ _
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_apply, RingHom.map_add, hx, hy, add_zero]
  | neg x _ hx => rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

theorem infPart_r (a : Af D.host.F) : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 a)) = 0 := by
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  exact TensorProduct.zero_tmul _ _

theorem finPart_r (N : ℕ) :
    finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (N : Af D.host.F))) = finPart D (incA D (N : D.host.E)) := by
  rw [map_natCast, map_natCast]
  show (N : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = _
  rw [← map_natCast (algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)) N]
  rfl

theorem den_latL : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ latL D, M • finPart D (u (o D) (o D)) ∈ intAE D := by
  have hΛ := GlobalTheory.PlaceModel.isSelfDualC_latFrame (line D)
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := line D) (T := line D) hΛ.1.fg hΛ.1.fg
  refine ⟨M, hM, fun u hu => ?_⟩
  have h2 : toEAf D ((M : AE D) * u (o D) (o D)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [RingHom.map_mul, map_natCast]; exact hden u hu (o D) (o D)
  have h3 := GlobalTheory.PlaceDatum.finPart_mem_of_toEAf h2
  rw [RingHom.map_mul, map_natCast] at h3
  rw [nsmul_eq_mul]
  exact h3

theorem exists_compact_fin (M : ℕ) (hM : 0 < M) : ∃ K0 : Set (AE D), IsCompact K0 ∧
    ∀ z : AE D, infPart D z = 0 → M • finPart D z ∈ intAE D → z ∈ K0 := by
  obtain ⟨C, hC, hCd⟩ := GlobalTheory.SmoothForms.Cover.exists_compact_denom D M hM
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm '' ({0} ×ˢ C), (isCompact_singleton.prod hC).image hc, fun z h1 h2 => ?_⟩
  have e1 : (e z).1 = 0 := by have := (he z).1; exact this.trans h1
  have e2 : M • (e z).2 ∈ intAE D := by have := (he z).2; rw [this]; exact h2
  exact ⟨e z, Set.mk_mem_prod (Set.mem_singleton_iff.2 e1) (hCd _ e2), e.symm_apply_apply z⟩

theorem tendsto_r : Tendsto (fun n : ℕ => algebraMap (AF D.host.F) (AE D)
    (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F))) atTop (𝓝 0) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have h : Tendsto (fun n : ℕ => pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F)) atTop (𝓝 (0 : AF D.host.F)) :=
    (tendsto_const_nhds (x := (0 : Ainf D.host.F))).prodMk_nhds
      (GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele D.host.F)
  have hcont : Continuous (algebraMap (AF D.host.F) (AE D)) := by
    have hfun : (algebraMap (AF D.host.F) (AE D) : AF D.host.F → AE D) = fun t => t • (1 : AE D) := by
      funext t; exact Algebra.algebraMap_eq_smul_one t
    haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
    rw [hfun]; exact continuous_id.smul (continuous_const (y := (1 : AE D)))
  have := (hcont.tendsto 0).comp h
  rwa [map_zero] at this

theorem exists_small (C' : Set (AE D)) (hC' : IsCompact C') (U : AddSubgroup (AE D)) (hU : IsOpen (U : Set (AE D))) :
    ∃ n : ℕ, ∀ z ∈ C', algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F)) * z ∈ U := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have hev : ∀ᶠ t in 𝓝 (0 : AE D), ∀ z ∈ C', t * z ∈ U := by
    refine hC'.eventually_forall_of_forall_eventually fun z _ => ?_
    have h0 : ((0 : AE D), z).1 * ((0 : AE D), z).2 ∈ U := by rw [zero_mul]; exact U.zero_mem
    exact (continuous_mul.continuousAt (x := ((0 : AE D), z))).preimage_mem_nhds (hU.mem_nhds h0)
  exact ((tendsto_r D).eventually hev).exists

theorem isCompact_mul (c : AE D) {K : Set (AE D)} (hK : IsCompact K) : IsCompact ((fun z => c * z) '' K) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact hK.image (continuous_const.mul continuous_id)

theorem isCompact_mul_conj (c : AE D) {K : Set (AE D)} (hK : IsCompact K) :
    IsCompact ((fun z => c * cA D z) '' K) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact hK.image (continuous_const.mul (GlobalTheory.ConjAutProps.continuous_conjA D))

set_option maxHeartbeats 1000000 in

theorem annihilator_finPart_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (AE D),
    IsOpen (U : Set (AE D)) → ∃ K : Set (AE D), IsCompact K ∧ ∀ x : AE D,
      (∀ a ∈ U, infPart D a = 0 → ψ (Algebra.trace (AF D.host.F) (AE D) (x * a)) = 1) →
        ∃ k ∈ K, finPart D (x - k) = 0 := by
  intro D ψ hψ U hU
  have hΛ := GlobalTheory.PlaceModel.isSelfDualC_latFrame (line D)
  obtain ⟨M, hM, hden⟩ := den_latL D
  obtain ⟨K0, hK0c, mem0⟩ := exists_compact_fin D M hM
  have memL : ∀ u ∈ latL D, u (o D) (o D) ∈ K0 := fun u hu => mem0 _ (infPart_latL D hu) (hden u hu)
  let c0 : AE D := incA D D.host.xi0 * incA D ((line D).gram⁻¹ (o D) (o D)) * incA D ((line D).gram (o D) (o D))
  obtain ⟨n, hn⟩ := exists_small D _ (isCompact_mul_conj D c0 hK0c) U hU
  let r : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F))
  have hN : ((n.factorial : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_pos n).ne'
  refine ⟨(fun z => incA D ((n.factorial : ℕ) : D.host.E)⁻¹ * z) '' K0, isCompact_mul D _ hK0c, ?_⟩
  intro x hx
  let u : WO (line D) (line D) := Matrix.of fun _ _ => x * r
  have hu0 : u.map (infPart D) = 0 := by
    ext i j
    show infPart D (x * r) = 0
    rw [RingHom.map_mul, infPart_r, mul_zero]
  have huL : u ∈ latL D := by
    refine ((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ (line D) (line D) _ _ hψ hΛ hΛ).1 u hu0).2 fun u' hu' => ?_
    have ha : r * (c0 * cA D (u' (o D) (o D))) ∈ U := hn _ ⟨_, memL u' hu', rfl⟩
    have hai : infPart D (r * (c0 * cA D (u' (o D) (o D)))) = 0 := by
      rw [RingHom.map_mul, infPart_r, zero_mul]
    have h := hx _ ha hai
    rw [symplO, hO_line]
    convert h using 3
    show _ = x * _
    simp only [c0, u, Matrix.of_apply]
    ring
  refine ⟨_, ⟨_, memL u huL, rfl⟩, ?_⟩
  show finPart D (x - incA D ((n.factorial : ℕ) : D.host.E)⁻¹ * (x * r)) = 0
  have h1 : finPart D (incA D ((n.factorial : ℕ) : D.host.E)⁻¹) * finPart D r = 1 := by
    rw [finPart_r, ← RingHom.map_mul, ← RingHom.map_mul, inv_mul_cancel₀ hN, map_one, map_one]
  rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, mul_left_comm, h1, mul_one, sub_self]

end GlobalTheory.CondBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalDoubleCosetRepsMulStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_borelSpherical_doubleCosetReps_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → (∀ i, γ i ≠ 0) → ∀ (g₀ : GL (Fin N) k) (R : Finset (GL (Fin N) k)), IsRepsK g₀ R → ∀ m : GL (Fin N) k, ∑ g ∈ R, ψ (m * g) = ψ m * ∑ g ∈ R, ψ g := by
  first | exact @GlobalTheory.ZonalSum.sum_mul_eq | exact GlobalTheory.ZonalSum.sum_mul_eq | (intros; apply GlobalTheory.ZonalSum.sum_mul_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TendstoUnitaryAdelicPointsAgreeOnGrowingFinsetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_unitaryAdelicPoints_agree_on_growing_finset : ∀ (D : D7) (S : HSp D) (κ : GA D S) (x : Finset (Pl D) → GA D S), (∀ Fs i j, infPart D (Formalism.L2.Theta.mt S (x Fs) i j) = infPart D (Formalism.L2.Theta.mt S κ i j)) → (∀ Fs, ∀ w ∈ Fs, ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) = GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S κ i j)) → (∀ Fs w, w ∉ Fs → ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) = GlobalTheory.FinPl.compAt D w ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)) → Filter.Tendsto x Filter.atTop (nhds κ) := by
  first | exact @GlobalTheory.AdelicLimit.tendsto_of_agree | exact GlobalTheory.AdelicLimit.tendsto_of_agree | (intros; apply GlobalTheory.AdelicLimit.tendsto_of_agree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExistStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist : ∀ D : D7, (∀ V : HSp D, Nonempty (Vol V)) ∧ (∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), Nonempty (VolN d)) ∧ (∀ m n, Nonempty (VolM D m n)) ∧ ∀ ρ, Nonempty (VolU D ρ) := by
  first | exact @GlobalTheory.Unf.VolExist.measures_exist | exact GlobalTheory.Unf.VolExist.measures_exist | (intros; apply GlobalTheory.Unf.VolExist.measures_exist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupTwoModelsRationalRealUnipotentDictioStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_twoModels_rationalReal_unipotent_dictionary : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ x, Formalism.IndefR.Eqv.UI.brg fr x ∈ GQ V ↔ x ∈ (Formalism.IndefR.Eqv.UI.instV fr).GFset) ∧ (∀ (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (τ : D.what₂.Tau) (A : Matrix (Fin V.rank) (Fin V.rank) ℂ), A = uMat (x.1 (Formalism.L2.Host.tauPl D τ)) → infMat D.sp.cm.sig V.gram (θ τ) (Formalism.IndefR.Eqv.UI.brg fr x) = fr.P (Formalism.L2.Host.tauPl D τ) * A * (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹) ∧ ∀ W, (Formalism.IndefR.Eqv.UI.instV fr).IsIsot W → ∃ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ ∧ ∀ x, Formalism.IndefR.Eqv.UI.brg fr x ∈ NI V C₀ → x ∈ (Formalism.IndefR.Eqv.UI.instV fr).NA W := by
  first | exact @GlobalTheory.BridgeDict.bridge_dict | exact GlobalTheory.BridgeDict.bridge_dict | (intros; apply GlobalTheory.BridgeDict.bridge_dict <;> assumption)
end

