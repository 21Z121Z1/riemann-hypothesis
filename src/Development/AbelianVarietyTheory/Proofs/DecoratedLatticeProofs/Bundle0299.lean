import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0027
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0293
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0232
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyEqOfIsZetaCont
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0031
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomSphericalCardWeightIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BottomWt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem relIndex_KO_ne_zero {n : Type} [Fintype n] [DecidableEq n] {J : Subgroup (GL n k)}
    (hJ : J ≤ KO k n) (ho : IsOpen (J : Set (GL n k))) : J.relIndex (KO k n) ≠ 0 := by
  haveI : CompactSpace (KO k n) := isCompact_iff_compactSpace.1 SplitFlip.isCompact_KO
  haveI : Finite ((KO k n) ⧸ J.subgroupOf (KO k n)) :=
    Subgroup.quotient_finite_of_isOpen _ (ho.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem N_one_apply_inl {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {u : GL (n ⊕ Fin c) k}
    (hu : u ∈ N k n c 1) (a b : n) : u.val (Sum.inl a) (Sum.inl b) = (1 : Matrix n n k) a b := by
  have := GlobalTheory.RootEx.prodN_inN_of_mem hu (Sum.inl a) (Sum.inl b) le_rfl
  simpa [Matrix.one_apply] using this

theorem mul_embX_inl {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {u : GL (n ⊕ Fin c) k}
    (hu : u ∈ N k n c 1) (g : GL n k) (a b : n) :
    (u * embX c g).val (Sum.inl a) (Sum.inl b) = g.val a b := by
  simp only [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, embX]
  simp [N_one_apply_inl hu, Matrix.one_apply]

theorem embX_mul_inl {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {u : GL (n ⊕ Fin c) k}
    (hu : u ∈ N k n c 1) (g : GL n k) (a b : n) :
    (embX c g * u).val (Sum.inl a) (Sum.inl b) = g.val a b := by
  simp only [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, embX]
  simp [N_one_apply_inl hu, Matrix.one_apply]

theorem intM_embX {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {g : GL n k} (h : IntM g.val) :
    IntM (embX c g : GL (n ⊕ Fin c) k).val := by
  rintro (a | a) (b | b)
  · simpa [embX] using h a b
  · simp [embX]
  · simp [embX]
  · by_cases e : a = b
    · subst e; simp [embX]
    · simp [embX, Matrix.one_apply, e]

theorem prX_Cgrp_KO_one (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) :
    prX (Cgrp (KO k (n ⊕ Fin c)) 1) = KO k n := by
  ext g
  rw [mem_prX]
  constructor
  · rintro ⟨u, hu, hC⟩
    have hw : u * embX c g ∈ KO k (n ⊕ Fin c) := by simpa using (mem_Cgrp.1 hC).2
    obtain ⟨h1, h2⟩ := mem_KO.1 hw
    refine mem_KO.2 ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [← mul_embX_inl hu g a b]; exact h1 _ _
    · have hu' : u⁻¹ ∈ N k n c 1 := inv_mem hu
      have e : (u * embX c g)⁻¹ = embX c g⁻¹ * u⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
      rw [← embX_mul_inl hu' g⁻¹ a b, ← e]; exact h2 _ _
  · intro hg
    refine ⟨1, one_mem _, ?_⟩
    rw [one_mul, mem_Cgrp]
    refine ⟨Subgroup.mem_sup_left ⟨g, rfl⟩, ?_⟩
    simp only [inv_one, one_mul, mul_one]
    obtain ⟨h1, h2⟩ := mem_KO.1 hg
    refine mem_KO.2 ⟨intM_embX h1, ?_⟩
    rw [← map_inv]; exact intM_embX h2

theorem reGL_symm_mem_KO_iff {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    {x : GL b k} : (reGL e).symm x ∈ KO k a ↔ x ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using h1 (e.symm i) (e.symm j)
    · simpa using h2 (e.symm i) (e.symm j)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

theorem twistChain_lev_zero {s : ℕ} {t κ : Type} [Fintype t] [DecidableEq t] [Fintype κ] [DecidableEq κ]
    (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (c : ℕ) (h : 0 + c = s + 1) :
    ((twistChain s t κ δ hδ η).lev 0 c h).J = KO k _ := by
  ext x
  change (plainFrame (k := k) (stdOrd κ t 0 c h)).conj.symm x ∈ (parahoric (κ ⊕ Fin (s + 1)) (Fin 0 × t) δ hδ).J ↔ _
  rw [mem_parahoric]
  have e : (plainFrame (k := k) (stdOrd κ t 0 c h)).conj.symm x = (reGL (stdOrd κ t 0 c h)).symm x := by
    simp [LatFrame.conj, plainFrame]
    rfl
  rw [e, reGL_symm_mem_KO_iff]
  exact ⟨fun H => H.1, fun H => ⟨H, fun i _ => i.1.elim0⟩⟩

end GlobalTheory.BottomWt

namespace GlobalTheory.QTw
open GlobalTheory.BottomWt

theorem QExt.bottom_one : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) (E : QExt G χ), Fintype.card (E.Ch 0) = 1 ∧ (∀ α, E.wt 0 α = 1) ∧ E.idx 0 = 1 ∧ ∀ j, j ≤ G.s + 1 + 1 → E.idx j ≠ 0 := by
  intro D c v B PP G χ E
  have hz : E.A 0 G.s (zero_add _) = {1} := E.reps.zero _ _
  have hrep : ∀ α, E.rep 0 G.s (zero_add _) α = 1 := fun α => by
    have := (E.rep_bij 0 G.s (zero_add _)).mapsTo (Set.mem_univ α)
    rw [hz] at this
    exact this
  have hJ0 : ∀ c h, ((G.T E.δ E.tame E.η).lev 0 c h).J = KO G.k _ := fun c h =>
    twistChain_lev_zero E.δ E.tame E.η c h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_eq_one_iff]
    have h1 : (1 : GL _ G.k) ∈ E.A 0 G.s (zero_add _) := by rw [hz]; rfl
    obtain ⟨x, -, -⟩ := (E.rep_bij 0 G.s (zero_add _)).surjOn h1
    exact ⟨x, fun y => (E.rep_bij 0 G.s (zero_add _)).injOn (Set.mem_univ _) (Set.mem_univ _)
      ((hrep y).trans (hrep x).symm)⟩
  · intro α
    rw [E.wt_mid 0 G.s (zero_add _) α, hrep α, hJ0, prX_Cgrp_KO_one, (E.haar 0).2]
    simp
  · rw [E.idx_mid 0 (G.s + 1) (zero_add _), hJ0]
    exact Subgroup.relIndex_self _
  · intro j hj
    rcases Nat.lt_or_ge j (G.s + 2) with hl | hl
    · rw [E.idx_mid j (G.s + 1 - j) (by omega)]
      exact relIndex_KO_ne_zero (E.le _ _ _) (E.reg.2.2 _ _ _).1
    · obtain rfl : j = G.s + 1 + 1 := by omega
      rw [E.idx_top]
      exact relIndex_KO_ne_zero E.leT E.openT

end GlobalTheory.QTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CapelliLowestGelfandConj
section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.CapelliLowest

end GlobalTheory.CapelliLowest

namespace GlobalTheory.CapelliLowest

theorem single_comm {N : ℕ} (a b c d : Fin N) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1; subst h2; simp [Matrix.single_mul_single_same]
  · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne (h := h2), h2]
  · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne (h := h1), h1]
  · simp [Matrix.single_mul_single_of_ne (h := h1), Matrix.single_mul_single_of_ne (h := h2), h1, h2]

theorem lie_of_glRel {A : Type} [Ring A] [Algebra ℂ A] {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] A)
    (h : Formalism.REAL.GlRel (fun i j => Q (Matrix.single i j 1))) (X Y : Matrix (Fin N) (Fin N) ℂ) :
    Q X * Q Y - Q Y * Q X = Q (X * Y - Y * X) := by
  refine Matrix.induction_on' X ?_ ?_ ?_
  · simp
  · intro p q hp hq
    have e : (p + q) * Y - Y * (p + q) = (p * Y - Y * p) + (q * Y - Y * q) := by noncomm_ring
    rw [e, map_add, map_add, ← hp, ← hq]
    noncomm_ring
  · intro i j x
    refine Matrix.induction_on' Y ?_ ?_ ?_
    · simp
    · intro p q hp hq
      have e : Matrix.single i j x * (p + q) - (p + q) * Matrix.single i j x =
          (Matrix.single i j x * p - p * Matrix.single i j x) + (Matrix.single i j x * q - q * Matrix.single i j x) := by
        noncomm_ring
      rw [e, map_add, map_add, ← hp, ← hq]
      noncomm_ring
    · intro k l y
      have hx : Matrix.single i j x = x • Matrix.single i j (1 : ℂ) := by rw [Matrix.smul_single, smul_eq_mul, mul_one]
      have hy : Matrix.single k l y = y • Matrix.single k l (1 : ℂ) := by rw [Matrix.smul_single, smul_eq_mul, mul_one]
      have e : x • Matrix.single i j (1 : ℂ) * (y • Matrix.single k l 1) - y • Matrix.single k l (1 : ℂ) * (x • Matrix.single i j 1)
          = (x * y) • (Matrix.single i j (1 : ℂ) * Matrix.single k l 1 - Matrix.single k l 1 * Matrix.single i j 1) := by
        simp only [smul_mul_smul_comm, mul_comm y x, smul_sub]
      rw [hx, hy, e, single_comm, map_smul, map_smul, map_smul, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm y x,
        ← smul_sub, h i j k l]
      split_ifs <;> simp

theorem glRel_conj {A : Type} [Ring A] [Algebra ℂ A] (N : ℕ) (Q : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] A)
    (g : GL (Fin N) ℂ) (h : Formalism.REAL.GlRel (fun i j => Q (Matrix.single i j 1))) :
    Formalism.REAL.GlRel (fun i j => Q (g.1 * Matrix.single i j 1 * (g⁻¹).1)) := by
  have HG : (g⁻¹).1 * g.1 = 1 := g.inv_mul
  have key : ∀ X Y : Matrix (Fin N) (Fin N) ℂ, (g.1 * X * (g⁻¹).1) * (g.1 * Y * (g⁻¹).1) = g.1 * (X * Y) * (g⁻¹).1 := by
    intro X Y
    rw [show g.1 * X * (g⁻¹).1 * (g.1 * Y * (g⁻¹).1) = g.1 * X * ((g⁻¹).1 * g.1) * Y * (g⁻¹).1 by simp only [mul_assoc],
      HG, mul_one]
    simp only [mul_assoc]
  intro a b c d
  simp only
  rw [lie_of_glRel Q h, key, key, ← sub_mul, ← mul_sub, single_comm]
  split_ifs <;> simp [mul_sub, sub_mul]

theorem gelfA_conj {A : Type} [Ring A] [Algebra ℂ A] (N : ℕ) (Q : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] A)
    (g : GL (Fin N) ℂ) :
    GlobalTheory.SmoothForms.gelfA (fun i j => Q (g.1 * Matrix.single i j 1 * (g⁻¹).1)) =
      GlobalTheory.SmoothForms.gelfA (fun i j => Q (Matrix.single i j 1)) := by
  have hGH : g.1 * (g⁻¹).1 = 1 := g.mul_inv
  funext k
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow, GlobalTheory.SmoothForms.gelfA_eq_sum_pow]
  have hE' : (fun a b => Q (g.1 * Matrix.single a b 1 * (g⁻¹).1)) =
      fun a b => ∑ c, ∑ d, ((g.1)ᵀ a c * ((g⁻¹).1)ᵀ d b) • Q (Matrix.single c d 1) := by
    funext a b
    simp only [← map_smul, ← map_sum]
    congr 1
    rw [Matrix.matrix_eq_sum_single (g.1 * _ * (g⁻¹).1)]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    simp [Matrix.mul_apply, Matrix.single, ite_and]
  rw [hE', GlobalTheory.RegSch.GChart.trace_pow_conj _ (g.1)ᵀ ((g⁻¹).1)ᵀ
    (by rw [← Matrix.transpose_mul, hGH, Matrix.transpose_one])]

end GlobalTheory.CapelliLowest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainFirstStageLValuesPositive
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChainTw

theorem isPar_flat_of_le {D : D7} {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} (hr : D.R.r ≤ s.V.rank)
    (hle : s.CC c ≤ (flat c w j s hr).CC c) (u : s.CC c) (B : GlobalTheory.LFun.Fam D.host.E) (hB : IsPar u B) :
    IsPar (⟨u.1, hle u.2⟩ : (flat c w j s hr).CC c) B := by
  refine ⟨fun h => ?_, fun v hv => ?_⟩
  · have h2 : ((⟨u.1, hle u.2⟩ : (flat c w j s hr).CC c) : SmT (flat c w j s hr).M →ₗ[ℂ] (GA D (flat c w j s hr).V → ℂ)) = 0 :=
      (Submodule.coe_eq_zero).2 h
    exact hB.1 ((Submodule.coe_eq_zero).1 h2)
  · have h3 := hB.2 v hv
    unfold ParFun at h3 ⊢
    exact h3

theorem bounded_first_member (hCRD : GlobalTheory.Published.CuspRapidDecay) {D : D7} {c : Com D} (hc : c.Is) (hj : 0 ≤ D.R.m) {s' : PiLocalization₂ D}
    (hflat : s'.Is c 0) (u' : s'.CC c) (B : GlobalTheory.LFun.Fam D.host.E) (hB' : IsPar u' B) :
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r (((D.R.r : ℝ) - 1) / 2) := by
  have hrank : s'.V.rank = D.R.r := by
    rw [hflat.rank]; simp [Formalism.BasicNotions.Ranks.rankY]
  have hbd0 := GlobalTheory.T.thetaChain_heckeParams_trivialBound_rapidDecay hCRD D (GlobalTheory.T.thetaChain_level_properties D) c hc 0 hj s' hflat u' B hB'
  rw [hrank] at hbd0
  exact hbd0

theorem conjStable_first_member (hCRD : GlobalTheory.Published.CuspRapidDecay) {D : D7} {c : Com D} (hc : c.Is) (hj : 0 ≤ D.R.m) {s' : PiLocalization₂ D}
    (hflat : s'.Is c 0) (u' : s'.CC c) (B : GlobalTheory.LFun.Fam D.host.E) (hB' : IsPar u' B) :
    ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
      (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w ≠ w' → B w' = (B w).map star) ∧
      (¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → (B w).map star = B w) := by
  have hex : ∃ v, PiLocalization₂.val u' v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hB'.1
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hex
  set f : GA D s'.V → ℂ := fun g => conj (PiLocalization₂.val u' v g) with hfdef
  have hPF : ParFun c s' (PiLocalization₂.val u' v) B := hB'.2 v hv
  have h3 : GlobalTheory.LFun.IsParamFunV s'.V c.S f B := ((GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc 0 hj s' hflat).2 f B).1 hPF
  obtain ⟨h4a, _, _⟩ := GlobalTheory.T.thetaChainStage_conjugate_values_hecke_operators hCRD D c hc 0 hj s' hflat
  obtain ⟨hcont, ⟨C, hC⟩, hinv, _⟩ := h4a u' v
  have hfmem : f ∈ GlobalTheory.FinZeta.bddAut s'.V := by
    refine ⟨(Complex.continuous_conj).comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [hfdef, hinv γ hγ g]
    · simpa [hfdef] using hC g
  exact GlobalTheory.T.boundedAutomorphic_parameters_star_stable D s'.V c.S f hfmem B h3

end GlobalTheory.ChainTw

namespace GlobalTheory.ChainTw

theorem lPos_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LPos D := by
  intro hCRD D c w hw j hj s hs hj0 u B hB
  subst hj0
  have hc := hw.com
  obtain ⟨hr, hL, hflat⟩ := hs
  have hle := GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level D c w hw 0 hj s ⟨hr, hL, hflat⟩ hr
  have hB' := isPar_flat_of_le hr hle u B hB
  have hbd : GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) :=
    GlobalTheory.LiftPole.Bounded.mono (bounded_first_member hCRD hc hj hflat _ B hB') (by linarith)
  refine ⟨hbd, fun k hk => ?_⟩
  have hst := conjStable_first_member hCRD hc hj hflat _ B hB'
  have hch := hc.chars.2.2.2.2 (k + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hrt : ((D.R.r : ℝ) / 2) + 1 < (1 + (D.R.t : ℝ)) / 2 := by
    have h5 : D.R.r + 5 ≤ D.R.t := by simpa [Formalism.BasicNotions.Ranks.r] using D.R.rank_add_five_le
    have h5' : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast h5
    linarith
  obtain ⟨l, hl, he⟩ := GlobalTheory.T.euler_product_conjugation_stable_parameters_pos D c.S B (c.μ (k + 1)) D.R.r ((D.R.r : ℝ) / 2) ((1 + (D.R.t : ℝ)) / 2) hch.1 hch.2
    (hc.unr ⟨k, hk⟩) hbd hrt hst
  refine ⟨l, hl, ?_⟩
  rw [← he]
  congr 1
  push_cast
  ring

end GlobalTheory.ChainTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjByColumnUnipotentPreservesUnipotentHaar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR.CjVol

open GlobalTheory.RootEx.VolN GlobalTheory.RootEx.Model

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem colE_inv_val_eq_zero (ρ : ℕ) (β : n → k) (t s : n ⊕ Fin c) (h : lev (ρ + 1) t ≠ lev (ρ + 1) s) :
    (colE c (ρ + 1) β)⁻¹.val t s = 0 := by
  rcases t with t | t <;> rcases s with s | s
  · exact absurd rfl h
  · simp only [colE, upU, Units.inv_mk, fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.of_apply]
    rw [if_neg, neg_zero]
    intro hs; apply h; simp [lev, hs]
  · simp [colE, upU]
  · have : t ≠ s := by rintro rfl; exact h rfl
    simp [colE, upU, Matrix.one_apply, this]

theorem colE_uni (ρ : ℕ) (β : n → k) :
    ∀ r s, (Sum.elim (fun _ => 0) (fun _ => 1) : n ⊕ Fin c → ℕ) s ≤ Sum.elim (fun _ => 0) (fun _ => 1) r →
      (colE c (ρ + 1) β).val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := by
  rintro (r | r) (s | s) h
  · simp [colE, upU, Matrix.one_apply]
  · simp at h
  · simp [colE, upU]
  · simp [colE, upU, Matrix.one_apply]

theorem colE_inv_uni (ρ : ℕ) (β : n → k) :
    ∀ r s, (Sum.elim (fun _ => 0) (fun _ => 1) : n ⊕ Fin c → ℕ) s ≤ Sum.elim (fun _ => 0) (fun _ => 1) r →
      (colE c (ρ + 1) β)⁻¹.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := by
  rintro (r | r) (s | s) h
  · simp [colE, upU, Matrix.one_apply]
  · simp at h
  · simp [colE, upU]
  · simp [colE, upU, Matrix.one_apply]

theorem extendAboveDiagonalEntries_mul_blockRespecting (p : ℕ) (h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (hh : ∀ t s, lev p t ≠ lev p s → h t s = 0) (e : Ix n c p → k) :
    ext0 (Up n c p) e * h = ext0 (Up n c p) ((rm (Up n c p) h).mulVec e) := by
  ext r s
  by_cases hrs : lev p r < lev p s
  · rw [matrixExtendByZero_mul (Up n c p) h e ⟨(r, s), hrs⟩]
    simp [ext0, hrs]
  · have : ext0 (Up n c p) ((rm (Up n c p) h).mulVec e) r s = 0 := by
      simp only [ext0, Matrix.of_apply]; rw [dif_neg hrs]
    rw [this, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases hts : lev p t = lev p s
    · have : ext0 (Up n c p) e r t = 0 := by
        simp only [ext0, Matrix.of_apply]; rw [dif_neg (show ¬ lev p r < lev p t by rw [hts]; exact hrs)]
      rw [this, zero_mul]
    · rw [hh t s hts, mul_zero]

theorem cjE_mkNel (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β : n → k) (e : Ix n c (ρ + 1) → k) :
    cjE ρ h1 h2 β (mkNel (ρ + 1) e) =
      mkNel (ρ + 1) ((lm (Up n c (ρ + 1)) (colE c (ρ + 1) β).val *
        rm (Up n c (ρ + 1)) (colE c (ρ + 1) β)⁻¹.val).mulVec e) := by
  rw [← mkNel_co (ρ + 1) (cjE ρ h1 h2 β (mkNel (ρ + 1) e))]
  congr 1
  funext a
  have hne : a.1.1 ≠ a.1.2 := fun h => by have := a.2; rw [h] at this; exact lt_irrefl _ this
  rw [← Matrix.mulVec_mulVec, ← mul_matrixExtendSelectedEntriesByZero_apply, ← extendAboveDiagonalEntries_mul_blockRespecting (ρ + 1) _ (colE_inv_val_eq_zero ρ β)]
  simp only [co, cjE_coe, Units.val_mul, val_mkNel, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Units.mul_inv, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.mul_assoc]

theorem det_L (ρ : ℕ) (β : n → k) :
    (lm (Up n c (ρ + 1)) (colE c (ρ + 1) β).val * rm (Up n c (ρ + 1)) (colE c (ρ + 1) β)⁻¹.val).det = 1 := by
  rw [det_mul, det_lm, det_rm]
  rw [Finset.prod_eq_one fun s _ => det_block_unitri _ _ (colE_uni ρ β) _,
    Finset.prod_eq_one fun s _ => det_block_unitri _ _ (colE_inv_uni ρ β) _, mul_one]

end GlobalTheory.HaarR.CjVol

open GlobalTheory.HaarR.CjVol GlobalTheory.RootEx.VolN GlobalTheory.RootEx.Model in
theorem GlobalTheory.HaarR.map_volN_cjE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (ν : Measure k), ν.IsAddHaarMeasure → ∀ β : n → k, (volN ν n c (ρ + 1)).map (cjE ρ h1 h2 β) = volN ν n c (ρ + 1) := by
  intro k _ _ _ _ _ _ n _ _ c ρ h1 h2 ν hν β
  exact map_volN_of_affine ν (ρ + 1) (cjE ρ h1 h2 β) _ (det_L ρ β) 0
    (fun e => by rw [add_zero]; exact cjE_mkNel ρ h1 h2 β e)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjRowEqTranslatedEvaluationCuspFormMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.SeeOnto

theorem see_onto : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → ∀ φ : L2X X, star φ ∈ HHX X → ∃ T ∈ MultT θ M J χ, (φ : X.B.I.GA → ℂ) =ᵐ[muX X] evS X h t (T (PiTensorProduct.tprod ℂ v₀)) := by
  intro hDS D X h θ S M J χ t v₀ hS hθ hGap hIdE hM hCV φ hφ
  obtain ⟨c, hc, hv₀⟩ := hCV
  have hL := (GlobalTheory.T.discreteSeriesTestData_of_noncompactGaps D X hGap).2.2.2.2.2
  obtain ⟨Φ, hΦ, hΦw⟩ := Formalism.L2.SG.EvalTOnto.rows_eq_hom X hL (star φ) hφ
  have hrep := GlobalTheory.T.exists_continuous_leftInvariant_rep_conjugateTensor hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ
  have hmult : GlobalTheory.ConjRowMult.conjMap X M c Φ h t ∈ Mult θ M J χ :=
    Submodule.subset_span
      ⟨GlobalTheory.T.conjugateIntertwiner_values_smoothAutomorphic hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep,
       GlobalTheory.T.conjugateIntertwiner_values_isCuspFun hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep,
       GlobalTheory.T.conjugate_evaluation_map_has_level hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep,
       fun τ g hg v w hw => GlobalTheory.T.conjugate_evaluation_map_intertwines_real_places hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep τ g hg v w hw,
       fun τ v x => GlobalTheory.T.conjIntertwiner_pointValue_sobolevContinuous hDS D X h θ S M J χ t c hS hθ hGap hIdE hM hc Φ hΦ hrep τ v x⟩
  refine ⟨PiTensorProduct.lift (GlobalTheory.ConjRowMult.conjMap X M c Φ h t), (mem_multT θ M J χ _).2 (by simpa using hmult), ?_⟩
  have hw : GlobalTheory.ConjRowMult.vecC X M c v₀ = X.B.w := GlobalTheory.ConjRowMult.vecC_eq X M c v₀ X.B.w hv₀
  obtain ⟨ψ, hψ⟩ := hrep v₀
  rw [hw, hΦw] at hψ
  have key : ∀ x, evS X h t (PiTensorProduct.lift (GlobalTheory.ConjRowMult.conjMap X M c Φ h t) (PiTensorProduct.tprod ℂ v₀)) x = star (ψ x) := by
    intro x
    rw [evS, PiTensorProduct.lift.tprod]
    refine (GlobalTheory.ConjRowMult.conjMap_apply X M c Φ h t v₀ _).trans ?_
    rw [hw, hΦw, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
    have e : ∀ a b : GA D (D.sp.Y 0), a * b * b⁻¹ = a := fun a b => mul_inv_cancel_right a b
    erw [e, ContinuousMulEquiv.apply_symm_apply]
  filter_upwards [hψ.2.2, Lp.coeFn_star φ] with x h1 h2
  rw [key x, ← h1, h2, Pi.star_apply, star_star]

end GlobalTheory.Core.SeeOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepLocalWeilActionLineCharactersCancelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStep_local_weil_action_line_characters_cancel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S)
    (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ))
    (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)),
    (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ →
  ∀ (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (φ : GA D S.B.A → ℂ) (F : GA D S.B'.V → ℂ)
    (a : GL (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) (x : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) (y : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k)
    (Φ₁ Φ₁' : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k))
    (Φ₂ Φ₂' : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k)),
    Φ₁'.1 = om Q.μ₁ a x Φ₁.1 → Φ₂'.1 = om Q.μ₂ x y Φ₂.1 →
    S.val c₁ c₂ (S.s₁.om (Q.gl₀ a, Q.gl₁ x) (T₁ Φ₁)) (S.s₂.om (Q.gl₁ x, Q.gl₂ y) (T₂ Φ₂)) φ F 1 1 1 =
      S.val c₁ c₂ (T₁ Φ₁') (T₂ Φ₂') φ F 1 1 1 := by
  first | exact @GlobalTheory.QPl.LineCancel.val_om_loc | exact GlobalTheory.QPl.LineCancel.val_om_loc | (intros; apply GlobalTheory.QPl.LineCancel.val_om_loc <;> assumption)
end

