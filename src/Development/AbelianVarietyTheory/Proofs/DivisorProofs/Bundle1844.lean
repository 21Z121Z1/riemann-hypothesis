import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1811
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVanishingLevelUnitBlockMulInvStab
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section
namespace GlobalTheory.BotPairSmall.BlockK

theorem blockJ_upper : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (o d : ℕ) (j : GA D d), j ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d →
    ∀ i l : Fin d, i.1 < o → o ≤ l.1 →
      ((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i l ∈ hatId D (D.host.conj • 𝔪) := by
  intro D 𝔪 o d j hj i l hi hl
  have hj' : j⁻¹ ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d := inv_mem hj
  rw [GlobalTheory.BotPairSmall.blockJ_mem_iff_blockSet] at hj'
  have h1 := hj'.2 l i hi hl
  have hu := (GlobalTheory.NormSum.PtsMem.mem_GA D _).1 j.2
  have hJJ : ((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) *
      (((j⁻¹ : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1 := by
    rw [← Units.val_mul]; simp
  have hinv : (((j⁻¹ : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) =
      (((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)).map (sgA D)).transpose := by
    calc _ = ((((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)).map (sgA D)).transpose *
          ((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D))) *
          (((j⁻¹ : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) := by rw [hu, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
  rw [hinv, Matrix.transpose_apply, Matrix.map_apply] at h1
  have h2 := GlobalTheory.FunObj.StdDatum.DetCong.sgA_mem_hatId h1
  rwa [GlobalTheory.NormSum.VacMove.sgA_sgA] at h2

theorem det_mem_OhE {D : D7} {a : ℕ} (M : Matrix (Fin a) (Fin a) (AE D)) (h : ∀ i l, M i l ∈ OhE D) : M.det ∈ OhE D := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

theorem mul_mem_OhE {D : D7} {a : ℕ} (M M' : Matrix (Fin a) (Fin a) (AE D)) (h : ∀ i l, M i l ∈ OhE D)
    (h' : ∀ i l, M' i l ∈ OhE D) : ∀ i l, (M * M') i l ∈ OhE D := fun i l => by
  rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (h _ _) (h' _ _)

theorem exists_k (hB2 : ∀ (D : D7) (𝔫 : Ideal (𝓞 D.host.E)) (a : ℕ) (Z : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) (f w : AE D), f ∈ OhE D → w ∈ OhE D → f * f = f → f * sgA D f = 0 → f = inc D ((Z.det : 𝓞 D.host.E) : D.host.E) * w → 1 - f ∈ hatId D 𝔫 → ∃ k ∈ intG D a, ∀ i l, (Z.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈ hatId D 𝔫) (hB3 : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (δ u : 𝓞 D.host.E), inc D ((δ * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • 𝔪) → ∃ f ∈ OhE D, ∃ w ∈ OhE D, f * f = f ∧ f * sgA D f = 0 ∧ f = inc D (δ : D.host.E) * w ∧ 1 - f ∈ hatId D (D.host.conj • 𝔪)) (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (a : ℕ)
    (Dt Dp : Matrix (Fin a) (Fin a) (AE D)) (hDt : ∀ i l, Dt i l ∈ OhE D) (hDp : ∀ i l, Dp i l ∈ OhE D)
    (hc : ∀ i l, (Dp * Dt - 1) i l ∈ hatId D (D.host.conj • 𝔪)) :
    ∃ k ∈ intG D a, ∀ i l, (Dt - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈
      hatId D (D.host.conj • 𝔪) := by
  have hn : D.host.conj • 𝔪 ≠ ⊥ := GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm
  choose Z hZ using fun i l => GlobalTheory.CongIdx.exists_rep hn (hDt i l)
  set Zm : Matrix (Fin a) (Fin a) (𝓞 D.host.E) := Matrix.of Z with hZm
  set φ : 𝓞 D.host.E →+* AE D := (inc D).comp (algebraMap (𝓞 D.host.E) D.host.E) with hφ
  set Zi : Matrix (Fin a) (Fin a) (AE D) := Zm.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) with hZi
  have hZiO : ∀ i l, Zi i l ∈ OhE D := fun i l => GlobalTheory.NormSum.VacMove.inc_int D _
  have hP : ∀ i l, (Dp * Zi - 1) i l ∈ hatId D (D.host.conj • 𝔪) := by
    intro i l
    have e : Dp * Zi - 1 = Dp * (Zi - Dt) + (Dp * Dt - 1) := by
      rw [Matrix.mul_sub]; abel
    rw [e, Matrix.add_apply]
    refine add_mem ?_ (hc i l)
    rw [Matrix.mul_apply]
    refine sum_mem fun m _ => GlobalTheory.CongIdx.mul_mem_hatId (hDp _ _) ?_
    rw [Matrix.sub_apply, ← neg_sub]
    exact neg_mem (hZ m l)
  have hdet := GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem_hatId_of _ (mul_mem_OhE _ _ hDp hZiO) hP
  have hZdet : Zi.det = inc D ((Zm.det : 𝓞 D.host.E) : D.host.E) := by
    have : Zi = φ.mapMatrix Zm := rfl
    rw [this, ← RingHom.map_det]; rfl
  rw [Matrix.det_mul, hZdet] at hdet
  obtain ⟨u, hu⟩ := GlobalTheory.CongIdx.exists_rep hn (det_mem_OhE Dp hDp)
  have key : inc D ((Zm.det * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • 𝔪) := by
    have e : inc D ((Zm.det * u : 𝓞 D.host.E) : D.host.E) - 1 =
        -(inc D ((Zm.det : 𝓞 D.host.E) : D.host.E) * (Dp.det - inc D (u : D.host.E))) +
          (Dp.det * inc D ((Zm.det : 𝓞 D.host.E) : D.host.E) - 1) := by
      push_cast; rw [map_mul]; ring
    rw [e]
    exact add_mem (neg_mem (GlobalTheory.CongIdx.mul_mem_hatId (GlobalTheory.NormSum.VacMove.inc_int D _) hu)) hdet
  obtain ⟨f, hf, w, hw, hff, hfs, hfw, h1f⟩ := hB3 D 𝔪 hcop _ _ key
  obtain ⟨k, hk, hkc⟩ := hB2 D _ a Zm f w hf hw hff hfs hfw h1f
  refine ⟨k, hk, fun i l => ?_⟩
  have e : (Dt - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l =
      (Dt i l - inc D (Z i l : D.host.E)) +
        (Zi - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l := by
    simp only [Matrix.sub_apply, hZi, Matrix.map_apply, hZm, Matrix.of_apply]; ring
  rw [e]
  exact add_mem (hZ i l) (hkc i l)

theorem blockJ_unitBlock : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (o a d : ℕ), o + a = d → ∀ j ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d, ∃ k ∈ intG D a, ∀ i l, (((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * (unitBlock D o a d).map (inc D) - (unitBlock D o a d).map (inc D) * (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈ hatId D (D.host.conj • 𝔪) := by
  intro D 𝔪 hm hcop o a d hd j hj
  subst hd
  have hA := blockJ_upper D 𝔪 o (o + a) j hj
  have hI := (mem_intG j).1 (GlobalTheory.BotPairSmall.blockJ_le D 𝔪 o (o + a) hj)
  set J : Matrix (Fin (o + a)) (Fin (o + a)) (AE D) := ((j : GL (Fin (o + a)) (AE D)) : Matrix (Fin (o + a)) (Fin (o + a)) (AE D)) with hJ
  set Ji : Matrix (Fin (o + a)) (Fin (o + a)) (AE D) := (((j⁻¹ : GA D (o + a)) : GL (Fin (o + a)) (AE D)) : Matrix (Fin (o + a)) (Fin (o + a)) (AE D)) with hJi
  have hJO : ∀ i l, J i l ∈ OhE D := fun i l => (hI i l).1
  have hJiO : ∀ i l, Ji i l ∈ OhE D := fun i l => by
    have := (hI i l).2
    simpa [hJi] using this
  have hJJ : Ji * J = 1 := by
    rw [hJi, hJ, ← Units.val_mul]; simp
  let Dt : Matrix (Fin a) (Fin a) (AE D) := fun p l => J (Fin.natAdd o p) (Fin.natAdd o l)
  let Dp : Matrix (Fin a) (Fin a) (AE D) := fun p l => Ji (Fin.natAdd o p) (Fin.natAdd o l)
  have hc : ∀ p l, (Dp * Dt - 1) p l ∈ hatId D (D.host.conj • 𝔪) := by
    intro p l
    have e1 := congrFun (congrFun hJJ (Fin.natAdd o p)) (Fin.natAdd o l)
    rw [Matrix.mul_apply, Fin.sum_univ_add] at e1
    have e2 : (1 : Matrix (Fin (o + a)) (Fin (o + a)) (AE D)) (Fin.natAdd o p) (Fin.natAdd o l) =
        (1 : Matrix (Fin a) (Fin a) (AE D)) p l := by
      by_cases h : p = l
      · subst h; rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      · have h' : Fin.natAdd o p ≠ Fin.natAdd o l := fun e => h (Fin.ext (by
          have := congrArg Fin.val e; simp only [Fin.coe_natAdd] at this; omega))
        rw [Matrix.one_apply_ne h', Matrix.one_apply_ne h]
    rw [e2] at e1
    have e3 : (Dp * Dt - 1) p l = -∑ m : Fin o, Ji (Fin.natAdd o p) (Fin.castAdd a m) * J (Fin.castAdd a m) (Fin.natAdd o l) := by
      rw [Matrix.sub_apply, Matrix.mul_apply, ← e1]; ring
    rw [e3]
    refine neg_mem (sum_mem fun m _ => GlobalTheory.CongIdx.mul_mem_hatId (hJiO _ _) (hA _ _ ?_ ?_))
    · simp
    · simp
  obtain ⟨k, hk, hkc⟩ := exists_k GlobalTheory.T.exists_integralUnitary_glue_idempotent (GlobalTheory.T.exists_orthogonalIdempotent_divisible_congruent GlobalTheory.T.exists_idempotent_limit_powers_integralAdeles) D 𝔪 hm hcop a Dt Dp (fun _ _ => hJO _ _) (fun _ _ => hJiO _ _) hc
  refine ⟨k, hk, fun i l => ?_⟩
  set K := (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hK
  have h1 : (J * (unitBlock D o a (o + a)).map (inc D)) i l = J i (Fin.natAdd o l) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.natAdd o l)]
    · rw [Matrix.map_apply]; unfold unitBlock
      rw [Matrix.of_apply, if_pos (by simp only [Fin.coe_natAdd]), map_one, mul_one]
    · intro m _ hm
      have : ¬ (m.1 = o + l.1) := fun h => hm (Fin.ext (by simp only [Fin.coe_natAdd]; exact h))
      rw [Matrix.map_apply]; unfold unitBlock
      rw [Matrix.of_apply, if_neg this, map_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Matrix.sub_apply, h1]
  refine Fin.addCases (fun i' => ?_) (fun p => ?_) i
  · have h2 : ((unitBlock D o a (o + a)).map (inc D) * K) (Fin.castAdd a i') l = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      have : ¬ ((Fin.castAdd a i' : Fin (o + a)).1 = o + m.1) := by simp only [Fin.coe_castAdd]; omega
      rw [Matrix.map_apply]; unfold unitBlock
      rw [Matrix.of_apply, if_neg this, map_zero, zero_mul]
    rw [h2, sub_zero]
    exact hA _ _ (by simp) (by simp)
  · have h2 : ((unitBlock D o a (o + a)).map (inc D) * K) (Fin.natAdd o p) l = K p l := by
      rw [Matrix.mul_apply, Finset.sum_eq_single p]
      · rw [Matrix.map_apply]; unfold unitBlock
        rw [Matrix.of_apply, if_pos (by simp only [Fin.coe_natAdd]), map_one, one_mul]
      · intro m _ hm
        have : ¬ ((Fin.natAdd o p : Fin (o + a)).1 = o + m.1) := by
          simp only [Fin.coe_natAdd]; intro h; exact hm (Fin.ext (by omega))
        rw [Matrix.map_apply]; unfold unitBlock
        rw [Matrix.of_apply, if_neg this, map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h2]
    exact hkc p l

end GlobalTheory.BotPairSmall.BlockK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxGraphGraphHeis
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat.GraphHeis

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

variable {D : D7}

theorem isHalf_nsmul' {m n : ℕ} {ε : AE D} {a : Mx D m n} (ha : IsHalf ε a) (k : ℕ) : IsHalf ε (k • a) :=
  fun i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, ha i j]

theorem isHalf_of_add' {m n : ℕ} {ε : AE D} {a b : Mx D m n} (h : IsHalf ε (a + b)) (hb : IsHalf ε b) : IsHalf ε a :=
  fun i j => by
    have h1 := h i j
    rw [Matrix.add_apply, mul_add, hb i j] at h1
    exact add_right_cancel h1

theorem sb_trans {m n : ℕ} {ε : AE D} {Λ : AddSubgroup (Mx D m n)} {φ : Mx D m n → ℂ} (h : IsSBHalf ε Λ φ)
    {x : Mx D m n} (hx : IsHalf ε x) {k₀ : ℕ} (hk₀ : 0 < k₀) (hkx : k₀ • x ∈ Λ) :
    IsSBHalf ε Λ (fun t => φ (t + x)) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => isHalf_of_add' (h1 _ ht) hx, k * k₀, Nat.mul_pos hk hk₀, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · show φ (t + (k * k₀) • u + x) = φ (t + x)
    rw [show t + (k * k₀) • u + x = (t + x) + k • (k₀ • u) by rw [mul_smul]; abel]
    exact h2 _ (nsmul_mem hu k₀) (isHalf_nsmul' hu' k₀) _
  · have e : (k * k₀) • t = k₀ • (k • (t + x)) - k • (k₀ • x) := by
      rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, mul_comm k₀ k]; abel
    rw [e]
    exact sub_mem (nsmul_mem (h3 _ ht) k₀) (nsmul_mem hkx k)

theorem sb_modul {m n : ℕ} {ε : AE D} {Λ : AddSubgroup (Mx D m n)} {φ : Mx D m n → ℂ} (h : IsSBHalf ε Λ φ)
    (χ : Mx D m n → ℂ) (hχ : ∀ a b, χ (a + b) = χ a * χ b) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (h1χ : ∀ u ∈ Λ, IsHalf ε u → χ (k₀ • u) = 1) : IsSBHalf ε Λ (fun t => χ t * φ t) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => h1 t (right_ne_zero_of_mul ht), k₀ * k, Nat.mul_pos hk₀ hk, fun u hu hu' t => ?_,
    fun t ht => ?_⟩
  · show χ (t + (k₀ * k) • u) * φ (t + (k₀ * k) • u) = χ t * φ t
    rw [hχ, mul_smul, h1χ _ (nsmul_mem hu k) (isHalf_nsmul' hu' k), mul_one, smul_comm k₀ k u,
      h2 _ (nsmul_mem hu k₀) (isHalf_nsmul' hu' k₀)]
  · rw [mul_smul]
    exact nsmul_mem (h3 t (right_ne_zero_of_mul ht)) k₀

theorem symplO_add_left' (S T : HSp D) (x x' y : WO S T) : symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  simp only [symplO, hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib, LinearMap.map_add]

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) : symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, RingHom.map_add, map_add (cA D), mul_add, add_mul, Finset.sum_add_distrib,
    LinearMap.map_add]

theorem symplO_nsmul' (S T : HSp D) (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  have h1 := map_nsmul (AddMonoidHom.mk' (fun x => symplO S T x y) fun a b => symplO_add_left' S T a b y) k x
  have h2 := map_nsmul (AddMonoidHom.mk' (fun y => symplO S T x y) fun a b => symplO_add_right' S T x a b) k y
  exact h1.trans h2.symm

theorem map_infPart_of_half {S T : HSp D} {a : AE D} (ha : infPart D a = 0) {u : WO S T} (hu : IsHalf a u) :
    u.map (infPart D) = 0 := by
  ext i j
  show infPart D (u i j) = 0
  rw [← hu i j, map_mul, ha, zero_mul]

theorem sb_trans_latO {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : Submodule.IsLattice D.host.E ΛS)
    (hT : Submodule.IsLattice D.host.E ΛT) {ε : AE D} (hinf : infPart D ε = 0) {φ : WO S T → ℂ}
    (h : IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) φ)
    {x : WO S T} (hx : IsHalf ε x) :
    IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (fun t => φ (t + x)) := by
  obtain ⟨k, hk, hkx⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_latO hS hT x (map_infPart_of_half hinf hx)
  exact sb_trans h hx hk hkx

theorem sb_modul_latO {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {ε : AE D} (hinf : infPart D (cA D ε) = 0) {φ : WO S T → ℂ}
    (h : IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) φ)
    {y : WO S T} (hy : IsHalf (cA D ε) y) :
    IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (fun t => ψ (symplO S T t y) * φ t) := by
  obtain ⟨k, hk, hky⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_latO hS.1 hT.1 y (map_infPart_of_half hinf hy)
  refine sb_modul h (fun t => ψ (symplO S T t y)) (fun a b => ?_) hk (fun u hu _ => ?_)
  · show ψ (symplO S T (a + b) y) = ψ (symplO S T a y) * ψ (symplO S T b y)
    rw [symplO_add_left', AddChar.map_add_eq_mul]
  · show ψ (symplO S T (k • u) y) = 1
    rw [symplO_nsmul']
    exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hu hky

end GlobalTheory.BigDat.GraphHeis

namespace GlobalTheory.BigDat

open GlobalTheory.BigDat.GraphHeis

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

def graphMap (e : Num G i j) (T₁ : (HomV G i j → ℂ) →ₗ[ℂ] (HomV G i j → ℂ))
    (T₂ : (HomW G i j → ℂ) →ₗ[ℂ] (HomW G i j → ℂ)) : (Pt G i j → ℂ) →ₗ[ℂ] (Pt G i j → ℂ) where
  toFun g u := T₁ (fun x => T₂ (fun y => g (ofMaps e (x, y))) (mapW e u)) (mapV e u)
  map_add' g g' := funext fun u => by
    have h : (fun x => T₂ (fun y => (g + g') (ofMaps e (x, y))) (mapW e u)) =
        (fun x => T₂ (fun y => g (ofMaps e (x, y))) (mapW e u)) + fun x => T₂ (fun y => g' (ofMaps e (x, y))) (mapW e u) :=
      funext fun x => by
        show T₂ ((fun y => g (ofMaps e (x, y))) + fun y => g' (ofMaps e (x, y))) (mapW e u) = _
        rw [map_add]; rfl
    show T₁ (fun x => T₂ (fun y => (g + g') (ofMaps e (x, y))) (mapW e u)) (mapV e u) = _
    rw [h, map_add]; rfl
  map_smul' c g := funext fun u => by
    have h : (fun x => T₂ (fun y => (c • g) (ofMaps e (x, y))) (mapW e u)) =
        c • fun x => T₂ (fun y => g (ofMaps e (x, y))) (mapW e u) :=
      funext fun x => by
        show T₂ (c • fun y => g (ofMaps e (x, y))) (mapW e u) = _
        rw [map_smul]; rfl
    show T₁ (fun x => T₂ (fun y => (c • g) (ofMaps e (x, y))) (mapW e u)) (mapV e u) = _
    rw [h, map_smul]; rfl

theorem graphMap_box (e : Num G i j) (T₁ : (HomV G i j → ℂ) →ₗ[ℂ] (HomV G i j → ℂ))
    (T₂ : (HomW G i j → ℂ) →ₗ[ℂ] (HomW G i j → ℂ)) (φ₁ : HomV G i j → ℂ) (φ₂ : HomW G i j → ℂ) :
    graphMap e T₁ T₂ (box e φ₁ φ₂) = box e (T₁ φ₁) (T₂ φ₂) := funext fun u => by
  have e2 : ∀ x, (fun y => box e φ₁ φ₂ (ofMaps e (x, y))) = φ₁ x • φ₂ := fun x => funext fun y => by
    show φ₁ (mapV e (ofMaps e (x, y))) * φ₂ (mapW e (ofMaps e (x, y))) = φ₁ x * φ₂ y
    rw [mapV_ofMaps, mapW_ofMaps]
  have e1 : (fun x => T₂ (fun y => box e φ₁ φ₂ (ofMaps e (x, y))) (mapW e u)) = T₂ φ₂ (mapW e u) • φ₁ :=
    funext fun x => by
      rw [e2, map_smul]
      show φ₁ x * T₂ φ₂ (mapW e u) = T₂ φ₂ (mapW e u) * φ₁ x
      exact mul_comm _ _
  show T₁ (fun x => T₂ (fun y => box e φ₁ φ₂ (ofMaps e (x, y))) (mapW e u)) (mapV e u) = T₁ φ₁ (mapV e u) * T₂ φ₂ (mapW e u)
  rw [e1, map_smul]
  show T₂ φ₂ (mapW e u) * T₁ φ₁ (mapV e u) = _
  exact mul_comm _ _

def transPair (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (x : Pt G i j) :
    ((Pt G i j → ℂ) × (Pt G i j → ℂ)) →ₗ[ℂ] ((Pt G i j → ℂ) × (Pt G i j → ℂ)) where
  toFun p := (fun u => p.1 (u + x), heisPt Γ ψ x p.2)
  map_add' p q := Prod.ext rfl (funext fun u => mul_add _ _ _)
  map_smul' c p := Prod.ext rfl (funext fun u => mul_left_comm _ _ _)

def modulPair (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (y : Pt G i j) :
    ((Pt G i j → ℂ) × (Pt G i j → ℂ)) →ₗ[ℂ] ((Pt G i j → ℂ) × (Pt G i j → ℂ)) where
  toFun p := (fun u => ψ (sympPt Γ u y) * p.1 u, heisPt Γ ψ y p.2)
  map_add' p q := Prod.ext (funext fun u => mul_add _ _ _) (funext fun u => mul_add _ _ _)
  map_smul' c p := Prod.ext (funext fun u => mul_left_comm _ _ _) (funext fun u => mul_left_comm _ _ _)

end GlobalTheory.BigDat

set_option maxHeartbeats 1600000 in
open GlobalTheory.BigDat.GraphHeis in

theorem GlobalTheory.BigDat.boxGraph_graph_heis : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e → ∀ (ε : AE D) (P : Finset (Pl D.host.E)), IsIdemSum ε P →
    ∀ (f₁ : HomV G i j → ℂ) (f₂ : HomW G i j → ℂ) (T₁ : (HomV G i j → ℂ) →ₗ[ℂ] (HomV G i j → ℂ))
      (T₂ : (HomW G i j → ℂ) →ₗ[ℂ] (HomW G i j → ℂ)),
    IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) ε (latV G i j) 1 f₁ T₁ →
    IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) ε (latW G i j) 1 f₂ T₂ →
    (∀ f, (0, f) ∈ boxGraph e ε T₁ T₂ → f = 0) ∧
    (∀ x ∈ mixHalf e ε, ∀ p ∈ boxGraph e ε T₁ T₂, (fun u => p.1 (u + x), heisPt Γ W.ψ x p.2) ∈ boxGraph e ε T₁ T₂) ∧
    ∀ y ∈ mixHalf e (cA D ε), ∀ p ∈ boxGraph e ε T₁ T₂,
      (fun u => W.ψ (sympPt Γ u y) * p.1 u, heisPt Γ W.ψ y p.2) ∈ boxGraph e ε T₁ T₂ := by
  intro D T L sc G μ₀ hL W i j e Γ hW hWW ε P hε f₁ f₂ T₁ T₂ h₁ h₂
  have hinf : infPart D ε = 0 := GlobalTheory.PlaceVec.idemSum_infPart hε
  have hinf' : infPart D (cA D ε) = 0 := GlobalTheory.PlaceVec.infPart_cA hinf
  have sdW : IsSelfDualC (spW G i j) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).sd
  have sdV : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have sdV₁ : IsSelfDualC (spV₁ G i j) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have sdW' : IsSelfDualC (negSp (spW G i j)) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) := isSelfDualC_neg sdW
  refine ⟨fun f hf => ?_, fun x hx p hp => ?_, fun y hy p hp => ?_⟩
  · have key : boxGraph e ε T₁ T₂ ≤ LinearMap.ker (LinearMap.snd ℂ _ _ - graphMap e T₁ T₂ ∘ₗ LinearMap.fst ℂ _ _) := by
      refine Submodule.span_le.2 fun p hp => ?_
      obtain ⟨φ₁, φ₂, -, -, rfl⟩ := hp
      show box e (T₁ φ₁) (T₂ φ₂) - graphMap e T₁ T₂ (box e φ₁ φ₂) = 0
      rw [graphMap_box, sub_self]
    have h0 := key hf
    rw [LinearMap.mem_ker] at h0
    have h1 : f - graphMap e T₁ T₂ 0 = 0 := h0
    rwa [map_zero, sub_zero] at h1
  · have key : boxGraph e ε T₁ T₂ ≤ (boxGraph e ε T₁ T₂).comap (transPair Γ W.ψ x) := by
      refine Submodule.span_le.2 fun p hp => ?_
      obtain ⟨φ₁, φ₂, hφ₁, hφ₂, rfl⟩ := hp
      have hx₁ : IsHalf ε (mapV e x) := hx.1
      have hx₂ : IsHalf ε (mapW e x) := hx.2
      have s₁ : IsSBHalf ε (latV G i j) (fun t => φ₁ (t + mapV e x)) :=
        sb_trans_latO (S := negSp (spW G i j)) (T := spV G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)))
          (ΛT := G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) sdW'.1 sdV.1 hinf hφ₁ hx₁
      have s₂ : IsSBHalf ε (latW G i j) (fun t => φ₂ (t + mapW e x)) :=
        sb_trans_latO (S := spV₁ G i j) (T := spW G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) (j : ℕ)))
          (ΛT := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) sdV₁.1 sdW.1 hinf hφ₂ hx₂
      show (fun u => box e φ₁ φ₂ (u + x), heisPt Γ W.ψ x (box e (T₁ φ₁) (T₂ φ₂))) ∈ boxGraph e ε T₁ T₂
      rw [heisPt_box e Γ hW hWW]
      refine Submodule.subset_span ⟨_, _, s₁, s₂, ?_⟩
      rw [h₁.trans φ₁ hφ₁ _ hx₁, h₂.trans φ₂ hφ₂ _ hx₂]
      refine Prod.ext (funext fun u => ?_) rfl
      show φ₁ (mapV e (u + x)) * φ₂ (mapW e (u + x)) = φ₁ (mapV e u + mapV e x) * φ₂ (mapW e u + mapW e x)
      rw [mapV_add, mapW_add]
    exact key hp
  · have key : boxGraph e ε T₁ T₂ ≤ (boxGraph e ε T₁ T₂).comap (modulPair Γ W.ψ y) := by
      refine Submodule.span_le.2 fun p hp => ?_
      obtain ⟨φ₁, φ₂, hφ₁, hφ₂, rfl⟩ := hp
      have hy₁ : IsHalf (cA D ε) (mapV e y) := hy.1
      have hy₂ : IsHalf (cA D ε) (mapW e y) := hy.2
      have s₁ : IsSBHalf ε (latV G i j) (fun t => W.ψ (symplO _ _ t (mapV e y)) * φ₁ t) :=
        sb_modul_latO (S := negSp (spW G i j)) (T := spV G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)))
          (ΛT := G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) W.ψ_std sdW' sdV hinf' hφ₁ hy₁
      have s₂ : IsSBHalf ε (latW G i j) (fun t => W.ψ (symplO _ _ t (mapW e y)) * φ₂ t) :=
        sb_modul_latO (S := spV₁ G i j) (T := spW G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) (j : ℕ)))
          (ΛT := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) W.ψ_std sdV₁ sdW hinf' hφ₂ hy₂
      show (fun u => W.ψ (sympPt Γ u y) * box e φ₁ φ₂ u, heisPt Γ W.ψ y (box e (T₁ φ₁) (T₂ φ₂))) ∈ boxGraph e ε T₁ T₂
      rw [heisPt_box e Γ hW hWW]
      refine Submodule.subset_span ⟨_, _, s₁, s₂, ?_⟩
      rw [h₁.modul φ₁ hφ₁ _ hy₁, h₂.modul φ₂ hφ₂ _ hy₂]
      refine Prod.ext (funext fun u => ?_) rfl
      show W.ψ (sympPt Γ u y) * (φ₁ (mapV e u) * φ₂ (mapW e u)) =
        (W.ψ (symplO _ _ (mapV e u) (mapV e y)) * φ₁ (mapV e u)) * (W.ψ (symplO _ _ (mapW e u) (mapW e y)) * φ₂ (mapW e u))
      rw [symp_eq e Γ hW hWW, AddChar.map_add_eq_mul]
      ring
    exact key hp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointIntegralFrameMemSpanEigenLatticeStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_point_integral_frame_mem_span_eigen_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → (∀ i, (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)))) := by
  first | exact @GlobalTheory.PtDeg.intFrame_mem_span_eigLat | exact GlobalTheory.PtDeg.intFrame_mem_span_eigLat | (intros; apply GlobalTheory.PtDeg.intFrame_mem_span_eigLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnSubstitutionUnitaryOfKillsLieCoinvariantsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnSubstitution_unitary_of_kills_lieCoinvariants : ∀ (D : D7) (ε : Bool) (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (eT : D.what₂.Tau → ℚ)
    (n₀ : D.what₂.Tau → ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q] (q : PolF D X.rank M.rank →ₗ[ℂ] Q),
    (∀ τ j, A.ε τ j = true) → (∀ τ i, B.ε τ i = true) →
    (∀ τ, (n₀ τ : ℚ) = (if ε then eT τ else -eT τ) - (X.rank : ℚ) / 2) →
    GlobalTheory.RealQuot.coinv ε A B eT ≤ LinearMap.ker q →
    ∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin M.rank) ℂ) (P : PolF D X.rank M.rank),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ)) • q P := by
  first | exact @GlobalTheory.LieInt.colSub_unitary_of_coinv | exact GlobalTheory.LieInt.colSub_unitary_of_coinv | (intros; apply GlobalTheory.LieInt.colSub_unitary_of_coinv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformRealLinesCmExtensionStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_thetaTransform_realLines_cmExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L →
            (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
            ∀ w, ContDiff ℝ ∞ fun t => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (w + L t) := by
  first | exact @GlobalTheory.ThetaSmoothCM.contDiff_thetaTr_real_CM | exact GlobalTheory.ThetaSmoothCM.contDiff_thetaTr_real_CM | (intros; apply GlobalTheory.ThetaSmoothCM.contDiff_thetaTr_real_CM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalTraceMultiplicityGivenStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_trace_multiplicity_given : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.GreenCuspidal → TRCusp → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.CuspMult.MultEq R := by
  first | exact @GlobalTheory.MultEqTrace.multEq_of_trCusp | exact GlobalTheory.MultEqTrace.multEq_of_trCusp | (intros; apply GlobalTheory.MultEqTrace.multEq_of_trCusp <;> assumption)
end

