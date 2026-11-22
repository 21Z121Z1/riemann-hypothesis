import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0180
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0240
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0202
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0340
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0172
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0327
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeTransformEqAtThetaLiftOfVacuumEq
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta

theorem prodId1 : ∀ (n : ℕ) (qu : ℂˣ) (Y : ℂ), Y ≠ 0 → ∀ (α : Fin (n / 2) → ℂˣ) (d : Fin (n / 2) → ℤ), (∏ k, Y ^ d k) * ∏ r : Fin (n / 2), (Y * (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ (-d r.rev) = ∏ k, ((α k : ℂ) * (qu : ℂ) ^ (-((n : ℤ) - 1 - 2 * (k : ℤ)))) ^ d k := by
  intro n qu Y hY α d
  have hq := qu.ne_zero
  have hα : ∀ k, (α k : ℂ) ≠ 0 := fun k => (α k).ne_zero
  rw [← Equiv.prod_comp Fin.revPerm]
  conv_rhs => rw [← Equiv.prod_comp Fin.revPerm]
  simp only [Fin.revPerm_apply]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [_root_.zpow_neg, ← div_eq_mul_inv, ← div_zpow]
  congr 1
  have e : ((n / 2 : ℕ) : ℤ) - 1 - ((k : ℕ) : ℤ) = ((k.rev : ℕ) : ℤ) := by
    have := k.isLt
    rw [Fin.val_rev]; omega
  rw [e, _root_.zpow_neg]
  have := hα k.rev
  have := zpow_ne_zero ((n : ℤ) - 1 - 2 * ((k.rev : ℕ) : ℤ)) hq
  field_simp

theorem prodId2 : ∀ (n n' : ℕ) (hn : n ≤ n') (qu : ℂˣ) (α : Fin (n / 2) → ℂˣ) (d : Fin (n' / 2) → ℤ), (∏ k, ((-1) ^ n * (qu : ℂ) ^ (-(n : ℤ))) ^ d k) * ∏ r : Fin (n / 2), ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') * (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ d ⟨n' / 2 - n / 2 + r.1, by omega⟩ = ∏ k, ((liftPar qu n n' α k : ℂ) * (qu : ℂ) ^ (-((n' : ℤ) - 1 - 2 * (k : ℤ)))) ^ d k := by
  intro n n' hn qu α d
  have hq := qu.ne_zero
  have hfac : ∀ k : Fin (n' / 2), ((liftPar qu n n' α k : ℂ) * (qu : ℂ) ^ (-((n' : ℤ) - 1 - 2 * (k : ℤ)))) =
      ((-1) ^ n * (qu : ℂ) ^ (-(n : ℤ))) * (if h : n' / 2 - n / 2 ≤ k.1 then
        ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
          (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - ((k.1 - (n' / 2 - n / 2) : ℕ) : ℤ))) /
          (α (Fin.rev ⟨k.1 - (n' / 2 - n / 2), by omega⟩) : ℂ)) else 1) := by
    intro k
    unfold liftPar
    split_ifs with h1 h2 h2
    · omega
    · push_cast
      rw [mul_one, mul_assoc, ← zpow_add₀ hq]
      congr 2; ring
    · have e : (Fin.rev ⟨k.1 - (n' / 2 - n / 2), by omega⟩ : Fin (n / 2)) = ⟨n' / 2 - 1 - k.1, by omega⟩ :=
        Fin.ext (by simp only [Fin.val_rev]; omega)
      rw [e]
      have e2 : (qu : ℂ) ^ (-((n' : ℤ) - 1 - 2 * (k : ℤ))) = (qu : ℂ) ^ (-(n : ℤ)) * ((qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
          (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - ((k.1 - (n' / 2 - n / 2) : ℕ) : ℤ)))) := by
        rw [← zpow_add₀ hq, ← zpow_add₀ hq]
        congr 1
        have := k.isLt
        omega
      rw [e2]
      push_cast
      rw [pow_add]
      have := (α ⟨n' / 2 - 1 - k.1, by omega⟩).ne_zero
      field_simp
    · omega
  simp only [hfac, mul_zpow, Finset.prod_mul_distrib]
  congr 1
  symm
  rw [← Fin.prod_congr' _ (show n' / 2 - n / 2 + n / 2 = n' / 2 by omega), Fin.prod_univ_add]
  rw [Finset.prod_eq_one (fun i _ => ?_), one_mul]
  · refine Finset.prod_congr rfl fun r _ => ?_
    have e : Fin.cast (show n' / 2 - n / 2 + n / 2 = n' / 2 by omega) (Fin.natAdd (n' / 2 - n / 2) r) =
        ⟨n' / 2 - n / 2 + r.1, by omega⟩ := Fin.ext (by simp)
    rw [e, dif_pos (by simp)]
    simp only [Fin.val_mk, Nat.add_sub_cancel_left, Fin.eta]
  · rw [dif_neg (by simp; omega), _root_.one_zpow]

theorem satU_eq_satU_liftPar_of_heckeVec_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n' ρ (ω.comp (MonoidHom.inl _ _)) s → CayleyRule q n ρ (ω.comp (MonoidHom.inr _ _)) s → n ≤ n' → ∀ h ∈ Hecke ℂ (KU σ n), ∀ h' ∈ Hecke ℂ (KU σ n'), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s = heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s → ∀ qu : ℂˣ, (qu : ℂ) = q → ∀ α : Fin (n / 2) → ℂˣ, SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h' (fun i => (liftPar qu n n' α i : ℂ)) := by
  intro L _ _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS hC hC' hnn h hh h' hh' hE qu hqu α
  have hU := hS.1.unr
  obtain ⟨ℓ, hℓs, hℓa, hℓ0, hℓu, hℓz⟩ := GlobalTheory.T.exists_mixedModelSelfDualLattice_invariant_linearForm L ϖ σ q δ ψ n n' M ρ ω s hS
  have hvac : LocVac ρ s := hS.2.2.1
  have hb1 : ∀ {N : ℕ}, IsBorelU (1 : GU σ N) := fun i j hij => by
    simp [Matrix.one_apply_ne (ne_of_gt hij)]
  have hmix := GlobalTheory.T.mixedModelInvariantForm_upperTriangular_pair_action L ϖ σ q δ ψ n n' M ρ ω s hS ℓ hℓa hℓu
  have hμ : ∀ b : GU σ n, IsBorelU b → ℓ (ω (b, 1) s) =
      ∏ k, ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n')) ^ ordL (b.1.1 (lo n k) (lo n k)) := by
    refine GlobalTheory.T.borelMultiplicative_eq_prod_diagonal_valuations L ϖ σ q hU n (fun g => ℓ (ω (g, 1) s)) ?_ ?_ _ ?_
    · intro b b' hb hb'
      have : ω (b * b', 1) s = ω (b, 1) (ω (b', 1) s) := by
        rw [show ((b * b', 1) : GU σ n × GU σ n') = (b, 1) * (b', 1) by simp, map_mul, Module.End.mul_apply]
      simp only [this]
      exact (hmix b 1 hb hb1).1 _
    · intro k hk _
      exact (congrArg ℓ (hS.1.fix k 1 (mem_KU_iff.1 hk) (by simpa using one_mem _) s hvac)).trans hℓs
    · intro k t ht
      rw [GlobalTheory.T.mixedModelForm_value_torusGenerator_firstGroup L ϖ σ q δ ψ n n' M ρ ω s hS hC ℓ hℓs hℓa hℓ0 k t ht, hqu]
  have hμ' : ∀ b : GU σ n', IsBorelU b → ℓ (ω (1, b) s) =
      ∏ k, ((-1) ^ n * (qu : ℂ) ^ (-(n : ℤ))) ^ ordL (b.1.1 (lo n' k) (lo n' k)) := by
    refine GlobalTheory.T.borelMultiplicative_eq_prod_diagonal_valuations L ϖ σ q hU n' (fun g => ℓ (ω (1, g) s)) ?_ ?_ _ ?_
    · intro b b' hb hb'
      have : ω (1, b * b') s = ω (1, b) (ω (1, b') s) := by
        rw [show ((1, b * b') : GU σ n × GU σ n') = (1, b) * (1, b') by simp, map_mul, Module.End.mul_apply]
      simp only [this]
      exact (hmix 1 b hb1 hb).1 _
    · intro k hk _
      exact (congrArg ℓ (hS.1.fix 1 k (by simpa using one_mem _) (mem_KU_iff.1 hk) s hvac)).trans hℓs
    · intro k t ht
      rw [GlobalTheory.T.mixedForm_torusTranslate_vacuum_value L ϖ σ q δ ψ n n' M ρ ω s hS hC' ℓ hℓs hℓa hℓ0 k t ht, hqu]
  obtain ⟨ι, _, b, hb, hvec, hsat⟩ := GlobalTheory.T.heckeVec_satake_sum_unitaryBorel_representatives L ϖ σ q hU n h hh
  obtain ⟨κ, _, b', hb', hvec', hsat'⟩ := GlobalTheory.T.heckeVec_satake_sum_unitaryBorel_representatives L ϖ σ q hU n' h' hh'
  have E := hE
  rw [hvec M (ω.comp (MonoidHom.inl _ _)) s (fun k hk => hS.1.fix k 1 (mem_KU_iff.1 hk) (by simpa using one_mem _) s hvac),
    hvec' M (ω.comp (MonoidHom.inr _ _)) s (fun k hk => hS.1.fix 1 k (by simpa using one_mem _) (mem_KU_iff.1 hk) s hvac)] at E
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply] at E
  obtain ⟨hbl1, hbl2⟩ := GlobalTheory.T.upperTriangularUnitary_lowerHalfBlock_triangular L ϖ σ q hU n n' hnn
  choose U hU1 hU2 hU3 using fun i => hbl1 (b i) (hb i)
  choose V hVt hV2 hV3 using fun j => hbl2 (b' j) (hb' j)
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin (n / 2)) (Fin (n / 2)) L → Matrix (Fin (n' / 2)) (Fin (n / 2)) L,
      ∀ t, Z t = Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then t ⟨r.1, e⟩ c else 0 :=
    ⟨_, fun _ => rfl⟩
  have hZmul : ∀ t A, Z t * A = Z (t * A) := by
    intro t A; ext r c
    simp only [hZ, Matrix.mul_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hZint : ∀ t, Z t ∈ intMat L (Fin (n' / 2)) (Fin (n / 2)) ↔ t ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) := by
    intro t
    constructor
    · intro ht i j
      have := ht ⟨i.1, by omega⟩ j
      simpa [hZ] using this
    · intro ht i j
      simp only [hZ, Matrix.of_apply]
      split_ifs
      exacts [ht _ _, zero_mem _]
  have hlow1 : ∀ N : ℕ, lowBlock (((1 : GU σ N) : GL (Fin N) L) : Matrix (Fin N) (Fin N) L) = 1 := by
    intro N
    simp only [OneMemClass.coe_one, Units.val_one, lowBlock]
    exact Matrix.submatrix_one _ (fun a b e => by simp [hi, Fin.ext_iff] at e; exact Fin.ext (by omega))
  have key : ∀ t : GL (Fin (n / 2)) L,
      ∑ i, (h (b i) * ℓ (ω (b i, 1) s)) * (if t.1 * (U i).1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) =
      ∑ j, (h' (b' j) * ℓ (ω (1, b' j) s)) * (if (V j).1 * t.1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) := by
    intro t
    have l1 : ∀ i, ℓ (ρ (embLow n' n (Z t.1)) (ω (b i, 1) s)) =
        ℓ (ω (b i, 1) s) * (if t.1 * (U i).1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) := by
      intro i
      rw [(hmix (b i) 1 (hb i) hb1).2, inv_one, hlow1, Matrix.one_mul, ← hU1 i, hZmul, hℓz, hZint]
    have l2 : ∀ j, ℓ (ρ (embLow n' n (Z t.1)) (ω (1, b' j) s)) =
        ℓ (ω (1, b' j) s) * (if (V j).1 * t.1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) := by
      intro j
      have e3 := hV3 j t.1
      simp only [← hZ] at e3
      rw [(hmix 1 (b' j) hb1 (hb' j)).2, hlow1, Matrix.mul_one, e3, hℓz, hZint]
    have := congrArg (fun v => ℓ (ρ (embLow n' n (Z t.1)) v)) E
    simp only [map_sum, map_smul, smul_eq_mul, l1, l2] at this
    simpa only [mul_assoc] using this
  have G := GlobalTheory.T.sum_diag_order_eq_of_integralTranslateIndicator_relation L ϖ σ q hU (n / 2) ι κ _ _ U V hU2 hVt key
    (fun d => ∏ r : Fin (n / 2), ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
      (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ d r)
  have hY : ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') : ℂ) ≠ 0 := by
    have := qu.ne_zero
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (zpow_ne_zero _ this)
  rw [hsat α, hsat' (liftPar qu n n' α)]
  simp only [← hqu]
  calc _ = ∑ i, (h (b i) * ℓ (ω (b i, 1) s)) * ∏ r : Fin (n / 2), ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
        (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ ordL ((U i).1 r r) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hμ _ (hb i), mul_assoc, ← prodId1 n qu _ hY α]
        simp only [hU3]
    _ = _ := G
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hμ' _ (hb' j), mul_assoc, ← prodId2 n n' hnn qu α]
        simp only [hV2]

end GlobalTheory.SphTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeTrivialBoundInertPlaceUnitarisableSpherica
section
noncomputable section

namespace GlobalTheory.SatBoundInert

open Formalism.UG GlobalTheory.PRep GlobalTheory.LGrp GlobalTheory.LFun

theorem norm_form_le {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ)
    (hsym : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hpos : ∀ v, v ≠ 0 → 0 < (B v v).re) (u v : V)
    (h : B u u = B v v) : ‖B u v‖ ≤ (B v v).re := by
  have hnn : ∀ z, 0 ≤ (B z z).re := fun z => by
    by_cases hz : z = 0
    · simp [hz]
    · exact (hpos z hz).le
  by_cases h0 : B u v = 0
  · rw [h0, norm_zero]; exact hnn v
  have hn : (‖B u v‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 h0)
  have hz := hnn (u - (B u v / (‖B u v‖ : ℂ)) • v)
  have e : B (u - (B u v / (‖B u v‖ : ℂ)) • v) (u - (B u v / (‖B u v‖ : ℂ)) • v) =
      B u u - starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B u v - (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v) +
        (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B v v := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul]
    rw [hsym u v]
    ring
  have h1 : starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B u v = ‖B u v‖ := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul', sq]
    field_simp
  have h2 : (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v) = ‖B u v‖ := by
    rw [div_mul_eq_mul_div, Complex.mul_conj', sq]
    field_simp
  have h3 : (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) = 1 := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj', sq]
    field_simp
  rw [e, h1, h2, h3, h] at hz
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, one_mul] at hz
  linarith

theorem satakeBoundInert : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.SatakeBoundInert := by
  intro L _ _ _ ϖ σ q n hU V _ _ π α _ hun hsat
  obtain ⟨B, hsym, hpos, hinv⟩ := hun
  obtain ⟨x, hx⟩ := hsat.exists_vec
  have hxx : B x x ≠ 0 := fun h => by
    have := hpos x hx.1
    rw [h] at this
    simp at this
  let c : ℂ := (B x x)⁻¹
  let l : V →ₗ[ℂ] ℂ :=
    { toFun := fun y => B y x * c
      map_add' := fun a b => by simp [add_mul]
      map_smul' := fun a y => by simp [mul_assoc] }
  have hl : ∀ k ∈ KU σ n, ∀ y, l (π k y) = l y := fun k hk y => by
    show B (π k y) x * c = B y x * c
    conv_lhs => rw [← GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk]
    rw [hinv]
  have h1 : l x = 1 := mul_inv_cancel₀ hxx
  have hz := GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.isZonal_of_isSatVecU hU hx l hl h1
  have hϖ : ϖ ≠ 0 := by
    intro h
    have := hU.2.2.2.1
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  refine GlobalTheory.T.satakeTrivialBound_of_bounded_zonal_spherical_unitary GlobalTheory.InertZeta.unramDoublingInert L (Units.mk0 ϖ hϖ) σ q n hU α _ hz ⟨(B x x).re * ‖c‖, fun g => ?_⟩
  show ‖B (π g x) x * c‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_form_le B hsym hpos _ _ (hinv g x x)) (norm_nonneg _)

end GlobalTheory.SatBoundInert

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelCoordinatesBijOnAndWeilLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitCoordModel

variable {D : D7}

theorem exists_haar (v : FinPl D) : ∃ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  exact ⟨MeasureTheory.Measure.addHaar, inferInstance⟩

theorem pull_sub {S T : HSp D} {v : FinPl D} {m n : ℕ} (a : AE D)
    (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)) (Φ₁ Φ₂ : Matrix (Fin m) (Fin n) (Fv D.host.F v) → ℂ) :
    pull a κ (Φ₁ - Φ₂) = pull a κ Φ₁ - pull a κ Φ₂ := by
  funext t
  simp only [pull, Pi.sub_apply]
  split_ifs <;> simp

theorem ipO_smul_smul {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (c : ℂ) (f : Mx D m n → ℂ) :
    ipO μ 𝓕 (c • f) (c • f) = (c * (starRingEnd ℂ) c) * ipO μ 𝓕 f f := by
  unfold ipO
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext w
  ring

theorem bijOn_and_om_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (e a : AE D), IsSplitIdem D e → e + cA D e = idem D (.inl v) → (a = e ∨ a = cA D e) → ∀ (m n : ℕ) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsCoord a (latO S T ΛS ΛT fun _ => True) κ → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → Set.BijOn (fun Φ => Tm (pull a κ Φ)) (GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v))) {f | IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) f} ∧ ∀ g h, SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∀ (γ : GL (Fin n) (Fv D.host.F v)) (δ : GL (Fin m) (Fv D.host.F v)), (∀ t, κ (actO S T g⁻¹ h⁻¹ t) = (δ⁻¹).val * κ t * γ.val) → ∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), om (g, h) (Tm (pull a κ Φ)) = ((splitFacO χS χT x y : Circle) : ℂ) • Tm (pull a κ (linOm v γ δ Φ)) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hC v e a he hev ha m n κ hκ Tm hTm

  obtain ⟨haS, haI⟩ : IsSplitIdem D a ∧ a + cA D a = idem D (.inl v) := by
    rcases ha with rfl | rfl
    · exact ⟨he, hev⟩
    · obtain ⟨h1, h2, w, ε, hε, h3⟩ := he
      refine ⟨⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm]; exact h2, w, ε, hε, by rw [cA_cA, add_comm]; exact h3⟩, ?_⟩
      rw [cA_cA, add_comm]; exact hev
  obtain ⟨-, hloc, hsurj⟩ : _ ∧ _ ∧ _ := by
    have := GlobalTheory.T.split_idempotent_base_function_identity D ψ θ S T sS sT ΛS ΛT f₀ hB v a haS haI
    exact ⟨this.1, this.2 Tm hTm⟩
  have hP := GlobalTheory.HalfCoordSB.isSBHalf_iff_pull D S T v m n a _ κ hκ
  obtain ⟨ν, hν⟩ := exists_haar (D := D) v
  obtain ⟨hv0, hvT, hIso⟩ := GlobalTheory.T.schrodingerModel_halfLatticeVolume_mul_inner_eq_inner D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC v a haS m n κ hκ Tm hTm ν hν
  have hvol : ((GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n)
      (κ '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf a t})).toReal : ℂ) ≠ 0 := by
    exact_mod_cast ENNReal.toReal_ne_zero.mpr ⟨hv0, hvT⟩
  have hU := GlobalTheory.LinUnit.linOm_unitary D v m n
  have hdef : ∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)),
      GlobalTheory.SplitWeil.ip ν Φ Φ = 0 → Φ = 0 := fun Φ hΦ => ((hU 1 1).2 Φ hΦ).2 ν hν |>.2
  refine ⟨⟨fun Φ hΦ => hloc _ (hP.1 Φ hΦ), ?_, ?_⟩, ?_⟩
  · intro Φ₁ h₁ Φ₂ h₂ heq
    have hd : Φ₁ - Φ₂ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)) :=
      Submodule.sub_mem _ h₁ h₂
    have h0 : Tm (pull a κ (Φ₁ - Φ₂)) = 0 := by
      rw [pull_sub, map_sub, sub_eq_zero]; exact heq
    have hi := hIso _ hd _ hd
    rw [h0] at hi
    refine sub_eq_zero.mp (hdef _ hd ?_)
    rw [← hi]; simp [ipO]
  · intro x hx
    obtain ⟨Ψ, hΨ, rfl⟩ := hsurj x hx
    obtain ⟨Φ, hΦ, rfl⟩ := hP.2 Ψ hΨ
    exact ⟨Φ, hΦ, rfl⟩
  · intro g h hg hh x y hx hy γ δ hκa Φ hΦ
    obtain ⟨r, hr, hom⟩ := GlobalTheory.PlaceTensor.om_placeModel_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ hW hB v e a he hev
      ha Tm hTm g h hg hh x y hx hy
    obtain ⟨r', hr', hlin⟩ := (hU γ δ).1
    have hr'0 : (r' : ℂ) ≠ 0 := by exact_mod_cast hr'.ne'

    have hsub : (fun t => pull a κ Φ (actO S T g⁻¹ h⁻¹ t)) = ((r' : ℂ)⁻¹) • pull a κ (linOm v γ δ Φ) := by
      funext t
      simp only [pull, Pi.smul_apply, smul_eq_mul, hlin]
      by_cases ht : IsHalf a t
      · rw [if_pos (GlobalTheory.SplitHecke.isHalf_actO g⁻¹ h⁻¹ ht), if_pos ht, hκa]
        field_simp
      · have ht' : ¬ IsHalf a (actO S T g⁻¹ h⁻¹ t) := by
          intro h'
          apply ht
          have h2 := GlobalTheory.SplitHecke.isHalf_actO g h h'
          have h3 := GlobalTheory.SplitHecke.actO_inv_actO g⁻¹ h⁻¹ t
          rw [inv_inv, inv_inv] at h3
          rwa [h3] at h2
        rw [if_neg ht', if_neg ht, mul_zero]
    have hmain : om (g, h) (Tm (pull a κ Φ)) =
        (((r : ℂ) * (r' : ℂ)⁻¹) * ((splitFacO χS χT x y : Circle) : ℂ)) • Tm (pull a κ (linOm v γ δ Φ)) := by
      rw [hom _ (hP.1 Φ hΦ), hsub, map_smul, smul_smul]
      congr 1; ring
    by_cases hΦ0 : GlobalTheory.SplitWeil.ip ν Φ Φ = 0
    ·
      have hz := hdef Φ hΦ hΦ0
      subst hz
      have hG0 : pull a κ (linOm v γ δ 0) = 0 := by
        funext t; simp [pull, hlin]
      rw [hmain, hG0]; simp
    ·
      have hF : IsThetaFunO ψ S T (Tm (pull a κ Φ)) := (hloc _ (hP.1 Φ hΦ)).1
      have h1 : ipO μ 𝓕 (om (g, h) (Tm (pull a κ Φ))) (om (g, h) (Tm (pull a κ Φ))) =
          ipO μ 𝓕 (Tm (pull a κ Φ)) (Tm (pull a κ Φ)) := by
        unfold ipO
        exact GlobalTheory.WeilInner.om_inner D ψ S T χS χT om hW μ 𝓕 hC (g, h) _ _ hF hF
      rw [hmain, ipO_smul_smul] at h1
      have hΦL := ((hU γ δ).2 Φ hΦ).1
      have hunit := (((hU γ δ).2 Φ hΦ).2 ν hν).1
      have e1 := hIso Φ hΦ Φ hΦ
      have e2 := hIso _ hΦL _ hΦL
      rw [hunit] at e2
      have hGF := mul_left_cancel₀ hvol (e2.trans e1.symm)
      have hI : ipO μ 𝓕 (Tm (pull a κ Φ)) (Tm (pull a κ Φ)) ≠ 0 := by
        intro h0; apply hΦ0; rw [← e1, h0, mul_zero]
      rw [hGF] at h1
      have hc := mul_right_cancel₀ hI (h1.trans (one_mul _).symm)
      have hχ : ((splitFacO χS χT x y : Circle) : ℂ) * (starRingEnd ℂ) ((splitFacO χS χT x y : Circle) : ℂ) = 1 := by
        rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
      rw [map_mul, map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_ofReal] at hc
      have hsq : ((r : ℂ) * (r' : ℂ)⁻¹) ^ 2 = 1 := by
        linear_combination hc - ((r : ℂ) * (r' : ℂ)⁻¹) ^ 2 * hχ
      have hsqR : (r * r'⁻¹) ^ 2 = (1 : ℝ) := by exact_mod_cast hsq
      have hq : r * r'⁻¹ = 1 := (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).mp hsqR
      have hqC : (r : ℂ) * (r' : ℂ)⁻¹ = 1 := by exact_mod_cast hq
      rw [hmain, hqC, one_mul]

end GlobalTheory.SplitCoordModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeparationLineOfBessel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mul_prod_of_separately {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (b : ∀ i, X i → ℂ) (β : (∀ i, X i) → ℂ)
    (h : ∀ i x, ∃ c : ℂ, ∀ y, β (Function.update x i y) = c * b i y) : ∃ l : ℂ, ∀ x, β x = (∏ i, b i (x i)) * l := by
  by_cases h0 : ∃ i, ∀ y, b i y = 0
  · obtain ⟨i, hi⟩ := h0
    refine ⟨0, fun x => ?_⟩
    obtain ⟨c, hc⟩ := h i x
    have := hc (x i)
    rw [Function.update_eq_self, hi] at this
    simp [this]
  push_neg at h0
  choose x₀ hx₀ using h0
  have key : ∀ s : Finset ι, ∀ x, (∀ i, i ∉ s → x i = x₀ i) →
      β x * ∏ i ∈ s, b i (x₀ i) = β x₀ * ∏ i ∈ s, b i (x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x hx; rw [show x = x₀ from funext fun i => hx i (by simp)]
    | insert j s hj ih =>
      intro x hx
      obtain ⟨c, hc⟩ := h j x
      have e1 := hc (x j)
      rw [Function.update_eq_self] at e1
      have e2 := ih (Function.update x j (x₀ j)) fun i hi => by
        by_cases e : i = j
        · subst e; simp
        · rw [Function.update_of_ne e]; exact hx i (by simp [e, hi])
      have e3 : ∏ i ∈ s, b i (Function.update x j (x₀ j) i) = ∏ i ∈ s, b i (x i) :=
        Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
      rw [hc, e3] at e2
      rw [Finset.prod_insert hj, Finset.prod_insert hj, e1]
      linear_combination b j (x j) * e2
  have hn : ∏ i, b i (x₀ i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hx₀ i
  refine ⟨β x₀ / ∏ i, b i (x₀ i), fun x => ?_⟩
  have := key Finset.univ x (by simp)
  field_simp
  linear_combination this

end GlobalTheory.SepRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothRepIntegratedOperatorNormalizedIndicatorFi
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

theorem smoothOp_normInd_of_fixed : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G), IsOpen (H : Set G) → IsCompact (H : Set G) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), GlobalTheory.PRep.IsSmooth ρ → ∀ x : W, (∀ h ∈ H, ρ h x = x) → smoothOp ρ μ (normInd μ (H : Set G)) x = x := by
  intro G _ _ _ _ _ _ μ _ H ho hK W _ _ ρ hρ x hx
  have hf : IsLocallyConstant ((H : Set G).indicator (1 : G → ℂ)) := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun g => ?_
    by_cases hg : g ∈ (H : Set G)
    · exact ⟨H, ho, hg, fun y hy => by simp [Set.indicator_of_mem hy, Set.indicator_of_mem hg]⟩
    · exact ⟨(H : Set G)ᶜ, (H.isClosed_of_isOpen ho).isOpen_compl, hg, fun y hy => by
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hg]⟩
  have hc : HasCompactSupport ((H : Set G).indicator (1 : G → ℂ)) :=
    HasCompactSupport.intro hK fun y hy => Set.indicator_of_notMem hy _
  have h0 : (μ.real H : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, Ne, measureReal_eq_zero_iff hK.measure_lt_top.ne]
    exact (ho.measure_pos μ ⟨1, one_mem H⟩).ne'
  have hf' : IsLocallyConstant (normInd μ (H : Set G)) := by
    unfold normInd; exact hf.comp ((μ.real H : ℂ)⁻¹ • ·)
  have hc' : HasCompactSupport (normInd μ (H : Set G)) := by
    unfold normInd; exact hc.comp_left (g := ((μ.real H : ℂ)⁻¹ • ·)) (smul_zero _)
  refine eq_of_forall_dual fun l => ?_
  have h1 : (fun g => normInd μ (H : Set G) g • l (ρ g x)) =
      (H : Set G).indicator fun _ => (μ.real H : ℂ)⁻¹ * l x := by
    ext g
    by_cases hg : g ∈ (H : Set G)
    · have : ρ g x = x := hx g hg
      simp [normInd, Set.indicator_of_mem hg, this]
    · simp [normInd, Set.indicator_of_notMem hg]
  rw [hρ.map_smoothOp hf' hc', h1, integral_indicator_const _ ho.measurableSet]
  rw [Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]

end GlobalTheory.TrIdem
end
end

