import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumSplitPlaceReadsThetaClassically
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1635
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0028

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingTermCoefEqResidueCardZpow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

noncomputable section
namespace GlobalTheory.FunObj.AaCoef
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

section Core
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

variable (k n c) in

def volDiag : (n ⊕ Fin c → kˣ) →* ℚ where
  toFun d := invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL d)).toMonoidHom)
  map_one' := by
    have h : diagGL (1 : n ⊕ Fin c → kˣ) = 1 := Units.ext (by simp [diagGL_val])
    rw [h, map_one]
    exact (congrArg invVol (Subgroup.map_id _)).trans invVol_KO
  map_mul' := GlobalTheory.T.inverseUnipotentVolume_conj_diagonalUnitsGL_mul

omit [IsNonarchimedeanLocalField k] [ValuativeRel k] [TopologicalSpace k] in
theorem prod_zpow_eq {ι : Type} (s : Finset ι) (q : ℚ) (hq : q ≠ 0) (g : ι → ℤ) :
    ∏ t ∈ s, q ^ g t = q ^ ∑ t ∈ s, g t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

theorem resCard_ne_zero : (resCard k : ℚ) ≠ 0 := by
  rw [resCard, Nat.cast_ne_zero]
  exact Nat.card_pos.ne'

theorem invVol_diag_zpow (ϖ : kˣ) (hϖ : IsUnif ϖ) (f : n ⊕ Fin c → ℤ) : ∃ z : ℤ,
    invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL fun r => ϖ ^ f r)).toMonoidHom) = (resCard k : ℚ) ^ z ∧
      |z| ≤ Fintype.card (n ⊕ Fin c) * ∑ r, |f r| := by
  choose z hz hzb using fun t : n ⊕ Fin c => GlobalTheory.T.exists_inverseUnipotentVolume_conj_diagonal_eq (k := k) (n := n) (c := c) ϖ hϖ t
  have hd : (fun r => ϖ ^ f r) = ∏ t, (Pi.mulSingle t ϖ) ^ f t := by
    funext r
    rw [Finset.prod_apply, Finset.prod_eq_single r]
    · simp
    · intro t _ ht; simp [Ne.symm ht]
    · simp
  have hq := resCard_ne_zero (k := k)
  let F := (volDiag k n c).toHomUnits
  have hF : ∀ d, (F d : ℚ) = invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL d)).toMonoidHom) := fun _ => rfl
  refine ⟨∑ t, z t * f t, ?_, ?_⟩
  · rw [← hF, hd, map_prod, Units.coe_prod]
    simp_rw [map_zpow, Units.val_zpow_eq_zpow_val, hF, hz, ← _root_.zpow_mul]
    exact prod_zpow_eq _ _ hq _
  · calc |∑ t, z t * f t| ≤ ∑ t, |z t * f t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t, (Fintype.card (n ⊕ Fin c) : ℤ) * |f t| := Finset.sum_le_sum fun t _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hzb t) (abs_nonneg _)
      _ = _ := (Finset.mul_sum _ _ _).symm

end Core

section Frame
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}
  (hs : 1 ≤ G.s)

theorem conjLevel_KO (g : G.VertexGroup) {j : ℕ} (hj : j < G.m) :
    conjLevel hs (fun _ => KO k _) g hj = (KO k _).map (MulAut.conj (toFrame hs hj (g (G.m, j)))).toMonoidHom := by
  have h : topRank G j + (G.m - 1 - j) = G.rank (G.m, j) := by have := topRank_add hs j; omega
  have hK : (KO k (Fin (G.rank (G.m, j)))).map (toFrame hs hj).toMonoidHom = KO k _ := by
    ext x
    rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap, mem_KO_iff, mem_KO_iff, ← map_inv]
    exact and_congr ((frame h).symm.forall_congr fun _ => (frame h).symm.forall_congr fun _ => Iff.rfl)
      ((frame h).symm.forall_congr fun _ => (frame h).symm.forall_congr fun _ => Iff.rfl)
  rw [conjLevel, Subgroup.map_map, ← hK, Subgroup.map_map]
  congr 1
  ext x : 1
  simp
end Frame

section AA
variable {D : D7}

def aaExp (w : Pl D.host.E) (j : ℕ) : Fin (topRank (bareGrid w) j) ⊕ Fin (D.R.m - 1 - j) → ℤ :=
  Sum.elim (fun _ => 0) fun p => FractionalIdeal.count D.host.E w D.host.AA * ((D.R.m - 1 - j - p.val : ℕ) : ℤ) -
    FractionalIdeal.count D.host.E w D.host.AAbar * (p.val + 1)

theorem toFrame_aaElt (w : Pl D.host.E) (hs : 1 ≤ (bareGrid w).s) {j : ℕ} (hj : j < (bareGrid w).m) :
    toFrame hs hj (aaElt w j) = diagGL fun r => unifAt w ^ aaExp w j r := by
  refine Units.ext ?_
  have h : topRank (bareGrid w) j + ((bareGrid w).m - 1 - j) = (bareGrid w).rank ((bareGrid w).m, j) := by
    have := topRank_add hs j; have hm : (bareGrid w).m = D.R.m := rfl; omega
  show (aaElt w j).val.submatrix (frame h) (frame h) = _
  rw [aaElt, diagGL_val, diagGL_val, submatrix_diagonal_equiv]
  congr 1
  funext x
  rcases x with a | p
  · show _ = ((unifAt w ^ aaExp w j (Sum.inl a) : (Kw w)ˣ) : Kw w)
    rw [show aaExp w j (Sum.inl a) = 0 from rfl]
    simp [frame, Nat.not_le.2 a.2]
  · have e : ∀ (x : ℤ) (N : ℕ), ((unifAt w) ^ x) ^ N = unifAt w ^ (x * N) := fun x N => by
      rw [← zpow_natCast, ← _root_.zpow_mul]
    show _ = ((unifAt w ^ aaExp w j (Sum.inr p) : (Kw w)ˣ) : Kw w)
    rw [show aaExp w j (Sum.inr p) = FractionalIdeal.count D.host.E w D.host.AA * ((D.R.m - 1 - j - p.val : ℕ) : ℤ) -
      FractionalIdeal.count D.host.E w D.host.AAbar * (p.val + 1) from rfl]
    simp only [Function.comp_apply, frame, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply, Fin.val_cast,
      Fin.val_natAdd, le_add_iff_nonneg_right, zero_le, if_true, Nat.add_sub_cancel_left, genAt]
    congr 1
    rw [e, e, ← _root_.zpow_neg, ← _root_.zpow_add]
    congr 1
end AA

section Main
variable {D : D7}

theorem rank_le_bigN (w : Pl D.host.E) {j : ℕ} (hj : j < D.R.m) :
    (bareGrid w).rank ((bareGrid w).m, j) ≤ bigN D := by
  have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hj)
  have h2 := Formalism.BasicNotions.Ranks.r_eq D.R
  simp only [Grid.rank, bareGrid, bigN, sLen, add_mul] at h1 ⊢
  nlinarith

theorem sum_abs_aaExp_le (w : Pl D.host.E) (j : ℕ) :
    ∑ r, |aaExp w j r| ≤ (D.R.m : ℤ) * ((D.R.m : ℤ) * (|FractionalIdeal.count D.host.E w D.host.AA| +
      |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by
  set A := FractionalIdeal.count D.host.E w D.host.AA
  set A' := FractionalIdeal.count D.host.E w D.host.AAbar
  have hA : 0 ≤ |A| + |A'| := by positivity
  rw [Fintype.sum_sum_type]
  have h0 : ∑ a : Fin (topRank (bareGrid w) j), |aaExp w j (Sum.inl a)| = 0 :=
    Finset.sum_eq_zero fun a _ => by simp [show aaExp w j (Sum.inl a) = 0 from rfl]
  rw [h0, zero_add]
  have hp : ∀ p : Fin (D.R.m - 1 - j), |aaExp w j (Sum.inr p)| ≤ (D.R.m : ℤ) * (|A| + |A'|) := fun p => by
    have hpv := p.2
    rw [show aaExp w j (Sum.inr p) = A * ((D.R.m - 1 - j - p.val : ℕ) : ℤ) - A' * (p.val + 1) from rfl]
    have e1 : (((D.R.m - 1 - j - p.val : ℕ) : ℤ)) ≤ D.R.m := by omega
    have e2 : ((p.val : ℤ) + 1) ≤ D.R.m := by omega
    have e3 : (0 : ℤ) ≤ ((D.R.m - 1 - j - p.val : ℕ) : ℤ) := by positivity
    calc |A * ((D.R.m - 1 - j - p.val : ℕ) : ℤ) - A' * (p.val + 1)|
        ≤ |A * ((D.R.m - 1 - j - p.val : ℕ) : ℤ)| + |A' * (p.val + 1)| := abs_sub _ _
      _ = |A| * ((D.R.m - 1 - j - p.val : ℕ) : ℤ) + |A'| * (p.val + 1) := by
          rw [abs_mul, abs_mul, abs_of_nonneg e3, abs_of_nonneg (by positivity : (0 : ℤ) ≤ p.val + 1)]
      _ ≤ |A| * D.R.m + |A'| * D.R.m := add_le_add (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
      _ = _ := by ring
  calc ∑ p : Fin (D.R.m - 1 - j), |aaExp w j (Sum.inr p)| ≤ ∑ _p : Fin (D.R.m - 1 - j), (D.R.m : ℤ) * (|A| + |A'|) :=
        Finset.sum_le_sum fun p _ => hp p
    _ = ((D.R.m - 1 - j : ℕ) : ℤ) * ((D.R.m : ℤ) * (|A| + |A'|)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by omega) (by positivity)

theorem factor (w : Pl D.host.E) (hs : 1 ≤ (bareGrid w).s) (g : (bareGrid w).VertexGroup) {j : ℕ} (hj : j < (bareGrid w).m)
    (hg : g ((bareGrid w).m, j) = aaElt w j) : ∃ z : ℤ,
    invVol (conjLevel hs (fun _ => KO _ _) g hj) = (resCard (Kw w) : ℚ) ^ z ∧
      |z| ≤ (bigN D : ℤ) * ((D.R.m : ℤ) * ((D.R.m : ℤ) * (|FractionalIdeal.count D.host.E w D.host.AA| +
        |FractionalIdeal.count D.host.E w D.host.AAbar|))) := by
  rw [conjLevel_KO, hg, toFrame_aaElt w hs hj]
  obtain ⟨z, hz, hzb⟩ := invVol_diag_zpow (unifAt w) (isUnif_unifAt w) (aaExp w j)
  refine ⟨z, hz, hzb.trans ?_⟩
  have hc : (Fintype.card (Fin (topRank (bareGrid w) j) ⊕ Fin (D.R.m - 1 - j)) : ℤ) ≤ bigN D := by
    have h := topRank_add hs j
    have hr := rank_le_bigN w hj
    have hm : (bareGrid w).m = D.R.m := rfl
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    exact_mod_cast (show topRank (bareGrid w) j + (D.R.m - 1 - j) ≤ bigN D by omega)
  exact mul_le_mul hc (sum_abs_aaExp_le w j) (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)

end Main

theorem aaTerm_coef_eq_zpow {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (w : Pl D.host.E) : ∃ n : ℤ, (aaTerm W w).coef = (resCard (Kw w) : ℚ) ^ n ∧
      |n| ≤ 2 * ((D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 * (|FractionalIdeal.count D.host.E w D.host.AA| +
        |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by
  set B := (bigN D : ℤ) * ((D.R.m : ℤ) * ((D.R.m : ℤ) * (|FractionalIdeal.count D.host.E w D.host.AA| +
        |FractionalIdeal.count D.host.E w D.host.AAbar|))) with hB
  have hz : ∀ i : Fin ((bareGrid w).m - 2), ∃ z : ℤ, invVol (conjLevel (G := bareGrid w) one_le_sLen (fun _ => KO _ _)
      ((Reps.through (G := bareGrid w) one_le_sLen (fun _ => KO _ _) (aaElt w)).elt
        fun i => DoubleCoset.mk _ _ (aaElt w (i + 1))) (j := i + 1) (by omega)) = (resCard (Kw w) : ℚ) ^ z ∧ |z| ≤ B :=
    fun i => factor w one_le_sLen _ _ (through_elt _ (by omega))
  choose z hz hzb using hz
  refine ⟨∑ i, z i, ?_, ?_⟩
  · show ∏ i : Fin ((bareGrid w).m - 2), _ = _
    rw [Finset.prod_congr rfl fun i _ => hz i]
    exact prod_zpow_eq _ _ resCard_ne_zero _
  · have hB0 : 0 ≤ B := by positivity
    calc |∑ i, z i| ≤ ∑ i, |z i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin ((bareGrid w).m - 2), B := Finset.sum_le_sum fun i _ => hzb i
      _ = (((bareGrid w).m - 2 : ℕ) : ℤ) * B := by simp
      _ ≤ (D.R.m : ℤ) * B := mul_le_mul_of_nonneg_right (by simp only [bareGrid]; omega) hB0
      _ ≤ _ := by
        have hN : (bigN D : ℤ) ≤ (bigN D : ℤ) ^ 2 := by
          rcases Nat.eq_zero_or_pos (bigN D) with h | h
          · simp [h]
          · nlinarith [show (1 : ℤ) ≤ bigN D by exact_mod_cast h]
        have hA : 0 ≤ |FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar| :=
          by positivity
        have hm : (0 : ℤ) ≤ D.R.m := by positivity
        rw [hB]
        have : (D.R.m : ℤ) * ((bigN D : ℤ) * ((D.R.m : ℤ) * ((D.R.m : ℤ) * (|FractionalIdeal.count D.host.E w D.host.AA| +
          |FractionalIdeal.count D.host.E w D.host.AAbar|)))) = (bigN D : ℤ) * ((D.R.m : ℤ) ^ 3 *
          (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by ring
        rw [this]
        have h3 : 0 ≤ (D.R.m : ℤ) ^ 3 * (|FractionalIdeal.count D.host.E w D.host.AA| +
          |FractionalIdeal.count D.host.E w D.host.AAbar|) := by positivity
        nlinarith

end GlobalTheory.FunObj.AaCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumCompactVacuumReadsDetCharacterStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_compact_vacuum_reads_det_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ k ∈ GinfC W, (∀ τ, s τ * compAt θ τ (Formalism.L2.Theta.mt W k) = compAt θ τ (Formalism.L2.Theta.mt W k) * s τ) → Reads θ V W hr X bas idx (om (1, k) f) (mu k • φ) (frMove θ W hr X k x) := by
  first | exact @GlobalTheory.AdTh.RealCompact.om_compact_reads | exact GlobalTheory.AdTh.RealCompact.om_compact_reads | (intros; apply GlobalTheory.AdTh.RealCompact.om_compact_reads <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumSplitPlaceReadsThetaClassicallyStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_split_place_reads_theta_classically : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (ΛV₁ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' Λ₁ : Lt D.host.E V.rank) (L : Lt D.host.E r), IsSelfDualC V ΛV → IsSelfDualC V ΛV₁ → IsSelfDualC W ΛW → (∀ v : Fin V.rank → D.host.E, v ∈ Λ' ↔ (fun j => star (v j)) ∈ ΛV) → (∀ v : Fin V.rank → D.host.E, v ∈ Λ₁ ↔ (fun j => star (v j)) ∈ ΛV₁) → (∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L₀ = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ ΛW, w = a • v} → L = latR hr L₀) → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ φ : TF V.rank g, Reads θ V W hr X bas idx f φ x → ∀ (e : AE D) (h : GA D V) (y : (AE D)ˣ), IsSplitIdem D e → SuppAt e V h → IsDetAt e V h y → (∀ u : WO V W, u ∈ (latO V W (ΛV₁ : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True), u = actO V W h 1 u₀) → Reads θ V W hr X bas idx (om (h, 1) f) ((((χW y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ₁ ⊓ Λ').toAddSubgroup.addSubgroupOf Λ₁.toAddSubgroup).index : ℝ) ^ r) : ℂ)) • projA X bas (H.w0 : D.host.E) (tens Λ₁ L) φ) x := by
  first | exact @GlobalTheory.AdTh.SplitClass.reads_om_split | exact GlobalTheory.AdTh.SplitClass.reads_om_split | (intros; apply GlobalTheory.AdTh.SplitClass.reads_om_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIntegralLocalToFinite
section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeilIntegral

theorem exists_factor_pi {O B : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B]
    {J : Type} [Finite J] {T : J → Type} [∀ i, CommRing (T i)] [∀ i, Algebra O (T i)]
    (e : B ≃ₐ[O] Π i, T i) (ψ : B →ₐ[O] O) :
    ∃ (i : J) (φ : T i →ₐ[O] O), ψ = φ.comp ((Pi.evalAlgHom O T i).comp e.toAlgHom) := by
  classical
  haveI := Fintype.ofFinite J
  set χ : (Π i, T i) →ₐ[O] O := ψ.comp e.symm.toAlgHom with hχ
  have hsum : ∑ i, χ (Pi.single i 1) = 1 := by
    rw [← map_sum, show (∑ i, Pi.single i 1 : Π i, T i) = 1 from Finset.univ_sum_single (1 : Π i, T i), map_one]
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
  have hidem : IsIdempotentElem (χ (Pi.single i 1)) := by
    have : IsIdempotentElem (Pi.single i (1 : T i) : Π j, T j) := by
      unfold IsIdempotentElem
      rw [← Pi.single_mul, _root_.one_mul]
    exact this.map χ
  have h1 : χ (Pi.single i 1) = 1 := (IsIdempotentElem.iff_eq_zero_or_one.1 hidem).resolve_left hi
  have hmul : ∀ y : Π j, T j, y * Pi.single i 1 = Pi.single i (y i) := by
    intro y
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  let φ : T i →ₐ[O] O :=
    { toFun := fun t => χ (Pi.single i t)
      map_one' := h1
      map_mul' := fun a b => by rw [Pi.single_mul, map_mul]
      map_zero' := by simp only [Pi.single_zero, map_zero]
      map_add' := fun a b => by simp only [Pi.single_add, map_add]
      commutes' := fun r => by
        change χ (Pi.single i (algebraMap O (T i) r)) = _
        rw [Algebra.algebraMap_eq_smul_one, Pi.single_smul, map_smul, h1, smul_eq_mul, _root_.mul_one]
        rfl }
  refine ⟨i, φ, AlgHom.ext fun b => ?_⟩
  have hb : ψ b = χ (e b) := by simp [hχ]
  rw [hb]
  change χ (e b) = χ (Pi.single i (e b i))
  rw [← hmul, map_mul, h1, _root_.mul_one]

end GlobalTheory.WeilIntegral

open GlobalTheory.TangentPow in

theorem GlobalTheory.WeilIntegral.weilIntegralFinite_of_local : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), WeilIntegralLocal P → WeilIntegralFinite P := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P hloc B _ _ _ _ N hN x y hx hy
  classical
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v P.integers
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI : HenselianLocalRing O := henselianLocalRing_of_valuationRing_of_isAlgClosed O C
  obtain ⟨J, hJ, T, _, _, e, hT⟩ := ((finite_algebras_over_henselian O).1 B).1
  let π : ∀ i, B →ₐ[O] T i := fun i => (Pi.evalAlgHom O T i).comp e.toAlgHom
  have hflat : ∀ i, Module.Flat O (T i) := fun i =>
    Module.Flat.of_retract (e.symm.toLinearMap ∘ₗ LinearMap.single O T i)
      (LinearMap.proj i ∘ₗ e.toLinearMap) (LinearMap.ext fun t => by simp)
  have key : ∀ i, ∃ u : T i, ∀ φ : T i →ₐ[O] O, algebraMap O C (φ u) =
      (weil P.A N (P.toA (ptMap φ ≫ ptMap (π i) ≫ x)) (P.toA (ptMap φ ≫ ptMap (π i) ≫ y)) : C) := by
    intro i
    haveI := (hT i).1
    haveI := (hT i).2
    haveI := hflat i
    exact hloc (T i) N hN (ptMap (π i) ≫ x) (ptMap (π i) ≫ y)
      (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
      (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
  choose u hu using key
  refine ⟨e.symm u, fun ψ => ?_⟩
  obtain ⟨i, φ, rfl⟩ := GlobalTheory.WeilIntegral.exists_factor_pi e ψ
  rw [← ptMap_comp_ptMap, Category.assoc, Category.assoc, ← hu i φ]
  exact congrArg (fun t => algebraMap O C (φ t)) (congrFun (e.apply_symm_apply u) i)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingIntegral
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral.Local

theorem inOpen_of_section {O : Type} [CommRing O] [IsLocalRing O] {B : Type} [CommRing B] [Algebra O B]
    [IsLocalRing B] (ψ : B →ₐ[O] O) {X : Over (Sp O)} {U : X.left.Opens} {w : specO O B ⟶ X}
    (h : InOpen U (ptMap ψ ≫ w)) : InOpen U w := by
  have hs : Function.Surjective ψ.toRingHom := fun a => ⟨algebraMap O B a, ψ.commutes a⟩
  haveI : IsLocalHom ψ.toRingHom := IsLocalHom.of_surjective _ hs
  unfold InOpen at h ⊢
  rw [Over.comp_left, Scheme.Hom.comp_preimage] at h
  refine (IsLocalRing.closedPoint_mem_iff (R := B) _).1 ?_
  have h1 : IsLocalRing.closedPoint O ∈ (ptMap ψ).left ⁻¹ᵁ (w.left ⁻¹ᵁ U) := by
    rw [h]; trivial
  have h2 : (ptMap ψ).left (IsLocalRing.closedPoint O) = IsLocalRing.closedPoint B :=
    IsLocalRing.comap_closedPoint ψ.toRingHom
  rw [← h2]
  exact h1

theorem section_comp {O : Type} [CommRing O] {B : Type} [CommRing B] [Algebra O B] (ψ : B →ₐ[O] O) :
    ptMap ψ ≫ ptMap (Algebra.ofId O B) = 𝟙 _ := by
  ext1
  simp only [ptMap, Over.comp_left, Over.homMk_left, Over.id_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : ψ.toRingHom.comp (Algebra.ofId O B).toRingHom = RingHom.id O := RingHom.ext fun a => ψ.commutes a
  rw [this]
  exact Spec.map_id _

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem inOpen_generic {U : P.G.left.Opens} {z : specO O O ⟶ P.G} {z' : Pts P.A.A} (hz : IsGeneric P z z')
    (h : InOpen U z) : InOpen (P.gen ⁻¹ᵁ U) z' := by
  unfold InOpen at h ⊢
  unfold IsGeneric at hz
  rw [← Scheme.Hom.comp_preimage]
  erw [hz]
  rw [Scheme.Hom.comp_preimage]
  erw [h]
  rfl

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem exists_lift {B : Type} [CommRing B] [Algebra O B] [IsLocalRing B] [Module.Finite O B] [Module.Flat O B]
    (ψ₀ : B →ₐ[O] O) {N : ℕ} {x : specO O B ⟶ P.Gt} (hx : x ^ N = 1) :
    ∃ x' : specO O B ⟶ P.G, x' ^ N = 1 ∧ ∀ ψ : B →ₐ[O] O, ptMap ψ ≫ x' = P.toG (ptMap ψ ≫ x) := by
  haveI := P.isLocalRing
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : B) := fun h => hp₀ (by simpa using h.map ψ₀)
  have hc : IsAdicComplete (Ideal.span {(p : B)}) B := by
    have := GlobalTheory.FlatComplete.isAdicComplete_of_finite_flat O (Ideal.span {(p : O)}) inferInstance B
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at this
  obtain ⟨x', hx', -⟩ := existsUnique_right (P := P) hp hc x
  have hpow : ∀ n : ℕ, Corr P (x ^ n) (x' ^ n) := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact Corr.one
    | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hx'
  refine ⟨x', (existsUnique_right (P := P) hp hc 1).unique (hx ▸ hpow N) Corr.one, fun ψ => ?_⟩
  exact (existsUnique_right (P := P) hp₀ inferInstance _).unique (hx'.comp ψ) fun m => P.red_toG _ m

variable [IsAlgClosed C] [CharZero C]

theorem exists_const_mul_unit (hΘ : HasCubeFn P.A) (hU : HasTrivialisingOpen P) (hT : TranslatesInto P)
    (hV : CubeValuesIntegral P) {B : Type} [CommRing B] [Algebra O B] [IsLocalRing B] [Module.Finite O B]
    [Module.Flat O B] (ψ₀ : B →ₐ[O] O) {N : ℕ} (hN : 1 ≤ N) {x y : specO O B ⟶ P.Gt} (hx : x ^ N = 1)
    (hy : y ^ N = 1) : ∃ (d : Cˣ) (u : Bˣ), ∀ ψ : B →ₐ[O] O,
      (weil P.A N (P.toA (ptMap ψ ≫ x)) (P.toA (ptMap ψ ≫ y)) : C) = d * algebraMap O C (ψ u) := by
  haveI := P.isLocalRing
  obtain ⟨x', hx', hxψ⟩ := exists_lift P ψ₀ hx
  obtain ⟨y', hy', hyψ⟩ := exists_lift P ψ₀ hy
  obtain ⟨U, hUs, hg⟩ := hU
  obtain ⟨Θ, hnat, hweil⟩ := hΘ (P.gen ⁻¹ᵁ U) hg
  obtain ⟨z₀, hz₀⟩ := hT U hUs (Fin N × Fin N) fun ij => ptMap ψ₀ ≫ (x' ^ (ij.1 : ℕ) * y' ^ (ij.2 : ℕ))
  obtain ⟨z, hz⟩ : ∃ z : specO O B ⟶ P.G, ptMap ψ₀ ≫ z = z₀ :=
    ⟨ptMap (Algebra.ofId O B) ≫ z₀, by rw [← Category.assoc, section_comp, Category.id_comp]⟩
  have hin : ∀ i j : ℕ, InOpen U (z * x' ^ i * y' ^ j) := fun i j => by
    refine inOpen_of_section ψ₀ ?_
    rw [_root_.mul_assoc, MonObj.comp_mul, hz, pow_eq_pow_mod i hx', pow_eq_pow_mod j hy']
    exact hz₀ (⟨_, Nat.mod_lt _ hN⟩, ⟨_, Nat.mod_lt _ hN⟩)
  have c₁ : ∀ i : ℕ, CubeIn U z (y' ^ i) y' x' := fun i a b c _ _ _ => by
    have := hin c (i * a + b)
    rwa [mul_right_comm, pow_add, pow_mul, ← _root_.mul_assoc] at this
  have c₂ : ∀ i : ℕ, CubeIn U z (x' ^ i) x' y' := fun i a b c _ _ _ => by
    have := hin (i * a + b) c
    rwa [pow_add, pow_mul, ← _root_.mul_assoc] at this
  choose d₁ u₁ h₁ using fun i => hV U Θ hnat B ⟨ψ₀⟩ _ _ _ _ (c₁ i)
  choose d₂ u₂ h₂ using fun i => hV U Θ hnat B ⟨ψ₀⟩ _ _ _ _ (c₂ i)
  refine ⟨(∏ i ∈ Finset.range N, d₁ i) / ∏ i ∈ Finset.range N, d₂ i,
    (∏ i ∈ Finset.range N, u₁ i) / ∏ i ∈ Finset.range N, u₂ i, fun ψ => ?_⟩
  let j : (specO O O ⟶ P.G) →* Pts P.A.A := P.exists_generic.choose
  let F : (specO O B ⟶ P.G) →* Pts P.A.A :=
    j.comp (MonoidHom.mk' (fun w => ptMap ψ ≫ w) fun a b => MonObj.comp_mul _ _ _)
  have hF : ∀ w, IsGeneric P (ptMap ψ ≫ w) (F w) := fun w => (P.exists_generic.choose_spec.2 _ _).2 rfl
  have ex : P.toA (ptMap ψ ≫ x) = F x' := congrArg j (hxψ ψ).symm
  have ey : P.toA (ptMap ψ ≫ y) = F y' := congrArg j (hyψ ψ).symm
  let m : Bˣ →* Cˣ := Units.map ((algebraMap O C).comp ψ.toRingHom).toMonoidHom
  have e₁ : ∀ i, Θ C (𝟙 _) (F z) (F y' ^ i) (F y') (F x') = d₁ i * m (u₁ i) := fun i =>
    Units.ext (h₁ i ψ _ _ _ _ (hF _) (by rw [← map_pow]; exact hF _) (hF _) (hF _))
  have e₂ : ∀ i, Θ C (𝟙 _) (F z) (F x' ^ i) (F x') (F y') = d₂ i * m (u₂ i) := fun i =>
    Units.ext (h₂ i ψ _ _ _ _ (hF _) (by rw [← map_pow]; exact hF _) (hF _) (hF _))
  have hw := hweil N hN (F x') (F y') (F z) (by rw [← map_pow, hx', map_one]) (by rw [← map_pow, hy', map_one])
    fun a b => by
      rw [← map_pow, ← map_pow, ← map_mul, ← map_mul]
      exact inOpen_generic P (hF _) ((hin a b).comp _)
  rw [Finset.prod_congr rfl fun i _ => e₁ i, Finset.prod_congr rfl fun i _ => e₂ i, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, ← map_prod, ← map_prod, mul_div_mul_comm, ← map_div] at hw
  rw [ex, ey, hw]
  rfl

theorem weilIntegralLocal (hΘ : HasCubeFn P.A) (hU : HasTrivialisingOpen P) (hT : TranslatesInto P)
    (hV : CubeValuesIntegral P) : WeilIntegralLocal P := by
  intro B _ _ _ _ _ N hN x y hx hy
  rcases isEmpty_or_nonempty (B →ₐ[O] O) with h0 | ⟨⟨ψ₀⟩⟩
  · exact ⟨0, fun ψ => h0.elim ψ⟩
  obtain ⟨d, u, h⟩ := exists_const_mul_unit P hΘ hU hT hV ψ₀ hN hx hy
  have tx : P.toA (ptMap ψ₀ ≫ x) ^ N = 1 := by
    rw [← map_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, map_one]
  have ty : P.toA (ptMap ψ₀ ≫ y) ^ N = 1 := by
    rw [← map_pow, ← MonObj.comp_pow, hy, MonObj.comp_one, map_one]
  have hw : weil P.A N (P.toA (ptMap ψ₀ ≫ x)) (P.toA (ptMap ψ₀ ≫ y)) ^ N = 1 := by
    rw [← weil_pow_left hN tx ty, tx]
    simpa using weil_pow_left hN tx ty 0
  have hv : v (weil P.A N (P.toA (ptMap ψ₀ ≫ x)) (P.toA (ptMap ψ₀ ≫ y)) : C) = 1 := by
    have := congrArg (fun w : Cˣ => v (w : C)) hw
    simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at this
    exact (pow_eq_one_iff_of_nonneg zero_le (by omega)).1 this
  rw [h, map_mul, P.integers.one_of_isUnit (u.isUnit.map ψ₀), _root_.mul_one] at hv
  obtain ⟨d₀, hd₀⟩ := P.integers.exists_of_le_one hv.le
  refine ⟨algebraMap O B d₀ * u, fun ψ => ?_⟩
  rw [h, map_mul, map_mul, ψ.commutes, ← hd₀]
  rfl

theorem weilIntegralLocal_of_cubes : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), HasCubeFn P.A → HasTrivialisingOpen P →
    TranslatesInto P → CubeValuesIntegral P → WeilIntegralLocal P :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P => weilIntegralLocal P

end GlobalTheory.WeilIntegral.Local
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmulStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_lattice_stabilizer_vacuum_eq_det_char_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (H : Geo.Tor.Host D.host.E) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), V.rank ≠ 0 → IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ k ∈ GfC W, (∀ u, u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ actO V W 1 k u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True)) → om (1, k) f = mu k • f := by
  first | exact @GlobalTheory.VacStab.om_vacuum_eq_smul | exact GlobalTheory.VacStab.om_vacuum_eq_smul | (intros; apply GlobalTheory.VacStab.om_vacuum_eq_smul <;> assumption)
end

