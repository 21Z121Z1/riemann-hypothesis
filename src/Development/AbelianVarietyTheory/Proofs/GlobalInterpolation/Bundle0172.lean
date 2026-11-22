import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JetsAllOfColIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0505
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EFirstGeOfULastNonpos
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0144
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0078
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0171
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0146

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHypJetsAll
section
noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

namespace GlobalTheory.KerT

namespace JetsInhab

open GlobalTheory.Mem GlobalTheory.Mem.Col2

theorem exists_pre_sized : ∃ P : Pre, StagesInhab.HasLetters P ∧ Nonempty (PreX P) ∧
    (letI := P.host.cmStar; DiagSpaces P.sp) ∧ ∀ u, (P.duStar u : ℝ) = duStarOf P.host (P.hcW u) := by
  obtain ⟨P, ⟨X⟩, -, -, ⟨hD, -⟩, Del, letter, h1, -, h3, h4⟩ := exists_pre_two_words
  obtain ⟨du, hdu, e⟩ := DuInt.duStarOf_nat _ P.host (P.hcW P.u₀) P.g_cond X.g_big
  have hT : (0 : ℝ) < P.T P.u₀ := Nat.cast_pos.2 (P.T_prime _).pos
  have hd : (0 : ℝ) < du := Nat.cast_pos.2 hdu
  have hG : 0 < P.GamP := zero_lt_one.trans P.one_lt_gammaP
  have hf : (0 : ℝ) < P.R.f := by
    have : 0 < P.R.f := by unfold Ranks.f Ranks.n; positivity
    exact_mod_cast this
  have hk : (0 : ℝ) < P.R.k := by
    have := P.R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < P.R.k)
  have hfk : (0 : ℝ) < (P.R.f : ℝ) * P.R.k := mul_pos hf hk
  have key : ((P.T P.u₀ : ℝ) ^ ((P.R.f : ℝ) * P.R.k) * P.GamP ^ (2 : ℝ) * du / du) ^ ((1 : ℝ) / (P.R.f * P.R.k)) *
      P.GamP ^ (-(2 : ℝ) / (P.R.f * P.R.k)) = P.T P.u₀ := by
    rw [mul_div_cancel_right₀ _ hd.ne', Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hT.le,
      ← Real.rpow_mul hG.le, mul_assoc, ← Real.rpow_add hG, mul_one_div_cancel hfk.ne', Real.rpow_one,
      show (2 : ℝ) * (1 / (P.R.f * P.R.k)) + -2 / (P.R.f * P.R.k) = 0 by ring, Real.rpow_zero, mul_one]
  let Q : Pre := { P with
    Word := Unit
    wordFin := inferInstance
    u₀ := ()
    hcW := fun _ => P.hcW P.u₀
    hcW_base := P.hcW_base
    hcW_v := fun _ => P.hcW_v _
    hcW_b := fun _ => P.hcW_b _
    hcW_e := fun _ => P.hcW_e _
    hcW_first := fun _ => P.hcW_first _
    hcW_last := fun _ => P.hcW_last _
    T := fun _ => P.T P.u₀
    T_level := fun _ => P.T_level _
    T_norm := fun _ => P.T_norm _
    sp_T := P.sp_T
    cOf := fun _ => P.cOf P.u₀
    cOf_ne := fun _ => P.cOf_ne _
    cOf_eq := fun _ => P.cOf_eq _
    T_ne_pde := fun _ => P.T_ne_pde _
    duStar := fun _ => du
    duStar_pos := fun _ => hdu
    Dstar := (P.T P.u₀ : ℝ) ^ ((P.R.f : ℝ) * P.R.k) * P.GamP ^ (2 : ℝ) * du
    Dstar_pos := by positivity
    T_win := fun _ => by
      rw [key]
      exact ⟨le_rfl, le_mul_of_one_le_left hT.le (le_add_of_nonneg_right (by positivity))⟩ }
  refine ⟨Q, ⟨Del, fun _ => letter P.u₀, h1, fun _ _ _ => rfl, fun _ => h3 _, fun _ => h4 _⟩, ⟨{ X with
    piT := fun _ => X.piT P.u₀
    piT_K := fun _ => X.piT_K _
    piT_norm := fun _ => X.piT_norm _
    piT_cong := fun _ => X.piT_cong _
    hcW_inj := fun _ _ _ => rfl
    T_gt := fun _ => X.T_gt _
    spread_le := fun _ => X.spread_le _ }⟩, hD, fun _ => e⟩

theorem exists_colIn_jets : ∃ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : ColIn B X),
    StagesInhab.HasLetters B.toPre ∧ I.Ok ∧ I.JetsIn := by
  classical
  obtain ⟨P, hL, ⟨X₀⟩, hsp, hdu⟩ := exists_pre_sized
  obtain ⟨f⟩ : Nonempty (Top.Fr P) := P.nonempty_hframe X₀.e_even
  obtain ⟨X, hX⟩ := InEx.exists_oriented X₀ f.P
  obtain ⟨Z, hZ, hjet⟩ := exists_bound_jetsIn
  obtain ⟨M, hM, -, -, m1, m2, -⟩ := FrameVal.frame_values P.R P.host _ f fun j τ => (P.hc τ).e_int j
  obtain ⟨α, hα, gα⟩ := @DatHecke.exists_gen M hM
  choose r hr using fun q : ℕ => IsAlgClosed.exists_pow_nat_eq (q : ℂ) (n := 2) two_pos
  obtain ⟨Y, hY, gY⟩ := InEx.exists_holds (2 * P.R.m) ({1, f.del, f.del'} : Set (Formalism.L2.Host.HChar P.host.E))
  obtain ⟨B, rfl, -, -, h2⟩ := BaseExt.exists_base P ∅ ∅
    (insert α ((Y ∪ Finset.univ.image fun k => r (P.host.g k)) ∪ Z P f.chiPsi {1, f.del, f.del'})) (by simp) (by simp)
    (fun z hz => by
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hα
      rcases Finset.mem_union.1 hz with hz | h
      · rcases Finset.mem_union.1 hz with h | h
        · exact hY z h
        · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 h
          exact IsAlgebraic.of_pow two_pos (by rw [hr]; exact isAlgebraic_natCast _)
      · exact hZ _ _ _ z h)
  have i1 := gα B.LL B.embLL (h2 _ (Finset.mem_insert_self _ _))
  have hf : ({1, f.del, f.del'} : Set (Formalism.L2.Host.HChar B.host.E)).Finite := Set.toFinite _
  have ht : ∀ ξ ∈ ({1, f.del, f.del'} : Set (Formalism.L2.Host.HChar B.host.E)), Chr.IsTwist B.host (InEx.avoid B.toPre) ξ :=
    fun ξ hξ => InEx.isTwist_of_mem_set B f (Top.TwDat.untw B ∅) ξ (.inl hξ)
  obtain ⟨sel, hsel⟩ := Formalism.L2.Col.exists_sel B.fields
  obtain ⟨J, hJ⟩ := exists_ambIn_ok B.host
  obtain ⟨I, a1, a2, -, a4, -⟩ := InEx.exists_colIn B X f hX hsp hdu (InEx.avoid B.toPre)
    (fun u => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Exists.intro u rfl))))), B.T_ne_pde u⟩)
    (fun i => ⟨Or.inr (Or.inl (Exists.intro i rfl)), (B.host.pde_ne_g i).1.symm, (B.host.pde_ne_g i).2.symm⟩)
    (fun _ hp h => InEx.mem_avoid_of_dvd _ hp h)
    _ hf (.inl rfl) (.inr (.inl rfl)) (.inr (.inr rfl)) ht
    (fun ξ hξ => gY hf B.LL B.embLL
      (fun z hz => h2 z (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hz)))) ξ hξ (ht ξ hξ).1)
    (fun j => InEx.valuesIn_of (m1 j) _ i1) (InEx.valuesIn_of m2 _ i1) (fun i => by
      obtain ⟨s, hs⟩ := h2 _ (Finset.mem_insert_of_mem (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))))
      exact ⟨s, B.embLL.injective (by rw [map_pow, hs, hr, map_natCast])⟩) sel hsel J hJ
  obtain ⟨I', k1, k2, -⟩ := hjet B X I hL a1 fun z hz => by
    rw [a2, a4] at hz
    exact h2 z (Finset.mem_insert_of_mem (Finset.mem_union_right _ hz))
  exact ⟨B, X, I', hL, k1, k2⟩

end JetsInhab

end GlobalTheory.KerT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueColumnsRowSharpBounds
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section
namespace GlobalTheory.LvT.Built.TrueCols

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem trueColumns_chain_last_step_sharp_bound (h : I.Ok) (hJ : I.JetsIn) (hS : GlobalTheory.LvT.WtSign.BaseSigns B) (l : I.Laws) (l0 : I.Law0 l)
    (Z : TC.Later B (I.cols l)) (u : (I.rec7 l Z).what₂.Word) (a : I.ι) : Conclusion5Sharp (tw (I.tw l l0 Z) u a) := by
  obtain ⟨Bd, hch, hsp, hse, hk, hBd⟩ := GlobalTheory.T.fivePointLaws_trueChains B X I h hJ l l0 Z u a
  have hT : Module.finrank ℚ Bd.E * (I.rec7 l Z).R.N (I.rec7 l Z).R.m + 1 < Bd.J.T := by
    subst hBd
    show Module.finrank ℚ B.host.E * B.R.N B.R.m + 1 < B.T u
    have h1 := X.a_gt
    have h2 := X.T_gt u
    have hf : Module.finrank ℚ B.host.E = 2 * B.R.f := by
      rw [B.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
      ring
    rw [hf]
    have h3 : ((2 * B.R.f * B.R.N B.R.m + 1 : ℕ) : ℝ) < (B.T u : ℝ) := lt_trans h1 h2
    exact_mod_cast h3
  have hW : TwColumn.WtSigns Bd.ch :=
    (GlobalTheory.LvT.WtSign.wtSigns_assemble_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G u Bd.ch).2 hS
  have := (GlobalTheory.LvT.Built.Assemble.sharpBound_stability_latticeColumnChain (I.rec7 l Z) u Bd hsp hse hk hT hW).1
  rwa [hch] at this

theorem row_true : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → GlobalTheory.LvT.WtSign.BaseSigns B →
    ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (Dx : DivX (I.rec7 l Z)) (u : (I.rec7 l Z).what₂.Word),
      Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (I.rec7 l Z) u ∧ ∀ w : (I.rec7 l Z).what₂.places.Pl,
        (I.rec7 l Z).what₂.places.resChar w = ((I.rec7 l Z).mem u).A.T → ∀ μ, Formalism.MainNotions.LocalQuadraticParts.UsedT (I.rec7 l Z) μ →
        μ ≠ (I.rec7 l Z).what₂.mu0 → (I.rec7 l Z).what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam (I.rec7 l Z) u w,
        Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw (I.tw l l0 Z) u μ w x (-(((I.rec7 l Z).R.m : ℝ) * EatT (I.rec7 l Z) u w)) := by
  intro B X I h hJ hS l l0 Z Dx u
  refine ⟨?_, fun w hw μ _ _ _ x hx => ?_⟩
  · have h0 := trueColumns_chain_last_step_sharp_bound h hJ hS l l0 Z u I.mu0
    rw [← own_eq I l l0 Z u] at h0
    exact (levelChainSharpColumnValuation_ownChain_iff (I.rec7 l Z) u).1 h0
  · have hTw : TupleChainSharpColumnValuation (I.tw l l0 Z) u μ :=
      TwSharp.tupleChainSharpColumnValuation_of_twisted (I.rec7 l Z) u (I.tw l l0 Z) μ (GlobalTheory.T.twistedChain_initialLattice_compatible_trueColumns B X I h l l0 Z u μ)
        (trueColumns_chain_last_step_sharp_bound h hJ hS l l0 Z u μ)
    exact GlobalTheory.Proof.ColumnWeightTwisted.colGeTw_of_tupleChainSharpColumnValuation (I.rec7 l Z) (I.tw l l0 Z) u μ hTw w hw x hx

end GlobalTheory.LvT.Built.TrueCols
end
end

