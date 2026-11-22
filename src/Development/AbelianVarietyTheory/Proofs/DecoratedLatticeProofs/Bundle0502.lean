import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlaceOfSupportedStabilizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JointStarProductNonvanishing
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0493
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualIsotropicLineMemCompletionIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DualLine

variable {D : D7}

theorem idV_le_idAt {𝔞 : FI D} {v : Pl D} {a : AE D} (ha : a ∈ idV 𝔞 v) : a ∈ idAt D (· = v) := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, -, hα, b, -, rfl⟩ := hx
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt (fun w hw => hα w hw) b
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem cA_mem_idAt {v : Pl D} {a : AE D} (h : a ∈ idAt D (· = v)) : cA D a ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

theorem cA_mem_idV_one {v : Pl D} {c : AE D} (hc : c ∈ idV (1 : FI D) v) : cA D c ∈ idV (1 : FI D) v := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hαi, hα, a, ha, rfl⟩ := hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨o', ho'⟩ := GlobalTheory.FinPl.LatMem.star_int o
    refine AddSubgroup.subset_closure ⟨α, hαi, hα, (o' : D.host.E), (FractionalIdeal.mem_one_iff _).2 ⟨o', rfl⟩, ?_⟩
    show pairA D.host.F 0 α ⊗ₜ[D.host.F] star ((o : D.host.E)) = _
    rw [ho']
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem mul_incA_mem {S : HSp D} {L : Lat S} {v : Pl D} {c : AE D} (hc : c ∈ idV (1 : FI D) v)
    {s : Fin S.rank → D.host.E} (hs : s ∈ L) : (fun a => c * incA D (s a)) ∈ latV S L (· = v) := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hαi, hα, a, ha, rfl⟩ := hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    refine AddSubgroup.subset_closure ⟨α, hαi, fun w hw => hα w hw, 1, rfl, o • s, L.smul_mem o hs, ?_⟩
    funext l
    show (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] s l) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Pi.smul_apply, Algebra.smul_def]
  | zero =>
    have : (fun a => (0 : AE D) * incA D (s a)) = 0 := funext fun a => zero_mul _
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    have : (fun a => (x + y) * incA D (s a)) = (fun a => x * incA D (s a)) + fun a => y * incA D (s a) :=
      funext fun a => add_mul _ _ _
    rw [this]; exact add_mem hx hy
  | neg x _ hx =>
    have : (fun a => (-x) * incA D (s a)) = -fun a => x * incA D (s a) := funext fun a => neg_mul _ _
    rw [this]; exact neg_mem hx

end GlobalTheory.DualLine

namespace GlobalTheory.DualLine

variable {D : D7}

def hA (S : HSp D) (w y : Fin S.rank → AE D) : AE D := ∑ a, ∑ b, cA D (y a) * gA S a b * w b

theorem hA_add_left (S : HSp D) (w w' y : Fin S.rank → AE D) : hA S (w + w') y = hA S w y + hA S w' y := by
  simp only [hA, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hA_neg_left (S : HSp D) (w y : Fin S.rank → AE D) : hA S (-w) y = -hA S w y := by
  simp only [hA, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hA_zero_left (S : HSp D) (y : Fin S.rank → AE D) : hA S 0 y = 0 := by
  simp only [hA, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem hA_add_right (S : HSp D) (w y y' : Fin S.rank → AE D) : hA S w (y + y') = hA S w y + hA S w y' := by
  simp only [hA, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hA_neg_right (S : HSp D) (w y : Fin S.rank → AE D) : hA S w (-y) = -hA S w y := by
  simp only [hA, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem hA_zero_right (S : HSp D) (w : Fin S.rank → AE D) : hA S w 0 = 0 := by
  simp only [hA, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]

theorem hA_mem {S : HSp D} {L : Lat S} (hL : IsSelfDualC S L) {v : Pl D} {w y : Fin S.rank → AE D}
    (hw : w ∈ latV S L (· = v)) (hy : y ∈ latV S L (· = v)) : hA S w y ∈ idV (1 : FI D) v := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy' =>
    obtain ⟨β, hβi, hβ, c, hc, x', hx', rfl⟩ := hy'
    rw [Set.mem_singleton_iff] at hc
    subst hc
    induction hw using AddSubgroup.closure_induction with
    | mem w hw' =>
      obtain ⟨α, hαi, hα, c, hc, x, hx, rfl⟩ := hw'
      rw [Set.mem_singleton_iff] at hc
      subst hc
      obtain ⟨b, hb⟩ := (hL.2 x).1 hx x' hx'
      have hp : pairA D.host.F 0 β * pairA D.host.F 0 α = pairA D.host.F 0 (β * α) := Prod.ext (zero_mul _) rfl
      have e : hA S (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
          pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] (b : D.host.E) := by
        rw [hb, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        show (pairA D.host.F 0 β ⊗ₜ[D.host.F] star (1 * x' a)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram a k) *
          (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x k)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp, one_mul, one_mul]
      rw [e]
      exact AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβi hαi,
        fun w hw => by rw [map_mul, hβ w hw, zero_mul], (b : D.host.E), (FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩, rfl⟩
    | zero => rw [hA_zero_left]; exact zero_mem _
    | add w w' _ _ h h' => rw [hA_add_left]; exact add_mem h h'
    | neg w _ h => rw [hA_neg_left]; exact neg_mem h
  | zero => rw [hA_zero_right]; exact zero_mem _
  | add y y' _ _ h h' => rw [hA_add_right]; exact add_mem h h'
  | neg y _ h => rw [hA_neg_right]; exact neg_mem h

end GlobalTheory.DualLine

namespace GlobalTheory.DualLine

variable {D : D7}

theorem cA_cA' (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c e => show c ⊗ₜ[D.host.F] star (star e) = _; rw [star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cA_gA (S : HSp D) (a b : Fin S.rank) : cA D (gA S a b) = incA D (S.gram b a) :=
  congrArg (incA D) (GlobalTheory.LatVac.gram_star S a b)

theorem mem_of_hA {S : HSp D} {L : Lat S} (hL : IsSelfDualC S L) {v : Pl D} {y : Fin S.rank → AE D}
    (hyAt : ∀ a, y a ∈ idAt D (· = v)) (h : ∀ w ∈ latV S L (· = v), hA S w y ∈ idV (1 : FI D) v) :
    y ∈ latV S L (· = v) := by
  obtain ⟨m, s, s', hs, hs', hdual⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hL
  set ι : AE D := pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) with hι
  set w : Fin m → Fin S.rank → AE D := fun i l =>
    pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 * s' i l) with hwdef
  have hw : ∀ i, w i ∈ latV S L (· = v) := fun i => AddSubgroup.subset_closure
    ⟨_, GlobalTheory.FinPl.LatMem.indicatorAdele_mem_integralAdeles' _ _, GlobalTheory.FinPl.LatMem.indicatorAdele_supported _ _, 1, rfl, s' i, hs' i, rfl⟩
  have hcw : ∀ i l, cA D (w i l) = ι * incA D (star (s' i l)) := fun i l => by
    show pairA D.host.F 0 _ ⊗ₜ[D.host.F] star (1 * s' i l) = (pairA D.host.F 0 _ ⊗ₜ[D.host.F] (1 : D.host.E)) *
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] star (s' i l))
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, one_mul]
  have hyeq : y = ∑ i, fun a => cA D (hA S (w i) y) * incA D (s i a) := by
    funext a
    rw [Finset.sum_apply]
    have e1 : y a = ∑ a', y a' * ι * incA D (∑ i, s i a * ∑ k, star (s' i k) * S.gram k a') := by
      simp only [hdual]
      rw [Finset.sum_eq_single a (fun b _ hb => by rw [if_neg (Ne.symm hb), map_zero, mul_zero])
        (fun h => absurd (Finset.mem_univ a) h), if_pos rfl, map_one, mul_one]
      exact (GlobalTheory.FinPl.LatMem.mul_indP (hyAt a)).symm
    rw [e1]
    simp only [hA, map_sum, map_mul, cA_cA', cA_gA, hcw, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hyeq]
  exact sum_mem fun i _ => mul_incA_mem (cA_mem_idV_one (h _ (hw i))) (hs i)

end GlobalTheory.DualLine

namespace GlobalTheory.DualLine

theorem dualLine_mem_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (L : Lat S) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (v : Pl D), IsSelfDualC S L → MonoId d L L₀ 𝔟 v → ∀ i : Fin ρ, 𝔟 i ≠ 0 →
      ∀ t ∈ idAt D (· = v), colMul d.jY i t ∈ latV S L (· = v) ↔ cA D t ∈ idV (𝔟 i)⁻¹ v := by
  intro D ψ hψ S S₀ ρ d L L₀ 𝔟 v hL hM i hb t ht
  have I2 := (GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v).2.1 (𝔟 i) 1 hb one_ne_zero (cA D t) (cA_mem_idAt ht)
  rw [one_mul] at I2
  have hH : ∀ w, hA S w (colMul d.jY i t) = cA D t * (d.pX *ᵥ w) i := by
    intro w
    rw [d.pX_eq]
    simp only [hA, colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, map_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    show cA D t * cA D (d.jY a i) * gA S a b * w b = cA D t * (cA D (d.jY a i) * gA S a b * w b)
    ring
  have hPX : ∀ a, (d.pX *ᵥ colMul d.jX i a) i = a := by
    intro a
    have h1 := congrFun (congrFun d.pX_jX i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    simp only [Matrix.mulVec, dotProduct, colMul]
    calc ∑ k, d.pX i k * (a * d.jX k i) = a * ∑ k, d.pX i k * d.jX k i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = a := by rw [h1, mul_one]
  constructor
  · intro hy
    refine I2.1 fun a ha => ?_
    have hx := (hM.2 i a (idV_le_idAt ha)).2 ha
    have h2 := hA_mem hL hx hy
    rwa [hH, hPX] at h2
  · intro hc
    have hall := I2.2 hc
    refine mem_of_hA hL (fun k => Ideal.mul_mem_right _ _ ht) fun w hw => ?_
    rw [hH]
    have hwAt := GlobalTheory.FinPlLoc.latV_idAt hw
    have heAt : (d.pX *ᵥ w) i ∈ idAt D (· = v) := by
      show ∑ b, d.pX i b * w b ∈ idAt D (· = v)
      exact
      Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ (d.pX i b) (hwAt b)
    exact hall _ ((hM.2 i _ heAt).1 (((hM.1 w).1 hw).1 i))

end GlobalTheory.DualLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.KOpen

variable {D : D7}

open Classical in

def indP (D : D7) (P : Pl D → Prop) : Af D.host.F :=
  ⟨fun v => if P v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : P v
    · simp only [if_pos h]; exact one_mem (v.adicCompletionIntegers D.host.F)
    · simp only [if_neg h]; exact zero_mem (v.adicCompletionIntegers D.host.F)⟩

open Classical in
theorem evalV_indP (P : Pl D → Prop) (w : Pl D) : evalV D.host.F w (indP D P) = if P w then 1 else 0 := rfl

theorem indicatorAdele_integral (P : Pl D → Prop) : indP D P ∈ intAf D.host.F := fun w => by
  rw [evalV_indP]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem one_sub_indP_int (P : Pl D → Prop) : 1 - indP D P ∈ intAf D.host.F := fun w => by
  rw [map_sub, map_one, evalV_indP]
  split_ifs
  · rw [sub_self]; exact zero_mem _
  · rw [sub_zero]; exact one_mem _

open Classical in
theorem compFin_e (P : Pl D → Prop) (w : Pl D) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) = if P w then 1 else 0 := by
  change evalV D.host.F w (indP D P) ⊗ₜ[D.host.F] (1 : D.host.E) = _
  rw [evalV_indP]
  split_ifs
  · rfl
  · exact TensorProduct.zero_tmul _ _

theorem e_mul_of_supp (P : Pl D → Prop) (X : Af D.host.F ⊗[D.host.F] D.host.E)
    (h : ∀ w, ¬ P w → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w X = 0) :
    (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * X = X := by
  refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_
  change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w _ = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w _
  rw [map_mul, compFin_e]
  by_cases hw : P w
  · rw [if_pos hw, one_mul]
  · rw [h w hw, mul_zero]

theorem e_mul_fin {P : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) :
    (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D a = finPart D a :=
  e_mul_of_supp P _ ((mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D P a).1 ha).2

set_option maxHeartbeats 800000 in

theorem exists_latticeCompletion_cut_to_places_finiteReal (S : HSp D) (L : Lat S) (P : Pl D → Prop) {z : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E))) :
    ∃ y ∈ latV S L P, (∀ i, infPart D (y i) = 0) ∧
      ∀ i, finPart D (y i) = (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * z i := by
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      refine ⟨fun i => pairA D.host.F 0 (indP D P * a) ⊗ₜ[D.host.F] (1 * x i),
        AddSubgroup.subset_closure ⟨_, GlobalTheory.KStabBridge.intAf_mul (indicatorAdele_integral P) ha, fun w hw => ?_, 1, rfl, x, hx, rfl⟩,
        fun i => GlobalTheory.KStabBridge.infPart_pair _ _, fun i => ?_⟩
      · rw [map_mul, evalV_indP, if_neg hw, zero_mul]
      · rw [GlobalTheory.KStabBridge.finPart_pair, one_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | zero =>
      refine ⟨0, zero_mem (latV S L P), fun i => (infPart D).map_zero, fun i => ?_⟩
      show finPart D 0 = (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * 0
      rw [mul_zero]; exact (finPart D).map_zero
    | add z z' _ _ h h' =>
      obtain ⟨y, hy, h1, h2⟩ := h
      obtain ⟨y', hy', h1', h2'⟩ := h'
      exact ⟨y + y', add_mem hy hy', fun i => by rw [Pi.add_apply, (infPart D).map_add, h1, h1', add_zero],
        fun i => by rw [Pi.add_apply, (finPart D).map_add, h2, h2', Pi.add_apply, mul_add]⟩
    | neg z _ h =>
      obtain ⟨y, hy, h1, h2⟩ := h
      refine ⟨-y, neg_mem hy, fun i => ?_, fun i => ?_⟩
      · show infPart D (-(y i)) = 0
        rw [(infPart D).map_neg, h1, neg_zero]
      · show finPart D (-(y i)) = (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * -(z i)
        rw [(finPart D).map_neg, h2, mul_neg]

theorem mem_idAt_of_fin (P : Pl D → Prop) {a : AE D} (h1 : infPart D a = 0) {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (h2 : finPart D a = (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * z) : a ∈ idAt D P := by
  refine (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D P _).2 ⟨h1, fun w hw => ?_⟩
  change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D a) = 0
  rw [h2, (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w).map_mul, compFin_e, if_neg hw, zero_mul]

theorem exists_lift_latV (S : HSp D) (L : Lat S) (P : Pl D → Prop) {z : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E))) :
    ∃ y ∈ latV S L P, (∀ i, y i ∈ idAt D P) ∧
      ∀ i, finPart D (y i) = (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * z i := by
  obtain ⟨y, hy, h1, h2⟩ := exists_latticeCompletion_cut_to_places_finiteReal S L P hz
  exact ⟨y, hy, fun i => mem_idAt_of_fin P (h1 i) (h2 i), h2⟩

theorem mem_latV_iff (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV S L P ↔ (finPart D ∘ y) ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E)) := by
  refine ⟨fun h => GlobalTheory.KStabBridge.fin_mem_latHat S L P h, fun h => ?_⟩
  obtain ⟨y', hy', h1, h2⟩ := exists_lift_latV S L P h
  have : y' = y := funext fun i => GlobalTheory.VacStabFixed.parts_ext
    (by rw [((mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D P _).1 (h1 i)).1, ((mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D P _).1 (hy i)).1])
    (by rw [h2]; exact e_mul_fin (hy i))
  rwa [← this]

theorem supp_mulVec (S : HSp D) (P : Pl D → Prop) (g : GA D S) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D P) : ∀ i, (Formalism.L2.Theta.mt S g *ᵥ y) i ∈ idAt D P := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem fin_mulVec (S : HSp D) (g : GA D S) (y : Fin S.rank → AE D) :
    finPart D ∘ (Formalism.L2.Theta.mt S g *ᵥ y) = (finMat D.sp.cm.sig S.gram g) *ᵥ (finPart D ∘ y) := by
  funext i
  exact RingHom.map_mulVec (finPart D) _ y i

theorem moves_of_levelOpen (S : HSp D) (L : Lat S) (hL : L.FG) (P : Pl D → Prop) {g : GA D S}
    (hg : g ∈ GlobalTheory.AdelicU.levelOpen D.sp.cm.sig S.gram L) : Moves S g L L P := by
  intro y hy
  rw [mem_latV_iff S L P y hy, mem_latV_iff S L P _ (supp_mulVec S P g hy), fin_mulVec]
  exact (GlobalTheory.AdelicU.mem_levelOpen_iff_latHat _ _ hL g).1 hg _

theorem keeps_of_core {R : Type} [CommRing R] {n : ℕ} (H : AddSubgroup (Fin n → R)) (e : R) (hee : e * e = e)
    (h1 : ∀ z ∈ H, e • z ∈ H) (h2 : ∀ z ∈ H, (1 - e) • z ∈ H) (M : Matrix (Fin n) (Fin n) R)
    (hN : ∀ i j, e * (M - 1) i j = (M - 1) i j)
    (hcore : ∀ z, e • z ∈ H ↔ M *ᵥ (e • z) ∈ H) (y : Fin n → R) : y ∈ H ↔ M *ᵥ y ∈ H := by
  have hsplit : ∀ z, z ∈ H ↔ e • z ∈ H ∧ (1 - e) • z ∈ H := fun z =>
    ⟨fun hz => ⟨h1 z hz, h2 z hz⟩, fun ⟨a, b⟩ => by
      have := add_mem a b
      rwa [← add_smul, add_sub_cancel, one_smul] at this⟩
  have hN' : (1 - e) • M = (1 - e) • (1 : Matrix (Fin n) (Fin n) R) := by
    ext i j
    have := hN i j
    rw [Matrix.sub_apply] at this
    simp only [Matrix.smul_apply, smul_eq_mul]
    linear_combination (-1 : R) * this
  have hoff : (1 - e) • (M *ᵥ y) = (1 - e) • y := by
    rw [← Matrix.smul_mulVec, hN', Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hsplit y, hsplit (M *ᵥ y), hoff, hcore, Matrix.mulVec_smul]

theorem fin_sub_one (S : HSp D) (g : GA D S) (i j : Fin S.rank) :
    finPart D ((Formalism.L2.Theta.mt S g - 1) i j) = (finMat D.sp.cm.sig S.gram g - 1) i j := by
  rw [Matrix.sub_apply, Matrix.sub_apply, (finPart D).map_sub]
  congr 1
  exact congrFun (congrFun (Matrix.map_one _ (map_zero (finPart D)) (map_one (finPart D))) i) j

theorem levelOpen_of_inK (S : HSp D) (L : Lat S) (hL : L.FG) (P : Pl D → Prop) {g : GA D S}
    (hg : InK S L P g) : g ∈ GlobalTheory.AdelicU.levelOpen D.sp.cm.sig S.gram L := by
  refine (GlobalTheory.AdelicU.mem_levelOpen_iff_latHat _ _ hL g).2 ?_
  have hI := (SetCut.mem_congGrp_iff S _ g).1 hg.1
  refine keeps_of_core (latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E)))
    (indP D P ⊗ₜ[D.host.F] (1 : D.host.E))
    (e_mul_of_supp P _ fun w hw => by rw [compFin_e, if_neg hw])
    (fun z hz => GlobalTheory.KStabBridge.latHat_smul _ (indicatorAdele_integral P) hz) (fun z hz => ?_) _ (fun i j => ?_) (fun z => ?_)
  · have := GlobalTheory.KStabBridge.latHat_smul _ (one_sub_indP_int P) hz
    rwa [TensorProduct.sub_tmul, ← Algebra.TensorProduct.one_def] at this
  · rw [← fin_sub_one]; exact e_mul_fin (hI i j)
  · choose lift hl1 hl2 using GlobalTheory.KStabBridge.exists_fin_lift (D := D)
    let y : Fin S.rank → AE D := fun i => lift ((indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) * z i)
    have hy : ∀ i, y i ∈ idAt D P := fun i => mem_idAt_of_fin P (hl1 _) (hl2 _)
    have hfy : finPart D ∘ y = (indP D P ⊗ₜ[D.host.F] (1 : D.host.E)) • z := funext fun i => hl2 _
    have h := hg.2 y hy
    rw [mem_latV_iff S L P y hy, mem_latV_iff S L P _ (supp_mulVec S P g hy), fin_mulVec, hfy] at h
    exact h

theorem compAt_eq (v : Pl D) (a : AE D) : compAt D v a = GlobalTheory.AdelicU.compFin D.host.F D.host.E v a := by
  induction a using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul x c => rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]

theorem map_eq_one_iff {R R' : Type} [CommRing R] [CommRing R'] {n : ℕ} (f : R →+* R') (M : Matrix (Fin n) (Fin n) R) :
    M.map f = 1 ↔ ∀ i j, f ((M - 1) i j) = 0 := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem mem_GfC_iff (S : HSp D) (g : GA D S) : g ∈ GfC S ↔ ∀ i j, infPart D ((Formalism.L2.Theta.mt S g - 1) i j) = 0 := by
  rw [← map_eq_one_iff]
  exact Units.ext_iff

theorem proj_eq_one_iff (S : HSp D) (v : Pl D) (g : GA D S) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram v g = 1 ↔ ∀ i j, compAt D v ((Formalism.L2.Theta.mt S g - 1) i j) = 0 := by
  simp only [compAt_eq]
  rw [← map_eq_one_iff]
  exact Subtype.ext_iff.trans Units.ext_iff

theorem mem_grpAt_iff (S : HSp D) (P : Pl D → Prop) (g : GA D S) :
    g ∈ grpAt S P ↔ g ∈ GfC S ∧ ∀ v, ¬ P v → GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram v g = 1 := by
  rw [grpAt, SetCut.mem_congGrp_iff, mem_GfC_iff]
  simp only [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere, proj_eq_one_iff]
  exact ⟨fun h => ⟨fun i j => (h i j).1, fun v hv i j => (h i j).2 v hv⟩, fun h i j => ⟨h.1 i j, fun v hv => h.2 v hv i j⟩⟩

theorem isClosed_grpAt (S : HSp D) (P : Pl D → Prop) : IsClosed (grpAt S P : Set (GA D S)) := by
  have e : (grpAt S P : Set (GA D S)) = (GlobalTheory.AdelicU.finPts D.sp.cm.sig S.gram : Set (GA D S)) ∩
      ⋂ v : {v : Pl D // ¬ P v}, (GlobalTheory.AdelicU.awayPts D.sp.cm.sig S.gram {v.1} : Set (GA D S)) := by
    ext g
    rw [SetLike.mem_coe, mem_grpAt_iff, Set.mem_inter_iff, Set.mem_iInter]
    refine and_congr Iff.rfl ⟨fun h v => GlobalTheory.AdelicU.mem_awayPts.2 fun u hu => ?_,
      fun h v hv => GlobalTheory.AdelicU.mem_awayPts.1 (h ⟨v, hv⟩) v (Finset.mem_singleton_self v)⟩
    rw [Finset.mem_singleton.1 hu]; exact h v.1 v.2
  rw [e]
  exact (GlobalTheory.AdelicU.isClosed_finPts _ _).inter (isClosed_iInter fun v => GlobalTheory.AdelicU.isClosed_awayPts _ _ _)

theorem exists_compact_open : ∀ (D : D7) (V : HSp D) (L : Lat V), IsSelfDualC V L → ∀ P : Pl D → Prop, ∃ K : Subgroup (GA D V), (∀ g, g ∈ K ↔ InK V L P g) ∧ IsCompact (K : Set (GA D V)) ∧ IsOpen ((K.subgroupOf (grpAt V P) : Subgroup _) : Set (grpAt V P)) := by
  intro D V L hL P
  haveI : Submodule.IsLattice D.host.E L := hL.1
  have hfg : L.FG := Submodule.IsLattice.fg (A := D.host.E)
  let U : Subgroup (GA D V) := GlobalTheory.AdelicU.levelOpen D.sp.cm.sig V.gram L
  have hU : IsOpen (U : Set (GA D V)) := GlobalTheory.AdelicU.isOpen_levelOpen D.sp.cm.sig V.gram L
  refine ⟨grpAt V P ⊓ U, fun g => ⟨fun h => ⟨h.1, moves_of_levelOpen V L hfg P h.2⟩,
    fun h => ⟨h.1, levelOpen_of_inK V L hfg P h⟩⟩, ?_, ?_⟩
  · refine (GlobalTheory.AdelicU.isCompact_levelFin D.sp.cm.sig V.gram L).of_isClosed_subset
      ((isClosed_grpAt V P).inter (U.isClosed_of_isOpen hU)) fun k hk => ?_
    exact GlobalTheory.AdelicU.mem_levelFin.2 ⟨((mem_grpAt_iff V P k).1 hk.1).1, GlobalTheory.AdelicU.mem_levelOpen.1 hk.2⟩
  · have e : (((grpAt V P ⊓ U).subgroupOf (grpAt V P) : Subgroup _) : Set (grpAt V P)) =
        Subtype.val ⁻¹' (U : Set (GA D V)) := by
      ext x
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [e]
    exact hU.preimage continuous_subtype_val

end GlobalTheory.FinPl.KOpen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JointStarProductNonvanishingStatement
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joint_star_product_nonvanishing : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → (∀ t F, (cxW W).Θ t ((cxW W).jR t (W.Q.F.eV (cxW W).zs t F)) ∈ (cxW W).EEl true) → Joint W → PuNZ D → (cxW W).MIstar2 (W.Q.F.eV (cxW W).zs) W.Q.sEE := by
  first | exact @GlobalTheory.MiTop.miStar2_at_realisation | exact GlobalTheory.MiTop.miStar2_at_realisation | (intros; apply GlobalTheory.MiTop.miStar2_at_realisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelStepVectorEqHeisenbergCombinationVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelStepVector_eq_heisenbergCombination_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (LS : LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f → ∃ d : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ LS.Pg ∪ Q, p = PP.under (𝓞 D.host.F)) d ∧ f = comb ψ S T d f₀ := by
  first | exact @GlobalTheory.StepComb.exists_comb_of_isStepVecOf | exact GlobalTheory.StepComb.exists_comb_of_isStepVecOf | (intros; apply GlobalTheory.StepComb.exists_comb_of_isStepVecOf <;> assumption)
end

