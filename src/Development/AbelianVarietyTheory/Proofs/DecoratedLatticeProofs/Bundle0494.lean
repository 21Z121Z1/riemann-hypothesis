import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0320
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0481
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0482
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineProjectionMemSplitCoreCompletion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LineProj

variable {D : D7}

theorem latV_le_of {S : HSp D} (L : Lat S) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) :
    GlobalTheory.FinPl.latV S L P ≤ GlobalTheory.FinPl.latV S L P' := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
  refine AddSubgroup.closure_mono ?_
  rintro y ⟨α, hα, hP, a, ha, x, hx, rfl⟩
  exact ⟨α, hα, fun v hv => hP v fun h' => hv (h v h'), a, ha, x, hx, rfl⟩

theorem row_iA {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    star (vecB o ζ) ᵥ* HSpace.gram S₀ ᵥ* o.iA = 0 := by
  show star (o.iB *ᵥ ζ) ᵥ* HSpace.gram S₀ ᵥ* o.iA = 0
  rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, o.orth,
    Matrix.vecMul_zero]

theorem row_vecB {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    (star (vecB o ζ) ᵥ* HSpace.gram S₀) ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  show (star (o.iB *ᵥ ζ) ᵥ* HSpace.gram S₀) ⬝ᵥ (o.iB *ᵥ ζ) = _
  rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, o.isoB]

theorem star_self {L : HSp D} (ζ : Fin L.rank → D.host.E) :
    star (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ) = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  conv_rhs => rw [Matrix.star_dotProduct, Matrix.star_mulVec, gram_conjTranspose, ← Matrix.dotProduct_mulVec]

theorem sum_incA_mulVec {s t : ℕ} (ρ : Fin s → D.host.E) (N : Matrix (Fin s) (Fin t) D.host.E) (u : Fin t → AE D) :
    ∑ j, incA D (ρ j) * (rat N *ᵥ u) j = ∑ a, incA D ((ρ ᵥ* N) a) * u a := by
  simp only [rat, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.map_apply, Finset.mul_sum, map_sum, map_mul,
    Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end GlobalTheory.LineProj

namespace GlobalTheory.LineProj

variable {D : D7}

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {q : SplitPt D k}
  {n : Type} [Fintype n] [DecidableEq n] {S₀ A L : HSp D} {o : OrthDec S₀ A L} {ζ : Fin L.rank → D.host.E}
  {α : Frame q A n} {α₀ : Frame q S₀ (n ⊕ Fin 1)} {M : Lat S₀} {Λ : Submodule 𝒪[k] (n → k)}

theorem e_vecB_mem (hsum : IsSumFrame o ζ α α₀) (hlat : α₀.IsLat M (lastKer Λ)) :
    (fun r => q.e * incA D (vecB o ζ r)) ∈ GlobalTheory.FinPl.latV S₀ M (· = q.v) := by
  let y0 : n ⊕ Fin 1 → k := Sum.elim 0 (fun _ => 1)
  have hb0 : α₀.b *ᵥ y0 = fun r => q.pr (incA D (vecB o ζ r)) := by
    rw [hsum, Matrix.fromCols_mulVec]
    funext r
    have h1 : y0 ∘ Sum.inl = 0 := Sum.elim_comp_inl _ _
    rw [Pi.add_apply, h1, Matrix.mulVec_zero, Pi.zero_apply, zero_add]
    simp only [Matrix.mulVec, dotProduct, Matrix.replicateCol_apply, Fin.sum_univ_one, Function.comp_apply, y0,
      Sum.elim_inr, mul_one]
    rfl
  have hy0 : y0 ∈ lastKer Λ := by
    refine GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨?_, ?_⟩
    · show (Sum.elim 0 (fun _ => 1) : n ⊕ Fin 1 → k) ∘ Sum.inl ∈ Λ
      rw [Sum.elim_comp_inl]; exact zero_mem _
    · exact one_mem _
  have h := (hlat y0).1 hy0
  rw [hb0] at h
  simpa only [q.sec_pr] using h

theorem pr_coeff_mem (hsum : IsSumFrame o ζ α α₀) (hlat : α₀.IsLat M (lastKer Λ)) {m : Fin S₀.rank → AE D} {c : AE D}
    (hmdec : ∀ r, m r = (o.jA *ᵥ (o.pA *ᵥ m)) r + c * incA D (vecB o ζ r))
    (hem : (fun r => q.e * m r) ∈ GlobalTheory.FinPl.latV S₀ M (· = q.v)) : q.pr c ∈ 𝒪[k] := by
  let pu : Fin A.rank → k := fun a => q.pr ((o.pA *ᵥ m) a)
  let y : n ⊕ Fin 1 → k := Sum.elim (α.b' *ᵥ pu) (fun _ => q.pr c)
  have hbx : α₀.b *ᵥ y = fun r => q.pr (m r) := by
    rw [hsum, Matrix.fromCols_mulVec]
    have h1 : (o.jA.map q.pr * α.b) *ᵥ (y ∘ Sum.inl) = o.jA.map q.pr *ᵥ pu := by
      show (o.jA.map q.pr * α.b) *ᵥ (α.b' *ᵥ pu) = _
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, α.bb', Matrix.mul_one]
    rw [h1]
    funext r
    rw [hmdec r, RingHom.map_add, RingHom.map_mul, RingHom.map_mulVec, Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.replicateCol_apply, Fin.sum_univ_one, Function.comp_apply, y,
      Sum.elim_inr]
    exact mul_comm _ _
  have hy : y ∈ lastKer Λ := by
    refine (hlat y).2 ?_
    rw [hbx]
    simpa only [q.sec_pr] using hem
  exact (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy).2

theorem pr_cA_mem {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : q.pr (cA D a) ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, RingHom.map_mul]
  exact FrameLat.mul_mem_intAE (GlobalTheory.UpMem.finPart_e_int q) ((FrameLat.cA_int_iff a).2 ha.2)

theorem e_mul_mem (hM : IsSelfDualC S₀ M) {P : Pl D → Prop} {m : Fin S₀.rank → AE D}
    (hm : m ∈ GlobalTheory.FinPl.latV S₀ M P) : (fun r => q.e * m r) ∈ GlobalTheory.FinPl.latV S₀ M (· = q.v) := by
  refine FrameLat.mem_of_pairing hM (fun r => Ideal.mul_mem_right _ _ (FrameLat.e_mem_idAt q)) fun s hs => ?_
  have h : FrameLat.pairing S₀ s (fun r => q.e * m r) = q.e * FrameLat.pairing S₀ s m := by
    simp only [FrameLat.pairing, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h, RingHom.map_mul]
  exact FrameLat.mul_mem_intAE (GlobalTheory.UpMem.finPart_e_int q) (FrameLat.pairing_int hM hs hm)

end Local

theorem pairing_eq {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (e c : AE D)
    {m : Fin S₀.rank → AE D} (hmdec : ∀ r, m r = (o.jA *ᵥ (o.pA *ᵥ m)) r + c * incA D (vecB o ζ r)) :
    (∑ a, ∑ b, cA D (e * incA D (vecB o ζ a)) * incA D (HSpace.gram S₀ a b) * m b) =
      cA D e * (c * incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) ⬝ᵥ vecB o ζ)) := by
  have h1 : (∑ a, ∑ b, cA D (e * incA D (vecB o ζ a)) * incA D (HSpace.gram S₀ a b) * m b) =
      cA D e * ∑ b, incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * m b := by
    simp only [RingHom.map_mul, FrameLat.cA_incA, Matrix.vecMul, dotProduct, map_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.star_apply]; ring
  rw [h1]
  congr 1
  have h2 : ∀ b, incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * m b =
      incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * (o.jA *ᵥ (o.pA *ᵥ m)) b +
        c * (incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * incA D (vecB o ζ b)) := fun b => by
    rw [hmdec b]; ring
  simp only [h2, Finset.sum_add_distrib]
  rw [OrthDec.jA, sum_incA_mulVec, row_iA]
  simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, zero_add, ← Finset.mul_sum, ← RingHom.map_mul,
    ← map_sum]
  rfl

end GlobalTheory.LineProj

namespace GlobalTheory.LineProj

set_option maxHeartbeats 1000000 in

theorem lineProj_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ m ∈ latV S₀ M P, o.jB *ᵥ (o.pB *ᵥ m) ∈ latV S₀ M P := by
  intro D k _ _ _ _ ι p I P hP n _ _ S₀ A L o ζ hζ α α₀ M Λ hM hfr m hm
  have hr : L.rank = 1 := hζ.1
  let i0 : Fin L.rank := ⟨0, by omega⟩
  have hsub : ∀ j : Fin L.rank, j = i0 := fun j => Fin.ext (by have := j.2; simp only [i0]; omega)
  have hz0 : ζ i0 ≠ 0 := by
    intro h0
    apply hζ.2
    have : ζ = 0 := funext fun j => by rw [hsub j, h0]; rfl
    rw [this]; simp
  have hmid : ∀ r, m r ∈ idAt D P := FrameLat.latV_supp hm
  set c : AE D := (o.pB *ᵥ m) i0 * incA D (ζ i0)⁻¹ with hc
  have hcid : c ∈ idAt D P := by
    refine Ideal.mul_mem_right _ _ ?_
    show (∑ j, o.pB i0 j * m j) ∈ idAt D P
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hmid j)
  have hpB : o.pB *ᵥ m = fun j => c * incA D (ζ j) := by
    funext j
    rw [hsub j, hc, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hz0, RingHom.map_one, mul_one]
  have hjB : o.jB *ᵥ (o.pB *ᵥ m) = fun r => c * incA D (vecB o ζ r) := by
    rw [hpB]; funext r
    simp only [Matrix.mulVec, dotProduct, OrthDec.jB, rat, Matrix.map_apply, vecB, map_sum, RingHom.map_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmdec : ∀ r, m r = (o.jA *ᵥ (o.pA *ᵥ m)) r + c * incA D (vecB o ζ r) := by
    intro r
    have h : m = o.jA *ᵥ (o.pA *ᵥ m) + o.jB *ᵥ (o.pB *ᵥ m) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.sum_eq_one, Matrix.one_mulVec]
    conv_lhs => rw [h]
    rw [Pi.add_apply, hjB]
  rw [hjB]
  refine (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n S₀ A L o ζ hζ α α₀ M Λ hM hfr c hcid).2 fun i => ?_
  obtain ⟨hsum, hlat⟩ := hfr i
  have hvP : P (p i).v := (hP.mem _).2 ⟨i, rfl⟩
  have hpre : (p i).pr (p i).e = 1 := by rw [← FrameLat.sec_one, (p i).pr_sec]
  refine ⟨pr_coeff_mem hsum hlat hmdec (e_mul_mem hM hm), ?_⟩
  have hzP := latV_le_of M (P := (· = (p i).v)) (P' := P) (fun w hw => by rw [hw]; exact hvP) (e_vecB_mem hsum hlat)
  have hH := (GlobalTheory.T.latticeCompletionAtPlaces_selfDual_of_selfDual D S₀ M hM P m hmid).1 hm _ hzP
  have h := pr_cA_mem (q := p i) hH
  rw [pairing_eq o ζ (p i).e c hmdec, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, cA_cA, hpre, one_mul,
    FrameLat.cA_incA, row_vecB, star_self, RingHom.map_mul] at h
  exact h

end GlobalTheory.LineProj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineVectorPairingMemInverseIdealCompletion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.LineDual

variable {D : D7}

theorem intAt_zero' (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩

theorem intAt_add' {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg' {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem latV_entry_mem_idAt {S : HSp D} {M : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S M P) (i : Fin S.rank) : y i ∈ idAt D P := by
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, x, -, rfl⟩ := hw
    exact LatMem.tmul_mem_idAt hα _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem idV_mem_idAt {𝔞 : FI D} {v : Pl D} {t : AE D} (ht : t ∈ idV 𝔞 v) : t ∈ idAt D (· = v) := by
  induction ht using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, rfl⟩ := hw
    exact LatMem.tmul_mem_idAt (fun w hw => hα w hw) _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem cA_mem_idAt {v : Pl D} {a : AE D} (h : a ∈ idAt D (· = v)) : cA D a ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

def pr (S : HSp D) (w y : Fin S.rank → AE D) : AE D := ∑ l, (∑ m, cA D (w m) * gA S m l) * y l

theorem pr_zero_left (S : HSp D) (y : Fin S.rank → AE D) : pr S 0 y = 0 := by simp [pr]
theorem pr_zero_right (S : HSp D) (w : Fin S.rank → AE D) : pr S w 0 = 0 := by simp [pr]
theorem pr_add_left (S : HSp D) (w w' y : Fin S.rank → AE D) : pr S (w + w') y = pr S w y + pr S w' y := by
  simp [pr, add_mul, Finset.sum_add_distrib]
theorem pr_add_right (S : HSp D) (w y y' : Fin S.rank → AE D) : pr S w (y + y') = pr S w y + pr S w y' := by
  simp [pr, mul_add, Finset.sum_add_distrib]
theorem pr_neg_left (S : HSp D) (w y : Fin S.rank → AE D) : pr S (-w) y = -pr S w y := by
  simp [pr]
theorem pr_neg_right (S : HSp D) (w y : Fin S.rank → AE D) : pr S w (-y) = -pr S w y := by
  simp [pr]

theorem pr_gen (S : HSp D) (α β : Af D.host.F) (x x' : Fin S.rank → D.host.E) :
    pr S (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
      pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (∑ m, ∑ l, star (x m) * S.gram m l * x' l) := by
  have hc : ∀ m, cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x m) = pairA D.host.F 0 α ⊗ₜ[D.host.F] star (x m) :=
    fun _ => rfl
  have hg : ∀ m l, gA S m l = (1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram m l := fun _ _ => rfl
  have hp : pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := Prod.ext (zero_mul _) rfl
  simp only [pr, one_mul]
  simp only [hc, hg, Finset.sum_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]
  rw [Finset.sum_comm]
  simp only [← TensorProduct.tmul_sum]

theorem pr_mem_intAt {S : HSp D} {M : Lat S} (hM : IsSelfDualC S M) {P : Pl D → Prop} {w y : Fin S.rank → AE D}
    (hw : w ∈ latV S M P) (hy : y ∈ latV S M P) : pr S w y ∈ intAt D P := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hw
    rw [Set.mem_singleton_iff] at ha
    subst ha
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨β, hβi, hβ, c, hc, x', hx', rfl⟩ := hz
      rw [Set.mem_singleton_iff] at hc
      subst hc
      rw [pr_gen]
      obtain ⟨b, hb⟩ := (hM.2 x').1 hx' x hx
      refine ⟨LatMem.tmul_mem_idAt (fun v hv => by rw [map_mul, hα v hv, zero_mul]) _, ?_⟩
      rw [← hb]
      exact AddSubgroup.subset_closure ⟨α * β, LatMem.intAf_mul' hαi hβi, b, rfl⟩
    | zero => rw [pr_zero_right]; exact intAt_zero' _
    | add z z' _ _ hz hz' => rw [pr_add_right]; exact intAt_add' hz hz'
    | neg z _ hz => rw [pr_neg_right]; exact intAt_neg' hz
  | zero => rw [pr_zero_left]; exact intAt_zero' _
  | add w w' _ _ hw hw' => rw [pr_add_left]; exact intAt_add' hw hw'
  | neg w _ hw => rw [pr_neg_left]; exact intAt_neg' hw

theorem line_pair_mem_idV : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L : HSp D) (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D), IsSelfDualC S M → LineId o ζ M 𝔠 v → 𝔠 ≠ 0 →
      ∀ y ∈ latV S M (· = v), cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idV 𝔠⁻¹ v := by
  intro D ψ hψ S A L o ζ M 𝔠 v hM hline h𝔠 y hy
  obtain ⟨h1, h2, -, h4, -⟩ := GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hX : (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idAt D (· = v) :=
    sum_mem fun l _ => Ideal.mul_mem_left _ _ (latV_entry_mem_idAt hy l)
  have hcX := cA_mem_idAt hX
  have hcint : ∀ s, s ∈ intAt D (· = v) → cA D s ∈ intAt D (· = v) := by
    intro s hs
    have e2 : s ∈ idV (D.host.AA ^ (0 : ℤ)) v := by rw [zpow_zero]; exact (h1 s).2 hs
    have e3 := (h4 0 s).1 e2
    rw [zpow_zero] at e3
    exact (h1 _).1 e3
  have key := (h2 𝔠 1 h𝔠 one_ne_zero _ hcX).1 (fun t ht => ?_)
  · rwa [one_mul] at key
  · have htI : t ∈ idAt D (· = v) := idV_mem_idAt ht
    have htz : t • ratV (vecB o ζ) ∈ latV S M (· = v) := (hline t htI).2 ht
    have hp := pr_mem_intAt hM htz hy
    have he : pr S (t • ratV (vecB o ζ)) y = cA D t * ∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l := by
      simp only [pr, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [he] at hp
    have h5 := hcint _ hp
    rw [map_mul, Formalism.L2.Theta.cA_cA, mul_comm] at h5
    exact (h1 _).2 h5

end GlobalTheory.LineDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterOfOneNonzeroValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerBlockParameter_of_one_nonzeroValue : ∀ D : D7, SoftQ D → QOfVal D := by
  first | exact @GlobalTheory.LowerBlockParam.qOfVal | exact GlobalTheory.LowerBlockParam.qOfVal | (intros; apply GlobalTheory.LowerBlockParam.qOfVal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLineHomLatticeCompletionIffScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Corev.mem_latO_line_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n'' : Type) [Fintype n''] [DecidableEq n''] (σ : ℕ) (B' : BesLev D σ) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M' : Lat B'.V₀) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ (∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ)) ∈ 𝒪[k])) := by
  intro D k _ _ _ _ ι p I P hP n'' _ _ σ B' γ γ₀ M' Λ' hM' hγ S LS hLS x hx
  have hu : (B'.o.resT S).symm (0, x) = B'.o.jB ⬝ x := by
    rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
  have hMx : MxAt P (B'.o.jB ⬝ x) := by
    intro i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)
  obtain ⟨hrk, hne⟩ := B'.line
  have hr : ∀ r r' : Fin B'.L.rank, r = r' := fun r r' => Fin.ext (by omega)
  let r₀ : Fin B'.L.rank := ⟨0, by omega⟩
  have hζ : B'.ζ r₀ ≠ 0 := by
    intro h0
    apply hne
    have : B'.ζ = 0 := funext fun r => by rw [hr r r₀, h0]; rfl
    rw [this, Matrix.mulVec_zero, dotProduct_zero]
  have hjB : ∀ d : AE D, B'.o.jB *ᵥ (d • ratV B'.ζ) = fun r => d * incA D (vecB B'.o B'.ζ r) := by
    intro d
    funext r
    simp only [Matrix.mulVec, dotProduct, OrthDec.jB, rat, Matrix.map_apply, ratV, Pi.smul_apply, smul_eq_mul, vecB,
      map_sum, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have key : ∀ y, (B'.o.jB ⬝ x) *ᵥ y ∈ latV B'.V₀ M' P ↔ ∃ d : AE D, d ∈ idAt D P ∧
      (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ (∀ i, (p i).pr d ∈ 𝒪[k] ∧
        (p i).pr (cA D d) * (p i).pr (incA D (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ)) ∈ 𝒪[k]) := by
    intro y
    rw [← Matrix.mulVec_mulVec]
    constructor
    · intro h
      have hz : ((x : Matrix _ _ (AE D)) *ᵥ y) r₀ ∈ idAt D P := by
        simp only [Matrix.mulVec, dotProduct]
        exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hx r₀ j)
      set d : AE D := ((x : Matrix _ _ (AE D)) *ᵥ y) r₀ * incA D (B'.ζ r₀)⁻¹ with hd
      have hdI : d ∈ idAt D P := Ideal.mul_mem_right _ _ hz
      have hzd : (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ := by
        funext r
        rw [hr r r₀, Pi.smul_apply, smul_eq_mul, ratV, hd, mul_assoc, ← map_mul, inv_mul_cancel₀ hζ, map_one, mul_one]
      rw [hzd, hjB] at h
      exact ⟨d, hdI, hzd, (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n'' B'.V₀ B'.A B'.L B'.o B'.ζ B'.line γ γ₀ M' Λ' hM' hγ d hdI).1 h⟩
    · rintro ⟨d, hdI, hzd, hc⟩
      rw [hzd, hjB]
      exact (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n'' B'.V₀ B'.A B'.L B'.o B'.ζ B'.line γ γ₀ M' Λ' hM' hγ d hdI).2 hc
  rw [hu, GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S B'.V₀ LS M' hLS hM' P, GlobalTheory.T.latticeCompletionAAScaled_eq_at_unitSplitPlaces D k ι p I P hP B'.V₀ M']
  constructor
  · rintro ⟨-, h⟩ y hy
    exact (key y).1 (h y hy)
  · intro h
    exact ⟨hMx, fun y hy => (key y).2 (h y hy)⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittTargetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelFormulas_wittTarget : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedTarget D := by
  first | exact @GlobalTheory.MixTargetProof.mixedTarget | exact GlobalTheory.MixTargetProof.mixedTarget | (intros; apply GlobalTheory.MixTargetProof.mixedTarget <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → (∀ (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) b (u : UX D ρ) c, term ψ d W vS (om (d.nC c * (d.nB b * d.levi u.1), 1) Ψ) x = ψ (d.qS W c (rat x)) * d.mixS W ψ vS.μ vS.𝓕 Ψ (rat x ⬝ u.1.1) (rat x ⬝ b)) ∧ (∀ γ ∈ GQ V, γ ∈ flagN d → ∀ x x' : Matrix (Fin W.rank) (Fin ρ) D.host.E, (rat x' : Mx D W.rank ρ) = rat x ⬝ blockX d γ → term ψ d W vS (om (γ, 1) Ψ) x = term ψ d W vS Ψ x') ∧ (∀ δ ∈ GQ W, ∀ x x' : Matrix (Fin W.rank) (Fin ρ) D.host.E, mt W δ ⬝ (rat x' : Mx D W.rank ρ) = rat x → term ψ d W vS (om (1, δ) Ψ) x = term ψ d W vS Ψ x') ∧ (∀ x, Continuous fun p : GA D V × GA D W => term ψ d W vS (om p Ψ) x) ∧ HasSum (term ψ d W vS Ψ) (Ψ 0) := by
  first | exact @GlobalTheory.Unf.TermLaw.term_laws | exact GlobalTheory.Unf.TermLaw.term_laws | (intros; apply GlobalTheory.Unf.TermLaw.term_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthogonalSumCoresHomotheticOffLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalSumCores_homothetic_off_level : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M M' : Lat S) (LA : Lat A) (LL : Lat L) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D) (a₀ : GA D A), IsLineVec L ζ → IsSelfDualC L LL → OrthAt o M LA LL v → TraceAt o a₀ LA M' v → SplitsAt o M' v → μ ≠ 0 → LineAt (vecB o ζ) μ M' v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → ∃ (a : GA D A) (c : AE D), CenAt A v a ∧ NormOneAt v c ∧ SMoves S c (o.emb (a₀ * a, 1)) M M' v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.coreOff_homothetic | exact GlobalTheory.Core.Mi.LatMatch.coreOff_homothetic | (intros; apply GlobalTheory.Core.Mi.LatMatch.coreOff_homothetic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealQuotientVolumeGrowthOfScalarHypothesesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realQuotientVolumeGrowth_of_scalarHypotheses : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → (∀ h : RangeX R, RChain R h) → RangeX R → RVol R := by
  first | exact @GlobalTheory.ChainTw.VolScale.rVol_of_given | exact GlobalTheory.ChainTw.VolScale.rVol_of_given | (intros; apply GlobalTheory.ChainTw.VolScale.rVol_of_given <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawWeilBiAction_commutes : ∀ D : D7, BiAct D := by
  first | exact @GlobalTheory.SeeSaw.biAct_all | exact GlobalTheory.SeeSaw.biAct_all | (intros; apply GlobalTheory.SeeSaw.biAct_all <;> assumption)
end

