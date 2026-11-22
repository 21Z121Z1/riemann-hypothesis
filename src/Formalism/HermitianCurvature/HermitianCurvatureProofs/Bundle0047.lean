import Formalism.HermitianCurvature.StatementJF
import Formalism.FormalDegreeBessel.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0036
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0044
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0042
import Formalism.HermitianCurvature.Bundle0004
import Formalism.HermitianCurvature.Bundle0003
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
import Formalism.HermitianCurvature.OperatorsCommuteTranslations
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0027

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellHermitian

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.TwoByOneBlock

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma bigCell_mulVec_jV (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u : Fin (k + 1) → ℂ) :
    bigCell k r c μ *ᵥ jV k r u = jV k r (μ *ᵥ u) := by
  rw [← emb_mulVec_jV (r := r) μ u]
  ext i
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · have hj1 : ¬ j.val < r := by omega
    have e : bigCell k r c μ i j = Formalism.FourierDecayAlt.B2.embWb k r μ i j := by
      simp only [bigCell, Formalism.FourierDecayAlt.B2.embWb, dif_neg hj1, dif_pos hj.2]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · rw [dif_pos hi, dif_pos ⟨hi, hj⟩]
      · rw [dif_neg hi, dif_neg (fun h => hi h.1)]
        rw [if_neg]
        rintro ⟨rfl, h2⟩
        exact h2 hj
    rw [e]
  · have h0 : jV k r u j = 0 := by simp only [jV, dif_neg hj]
    rw [h0, mul_zero, mul_zero]

lemma herm_bigCell (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z z' : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') :
    herm (Hpk k r) (bigCell k r c μ *ᵥ z') z = herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) := by
  conv_lhs => rw [← jV_wbPart hz', ← jV_wbPart hz]
  rw [bigCell_mulVec_jV, herm_jV]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem gqDom (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ QDom k r D.z D.z') :
    gq D q ∈ Om k r D.z D.z' := by
  obtain ⟨hc, hζ⟩ := hq
  have hsec := D.sec.2 q.2 hζ
  have hmin := big_cell_minors_holds k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem
  refine ⟨big_cell_mem_holds k r q.1 _ hc hsec.1, ?_, ?_⟩
  · intro l hl
    have h := hmin.1 ⟨l.val, by omega⟩
    have hl' : (⟨(⟨l.val, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Fin (r + 2)) = l := Fin.ext rfl
    show Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) l ≠ 0
    rw [← hl', h]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  · have hz := hmin.2.2 hc
    rw [herm_bigCell _ _ D.z_mem D.z'_mem, hsec.2] at hz
    have hr := hmin.1 (Fin.last r)
    set P := Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) ⟨r, by omega⟩ with hP
    have hP0 : P ≠ 0 := by
      have : P = ∏ a : Fin r with a.val < (Fin.last r).val, q.1 a := hr
      rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
    have hlast : Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1)) = q.2 * P := by
      unfold zeta at hz
      rw [← hP] at hz
      have h2 := div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1))) hP0
      rw [hz] at h2
      exact h2.symm
    show 0 < Gf k r D.z D.z' (gq D q)
    unfold Gf gq
    rw [hlast, ← hP, Complex.normSq_mul]
    have h1 : 0 < Complex.normSq P := Complex.normSq_pos.2 hP0
    nlinarith

theorem _root_.Formalism.FourierDecayAlt.P.big_cell_domain : GqDom := fun _ _ _ _ _ _ _ _ D _ hq => gqDom D hq

end Formalism.FourierDecayAlt.P.BigCellHermitian
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellVanishingDifferential
section
namespace Formalism.FourierDecayAlt.P

theorem big_cell_vanishing_differential (hJ : C6.JCommuteBig) : C6.BigCellVanishing :=
  big_cell_vanishing_of_commute' hJ

theorem vanishing_of_budget_and_density (hJ : C6.JCommuteBig) (hB : C6.BudgetClass) (hD : C6.LemmaDens) :
    C6.Vanishing :=
  vanishing_of_components_true (big_cell_vanishing_differential hJ) hB c6_budgetArith_proof big_cell_threshold hD

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockTwist
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

namespace TwistedTransfer

section Ring

end Ring

section Frame

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

structure WaveHyp (L : R.LevelData A r) (st : Fr.Start A) (f fi : A) (s : ℂ) : Prop where
  f_fi : f * fi = 1
  fi_f : fi * f = 1
  star_f : star f = fi
  fn : ∀ g ∈ Fr.zfns L, Commute f g
  x : ∀ Y, Commute f (st.x Y)
  l : ∀ Y ∈ st.inv, fi * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * f =
    L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y - algebraMap ℂ A s

theorem mem_zfns (L : R.LevelData A r) : L.ζ ∈ Fr.zfns L ∧ L.ζi ∈ Fr.zfns L ∧ L.ζb ∈ Fr.zfns L ∧
    L.ζbi ∈ Fr.zfns L ∧ L.GG ∈ Fr.zfns L ∧ L.GGi ∈ Fr.zfns L := by
  simp [Fr.zfns]

theorem lowering_constant_sub (L : R.LevelData A r) (Y Y' : ℂ) :
    L.l0 Y - L.l0 Y' = algebraMap ℂ A (Y' - Y) * (L.ζb * L.GGi) := by
  simp only [R.LevelData.l0, map_sub, map_add]
  noncomm_ring

theorem embed_lowering_constant (L : R.LevelData A r) (Y : ℂ) :
    (io (L.l0 Y) : SlopeTestRemainingChoices S A) = -io L.nab - ((Y + 1 / 2) • (1 : SlopeTestRemainingChoices S A)) * (io L.ζb * io L.GGi) := by
  simp only [R.LevelData.l0, io_sub', io_neg', io_mul', io_algebraMap]

theorem wti_wt (L : R.LevelData A r) : L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) = 1 := by
  have h1 : L.ζbi * L.ζ = L.ζ * L.ζbi := L.fns_comm _ (by simp) _ (by simp)
  calc L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) = L.GG * L.ζi * (L.ζbi * L.ζ) * L.ζb * L.GGi := by
        simp only [mul_assoc]
    _ = L.GG * (L.ζi * L.ζ) * (L.ζbi * L.ζb) * L.GGi := by rw [h1]; simp only [mul_assoc]
    _ = 1 := by rw [L.ζi_ζ, L.ζbi_ζb, mul_one, mul_one, L.GG_GGi]

theorem wt_wti (L : R.LevelData A r) : L.ζ * L.ζb * L.GGi * (L.GG * L.ζi * L.ζbi) = 1 := by
  have h2 : L.ζb * L.ζi = L.ζi * L.ζb := L.fns_comm _ (by simp) _ (by simp)
  calc L.ζ * L.ζb * L.GGi * (L.GG * L.ζi * L.ζbi) = L.ζ * L.ζb * (L.GGi * L.GG) * L.ζi * L.ζbi := by
        simp only [mul_assoc]
    _ = L.ζ * (L.ζb * L.ζi) * L.ζbi := by rw [L.GGi_GG, mul_one]; simp only [mul_assoc]
    _ = (L.ζ * L.ζi) * (L.ζb * L.ζbi) := by rw [h2]; simp only [mul_assoc]
    _ = 1 := by rw [L.ζ_ζi, L.ζb_ζbi, mul_one]

theorem di_d (L : R.LevelData A r) (fr : Fr.FrameData S A) (hc : fr.ci * fr.c = 1) : fr.di L * fr.d L = 1 := by
  have h1 : (Fr.wti L : SlopeTestRemainingChoices S A) * Fr.wt L = 1 := by
    rw [Fr.wti, Fr.wt, ← io_mul', wti_wt, io_one']
  have h2 : (Fr.wt L : SlopeTestRemainingChoices S A) * Fr.wti L = 1 := by
    rw [Fr.wti, Fr.wt, ← io_mul', wt_wti, io_one']
  have hc' : Commute (Fr.wti L : SlopeTestRemainingChoices S A) (Fr.wt L) := by
    show _ = _; rw [h1, h2]
  have hp : (Fr.wti L : SlopeTestRemainingChoices S A) ^ fr.N * Fr.wt L ^ fr.N = 1 := by
    rw [← hc'.mul_pow, h1, one_pow]
  unfold Fr.FrameData.di Fr.FrameData.d
  calc fr.ci * Fr.wti L ^ fr.N * (Fr.wt L ^ fr.N * fr.c) = fr.ci * (Fr.wti L ^ fr.N * Fr.wt L ^ fr.N) * fr.c := by
        simp only [mul_assoc]
    _ = 1 := by rw [hp, mul_one, hc]

variable {L : R.LevelData A r} {st : Fr.Start A} {f fi : A} {s : ℂ}

theorem WaveHyp.io_fn (hW : WaveHyp L st f fi s) {g : A} (hg : g ∈ Fr.zfns L) :
    Commute (io f : SlopeTestRemainingChoices S A) (io g) :=
  commute_io_io (hW.fn g hg)

theorem WaveHyp.kap (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.kapL L) := by
  obtain ⟨-, h1, h2, -, -, h5⟩ := mem_zfns L
  unfold Fr.kapL
  exact commute_io_io (((hW.fn _ h2).mul_right (hW.fn _ h1)).mul_right (hW.fn _ h5))

theorem WaveHyp.tz (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.tz L) := by
  obtain ⟨-, -, -, h3, -, -⟩ := mem_zfns L
  unfold Fr.tz
  exact commute_io_io ((hW.fn _ h3).smul_right _)

theorem WaveHyp.wt (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.wt L) := by
  obtain ⟨h0, -, h2, -, -, h5⟩ := mem_zfns L
  unfold Fr.wt
  exact commute_io_io (((hW.fn _ h0).mul_right (hW.fn _ h2)).mul_right (hW.fn _ h5))

theorem WaveHyp.wti (hW : WaveHyp L st f fi s) : Commute (io f : SlopeTestRemainingChoices S A) (Fr.wti L) := by
  obtain ⟨-, h1, -, h3, h4, -⟩ := mem_zfns L
  unfold Fr.wti
  exact commute_io_io (((hW.fn _ h4).mul_right (hW.fn _ h1)).mul_right (hW.fn _ h3))

theorem WaveHyp.lowering_constant_sub (hW : WaveHyp L st f fi s) (Y Y' : ℂ) : Commute f (L.l0 Y - L.l0 Y') := by
  obtain ⟨-, -, h2, -, -, h5⟩ := mem_zfns L
  rw [TwistedTransfer.lowering_constant_sub L Y Y']
  exact (Algebra.commute_algebraMap_right _ f).mul_right ((hW.fn _ h2).mul_right (hW.fn _ h5))

theorem frame_step (hW1 : f * fi = 1) (a : S) (t : ℂ) (D : M2 (SlopeTestRemainingChoices S A)) (Fw UU : SlopeTestRemainingChoices S A) (hD : FreeOf2 a D)
    (hFw : FreeOf a Fw) (hIH : Fw * (io f * UU) = io f * Fw)
    (hE : (D * lift0 (Uinv (A := A) t)).map (cj f fi) = D) :
    ins a D * Fw * (io f * (ins a (lift0 (Uinv (A := A) t)) * UU)) = io f * (ins a D * Fw) := by
  have hcent : ∀ z : SlopeTestRemainingChoices S A, ∀ i j, Commute z ((lift0 (Uinv (A := A) t) : M2 (SlopeTestRemainingChoices S A)) i j) := by
    intro z i j
    rw [lift_unipotent_inverse]
    fin_cases i <;> fin_cases j <;> simp [commute_smul_one]
  have hUf : Commute (io f) (ins a (lift0 (Uinv (A := A) t))) :=
    Formalism.FourierDecayAlt.P.Wd1.ins_comm a _ _ (Formalism.FourierDecayAlt.P.Fr4.free_io a f) (hcent _)
  have hUF : Commute Fw (ins a (lift0 (Uinv (A := A) t))) := Formalism.FourierDecayAlt.P.Wd1.ins_comm a _ _ hFw (hcent _)
  have hins : ins a D * ins a (lift0 (Uinv (A := A) t)) = ins a (D * lift0 (Uinv (A := A) t)) :=
    (Formalism.FourierDecayAlt.P.Wd1.ins_mul a D _ hD).symm
  have hcj : ins a (D * lift0 (Uinv (A := A) t)) * io f = io f * ins a D := by
    have h := cj_ins (f := f) (fi := fi) a (D * lift0 (Uinv (A := A) t))
    rw [hE] at h
    calc ins a (D * lift0 (Uinv (A := A) t)) * io f
        = (io f * io fi) * ins a (D * lift0 (Uinv (A := A) t)) * io f := by rw [io_f_fi hW1, one_mul]
      _ = io f * cj f fi (ins a (D * lift0 (Uinv (A := A) t))) := by simp only [cj, mul_assoc]
      _ = io f * ins a D := by rw [h]
  calc ins a D * Fw * (io f * (ins a (lift0 (Uinv (A := A) t)) * UU))
      = ins a D * (Fw * ((io f * ins a (lift0 (Uinv (A := A) t))) * UU)) := by simp only [mul_assoc]
    _ = ins a D * (Fw * ((ins a (lift0 (Uinv (A := A) t)) * io f) * UU)) := by rw [hUf.eq]
    _ = ins a D * ((Fw * ins a (lift0 (Uinv (A := A) t))) * (io f * UU)) := by simp only [mul_assoc]
    _ = ins a D * ((ins a (lift0 (Uinv (A := A) t)) * Fw) * (io f * UU)) := by rw [hUF.eq]
    _ = ins a D * ins a (lift0 (Uinv (A := A) t)) * (Fw * (io f * UU)) := by simp only [mul_assoc]
    _ = ins a (D * lift0 (Uinv (A := A) t)) * io f * Fw := by rw [hIH, hins]; simp only [mul_assoc]
    _ = io f * (ins a D * Fw) := by rw [hcj, mul_assoc]

theorem block_twist (hW1 : f * fi = 1) (hW2 : fi * f = 1) (t : ℂ) (p q g l : SlopeTestRemainingChoices S A) (hp : Commute (io f) p)
    (hq : Commute (io f) q) (hg : Commute (io f) g) (hl : Tw f fi t l) :
    ((!![p, 0; 0, q] * !![1, 0; g * l, g]) * lift0 (Uinv (A := A) t)).map (cj f fi) =
      !![p, 0; 0, q] * !![1, 0; g * l, g] := by
  rw [lift_unipotent_inverse]
  simp only [Matrix.mul_fin_two, mul_one, mul_zero, zero_mul, add_zero, zero_add]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · simp [cj_of_comm hW2 hp]
  · simp [cj_zero]
  · simp only [Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_one, Fin.zero_eta]
    unfold Tw at hl
    rw [cj_add, cj_mul hW1, cj_mul hW1, cj_mul hW1, cj_mul hW1, cj_of_comm hW2 hq, cj_of_comm hW2 hg, hl,
      cj_of_comm hW2 (commute_smul_one t _), mul_sub, mul_sub, mul_assoc q g, sub_add_cancel]
  · simp [cj_of_comm hW2 (hq.mul_right hg)]

end Frame

end TwistedTransfer

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliUnderIntegral
section
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.CapelliUnderIntegral

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem glev0 {k r : ℕ} (g : Mat k r) : g ∈ Q.Glev k r 0 ↔ g ∈ GV k r := by
  simp only [Q.Glev, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    exact ⟨h, fun a ha => by simp at ha⟩

theorem integrable_map_sum {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} (L : List ι) (φ : ι → α → E) (h : ∀ i ∈ L, Integrable (φ i) μ) :
    Integrable (fun x => (L.map (fun i => φ i x)).sum) μ := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

theorem integral_map_sum {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} (L : List ι) (φ : ι → α → E) (h : ∀ i ∈ L, Integrable (φ i) μ) :
    ∫ x, (L.map (fun i => φ i x)).sum ∂μ = (L.map (fun i => ∫ x, φ i x ∂μ)).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    have hi := h i (by simp)
    have hL : ∀ j ∈ L, Integrable (φ j) μ := fun j hj => h j (by simp [hj])
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add hi (integrable_map_sum L φ hL), ih hL]

end Formalism.FourierDecayAlt.P.CapelliUnderIntegral

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem CapelliUnderIntegral.cvUnderInt_of_jWords : Formalism.FourierDecayAlt.JF.JWords → Formalism.FourierDecayAlt.JF.RwRho → Formalism.FourierDecayAlt.JF.CVUnderInt := by
  intro hJW hRR k r Wp Wq _ _ _ _ _ _ D A m F Y hnm hThr hF g hg
  obtain ⟨L, hLw, hL⟩ := CapelliWordSumExpansion.cvWordSumG k r Y
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hCkn : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) F := B5.ckOn_mono (by exact_mod_cast hnm) hCk
  have hJ := hJW k r Wp Wq D A m F hThr hF
  have hJck : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (Om k r D.z D.z') (JF D F) := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, he⟩ := hJ.1 g₀ ⟨(CapelliUnderIntegral.glev0 g₀).2 hg₀.1, hg₀.2⟩
    exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast hnm),
      fun g' hg'U hg'G => he g' hg'U ((CapelliUnderIntegral.glev0 g').2 hg'G)⟩
  have hw : ∀ cw ∈ L, (∀ X ∈ cw.2, unitLie k r X) ∧ cw.2.length ≤ m :=
    fun cw h => ⟨(hLw cw h).1, (hLw cw h).2.trans hnm⟩
  have hword : ∀ cw ∈ L, Integrable (fun p => xiP D p • Rw cw.2 (rho D p F) g) D.μSS ∧
      Rw cw.2 (JF D F) g = ∫ p, xiP D p • Rw cw.2 (rho D p F) g ∂D.μSS := by
    intro cw hcw
    obtain ⟨hint, heq⟩ := hJ.2 [] cw.2 (by simp) (hw cw hcw).1 (by simpa using (hw cw hcw).2) g hg
    have hae : (fun p => xiP D p • rho D p (dLR ([].map (AdL p)) (cw.2.map (AdR p)) F) g) =ᵐ[D.μSS]
        (fun p => xiP D p • Rw cw.2 (rho D p F) g) := by
      filter_upwards [B5.ae_inSS D] with p hp
      have e := hRR k r Wp Wq D m F p hp hCk [] cw.2 (by simp)
        (fun X hX => ((hw cw hcw).1 X hX).1) (by simpa using (hw cw hcw).2) g hg.1
      simp only [List.map_nil] at e ⊢
      rw [← e]
      rfl
    exact ⟨hint.congr hae, (show Rw cw.2 (JF D F) g = dLR [] cw.2 (JF D F) g from rfl).trans
      (heq.trans (integral_congr_ae hae))⟩
  rw [hL _ _ (JF D F) hJck g hg hg.1]
  have hae2 : (fun p => xiP D p • Q.CV k r Y (rho D p F) g) =ᵐ[D.μSS]
      (fun p => (L.map (fun cw => cw.1 • (xiP D p • Rw cw.2 (rho D p F) g))).sum) := by
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hL _ _ (rho D p F) (B5.ckOn_rho D hp hCkn) g hg.1 hg.1, List.smul_sum, List.map_map]
    congr 1
    refine List.map_congr_left (fun cw _ => ?_)
    simp only [Function.comp_apply]
    exact smul_comm _ _ _
  rw [integral_congr_ae hae2, CapelliUnderIntegral.integral_map_sum L
    (fun cw p => cw.1 • (xiP D p • Rw cw.2 (rho D p F) g))
    (fun cw hcw => (hword cw hcw).1.smul cw.1)]
  congr 1
  refine List.map_congr_left (fun cw hcw => ?_)
  rw [integral_smul, (hword cw hcw).2]

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DeterminantReindex
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

namespace DeterminantReindex

open C2x2 CardInsertEmbedding

lemma perm_of_range {m k : ℕ} (e ρ : Fin k → Fin m) (he : Function.Injective e)
    (hr : ∀ t, ∃ s, ρ s = e t) : ∃ τ : Equiv.Perm (Fin k), ∀ t, e t = ρ (τ t) := by
  choose τ' hτ' using hr
  have hinj : Function.Injective τ' := by
    intro x y hxy; apply he; rw [← hτ' x, ← hτ' y, hxy]
  refine ⟨Equiv.ofBijective τ' (Finite.injective_iff_bijective.mp hinj), fun t => ?_⟩
  simp [hτ']

lemma det_reindex {m k : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (e ρ f : Fin k → Fin m) (τ : Equiv.Perm (Fin k))
    (h : ∀ t, e t = ρ (τ t)) :
    (M.submatrix e f).det = ((Equiv.Perm.sign τ : ℤ) : ℂ) * (M.submatrix ρ f).det := by
  have : M.submatrix e f = (M.submatrix ρ f).submatrix τ id := by
    ext t s; simp [h]
  rw [this, Matrix.det_permute]

lemma sign_sq {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    ((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simp

lemma sign_pm {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1 ∨ ((Equiv.Perm.sign τ : ℤ) : ℂ) = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simp

lemma U_mul_sub {m k : ℕ} (hkm : k ≤ m) (M U : Matrix (Fin m) (Fin m) ℂ) (hU : ∀ i j, j < i → U i j = 0)
    (e f : Fin k → Fin m) (hf : ∀ t, (f t).val = t.val) :
    (M * U).submatrix e f = M.submatrix e f * U.submatrix f f := by
  ext t s
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [sum_emb hkm f hf]
  intro j hj
  rw [hU _ _ (by rw [Fin.lt_def, hf]; omega), mul_zero]

lemma submatrix_mul_monomialMatrix {m k : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (M : Matrix (Fin m) (Fin m) ℂ)
    (e f : Fin k → Fin m) :
    (M * C2.monoP w d).submatrix e f = M.submatrix e (fun s => w (f s)) * Matrix.diagonal (fun s => d (f s)) := by
  ext t s
  rw [Matrix.mul_diagonal]
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, C2.monoP, Matrix.of_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma prod_emb {m k n : ℕ} (hkn : k = n) (d : Fin m → ℂ) (e : Fin k → Fin m) (he : ∀ t, (e t).val = t.val) :
    ∏ t, d (e t) = ∏ j ∈ Finset.range n, (if h : j < m then d ⟨j, h⟩ else 1) := by
  subst hkn
  rw [← Fin.prod_univ_eq_prod_range (fun j => if h : j < m then d ⟨j, h⟩ else 1)]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  have hlt : t.val < m := by have := (e t).isLt; rw [he] at this; exact this
  rw [dif_pos hlt]; congr 1; exact Fin.ext (he t)

end DeterminantReindex

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvSelf
section
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem contDiff_fsv (s : ℂ) : ContDiff ℝ ∞ (fsv s) := by
  have hL : ContDiff ℝ ∞ (fun t : ℂ => s * t - conj s * conj t) :=
    (contDiff_const.mul contDiff_id).sub (contDiff_const.mul Complex.conjCLE.contDiff)
  exact Complex.contDiff_exp.comp hL

section PairNeg

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem pr_neg_fst (a : Pr V) : (-a).1 = -a.1 := rfl
theorem pr_neg_snd (a : Pr V) : (-a).2.unop = -a.2.unop := rfl

end PairNeg

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HerClassesOfParts
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section Struct

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]

theorem inK_act_span {G G' : Set V} (M : SlopeTestRemainingChoices S (Pr V)) (hM : ∀ a b, ∀ Φ ∈ G, (M a b).1 Φ ∈ Submodule.span ℂ G')
    (x : Ix S → V) (hx : ∀ a, x a ∈ Submodule.span ℂ G) : ∀ a, ∑ b, (M a b).1 (x b) ∈ Submodule.span ℂ G' := by
  intro a
  refine Submodule.sum_mem _ (fun b _ => ?_)
  have hle : Submodule.span ℂ G ≤ (Submodule.span ℂ G').comap (M a b).1 :=
    Submodule.span_le.mpr (fun Φ hΦ => hM a b Φ hΦ)
  exact hle (hx b)

end Struct

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
  {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ} {D : B.RealPlaceData P.k P.r Wp Wq}

theorem herK_sliceIn : SliceIn (S := S) P z z' π π' L st (herK S P z z' π π' L st l0 D) l0 := by
  intro w hw l x hx
  exact inK_act_span _ (fun a b Φ hΦ => Submodule.subset_span (HerGen.slice l w a b Φ hw hΦ)) x hx

theorem herK_waveK : WaveK (S := S) P z z' π π' st (herK S P z z' π π' L st l0 D) l0 := by
  intro w hw l s Wv Wv' hW hW' x hx
  exact inK_act_span _
    (fun a b Φ hΦ => Submodule.subset_span (HerGen.waveC l w s Wv Wv' a b Φ hw hW hW' hΦ)) x hx

theorem herK_waveZ (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')) (hW : multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)))
    (hW' : multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g))) (x : Ix S → RadSp P.k P.r z z' π π')
    (hx : InK (herK S P z z' π π' L st l0 D (Fin.last P.r)) x) :
    InK (herK S P z z' π π' L st l0 D (Fin.last P.r)) (act (Vw (mkP Wv Wv') s w) x) :=
  inK_act_span _ (fun a b Φ hΦ => Submodule.subset_span (HerGen.waveZ w s Wv Wv' a b Φ hw hW hW' hΦ)) x hx

theorem herK_jf (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (hF : JFOK P z z' F) (Φ : RadSp P.k P.r z z' π π')
    (hΦ : IsRadJF P z z' π π' D F Φ) : Φ ∈ herK S P z z' π π' L st l0 D 0 :=
  Submodule.subset_span (HerGen.jf F Φ hF hΦ)

end Classes

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.XiYZhatIdentity
section
theorem Formalism.FourierDecayAlt.P.xi_Y_zhat_identity : Formalism.FourierDecayAlt.C3.XiYZhat :=
  covector_entries
end

