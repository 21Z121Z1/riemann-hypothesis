import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0195
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0132
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplySub
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0196

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDQQ
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def JDHatOpQQ : Prop :=
  ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ X ∈ MA.hatSet (D.parOf S v) L,
        ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))),
          (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ B.SmoothCoef (B.GPos (T v).base) t.2 ∧
            B.Commutes (T v).base (B.GPos (T v).base) t.2 ∧
            GlobCoef t.2 (Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) ∧ (B.opOrder t.2 : ℝ) ≤ Cc * nDim S.G.k S.G.r) ∧
          ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
            MA.actA (D.parOf S v) X (trJ S T v e J) =
              (ts.map fun t => MA.actA (D.parOf S v) t.1 (trJ S T v e (B.opApply t.2 J))).sum

theorem jDHatOpQQ_of (h : JDHatOp) : JDHatOpQQ := by
  obtain ⟨Cc, hCc, H⟩ := h
  exact ⟨Cc, hCc, fun E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa _ hL =>
    H E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hL⟩

def JDecayTrQQd : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      B.JF (T v).base (f v) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      MA.JDecay (D.parOf S v) L (trJ S T v e (B.JF (T v).base (f v))) (2 * S.Ntop + 2)

theorem jDecayTrQQd_of_leaves (h1 : JDHatBdd) (h2 : JDHatOpQQ) (h3 : JDJComm) (h4 : JDCCLower) (h5 : TransferSquareIntegrable)
    (h6 : BoundedOperatorsSquareIntegrable) : JDecayTrQQd := by
  obtain ⟨C2, hC2, H2⟩ := h2
  obtain ⟨C3, H3⟩ := h3
  obtain ⟨C5, H5⟩ := h5
  unfold JDecayTrQQd
  refine ⟨8 * C2 + |C3| + |C5|, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL hJf
  have hmono : ∀ c, c ≤ 8 * C2 + |C3| + |C5| → BuiltOW c S T f χ ν' m₀ top A₀ := fun c hc =>
    ⟨isBuiltPlace_mono hc hB.1, hB.2⟩
  have hB2 := hmono C2 (by linarith [abs_nonneg C3, abs_nonneg C5])
  have hB3 := hmono C3 (by linarith [le_abs_self C3, abs_nonneg C5])
  have hB5 := hmono C5 (by linarith [le_abs_self C5, abs_nonneg C3])
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hTTpos : 0 < (D.parOf S v).TT := by rw [hTT]; exact mul_pos (T v).base.T_pos (T v).base.T'_pos
  have hInCC : ∀ m : ℕ, B.InCC A₀ m (f v) := (hB.1.2.2.2.1.2 v).2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hCk, -, hA, -⟩ := hB.1

  have hR : (0 : ℝ) ≤ (S.G.r : ℝ) := Nat.cast_nonneg _
  have hnE : nDim S.G.k S.G.r = 2 * (S.G.r : ℝ) + S.G.k + 1 := by unfold nDim; push_cast; ring
  have hn : (1 : ℝ) ≤ nDim S.G.k S.G.r := by
    rw [hnE]; have := Nat.cast_nonneg (α := ℝ) S.G.k; linarith
  have hA' : (8 * C2 + |C3| + |C5|) * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * nDim S.G.k S.G.r ^ 2 + nDim S.G.k S.G.r ^ 3) ≤ A₀ := by rw [hnE]; exact hA
  obtain ⟨hK3', hK5'⟩ := jd_arith C2 C3 C5 _ _ _ A₀ hC2 hR hn (Nat.cast_nonneg _) hA'
  have hdm0 : 0 ≤ C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r := by
    have := le_trans zero_le_one hn; positivity
  have hK3 : ∀ i : ℕ, i ≤ 2 * S.Ntop + 1 → ∀ o : ℝ, o ≤ C2 * nDim S.G.k S.G.r →
      C3 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * o +
      C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ≤ A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) := by
    intro i hi o ho
    refine hK3' _ _ ?_ ho
    have : ((i : ℕ) : ℝ) ≤ ((2 * S.Ntop + 1 : ℕ) : ℝ) := by exact_mod_cast hi
    push_cast at this; linarith
  have hK5 : ∀ i : ℕ, i ≤ 2 * S.Ntop + 2 → C5 * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r ≤
      A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) := by
    intro i hi
    refine hK5' _ ?_
    have : ((i : ℕ) : ℝ) ≤ ((2 * S.Ntop + 2 : ℕ) : ℝ) := by exact_mod_cast hi
    push_cast at this; linarith

  let Good : ℕ → (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → Prop := fun i F =>
    B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧ (∀ m : ℕ, B.InCC (A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) m F) ∧
      B.JF (T v).base F ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)
  let tr : (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → M.Ty (D.parOf S v) →
      MA.SmQ (D.parOf S v).r (D.parOf S v).TT := fun F => trJ S T v e (B.JF (T v).base F)
  have hStep : ∀ i, i < 2 * S.Ntop + 2 → ∀ F, Good i F → ∀ X ∈ MA.hatSet (D.parOf S v) L,
      ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))),
        (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ Good (i + 1) t.2) ∧
        MA.actA (D.parOf S v) X (tr F) = (ts.map fun t => MA.actA (D.parOf S v) t.1 (tr t.2)).sum := by
    intro i hi F hF X hX
    obtain ⟨hCkF, hCCF, hFF⟩ := hF
    obtain ⟨ts, hts, hid⟩ := H2 E Wp Wq S T f χ ν' m₀ top A₀ hB2 v e L hFr hGa hQQ hL X hX
    have hthr : ∀ t ∈ ts, C3 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder t.2 : ℝ) +
        C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ≤ A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) :=
      fun t ht => hK3 i (by omega) _ (hts t ht).2.2.2.2
    have l3 : ∀ t ∈ ts, _ := fun t ht =>
      H3 E Wp Wq S T f χ ν' m₀ top A₀ hB3 v t.2 (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) (A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) hdm0
        (hts t ht).2.1 (hts t ht).2.2.1 (hts t ht).2.2.2.1 (hthr t ht) F hCkF hCCF hFF
    refine ⟨ts.map fun t => (t.1, B.opApply t.2 F), ?_, ?_⟩
    · intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht
      have l4 := h4 _ _ _ _ t0.2 (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) (A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) hdm0 (hts t0 ht0).2.2.2.1 F hCkF hCCF
      refine ⟨(hts t0 ht0).1, l4.1, fun m => ?_, (l3 t0 ht0).1⟩
      have e : A₀ - (i : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) - (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) = A₀ - ((i + 1 : ℕ) : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) := by push_cast; ring
      rw [← e]; exact l4.2 m
    · rw [hid (B.JF (T v).base F) hFF, List.map_map]
      congr 1
      refine List.map_congr_left fun t ht => ?_
      simp only [Function.comp]
      congr 1
      exact trJ_congr S T v e _ _ (l3 t ht).2
  intro w hw hwh π
  have hG0 : Good 0 (f v) := ⟨hCk v, fun m => by simpa using hInCC m, hJf⟩
  have hmem := jd_word_span L Good tr (2 * S.Ntop + 2) (h1 _ L hTTpos.le hL) hStep w hw hwh (f v) hG0
  have hgen : ∀ u ∈ {u | ∃ b ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L), ∃ F', Good w.length F' ∧
      u = MA.actA (D.parOf S v) b (tr F')}, componentwiseL2 (D.parOf S v) u := by
    rintro u ⟨b, hb, F', ⟨hCk', hCC', hFF'⟩, rfl⟩
    have l5 := H5 E Wp Wq S T f χ ν' m₀ top A₀ hB5 v e hFr (A₀ - (w.length : ℝ) * (C2 * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r)) (hK5 _ hw) F' hCk' hCC' hFF'
    exact (componentwiseL2_iff_integrable _ _).2 (h6 _ L hTTpos hL b hb _ l5)
  exact (componentwiseL2_iff_integrable _ _).1 (componentwiseL2_of_span _ _ hgen _ hmem) π

theorem jDecayTrQQd_of_open (h2 : JDHatOpQQ) : JDecayTrQQd :=
  jDecayTrQQd_of_leaves hat_bounded_decay_holds h2 transfer_commutation_holds class_lower_decay_holds transfer_square_integrable_holds bounded_operators_square_integrable

theorem jDecayTr_of_hatOp (h2 : JDHatOp) : JDecayTr := jDecayTr_of_open h2 transfer_commutation_holds

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormLevLimit
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.JCTx6.Lev0

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lev0Q {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (z z' : Fin (2 * (0 + ρ) + k + 1) → ℂ) (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (ε : ℝ) (hε : 0 < ε)
    (A₀ A : ℝ) (mm : ℕ) (hA : A + 2 * (((0 + ρ : ℕ) : ℝ) + 1) * (mm : ℝ) ≤ A₀) :
    ∃ ε' C : ℝ, 0 < ε' ∧ 0 ≤ C ∧ ∀ (f : B.Mat k (0 + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ mm f c →
      B.CCle A mm (fun g => ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g) (C * c) ∧
      ∀ g ∈ B.GV k (0 + ρ), ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g ≠ 0 → ε' ≤ Gf k (0 + ρ) z z' g := by
  obtain ⟨δ, hδ, hG, hsupp⟩ := isCutG_div hχ hε
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt k 0 ρ Wp Wq z z' 0 0 (idOp k (0 + ρ) Wp Wq) bumpOne
    (fun x => χ (x / ε)) (δ * ε) (inDD_idOp k ρ Wp Wq) isCutC_bumpOne hG mm mm A₀ (by simp)
  refine ⟨δ * ε, max C 0, by positivity, le_max_right _ _, fun f c hc => ?_⟩
  have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc
  have hS := hC f c hc
  have hF : B.opApply (idOp k (0 + ρ) Wp Wq) (U.cutDG k 0 ρ z z' bumpOne (fun x => χ (x / ε)) f) =
      fun g => ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g := by
    rw [opApply_idOp]
    funext g
    simp [U.cutDG, U.DjU, bumpOne_one]
  rw [hF] at hS
  obtain ⟨hck, -, hbd⟩ := hS
  refine ⟨Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (Formalism.FourierDecayAlt.P.compactly_supported_monotone k (0 + ρ) _
      (A₀ - ((0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) * ((0 : ℕ) : ℝ) - 2 * (((0 + ρ : ℕ) : ℝ) + 1) * ((mm + 0 : ℕ) : ℝ))
      A (C * c) mm _ ?_ ⟨hck, ?_⟩) (mul_le_mul_of_nonneg_right (le_max_left _ _) hc0), ?_⟩
  · push_cast at hA ⊢; linarith
  · intro u v hu hv hl g hg
    refine hbd u v ?_ ?_ hl g hg
    · intro X hX; exact ⟨⟨(hu X hX).1, fun i b hb => absurd hb (Nat.not_lt_zero _)⟩, (hu X hX).2⟩
    · intro X hX; exact ⟨⟨(hv X hX).1, fun i b hb => absurd hb (Nat.not_lt_zero _)⟩, (hv X hX).2⟩
  · intro g hg hne
    have h1 : χ (Gf k (0 + ρ) z z' g / ε) ≠ 0 := by
      intro h0; apply hne; simp [h0]
    have h2 := hsupp _ h1
    rw [le_div_iff₀ hε] at h2
    linarith

def xs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (ε : ℝ) (i : ℕ) (hi : i ≤ r)
    (w : List C.Letter) (p : C.LPt) (hc : r - i = r - D.ptSize p) (h : B.Mat k r → (Wq →L[ℂ] Wp))
    (a : Wd.Ix (Fin w.length)) : B.Mat k (r - i) → (Wq →L[ℂ] Wp) :=
  D.castF hc (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ h ε) i hi w a) p)

theorem sliceQ : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ Cc : ℝ, Cs ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r) (w : List C.Letter), w.length ≤ N →
      ∀ (p : C.LPt) (hc : r - i = r - D.ptSize p), D.IsLocPt p i → ∀ (a : Wd.Ix (Fin w.length)),
      ∃ ε' K : ℝ, 0 < ε' ∧ 0 ≤ K ∧
      (∀ (h : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) h →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h c →
        JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε' (xs T χ ε i hi w p hc h a) ∧
        B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xs T χ ε i hi w p hc h a) (K * c)) ∧
      ∀ (h₁ h₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (c₁ c₂ : ℝ), B.CkOn ⊤ (B.GV k r) h₁ → B.CkOn ⊤ (B.GV k r) h₂ →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h₁ c₁ →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h₂ c₂ →
        ∀ γ ∈ B.GV k (r - i), xs T χ ε i hi w p hc h₁ a γ - xs T χ ε i hi w p hc h₂ a γ =
          xs T χ ε i hi w p hc (fun g => h₁ g - h₂ g) a γ := by
  obtain ⟨Cp, hCp0, hL⟩ := levQ
  refine ⟨max 150 (16 * Cp), by positivity, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw p hc hp a
  rcases Nat.eq_zero_or_pos i with h0 | h1
  · subst h0
    obtain rfl : p = [] := by
      cases p with
      | nil => rfl
      | cons b p =>
        exfalso
        have h1 := (hp.1 b (by simp)).1
        have h2 := hp.2
        simp [D.ptSize] at h2
        omega
    have hfun : ∀ h : B.Mat k r → (Wq →L[ℂ] Wp), xs T χ ε 0 hi w [] hc h a =
        (if a = Wd.e1 then D.cutF T.base χ h ε else 0) := by
      intro h
      funext γ
      have hcm : D.castM (k := k) (a := r - 0) (b := r - D.ptSize []) hc γ = γ := by
        ext i j; rfl
      simp only [xs, D.castF]
      rw [hcm, Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k r _ _ T.base.z_mem T.base.z'_mem, Formalism.FourierDecayAlt.P.Dx1.LZ.uwG_zero]
    obtain ⟨ρ, rfl⟩ : ∃ ρ, r = 0 + ρ := ⟨r, (zero_add r).symm⟩
    have hb := Formalism.FourierDecayAlt.P.JCTx6.Link.budget0 (0 + ρ) k N hk2 A₀ Cc (le_trans (le_max_left _ _) hCc) hA₀
    obtain ⟨ε', C, hε', hC0, hQ⟩ := lev0Q (Wp := Wp) (Wq := Wq) T.base.z T.base.z' χ hχ ε hε A₀ (P5.Auser P0 N + 1) (P5.mmUser P0 N) (by
        simp only [P5.Auser, P5.mmUser, P5.nV, hPk, hPr]
        push_cast
        push_cast at hb
        linarith)
    have hmmM : P5.mmUser P0 N ≤ 3 * (11 * (N * (2 * (0 + ρ) + k + 1) ^ 2 + (2 * (0 + ρ) + k + 1) ^ 3) + 5) := by
      obtain ⟨-, -, b3, -, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Link2.budgetAs (0 + ρ) k N 0 0 hk2 (Nat.zero_le _) (Nat.zero_le _)
      have : P5.mmUser P0 N = 5 + 3 * ((0 + ρ) + 1) * (N + 2) * (2 * (0 + ρ) + k + 1) + N * (0 + ρ) := by
        simp only [P5.mmUser, P5.nV, hPk, hPr]
      omega
    refine ⟨ε', C, hε', hC0, ?_, ?_⟩
    · intro h c _ hcl
      have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hcl
      rw [hfun h]
      by_cases ha : a = Wd.e1
      · rw [if_pos ha]
        obtain ⟨q1, q2⟩ := hQ h c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hmmM hcl)
        exact ⟨⟨q1.1, ⟨_, q1⟩, q2⟩, q1⟩
      · rw [if_neg ha]
        have hz : B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (0 : B.Mat k (0 + ρ - 0) → (Wq →L[ℂ] Wp)) (C * c) :=
          Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (mul_nonneg hC0 hc0)
        exact ⟨⟨hz.1, ⟨_, hz⟩, fun g _ hne => (hne rfl).elim⟩, hz⟩
    · intro h₁ h₂ c₁ c₂ _ _ _ _ γ _
      rw [hfun h₁, hfun h₂, hfun (fun g => h₁ g - h₂ g)]
      by_cases ha : a = Wd.e1
      · simp only [if_pos ha, D.cutF, smul_sub]
      · simp only [if_neg ha, Pi.zero_apply, sub_zero]
  · obtain ⟨ε', K, hε', hK, hQ1, hQ2⟩ := hL Cc (le_trans (le_max_right _ _) hCc) k r Wp Wq T χ A₀ N P0 hPk hPr hk2 hχ
      hA₀ ε hε i hi h1 w hw p hc hp a
    exact ⟨ε', K, hε', hK, hQ1, hQ2⟩

theorem auser_mono (P0 : M.Par) {L N : ℕ} (h : L ≤ N) : P5.Auser P0 L ≤ P5.Auser P0 N := by
  unfold P5.Auser
  have : (L : ℝ) ≤ N := by exact_mod_cast h
  gcongr

theorem mmUser_mono (P0 : M.Par) {L N : ℕ} (h : L ≤ N) : P5.mmUser P0 L ≤ P5.mmUser P0 N := by
  unfold P5.mmUser
  gcongr

theorem formLev_limit {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (N : ℕ) (hw : w.length ≤ N)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (x y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (xn yn : ℕ → Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (Bd : ℝ) (dn : ℕ → ℝ)
    (hdn : Tendsto dn atTop (𝓝 0))
    (hx : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (x e) Bd)
    (hy : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (y e) Bd)
    (hxn : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e) Bd)
    (hyn : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e) Bd)
    (hdx : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e - x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e - x e) (dn n))
    (hdy : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e - y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e - y e) (dn n)) :
    Tendsto (fun n => D.formLev T s j w (xn n) (yn n)) atTop (𝓝 (D.formLev T s j w x y)) := by
  have hAu : P5.Auser P0 w.length + 1 ≤ P5.Auser P0 N + 1 := by linarith [auser_mono P0 hw]
  have hmu : P5.mmUser P0 w.length ≤ P5.mmUser P0 N := mmUser_mono P0 hw
  have hS := Formalism.FourierDecayAlt.P.level_form_sesquilinear_moderate Wp Wq P0 T s j w (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ hε₀ hAu hmu
  obtain ⟨Cf, hCf0, hCf⟩ := Formalism.FourierDecayAlt.P.JCx4.formLev_bound_mm P0 T s j w (P5.Auser P0 N + 1 + 1) (by linarith)
  have hmm5 : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ P5.mmUser P0 N := by
    have := Formalism.FourierDecayAlt.P.JCx2.pd_thr_mm P0 j N (P5.mmUser P0 N) le_rfl
    have h2 : (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ (2 * (P0.r - (j : ℕ)) + P0.k + 1) * N :=
      Nat.mul_le_mul_left _ hw
    omega
  have h5 : 5 ≤ P5.mmUser P0 N := by unfold P5.mmUser; omega
  have hu : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (u e) cu := by
    intro u cu h e
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hmm5 (h e))
  have hv : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1 - 2 * (w.length : ℝ)) 5 (u e) cu := by
    intro u cu h e
    have hw0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m h5 (h e))
  have key : ∀ n, D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y =
      D.formLev T s j w (xn n - x) (yn n) + D.formLev T s j w x (yn n - y) := by
    intro n
    have e1 : xn n = x + (1 : ℂ) • (xn n - x) := by simp
    have e2 : yn n = y + (1 : ℂ) • (yn n - y) := by simp
    have s1 := (hS x (xn n - x) (yn n) 1 (fun e => (hx e).1) (fun e => (hdx n e).1) (fun e => (hyn n e).1)).1
    have s2 := (hS y (yn n - y) x 1 (fun e => (hy e).1) (fun e => (hdy n e).1) (fun e => (hx e).1)).2
    rw [← e1] at s1
    rw [← e2] at s2
    rw [s1, s2]
    simp
    ring
  have hbd : ∀ n, ‖D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y‖ ≤ 2 * Cf * Bd * dn n := by
    intro n
    rw [key n]
    have b1 := hCf (xn n - x) (yn n) (dn n) Bd (hu _ _ fun e => (hdx n e).2) (hv _ _ fun e => (hyn n e).2)
    have b2 := hCf x (yn n - y) Bd (dn n) (hu _ _ fun e => (hx e).2) (hv _ _ fun e => (hdy n e).2)
    calc _ ≤ ‖D.formLev T s j w (xn n - x) (yn n)‖ + ‖D.formLev T s j w x (yn n - y)‖ := norm_add_le _ _
      _ ≤ Cf * dn n * Bd + Cf * Bd * dn n := add_le_add b1 b2
      _ = 2 * Cf * Bd * dn n := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n => 2 * Cf * Bd * dn n) atTop (𝓝 0) := by
    simpa using hdn.const_mul (2 * Cf * Bd)
  exact squeeze_zero (fun n => norm_nonneg _) hbd hlim

end Formalism.FourierDecayAlt.P.PBE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermZeroOfTrace
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem herm_zero_of_trace {ζ : B.Mat k r} (hζ : B.inLie k r ζ) (u v : Fin (2 * r + k + 1) → ℂ)
    (h1 : (Matrix.trace (ζ * Xuv k r u v)).re = 0)
    (h2 : (Matrix.trace (ζ * Xuv k r u (Complex.I • v))).re = 0) :
    herm (Hpk k r) (ζ *ᵥ u) v = 0 := by
  rw [trace_xuv] at h1 h2
  have hs : ∀ w, herm (Hpk k r) (ζ *ᵥ w) u = -star (herm (Hpk k r) (ζ *ᵥ u) w) := by
    intro w
    rw [herm_skew hζ, herm_swap w]
  rw [hs] at h1 h2
  rw [herm_smul_right] at h2
  set A := herm (Hpk k r) (ζ *ᵥ u) v
  simp [Complex.ext_iff, Complex.mul_re, Complex.mul_im] at h1 h2 ⊢
  constructor <;> linarith

theorem herm_bvec (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    herm (Hpk k r) x (bvec i) = (Hpk k r *ᵥ x) i := by
  rw [herm_eq, Finset.sum_eq_single i]
  · simp [bvec]
  · intro j _ hj; simp [bvec, hj]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem herm_e (x : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) x (bvec (eI k r b)) = x (esI k r b) := by
  rw [herm_bvec, hpk_mulVec, if_pos (Or.inl (by simp [eI]))]
  rfl

theorem herm_es (x : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) x (bvec (esI k r b)) = x (eI k r b) := by
  rw [herm_bvec, hpk_mulVec, if_pos (Or.inr (by simp [esI]; omega))]
  congr 1
  apply Fin.ext
  simp [eI, esI]
  omega

theorem herm_w (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) :
    herm (Hpk k r) x (bvec i) = if i.val = r + k then -x i else x i := by
  rw [herm_bvec, hpk_mulVec, if_neg (by omega)]

theorem inWb_sub {u v : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (hv : inWb k r v) : inWb k r (u - v) := by
  intro i hi; simp [hu i hi, hv i hi]

theorem inWb_smul (c : ℂ) {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) : inWb k r (c • u) := by
  intro i hi; simp [hu i hi]

def sg (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hpk_mulVec_wb {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ u) i = sg (k := k) (r := r) i * u i := by
  rw [hpk_mulVec, sg]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, hu i h, hu ⟨2 * r + k - i.val, by omega⟩ (by simp; omega), mul_zero]
  · rw [if_neg h]
    split_ifs <;> ring

def KI (k r : ℕ) : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩

theorem herm_wb {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) u y = ∑ i ∈ Finset.univ.erase (KI k r), star (y i) * u i - star (y (KI k r)) * u (KI k r) := by
  rw [herm_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (KI k r))]
  have hK : sg (k := k) (r := r) (KI k r) = -1 := by simp [sg, KI]
  rw [hpk_mulVec_wb hu, hK]
  have : ∀ i ∈ Finset.univ.erase (KI k r), star (y i) * (Hpk k r *ᵥ u) i = star (y i) * u i := by
    intro i hi
    rw [hpk_mulVec_wb hu]
    have : i.val ≠ r + k := fun e => (Finset.mem_erase.1 hi).1 (Fin.ext (by simp [KI, e]))
    simp [sg, this]
  rw [Finset.sum_congr rfl this]
  ring

theorem re_star_mul_self (a : ℂ) : (star a * a).re = ‖a‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem wb_definite {z w : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hw : inWb k r w) (hwz : herm (Hpk k r) w z = 0) (hww : (herm (Hpk k r) w w).re ≤ 0) : w = 0 := by
  set S := Finset.univ.erase (KI k r)
  set K := KI k r
  have e2 : (herm (Hpk k r) w w).re = ∑ i ∈ S, ‖w i‖ ^ 2 - ‖w K‖ ^ 2 := by
    rw [herm_wb hw, Complex.sub_re, Complex.re_sum, re_star_mul_self]
    simp only [re_star_mul_self]
    rfl
  have eT : Tz k r z = ‖z K‖ ^ 2 - ∑ i ∈ S, ‖z i‖ ^ 2 := by
    rw [Tz, herm_wb hz, Complex.sub_re, Complex.re_sum, re_star_mul_self]
    simp only [re_star_mul_self]
    ring
  rw [herm_wb hw, sub_eq_zero] at hwz
  have hn : ‖z K‖ * ‖w K‖ ≤ ∑ i ∈ S, ‖z i‖ * ‖w i‖ := by
    calc ‖z K‖ * ‖w K‖ = ‖star (z K) * w K‖ := by rw [norm_mul, norm_star]
      _ = ‖∑ i ∈ S, star (z i) * w i‖ := by rw [hwz]
      _ ≤ ∑ i ∈ S, ‖star (z i) * w i‖ := norm_sum_le _ _
      _ = ∑ i ∈ S, ‖z i‖ * ‖w i‖ := by simp only [norm_mul, norm_star]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => ‖z i‖) (fun i => ‖w i‖)
  set P := ∑ i ∈ S, ‖w i‖ ^ 2
  set Q := ∑ i ∈ S, ‖z i‖ ^ 2
  set m := ∑ i ∈ S, ‖z i‖ * ‖w i‖
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i _ => by positivity)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => by positivity)
  have ha : 0 ≤ ‖w K‖ := norm_nonneg _
  have hc : 0 ≤ ‖z K‖ := norm_nonneg _
  have h1 : P ≤ ‖w K‖ ^ 2 := by linarith
  have h2 : Q < ‖z K‖ ^ 2 := by linarith
  have h3 : (‖z K‖ * ‖w K‖) ^ 2 ≤ m ^ 2 := by
    have : 0 ≤ ‖z K‖ * ‖w K‖ := by positivity
    exact pow_le_pow_left₀ this hn 2
  have h4 : (‖z K‖ * ‖w K‖) ^ 2 ≤ Q * ‖w K‖ ^ 2 := by
    calc (‖z K‖ * ‖w K‖) ^ 2 ≤ m ^ 2 := h3
      _ ≤ Q * P := hcs
      _ ≤ Q * ‖w K‖ ^ 2 := mul_le_mul_of_nonneg_left h1 hQ
  have h5 : ‖w K‖ ^ 2 * (‖z K‖ ^ 2 - Q) ≤ 0 := by nlinarith
  have h6 : ‖w K‖ ^ 2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have : 0 < ‖w K‖ ^ 2 * (‖z K‖ ^ 2 - Q) := mul_pos hcon (by linarith)
    linarith
  have hwK : w K = 0 := by
    have : ‖w K‖ = 0 := by nlinarith
    exact norm_eq_zero.1 this
  have hP0 : P = 0 := le_antisymm (by nlinarith) hP
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 hP0
  funext i
  by_cases hi : i = K
  · rw [hi, hwK]; rfl
  · have := hall i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at this
    rw [this]; rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

