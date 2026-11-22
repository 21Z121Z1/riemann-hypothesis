import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PNefCountAlongMultiples
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Dominated

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAmpleCountAlongMultiplesX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

theorem AmpleCountAlongMultiples.statementB (hBig : NefBigCountAlongMultiples.Statement) (hPk : PackingStatement) :
    G6.StatementB := by
  intro K _ ι _ Ω _ _ y D M P0 II hD hII har hb hM
  obtain ⟨-, Cp, hCp⟩ := hPk K ι Ω y D M (chartLat y M.a) har hb hM.semipos.1
    (fun τ _ hs' c hc' => isIntegral_algebraMap (x := (⟨_, hs' c hc'⟩ : chartRingZ y c)))
  exact NefCountAlongMultiples.le_arithmeticVolume_of_alongMultiples hCp fun ε hε => hBig K ι Ω y D M P0 II hD hII har hb hM ε hε

theorem AmpleCountAlongMultiples.top_nonpos (hBig : NefBigCountAlongMultiples.Statement) (hPk : PackingStatement)
    (hN : ShiftNefBig.Statement) (hV : ShiftVolumeBound.Statement) (hI : ShiftIntersectionPolynomial.Statement)
    (hG : ShiftDegreePolynomial.Statement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {D : ℕ} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {P0 : Ideal (MRing ι)}
    {II : IntersectionSystem} (hD : 1 ≤ D) (hII : IsIntersectionSystem II)
    (har : IsArithVar (mCoordIdeal y) (D + 1)) (hb : Birational y) (hP0 : P0 ≤ mCoordIdeal y)
    (hs : IsSemipositiveRel P0 (mCoordIdeal y) A) (hnef : NefOnFibres (mCoordIdeal y) A.a)
    (hc : IsConjInvariantH A) (hdeg : genDeg (mCoordIdeal y) D A.a ≤ 0) :
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A) ≤ 0 := by
  have : CharZero Ω := ArithmeticVolumeDegreeZero.charZero_of_horizontal y har.2.2.1
  have hB := AmpleCountAlongMultiples.statementB hBig hPk
  obtain ⟨C, hC0, hC⟩ := hV K ι Ω y D A P0 hD har hb hP0 hs hnef hc
  obtain ⟨p, hpdeg, hpc, hp⟩ := hI K ι II (mCoordIdeal y) (D + 1) A (fsH ι) hII har hs.1
    (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1)
  obtain ⟨r, hrdeg, hrc, hr⟩ := hG K ι (mCoordIdeal y) D A.a ((1 : ℤ) • (fsH ι).a) har
  have hbound : ∀ q : ℕ, 1 ≤ q → p.eval (q : ℝ) ≤ C * ((q : ℝ) + 1) * r.eval (q : ℝ) := by
    intro q hq
    rw [← hp q, ← hr q]
    exact (hB K ι Ω y D _ P0 II hD hII har hb (hN K ι Ω y D A P0 hD har hb hP0 hs hnef hc q hq)).trans (hC q hq)
  rw [← hpc]
  exact ArithmeticVolumeDegreeZero.coeff_le_of_eval_le_mul p r hC0 hpdeg hrdeg (by rw [hrc]; exact_mod_cast hdeg) hbound

theorem AmpleCountAlongMultiples.proof (hBig : NefBigCountAlongMultiples.Statement)
    (hF : AmpleVNefOnFibres.Statement) (hPk : PackingStatement) (hN : ShiftNefBig.Statement)
    (hV : ShiftVolumeBound.Statement) (hI : ShiftIntersectionPolynomial.Statement)
    (hG : ShiftDegreePolynomial.Statement) : AmpleCountAlongMultiples.Statement := by
  intro K _ _ ι _ _ Ω _ y D N P0 II hD hII har hb hP0 hs hcj _ hfib ε hε
  have hnef : NefOnFibres (mCoordIdeal y) N.a := hF K ι Ω y N.a hfib
  by_cases hT : II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε ≤ 0
  · exact ⟨1, le_rfl, Eventually.of_forall fun n =>
      (mul_nonpos_of_nonpos_of_nonneg hT (by positivity)).trans (Real.log_natCast_nonneg _)⟩
  by_cases hg : genDeg (mCoordIdeal y) D N.a ≤ 0
  · exact absurd (AmpleCountAlongMultiples.top_nonpos hBig hPk hN hV hI hG hD hII har hb hP0 hs hnef hcj hg)
      (by linarith)
  exact hBig K ι Ω y D N P0 II hD hII har hb ⟨hP0, hs, hcj, hnef, by omega⟩ ε hε

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNefBigCountAlongMultiples
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace NefBigCountAlongMultiples

theorem two_zcomb_sub_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (q k : ℕ) (hkq : k < q) :
    ((2 : ℕ) • (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * ((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)).a - fun _ => (1 : ℤ)) =
      ((2 * (q - k) : ℕ) : ℤ) • M.a + fun _ => ((1 : ℕ) : ℤ) := by
  funext j
  have hfs : (fsH ι).a j = 1 := rfl
  simp only [HermLine.zcomb, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hfs]
  rw [Nat.cast_mul, Nat.cast_sub hkq.le]
  push_cast
  ring

theorem along_of_shift (hAC : AmpleCountAlongMultiples.StatementAmple) (hGD : GenDegGeomDeg.Statement)
    (hPk : PackingStatement)
    {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} {A N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {P0 : Ideal (MRing ι)} {II : IntersectionSystem} {e : Ω} {C T ε : ℝ} {p q : ℕ}
    (hD : 1 ≤ D) (hII : IsIntersectionSystem II) (har : IsArithVar (mCoordIdeal y) (D + 1)) (hb : Birational y)
    (hP0 : P0 ≤ mCoordIdeal y) (hsA : IsSmoothHerm A) (hq : 1 ≤ q) (hε : 0 < ε)
    (hsp : IsSemipositiveRel P0 (mCoordIdeal y) N) (hci : IsConjInvariantH N)
    (hamp : KH.AmpleV ℚ (KH.genIdeal y) N.a)
    (hamp2 : ∃ c : ℕ, 1 ≤ c ∧ KH.AmpleV ℚ (KH.genIdeal y) (c • N.a - fun _ => 1))
    (hampl : ∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) N.a) (he0 : e ≠ 0)
    (hmap : ∀ (n : ℕ) (s : Ω), s ∈ chartLat y N.a n → s * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧
      ∀ c : ℝ, IsBoundedH (mCoordIdeal y) y N n c s →
        IsBoundedH (mCoordIdeal y) y A (q * n) (c * Real.exp (((p * n : ℕ) : ℝ) * C)) (s * e ^ (p * n)))
    (hnum : (T - ε) * (q : ℝ) ^ (D + 1) + ε / 4 * (q : ℝ) ^ (D + 1) ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => N) -
        ((D : ℝ) + 1) * ((p : ℝ) * C) * (genDeg (mCoordIdeal y) D N.a : ℝ)) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ᶠ k : ℕ in atTop,
      (T - ε) * (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (a * k) := by
  obtain ⟨b, hb1, hev⟩ := hAC K ι Ω y D (HermLine.constShift N ((p : ℝ) * C)) P0 II hD hII har hb hP0
    (isSemipositiveRel_constShift hsp _) (isConjInvariantH_constShift hci _)
    (by rw [constShift_a]; exact hamp) (by rw [constShift_a]; exact hamp2) (by rw [constShift_a]; exact hampl)
    (ε / 4 * (q : ℝ) ^ (D + 1)) (by positivity)
  have htop : II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.constShift N ((p : ℝ) * C)) =
      II K ι (mCoordIdeal y) (D + 1) (fun _ => N) -
        ((D : ℝ) + 1) * ((p : ℝ) * C) * (genDeg (mCoordIdeal y) D N.a : ℝ) := by
    rw [ConstantShift.proof K ι (II K ι) (mCoordIdeal y) D N _ (hII K ι) har hsp.1, hGD K ι Ω y D N har hsp.1]
  have hfin := (hPk K ι Ω y D A (chartLat y A.a) har hb hsA
    (fun τ _ hs' c hc' => isIntegral_algebraMap (x := (⟨_, hs' c hc'⟩ : chartRingZ y c)))).1
  refine ⟨q * b, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  filter_upwards [hev] with j hj
  have hX : (0 : ℝ) ≤ ((b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
  calc (T - ε) * (((q * b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))
      = ((T - ε) * (q : ℝ) ^ (D + 1)) * (((b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
        push_cast
        ring
    _ ≤ (II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.constShift N ((p : ℝ) * C)) -
          ε / 4 * (q : ℝ) ^ (D + 1)) * (((b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right (by rw [htop]; linarith) hX
    _ ≤ _ := hj
    _ ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (q * (b * j)) :=
        NefCountAlongMultiples.count_shift_le he0 (hmap (b * j)) (hfin _)
    _ = _ := by rw [mul_assoc]

theorem proof (hG2 : G2.Statement) (hAC : AmpleCountAlongMultiples.StatementAmple)
    (hNA : NefAmpleGeneric.Statement) (hGD : GenDegGeomDeg.Statement) (hPk : PackingStatement) :
    NefBigCountAlongMultiples.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hD hII har hb hA ε hε
  have : CharZero Ω := ArithmeticVolumeDegreeZero.charZero_of_horizontal y har.2.2.1
  let _ : LinearOrder K := LinearOrder.lift' _ (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k => LinearOrder.lift' _ (Fintype.equivFin (ι k)).injective
  obtain ⟨k, e, C, -, hC, he0, -, -, hpq, hconv⟩ := hG2 K ι Ω y D A P0 II hD hII har hb hA
  obtain ⟨δ, hδ, hδc⟩ := hconv (ε / 4) (by linarith)
  have hg0 : (0 : ℝ) < (genDeg (mCoordIdeal y) D A.a : ℝ) := by exact_mod_cast hA.big
  obtain ⟨q, hq⟩ := exists_nat_gt ((k : ℝ) + 1 / δ +
    4 * (((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4)) / ε)
  have hX0 : 0 ≤ 4 * (((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4)) / ε := by
    positivity
  have hδ' : 0 < 1 / δ := by positivity
  have hkq : k * 1 < q := by
    have : (k : ℝ) < q := by linarith
    rw [mul_one]
    exact_mod_cast this
  have hq1 : 1 ≤ q := by omega
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hpqδ : ((1 : ℕ) : ℝ) / q < δ := by
    have h1 : 1 / δ < q := by linarith
    rw [div_lt_iff₀ hδ] at h1
    rw [Nat.cast_one, div_lt_iff₀ hqpos]
    linarith
  have hqC : ((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4) < q * (ε / 4) := by
    have h1 : 4 * (((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4)) / ε < q := by linarith
    rw [div_lt_iff₀ hε] at h1
    linarith
  obtain ⟨hsp, hci, hamp, hampl, hmap⟩ := hpq 1 q one_pos hkq
  obtain ⟨htop, hdeg⟩ := hδc 1 q one_pos (by omega) hpqδ
  have hamp2 : ∃ c : ℕ, 1 ≤ c ∧ KH.AmpleV ℚ (KH.genIdeal y)
      (c • (HermLine.zcomb A (fsH ι) ((q : ℤ) - k * ((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)).a - fun _ => 1) := by
    refine ⟨2, by norm_num, ?_⟩
    rw [two_zcomb_sub_one A q k (by omega)]
    exact hNA K ι Ω y D A P0 (2 * (q - k)) 1 har hA.normalForm_baseLattice_le_dualSpan_sup_line hA.semipos (by omega) le_rfl
  exact along_of_shift hAC hGD hPk hD hII har hb hA.normalForm_baseLattice_le_dualSpan_sup_line hA.semipos.1 hq1 hε hsp hci hamp hamp2 hampl he0 hmap
    (NefCountAlongMultiples.num_bound hε hqpos hC htop hdeg hqC)

end NefBigCountAlongMultiples

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StAmpleOnModelRestrict
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def AmpleOnModelRestrict.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω Ω' : Type) [Field Ω] [Field Ω']
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι k) → Ω') (a : K → ℤ),
    mCoordIdeal y ≤ mCoordIdeal y' → IsAmpleOnModel y a → IsAmpleOnModel y' a

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StArithNMLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def IsGenBySmallSections (y : (Σ k, ι k) → Ω) (L : HermLine ι) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ (q : ℕ) (w : Fin q → Ω),
    (∀ j, w j ∈ chartLat y (GroundTheory.Heights₂.Heights.Inter.hermZpow L n).a 1) ∧
    KH.GeneratesOn y (GroundTheory.Heights₂.Heights.Inter.hermZpow L n).a w ∧
    ∃ c : ℝ, c < 1 ∧
      ∀ j, IsBoundedH (mCoordIdeal y) y (GroundTheory.Heights₂.Heights.Inter.hermZpow L n) 1 c (w j)

end Objects

def ArithNMLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : HermLine ι) (P0 : Ideal (MRing ι)),
    IsArithVar (mCoordIdeal y) (D + 1) →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) L → IsConjInvariantH L →
    IsAmpleOnModel y L.a →
    (∃ m : ℕ, 1 ≤ m ∧ ∃ s ∈ chartLat y (GroundTheory.Heights₂.Heights.Inter.hermZpow L m).a 1, s ≠ 0 ∧
      ∃ c : ℝ, c < 1 ∧ IsBoundedH (mCoordIdeal y) y (GroundTheory.Heights₂.Heights.Inter.hermZpow L m) 1 c s) →
    (∀ (W : Ideal (MRing ι)) (e : ℕ), IsArithVar W (e + 1) → mCoordIdeal y ≤ W → e < D →
      ∀ (Ω' : Type) [Field Ω'] (y' : (Σ k, ι k) → Ω'), mCoordIdeal y' = W → IsGenBySmallSections y' L) →
    IsGenBySmallSections y L

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StArithNMSmallSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def ArithNMSmallSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) L → IsConjInvariantH L →
    IsAmpleOnModel y L.a →
    0 < II K ι (mCoordIdeal y) (D + 1) (fun _ => L) →
    ∃ m : ℕ, 1 ≤ m ∧ ∃ s ∈ chartLat y (GroundTheory.Heights₂.Heights.Inter.hermZpow L m).a 1, s ≠ 0 ∧
      ∃ c : ℝ, c < 1 ∧ IsBoundedH (mCoordIdeal y) y (GroundTheory.Heights₂.Heights.Inter.hermZpow L m) 1 c s

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StSmallGenHeightsNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SmallGenHeightsNonneg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι)
    (II : IntersectionSystem) (q : ℕ) (w : Fin q → MRing ι),
    IsIntersectionSystem II → IsSmoothHerm A → (∀ k, 0 ≤ A.a k) →
    (∀ j, IsMultiHomog (w j) fun k ↦ (A.a k).toNat) →
    (∀ Q : Ideal (MRing ι), IsMultiProjPrime Q → P ≤ Q → ∃ j, w j ∉ Q) →
    (∀ j, ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) (w j))‖ ≤ A.h z) →
    HeightsNonneg II P A

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

