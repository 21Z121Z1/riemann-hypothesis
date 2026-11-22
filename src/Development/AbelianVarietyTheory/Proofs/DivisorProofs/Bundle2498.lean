import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2400
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0106

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDataBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.FunDat

section Val

variable {D : D7}

theorem lossLe_one (w : PlL D) : LossLe w 1 0 := ⟨1, map_one _, Or.inr (by simp [Formalism.DivisionValues.ValuationRepresentative.vw_one])⟩

theorem lossLe_mul {w : PlL D} {z z' : ℂ} {a a' : ℝ} (h : LossLe w z a) (h' : LossLe w z' a') :
    LossLe w (z * z') (a + a') := by
  obtain ⟨y, rfl, hy⟩ := h
  obtain ⟨y', rfl, hy'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y = 0
  · exact Or.inl (by simp [h0])
  by_cases h0' : y' = 0
  · exact Or.inl (by simp [h0'])
  rcases hy with h1 | h1
  · exact absurd h1 h0
  rcases hy' with h2 | h2
  · exact absurd h2 h0'
  refine Or.inr ?_
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h0 h0', Int.cast_add]
  linarith

theorem lossLe_prod {w : PlL D} {ι : Type*} (s : Finset ι) (z : ι → ℂ) (a : ι → ℝ) (h : ∀ i ∈ s, LossLe w (z i) (a i)) :
    LossLe w (∏ i ∈ s, z i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lossLe_one w
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact lossLe_mul (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem loss_mono {dl : PlL D → ℝ} {B B' : ℝ} (h : Loss dl B) (hB : B ≤ B') : Loss dl B' :=
  ⟨h.1, h.2.1, fun s => (h.2.2 s).trans hB⟩

end Val

section Sum

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

def dlD (K : ℝ) (w : PlL D) : ℝ := ∑ P ∈ G.pl.W0, K * (cosExp G P : ℝ) * (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ)

theorem sum_cosExp_le : ∑ P ∈ G.pl.W0, (cosExp G P : ℝ) * Real.log (resCard (Kw P) : ℕ) ≤ 2 * sig G := by
  classical
  have hinj : Set.InjOn G.pl.w (G.pl.S0 : Set (Pl D.host.F)) := fun v hv v' hv' h =>
    (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))
  rw [Places.W0, Finset.sum_image hinj, sig, Finset.mul_sum]
  refine Finset.sum_le_sum fun v hv => ?_
  obtain ⟨h1, -⟩ := depthAt_w G hv
  rw [h1, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]
  have h2 := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.log_absNorm_le (G.pl.w v)
  rw [G.pl.under_w hv] at h2
  have h3 : (0 : ℝ) ≤ (G.pl.depth sc v : ℝ) := by positivity
  calc (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm (G.pl.w v).asIdeal : ℕ)
      ≤ (G.pl.depth sc v : ℝ) * (2 * Real.log (Ideal.absNorm v.asIdeal)) := mul_le_mul_of_nonneg_left h2 h3
    _ = _ := by ring

theorem loss_dlD {K : ℝ} (hK : 0 ≤ K) : Loss (dlD G K) (2 * K * sig G) := by
  classical
  refine ⟨fun w => Finset.sum_nonneg fun P _ => mul_nonneg (by positivity) ?_, ?_, fun s => ?_⟩
  · exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w _
  · refine ((G.pl.W0.finite_toSet.biUnion fun P _ =>
      ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.finite_vw_ne (K := D.what₂.LL) (resCard (Kw P))
        (ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P))).subset fun w hw => ?_
    by_contra h
    refine hw (Finset.sum_eq_zero fun P hP => ?_)
    have : vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) = 0 := by
      by_contra h'
      exact h (Set.mem_biUnion hP h')
    simp [this]
  · have h1 : ∑ w ∈ s, lw w * dlD G K w =
        ∑ P ∈ G.pl.W0, K * (cosExp G P : ℝ) * ∑ w ∈ s, lw w * (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ) := by
      simp only [dlD, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun w _ => by ring
    have h2 : ∑ w ∈ s, lw w * dlD G K w ≤ ∑ P ∈ G.pl.W0, K * (cosExp G P : ℝ) * Real.log (resCard (Kw P) : ℕ) := by
      rw [h1]
      exact Finset.sum_le_sum fun P _ => mul_le_mul_of_nonneg_left
        (Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le s _ (ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P)) (by positivity)
    calc ∑ w ∈ s, lw w * dlD G K w ≤ _ := h2
      _ = K * ∑ P ∈ G.pl.W0, (cosExp G P : ℝ) * Real.log (resCard (Kw P) : ℕ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun P _ => by ring
      _ ≤ K * (2 * sig G) := mul_le_mul_of_nonneg_left (sum_cosExp_le G) hK
      _ = 2 * K * sig G := by ring

end Sum

end GlobalTheory.FunDat

end

noncomputable section

namespace GlobalTheory.FunDat

section Cases

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem away_cases {t : T} {w : PlL D} (hA : Away G t w) {P : Pl D.host.E} (hl : P ∈ locPl G t) :
    P ∈ G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := by
  classical
  by_cases hP : P ∈ G.pl.W0
  · exact Or.inl hP
  have hQ : P ∈ L.Q t := by
    rcases Finset.mem_union.1 hl with h | h
    · exact absurd h hP
    · exact h
  refine Or.inr ?_
  rcases hA P hQ with h | h
  · exfalso
    rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact G.pl.levelPlace_ne_basePlace t P hQ h
    · exact hP (by
        rw [G.pl.w_Q t P hQ h]
        exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h)))
  · exact h _ (Formalism.EigenvalueLevelCeiling.plc_prime P) (Formalism.EigenvalueLevelCeiling.plc_mem P)

theorem sum_locPl (t : T) (K : ℝ) (w : PlL D) :
    ∑ v : locPl G t, K * (cosExp G v : ℝ) * (vw w ((resCard (Kw (v : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ) = dlD G K w := by
  classical
  rw [Finset.sum_coe_sort (locPl G t) fun P => K * (cosExp G P : ℝ) * (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ), dlD]
  refine (Finset.sum_subset Finset.subset_union_left fun P _ hn => ?_).symm
  simp [(depthAt_of_notMem G hn).1]

end Cases

theorem finDatK_of (hA : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₁ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum) (P : Pl D.host.E), P ∈ locPl ch.G t → ∀ w : PlL D,
        (P ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) (c₁ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * large₂.sc.b * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ))) (hB : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₂ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t) (w : PlL D),
        ((P : Pl D.host.E) ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ c : ℝ, 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
        ∀ X Y, LossLe w ((ch.S.term t Φ β P).datum X Y) (c + c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ))) : FinDatK := by
  obtain ⟨CFa, hA⟩ := hA
  obtain ⟨CFb, hB⟩ := hB
  refine ⟨max CFa CFb, fun CF hCF => ?_⟩
  obtain ⟨c₁, hA⟩ := hA CF ((le_max_left _ _).trans hCF)
  obtain ⟨c₂, hB⟩ := hB CF ((le_max_right _ _).trans hCF)
  refine ⟨max 2 (2 * (max c₁ 0 + max c₂ 0)), fun ε C hC => ?_⟩
  obtain ⟨xa, hA⟩ := hA ε
  obtain ⟨xb, hB⟩ := hB ε
  refine ⟨max xa xb, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hIs hSc hF => ?_⟩
  have hA := hA D large₂ hε ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F s ch hIs hSc hF
  have hB := hB D large₂ hε ((le_max_right _ _).trans hx) Γ Pl0 T A Ks R F s ch hIs hSc hF
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hf : (1 : ℝ) ≤ D.R.f := by
    have h1 : D.R.m ≤ D.R.f := D.R.m_le_f
    have h2 := D.R.two_le_m
    exact_mod_cast (show 1 ≤ D.R.f by omega)
  set K0 : ℝ := max c₁ 0 + max c₂ 0 with hK0
  have hK0' : 0 ≤ K0 := add_nonneg (le_max_right _ _) (le_max_right _ _)
  set M : ℝ := (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  set K : ℝ := K0 * M * large₂.sc.b with hK
  have hK' : 0 ≤ K := mul_nonneg (mul_nonneg hK0' hM0) (by linarith)
  have hC2 : 2 * K0 ≤ C := (le_max_right _ _).trans hC
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 2).trans ((le_max_left _ _).trans hC)
  have hsig := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.sig_nonneg ch.G
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg hb
  have hbound : 2 * K * sig ch.G ≤ D.R.m * bOne ch.G C large₂.sc.b := by
    have h1 : 2 * K0 * sig ch.G ≤ C * D.R.f * (Real.log large₂.sc.b + sig ch.G) := by
      have h2 : 2 * K0 * sig ch.G ≤ C * sig ch.G := mul_le_mul_of_nonneg_right hC2 hsig
      have h3 : C * sig ch.G ≤ C * D.R.f * (Real.log large₂.sc.b + sig ch.G) := by
        have h4 : sig ch.G ≤ D.R.f * (Real.log large₂.sc.b + sig ch.G) := by nlinarith
        calc C * sig ch.G ≤ C * (D.R.f * (Real.log large₂.sc.b + sig ch.G)) := mul_le_mul_of_nonneg_left h4 hC0
          _ = _ := by ring
      linarith
    have h5 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ large₂.sc.b))
    calc 2 * K * sig ch.G = 2 * K0 * sig ch.G * (M * large₂.sc.b) := by rw [hK]; ring
      _ ≤ C * D.R.f * (Real.log large₂.sc.b + sig ch.G) * (M * large₂.sc.b) := h5
      _ = D.R.m * bOne ch.G C large₂.sc.b := by rw [bOne, hM]; ring
  refine ⟨dlD ch.G K, loss_mono (loss_dlD ch.G hK') hbound, fun t w hAw Φ β hβ x y => ?_⟩
  have key : ∀ v : locPl ch.G t, LossLe w ((ch.S.term t Φ β v).datum (ch.S.colAt t v x) (ch.S.rowAt t v y))
      (K * (cosExp ch.G v : ℝ) * (vw w ((resCard (Kw (v : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) := by
    intro v
    have hcase := away_cases ch.G hAw v.2
    set e : ℝ := (cosExp ch.G v : ℝ) with he
    set q : ℝ := (vw w ((resCard (Kw (v : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ) with hq
    have he0 : 0 ≤ e := by positivity
    have hq0 : 0 ≤ q := by
      rw [hq]; exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w _
    have hX : 0 ≤ M * large₂.sc.b * e * q := mul_nonneg (mul_nonneg (mul_nonneg hM0 (by linarith)) he0) hq0
    set c : ℝ := max c₁ 0 * M * large₂.sc.b * e * q with hc
    have hc0 : 0 ≤ c := by
      have : c = max c₁ 0 * (M * large₂.sc.b * e * q) := by rw [hc]; ring
      rw [this]; exact mul_nonneg (le_max_right _ _) hX
    have h1 : ∀ z, LossLe w (Tflip ch.W ch.S.B t Φ v z) c := fun z => (hA t Φ v v.2 w hcase z).mono (by
      have e1 : c₁ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * large₂.sc.b * e * q = c₁ * (M * large₂.sc.b * e * q) := by rw [hM]; ring
      have e2 : c = max c₁ 0 * (M * large₂.sc.b * e * q) := by rw [hc]; ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
    refine (hB t Φ β hβ v w hcase c hc0 h1 _ _).mono ?_
    have e3 : c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * e * q ≤ max c₂ 0 * M * large₂.sc.b * e * q := by
      have hY : 0 ≤ M * e * q := mul_nonneg (mul_nonneg hM0 he0) hq0
      calc c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * e * q = c₂ * (M * e * q) := by rw [hM]; ring
        _ ≤ max c₂ 0 * (M * e * q) := mul_le_mul_of_nonneg_right (le_max_left _ _) hY
        _ ≤ max c₂ 0 * (M * e * q) * large₂.sc.b := le_mul_of_one_le_right (mul_nonneg (le_max_right _ _) hY) hb
        _ = max c₂ 0 * M * large₂.sc.b * e * q := by ring
    calc c + c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * e * q ≤ c + max c₂ 0 * M * large₂.sc.b * e * q := by linarith
      _ = K * e * q := by rw [hc, hK, hK0]; ring
  have hP := lossLe_prod Finset.univ _ _ fun v _ => key v
  rw [sum_locPl ch.G t K w] at hP
  exact hP

theorem finDatK : GlobalTheory.FunPr.Hypotheses₂ → FinDatK := fun _ => finDatK_of GlobalTheory.T.flips_loss_bounded_at_exceptional_places GlobalTheory.T.movedTensor_unfolding_integral_valuation_loss_bound

end GlobalTheory.FunDat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsSmoothCone
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.MinSys

open Matrix

theorem finite_of_pos {r : ℕ} (G : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hs : ∀ a b, G a b = G b a)
    (hn : ∀ x, 0 ≤ G x x) (hp : ∀ x, x ≠ 0 → 0 < G x x) (B : ℤ) : {x | G x x ≤ B}.Finite := by
  classical
  set S : Matrix (Fin r) (Fin r) ℤ := LinearMap.BilinForm.toMatrix' G with hS
  have hGS : ∀ x, G x x = x ⬝ᵥ S *ᵥ x := fun x => by
    rw [← Matrix.toBilin'_apply', hS, Matrix.toBilin'_toMatrix']
  have hdet : S.det ≠ 0 := by
    intro h
    obtain ⟨z, hz, hSz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    have h1 := hp z hz
    rw [hGS, hSz, dotProduct_zero] at h1
    exact lt_irrefl _ h1
  have hpsd : (S.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    have h := GlobalTheory.Poinc.QWDom.gram_posSemidef G hs hn (fun u => Pi.single u 1)
    convert h using 1
    ext u v
    simp [hS, LinearMap.BilinForm.toMatrix'_apply]
  have hpd : (S.map (Int.cast : ℤ → ℝ)).PosDef := by
    rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← Int.cast_det]
    exact_mod_cast hdet
  obtain ⟨c, hc, hP⟩ := GlobalTheory.Poinc.QWDom.exists_pos_posSemidef_sub_smul_one hpd
  have key : ∀ x : Fin r → ℤ, c * ∑ u, ((x u : ℝ)) ^ 2 ≤ (G x x : ℝ) := by
    intro x
    have h := hP.dotProduct_mulVec_nonneg (fun u => (x u : ℝ))
    simp only [star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg] at h
    have e1 : (fun u => (x u : ℝ)) ⬝ᵥ (S.map (Int.cast : ℤ → ℝ)) *ᵥ (fun u => (x u : ℝ)) = ((x ⬝ᵥ S *ᵥ x : ℤ) : ℝ) := by
      simp [dotProduct, mulVec, Matrix.map_apply]
    have e2 : (fun u => (x u : ℝ)) ⬝ᵥ (c • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ (fun u => (x u : ℝ)) =
        c * ∑ u, ((x u : ℝ)) ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Matrix.one_apply, Finset.mul_sum, sq]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, e2] at h
    rw [hGS]
    exact h
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (B : ℝ) / c ≤ M := exists_nat_ge _
  rw [div_le_iff₀ hc] at hM
  refine (Set.Finite.pi' (fun _ : Fin r => Set.finite_Icc (-(M : ℤ)) M)).subset fun x hx => ?_
  intro u
  have hxB : (G x x : ℝ) ≤ B := by exact_mod_cast hx
  have h1 : ((x u : ℝ)) ^ 2 ≤ ∑ v, ((x v : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun v => ((x v : ℝ)) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ u)
  have h2 : c * ((x u : ℝ)) ^ 2 ≤ c * M := by
    have := (mul_le_mul_of_nonneg_left h1 hc.le).trans ((key x).trans hxB)
    linarith
  have h3 : ((x u : ℝ)) ^ 2 ≤ M := le_of_mul_le_mul_left h2 hc
  have h4 : (x u) ^ 2 ≤ (M : ℤ) := by exact_mod_cast h3
  have h5 := Int.le_self_sq (x u)
  have h6 := Int.le_self_sq (-(x u))
  rw [neg_sq] at h6
  exact ⟨by linarith, by linarith⟩

theorem qW_sum_nsmul {s m : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (cf : Fin m → ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (y : Fin s → X) :
    qW W (∑ j, cf j • γ j) y = ∑ j, (cf j : ℤ) * qW W (γ j) y := by
  simp only [qW, LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem qW_nsmul {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (k : ℕ)
    (b : LinearMap.BilinForm ℤ X) (y : Fin s → X) : qW W (k • b) y = (k : ℤ) * qW W b y := by
  simp only [qW, LinearMap.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

theorem finite_minimiser_systems : ∀ (φ : InvFun ℤ), ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)), IsCone id φ γ → (∀ x, x ≠ 0 → 0 < ∑ j, γ j x x) → ∃ Sμ : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (k : ℕ) (cf : Fin m → ℕ), 0 < k → (∀ j, 0 < cf j) → k • b = ∑ j, cf j • γ j → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) → μ ∈ Sμ := by
  intro φ W hW N _ _ r m γ hC hdef
  classical
  obtain ⟨c0, hc0, hge⟩ := GlobalTheory.Poinc.QWDom.qW_ge 8 W hW
  have hsym : ∀ j a b, γ j a b = γ j b a := fun j => (hC.mem j).1
  have hnn : ∀ j y, 0 ≤ γ j y y := hC.nonneg
  have hq0 : ∀ j (α : Fin 8 → Fin r → ℤ), 0 ≤ qW W (γ j) α := fun j α => by
    have h := hge (Fin r → ℤ) (γ j) (hsym j) (hnn j) α
    have h1 : (0 : ℝ) ≤ c0 * ((∑ u, γ j (α u) (α u) : ℤ) : ℝ) :=
      mul_nonneg hc0.le (by exact_mod_cast Finset.sum_nonneg fun u _ => hnn j (α u))
    exact_mod_cast h1.trans h
  set G : LinearMap.BilinForm ℤ (Fin r → ℤ) := ∑ j, γ j with hG
  have hGapp : ∀ a b, G a b = ∑ j, γ j a b := fun a b => by simp [hG, LinearMap.sum_apply]
  have hGsym : ∀ a b, G a b = G b a := fun a b => by simp only [hGapp, hsym _ a b]
  have hGnn : ∀ y, 0 ≤ G y y := fun y => by rw [hGapp]; exact Finset.sum_nonneg fun j _ => hnn j y
  have hGpos : ∀ x, x ≠ 0 → 0 < G x x := fun x hx => by rw [hGapp]; exact hdef x hx
  have hGq : ∀ α, qW W G α = ∑ j, qW W (γ j) α := fun α => by
    have := qW_sum_nsmul W (fun _ => 1) γ α
    simpa [hG] using this
  have hfinG : ∀ B : ℤ, {α : Fin 8 → Fin r → ℤ | qW W G α ≤ B}.Finite := by
    intro B
    obtain ⟨M, hM⟩ : ∃ M : ℕ, (B : ℝ) / c0 ≤ M := exists_nat_ge _
    rw [div_le_iff₀ hc0] at hM
    refine (Set.Finite.pi' fun _ : Fin 8 => finite_of_pos G hGsym hGnn hGpos M).subset fun α hα u => ?_
    have h := hge (Fin r → ℤ) G hGsym hGnn α
    have h1 : G (α u) (α u) ≤ ∑ v, G (α v) (α v) :=
      Finset.single_le_sum (f := fun v => G (α v) (α v)) (fun v _ => hGnn (α v)) (Finset.mem_univ u)
    have hα' : (qW W G α : ℝ) ≤ B := by exact_mod_cast hα
    have h1' : ((G (α u) (α u) : ℤ) : ℝ) ≤ ((∑ v, G (α v) (α v) : ℤ) : ℝ) := by exact_mod_cast h1
    have h2 : c0 * (G (α u) (α u) : ℝ) ≤ c0 * M := by
      have := (mul_le_mul_of_nonneg_left h1' hc0.le).trans (h.trans hα')
      linarith
    have h3 : (G (α u) (α u) : ℝ) ≤ M := le_of_mul_le_mul_left h2 hc0
    show G (α u) (α u) ≤ ((M : ℕ) : ℤ)
    exact_mod_cast h3
  let T : (Fin 8 → Fin r → ZMod N) → Type := fun c =>
    {α : Fin 8 → Fin r → ℤ // ∀ u i, ((α u i : ℤ) : ZMod N) = c u i}
  have hD : ∀ c, ∃ F : Finset (T c), ∀ α : T c, ∃ β ∈ F,
      (fun j => (qW W (γ j) β.1).toNat) ≤ (fun j => (qW W (γ j) α.1).toNat) :=
    fun c => GlobalTheory.dickson_finite_below_every m (fun (α : T c) j => (qW W (γ j) α.1).toNat)
  choose F hF using hD
  let Bd : (Fin 8 → Fin r → ZMod N) → ℤ := fun c => ∑ β ∈ F c, qW W G β.1
  have hfin : {μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ) | ∀ c, μ c ∈ {α | qW W G α ≤ Bd c}}.Finite :=
    Set.Finite.pi' fun c => hfinG (Bd c)
  refine ⟨hfin.toFinset, fun b k cf hk hcf hkb μ hμ hmin => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  intro c
  obtain ⟨β, hβF, hβ⟩ := hF c ⟨μ c, hμ c⟩
  have hle : ∀ j, qW W (γ j) β.1 ≤ qW W (γ j) (μ c) := fun j => by
    have h1 : (qW W (γ j) β.1).toNat ≤ (qW W (γ j) (μ c)).toNat := hβ j
    have := hq0 j β.1
    have := hq0 j (μ c)
    omega
  have hkq : ∀ α, (k : ℤ) * qW W b α = ∑ j, (cf j : ℤ) * qW W (γ j) α := fun α => by
    rw [← qW_nsmul, hkb, qW_sum_nsmul]
  have h2 : ∑ j, (cf j : ℤ) * qW W (γ j) (μ c) ≤ ∑ j, (cf j : ℤ) * qW W (γ j) β.1 := by
    rw [← hkq, ← hkq]
    exact mul_le_mul_of_nonneg_left (hmin c β.1 β.2) (by positivity)
  have h3 : ∀ j, qW W (γ j) (μ c) - qW W (γ j) β.1 ≤
      (cf j : ℤ) * qW W (γ j) (μ c) - (cf j : ℤ) * qW W (γ j) β.1 := fun j => by
    have h4 := hle j
    have h5 : (1 : ℤ) ≤ cf j := by exact_mod_cast hcf j
    nlinarith
  have h6 : ∑ j, qW W (γ j) (μ c) ≤ ∑ j, qW W (γ j) β.1 := by
    have h7 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h3 j
    simp only [Finset.sum_sub_distrib] at h7
    linarith
  have h8 : qW W G β.1 ≤ Bd c :=
    Finset.single_le_sum (f := fun β : T c => qW W G β.1)
      (fun β _ => by rw [hGq]; exact Finset.sum_nonneg fun j _ => hq0 j β.1) hβF
  rw [hGq] at h8 ⊢
  linarith

end GlobalTheory.Poinc.MinSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetsInAffineOpenAbelianSchemeRelAmpleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteSetsInAffineOpen_abelianScheme_relAmple : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → FinAff A.left := by
  first | exact @GlobalTheory.DualCon.FinAffNoeth.finAff_of_relAmple_noetherian | exact GlobalTheory.DualCon.FinAffNoeth.finAff_of_relAmple_noetherian | (intros; apply GlobalTheory.DualCon.FinAffNoeth.finAff_of_relAmple_noetherian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTorsionAndDescentAbelianVarietyAlgClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ), (n : k) ≠ 0 → Finite {g : 𝟙_ (Over (Sp k)) ⟶ A // g ^ n = 1} ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Sp k) (g : Over.mk x ⟶ A), g ^ n = 1 → ∃ g₀ : 𝟙_ (Over (Sp k)) ⟶ A, g₀ ^ n = 1 ∧ g = toUnit (Over.mk x) ≫ g₀ := by
  first | (exact @GlobalTheory.AbTorsionGeomDescent.finite_torsion_and_descent) | (exact GlobalTheory.AbTorsionGeomDescent.finite_torsion_and_descent) | (intros; apply GlobalTheory.AbTorsionGeomDescent.finite_torsion_and_descent  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomHarrisTaylorOrderMorita
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTRho

theorem span_one_tmul (k : Type) [Field k] (C O : Type) [CommRing C] [Ring O] [Algebra C O] [Algebra C k] :
    Submodule.span k (Set.range fun o : O => (1 : k) ⊗ₜ[C] o) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top
  | exact _root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top
  | (apply _root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top ..)

theorem finrank_homO_morita : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] [IsAlgClosed k], (∀ n : ℕ, n.Coprime p → (n : k) ≠ 0) → ∀ (χ : 𝓞 D.F →+* k) (X Y : Type) [AddCommGroup X] [Module k X] [FiniteDimensional k X] [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y] (σX : D.O →+* Module.End k X) (σY : D.O →+* Module.End k Y), (∀ c, σX (algebraMap (𝓞 D.F) D.O c) = χ c • 1) → (∀ c, σY (algebraMap (𝓞 D.F) D.O c) = χ c • 1) → D.m ^ 2 * Module.finrank k (GlobalTheory.HTRho.homO σX σY) = Module.finrank k X * Module.finrank k Y := by
  intro p _ D k _ _ hk χ X Y _ _ _ _ _ _ σX σY hX hY
  letI : Algebra (𝓞 D.F) k := χ.toAlgebra
  have hiso : Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
    obtain ⟨q, hq⟩ := CharP.exists k
    rcases CharP.char_is_prime_or_zero k q with hq' | rfl
    · by_cases hqp : q = p
      · subst hqp; exact GlobalTheory.T.harrisTaylor_tensor_order_algEquiv_matrix_charP q D k
      · exfalso
        exact hk q ((Nat.coprime_primes hq' (Fact.out)).2 hqp) (CharP.cast_eq_zero k q)
    · haveI : CharZero k := CharP.charP_to_charZero k
      exact GlobalTheory.T.harrisTaylor_tensor_order_algEquiv_matrix_charZero p D k
  obtain ⟨e⟩ := hiso
  obtain ⟨ρX, hρX⟩ := GlobalTheory.T.exists_action_factor_through_tensor_character k (𝓞 D.F) D.O _ e X σX hX
  obtain ⟨ρY, hρY⟩ := GlobalTheory.T.exists_action_factor_through_tensor_character k (𝓞 D.F) D.O _ e Y σY hY
  have heq : GlobalTheory.HTRho.homO σX σY = GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom := by
    ext T
    rw [GlobalTheory.HTRho.mem_homO, GlobalTheory.HTRho.mem_homO]
    constructor
    · intro h b
      have hb : b ∈ Submodule.span k (Set.range fun o : D.O => e ((1 : k) ⊗ₜ[𝓞 D.F] o)) := by
        have hr : (Set.range fun o : D.O => e ((1 : k) ⊗ₜ[𝓞 D.F] o)) =
            (e.toLinearMap) '' Set.range (fun o : D.O => (1 : k) ⊗ₜ[𝓞 D.F] o) := by
          rw [← Set.range_comp]; rfl
        rw [hr, Submodule.span_image, span_one_tmul, Submodule.map_top,
          LinearMap.range_eq_top.2 e.surjective]
        trivial
      induction hb using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨o, rfl⟩ := hz
        intro x; simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hρX, hρY]; exact h o x
      | zero => intro x; simp
      | add a b _ _ ha hb =>
        intro x
        have h1 := ha x
        have h2 := hb x
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, LinearMap.add_apply] at h1 h2 ⊢
        rw [h1, h2]
      | smul c a _ ha =>
        intro x
        have h1 := ha x
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_smul, LinearMap.smul_apply] at h1 ⊢
        rw [h1]
    · intro h o x
      have := h (e (1 ⊗ₜ o)) x
      simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hρX, hρY] using this
  rw [heq]
  exact GlobalTheory.T.sq_mul_finrank_matrixAlgebra_hom_eq_finrank_mul k D.m X Y ρX ρY

end GlobalTheory.HTRho
end

