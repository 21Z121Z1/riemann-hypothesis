import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DenBound
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0004
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ConstantLeRpowOfThreeLe
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DvdCoeffsOfMemSpanDistinguished
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0012
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LenTLeThree
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCaseAOfP9

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLenTwoThickLetters
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem arc_len_two_thick_letters [NeZero n] {b w S η : ℕ} {up : ZMod n → Bool} {size : ZMod n → ℕ} (c : ZMod n)
    (hlen : (arcOf b w S η up size).len c = 2) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
  set s := {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} with hs
  have hlen' : sInf s = 2 := hlen
  have hne : s.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Nat.sInf_empty] at hlen'
    norm_num at hlen'
  have h2 : 2 ∈ s := hlen' ▸ Nat.sInf_mem hne
  have h1 : 1 ∉ s := fun h => by
    have := Nat.sInf_le h
    omega
  constructor
  · by_contra hT
    apply h1
    refine ⟨le_rfl, ?_⟩
    simpa using hT
  · have h22 := h2.2
    convert h22 using 2
    push_cast
    ring

theorem lifts_scale (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d) {f : W.EE}
    {e k : ℕ} (h : LiftsAt W A F c bb sol k₀ (lE W k * f) e) : LiftsAt W A F c bb sol k₀ f (e + k) := by
  obtain ⟨w₁, z, h1, h2, h3, h4, h5⟩ := h
  refine ⟨w₁, z, h1, h2, h3, h4, ?_⟩
  have he : lE W (e + k) * f = lE W e * (lE W k * f) := by
    simp only [lE, pow_add, mul_assoc]
  have hfun : (fun kk => if kk = k₀ then lE W (e + k) * f else 0) =
      (fun kk => if kk = k₀ then lE W e * (lE W k * f) else 0) := funext fun kk => by rw [he]
  rw [hfun]
  exact h5

theorem lE_alg (W : LocWach PD LL O v n) (k : ℕ) :
    lE W k = algebraMap (LetA O n) W.EE (lA W ^ k) := by
  simp only [lE, lA, map_pow, map_natCast]

theorem algO (W : LocWach PD LL O v n) (x : O) :
    algebraMap O W.EE x = algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) x) := IsScalarTower.algebraMap_apply O (LetA O n) W.EE x

theorem den_step [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (W : LocWach PD LL O v n) (Br : Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge W) (c : ZMod n) (y Bq κ : ℕ)
    (hy : 1 ≤ y) (hBq : 1 ≤ Bq) (f : W.EE) (x : O)
    (hf : InFr W c 1 (ps W 1 ^ y) f)
    (hx : InFr W c (ps W 0 ^ Bq) (ps W 1 ^ y)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    ∃ (de : ℕ) (x' : O), de ≤ ⌈max 0 ((y : ℝ) - Bq / PD.p + 2 + Real.logb PD.p y)⌉₊ ∧
      (PD.p * y < Bq → de = 0) ∧
      InFr W c 1 (ps W 1 ^ y) (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') ∧
      InFr W c (ps W 0 ^ Bq) (ps W 1 ^ y)
        (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') := by
  haveI := Fact.mk PD.hp
  set P := Br.P
  have hp0 : P.p 0 = X := rfl
  have hps : ∀ s k, ps W s ^ k = Br.cst (P.p s ^ k) := by
    intro s k; rw [Br.cst_pow, Br.ps_eq]
  have h1 : (1 : LetA O n) = Br.cst 1 := Br.cst_one.symm
  rw [hps, h1] at hf
  rw [hps, hps, hp0] at hx
  obtain ⟨U₁, U₂, hU⟩ := Br.inFr_const c hf hx
  obtain ⟨hd1, hd2⟩ := den_bound P y Bq κ hy hBq x U₁ U₂ hU
  set D := ⌈max 0 ((y : ℝ) - Bq / PD.p + 2 + Real.logb PD.p y)⌉₊ with hD
  set de : ℕ := if PD.p * y < Bq then 0 else min D κ with hde
  have hxd : ((PD.p : ℕ) : O) ^ (κ - de) ∣ x := by
    rw [hde]; split_ifs with hlt
    · simpa using hd2 hlt
    · have : κ - min D κ = κ - D := by omega
      rw [this]; exact hd1
  have hdeκ : de ≤ κ := by rw [hde]; split_ifs <;> omega
  obtain ⟨x', hx'⟩ := hxd
  refine ⟨de, x', ?_, ?_, ?_⟩
  · rw [hde]; split_ifs <;> omega
  · intro hlt; rw [hde, if_pos hlt]
  obtain ⟨u₁, hu₁, hfu⟩ := hf
  obtain ⟨F₁, hF₁⟩ := Br.range u₁ hu₁ c
  set G : PowerSeries O := C ((PD.p : ℕ) : O) ^ de * F₁ - P.p 1 ^ y * C x' with hG
  have hletu : (letE c : LetA O n) * u₁ = letE c * Br.cst F₁ := by
    funext i
    by_cases hi : i = c
    · subst hi; simp [letE, hF₁, Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst]
    · simp [letE, Pi.single_apply, hi]
  have e1 : (letE c : LetA O n) * Br.cst G =
      lA W ^ de * (letE c * Br.cst 1 * u₁) - Br.cst (P.p 1 ^ y) * (letE c * algebraMap O (LetA O n) x') := by
    rw [Br.cst_one, mul_one, hletu, hG, Br.lA_eq, ← Br.cst_pow, ← Br.cst_C]
    funext i
    simp only [Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst, Pi.mul_apply, Pi.sub_apply, map_sub, map_mul, map_pow]
    ring
  have hkey : algebraMap (LetA O n) W.EE (Br.cst (P.p 1 ^ y)) *
      (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') =
      algebraMap (LetA O n) W.EE (letE c * Br.cst G) := by
    rw [algO, e1]
    simp only [map_sub, map_mul] at hfu ⊢
    rw [← lE_alg]
    linear_combination (lE W de) * hfu
  refine ⟨⟨Br.cst G, Br.cst_mem G, ?_⟩, ?_⟩
  · rw [hps 1 y, hkey, mul_one]
  have hscale : lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x =
      lE W (κ - de) * (lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') := by
    have hj' : lE W κ = lE W (κ - de) * lE W de := by
      unfold lE; rw [← pow_add, Nat.sub_add_cancel hdeκ]
    rw [hx', map_mul, map_pow, map_natCast, hj']
    unfold lE
    ring
  obtain ⟨u₂, hu₂, hxu⟩ := hx
  have hxu2 : algebraMap (LetA O n) W.EE (lA W ^ (κ - de) * (letE c * Br.cst G)) =
      algebraMap (LetA O n) W.EE (letE c * Br.cst (X ^ Bq) * u₂) := by
    rw [map_mul, ← hkey, ← lE_alg, ← hxu, hscale]
    ring
  have hxc := congrFun (W.EE_inj hxu2) c
  obtain ⟨F₂, hF₂⟩ := Br.range u₂ hu₂ c
  have hιeq : Br.ι (C ((PD.p : ℕ) : O) ^ (κ - de) * G) = Br.ι (X ^ Bq * F₂) := by
    have e2 : (lA W ^ (κ - de) * (letE c * Br.cst G) : LetA O n) c = Br.ι (C ((PD.p : ℕ) : O) ^ (κ - de) * G) := by
      rw [Br.lA_eq, ← Br.cst_pow]
      simp [letE, Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst, map_mul]
    have e3 : (letE c * Br.cst (X ^ Bq) * u₂ : LetA O n) c = Br.ι (X ^ Bq * F₂) := by
      simp [letE, Formalism.MainNotions.N.FrobeniusPowerSeries.PhiBridge.cst, hF₂, map_mul]
    rw [← e2, ← e3, hxc]
  have hGB := Br.inj hιeq
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨u, hu⟩ := l_eq_unit_mul_pow hϖ P.hl0
  have hmem : C ϖ ^ (eO (O := O) PD.p * (κ - de)) * (C ((↑u : O) ^ (κ - de)) * G) ∈
      Ideal.span {(X : O⟦X⟧) ^ Bq} := by
    have : C ϖ ^ (eO (O := O) PD.p * (κ - de)) * (C ((↑u : O) ^ (κ - de)) * G) = X ^ Bq * F₂ := by
      rw [← hGB, hu]
      simp only [map_mul, map_pow, mul_pow, ← pow_mul]
      ring
    rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hmem2 := Cont.mem_of_pow_mul_mem hϖ (ContPA.dist_X_pow (O := O) Bq).1 _ _ hmem
  obtain ⟨U', hU'⟩ := Ideal.mem_span_singleton'.mp hmem2
  have hone : (C ((↑(u⁻¹) : O) ^ (κ - de)) : O⟦X⟧) * C ((↑u : O) ^ (κ - de)) = 1 := by
    rw [← map_mul, ← mul_pow, Units.inv_mul, one_pow, map_one]
  have hG2 : G = X ^ Bq * (C ((↑(u⁻¹) : O) ^ (κ - de)) * U') := by
    linear_combination (-G) * hone + (-(C ((↑(u⁻¹) : O) ^ (κ - de)) : O⟦X⟧)) * hU'
  refine ⟨Br.cst (C ((↑(u⁻¹) : O) ^ (κ - de)) * U'), Br.cst_mem _, ?_⟩
  rw [hps 1 y, hps 0 Bq, hp0, hkey, hG2, Br.cst_mul, mul_assoc]

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeLeValuationConstantTerm
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_three_le_valuation_constant_term [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))
    (f₂ : W.EE) (hf₂ : InFr W c (ps W 2 ^ (size (c - 2) + S)) (ps W 1 ^ size (c - 1)) f₂) (κ₀ : ℕ) (X₀ : O) (hX₀ : InFr W c (ps W 0 ^ (size c + S)) (ps W 1 ^ size (c - 1))
      (lE W κ₀ * f₂ - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₀)) :
    ∀ r : ℚ, v (algebraMap O LL X₀) = ((r : ℚ) : WithTop ℚ) →
      ((size (c - 2) : ℝ) + S - size (c - 1) + ((size c + S : ℕ) : ℝ) / PD.p - ((size c + S : ℕ) : ℝ) / (PD.p : ℝ) ^ 2 - 2 -
        Real.logb PD.p (2 * (((arcOf b w S η up size).h : ℕ) : ℝ))) + κ₀ ≤ (r : ℝ) := by
  intro r hr
  classical
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨hcr, -⟩ := hW₁
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T₁ hcr hO hinj
  obtain ⟨hl11, hSet, -, hη20, hS20, -⟩ := hB
  obtain ⟨-, -, hsz, -⟩ := hSet

  have hthick : ∀ d : ℕ, 1 ≤ d → d < 3 →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1) := by
    intro d hd1 hd3
    by_contra hnt
    have hmem : d ∈ {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} :=
      ⟨hd1, hnt⟩
    have hle := Nat.sInf_le hmem
    have hlen' : (arcOf b w S η up size).len c =
        sInf {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := rfl
    rw [hlen'] at hlen
    omega
  have ht1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    have h := hthick 2 (by norm_num) (by norm_num)
    have e2 : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
    rwa [e2] at h
  have ht0 : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c := by
    have h := hthick 1 le_rfl (by norm_num)
    have e1 : c - ((1 : ℕ) : ZMod n) + 1 = c := by push_cast; ring
    rwa [e1] at h
  have hh : (arcOf b w S η up size).h = b + η + S := by
    show Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = _
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
    rw [if_pos ⟨c - 1, ht1⟩]
  have hη1 := hsz (c - 1)
  have hη0 := hsz c
  have hB1 : 1 ≤ size c + S := by omega
  have hb1 : 1 ≤ size (c - 1) := by omega
  have hB11 : size c + S ≤ 11 * size (c - 1) := by
    obtain ⟨h1, -⟩ := ht1
    obtain ⟨-, h2⟩ := ht0
    omega

  simp only [Br.ps_eq, ← Br.cst_pow] at hf₂ hX₀
  obtain ⟨U₁, U₂, hU⟩ := Br.inFr_const c hf₂ hX₀
  have hp0 : Br.P.p 0 = PowerSeries.X := rfl
  rw [hp0] at hU

  by_cases hx0 : X₀ = 0
  · rw [hx0, map_zero, AddValuation.map_zero] at hr
    exact (WithTop.top_ne_coe hr).elim
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨nn, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨vl, hvl⟩ := l_eq_unit_mul_pow hϖ Br.P.hl0
  obtain ⟨e, he⟩ : ∃ e, e = eO (O := O) PD.p := ⟨_, rfl⟩
  rw [← he] at hvl

  have hunit : ∀ y : Oˣ, v (algebraMap O LL (y : O)) = 0 := by
    intro y
    have h1 := hO y
    have h2 := hO (↑y⁻¹ : O)
    have h3 : v (algebraMap O LL (y : O)) + v (algebraMap O LL (↑y⁻¹ : O)) = 0 := by
      rw [← AddValuation.map_mul, ← _root_.map_mul, Units.mul_inv, _root_.map_one,
        AddValuation.map_one]
    exact le_antisymm (le_of_le_of_eq (le_add_of_nonneg_right h2) h3) h1
  have hϖ0 : v (algebraMap O LL ϖ) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    intro h
    exact hϖ.ne_zero (hinj (by rw [h, _root_.map_zero]))
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hϖ0
  have hvl1 : (((e : ℚ) * d : ℚ) : WithTop ℚ) = 1 := by
    have h := W.v_l
    rw [← map_natCast (algebraMap O LL), hvl, _root_.map_mul, _root_.map_pow,
      AddValuation.map_mul, AddValuation.map_pow, hunit, ← hd, zero_add] at h
    rw [← h, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have hEd : (e : ℚ) * d = 1 := by exact_mod_cast hvl1
  have hrv : (r : ℚ) = nn * d := by
    have h := hr
    rw [hxu, _root_.map_mul, _root_.map_pow, AddValuation.map_mul, AddValuation.map_pow, hunit,
      ← hd, zero_add, ← WithTop.coe_nsmul, nsmul_eq_mul] at h
    exact_mod_cast h.symm

  obtain ⟨k₃, hk₃⟩ : ∃ k : ℕ, k = ⌈(e : ℝ) * (((size (c - 2) + S : ℕ) : ℝ) -
      ((size c + S : ℕ) : ℝ) / ((PD.p : ℕ) : ℝ) ^ 2)⌉₊ := ⟨_, rfl⟩
  have hc3 := Br.P.c3a hϖ (size (c - 2) + S) (size c + S) hB1 k₃ (by rw [← he]; exact hk₃.le)
  obtain ⟨α₁, β₁, hαβ⟩ := Ideal.mem_span_pair.mp hc3
  have hF1 : (e : ℝ) * (((size (c - 2) + S : ℕ) : ℝ) -
      ((size c + S : ℕ) : ℝ) / ((PD.p : ℕ) : ℝ) ^ 2) ≤ k₃ := by
    rw [hk₃]; exact Nat.le_ceil _

  have hc2 := Br.P.constant_le_rpow_of_three_le hϖ (size c + S) (size (c - 1)) hB1 hb1
  rw [← he] at hc2
  have hL : (11 : ℝ) ≤ ((PD.p : ℕ) : ℝ) := by exact_mod_cast hl11
  have hL1 : (1 : ℝ) < ((PD.p : ℕ) : ℝ) := by linarith
  have hy1 : (1 : ℝ) ≤ ((size (c - 1) : ℕ) : ℝ) := by exact_mod_cast hb1
  have hBl : ((size c + S : ℕ) : ℝ) / ((PD.p : ℕ) : ℝ) ≤ ((size (c - 1) : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    have : ((size c + S : ℕ) : ℝ) ≤ 11 * ((size (c - 1) : ℕ) : ℝ) := by exact_mod_cast hB11
    nlinarith
  have hlog0 : 0 ≤ Real.logb ((PD.p : ℕ) : ℝ) ((size (c - 1) : ℕ) : ℝ) := Real.logb_nonneg hL1 hy1
  have hbr : 0 ≤ ((size (c - 1) : ℕ) : ℝ) - ((size c + S : ℕ) : ℝ) / ((PD.p : ℕ) : ℝ) + 2 +
      Real.logb ((PD.p : ℕ) : ℝ) ((size (c - 1) : ℕ) : ℝ) := by linarith
  rw [max_eq_right hbr] at hc2
  have hE0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hF2 : ((e * κ₀ + k₃ : ℕ) : ℝ) - nn ≤ (e : ℝ) * (((size (c - 1) : ℕ) : ℝ) -
      ((size c + S : ℕ) : ℝ) / ((PD.p : ℕ) : ℝ) + 2 +
      Real.logb ((PD.p : ℕ) : ℝ) ((size (c - 1) : ℕ) : ℝ)) := by
    by_cases hlt : nn < e * κ₀ + k₃
    · obtain ⟨m, hm⟩ : ∃ m, e * κ₀ + k₃ = nn + m := ⟨e * κ₀ + k₃ - nn, by omega⟩
      have hpw : (PowerSeries.C ϖ) ^ (e * κ₀) * (PowerSeries.C ϖ) ^ k₃ =
          (PowerSeries.C ϖ) ^ nn * (PowerSeries.C ϖ) ^ m := by
        rw [← pow_add, ← pow_add, hm]
      rw [hvl, hxu, _root_.map_mul, _root_.map_mul, _root_.map_pow, _root_.map_pow, mul_pow,
        ← pow_mul, ← hαβ] at hU
      have hdist := (ContPA.dist_X_pow (O := O) (size c + S)).1
      have hdvd := ContM_cancel_unif hϖ hdist nn
        (x := PowerSeries.C (u : O) * Br.P.p 1 ^ size (c - 1) -
          (PowerSeries.C ϖ) ^ m * (PowerSeries.C (vl : O) ^ κ₀ * α₁ * U₁))
        (a := PowerSeries.C (vl : O) ^ κ₀ * (PowerSeries.C ϖ) ^ (e * κ₀) * β₁ * U₁ - U₂)
        (by linear_combination hU + PowerSeries.C (vl : O) ^ κ₀ * α₁ * U₁ * hpw)
      obtain ⟨γ, hγ⟩ := hdvd
      have hu1 : PowerSeries.C (↑u⁻¹ : O) * PowerSeries.C (u : O) = 1 := by
        rw [← _root_.map_mul, Units.inv_mul, _root_.map_one]
      have hmem : Br.P.p 1 ^ size (c - 1) ∈
          Ideal.span {PowerSeries.C ϖ ^ m, (PowerSeries.X : PowerSeries O) ^ (size c + S)} := by
        refine Ideal.mem_span_pair.mpr ⟨PowerSeries.C (↑u⁻¹ : O) *
          (PowerSeries.C (vl : O) ^ κ₀ * α₁ * U₁), PowerSeries.C (↑u⁻¹ : O) * γ, ?_⟩
        linear_combination (-PowerSeries.C (↑u⁻¹ : O)) * hγ + Br.P.p 1 ^ size (c - 1) * hu1
      have hcont := (Cont.mem_iff_le ϖ _ _ m).mp hmem
      rw [← ENat.natCast_toNat hc2.1] at hcont
      have hmle : (m : ℝ) ≤
          ((cont ϖ (PowerSeries.X ^ (size c + S)) (Br.P.p 1 ^ size (c - 1))).toNat : ℝ) := by
        exact_mod_cast hcont
      have : ((e * κ₀ + k₃ : ℕ) : ℝ) - nn = m := by rw [hm]; push_cast; ring
      rw [this]
      exact hmle.trans hc2.2
    · have : ((e * κ₀ + k₃ : ℕ) : ℝ) - nn ≤ 0 := by
        have : e * κ₀ + k₃ ≤ nn := by omega
        have : ((e * κ₀ + k₃ : ℕ) : ℝ) ≤ nn := by exact_mod_cast this
        linarith
      exact this.trans (mul_nonneg hE0 hbr)

  rw [hh]
  have hlog : Real.logb ((PD.p : ℕ) : ℝ) ((size (c - 1) : ℕ) : ℝ) ≤
      Real.logb ((PD.p : ℕ) : ℝ) (2 * ((b + η + S : ℕ) : ℝ)) := by
    have h2h : (1 : ℝ) ≤ ((b + η + S : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ b + η + S by obtain ⟨-, h2⟩ := ht1; omega)
    apply (Real.logb_le_logb hL1 (by linarith) (by linarith)).mpr
    obtain ⟨-, h2⟩ := ht1
    have : size (c - 1) ≤ 2 * (b + η + S) := by omega
    exact_mod_cast this
  have h3 := mul_le_mul_of_nonneg_left hlog hE0
  have hEd' : (e : ℝ) * (d : ℝ) = 1 := by exact_mod_cast hEd
  have hrv' : ((r : ℚ) : ℝ) = (nn : ℝ) * (d : ℝ) := by exact_mod_cast hrv
  have hd0 : (0 : ℝ) < d := by
    rcases lt_or_ge 0 (d : ℝ) with h | h
    · exact h
    · nlinarith
  push_cast at hF1 hF2 h3 ⊢
  have hmain : (e : ℝ) * ((size (c - 2) : ℝ) + S - size (c - 1) + ((size c : ℝ) + S) / PD.p -
      ((size c : ℝ) + S) / (PD.p : ℝ) ^ 2 - 2 - Real.logb PD.p (2 * ((b : ℝ) + η + S)) + κ₀) ≤ nn := by
    linear_combination hF1 + hF2 + h3
  rw [hrv']
  calc _ = ((e : ℝ) * ((size (c - 2) : ℝ) + S - size (c - 1) + ((size c : ℝ) + S) / PD.p -
      ((size c : ℝ) + S) / (PD.p : ℝ) ^ 2 - 2 - Real.logb PD.p (2 * ((b : ℝ) + η + S)) + κ₀)) * d := by
        rw [mul_comm (e : ℝ), mul_assoc, hEd', mul_one]
    _ ≤ (nn : ℝ) * d := mul_le_mul_of_nonneg_right hmain hd0.le

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcSetupTheorem
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_setup_theorem [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR) (hDc : Formalism.MainNotions.TruncatedSeriesCountingBounds.DcrisExactStrict PD LL)
    (hJ21 : ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a)
    (hJmp : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O) :
    let A := arcOf b w S η up size
    A.OK ∧ Win W A T₁ ∧ Win W A T₂ ∧ (∑ c ∈ A.cuts, A.len c) = n ∧
    (Alt b η up size → ∀ c ∈ A.cuts, A.len c ≤ 3) ∧
    (∀ R : ℕ, 1 ≤ R → One b η R up size → ∀ c ∈ A.cuts, A.len c ≤ R) ∧
    (A.σ PD.p : ℝ) ≤ 3 * Sg PD.p b w S η size ∧
    ∃ rr : ℕ, (rr : ℝ) ≤ 3 * Sg PD.p b w S η size ∧
      (∀ c ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr)) ∧
      ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L) (cc : G → T₂.V),
        cc ∈ latticeCocycles T₂.L → IsCrys PD Y.ρ → Formalism.MainNotions.LiftingTheory.IsExtOf W ι π cc →
          Win W A Y ∧ ∀ c ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W π c (Formalism.MainNotions.LiftingTheory.lp W rr) :=
  SetupA.arcSetup_of W hcase F hB CR hWR hJmp hJ21

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SaturationFractionModule
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

variable (W : LocWach PD LL O v n)

theorem gamma_pi0_eq_pi0_mul_one_add_unit_mul_q (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    ∃ κ ∈ W.AΔ, IsUnit κ ∧ W.γA W.gam W.π₀ = W.π₀ * (1 + κ * qA W) := by
  obtain ⟨w, hw, h⟩ := GS.gamma_pi0_eq_pi0_mul_unit (GS.ringData_of_caseA_of_p9 W hcase hP9)
  exact ⟨w, hw, w.isUnit, h⟩

theorem gamma_sub_self_mem_pi0_q (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (f : LetA O n) (hf : f ∈ W.AΔ) :
    ∃ g ∈ W.AΔ, W.γA W.gam f - f = W.π₀ * qA W * g :=
  GS.gam_A_core (GS.ringData_of_caseA_of_p9 W hcase hP9) hf

theorem gamma_level_eq_mul (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (s : ℕ) (hs : 1 ≤ s) :
    ∃ g ∈ W.AΔ, W.γA W.gam (ps W s) = ps W s * (1 + W.π₀ * qA W * g) :=
  GS.gam_ps_core (GS.ringData_of_caseA_of_p9 W hcase hP9) s hs

theorem gamma_fraction_in_ideal (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (a : ZMod n) (e : ℕ) (α : ℕ → ℤ)
    (f : W.EE) (hf : InId W a e α f) :
    InId W a e α (W.γE W.gam f) ∧
      InFr W a (W.π₀ * ∏ s ∈ Finset.range e, ps W s ^ (α s).toNat)
        (∏ s ∈ Finset.range e, ps W s ^ (-(α s)).toNat) (W.γE W.gam f - f) :=
  GS.gam_frac_core (GS.ringData_of_caseA_of_p9 W hcase hP9) a e α f hf

theorem saturation_fraction_module (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hSat : SATcore W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (f₁ f₂ f' : LetA O n) (h₁ : f₁ ∈ PiPs W) (h₂ : f₂ ∈ PiPs W) (h' : f' ∈ PiPs W) (x : W.DD T)
    (hx : f' • x ∈ W.NΔ T) (hk : ∃ k : ℕ, InFN W T f₁ (lA W ^ k • (f₂ • x))) :
    InFN W T f₁ (f₂ • x) := by
  have hx' : f' • (f₂ • x) ∈ W.NΔ T := by
    rw [smul_smul, mul_comm, ← smul_smul]
    exact GS.smul_mem_NΔ W T (GS.piPs_mem W h₂) hx
  exact hSat hcase T f₁ f' hT h₁ h' (f₂ • x) hx' hk

theorem saturation_fraction_ring [IsDomain O] [IsDiscreteValuationRing O] (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hinj : Function.Injective (algebraMap O LL)) (f₁ f₂ f' : LetA O n) (h₁ : f₁ ∈ PiPs W) (h₂ : f₂ ∈ PiPs W)
    (h' : f' ∈ PiPs W) (x : LetA O n) (hx : f' * x ∈ W.AΔ)
    (hk : ∃ (k : ℕ) (y : LetA O n), y ∈ W.AΔ ∧ lA W ^ k * (f₂ * x) = f₁ * y) :
    ∃ y ∈ W.AΔ, f₂ * x = f₁ * y := by
  obtain ⟨k, y, hy, hky⟩ := hk
  exact GS.sat_A_core (GS.ringData_of_caseA_of_p9 W hcase hP9) (GS.p_ne_zero W) h₁ hy k hky

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

