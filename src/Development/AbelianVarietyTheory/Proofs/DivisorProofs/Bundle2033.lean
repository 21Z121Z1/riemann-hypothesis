import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0651
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.EmbeddingValuationsAnti
import Development.AutomorphicArithmetic.DivisorFrames.IsIntegralLocalGridTensorOfLevelChar
import Development.AutomorphicArithmetic.DivisorFrames.Bundle0006
import Development.AutomorphicArithmetic.LocalEmbeddings.FlipVal
import Development.AutomorphicArithmetic.LocalEmbeddings.FlipInt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0145
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0959
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlipsLossBoundedAtExceptionalPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

section SlopeTestRemainingChoices

open ValuativeRel UpperTheory.FlipInt UpperTheory.FlipVal

private theorem psi_int {D : D7} {w : Pl D.host.E} {ψ : AddChar (Kw w) Circle} (hc : HasConductor ψ 1) (n : ℕ) (x : Kw w)
    (hx : valuation (Kw w) ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1) : IsIntegral ℤ (ψ x : ℂ) := by
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
  set q := Ideal.absNorm w.asIdeal
  have hq0 : q ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot
  have hq : Valued.v ((q : ℕ) : Kw w) ≤ WithZero.exp (-1 : ℤ) := by
    have hmem : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem w.asIdeal
    have h2 : Valued.v ((q : ℕ) : Kw w) = w.intValuation ((q:ℕ) : 𝓞 D.host.E) := by
      rw [← map_natCast (algebraMap (𝓞 D.host.E) (Kw w))]
      exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.E) w _).trans
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _)
    rw [h2]
    have := (w.intValuation_le_pow_iff_mem ((q:ℕ) : 𝓞 D.host.E) 1).2 hmem
    simpa using this
  have hu : Valued.v ((unifAt w : (Kw w)ˣ) : Kw w) = WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec w
  have hx' : Valued.v ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1 := by
    have := (e ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) 1).1 (by rw [map_one]; exact hx)
    rwa [map_one] at this
  have hNx : Valued.v (((q ^ n : ℕ) : Kw w) * x) ≤ 1 := by
    refine le_trans ?_ hx'
    rw [map_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Nat.cast_pow, map_pow, hu]
    gcongr
  have hNx2 : valuation (Kw w) (((q ^ n : ℕ) : Kw w) * x) ≤ valuation (Kw w) 1 :=
    (e (((q ^ n : ℕ) : Kw w) * x) 1).2 (by rw [map_one]; exact hNx)
  have h1 : ψ ((q ^ n) • x) = 1 := by
    rw [nsmul_eq_mul]
    exact (hc 1).2 (by simp) _ hNx2
  refine IsIntegral.of_pow (Nat.pos_of_ne_zero (pow_ne_zero n hq0)) ?_
  rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, h1, Circle.coe_one]
  exact isIntegral_one

private theorem emb_inj (D : D7) : Function.Injective
    (Sum.elim (Formalism.L2.Host.embTau D) fun i => ComplexEmbedding.conjugate (Formalism.L2.Host.embTau D i)) := by
  have h1 : Function.Injective (Formalism.L2.Host.embTau D) := GlobalTheory.Survey.EmbeddingValuationsAnti.embTau_injective D
  have h2 : ∀ τ τ', ComplexEmbedding.conjugate (Formalism.L2.Host.embTau D τ) ≠ Formalism.L2.Host.embTau D τ' := fun τ τ' h =>
    GlobalTheory.Survey.EmbeddingValuationsAnti.embTau_ne_bar D τ τ' ((RingHom.ext fun _ => rfl).trans h)
  refine h1.sumElim (fun a b h => h1 (star_injective h)) fun a b h => h2 b a h.symm

private theorem lev_two {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {v : HeightOneSpectrum (𝓞 E)}
    (h : χ.LevelLe v 1) : χ.LevelLe v 2 :=
  fun x hx h' => h x hx (h'.trans (WithZero.exp_le_exp.2 (by norm_num)))

private theorem nu_int {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀)
    (large₂ : SizeData₂ D) (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (hH : HostHyp D) (hc : sc.cGap = 1) (t : T) (w : Pl D.host.E)
    {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) :
    ((locGrid G t w).nu i j (unifAt w) : ℂ) ∈ Lo (Ideal.absNorm w.asIdeal) (2 * ⌊8 * large₂.sc.b⌋₊) ∧
      ((locGrid G t w).nu i j (unifAt w)⁻¹ : ℂ) ∈ Lo (Ideal.absNorm w.asIdeal) (2 * ⌊8 * large₂.sc.b⌋₊) := by
  classical
  obtain ⟨b1, b2⟩ := UpperTheory.abs_hc_exponent_le_and_abs_center_le_of_sizeRows D large₂ hS hH
  have h12 := (GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS).2.2.2.2.2.2.2
  have e1 : (((locGrid G t w).nu i j (unifAt w) : ℂˣ) : ℂ) =
      ((L.C.mu0 ⟨j, hj⟩).val w : ℂ) * ((L.xiH t).val w : ℂ) * (((G.ch.chiH (D.R.m - i)).val w : ℂ))⁻¹ := by
    simp only [Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Units.val_div_eq_div_val, div_eq_mul_inv]
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  have hμ := L.C.isMu0 ⟨j, hj⟩
  obtain ⟨n, hn, hinf⟩ := GlobalTheory.Chain.StepVac.hasInfQ_tau hμ.inf
  have hg0 : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    exact_mod_cast mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  obtain ⟨m1, m2⟩ := val_int (L.C.mu0 ⟨j, hj⟩) (Formalism.L2.DIV.primesOf ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E))
    (fun v hv => hμ.unr v fun k hk => hv (by
      rw [Formalism.L2.DIV.mem_primesOf, and_iff_right hg0, Nat.cast_mul, v.isPrime.mul_mem_iff_mem_or_mem]
      fin_cases k
      exacts [Or.inl hk, Or.inr hk])) (fun v => lev_two (hμ.tame v)) (Formalism.L2.Host.embTau D) (emb_inj D) n hinf
    ⌊8 * large₂.sc.b⌋₊ (fun τ => Nat.le_floor (by
      have h1 := hn τ
      simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
      have h2 : (n τ : ℝ) = 2 * -(((D.hc τ).e ⟨j, hj⟩ : ℚ) : ℝ) := by exact_mod_cast h1
      have h3 := b1 τ ⟨j, hj⟩
      rw [Nat.cast_natAbs, Int.cast_abs, h2, abs_mul, abs_neg, abs_two]
      linarith)) w
  have hi1 : 1 ≤ D.R.m - i := by omega
  have hi2 : D.R.m - i ≤ D.R.m := by omega
  obtain ⟨c1, c2⟩ := val_int (G.ch.chiH (D.R.m - i)) (G.pl.S0.biUnion (Formalism.L2.Host.aboveF (L := D.host.E) D.host.F))
    (fun v hv => G.ch.unr _ hi1 hi2 v fun h => hv (Finset.mem_biUnion.2 ⟨_, h, by simp [Formalism.L2.Host.aboveF]⟩))
    (fun v => by
      by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
      · rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
        · exact lev_two (G.ch.lev0 _ hi1 hi2 v h).1
        · exact (G.ch.lev1 _ hi1 hi2 v h).1
      · exact fun x hx _ => G.ch.unr _ hi1 hi2 v h x hx) (Formalism.L2.Host.embTau D) (emb_inj D) _ (G.ch.inf _ hi1 hi2)
    ⌊8 * large₂.sc.b⌋₊ (fun τ => Nat.le_floor (by
      have h3 := b2 τ _ hi1 hi2
      rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_mul, abs_mul, Int.cast_ofNat, abs_two, hc]
      linarith)) w
  obtain ⟨N, hN, hord⟩ := hL.xi_fin t
  have hx : ((L.xiH t).val w : ℂ) ^ N = 1 := by
    have h1 : ((L.xiH t) ^ N).val w = 1 := by rw [show (L.xiH t) ^ N = 1 from hord]; rfl
    have h2 : ((L.xiH t) ^ N).val w = (L.xiH t).val w ^ N := rfl
    rw [← Units.val_pow_eq_pow_val, ← h2, h1, Units.val_one]
  have x1 : IsIntegral ℤ ((L.xiH t).val w : ℂ) := IsIntegral.of_pow hN (by rw [hx]; exact isIntegral_one)
  have x2 : IsIntegral ℤ ((L.xiH t).val w : ℂ)⁻¹ := IsIntegral.of_pow hN (by rw [inv_pow, hx, inv_one]; exact isIntegral_one)
  rw [map_inv, Units.val_inv_eq_inv_val, e1, two_mul]
  refine ⟨Lo_mul (Lo_mul (b := 0) (mem_Lo.2 m1) (Lo_zero x1)) (mem_Lo.2 c2), ?_⟩
  rw [mul_inv, mul_inv, inv_inv]
  exact Lo_mul (Lo_mul (b := 0) (mem_Lo.2 m2) (Lo_zero x2)) (mem_Lo.2 c1)

end SlopeTestRemainingChoices

theorem _root_.GlobalTheory.T.flips_loss_bounded_at_exceptional_places : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₁ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum) (P : Pl D.host.E), P ∈ locPl ch.G t → ∀ w : PlL D,
        (P ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) (c₁ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * large₂.sc.b * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ)) := by
  refine ⟨0, fun CF _ => ⟨56, fun ε => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc hF t Φ w hw la hla z
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B t Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hq : resCard (Kw w) = Ideal.absNorm w.asIdeal := GlobalTheory.LFun.SatBoundGL.resCard_completion w
  have hq0 : resCard (Kw w) ≠ 0 := by rw [hq]; exact Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot
  have hgap : ch.sc.cGap = 1 := by rw [show ch.sc = _ from hsc]
  have hfl : ∀ x ∈ flipOrder D.R.m, x.1 < D.R.m ∧ x.2 < D.R.m ∧
      CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G t w).nu x.1 x.2) ∧ ¬ IsUnram ((locGrid ch.G t w).nu x.1 x.2) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    have hs := hg.square i hi j hj
    have e := (locGrid ch.G t w).alpha_div_beta i j
    exact ⟨hi, hj, by rw [← e]; exact hs.condν, by rw [← e]; exact hs.ram⟩

  let K : Subfield ℂ := D.what₂.embLL.fieldRange
  have hK : ∀ y, y ∈ Set.range D.what₂.embLL → y ∈ K := fun y hy => RingHom.mem_fieldRange.2 hy
  have hmu : ∀ j x, ((R.toLevCh.C.mu0 j).loc w x : ℂ) ∈ K := fun j x => hK _ (hF.chars.mu0 j w x)
  have hxi : ∀ x, ((R.toLevCh.xiH t).loc w x : ℂ) ∈ K := fun x => hK _ (hF.chars.xi t w x)
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, ((ch.G.ch.chiH i).loc w x : ℂ) ∈ K :=
    fun i a b x => hK _ (hF.chars.chi i a b w x)
  have habs : ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ K :=
    GlobalTheory.TflipField.apow_half_mem K w (hK _ (hF.sqrt w (.inr ⟨t, hw⟩)))
  have hψ := GlobalTheory.TflipField.psiAt_mem (W := ch.W) K (fun z hz => hK _ (hF.roots t w hw z hz)) h00.cond
  obtain ⟨y, hy⟩ : ∃ y, D.what₂.embLL y = Tflip ch.W ch.S.B t Φ w z :=
    RingHom.mem_fieldRange.1 (GlobalTheory.TflipField.flips_mem K h00.unif h00.cond h00.one_le habs hψ (flipOrder D.R.m)
      (givenStage t w ch.S.B Φ)
      (fun x hx => ⟨(hfl x hx).2.2.1, (hfl x hx).2.2.2, GlobalTheory.TflipField.nu_mem K t w hmu hxi hchi (hfl x hx).1 (hfl x hx).2.1⟩)
      (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) hadm.tensor
      (GlobalTheory.TflipField.givenStage_mem K ch.S.B t Φ w hmu hxi) z)

  have key : Tflip ch.W ch.S.B t Φ w z ∈ UpperTheory.FlipInt.Lo (resCard (Kw w)) (0 + (flipOrder D.R.m).length *
      (depthAt ch.G w * bigN D * (3 * (2 * ⌊8 * large₂.sc.b⌋₊) + 8 * bigN D))) := by
    refine UpperTheory.FlipInt.flips_mem h00.unif h00.cond h00.one_le hq0 (psi_int h00.cond _) (flipOrder D.R.m)
      (givenStage t w ch.S.B Φ) 0 (fun x hx => ?_) (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) hadm
      (fun z => UpperTheory.FlipInt.Lo_zero (UpperTheory.isIntegral_localGrid_tensor_of_levelChar hL ch.S.B t Φ w z)) z
    obtain ⟨hi, hj, h1, h2⟩ := hfl x hx
    have h3 := nu_int ch.G hL large₂ hS.size hS.host hgap t w hi hj
    rw [← hq] at h3
    refine ⟨h1, h2, h3.1, h3.2, ?_⟩
    change D.R.r + (x.2 + 1) * D.R.t + (x.1 + 1) * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have a1 : (x.2 + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
    have a2 : (x.1 + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
    have a3 : D.R.r ≤ D.R.k + D.R.m := by unfold Ranks.r; omega
    rw [mul_add, mul_add]; omega
  rw [zero_add, (canFlip_flipOrder _).2.1, UpperTheory.FlipInt.mem_Lo, ← hy, ← map_natCast D.what₂.embLL, ← map_pow, ← map_mul] at key
  replace key := (isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective).1 key
  refine ⟨y, hy, ?_⟩
  by_cases hy0 : y = 0
  · exact Or.inl hy0
  refine Or.inr ?_
  have h1 := UpperTheory.FlipVal.vw_ge la hy0 hq0 _ key
  have h2 : -(((D.R.m ^ 2 * (depthAt ch.G w * bigN D * (3 * (2 * ⌊8 * large₂.sc.b⌋₊) + 8 * bigN D)) : ℕ) : ℝ) *
      (vw la ((resCard (Kw w) : ℕ) : D.what₂.LL) : ℝ)) ≤ (vw la y : ℝ) := by exact_mod_cast h1
  refine le_trans (neg_le_neg ?_) h2
  by_cases hW : w ∈ ch.G.pl.W0
  · have hd : depthAt ch.G w = cosExp ch.G w := by
      rw [depthAt, max_eq_left]
      rw [cosExp, if_pos hW]
      exact ch.G.pl.depth_pos _ _
    obtain ⟨s1, -, s2, -, -, -, -, s3⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS.size
    have s2' : (1 : ℝ) ≤ bigN D := by exact_mod_cast s2
    have s4 : (⌊8 * large₂.sc.b⌋₊ : ℝ) ≤ 8 * large₂.sc.b := Nat.floor_le (by linarith)
    have s5 : (0 : ℝ) ≤ (vw la ((resCard (Kw w) : ℕ) : D.what₂.LL) : ℝ) := by
      exact_mod_cast UpperTheory.FlipVal.vw_nat_nonneg la _
    refine mul_le_mul_of_nonneg_right ?_ s5
    rw [hd]
    push_cast
    have s6 : 3 * (2 * (⌊8 * large₂.sc.b⌋₊ : ℝ)) + 8 * bigN D ≤ 56 * (bigN D * large₂.sc.b) := by nlinarith
    calc _ ≤ (D.R.m : ℝ) ^ 2 * ((cosExp ch.G w : ℝ) * bigN D * (56 * (bigN D * large₂.sc.b))) := by gcongr
      _ = _ := by ring
  · have h0 : vw la ((resCard (Kw w) : ℕ) : D.what₂.LL) = 0 := by
      rw [hq]; exact UpperTheory.FlipVal.vw_absNorm la w (hla.resolve_left hW)
    rw [h0]; simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasIndexBoundOfRuns
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.BigOn

theorem isLattice_of_spanK {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {C : Type}
    [AddCommGroup C] [Module F C] [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (M : Submodule (𝓞 F) C) (h : IsLatIn ⊤ (spanK z (M : Set C))) :
    Submodule.IsLattice F M := by
  have hinj : Function.Injective (coordMap z) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : z.symm ((1 : K) ⊗ₜ[F] x) = 0 := hx
    rw [LinearEquiv.map_eq_zero_iff] at h1
    exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff F C x).1 h1
  refine ⟨?_, ?_⟩
  · have h1 : ((spanK z (M : Set C)).restrictScalars (𝓞 F)).FG := h.1.restrictScalars
    have h2 : M.map ((coordMap z).restrictScalars (𝓞 F)) ≤ (spanK z (M : Set C)).restrictScalars (𝓞 F) := by
      rintro _ ⟨x, hx, rfl⟩
      exact mem_spanK z hx
    exact Submodule.fg_of_fg_map_injective ((coordMap z).restrictScalars (𝓞 F)) hinj (h1.of_le h2)
  · refine Submodule.baseChange_injective (A := K) ?_
    rw [Submodule.baseChange_top, Submodule.baseChange_span, eq_top_iff]
    intro y _
    have h2 := h.2
    unfold spanK at h2
    rw [Submodule.span_span_of_tower] at h2
    have h3 : z.symm y ∈ Submodule.span K ((fun f : C => z.symm (1 ⊗ₜ[F] f)) '' (M : Set C)) := h2 ▸ Submodule.mem_top
    have h4 := Submodule.mem_map_of_mem (f := z.toLinearMap) h3
    rw [Submodule.map_span, ← Set.image_comp] at h4
    simp only [Function.comp_def, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h4
    exact h4

theorem exists_rem_of_concl {D : D7} {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P6 j) (S : WeightAlgebra.Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (a b c d : ℝ)
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (hM : IsLatIn ⊤ (spanK z (B.Mlat j ka : Set _)))
    (hC : WeightAlgebra.Concl X S ka wL wF T nus (X.rk ka (B.Mlat j ka) * a * b * c * d)) :
    ∃ r : HeightOneSpectrum (𝓞 K) → ℝ, (∀ v, 0 ≤ r v) ∧
      (∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ v ∈ S', Formalism.DivisionValues.lw v * r v ≤ (n : ℝ) * (a * b * c * d)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 K)) (e : ℕ), (T : ℝ) * nus (placeBelow (K := B.KO) v) ≤ e →
        ∀ W : Submodule K (Fin n → K),
          (lix v (cut W (spanK z (B.Mlat j ka : Set _))) (cut W (spanK z {F | X.inc ka F ∈ X.Theta S ka wL wF T})) : ℝ) ≤
            ((ramOver (K := B.KO) v * e : ℕ) : ℝ) * (Module.finrank K W : ℝ) + r v := by
  have hM' := isLattice_of_spanK z _ hM
  have hn : X.rk ka (B.Mlat j ka) = n := by
    unfold WeightAlgebra.PJ.rk
    rw [hM'.span_eq_top, finrank_top]
    have := z.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_fin_fun] at this
    exact this.symm
  let Q : Formalism.MainNotions.Gaps.LocalGlobalPassage.Run D B P6 := ⟨j, X, S, ka, wL, wF, T, nus, X.rk ka (B.Mlat j ka) * a * b * c * d⟩
  obtain ⟨r, h0, h1, h2, h3⟩ := Formalism.MainNotions.Gaps.LocalGlobalPassage.l2 Q (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1 la)
    (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1b la) (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1c la) hM' hC
  have hβ : Q.β = (n : ℝ) * (a * b * c * d) := by
    change (X.rk ka (B.Mlat j ka) : ℝ) * a * b * c * d = _
    rw [hn]
    ring
  refine ⟨fun v => (v.asIdeal.ramificationIdx (𝓞 B.KO) : ℝ) * r (v.under (𝓞 B.KO)),
    fun v => mul_nonneg (Nat.cast_nonneg _) (h0 _),
    fun S' => (Formalism.MainNotions.Gaps.LocalGlobalPassage.l4 r h0 h1 S').trans (h2.trans hβ.le), ?_⟩
  intro v e he W
  have hpl : placeBelow (K := B.KO) v = v.under (𝓞 B.KO) := rfl
  have hram : ramOver (K := B.KO) v = v.asIdeal.ramificationIdx (𝓞 B.KO) := Formalism.MainNotions.Gaps.LocalGlobalPassage.ram_eq v
  obtain ⟨h4, h5⟩ := h3 (v.under (𝓞 B.KO))
  have hTh : Formalism.MainNotions.Gaps.LocalGlobalPassage.up (coordMap z) (Q.M0 ⊓ Q.Th0) ≤ spanK z {F | X.inc ka F ∈ X.Theta S ka wL wF T} :=
    Submodule.span_mono (Set.image_mono fun f hf => hf.2)
  exact Formalism.MainNotions.Gaps.LocalGlobalPassage.l5 (coordMap z) (coordMap_linearIndependent z) (coordMap_span z) Q.M0 (Q.M0 ⊓ Q.Th0) hM'.fg
    hM'.span_eq_top h4 inf_le_left v e (r (v.under (𝓞 B.KO))) (ramOver (K := B.KO) v * e)
    (by rw [hram]; push_cast; rfl) (h5 e (by rw [Int.cast_natCast, ← hpl]; exact he)) _ hTh W

theorem starRing_eq {R : Type} [CommRing R] (s t : StarRing R) (h : ∀ a : R, s.star a = t.star a) : s = t := by
  obtain @⟨@⟨@⟨⟨f⟩, _⟩, _⟩, _⟩ := s
  obtain @⟨@⟨@⟨⟨g⟩, _⟩, _⟩, _⟩ := t
  obtain rfl : f = g := funext h
  rfl

theorem exists_rem_of_tie {D : D7} {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} {X : WeightAlgebra.PJ D B P6 j}
    {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ} {ka wL wF : WeightFamilies.Wt D j} {T : ℕ}
    {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} {a b c d : ℝ}
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra B.KO K]
    {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    {O : OnObj S P oc} {v₁ : HeightOneSpectrum (𝓞 K)} {i : Bs.J}
    {z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka} {act : P → B.Cusp j ka → B.Cusp j ka}
    (ht : FormTieK X hinj EX p ka wL wF T O v₁ i z act) (hM : IsLatIn ⊤ (O.Ms i))
    (hC : WeightAlgebra.Concl X (scalOfP B hinj EX p ka wL wF T) ka wL wF T nus (X.rk ka (B.Mlat j ka) * a * b * c * d)) :
    ∃ r : HeightOneSpectrum (𝓞 K) → ℝ, (∀ v, 0 ≤ r v) ∧
      (∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ v ∈ S', Formalism.DivisionValues.lw v * r v ≤ (O.nZ i : ℝ) * (a * b * c * d)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 K)), FormTieK X hinj EX p ka wL wF T O v i z act →
        ∀ e : ℕ, (T : ℝ) * nus (placeBelow (K := B.KO) v) ≤ e → ∀ W : Submodule K (Fin (O.nZ i) → K),
          (lix v (cut W (O.Ms i)) (cut W (O.Th v i)) : ℝ) ≤
            ((ramOver (K := B.KO) v * e : ℕ) : ℝ) * (Module.finrank K W : ℝ) + r v := by
  obtain ⟨ρ, h0, h1, h2⟩ := exists_rem_of_concl X _ ka wL wF T nus a b c d z (ht.Ms_eq ▸ hM) hC
  refine ⟨ρ, h0, h1, fun v hv e he W => ?_⟩
  rw [hv.Ms_eq, hv.Th_eq]
  exact h2 v e he W

theorem nusR_le_eLam {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D)
    (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) :
    letI := T.Q.H.starRing
    (Tp.TO : ℝ) * GlobalTheory.RunJoin.nusR h j (lR Tp hK j) la ≤
      ((GlobalTheory.RunDepth.depOf T.toCore EX Tp hK).Q.eLam (ramOverZ la)
        (nuStarAt (Xo := T.Q.Xo j) (c := T.Q.c) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) la j) (resCharOf la) : ℝ) := by
  have hn := GlobalTheory.RunDepthScale.nusOf_eq_ram_mul_nuStarAt D L Pm Tp hK T h EX j hj la
  refine le_trans (le_of_eq ?_) (DepPage.le_eLam _ _ _ _)
  refine (congrArg (fun t => (Tp.TO : ℝ) * t) hn).trans ?_
  rw [← mul_assoc, mul_comm (Tp.TO : ℝ)]
  rfl

set_option maxHeartbeats 1000000 in

theorem hasIndexBound_of_runs : ∀ CK : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → CoreTies L EX J R → OwnPin r → RunsHold Tp hK EX CK r → LeafSup O → LeafSpan O → O.b = L.sc.b → HasIndexBound O := by
  intro CK D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hO _ _ hR hS hSp hb
  obtain rfl : κ = fun i : Fin D.R.m => kaR Tp hK ((i : ℕ) + 1) := funext hO.kap
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hO.tied
  obtain ⟨st, hd⟩ := hO.depth
  let _ := hostAlg D
  obtain rfl : st = J.toCore.Q.H.starRing := starRing_eq _ _ hd.star_eq
  let _ := J.toCore.Q.H.starRing
  let _ : ∀ s : RunData J, Algebra s.full.J.Q.c.F D.what₂.LL := fun _ => inst
  let _ : ∀ (s : RunData J) (h : LawsP s.full.toTop), Algebra (recB h.toLawsCore).KO D.what₂.LL := fun _ _ => inst
  have key : ∀ (q : Prop) (i : Fin D.R.m), ∃ ρ : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ, (∀ v, 0 ≤ ρ v) ∧
      (∀ S' : Finset (HeightOneSpectrum (𝓞 D.what₂.LL)),
        ∑ v ∈ S', Formalism.DivisionValues.lw v * ρ v ≤ (O.nZ i : ℝ) * (D.R.f * D.R.m * L.sc.b * L.de2)) ∧
      ∀ v, (Formalism.EigenvalueLevelCeiling.plc v = D.host.pde ↔ q) → ∀ W : Submodule D.what₂.LL (Fin (O.nZ i) → D.what₂.LL),
        (lix v (cut W (O.Ms i)) (cut W (O.Th v i)) : ℝ) ≤ (O.E v i : ℝ) * (finrank D.what₂.LL W : ℝ) + ρ v := by
    intro q i
    by_cases hq : ∃ v₁ : HeightOneSpectrum (𝓞 D.what₂.LL), (Formalism.EigenvalueLevelCeiling.plc v₁ = D.host.pde ↔ q)
    · obtain ⟨v₁, hv₁⟩ := hq
      obtain ⟨ρ, h0, h1, h2⟩ := @exists_rem_of_tie D (recB hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inst _ _ _ _ _ _ _ _ _ _ _ _ (ht v₁ i).1.toFormTieK (hS i).1
        (hR v₁ (hO.ok.laws v₁).p hinj ((i : ℕ) + 1) (inR_succ i)).2
      refine ⟨ρ, h0, h1, fun v hv W => ?_⟩
      have e1 : r.used v = r.used v₁ := by
        unfold TwoRuns.used
        exact if_congr (hv.trans hv₁.symm) rfl rfl
      have e2 : ownAt D v = ownAt D v₁ := by
        unfold ownAt
        exact if_congr (hv.trans hv₁.symm) rfl rfl
      have h3 := (ht v i).1.toFormTieK
      have h4 := (hO.ok.laws v).p
      rw [hd.E_eq v i]
      refine h2 v ?_ _ (nusR_le_eLam Tp hK EX (r.used v₁).full.toTop (hO.ok.laws v₁).p _ (inR_succ i) _) W
      have h5 : ∀ (s : RunData J) (h' : LawsP s.full.toTop) (p' : ℕ), s = r.used v₁ → p' = ownAt D v₁ →
          letI : Algebra (recB h'.toLawsCore).KO D.what₂.LL := inst
          FormTieK (recPJ h' ((i : ℕ) + 1) (inR_succ i)) hinj EX p' (kaR Tp hK ((i : ℕ) + 1)) (lR Tp hK ((i : ℕ) + 1))
            (fR Tp hK ((i : ℕ) + 1)) Tp.TO O v i (z i) (act i) →
          letI : Algebra (recB (hO.ok.laws v₁).p.toLawsCore).KO D.what₂.LL := inst
          FormTieK (recPJ (hO.ok.laws v₁).p ((i : ℕ) + 1) (inR_succ i)) hinj EX (ownAt D v₁) (kaR Tp hK ((i : ℕ) + 1))
            (lR Tp hK ((i : ℕ) + 1)) (fR Tp hK ((i : ℕ) + 1)) Tp.TO O v i (z i) (act i) := by
        rintro _ _ _ rfl rfl h
        exact h
      exact h5 _ h4 _ e1 e2 h3
    · refine ⟨fun _ => 0, fun _ => le_rfl, fun S' => ?_, fun v hv => absurd ⟨v, hv⟩ hq⟩
      have h1 := L.thickDensity_pos
      have h2 : 0 < L.sc.b := Real.exp_pos _
      simp only [mul_zero, Finset.sum_const_zero]
      positivity
  choose ρ h0 h1 h2 using key
  rw [← hd.f_eq, ← hd.m_eq, ← hb] at h1
  choose a ha using fun (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Fin D.R.m) => Formalism.MainNotions.Gaps.LocalGlobalPassage.exists_vw_eq v (O.E v i)
  refine ⟨O.Th, a, fun v i => ρ False i v, fun v i => ρ True i v, L.de2, ?_, L.thickDensity_pos.le, L.thickDensity_le_one,
    fun v i => ⟨h0 _ i v, h0 _ i v⟩, fun i S' => ⟨h1 _ i S', h1 _ i S'⟩⟩
  have hloc : ∀ v (i : Fin D.R.m) (W : Submodule D.what₂.LL (Fin (O.nZ i) → D.what₂.LL)),
      (lix v (cut W (O.Ms i)) (cut W (O.Th v i)) : ℝ) ≤ (O.E v i : ℝ) * (finrank D.what₂.LL W : ℝ) +
        (if Formalism.EigenvalueLevelCeiling.plc v = O.pde then ρ True i v else ρ False i v) := by
    intro v i W
    rw [hO.pde_eq]
    split_ifs with hv
    · exact h2 True i v (iff_true_intro hv) W
    · exact h2 False i v (iff_false_intro hv) W
  intro w hw
  exact ⟨fun i => ⟨((hSp w hw).1 i).1, le_rfl, (ha _ i).1, (ha _ i).2, hloc _ i⟩,
    fun i => ⟨((hSp w hw).2 i).1, le_rfl, (ha _ i).1, (ha _ i).2, hloc _ i⟩⟩

end GlobalTheory.BigOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookPlusLeMainTerm
section
noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowTopBound

theorem idem_apply {G H : Type} [Group G] [Fintype G] [AddCommGroup H] [Module ℂ H] (ρ : Representation ℂ G H) {a : G → ℂ}
    (ha : GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents.IsCentralIdem a) (u : H) :
    (∑ g, a g • ρ g : H →ₗ[ℂ] H) ((∑ g, a g • ρ g : H →ₗ[ℂ] H) u) = (∑ g, a g • ρ g : H →ₗ[ℂ] H) u := by
  have h1 : (∑ g, a g • ρ g : H →ₗ[ℂ] H) u = ∑ g, ∑ h, (a h * a (h⁻¹ * g)) • ρ g u := by
    simp only [← Finset.sum_smul, ha.2, LinearMap.sum_apply, LinearMap.smul_apply]
  have h2 : (∑ g, a g • ρ g : H →ₗ[ℂ] H) ((∑ g, a g • ρ g : H →ₗ[ℂ] H) u) = ∑ h, ∑ g, (a h * a g) • ρ h (ρ g u) := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [h2, h1, Finset.sum_comm (f := fun g h => (a h * a (h⁻¹ * g)) • ρ g u)]
  refine Finset.sum_congr rfl fun h _ => Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

theorem le_eigenvalue {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T S : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y) (m l : ℝ)
    (hS : ∀ y, S y = e (T y)) (hee : ∀ y, e (e y) = e y) (hadj : ∀ x, e x = x → ∀ y, ⟪x, e y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hm : ∀ u, m * ‖u‖ ^ 2 ≤ ‖LinearMap.adjoint T u‖ ^ 2) (x : Y) (hx : x ≠ 0) (hl : 0 < l)
    (h : S (LinearMap.adjoint S x) = (l : ℂ) • x) : m ≤ l := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hex : e x = x := by
    refine smul_right_injective Y hl' ?_
    show (l : ℂ) • e x = (l : ℂ) • x
    rw [← map_smul, ← h, hS, hee]
  have h1 : LinearMap.adjoint S x = LinearMap.adjoint T x := ext_inner_right ℂ fun f => by
    rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, hS, hadj x hex]
  have h2 : ‖LinearMap.adjoint T x‖ ^ 2 = l * ‖x‖ ^ 2 := by
    have h3 : ⟪LinearMap.adjoint S x, LinearMap.adjoint S x⟫_ℂ = (l : ℂ) * ⟪x, x⟫_ℂ := by
      rw [LinearMap.adjoint_inner_left, h, inner_smul_right]
    rw [h1, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
    have h4 : ((‖LinearMap.adjoint T x‖ ^ 2 : ℝ) : ℂ) = ((l * ‖x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast; exact h3
    exact_mod_cast h4
  have h5 := hm x
  rw [h2] at h5
  exact le_of_mul_le_mul_right h5 (by positivity)

theorem scalar_of_ne_bot {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (T : X →ₗ[ℂ] Y) (U U' : Y →ₗ[ℂ] X)
    (hU : U' = U) (P P' : Submodule ℂ Y) (hP : P' = P) (m m' : ℝ) (hm : m ≤ m')
    (h : P' ≠ ⊥ → ∃ l : ℝ, 0 < l ∧ (∀ x ∈ P', T (U' x) = (l : ℂ) • x) ∧ m' ≤ Real.log l) :
    ∃ l : ℝ, Real.exp m ≤ l ∧ ∀ y ∈ P, T (U y) = (l : ℂ) • y := by
  subst hU hP
  by_cases hc : P' = ⊥
  · refine ⟨_, le_rfl, fun y hy => ?_⟩
    have h0 : y = 0 := (Submodule.eq_bot_iff _).1 hc y hy
    rw [h0, map_zero, map_zero, smul_zero]
  · obtain ⟨l, hl, h1, h2⟩ := h hc
    exact ⟨l, (Real.le_log_iff_exp_le hl).1 (hm.trans h2), h1⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

include R in

theorem hookPlus_le_mainTerm (i : Fin D.R.m) : GlobalTheory.LiftLower.hookPlus D i ≤ GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.mainTerm D i (sg0 D A) := by
  have hl : ∀ ρ, lab (sg0 D A) ρ = ρ := fun ρ => by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.lab_base ρ
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.mainTerm GlobalTheory.LiftLower.hookPlus GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.aPlAt
  simp only [hl]
  have hp : ∀ n a, (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a : ℝ) := fun n a => by
    have : 0 < GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a := GlobalTheory.Survey.LevelVectorSizeBounds.hookProd_pos _
    exact_mod_cast this
  refine Finset.sum_le_sum fun ρ _ => Real.log_le_log (lt_of_lt_of_le one_pos (hp _ _)) ?_
  exact le_mul_of_one_le_right (zero_le_one.trans (hp _ _)) (hp _ _)

end GlobalTheory.LowTopBound

end
end

