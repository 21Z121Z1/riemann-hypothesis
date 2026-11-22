import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0131
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0398
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0112
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0055
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0341
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0246
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSStageLoc
section
noncomputable section

namespace GlobalTheory.Mem.SProv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

theorem delv_pos (s : Scale) (cD : ℝ) : (0 : ℚ) < (Delv s cD : ℚ) := by
  have h : 0 < s.x ^ cD := Real.rpow_pos_of_pos (lt_trans one_pos s.one_lt_alt) _
  exact_mod_cast Nat.ceil_pos.2 h

theorem code_of_over (K : Ctx) (B : Pre) (h : K.Over B) :
    ∃ letter : B.Word → Fin (B.R.k - 2) → Bool, Function.Injective letter ∧
      (∀ (w : B.Word) (τ : Tau B.R) (l : ℕ) (h : l + 1 < B.R.k - 1),
        (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * (Delv K.s K.cD : ℚ)) ∧
      ∀ (w : B.Word) (τ : Tau B.R) (l : ℕ) (h : l < B.R.k - 2),
        (B.hcW w τ).u ⟨l + 1, by omega⟩ =
          (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then (Delv K.s K.cD : ℚ) else 0) := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  refine ⟨K.c, K.ok.inj, fun w τ l h => ?_, K.ok.code⟩
  have h' : l + 1 < K.P.R.k - 1 := h
  have a := (K.ok.hc w).1 τ ⟨l, by omega⟩
  have b := (K.ok.hc w).1 τ ⟨l + 1, h'⟩
  have e : K.P.R.k - 2 - l = K.P.R.k - 2 - (l + 1) + 1 := by omega
  show (K.P.hcW w τ).v ⟨l, _⟩ - (K.P.hcW w τ).v ⟨l + 1, h'⟩ = _
  rw [a, b]
  simp only [e]
  push_cast
  ring

theorem exists_split (B : Pre) (p : HeightOneSpectrum (𝓞 B.host.F)) (L : LocAt B.host.F B.host.E B.conjF p) :
    ∃ s : Option (SplitAt L.Fp L.Ep L.cj (resChar p)),
      (s.isSome ↔ resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)) := by
  letI := B.host.cmStar
  by_cases h : resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)
  · have hk : ∃ k, resChar p = B.host.g k := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> exact ⟨_, h⟩
    obtain ⟨k, hk⟩ := hk
    obtain ⟨S⟩ := GlobalTheory.LocSplit.nonempty_splitAt B.host.F B.host.E B.conjF B.sp.cm.deg2 (SpectralModel.conjF_ne B) p L
      (by rw [hk, SpectralModel.ncard_primesOver _ _ (B.host.g_prime k), B.g_split])
    exact ⟨some S, by simpa using h⟩
  · exact ⟨none, by simp [h]⟩

theorem exists_sStage_loc (K : Ctx) (B : Base) (C : Cols B) (W : RowsRest B C) (cd : CDHaar) (h : K.Over B.toPre)
    (h2 : SpectralModel.ColsPos C) (h3 : W.Drows ≤ W.Dall)
    (L : ∀ p : HeightOneSpectrum (𝓞 B.host.F), LocAt B.host.F B.host.E B.toPre.conjF p) :
    ∃ S : SStage B C W, S.s.Del = (Delv K.s K.cD : ℚ) ∧ S.s.cdScale = Vol.trueScale cd ∧
      (∀ τ, S.dsig τ = Vol.trueDsig B.R (B.hc τ)) ∧
      ∀ p, ∃ s, S.s.atP p = { L p with split := s } := by
  obtain ⟨letter, hl, hg, hu⟩ := code_of_over K B.toPre h
  obtain ⟨S, hd, -⟩ := SpectralModel.exists_sStage W ⟨_, letter, delv_pos K.s K.cD, hl, hg, hu⟩ h2 h3
    (fun τ => Vol.trueDsig B.R (B.hc τ)) (fun τ => (Vol.lamSH_isHCParam_and_trueDsig_pos B.R (B.hc τ)).2) (fun _ => 0)
  choose sp hsp using fun p => exists_split B.toPre p (L p)
  exact ⟨{ S with
      s := { S.s with
        cdScale := Vol.trueScale cd
        cdScale_pos := Vol.trueScale_pos cd
        Del := (Delv K.s K.cD : ℚ)
        Del_pos := delv_pos K.s K.cD
        cloud_gap := hg
        letter := letter
        letter_inj := hl
        u_letter := hu
        atP := fun p => { L p with split := sp p } }
      s_split := hsp
      s_HH := S.s_HH
      s_Cu := S.s_Cu
      s_PlF := S.s_PlF
      s_Cu_isom := S.s_Cu_isom
      sEE := S.sEE },
    rfl, rfl, fun τ => congrFun hd τ, fun p => ⟨sp p, rfl⟩⟩

end GlobalTheory.Mem.SProv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceWPlGw
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixedPlaceOverType

theorem exists_splitPlace_w_plGw : ∀ (D : D7) (k : Fin 2) (v : D.nd.PlG k), ∃ s : SplitPlace D.host.E, s.w = D.naut.plGw k v :=
  fun D k v => GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, v⟩

end GlobalTheory.FixedPlaceOverType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FcLargeOfSup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top

theorem fc_large_of_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

theorem Ev.and {p q : Ctx → Prop} (hp : Ev p) (hq : Ev q) : Ev fun K => p K ∧ q K := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (fc_large_of_sup hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (fc_large_of_sup hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx), hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx)⟩⟩

theorem Ev.mono {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx => h X (ha3 X h1 h2 h3 h4 hx)⟩

theorem large₂.and {K : Ctx} {p q : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (hp : large₂ K p) (hq : large₂ K q) :
    large₂ K fun B f T => p B f T ∧ q B f T :=
  large₂.inter hp hq

theorem large₂.mono {K : Ctx} {p q : ∀ B : Base, Fr B.toPre → TwDat B → Prop}
    (h : ∀ B f T, K.Over B.toPre → p B f T → q B f T) (hp : large₂ K p) : large₂ K q :=
  large₂.imp hp h

end GlobalTheory.Mem.Top
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourMulRootLt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TamePow

theorem four_mul_root_lt {m k g : ℝ} (hm : 2 ≤ m) (hk : m + 3 ≤ k) (hg : k ^ 8 ≤ g) :
    4 * m * g ^ ((1 : ℝ) / 4) < g - 1 := by
  have hk5 : (5 : ℝ) ≤ k := by linarith
  have hg0 : 0 ≤ g := le_trans (by positivity) hg
  set t := g ^ ((1 : ℝ) / 4) with ht
  have ht4 : t ^ 4 = g := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hg0]
    norm_num
  have hkt : k ^ 2 ≤ t := by
    have h8 : (k ^ 8) ^ ((1 : ℝ) / 4) ≤ t := Real.rpow_le_rpow (by positivity) hg (by norm_num)
    have e : (k ^ 8) ^ ((1 : ℝ) / 4) = k ^ 2 := by
      rw [show (k ^ 8 : ℝ) = (k ^ 2) ^ (4 : ℕ) by ring, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity)]
      norm_num
    linarith
  have ht25 : 25 ≤ t := by nlinarith
  have h1 : 4 * m * t < k ^ 2 * t := by
    have : 4 * m < k ^ 2 := by nlinarith
    exact mul_lt_mul_of_pos_right this (by linarith)
  have h2 : k ^ 2 * t ≤ t * t := mul_le_mul_of_nonneg_right hkt (by linarith)
  have hs : 625 ≤ t * t := by nlinarith
  have h3 : t * t + 1 < t ^ 4 := by
    have e4 : t ^ 4 = t * t * (t * t) := by ring
    have := mul_le_mul_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ t * t)
    nlinarith
  linarith

theorem bound_of_over (K : Ctx) (B : Pre) (h : K.Over B) (i : Fin 2) :
    4 * (B.R.m : ℝ) * (B.host.g i : ℝ) ^ ((1 : ℝ) / 4) < (B.host.g i : ℝ) - 1 := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  show 4 * (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) < (K.P.H.g i : ℝ) - 1
  have hr : RankVal K.s K.P.R := K.ok.rank
  unfold RankVal at hr
  obtain ⟨-, ⟨-, hm⟩, ⟨hk, -⟩, -⟩ := hr
  have hv : HostVal K.s K.C.P.Cpde K.P.H := K.ok.val
  unfold HostVal at hv
  obtain ⟨-, -, -, -, hg, -⟩ := hv
  have hx1 : 1 < K.s.x := K.s.one_lt_alt
  have he0 : 0 < K.s.eps := K.s.eps_pos
  have hx0 : (0 : ℝ) ≤ K.s.x := by linarith
  have hd1 : K.s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
  have hd0 : 0 ≤ K.s.delta1 := Real.rpow_nonneg hx0 _
  set y := Real.sqrt K.s.x with hy
  have hy2 : y ^ 2 = K.s.x := Real.sq_sqrt hx0
  have hy1 : 1 ≤ y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1.le
  have hmy : (K.P.R.m : ℝ) ≤ 2 * y := by
    have : Real.sqrt (K.s.x * K.s.delta1) ≤ y := Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hk4 : K.s.x ^ (4 : ℕ) ≤ (K.P.R.k : ℝ) := by
    have h1 : K.s.x ^ (4 : ℝ) ≤ K.s.x ^ ((9 : ℝ) / 2 + 10 * K.s.eps) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have h2 : K.s.x ^ (4 : ℝ) = K.s.x ^ (4 : ℕ) := by exact_mod_cast Real.rpow_natCast K.s.x 4
    exact le_trans (le_trans h2.symm.le h1) hk
  have hk8 : y ^ 8 ≤ (K.P.R.k : ℝ) := by
    have : y ^ 8 = K.s.x ^ (4 : ℕ) := by rw [← hy2]; ring
    linarith
  have hk2 : (2 : ℝ) ≤ K.P.R.k := by
    have h1 : (1 : ℝ) < K.P.R.k := lt_of_lt_of_le (one_lt_pow₀ hx1 (by norm_num)) hk4
    have h2 : 1 < K.P.R.k := by exact_mod_cast h1
    exact_mod_cast h2
  have hb : (2.718 : ℝ) ≤ K.s.b := by
    have hL : 1 ≤ K.s.L := Real.one_le_rpow hx1.le he0.le
    have h1 : Real.exp 1 ≤ K.s.b := Real.exp_le_exp.2 hL
    have h2 := Real.exp_one_gt_d9
    linarith
  have hkb1 : (5 : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b := by nlinarith
  have hkb2 : 2 * y + 3 ≤ (K.P.R.k : ℝ) * K.s.b := by
    have hkb : 2.718 * (K.P.R.k : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b := by nlinarith
    by_cases h5 : (5 : ℝ) ≤ (K.P.R.k : ℝ)
    · have : y ≤ y ^ 8 := le_self_pow₀ hy1 (by norm_num)
      linarith
    · push_neg at h5
      have hk4' : (K.P.R.k : ℝ) ≤ 4 := by
        have : K.P.R.k < 5 := by exact_mod_cast h5
        have : K.P.R.k ≤ 4 := by omega
        exact_mod_cast this
      have hy12 : y ≤ 1.2 := by
        by_contra hc
        push_neg at hc
        have : (1.2 : ℝ) ^ 8 < y ^ 8 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
        norm_num at this
        linarith
      linarith
  have hM : max 2 (K.P.R.m : ℝ) + 3 ≤ (K.P.R.k : ℝ) * K.s.b := by
    have : max 2 (K.P.R.m : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b - 3 := max_le (by linarith) (by linarith)
    linarith
  have hmain := four_mul_root_lt (le_max_left 2 (K.P.R.m : ℝ)) hM (hg i).1
  have ht : (0 : ℝ) ≤ (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have hle : 4 * (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) ≤
      4 * max 2 (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) := by
    have : (K.P.R.m : ℝ) ≤ max 2 (K.P.R.m : ℝ) := le_max_right _ _
    nlinarith
  linarith

theorem tame_of_pow : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → (∀ (k : Fin 2) (v : X.N.nd.PlG k), ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧ ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1))) → ∀ (k : Fin 2) (v : X.toD7.nd.PlG k), haveI : Fact (X.toD7.host.g k).Prime := ⟨X.toD7.host.g_prime k⟩; DC.TameDistinct X.toD7.R.r (X.toD7.host.g k) (X.toD7.nd.chiT k v) := by
  have key : ∀ K : Ctx, ∀ X : Stages, K.Over X.B.toPre → (∀ (k : Fin 2) (v : X.N.nd.PlG k),
      ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧
        ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1))) →
      ∀ (k : Fin 2) (v : X.toD7.nd.PlG k), haveI : Fact (X.toD7.host.g k).Prime := ⟨X.toD7.host.g_prime k⟩;
        DC.TameDistinct X.toD7.R.r (X.toD7.host.g k) (X.toD7.nd.chiT k v) := by
    intro K X hO hpow k v
    obtain ⟨w, hw, hchi⟩ := hpow k v
    have hb := bound_of_over K X.B.toPre hO k
    have hr : 1 ≤ X.toD7.R.r := by
      have h2 := X.toD7.R.two_le_m
      first
      | (show 1 ≤ X.toD7.R.k + X.toD7.R.m - 1; omega)
      | omega
      | (simp only [Formalism.MainNotions.Ranks.r]; omega)
      | (unfold Formalism.MainNotions.Ranks.r; omega)
    have e : X.toD7.nd.chiT k v = fun j : Fin X.B.R.m => w ^ (2 * (j.1 + 1)) := funext hchi
    haveI : Fact (X.toD7.host.g k).Prime := ⟨X.toD7.host.g_prime k⟩
    have h := GlobalTheory.EX.DC.TameGen.tameDistinct_gen X.toD7.R.r (X.toD7.host.g k) X.B.R.m w hw hb hr
    rw [e]
    exact h
  unfold Ev
  refine ⟨1, one_pos, ?_⟩
  intro eps C8 _ _ _ _
  refine ⟨?k0, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K => ?_⟩⟩⟩⟩
  case k0 => first | exact ⟨0, 0, 0, 0⟩ | exact default | exact Classical.arbitrary _
  first
  | exact key K
  | exact fun _ => key K
  | exact fun _ _ => key K
  | exact fun _ _ _ => key K
  | exact fun _ _ _ _ => key K
  | exact fun _ _ _ _ _ => key K
  | exact fun _ _ _ _ _ _ => key K
  | exact fun _ _ _ _ _ _ _ => key K
  | exact fun _ _ _ _ _ _ _ _ => key K

end GlobalTheory.Mem.Top.TamePow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory
  Matrix
open scoped TensorProduct InnerProductSpace Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultFinite

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}

def pt (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  atTau θ V τ ((M.fr τ)⁻¹ * g * M.fr τ)

theorem mem_sm {τ : D.what₂.Tau} {w : M.H τ} :
    w ∈ M.sm τ ↔ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := by rw [sm_eq]

theorem sigma_mem_sm {τ : D.what₂.Tau} (w : M.sm τ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ UJset (M.ε τ)) : M.σ τ g w ∈ M.sm τ :=
  mem_sm.2 (sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (mem_sm.1 w.2) hg)

theorem map_sigma {T : MMap M} (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) (v : M.Vec) (w : M.sm τ)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ UJset (M.ε τ)) :
    T (Function.update v τ ⟨M.σ τ g w, sigma_mem_sm w hg⟩) = rTr V (pt θ M τ g) (T (Function.update v τ w)) := by
  have := hT.equiv τ _ (conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hg) (Function.update v τ w)
    ⟨M.σ τ g w, sigma_mem_sm w hg⟩ (by
      rw [Function.update_self]
      exact (congrArg (fun L : M.H τ →L[ℂ] M.H τ => L w) (trRep_conj (σ := M.σ τ) (M.fr_unit τ) g)).symm)
  rwa [Function.update_idem] at this

theorem exists_continuousLinearMap_tens_update {T : MMap M} (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ a : M.H τ →ₗ[ℂ] (GA D V → ℂ), (∀ w : M.sm τ, a w = T (Function.update v τ w)) ∧
      (∀ x, Sobolev₂ (lieG (gramAt D V τ)) (trRep (M.σ τ) (M.fr τ)) ((LinearMap.proj x).comp a)) ∧
      ∀ g ∈ UJset (M.ε τ), ∀ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)),
        a (M.σ τ g w) = rTr V (pt θ M τ g) (a w) := by
  obtain ⟨a, ha⟩ := LinearMap.exists_extend (T.toLinearMap v τ)
  have ha' : ∀ w : M.sm τ, a w = T (Function.update v τ w) := fun w => LinearMap.congr_fun ha w
  refine ⟨a, ha', fun x => ?_, fun g hg w hw => ?_⟩
  · obtain ⟨ℓ, ⟨L, C, h1, h2⟩, e⟩ := hT.cont τ v x
    refine ⟨L, C, h1, fun w hw => ?_⟩
    have := h2 w hw
    rw [e ⟨w, mem_sm.2 hw⟩, ← ha'] at this
    exact this
  · rw [ha' ⟨w, mem_sm.2 hw⟩, ← map_sigma hT τ v _ hg, ← ha']

theorem eq_zero_of_apply {T : MMap M} (hT : IsMultMap θ M J χ T) (v₀ : M.Vec) (h₀ : ∀ τ, v₀ τ ≠ 0) (h : T v₀ = 0) :
    T = 0 := by
  have key : ∀ s : Finset D.what₂.Tau, ∀ v : M.Vec, (∀ ρ, ρ ∉ s → v ρ = v₀ ρ) → T v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro v hv; rw [show v = v₀ from funext fun ρ => hv ρ (by simp), h]
    | insert τ s _ ih =>
      intro v hv
      have h2 : T (Function.update v τ (v₀ τ)) = 0 := by
        refine ih _ fun ρ hρ => ?_
        by_cases hh : ρ = τ
        · subst hh; simp
        · rw [Function.update_of_ne hh]; exact hv ρ (by simp [hh, hρ])
      obtain ⟨a, e, hs, hq⟩ := exists_continuousLinearMap_tens_update hT τ v
      have := (M.ds τ).1
      funext x
      have h3 := GlobalTheory.T.sobolevForm_eq_zero_of_smooth_orbit _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 _ (hs x)
        (v₀ τ) (mem_sm.1 (v₀ τ).2) (fun c => h₀ τ (Subtype.ext c)) (fun g hg => by
          show a _ x = 0
          rw [hq g hg _ (mem_sm.1 (v₀ τ).2), e, h2]
          rfl) (v τ) (mem_sm.1 (v τ).2)
      have h4 : a (v τ) x = 0 := h3
      rwa [e, Function.update_eq_self] at h4
  exact MultilinearMap.ext fun v => key Finset.univ v (by simp)

def kRep {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (W : Submodule ℂ H)
    (hW : ∀ k ∈ Formalism.REAL.Kset ε, ∀ w ∈ W, σ k w ∈ W) : Representation ℂ (Formalism.REAL.KG ε) W where
  toFun k := (σ (Formalism.REAL.toMK k) : H →ₗ[ℂ] H).restrict fun w hw => hW _ k.2 w hw
  map_one' := by
    ext w
    show σ 1 w = w
    rw [hσ.1.1]; rfl
  map_mul' k k' := by
    ext w
    show σ (Formalism.REAL.toMK k * Formalism.REAL.toMK k') w = σ (Formalism.REAL.toMK k) (σ (Formalism.REAL.toMK k') w)
    rw [hσ.1.2 _ (k : Formalism.REAL.UJ ε).2 _ (k' : Formalism.REAL.UJ ε).2]; rfl

theorem isContRep_kRep {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (hW : ∀ k ∈ Formalism.REAL.Kset ε, ∀ w ∈ W, σ k w ∈ W) :
    GlobalTheory.Published.AutFin.IsContRep (kRep hσ W hW) := fun ℓ w =>
  (LinearMap.continuous_of_finiteDimensional ℓ).comp
    (Continuous.subtype_mk ((continuous_orbit hσ w).comp continuous_subtype_val) _)

theorem hcFinite (hP : GlobalTheory.Published.HarishChandraFinite) : HCFinite θ M J χ := by
  rintro hθ ⟨U, hU, hUJ⟩
  have hc := fun τ => (M.ds τ).1
  choose W hWf hW0 hWs hWk using fun τ => GlobalTheory.T.exists_finiteDimensional_kStable_smoothVectors _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
    ⟨_, (M.ds τ).2.2.2.2.2.1⟩
  choose c hcs using fun τ => GlobalTheory.T.gelfandInvariantAction_smoothVectors_scalar _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1
  choose u huW hu0 using fun τ => (Submodule.ne_bot_iff _).1 (hW0 τ)
  let v₀ : M.Vec := fun τ => ⟨u τ, mem_sm.2 (hWs τ (huW τ))⟩
  have hfin := hP D θ hθ V U hU M.ε M.fr (fun τ => ⟨M.fr_unit τ, M.fr_gram τ⟩) (fun τ => W τ)
    (fun τ => kRep (M.ds τ).2.2.1 (W τ) (hWk τ)) (fun τ => isContRep_kRep _ _ _) c
  have hmem : ∀ T : Mult θ M J χ, (T : MMap M) v₀ ∈ GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr
      (fun τ => kRep (M.ds τ).2.2.1 (W τ) (hWk τ)) c := by
    intro T
    have hT := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 T.2
    refine ⟨hT.aut v₀, fun k hk hf g => ?_, fun τ => ?_, fun τ k => ?_⟩
    · rw [hT.lev v₀ k (hUJ k hk hf).1, (hUJ k hk hf).2, one_mul]
    · obtain ⟨a, e, -, hq⟩ := exists_continuousLinearMap_tens_update hT τ v₀
      have := GlobalTheory.Published.AutFin.hasTypeAt_of_map θ V τ (M.ε τ) (M.fr τ) (kRep (M.ds τ).2.2.1 (W τ) (hWk τ))
        (a.comp (W τ).subtype) (fun k w => hq (Formalism.REAL.toMK k) (GlobalTheory.LowTypeRestriction.kset_subset k.2) w (hWs τ w.2)) ⟨u τ, huW τ⟩
      have e' : (a.comp (W τ).subtype) ⟨u τ, huW τ⟩ = (T : MMap M) v₀ := by
        rw [← Function.update_eq_self τ v₀, ← e]; rfl
      rwa [e'] at this
    · rw [GlobalTheory.T.equivariant_map_carries_gelfandInvariant_to_function D θ V S M J χ hθ T hT τ k v₀ (c τ k • v₀ τ) (hcs τ k _ (mem_sm.1 (v₀ τ).2)).symm,
        MultilinearMap.map_update_smul, Function.update_eq_self]
  let ev : Mult θ M J χ →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr
      (fun τ => kRep (M.ds τ).2.2.1 (W τ) (hWk τ)) c) :=
    { toFun := fun T => ⟨(T : MMap M) v₀, Submodule.subset_span (hmem T)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero ev).2 fun T hT => Subtype.ext ?_)
  exact eq_zero_of_apply ((GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 T.2) v₀
    (fun τ h => hu0 τ (congrArg Subtype.val h)) (congrArg Subtype.val hT)

theorem schur_multMap (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {T T' : MMap M} (hT : IsMultMap θ M J χ T)
    (hT' : IsMultMap θ M J χ T') (τ : D.what₂.Tau) (v v' : M.Vec) :
    ∃ c : ℂ, ∀ w w' : M.sm τ,
      ∫ g in 𝓕, star (T (Function.update v τ w) g) * T' (Function.update v' τ w') g ∂μ = c * ⟪w, w'⟫_ℂ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : SecondCountableTopology (GA D V) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.1
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne
  have := (M.ds τ).1
  obtain ⟨a, e, hs, hq⟩ := exists_continuousLinearMap_tens_update hT τ v
  obtain ⟨a', e', hs', hq'⟩ := exists_continuousLinearMap_tens_update hT' τ v'
  have hpt : Continuous fun g : Formalism.REAL.UJ (M.ε τ) => pt θ M τ (umat g) :=
    (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous
      ((continuous_const.matrix_mul continuous_umat).matrix_mul continuous_const)
      fun g => conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) g.2
  have hf : ∀ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)), IsAutFunSm θ V (a w) ∧ IsCuspFun V (a w) :=
    fun w hw => by rw [e ⟨w, mem_sm.2 hw⟩]; exact ⟨hT.aut _, hT.cusp _⟩
  have hf' : ∀ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)), IsAutFunSm θ V (a' w) ∧ IsCuspFun V (a' w) :=
    fun w hw => by rw [e' ⟨w, mem_sm.2 hw⟩]; exact ⟨hT'.aut _, hT'.cusp _⟩
  have hinv : ∀ (φ ψ : GA D V → ℂ) (k : GA D V), IsAutFunSm θ V φ → IsAutFunSm θ V ψ →
      ∫ x in 𝓕, star (rTr V k φ x) * rTr V k ψ x ∂μ = ∫ x in 𝓕, star (φ x) * ψ x ∂μ := fun φ ψ k hφ hψ =>
    (GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun x => star (φ x) * ψ x) k h𝓕 fun γ hγ g => by
      rw [hφ.left γ hγ, hψ.left γ hγ]).2
  obtain ⟨c, hc⟩ := GlobalTheory.T.schurLemma_equivariant_pair_boundedFunctions_alt _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 (GA D V)
    (μ.restrict 𝓕) (fun g x => x * pt θ M τ (umat g)) (continuous_snd.mul (hpt.comp continuous_fst)) a a'
    (fun w hw => ⟨(hf w hw).1.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hf w hw).1 (hf w hw).2,
      fun g x => congrFun (hq _ g.2 w hw) x⟩) hs
    (fun w hw => ⟨(hf' w hw).1.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hf' w hw).1 (hf' w hw).2,
      fun g x => congrFun (hq' _ g.2 w hw) x⟩) hs'
    (fun g hg u hu w hw => by rw [hq g hg u hu, hq g hg w hw]; exact hinv _ _ _ (hf u hu).1 (hf w hw).1)
    (fun g hg u hu w hw => by rw [hq' g hg u hu, hq' g hg w hw]; exact hinv _ _ _ (hf' u hu).1 (hf' w hw).1)
    (fun g hg u hu w hw => by rw [hq g hg u hu, hq' g hg w hw]; exact hinv _ _ _ (hf u hu).1 (hf' w hw).1)
  refine ⟨c, fun w w' => ?_⟩
  rw [← e, ← e']
  exact hc w (mem_sm.1 w.2) w' (mem_sm.1 w'.2)

theorem schurMult (hP : GlobalTheory.Published.CuspRapidDecay) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) :
    SchurMult θ M J χ μ 𝓕 := by
  intro hθ hμ h𝓕 T hT T' hT'
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT hT'
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_eq_const_mul_prod_inner_of_slotwise' D.what₂.Tau (fun τ => M.sm τ) (fun v v' => ∫ g in 𝓕, star (T v g) * T' v' g ∂μ)
    fun τ v v' => schur_multMap hP hθ hμ h𝓕 hT hT' τ v v'
  exact ⟨c, fun v v' => ⟨GlobalTheory.CuspDecay.integrableOn_star_mul hP GlobalTheory.Mem.VolFin.finVol hθ μ 𝓕 hμ h𝓕 (hT.aut v)
    (hT'.aut v') (hT'.cusp v'), hc v v'⟩⟩

theorem hcFinite_and_schurMult : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay →
    ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
      (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
      HCFinite θ M J χ ∧ SchurMult θ M J χ μ 𝓕 :=
  fun h h' _ _ _ _ _ _ _ μ 𝓕 => ⟨hcFinite h, schurMult h' μ 𝓕⟩

end GlobalTheory.MultFinite

end
end

