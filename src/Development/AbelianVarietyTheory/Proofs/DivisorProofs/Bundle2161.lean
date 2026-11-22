import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuRatioValuesRootsOfUnity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem chrEq_pow' {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) :
    ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · have hp : (χ ^ a).locK P k = χ.locK P k ^ a := by
      have : ∀ x, (χ ^ a).1 x = χ.1 x ^ a := fun x => by rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]
      exact this _
    rw [MonoidHom.pow_apply, hp, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

private theorem exists_prime_power_pow_eq_one {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) {n : ℕ}
    (hn : χ.OrderDvd n) : c ^ n = 1 := by
  have h1 := chrEq_pow' h n
  rw [show χ ^ n = 1 from hn] at h1
  exact MonoidHom.ext fun x => GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x

theorem _root_.GlobalTheory.T.squareNu_ratio_values_roots_of_unity : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
    ∀ (i j : Fin D.R.m) (t : T) (k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)ˣ), ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧
      (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) = D.what₂.embLL ζ := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G W S hN i j t k => ?_⟩⟩
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have hc1 : Lc.xi μ₀ k = 1 := GlobalTheory.ChrEqUnique.eq_one_of_chrEq (hL.xi_base ▸ hL.xi μ₀) k
  have e : (GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k = Lc.xi t k := by
    have key : ∀ {Γ : Type} [CommGroup Γ] (a x y e c : Γ), y = 1 → (a * x * e / (c * e)) / (a * y * e / (c * e)) = x := by
      intro Γ _ a x y e c hy
      subst hy
      rw [mul_one, div_div_div_cancel_right, mul_div_mul_right_eq_div, mul_div_cancel_left]
    exact key (Lc.mu0 ((j : ℕ) + 1) k) (Lc.xi t k) (Lc.xi μ₀ k) ((Lc.eta ^ (rankV D i j % 2)) k) (G.ch.chi (D.R.m - i) k) hc1
  obtain ⟨y, hy⟩ := GlobalTheory.Adopt.heckeCharacter_finiteOrder_values_in_field D (Lc.xi t) (Lc.xiH t) n _ D.what₂.embLL (hL.xi t) hn ho ((hN.chars.xi t).valuesIn) k
  have h1 : ((Lc.xi t k : Circle) : ℂ) ^ n = 1 := by
    have := DFunLike.congr_fun (exists_prime_power_pow_eq_one (hL.xi t) ho) k
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    exact (map_pow Circle.coeHom _ _).symm.trans (congrArg _ this)
  have hyn : (y : D.what₂.LL) ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, hy, h1, map_one])
  exact ⟨y, GlobalTheory.KappaArith.isAwayUnit_of_pow_eq_one _ hn hyn, by rw [e, hy]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuUnramifiedOffPairPartialLPrimitive
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section

namespace GlobalTheory.NuOffPair

theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → D.host.F = maximalRealSubfield D.host.E →
  ∀ (G : GridData L sc) (t : T) (i j : Fin D.R.m) (χ : (AE D)ˣ →* Circle), ChrEq χ (nuH G t i j) →
    GlobalTheory.LFun.UnrOff χ ((sfB G t : Finset (FinPl D)) : Set (FinPl D)) ∧
    ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ → ∀ s : ℂ,
      GlobalTheory.Cont.HolValueAt (GlobalTheory.LFun.charL χ⁻¹ ((sfB G t : Finset (FinPl D)) : Set (FinPl D))) s (Λ s) := by
  intro D T L sc μ₀ hL hF G t i j χ hχ
  classical
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have hunr : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ sfB G t → (nuH G t i j).UnrAt w := by
    intro w hw
    have hv : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h => hw (GlobalTheory.BottomIPData.mem_bottomPairFinitePlacesBelow_of_mem_exceptional G t h)
    have hQ : ∀ P ∈ L.Q t, P.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F) := fun P hP e =>
      hw (e ▸ GlobalTheory.BottomIPData.under_mem_sfB G t (by unfold locPl; exact Finset.mem_union_right _ hP))
    have hchi : (G.ch.chiH (D.R.m - i)).UnrAt w := G.ch.unr _ hm.1 hm.2 w hv
    have hmu : (L.C.mu0 j).UnrAt w := (L.C.isMu0 j).unr _ fun k hk => hv (by
      have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
        rw [map_natCast]; exact hk
      refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
      fin_cases k
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
    have hxi : (L.xiH t).UnrAt w := by
      by_contra hn
      rcases (hL.Q_ram t w).1 hn with hq | ⟨P', hq, hc⟩
      · exact hQ w hq rfl
      · exact hQ P' hq (GlobalTheory.BotTripleUnr.under_eq_of_isConjPl hc)
    rw [nuH, div_eq_mul_inv]
    exact (hmu.mul hxi).mul hchi.inv
  have hram : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∈ sfB G t → ¬ (nuH G t i j).UnrAt w := by
    intro w hw
    by_cases h0 : w.under (𝓞 D.host.F) ∈ G.pl.S0
    · exact GlobalTheory.SqStep.nuH_not_unrAt_above hL G t i j w h0
    · unfold GlobalTheory.BottomIPData.sfB at hw
      obtain ⟨P, hP, hPw⟩ := Finset.mem_image.1 hw
      have hP' : P ∈ L.Q t := by
        unfold locPl GlobalTheory.ChiGrid.Places.W0 at hP
        rcases Finset.mem_union.1 hP with h | h
        · exfalso
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
          apply h0
          rw [← hPw, G.pl.under_w hv]
          exact hv
        · exact h
      have := GlobalTheory.TwistRam.not_unrAt_alpha_div_beta hL t i j w P hP' hPw h0
      have e0 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.nu t i (j + 1) :=
        mul_div_mul_right_eq_div _ _ _
      rwa [e0, GlobalTheory.LFun.unrAt_iff_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL)] at this
  refine ⟨fun w hw => (GlobalTheory.LFun.unrAt_iff_of_chrEq hχ w).2 (hunr w ?_), fun Λ hΛ s => ?_⟩
  · exact hw
  have hT : GlobalTheory.CMVal.TrivOnF (nuH G t i j) := by
    have h := ((L.C.isMu0 j).triv.mul (hL.xi_triv t)).mul (G.ch.triv _ hm.1 hm.2).inv
    rw [nuH, div_eq_mul_inv]
    exact h
  have hu : ∀ w, GlobalTheory.LFun.UnrAt χ⁻¹ w ↔ (nuH G t i j)⁻¹.UnrAt w := fun w => by
    rw [GlobalTheory.UnrCharZeta.unrAt_inv, ← GlobalTheory.LFun.unrAt_iff_of_chrEq hχ w]
    exact ⟨fun h => inv_inv χ ▸ h.inv, fun h => h.inv⟩
  have hfam : GlobalTheory.LFun.charFam χ⁻¹ = GlobalTheory.LFun.heckeFam (nuH G t i j)⁻¹ := funext fun w => by
    by_cases h : (nuH G t i j)⁻¹.UnrAt w
    · rw [GlobalTheory.LFun.heckeFam_of_unrAt h, GlobalTheory.LFun.charFam, if_pos ((hu w).2 h), GlobalTheory.LFun.val_inv,
        GlobalTheory.LFun.val_eq_of_chrEq hχ, GlobalTheory.UnrCharZeta.val_inv]
    · rw [GlobalTheory.LFun.heckeFam_of_not_unrAt h, GlobalTheory.LFun.charFam, if_neg (mt (hu w).1 h)]
  have hΛ' := GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF D.host.E (nuH G t i j) Λ hT hΛ
  have hr' : ∀ w ∈ GlobalTheory.LFun.above D.host.E ((sfB G t : Finset (FinPl D)) : Set (FinPl D)),
      ¬ (nuH G t i j)⁻¹.UnrAt w := fun w hw h =>
    hram w hw ((GlobalTheory.UnrCharZeta.unrAt_inv _ w).1 h)
  have heq : GlobalTheory.Cont.EqRight Λ (GlobalTheory.LFun.charL χ⁻¹ ((sfB G t : Finset (FinPl D)) : Set (FinPl D))) := ⟨1, fun z hz => by
    change Λ z = GlobalTheory.LFun.eulerProd _ (GlobalTheory.LFun.charFam χ⁻¹) z
    rw [hfam]
    exact (GlobalTheory.SqStep.heckeL_eq_of_ram hr' hΛ' hz).symm⟩
  exact (GlobalTheory.Cont.holValueAt_self (σ := s.re - 1) (fun z _ => hΛ.1.analyticAt z) (by linarith)).congr heq

end GlobalTheory.NuOffPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareRatioValuationWithoutNormFormula
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.DivisionValues (vw)
open Formalism.PairingDivisionLocalBalance (wt HtLe)
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (IsHeckeL IsValChar beta)
open GlobalTheory.SqTop.OneSqProof

namespace GlobalTheory.SqTop.OneSqNoSmall

theorem oneSqSt_of_claims' : (∀ D, GlobalTheory.NormSum.Inp D) → LNe → TorEx → BotSmall → BotExT → NormBig → BotNe → TriEx → Tower → BotConst → Refl → RhoLow → OneSqSt := by
  intro hInp h1 h2 h3 h4 h5 h5' h6 h7 h8 h9 h10
  obtain ⟨c, hc⟩ := Model.gBig_and h1 (Model.gBig_and h2 (Model.gBig_and h3 (Model.gBig_and h4 (Model.gBig_and h5
    (Model.gBig_and h5' (Model.gBig_and h6 (Model.gBig_and h7 (Model.gBig_and h8 (Model.gBig_and h9 h10)))))))))
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ₀ hL G => ?_⟩
  obtain ⟨H1, H2, H3, H4, H5, H5', H6, H7, H8, H9, H10⟩ := h C hC D large₂ a b r T Lc μ₀ hL G
  clear h hc h1 h2 h3 h4 h5 h5' h6 h7 h8 h9 h10
  intro W S ρ hstd hnum C' μ rq zA zA' zT zTd gT ch N0 Sd Se dl Bw hThA hSq w ij

  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := Model.tower_numbers ij.1 ij.2

  have hN0 : ∀ s : ℤ, 1 ≤ s → s ≤ (halfRank D ij.1 ij.2 : ℤ) → ∀ l ∈ Sd, 0 ≤ N0 ij s l := by
    intro s h1 h2 l hl
    obtain ⟨z, -, hz⟩ := (hSq.inside ij s.toNat (by omega) (by omega)).2
    have e : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg (by omega)
    rw [e] at hz
    rw [hz l ((hSq.den l).1 hl).1]
    positivity
  have hdl : 0 ≤ dl w := by
    obtain ⟨S', del, hE, -, -, e⟩ := hSq.int
    rw [e]; exact wt_nonneg w fun l _ => hE.2.1 l
  have hEr : 0 ≤ wt Se (fun l => 1 / (l : ℝ) ^ 2) w := wt_nonneg w fun l _ => by positivity
  have hlast : 0 ≤ ((D.R.m - 1 - ij.2 : ℕ) : ℝ) * (2 * ∑ q ∈ G.pl.S0, (condExp G.pl q : ℝ) *
      (vw w (Ideal.absNorm q.asIdeal : D.what₂.LL) : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (sum_nonneg fun q _ =>
      mul_nonneg (Nat.cast_nonneg _) (GlobalTheory.Square.TwoStep.vw_natCast_nonneg w _)))
  by_cases hne : μ w = μ₀
  · rw [hne, hSq.rq_base ij, Formalism.DivisionValues.ValuationRepresentative.vw_one]
    refine ⟨one_ne_zero, ?_⟩
    have s1 : 0 ≤ ∑ s ∈ Icc (1 : ℤ) (halfRank D ij.1 ij.2), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
        |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|) := sum_nonneg fun _ _ => by positivity
    have s2 : 0 ≤ ∑ s ∈ Icc (1 : ℤ) (halfRank D ij.1 ij.2), wt Sd (N0 ij s) w := sum_nonneg fun s hs => by
      rw [mem_Icc] at hs; exact wt_nonneg w (hN0 s hs.1 hs.2)
    have s3 := mul_nonneg (Nat.cast_nonneg (2 * halfRank D ij.1 ij.2)) hEr
    rw [Int.cast_zero]
    have a1 := abs_nonneg (vw w (zA ij) : ℝ)
    have a2 := abs_nonneg (vw w (zA' ij) : ℝ)
    linarith

  · set t := μ w with ht
    obtain ⟨hQn, hThl⟩ := hThA w hne
    obtain ⟨l, hl, hlw⟩ := exists_prime_mem' w
    obtain ⟨HL1, HL2⟩ := H1 ij.1 ij.2
    obtain ⟨Λ, hΛ, hΛne⟩ := HL1 t
    obtain ⟨Λ₀, hΛ₀, hΛ₀ne⟩ := HL1 μ₀
    obtain ⟨Λd, hΛd, hΛdne⟩ := HL2 (some (ch w))
    have hΛd' : IsHeckeL (nuH G μ₀ ij.1 ij.2 * Lc.C.delAt l) Λd := by
      rw [← hSq.delOf_ch hl hlw]; exact hΛd
    have hTd : ∀ s : ℕ, 1 ≤ s → s ≤ halfRank D ij.1 ij.2 →
        D.what₂.embLL (zTd ij (ch w) s) * Λ₀ s = Λd s ∧ Λd s ≠ 0 := by
      intro s h1' h2'
      obtain ⟨x, hx, hx0, hxc, -⟩ := (hSq.inside ij s h1' h2').1
      obtain ⟨y, hy, hy0, hyΛ, -⟩ := H2 ij.1 ij.2 s h1' h2' none
      obtain ⟨y', hy', hy'0, hy'Λ, -⟩ := H2 ij.1 ij.2 s h1' h2' (some (ch w))
      have e1 : x = y := hx.2.unique hy.2
      have e2 : D.what₂.embLL (zTd ij (ch w) s) * x = y' := (hxc (ch w)).2.unique hy'.2
      rw [← hyΛ Λ₀ hΛ₀, ← hy'Λ Λd hΛd, ← e1]
      exact ⟨e2, e2 ▸ hy'0⟩
    have hzψ : ∀ s : ℤ, ∃ z : D.what₂.LL, 1 ≤ s → s ≤ (halfRank D ij.1 ij.2 : ℤ) →
        D.what₂.embLL z * Λ₀ s = Λ s := by
      intro s
      by_cases hs : 1 ≤ s ∧ s ≤ (halfRank D ij.1 ij.2 : ℤ)
      · have e : ((s.toNat : ℕ) : ℂ) = (s : ℂ) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
        have h0 : Λ₀ s ≠ 0 := hΛ₀ne s (by omega) hs.2
        obtain ⟨z, hz⟩ := hnum.ratios ij.1 ij.2 t Λ Λ₀ hΛ hΛ₀ s.toNat (by omega) (by omega) (by rw [e]; exact h0)
        refine ⟨z, fun _ _ => ?_⟩
        rw [hz, e, div_mul_cancel₀ _ h0]
      · exact ⟨0, fun h1' h2' => absurd ⟨h1', h2'⟩ hs⟩
    choose zψ hzψ using hzψ
    have hEp : ∀ s : ℤ, ∃ E : D.what₂.LL, 1 - (e0 D ij.1 ij.2 : ℤ) ≤ s → s ≤ 0 →
        GlobalTheory.Square.IsAwayUnit (Qn G t) E ∧
          Λ s * Λ₀ ((1 - s : ℤ) : ℂ) = D.what₂.embLL E * (Λ ((1 - s : ℤ) : ℂ) * Λ₀ s) := by
      intro s
      by_cases hs : 1 - (e0 D ij.1 ij.2 : ℤ) ≤ s ∧ s ≤ 0
      · obtain ⟨E, hE⟩ := H9 W S hnum ij.1 ij.2 t Λ Λ₀ hΛ hΛ₀ s hs.1 hs.2
        exact ⟨E, fun _ _ => hE⟩
      · exact ⟨0, fun h1' h2' => absurd ⟨h1', h2'⟩ hs⟩
    choose Ep hEp using hEp
    have hwSd : ∀ s, wt Sd (N0 ij s) w = N0 ij s l * (vw w (l : D.what₂.LL) : ℝ) :=
      fun s => wt_at w (fun l' hl' => ((hSq.den l').1 hl').1) hl hlw fun h => by
        by_contra h'; exact h ((hSq.den l).2 ⟨hl, ij, s, h'⟩)
    have hwSe : wt Se (fun l => 1 / (l : ℝ) ^ 2) w = 1 / (l : ℝ) ^ 2 * (vw w (l : D.what₂.LL) : ℝ) :=
      wt_at w (fun l' hl' => ((hSq.err l').1 hl').1) hl hlw fun h => absurd ((hSq.err l).2 ⟨hl, w, hne, hlw⟩) h
    have hmid : ∀ s : ℤ, 1 ≤ s → s ≤ (halfRank D ij.1 ij.2 : ℤ) → zT ij s ≠ 0 ∧ zTd ij (ch w) s ≠ 0 ∧
        D.what₂.embLL (zψ s) * Λ₀ s = D.what₂.embLL (zT ij s) * Λ s ∧
        -(wt Sd (N0 ij s) w) ≤ ((vw w (zψ s) + gT ij s w : ℤ) : ℝ) ∧
        (vw w (zψ s) : ℝ) ≤ (vw w (zTd ij (ch w) s) : ℝ) + wt Se (fun l => 1 / (l : ℝ) ^ 2) w := by
      intro s h1' h2'
      have e : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg (by omega)
      have eC : ((s.toNat : ℕ) : ℂ) = (s : ℂ) := by rw [← Int.cast_natCast, e]
      obtain ⟨hTd1, hTd2⟩ := hTd s.toNat (by omega) (by omega)
      rw [eC, e] at hTd1
      rw [eC] at hTd2
      have hψ := hzψ s h1' h2'
      have hTd0 : zTd ij (ch w) s ≠ 0 := fun h0 => hTd2 (by rw [← hTd1, h0, map_zero, zero_mul])
      have hψ0 : zψ s ≠ 0 := fun h0 => hΛne s (by omega) h2' (by rw [← hψ, h0, map_zero, zero_mul])
      refine ⟨by rw [hSq.base]; exact one_ne_zero, hTd0, by rw [hSq.base, map_one, one_mul]; exact hψ, ?_, ?_⟩
      · have hin := hSq.inside ij s.toNat (by omega) (by omega)
        have := H10 ij.1 ij.2 s.toNat (by omega) (by omega) t Λ Λ₀ (zψ s) _ _ _ hΛ hΛ₀ (by rw [eC]; exact hψ)
          hin.1 hin.2 w l hl hlw hQn
        rw [e] at this
        rw [hwSd]; exact this
      · have hz := hThl l hl hlw ij.1 ij.2 s.toNat Λ Λd (zψ s / zTd ij (ch w) s) (by omega) (by omega) hΛ hΛd' (by
          rw [eC, ← hTd1, ← hψ, map_div₀]; field_simp [(map_ne_zero _).2 hTd0])
        have hv := Formalism.DivisionValues.ValuationRepresentative.vw_mul w (zψ s / zTd ij (ch w) s) (zTd ij (ch w) s) (div_ne_zero hψ0 hTd0) hTd0
        rw [div_mul_cancel₀ _ hTd0] at hv
        rw [hwSe, hv]
        have : (vw w (l : D.what₂.LL) : ℝ) / (l : ℝ) ^ 2 = 1 / (l : ℝ) ^ 2 * (vw w (l : D.what₂.LL) : ℝ) := by ring
        push_cast
        linarith
    obtain ⟨rr, hr1, hr2, hr3⟩ := GlobalTheory.Square.Ratio.exists_ratios D.what₂.LL D.what₂.embLL w (Qn G t) hQn
      (e0 D ij.1 ij.2) (halfRank D ij.1 ij.2) (by omega) (fun s => Λ₀ s) (fun s => Λ s) (zT ij) (zTd ij (ch w)) zψ Ep
      (fun s => gT ij s w) (fun s => wt Sd (N0 ij s) w) (wt Se (fun l => 1 / (l : ℝ) ^ 2) w)
      (fun s h1' h2' => ⟨hΛ₀ne s h1' h2', hΛne s h1' h2'⟩) hmid (fun s h1' h2' => hEp s h1' h2')

    have hrat : ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D ij.1 ij.2 → Λ (n : ℂ) / Λ₀ (n : ℂ) = D.what₂.embLL (rr n) := by
      intro n h1' h2'
      have := (hr1 n (by omega) (by omega)).2
      have h0 := hΛ₀ne n (by omega) (by omega)
      simp only [Int.cast_natCast] at this h0
      rw [← this, mul_div_cancel_right₀ _ h0]
    obtain ⟨cf, hcf0, hcf⟩ := hSq.ratio ij
    obtain ⟨sn, sc, hrq⟩ := hcf t (Or.inr ⟨w, ht.symm⟩)
    obtain ⟨sn₀, sc₀, -⟩ := hcf μ₀ (Or.inl rfl)
    obtain ⟨A₁, A₁', WW, X, c0, hX, hXc⟩ := H6 W hstd ij.1 ij.2
    obtain ⟨u, hu, ζ, hζ, hT⟩ := H7 W S ρ hstd hnum ij.1 ij.2 t (cf t) (cf μ₀) A₁ A₁' WW X c0 Λ Λ₀ sn sc sn₀ sc₀ hX hXc
      hΛ hΛ₀
    obtain ⟨δ, t0, hN⟩ := hSq.norms
    obtain ⟨P₀, P₀', hB₀, hzA, hzA'⟩ := hN ij
    obtain ⟨P, P', hB⟩ := H4 δ t0 (levQ G.pl) P₀ t ij.1 ij.2
    have hmod : modT G μ₀ = SqNum.condE G.pl := (Model.base_tuple G hL).2.2
    have hB₀' : IsBottom G μ₀ ij.1 ij.2 (modT G μ₀) P₀ P₀' := by rw [hmod]; exact hB₀
    obtain ⟨A, hA, hNA⟩ := H5 δ t0 ij.1 ij.2
    have eP := hNA t _ P P' Λ hB hΛ
    have eP₀ := hNA μ₀ _ P₀ P₀' Λ₀ hB₀' hΛ₀
    have hIcc : ∀ s ∈ Icc (1 - (e0 D ij.1 ij.2 : ℤ)) (h0 D ij.1 ij.2 : ℤ),
        1 - (e0 D ij.1 ij.2 : ℤ) ≤ s ∧ s ≤ (halfRank D ij.1 ij.2 : ℤ) := fun s hs => by
      rw [mem_Icc] at hs; omega
    set z : D.what₂.LL := zA ij * ∏ s ∈ Icc (1 - (e0 D ij.1 ij.2 : ℤ)) (h0 D ij.1 ij.2 : ℤ), rr s with hzdef
    have hz : D.what₂.embLL z = (P.norm : ℂ) := by
      rw [eP, hzdef, map_mul, hzA, eP₀, map_prod, mul_assoc, ← prod_mul_distrib]
      congr 1
      refine prod_congr rfl fun s hs => ?_
      obtain ⟨a1, a2⟩ := hIcc s hs
      rw [mul_comm]; exact (hr1 s a1 a2).2
    have hzne : z ≠ 0 := by
      intro h0
      have : (P.norm : ℂ) = 0 := by rw [← hz, h0, map_zero]
      rw [eP] at this
      refine mul_ne_zero hA (prod_ne_zero_iff.2 fun s hs => ?_) this
      obtain ⟨a1, a2⟩ := hIcc s hs
      exact hΛne s a1 a2
    have hzAne : zA ij ≠ 0 := by
      intro h0
      have : (P₀.norm : ℂ) = 0 := by rw [← hzA, h0, map_zero]
      rw [eP₀] at this
      refine mul_ne_zero hA (prod_ne_zero_iff.2 fun s hs => ?_) this
      obtain ⟨a1, a2⟩ := hIcc s hs
      exact hΛ₀ne s a1 a2
    have hz'ne : zA' ij ≠ 0 := by
      intro h0
      have hne' : P₀'.norm ≠ 0 := GlobalTheory.T.definiteThetaPair_norm_ne_zero_of_coord_ne_zero D (hInp D) δ t0 (levQ G.pl) P₀' (H5' δ t0 (levQ G.pl) P₀ P₀' ij.1 ij.2 hB₀).2
      have : (P₀'.norm : ℂ) = 0 := by rw [← hzA', h0, map_zero]
      exact hne' (by exact_mod_cast this)
    obtain ⟨γ, hγ0, hc00, hγc, hγv⟩ := H8 W S hstd hnum ij.1 ij.2 t A₁ A₁' WW X c0 δ t0 P₀ P₀' P P' z (zA' ij) C' dl
      hX hXc hB₀ hB hz hzA' hzne hz'ne hSq.int
    have hS0 : ∀ v ∈ G.pl.S0, 0 < Ideal.absNorm v.asIdeal := fun v _ =>
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
    have htk := fun k => GlobalTheory.Square.stepRatio_vw_bound D.what₂.LL D.what₂.embLL w (Qn G t) hQn _ G.pl.S0
      (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) hS0 (u k) 1 (hu k)
    choose tk htk0 htku htkv using htk
    obtain ⟨hζ0, hζv⟩ := hζ.ne_zero_and_vw w hQn

    have hq' : ∏ k ∈ range (qq D ij.2), Λ ((eTop D ij.1 ij.2 + k + 1 : ℕ) : ℂ) / Λ₀ ((eTop D ij.1 ij.2 + k + 1 : ℕ) : ℂ) =
        D.what₂.embLL (∏ k ∈ range (qq D ij.2), rr ((eTop D ij.1 ij.2 : ℤ) + k + 1)) := by
      rw [map_prod]
      refine prod_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      rw [hrat _ (by omega) (by omega)]
      push_cast; rfl
    have hp' : ∏ k ∈ range (pp D ij.2), Λ ((eTop D ij.1 ij.2 + qq D ij.2 - k : ℕ) : ℂ) /
        Λ₀ ((eTop D ij.1 ij.2 + qq D ij.2 - k : ℕ) : ℂ) =
        D.what₂.embLL (∏ k ∈ range (pp D ij.2), rr ((eTop D ij.1 ij.2 : ℤ) + qq D ij.2 - k)) := by
      rw [map_prod]
      refine prod_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      rw [hrat _ (by omega) (by omega)]
      rw [Nat.cast_sub (by omega)]
      push_cast; rfl
    have hc0 : cf μ₀ ≠ 0 := hcf0
    have e1 : cf t / cf μ₀ = D.what₂.embLL (rq t ij) := by rw [← hrq, mul_div_cancel_right₀ _ hc0]
    have e2 : c0 t / c0 μ₀ = D.what₂.embLL γ := by rw [← hγc, mul_div_cancel_right₀ _ hc00]
    have e3 : ∏ k, u k = D.what₂.embLL (∏ k, tk k) := by
      rw [map_prod]; exact prod_congr rfl fun k _ => by rw [htku k, mul_one]
    rw [e1, e2, e3, hq', hp'] at hT
    have heqLL : rq t ij * ∏ k ∈ range (qq D ij.2), rr ((eTop D ij.1 ij.2 : ℤ) + k + 1) =
        ζ * (∏ k, tk k) * γ * ∏ k ∈ range (pp D ij.2), rr ((eTop D ij.1 ij.2 : ℤ) + qq D ij.2 - k) := by
      apply D.what₂.embLL.injective
      simp only [map_mul]
      exact hT
    have key := vw_ratio_le w (eTop D ij.1 ij.2) (pp D ij.2) (qq D ij.2) (e0 D ij.1 ij.2) (h0 D ij.1 ij.2) n1 n5.le
      (rq t ij) ζ γ (zA ij) (zA' ij) tk rr
      (fun s => |((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| + |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)
      (fun s => wt Sd (N0 ij s) w) (wt Se (fun l => 1 / (l : ℝ) ^ 2) w) (dl w)
      (2 * ∑ v ∈ G.pl.S0, (condExp G.pl v : ℝ) * (vw w (Ideal.absNorm v.asIdeal : D.what₂.LL) : ℝ))
      heqLL (fun s h1' h2' => (hr1 s h1' (by rw [n2]; push_cast; omega)).1) ⟨hζ0, hζv⟩ (fun k => ⟨htk0 k, htkv k⟩)
      hγ0 hzAne (hγv w hQn) hEr (fun s h1' h2' => by
        have h2'' : s ≤ (halfRank D ij.1 ij.2 : ℤ) := by rw [n2]; push_cast; omega
        obtain ⟨b1, b2⟩ := hr2 s h1' h2''
        refine ⟨by positivity, wt_nonneg w (hN0 s h1' h2''), b1, ?_⟩
        have := abs_nonneg ((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)
        linarith) hr3
    rw [n2, ← n3]
    exact key

end GlobalTheory.SqTop.OneSqNoSmall

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairMemSchwartzBruhatOfConductorExponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

namespace GlobalTheory.StdPairSBDepth

open GlobalTheory.StdPairSB GlobalTheory.StdPairCone ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gfun_eq_mul (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n c : ℕ) {m r : ℕ} (A : Matrix (Fin m) (Fin m) k)
    (B : Matrix (Fin m) (Fin r) k) :
    gfun ν ϖ c A B = gfun ν ϖ n A (0 : Matrix (Fin m) (Fin r) k) * gfun 1 ϖ c A B := by
  have h0 : ∀ (i : Fin m) (j : Fin r),
      (0 : Matrix (Fin m) (Fin r) k) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ n) := by
    intro i j
    simp [GlobalTheory.SplitWeil.cball]
  unfold gfun
  by_cases h : A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
  · rw [dif_pos h, dif_pos h, dif_pos ⟨h.1, h.2.1, h0⟩]
    simp
  · rw [dif_neg h, dif_neg h, mul_zero]

theorem isLocallyConstant_gfun' {ν : kˣ →* ℂˣ} {ϖ : kˣ} {n : ℕ} (c : ℕ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ n ν) (m r : ℕ) :
    IsLocallyConstant
      (fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k => gfun ν ϖ c q.1 q.2) := by
  have h1 := (isLocallyConstant_gfun hϖ hν m r).comp_continuous
    (f := fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k =>
      (q.1, (0 : Matrix (Fin m) (Fin r) k))) (continuous_fst.prodMk continuous_const)
  have h2 := isLocallyConstant_gfun (ν := (1 : kˣ →* ℂˣ)) (c := c) hϖ (fun _ _ => rfl) m r
  have h3 := h1.mul h2
  convert h3 using 1
  funext q
  exact gfun_eq_mul ν ϖ n c q.1 q.2

end GlobalTheory.StdPairSBDepth

open GlobalTheory.StdPairCone ValuativeRel in

theorem GlobalTheory.StdPairSBDepth.stdPair_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n c a a' : ℕ), IsUnif ϖ → CondLE ϖ n ν →
      GlobalTheory.StdPairCone.stdA ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧
        GlobalTheory.StdPairCone.stdB ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) := by
  intro k _ _ _ _ ν ϖ n c a a' hϖ hν
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc1 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₁ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.castAdd a' j)
  have hc2 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₂ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.natAdd a j)
  have hK : ∀ m : ℕ, IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin (a + a') => (𝒪[k] : Set k) :
      Set (Matrix (Fin m) (Fin (a + a')) k)) :=
    fun m => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int k
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : stdA ν ϖ c a a' = (fun q => GlobalTheory.StdPairSB.gfun ν ϖ c q.1 q.2) ∘ fun X => (blk₁ X, blk₂ X) := rfl
    rw [this]
    exact (GlobalTheory.StdPairSBDepth.isLocallyConstant_gfun' c hϖ hν a a').comp_continuous ((hc1 a).prodMk (hc2 a))
  · refine HasCompactSupport.intro (hK a) fun X hX => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := GlobalTheory.StdPairSB.integral_of_ne (A := blk₁ X) (B := blk₂ X) hϖ hne
    exact hX fun i _ j _ => Fin.addCases (motive := fun j => X i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
  · have : stdB ν ϖ c a a' = (fun q => GlobalTheory.StdPairSB.gfun ν ϖ c q.1 q.2) ∘ fun Y => (blk₂ Y, blk₁ Y) := rfl
    rw [this]
    exact (GlobalTheory.StdPairSBDepth.isLocallyConstant_gfun' c hϖ hν a' a).comp_continuous ((hc2 a').prodMk (hc1 a'))
  · refine HasCompactSupport.intro (hK a') fun Y hY => ?_
    by_contra hne
    obtain ⟨h2, h1⟩ := GlobalTheory.StdPairSB.integral_of_ne (A := blk₂ Y) (B := blk₁ Y) hϖ hne
    exact hY fun i _ j _ => Fin.addCases (motive := fun j => Y i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfMemDualWeylLatticeStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalDegree_le_of_mem_dualWeylLattice : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O), f ∈ dualWeyl O N N ν → f.totalDegree ≤ ∑ a, ν a := by
  first | exact @GlobalTheory.DualWeylDeg.totalDegree_le_of_mem_dualWeyl | exact GlobalTheory.DualWeylDeg.totalDegree_le_of_mem_dualWeyl | (intros; apply GlobalTheory.DualWeylDeg.totalDegree_le_of_mem_dualWeyl <;> assumption)
end

