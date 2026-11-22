import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0799
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0800
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0801
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0576
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0651
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0622

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelThirdStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspFun_theta_integral_of_integrableOn : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → IsCuspFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  first | exact @GlobalTheory.ThLiftCusp.thetaLift_isCuspFun | exact GlobalTheory.ThLiftCusp.thetaLift_isCuspFun | (intros; apply GlobalTheory.ThLiftCusp.thetaLift_isCuspFun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrandSupportedOnCellsLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

theorem biInv_eq_of_cells {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)]
    {R K : ∀ i, Subgroup (H i)} {q : (∀ i, H i) → ℂ} :
    ∀ (l : List ι), BiInv R K l q → ∀ h h' : (∀ i, H i), (∀ i, i ∉ l → h i = h' i) →
      (∀ i ∈ l, ∃ r ∈ R i, ∃ k ∈ K i, h i = r * h' i * k) → q h = q h'
  | [], _, h, h', h1, _ => by
      have : h = h' := funext fun i => h1 i List.not_mem_nil
      rw [this]
  | i :: l, hq, h, h', h1, h2 => by
      obtain ⟨r, hr, k, hk, e⟩ := h2 i List.mem_cons_self
      have hq' : BiInv R K l q := fun j hj => hq j (List.mem_cons_of_mem _ hj)
      set h₁ := Function.update h i (h' i) with hh₁
      have hi₁ : h₁ i = h' i := by simp [hh₁]
      have step1 : q h = q h₁ := by
        have a1 := (hq i List.mem_cons_self (Function.update h₁ i (h' i * k))).1 r hr
        have a2 := (hq i List.mem_cons_self h₁).2 k hk
        simp only [Function.update_self, Function.update_idem] at a1
        rw [hi₁] at a2
        have hh : h = Function.update h₁ i (r * (h' i * k)) := by
          funext j
          by_cases hj : j = i
          · subst hj; simp [e, mul_assoc]
          · simp [hh₁, Function.update_of_ne hj]
        rw [hh, a1, a2]
      rw [step1]
      refine biInv_eq_of_cells l hq' h₁ h' (fun j hj => ?_) (fun j hj => ?_)
      · by_cases hji : j = i
        · subst hji; exact hi₁
        · rw [hh₁, Function.update_of_ne hji]
          exact h1 j (by simp [hji, hj])
      · by_cases hji : j = i
        · subst hji; exact ⟨1, one_mem _, 1, one_mem _, by simp [hi₁]⟩
        · rw [hh₁, Function.update_of_ne hji]
          exact h2 j (List.mem_cons_of_mem _ hj)

theorem zero_not_mem_idx (D : D7) : 0 ∉ idx D := by simp [idx, List.mem_range']; intro x _; omega

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem evT_eq_zero_of (C : BiFam ch.G) (j : ℕ) (hj : Even j) (hjm : j < D.R.m) (hC : C j = 0) (f : SchRow ch.G)
    (u : ColPt ch.G) (y : RowPt ch.G) : evT C f u y = 0 := by
  obtain ⟨k, rfl⟩ := hj
  obtain ⟨c, hc⟩ := D.R.m_even
  unfold evT
  rw [Finset.prod_eq_zero (i := k) (by simp [Finset.mem_range]; omega) (by rw [two_mul, hC]; rfl), zero_mul]

end
end GlobalTheory.RowVal

namespace GlobalTheory.RowVal
section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem suppOn_of_cover (s : ℤˣ) (hC : CoverAt ch s) (hF : FlatAt ch s) (hO : OffAt ch) (hI : InvAt ch) (hT : TensAt ch)
    (hB : BasicAt ch) : SuppOn ch s := by
  intro t a τ hτ M hM P y b hb h h1 hne
  obtain ⟨hφ, hFt, hHaar, -, hGood, -, -⟩ := hB
  have hsum : ∀ h' : Pts ch.G, tot ch.W hM P τ (colFn ch a) (formTop ch t y) h' = ∑ d ∈ τ.support,
      τ d * per ch.W M t (conAt ch.W hM (fockD ch.W t d.2 P.2) h') d.1 P.1 (colFn ch a) (formTop ch t y) := fun _ => rfl
  have hne' := hne
  rw [hsum] at hne'
  obtain ⟨d, hd, hdne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
  have hper := right_ne_zero_of_mul hdne
  have hnz : ∀ j, Even j → j < D.R.m → conAt ch.W hM (fockD ch.W t d.2 P.2) h j ≠ 0 := by
    intro j hj hjm h0
    apply hper
    have := hT t M (hHaar t M hM) _ _ (hφ a) (hFt t y) Unit {()} (fun _ => 1)
      (fun _ => conAt ch.W hM (fockD ch.W t d.2 P.2) h) (fun _ => d.1)
      (fun _ _ => hGood t _ τ hτ M hM d hd P.2 h)
      (fun u y' => by simp [evT_eq_zero_of ch _ j hj hjm h0]) P.1
    simpa using this
  have h0 : h 0 = 1 := h1 0 (zero_not_mem_idx D)
  obtain ⟨β, hβ⟩ := hC t b hb h (hO t _ τ hτ M hM d hd P.2 h h0 hnz)
  refine ⟨β, ?_, hβ⟩
  by_contra hns
  apply hne
  classical

  choose! r hr a' ha' k hk e using hβ
  let p : Pts ch.G := fun j => if j ∈ idx D then a' j else 1
  have hp : IsRealPt p := by
    refine ⟨fun j => ?_, fun j hj => by simp [p, hj]⟩
    by_cases hj : j ∈ idx D
    · simp only [p, if_pos hj]; exact ha' j hj
    · simp only [p, if_neg hj]; exact one_mem _
  have hmove : tot ch.W hM P τ (colFn ch a) (formTop ch t y) h = tot ch.W hM P τ (colFn ch a) (formTop ch t y) (p * b β) := by
    refine biInv_eq_of_cells (idx D) (hI t a τ hτ M hM P y) h (p * b β) (fun j hj => ?_) (fun j hj => ?_)
    · simp [p, hj, h1 j hj, (hb β).1 j hj]
    · refine ⟨r j, hr j hj, k j, hk j hj, ?_⟩
      simp only [Pi.mul_apply, p, if_pos hj, e j hj, mul_assoc]
  rw [hmove]

  have hexp : ch.S.IsExpansion t (ch.Phi a) β 0 := by
    obtain ⟨e₀, he₀, -⟩ := hτ
    refine ⟨e₀, he₀, by simp, fun x y' _ _ => ?_⟩
    rw [Finsupp.sum_zero_index]
    simp only [GridChoice.supp, Set.mem_setOf_eq, not_forall] at hns
    obtain ⟨w, hw⟩ := hns
    have hz : (ch.S.term t (ch.Phi a) β w).datum = 0 := by
      simpa [unfSupport, GridChoice.term] using hw
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ w) (by rw [hz]; rfl)
  obtain ⟨z, -, hFl⟩ := hF
  obtain ⟨Cr, -, hCr⟩ := hFl P.2 p hp
  obtain ⟨ζ, -, hz⟩ := hCr t (ch.Phi a) τ hτ M hM β (b β) (hb β) 0 (fun _ => 0) hexp (by intro d hd; simp at hd)
  rw [hsum]
  exact hT t M (hHaar t M hM) _ _ (hφ a) (hFt t y) _ τ.support (fun d => τ d)
    (fun d => conAt ch.W hM (fockD ch.W t d.2 P.2) (p * b β)) (fun d => d.1)
    (fun d hd => hGood t _ τ hτ M hM d hd P.2 _)
    (fun u y' => by simpa [Finsupp.sum] using hz u y') P.1

end

theorem big_suppOn_of_flat :
    Big fun ch => ∀ s, FlatAt ch s → OffAt ch → InvAt ch → TensAt ch → BasicAt ch → SuppOn ch s :=
  big_mono (fun ch hC s hF hO hI hT hB => suppOn_of_cover ch s (hC s) hF hO hI hT hB) GlobalTheory.T.tiltedPoints_covered_by_representativeCells

end GlobalTheory.RowVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorSquareNormEqProdLocalVolumesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelVector_squareNorm_eq_prod_localVolumes : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ), P = LevelP.ofLocal Hl cl → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → nrm2 μ 𝓧 f = (∏ PP ∈ R.Pg.attach, (Nat.card (Hl PP) : ℝ) * ((Nat.card (kP PP.1) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹) * ∏ PP ∈ R.Q t, (Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) * ((Nat.card (kP PP) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹ := by
  first | exact @GlobalTheory.LevelVecNorm.levelVector_squareNorm_eq_prod_localVolumes_alt | exact GlobalTheory.LevelVecNorm.levelVector_squareNorm_eq_prod_localVolumes_alt | (intros; apply GlobalTheory.LevelVecNorm.levelVector_squareNorm_eq_prod_localVolumes_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGlobalSumStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_maps_global_sum : GlobalTheory.Published.HoweDualityFinite → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, IsEmpty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p v φ = 0 := by
  first | exact @GlobalTheory.HoweNonsplitKer.howe_nonsplit_ker | exact GlobalTheory.HoweNonsplitKer.howe_nonsplit_ker | (intros; apply GlobalTheory.HoweNonsplitKer.howe_nonsplit_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicLiftedKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.BotDictAlg

theorem applyAt0_isAlgebraic {D : D7} {N N' : ℕ} {P : MvPolynomial (GL3Theta.Idx D N N') ℂ} {G : TaylorLogMetric.VC D N N' → ℂ}
    (hP : ∀ α, IsAlgebraic ℚ (P.coeff α)) (hG : TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar) : IsAlgebraic ℚ (GL3Theta.applyAt0 D P G) := by
  rw [← mem_algebraicClosure_iff]
  unfold GL3Theta.applyAt0
  refine sum_mem fun α _ => mul_mem (mul_mem ((mem_algebraicClosure_iff).2 (hP α)) ?_) (hG α)
  exact prod_mem fun _ _ => natCast_mem _ _

theorem even_bot {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) : Even (A'.rank * WW.rank) := by
  refine Even.mul_left ?_ _
  have h1 := hX.rank
  have h2 := hX.rank'
  have h3 := hX.is.rank
  have h4 := SqNum.ranks_exact D i j
  rw [← h3, h1, h2]
  refine ⟨SqNum.halfRank D i j - (D.R.m - (j.1 + 1)) / 2 - (D.R.m - j.1) / 2, ?_⟩
  omega

theorem kernel_div_period_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ n : D.what₂.Tau → ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ U : GlobalTheory.NormSum.Tup D A'.rank WW.rank n,
      IsAlgebraic ℚ (X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D U) h x / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX n
  obtain ⟨Ω, hΩ, H⟩ := GlobalTheory.T.period_algebraic_ideal_expansion hP hI hL hX n
  refine ⟨Ω, hΩ, fun t x hx h hh U => ?_⟩
  obtain ⟨cc, δ, t0, e0, k, c, s, hc, ht0, he0, hca, hs, hU⟩ := H t x hx h hh
  obtain ⟨Q, hQ, heq⟩ := hU U
  rw [heq, mul_div_cancel_left₀ _ hΩ]
  refine applyAt0_isAlgebraic hQ ?_
  exact ((hI D).alg cc δ hc t0 ht0 A'.rank WW.rank (StandardLatticesGL3.stdL D A'.rank) (StandardLatticesGL3.stdL D WW.rank)
    (GlobalTheory.MovedVacuum.sd_stdL D _) (GlobalTheory.MovedVacuum.sd_stdL D _) (even_bot hX) e0 he0.2.2.2.1).2.2.1 k c s
    (fun l => (mem_algebraicClosure_iff).2 (hca l)) hs

end GlobalTheory.BotDictAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticesDifferentiableOperatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattices_differentiable_operator : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (p : Pair _), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ∃ (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.pS p).rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.pT p).rank → D.host.E)) (κ : ℂ), SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → EqAt D q Ls (stdL D _) ∧ EqAt D q Lt (stdL D _) ∧ ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧ ∀ (k : ℕ), 0 < k → ∀ w : WO (ch.G.pS p) (ch.G.pT p), k • w ∈ latO (ch.G.pS p) (ch.G.pT p) (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True) → ∃ (ζ : Qbar) (s : VC D (ch.G.pS p).rank (ch.G.pT p).rank), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ k • s ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt ∧ ∀ mon, jetTab ch.W ch.S.N.frC p (heisO ch.W.ψ (ch.G.pS p) (ch.G.pT p) w (ch.S.Z.vac p)) (x * ch.S.N.u _) (y * ch.S.N.u _) mon = ch.S.Z.c0 p * opp p (((mon.mapDomain (fvar ch.G p)).prod fun v e => period ch.S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar ch.G p)) 1) fun z => κ * ((ζ : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) s (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) z)) := by
  first | exact @GlobalTheory.MovedDict.jets_moved | exact GlobalTheory.MovedDict.jets_moved | (intros; apply GlobalTheory.MovedDict.jets_moved <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaExpansionRationalCoeffsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_expansion_rational_coeffs : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (γ, γ') X.vac = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  first | exact @GlobalTheory.RatMovedAlg.rat_algComb | exact GlobalTheory.RatMovedAlg.rat_algComb | (intros; apply GlobalTheory.RatMovedAlg.rat_algComb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExistsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_frame_base_exists : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
      ∃ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
        (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
        (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
        (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' ∧
        GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) ∧
        GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) := by
  first | exact @GlobalTheory.TripleDarboux.exists_reading | exact GlobalTheory.TripleDarboux.exists_reading | (intros; apply GlobalTheory.TripleDarboux.exists_reading <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedIntegrandBiInvariantLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolded_integrand_biInvariant_large_depth : Big fun ch => InvAt ch := by
  first | exact @GlobalTheory.RowInv.main | exact GlobalTheory.RowInv.main | (intros; apply GlobalTheory.RowInv.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaRealUpToTwistLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolded_vacua_real_up_to_twist_large_depth : Big fun ch => VacAt ch := by
  first | exact @GlobalTheory.RowVal.OneVac.big_vacAt | exact GlobalTheory.RowVal.OneVac.big_vacAt | (intros; apply GlobalTheory.RowVal.OneVac.big_vacAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSplitSupport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

namespace GlobalTheory.MovedAlg

theorem suppSplit_algComb : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ), 0 < N → ∀ g ∈ GfC A, ∀ g' ∈ GfC WW,
      GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N ((finHom A) g : Matrix (Fin A.rank) (Fin A.rank) _) →
      GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N ((finHom WW) g' : Matrix (Fin WW.rank) (Fin WW.rank) _) →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (g, g') X.vac = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX t N hN g hg g' hg' hs hs'
  have hψ : ∀ u v : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (W.ψ (symplOH (GlobalTheory.Grid.neg A) WW u v)) := fun u v hu hv =>
    GlobalTheory.T.isAlgebraic_stdChar_halfSymplectic_realPart_zero hX.is.isVac.1 _ _ u v hu hv
  have hmul : ∀ p q : GA D A × GA D WW, IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t p X.vac) →
      IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t q X.vac) →
      IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (p * q) X.vac) := by
    rintro ⟨x, h⟩ q hp hq
    rw [map_mul, Module.End.mul_apply]
    exact om_algComb hX hψ t x h hp hq
  have hone : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t 1 X.vac) := by
    rw [map_one, Module.End.one_apply]
    refine ⟨1, fun _ => 1, fun _ => 0, fun _ => isAlgebraic_one, fun _ => by simp, ?_⟩
    simp [GlobalTheory.SplitScalar.heisO_zero]
  have hW : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, g') X.vac) :=
    GlobalTheory.T.unitary_induction_on_splitPlaceSupport WW N (fun h => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, h) X.vac)) hone
      (fun x y hx hy => by simpa using hmul _ _ hx hy)
      (fun e P hP' hN' x hx hsx => GlobalTheory.T.theta_local_support_idempotent hP hI hL hX t N e P hP' hN' x hx hsx) g' hg' hs'
  have hA : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (g, 1) X.vac) :=
    GlobalTheory.T.unitary_induction_on_splitPlaceSupport A N (fun x => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (x, 1) X.vac)) hone
      (fun x y hx hy => by simpa using hmul _ _ hx hy)
      (fun e P hP' hN' x hx hsx => GlobalTheory.T.theta_local_support_source hP hI hL hX t N e P hP' hN' x hx hsx) g hg hs
  have := hmul _ _ hA hW
  simp only [Prod.mk_mul_mk, mul_one, one_mul] at this
  exact this

end GlobalTheory.MovedAlg

end
end

