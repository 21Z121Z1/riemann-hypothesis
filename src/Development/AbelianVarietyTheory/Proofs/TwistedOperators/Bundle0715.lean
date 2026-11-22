import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0360
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0707
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2057
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0333
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0711
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0709
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0579
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0708
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0560

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicDataUnitaryRelationsFinitePlacePolZero
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem RelV.exists_decomp_of_mem_algD {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, EmbOver E w) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb) :
    ∃ (T : Finset (Pl F)) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = M.vac v) ∧ Φ = ∑ i, pure (f i) (φ i) := by
  classical
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hx
    refine ⟨(Filter.eventually_cofinite.1 hev).toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hSB, fun v hv => ?_⟩, ?_⟩
    · by_contra hc
      exact hv ((Set.Finite.mem_toFinset _).2 hc)
    · simp
  | zero => exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, m₁, f₁, φ₁, h₁, rfl⟩ := hx
    obtain ⟨T₂, m₂, f₂, φ₂, h₂, rfl⟩ := hy
    refine ⟨T₁ ∪ T₂, m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, fun k => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · simp only [Fin.append_left]
        exact ⟨(h₁ i).1, (h₁ i).2.1, fun v hv => (h₁ i).2.2 v fun h => hv (Finset.mem_union_left _ h)⟩
      · simp only [Fin.append_right]
        exact ⟨(h₂ i).1, (h₂ i).2.1, fun v hv => (h₂ i).2.2 v fun h => hv (Finset.mem_union_right _ h)⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
    obtain ⟨T, m, f, φ, h, rfl⟩ := hx
    refine ⟨T, m, fun i => c • f i, φ, fun i => ⟨(M.Pol ψ emb).smul_mem c (h i).1, (h i).2.1, (h i).2.2⟩, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]

theorem RelV.pure_neg {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure (-f) φ = -pure f φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.neg_apply, Pi.neg_apply, neg_mul]

theorem polZero_relV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin F v),
    ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (g, 1) Φ - Φ) := by
  classical
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v g hg Φ hΦ
  obtain ⟨T₀, m, f, φ, hφ, rfl⟩ := RelV.exists_decomp_of_mem_algD G.M Bs.ψ Bs.emb hΦ
  have hT := hM.triple
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := by
    intro u _
    show u • ((1 : Matrix _ _ _) - 1) = 0
    simp
  choose ψ hψ using fun i => GlobalTheory.ThK.LocalOps.acts_exists hP v (g, 1) hg h1W (φ i v) ((hφ i).2.1 v)
  have hpv : ∀ i, Rf.p v (ψ i) = Rf.p v (φ i v) := by
    intro i
    have hmem : ψ i - φ i v ∈ augAt om v :=
      Submodule.subset_span ⟨g, hg, φ i v, (hφ i).2.1 v, ψ i, (hψ i).1, (hψ i).2, rfl⟩
    have := hM.fin.inv v hmem
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  have hstd : ∀ i, ∀ᶠ w in Filter.cofinite, φ i w = Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1 := by
    intro i
    have e0 : ∀ᶠ w in Filter.cofinite, φ i w = G.M.vac w :=
      Filter.eventually_cofinite.2 ((T₀.finite_toSet).subset fun w hw => by
        by_contra hc; exact hw ((hφ i).2.2 w hc))
    filter_upwards [e0, hT.geo.hM.std] with w e1 e2
    rw [e1, e2]
  set T : Finset (Pl F) := insert v (Xc.T ∪ T₀) with hTdef
  have hvT : ∀ w, w ∉ T → w ≠ v := fun w hw e => hw (e ▸ Finset.mem_insert_self _ _)
  have hT₀ : ∀ w, w ∉ T → w ∉ T₀ := fun w hw h =>
    hw (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
  refine ⟨T, fun w hw => Finset.mem_insert_of_mem (Finset.mem_union_left _ hw), m + m,
    Fin.append f fun i => -f i, Fin.append (fun i => Function.update (φ i) v (ψ i)) φ, fun k => ?_, ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [Fin.append_left]
      refine ⟨(hφ i).1, fun w => ?_, fun w hw => ?_⟩
      · by_cases hw : w = v
        · subst hw; rw [Function.update_self]; exact (hψ i).1
        · rw [Function.update_of_ne hw]; exact (hφ i).2.1 w
      · rw [Function.update_of_ne (hvT w hw)]; exact (hφ i).2.2 w (hT₀ w hw)
    · simp only [Fin.append_right]
      exact ⟨neg_mem (hφ i).1, (hφ i).2.1, fun w hw => (hφ i).2.2 w (hT₀ w hw)⟩
  · rw [map_sum, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, RelV.pure_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact GlobalTheory.ThK.PolMatchStep.pure_update v (om (g, 1)) (f i) (φ i) (hφ i).2.1 (hstd i) (hψ i).2
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, map_neg, TensorProduct.neg_tmul, Finset.sum_neg_distrib]
    have e : ∀ i, (fun w : T => Rf.p w (Function.update (φ i) v (ψ i) w)) = fun w : T => Rf.p w (φ i w) := by
      intro i
      funext w
      obtain ⟨w, hw⟩ := w
      by_cases hwv : w = v
      · subst hwv
        simp only [Function.update_self]
        exact hpv i
      · simp only [Function.update_of_ne hwv]
    simp only [e, add_neg_cancel]

end GlobalTheory.PolKer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArrowLocalModelMovedFramesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arrowLocalModel_movedFrames : Big fun ch => LatP ch → ChrP ch → ArrP ch := by
  first | exact @GlobalTheory.ArrowModel.arrow_model | exact GlobalTheory.ArrowModel.arrow_model | (intros; apply GlobalTheory.ArrowModel.arrow_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CarryWeilUnitaryPair
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx.CarryWeil

open GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem gram_posDef_def (G : GridData L sc) {Y : Node} (hY : DefNode D.R.m Y) (τ : D.what₂.Tau) :
    (gramAt D (G.V Y) τ).PosDef := by
  rcases Y with ⟨_ | i, j⟩ | i | j
  · obtain ⟨-, rfl⟩ := hY
    have e : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m L)
    rw [e]
    exact GlobalTheory.Hk3.StepX.gram_posDef_X τ
  · obtain ⟨hi, rfl⟩ := hY
    have hV := G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (fun j h => by cases h)
    have := hV.sigOK (tauE D τ)
    rw [hV.sig] at this
    simp only [Node.neg, Nat.sub_self, Nat.zero_div] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  · exact hY.elim
  · have hV := G.isV (X := .top j) hY (fun j h => by cases h)
    have := hV.sigOK (tauE D τ)
    rw [hV.sig] at this
    simp only [Node.neg] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem cart_def (G : GridData L sc) (W : G.Weil) {Y : Node} (hY : DefNode D.R.m Y) : W.cart Y = fun _ => 1 := by
  funext τ
  have hr : Y.InRange D.R.m := by
    rcases Y with ⟨i, j⟩ | i | j <;> simp only [DefNode, Node.InRange] at hY ⊢ <;> omega
  have hpos := gram_posDef_def G hY τ
  exact GlobalTheory.StdUnn.isCartanInv_eq_of_commute _ _ _ _ (W.cart_is Y hr τ) ⟨Matrix.mul_one 1, by simp, by simpa using hpos⟩
    (by simp)

theorem heq_one {V V' : HSp D} (h : V' = V) :
    HEq (fun _ : D.what₂.Tau => (1 : Matrix (Fin V'.rank) (Fin V'.rank) ℂ))
      (fun _ : D.what₂.Tau => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) := by
  subst h; rfl

theorem attChr_congr {C : Type} [CommGroup C] {a a' b b' : C} {n n' : ℕ} (h1 : a = a') (h2 : b = b') (h3 : n = n') :
    Formalism.IndefR.Lift.attChr a b n = Formalism.IndefR.Lift.attChr a' b' n' := by
  subst h1 h2 h3; rfl

section Transport

open GlobalTheory.Mem

theorem exists_om_tr {X X' : Stages} (h : X'.B.toPre = X.B.toPre) {ψ : AddChar (AF X.toD7.host.F) ℂ} {S T : HSp X.toD7}
    {χS χT : (AE X.toD7)ˣ →* Circle} {ω : GA X.toD7 S × GA X.toD7 T →* Module.End ℂ (WO S T → ℂ)}
    {ψ' : AddChar (AF X'.toD7.host.F) ℂ} {S' T' : HSp X'.toD7} {χS' χT' : (AE X'.toD7)ˣ →* Circle}
    (hψ : HEq ψ' ψ) (hS : HEq S' S) (hT : HEq T' T) (h1 : HEq χS' χS) (h2 : HEq χT' χT)
    (hw : IsWeilDatumO ψ S T χS χT ω) :
    ∃ ω' : GA X'.toD7 S' × GA X'.toD7 T' →* Module.End ℂ (WO S' T' → ℂ), IsWeilDatumO ψ' S' T' χS' χT' ω' ∧ HEq ω' ω := by
  obtain ⟨B, C, Wr, V, Sg, N, Gj⟩ := X
  obtain ⟨B', C', Wr', V', Sg', N', Gj'⟩ := X'
  cases B; cases B'
  dsimp only at h
  subst h
  obtain rfl := eq_of_heq hψ
  obtain rfl := eq_of_heq hS
  obtain rfl := eq_of_heq hT
  obtain rfl := eq_of_heq h1
  obtain rfl := eq_of_heq h2
  refine ⟨ω, ?_, HEq.rfl⟩
  exact
    { std := (by with_unfolding_all exact (hw.std :))
      hecS := (by with_unfolding_all exact (hw.hecS :))
      hecT := (by with_unfolding_all exact (hw.hecT :))
      resS := (by with_unfolding_all exact (hw.resS :))
      resT := (by with_unfolding_all exact (hw.resT :))
      om_pres := fun p f hf =>
        have r := hw.om_pres p f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
        ⟨(by with_unfolding_all exact (r.quasi :)), (by with_unfolding_all exact (r.level :)), (by with_unfolding_all exact (r.cont :)), (by with_unfolding_all exact (r.smooth :))⟩
      om_heis := fun g h w₀ f hf => hw.om_heis g h w₀ f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_aut := fun γ hγ γ' hγ' f hf => hw.om_aut γ hγ γ' hγ' f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_cont := fun f hf => hw.om_cont f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_unit := fun μ 𝓕 hμ h𝓕 p f hf => hw.om_unit μ 𝓕 hμ h𝓕 p f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_split := fun e he g h hg hh x y hx hy => by
        obtain ⟨r, hr, hℓ⟩ := hw.om_split e he g h hg hh x y hx hy
        exact ⟨r, hr, fun ℓ hℓ' f hf => hℓ ℓ (fun u hu f' hf' => hℓ' u hu f' ⟨(by with_unfolding_all exact (hf'.quasi :)), (by with_unfolding_all exact (hf'.level :)), (by with_unfolding_all exact (hf'.cont :)), (by with_unfolding_all exact (hf'.smooth :))⟩) f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩⟩ }

end Transport

end GlobalTheory.RowEx.CarryWeil

open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowEx.CarryWeil in

theorem GlobalTheory.RowEx.carryW_of_weil : GlobalTheory.Published.WeilRepresentationUnitaryPair → CarryW := by
  intro hW X X' T T' L Γ _ _ Pl0 A Ks _ _ _ R μ₀ ι hL hch hmod sc G G' hG W
  obtain ⟨W1, hW1⟩ := GlobalTheory.ChiGrid.WeilOver.exists_weil_over_of_clauses hW R hL.is' hch hmod sc G'
  have hm : X'.toD7.R.m = X.toD7.R.m := by
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    rfl
  have F1 : HEq W1.ψ W.ψ := by
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    exact heq_of_eq ((GlobalTheory.StdAdelicChar.existsUnique_isStdChar _ (-1) (Or.inr rfl)).unique W1.ψ_std ((by with_unfolding_all exact (W.ψ_std :))))
  have F2 : HEq W1.θ W.θ := by
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    exact heq_of_eq ((GlobalTheory.SmoothForms.RealPts.realPoints _).1 _ _ W1.θ_is ((by with_unfolding_all exact (W.θ_is :))))
  have F3 : ∀ Y, DefNode X'.toD7.R.m Y → HEq (W1.cart Y) (W.cart Y) := by
    intro Y hY
    rw [cart_def G' W1 hY, cart_def G W (hm ▸ hY)]
    have hV : HEq (G'.V Y) (G.V Y) := by
      rcases Y with ⟨_ | i, j⟩ | i | j
      · obtain ⟨-, rfl⟩ := hY
        have hpre := hL.pre
        obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
        obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
        cases B; cases B'
        dsimp only at hpre
        subst hpre
        exact heq_of_eq ((congrArg LSp.sp (colY_m _)).trans (congrArg LSp.sp (colY_m L)).symm)
      · exact (hG.grid i j).1
      · exact hY.elim
      · exact (hG.top j).1
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    exact heq_one (eq_of_heq hV)
  have F4 : ∀ p, DefPair X'.toD7.R.m p → ∃ ω, IsWeilDatumO W1.ψ (G'.pS p) (G'.pT p) (G'.chrS p) (G'.chrT p) ω ∧
      HEq ω (W.om (mapPair ι p)) := by
    intro p hp
    have hr : (mapPair ι p).InRange X.toD7.R.m := by
      rw [← hm]
      rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩ <;>
        simp only [DefPair, mapPair, Pair.InRange, Pair.big, Node.InRange] at hp ⊢ <;> omega
    have key : HEq (G'.pS p) (G.pS (mapPair ι p)) ∧ HEq (G'.pT p) (G.pT (mapPair ι p)) ∧
        HEq (G'.chrS p) (G.chrS (mapPair ι p)) ∧ HEq (G'.chrT p) (G.chrT (mapPair ι p)) := by
      have eta := hL.is.eta
      have eta' := hL.is'.eta
      have mu0 := hL.is.mu0
      have mu0' := hL.is'.mu0
      have xi := hL.is.xi
      have xi' := hL.is'.xi
      have hxi := hL.xi
      obtain ⟨f, f', hff, hC, hC'⟩ := hL.C
      have hpre := hL.pre
      obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
      obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
      cases B; cases B'
      dsimp only at hpre
      subst hpre
      obtain rfl := eq_of_heq hff
      rw [hC] at eta mu0
      rw [hC'] at eta' mu0'
      have eEta : R.toLevCh.eta = L.eta := (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ eta' ((by with_unfolding_all exact (eta :)))
      rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩
      · obtain ⟨hi, hj⟩ := hp
        have hS1 : G'.V (.grid (i + 1) j) = G.V (.grid (i + 1) j) := eq_of_heq (hG.grid i j).1
        have hT1 : G'.V (.grid i j) = G.V (.grid i j) := by
          cases i with
          | zero =>
            subst hj
            exact (congrArg LSp.sp (colY_m _)).trans (congrArg LSp.sp (colY_m L)).symm
          | succ k => exact eq_of_heq (hG.grid k j).1
        have ech := eq_of_heq hG.chi
        exact ⟨heq_of_eq (congrArg negSp hS1), heq_of_eq hT1,
          heq_of_eq (attChr_congr (congrFun ech _) eEta (congrArg (fun V : HSp _ => (negSp V).rank) hS1)),
          heq_of_eq (attChr_congr (congrFun ech _) eEta (congrArg (fun V : HSp _ => V.rank) hT1))⟩
      · exact hp.elim
      · exact hp.elim
      · have hj := Nat.lt_of_succ_le hp
        have emu : R.toLevCh.mu0 (j + 1) = L.mu0 (j + 1) :=
          (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ (mu0' ⟨j, hj⟩) ((by with_unfolding_all exact ((mu0 ⟨j, hj⟩) :)))
        have exi : R.toLevCh.xi t = L.xi (ι t) := by
          have h1 := xi (ι t)
          have h2 := xi' t
          rw [eq_of_heq (hxi t)] at h2
          exact (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ h2 ((by with_unfolding_all exact (h1 :)))
        have hS1 : G'.V (.top j) = G.V (.top j) := eq_of_heq (hG.top j).1
        have hT1 : G'.V (.top (j + 1)) = G.V (.top (j + 1)) := eq_of_heq (hG.top (j + 1)).1
        have emu' : R.toLevCh.mu t (j + 1) = L.mu (ι t) (j + 1) := congrArg₂ (· * ·) emu exi
        exact ⟨heq_of_eq hS1, heq_of_eq hT1,
          heq_of_eq (attChr_congr emu' eEta (congrArg (fun V : HSp _ => V.rank) hS1)),
          heq_of_eq (attChr_congr emu' eEta (congrArg (fun V : HSp _ => V.rank) hT1))⟩
    exact exists_om_tr hL.pre F1 key.1 key.2.1 key.2.2.1 key.2.2.2 (W.om_is (mapPair ι p) hr)
  have key : ∀ p : Pair T', ∃ ω, (p.InRange X'.toD7.R.m →
      IsWeilDatumO W1.ψ (G'.pS p) (G'.pT p) (G'.chrS p) (G'.chrT p) ω) ∧
      (DefPair X'.toD7.R.m p → HEq ω (W.om (mapPair ι p))) ∧ (¬ DefPair X'.toD7.R.m p → ω = W1.om p) := by
    intro p
    by_cases hp : DefPair X'.toD7.R.m p
    · obtain ⟨ω, h1, h2⟩ := F4 p hp
      exact ⟨ω, fun _ => h1, fun _ => h2, fun h => absurd hp h⟩
    · exact ⟨W1.om p, W1.om_is p, fun h => absurd h hp, fun _ => rfl⟩
  choose om hom hdef hnd using key
  refine ⟨{ W1 with om := om, om_is := hom }, ?_, F1, F2, F3, hdef⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hW1
  refine ⟨a1, a2, a3, a4, a5, a6, fun t k hk => ?_, fun t k hk => ?_⟩
  · show HEq (om (.mu t 0 k)) _
    rw [hnd (.mu t 0 k) (fun h => h)]
    exact a7 t k hk
  · show HEq (om (.mu t 0 k)) _
    rw [hnd (.mu t 0 k) (fun h => h)]
    exact a8 t k hk

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvKWithRealAll
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.RowTest.convK_withReal_all (hP : GlobalTheory.FunPr.Hypotheses₂) (hL : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal) :
    GlobalTheory.RowClaim.Big (fun ch => ∀ ρ ξ a u, GlobalTheory.RowTest.ConvK (ch.withReal ρ ξ) a u) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc ρ ξ a u => ?_⟩⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.theta_convergence_base_choice hP hL large₂ hS (ch.withReal ρ ξ) (hch.toIsBase.withReal ρ ξ) CF hsc a u
  exact ⟨h1, GlobalTheory.T.besselPeriodCorank_converges_column ch.W ch.M hch.vol ξ _ (col_mem ch a) _ h2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormFiniteDimInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KFinCuspSum

theorem eq_sum_values : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ → (∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V i j).V τ), (G.V i j).M.fr τ * g * ((G.V i j).M.fr τ)⁻¹ ∈ Formalism.REAL.Kset ((G.V i j).M.ε τ) → ∀ f ∈ W, Formalism.L2.Theta.rTr (G.V i j).V (Formalism.L2.Theta.atTau R.θ (G.V i j).V τ g) f ∈ W) → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ψ g = ∑ l, T l (v l) g := by
  intro hP D G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i j hi hj ψ hψ hW
  obtain ⟨n, F, u, hF, hsum⟩ :=
    GlobalTheory.T.cusp_form_unitary_conjugate hP R.θ (G.V i j).V (G.V i j).S (G.V i j).M hR.inf ψ hψ.1 hψ.2.1 hψ.2.2 hW
  choose Tm hTm hext using fun l =>
    GlobalTheory.T.multilinear_cusp_form_family hP R.θ (G.V i j).V (G.V i j).S (G.V i j).M hR.inf (F l) (hF l)
  choose v hv hTv using fun l => hext l (u l)
  refine ⟨n, Tm, v, hTm, fun g => ?_⟩
  rw [hsum g]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hTv l]

end GlobalTheory.KFinCuspSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColumnUnitVacuaFamilyMovedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_columnUnitVacuaFamily_moved : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∃ v, IsColVac ch v ∧ ∃ (κ : ℕ → ℂˣ) (z : T → ℕ → ℂˣ), (∀ t j, z t j ∈ xiVals R.toLevCh t) ∧ ∀ (t : T) (j : ℕ), j < D.R.m → ch.W.om (.top t j) (ch.G.toPair (.top t j) (ch.S.N.u (Pair.top t j : Pair T).small).1 (ch.S.N.u (Pair.top t j : Pair T).big).1) (ch.S.Z.vac (.top t j)) = ((κ j * z t j : ℂˣ) : ℂ) • v j := by
  first | exact @GlobalTheory.ColVac.colVac | exact GlobalTheory.ColVac.colVac | (intros; apply GlobalTheory.ColVac.colVac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPointPrescribedLocalMatricesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryPoint_prescribed_localMatrices : Big fun ch => ∀ t (j : ℕ) (hj : j ≤ _) (g : ∀ w : GlobalTheory.FunObj.locPl ch.G t, GL (Fin ((GlobalTheory.FunObj.locGrid ch.G t w.1).rank (_, j))) (GlobalTheory.FunObj.Kw w.1)), ∃ r, HasLoc t ch.S.B hj r g := by
  first | exact @GlobalTheory.RowLocBig.exists_hasLoc_big | exact GlobalTheory.RowLocBig.exists_hasLoc_big | (intros; apply GlobalTheory.RowLocBig.exists_hasLoc_big <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryDoubleStepAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatDictionary_doubleStep_at_place : Big fun ch => ChrP ch → ArrP ch → LocP ch → BesP ch → JacP ch → DblP ch := by
  first | exact @GlobalTheory.FlatPlace.dblP_big | exact GlobalTheory.FlatPlace.dblP_big | (intros; apply GlobalTheory.FlatPlace.dblP_big <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryLastTwoStepsAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatDictionary_lastTwoSteps_at_place : Big fun ch => ChrP ch → ArrP ch → LocP ch → BesP ch → JacP ch → LastP ch := by
  first | exact @GlobalTheory.FlatPlace.lastStep_eventually | exact GlobalTheory.FlatPlace.lastStep_eventually | (intros; apply GlobalTheory.FlatPlace.lastStep_eventually <;> assumption)
end

