import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} {N : GlobalTheory.FunObj.Std G U} (Z : GlobalTheory.FunObj.Normal W N) {t : T} {p : GlobalTheory.ChiGrid.Pair T}, GlobalTheory.FunObj.DefPair D.R.m p → ∀ d : GlobalTheory.FunObj.FinDatum G t p, Z.HasVec d → IsThetaFunO W.ψ (G.pS p) (G.pT p) (Z.vec d) ∧ ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) (Z.vec d) := by
  first | exact @GlobalTheory.FockRealVec.vec_theta_fock | exact GlobalTheory.FockRealVec.vec_theta_fock | (intros; apply GlobalTheory.FockRealVec.vec_theta_fock <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridPathCutAtSquareSwapRoute
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.PathCut

variable {T : Type}

def height : Node → ℤ
  | .grid i j => (i : ℤ) - j
  | _ => 0

theorem height_tgt {m : ℕ} {t : T} {a : Arrow T} (h : IsGridArrow m t a) : height a.tgt = height a.src + 1 := by
  rcases h with ⟨i, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ <;> simp [height] <;> push_cast <;> ring

theorem arrows_comp {X Y : Node} (p : Path T X Y) :
    ∀ {Z : Node} (q : Path T Y Z), (p.comp q).arrows = p.arrows ++ q.arrows
  | _, .nil => by simp [Path.comp, Path.arrows]
  | _, .snoc a q => by simp [Path.comp, Path.arrows, arrows_comp p q]

theorem onGrid_snoc {m : ℕ} {t : T} {X : Node} {a : Arrow T} {p : Path T X a.src} :
    OnGrid m t (.snoc a p) ↔ OnGrid m t p ∧ IsGridArrow m t a := by
  simp [OnGrid, Path.arrows, or_imp, forall_and]

theorem height_le {m : ℕ} {t : T} {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid m t p → height X ≤ height Y
  | _, .nil, _ => le_rfl
  | _, .snoc a p, h => by
    rw [onGrid_snoc] at h
    have := height_le p h.1
    rw [height_tgt h.2]; omega

theorem height_arrows {m : ℕ} {t : T} {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid m t p →
    ∀ b ∈ p.arrows, height X ≤ height b.src ∧ height b.tgt ≤ height Y
  | _, .nil, _, b, hb => by simp [Path.arrows] at hb
  | _, .snoc a p, h, b, hb => by
    rw [onGrid_snoc] at h
    simp only [Path.arrows, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | rfl
    · have := height_arrows p h.1 b hb
      have h2 := height_tgt h.2
      exact ⟨this.1, by omega⟩
    · exact ⟨height_le p h.1, le_rfl⟩

theorem eq_down {m : ℕ} {t : T} {a : Arrow T} (h : IsGridArrow m t a) {i j : ℕ}
    (he : edgeOf a = .theta i j) : a = .down t i j := by
  rcases h with ⟨i', j', -, -, rfl⟩ | ⟨i', j', -, -, rfl⟩
  · simp [edgeOf] at he
  · simp only [edgeOf, GlobalTheory.SplitFlip.Edge.theta.injEq] at he
    rw [he.1, he.2]

theorem eq_right {m : ℕ} {t : T} {a : Arrow T} (h : IsGridArrow m t a) {i j : ℕ}
    (he : edgeOf a = .ex i j) : a = .right i j := by
  rcases h with ⟨i', j', -, -, rfl⟩ | ⟨i', j', -, -, rfl⟩
  · simp only [edgeOf, GlobalTheory.SplitFlip.Edge.ex.injEq] at he
    rw [he.1, he.2]
  · simp [edgeOf] at he

theorem edgeOf_ne {m : ℕ} {t : T} {b : Arrow T} (hb : IsGridArrow m t b) {i j : ℕ}
    (h : height b.tgt < (i : ℤ) - j ∨ (i : ℤ) - j < height b.src) :
    edgeOf b ≠ .theta i j ∧ edgeOf b ≠ .ex i j := by
  refine ⟨fun he => ?_, fun he => ?_⟩
  · obtain rfl := eq_down hb he
    (simp [height] at h) <;> omega
  · obtain rfl := eq_right hb he
    (simp [height] at h) <;> omega

theorem infix_concat' {α : Type*} {x y z : α} {l : List α} (h : [x, y] <:+: l ++ [z]) :
    [x, y] <:+: l ∨ ∃ l', l = l' ++ [x] ∧ z = y := by
  obtain ⟨s, u, hsu⟩ := h
  rcases List.eq_nil_or_concat u with rfl | ⟨u', w, rfl⟩
  · have h1 : (s ++ [x]) ++ [y] = l ++ [z] := by simpa using hsu
    obtain ⟨h2, h3⟩ := List.append_inj' h1 rfl
    exact Or.inr ⟨s, h2.symm, (List.singleton_inj.1 h3).symm⟩
  · have h1 : (s ++ [x, y] ++ u') ++ [w] = l ++ [z] := by simpa using hsu
    obtain ⟨h2, -⟩ := List.append_inj' h1 rfl
    exact Or.inl ⟨s, u', h2⟩

theorem exists_of_last {m : ℕ} {t : T} {i j : ℕ} {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid m t p →
    ∀ l, edges p = l ++ [.theta i j] → ∃ A : Path T X (.grid i (j + 1)), HEq p (Path.snoc (.down t i j) A)
  | _, .nil, _, l, h => by simp [edges, Path.arrows] at h
  | _, .snoc a q, hp, l, h => by
    rw [onGrid_snoc] at hp
    have h2 : edgeOf a = .theta i j := by
      have := congrArg List.getLast? h
      simpa [edges, Path.arrows] using this
    obtain rfl := eq_down hp.2 h2
    exact ⟨q, HEq.rfl⟩

theorem exists_cut {m : ℕ} {t : T} {i j : ℕ} {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid m t p →
    [GlobalTheory.SplitFlip.Edge.theta i j, GlobalTheory.SplitFlip.Edge.ex i j] <:+: edges p →
    ∃ (A : Path T X (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) Y), p = (A.comp (routeSmall t i j)).comp Bp
  | _, .nil, _, h => by simp [edges, Path.arrows] at h
  | _, .snoc a q, hp, h => by
    rw [onGrid_snoc] at hp
    have he : edges (.snoc a q) = edges q ++ [edgeOf a] := by simp [edges, Path.arrows]
    rw [he] at h
    rcases infix_concat' h with h | ⟨l, hl, ha⟩
    · obtain ⟨A, Bq, rfl⟩ := exists_cut q hp.1 h
      exact ⟨A, .snoc a Bq, rfl⟩
    · obtain rfl := eq_right hp.2 ha
      obtain ⟨A, hA⟩ := exists_of_last q hp.1 l hl
      obtain rfl := eq_of_heq hA
      exact ⟨A, .nil, rfl⟩

end GlobalTheory.PathCut

namespace GlobalTheory.PathCut

theorem cut_at_square : ∀ {T : Type} (m : ℕ) (t : T) (i j : ℕ), i < m → j < m → ∀ {X Y : Node} (p : Path T X Y),
    GlobalTheory.FlipRun.OnGrid m t p → GlobalTheory.SplitFlip.PassesThrough i j (GlobalTheory.FlipRun.edges p) →
    ∃ (A : Path T X (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) Y), p = (A.comp (routeSmall t i j)).comp Bp ∧
      GlobalTheory.FlipRun.OnGrid m t A ∧ GlobalTheory.FlipRun.OnGrid m t Bp ∧
      GlobalTheory.FlipRun.OnGrid m t ((A.comp (routeBig t i j)).comp Bp) ∧
      GlobalTheory.FlipRun.edges ((A.comp (routeBig t i j)).comp Bp) = GlobalTheory.SplitFlip.flipPath i j (GlobalTheory.FlipRun.edges p) := by
  intro T m t i j hi hj X Y p hp hpass
  obtain ⟨A, Bp, rfl⟩ := exists_cut p hp hpass
  have harr : ((A.comp (routeSmall t i j)).comp Bp).arrows = A.arrows ++ [.down t i j, .right i j] ++ Bp.arrows := by
    simp [arrows_comp, Path.arrows, routeSmall, Path.one]
  have harr' : ((A.comp (routeBig t i j)).comp Bp).arrows =
      A.arrows ++ [.right i (j + 1), .down t (i + 1) j] ++ Bp.arrows := by
    simp [arrows_comp, Path.arrows, routeBig, Path.one]
  have hA : OnGrid m t A := fun b hb => hp b (by rw [harr]; simp [hb])
  have hB : OnGrid m t Bp := fun b hb => hp b (by rw [harr]; simp [hb])
  refine ⟨A, Bp, rfl, hA, hB, ?_, ?_⟩
  · intro b hb
    rw [harr'] at hb
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with (hb | rfl | rfl) | hb
    · exact hA b hb
    · exact Or.inl ⟨i, j + 1, hi, hj, rfl⟩
    · exact Or.inr ⟨i + 1, j, hi, hj, rfl⟩
    · exact hB b hb
  · unfold edges GlobalTheory.SplitFlip.flipPath
    rw [harr, harr']
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
    have hfA := fun b hb => height_arrows A hA b hb
    have hfB := fun b hb => height_arrows Bp hB b hb
    refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_
    · refine List.map_congr_left fun b hb => ?_
      have h1 : height b.tgt ≤ (i : ℤ) - ((j + 1 : ℕ) : ℤ) := (hfA b hb).2
      obtain ⟨n1, n2⟩ := edgeOf_ne (hA b hb) (i := i) (j := j) (Or.inl (by push_cast at h1; omega))
      simp only [Function.comp, if_neg n1, if_neg n2]
    · simp [edgeOf]
    · refine List.map_congr_left fun b hb => ?_
      have h1 : ((i + 1 : ℕ) : ℤ) - (j : ℤ) ≤ height b.src := (hfB b hb).1
      obtain ⟨n1, n2⟩ := edgeOf_ne (hB b hb) (i := i) (j := j) (Or.inr (by push_cast at h1; omega))
      simp only [Function.comp, if_neg n1, if_neg n2]

end GlobalTheory.PathCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobZeroNeTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
open GlobalTheory.Grow GlobalTheory.Size
open scoped ENNReal

namespace GlobalTheory.CuspApproxAll

variable {D : D7}

def avgList (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ)
    (l : List D.what₂.Tau) (φ : GA D N.V → ℂ) : GA D N.V → ℂ :=
  l.foldr (fun τ f => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (e τ) f) φ

theorem avgList_nil (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ) (φ : GA D N.V → ℂ) :
    avgList θ N e [] φ = φ := rfl

theorem avgList_cons (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ) (τ : D.what₂.Tau)
    (l : List D.what₂.Tau) (φ : GA D N.V → ℂ) :
    avgList θ N e (τ :: l) φ = GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (e τ) (avgList θ N e l φ) := rfl

theorem growthSob_zero_ne_top {θ : InfFam D} {V : HSp D} {φ : GA D V → ℂ} (h : RapidDecSm θ V φ) (d : ℕ) :
    growthSob θ V d 0 φ ≠ ∞ := by
  let M : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | growthSize V 0 f ≠ ∞}
      add_mem' := fun a b => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨a, b⟩) growthSize_add_le
      zero_mem' := (growthSize_const (0 : ℂ)).trans_ne enorm_ne_top
      smul_mem' := fun c _ a => (growthSize_smul c).trans_ne (ENNReal.mul_ne_top enorm_ne_top a) }
  have hM : φ ∈ allDer θ V M := ⟨h.smooth, fun l hl => modGrowthExp_iff.1
    ((h.decay l hl).bounded.imp fun _ hC g => (hC g).trans_eq (by simp))⟩
  refine wordSum_ne_top_iff.2 fun l _ => ?_
  exact (wordAct_rel (A := glDer θ V) (B := glDer θ V) (R := fun f _ => f ∈ allDer θ V M) l
    (fun a _ _ _ hf => RderC_mem_allDer hf a.1 _) (y := φ) hM).2 [] (fun _ h => by simp at h)

def Good (θ : InfFam D) (V : HSp D) (f : GA D V → ℂ) : Prop := RapidDecSm θ V f ∧ IsCuspFun V f

theorem good_add {θ : InfFam D} {V : HSp D} {f f' : GA D V → ℂ} (h : Good θ V f) (h' : Good θ V f') :
    Good θ V (f + f') :=
  ⟨h.1.add h'.1, GlobalTheory.MultMem.isCuspFun_add h.1.toIsAutFun h'.1.toIsAutFun h.2 h'.2⟩

theorem good_smul {θ : InfFam D} {V : HSp D} {f : GA D V → ℂ} (c : ℂ) (h : Good θ V f) : Good θ V (c • f) :=
  ⟨h.1.smul c, GlobalTheory.MultMem.isCuspFun_smul c h.2⟩

theorem good_zero (θ : InfFam D) (V : HSp D) : Good θ V 0 := by
  refine ⟨rapidDecSm_iff.2 ⟨zero_mem _, ⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, ?_⟩
  exact fun _ _ _ _ _ _ _ _ => by simp

theorem good_value (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) (N : GlobalTheory.Grid.Node D) {Φ : N.Maps}
    (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) : Good θ N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have hU' : ∀ w, Good θ N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => ⟨rapidDecSm_of_cuspForm hP hθ (hx.aut w) (hx.cusp w), hx.cusp w⟩
    | zero => exact fun w => good_zero θ N.V
    | add x y _ _ hx hy => exact fun w => good_add (hx w) (hy w)
    | smul c x _ hx => exact fun w => good_smul c (hx w)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using good_smul r (hU' f)
  | add x y hx hy => simpa using good_add hx hy

end GlobalTheory.CuspApproxAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLatticeCharSumDetectsNsmulMultiple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.CharSumHalf

open GlobalTheory.Core.Rk.ThetaOf GlobalTheory.DownLift.GenQuot

set_option synthInstance.maxHeartbeats 100000 in

theorem charSum_detects_multiple : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (k : ℕ) (R : Finset (WO S T)), 0 < k → (∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1) → (∀ x : WO S T, IsHalf e x → (∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) → x ∈ Λ) → (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ Λ) → (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ Λ → ∃! r, r ∈ R ∧ y - r ∈ Λ) → ∀ t ∈ Λ, IsHalf e t → ((∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = R.card) ∧ ((¬ ∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = 0) := by
  intro D ψ S T Λ e k R hk hpair hann hR hU t htΛ hte
  classical
  have half_sub : ∀ {c : AE D} {x y : WO S T}, IsHalf c x → IsHalf c y → IsHalf c (x - y) :=
    fun hx hy i j => by simp only [Matrix.sub_apply, mul_sub, hx i j, hy i j]
  have half_add : ∀ {c : AE D} {x y : WO S T}, IsHalf c x → IsHalf c y → IsHalf c (x + y) :=
    fun hx hy i j => by simp only [Matrix.add_apply, mul_add, hx i j, hy i j]
  have half_nsmul : ∀ {c : AE D} {x : WO S T} (n : ℕ), IsHalf c x → IsHalf c (n • x) :=
    fun n hx i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hx i j]
  have half_smul : ∀ {c : AE D} {x : WO S T} (a : AE D), IsHalf c x → IsHalf c (a • x) :=
    fun a hx i j => by simp only [Matrix.smul_apply, smul_eq_mul]; rw [mul_left_comm, hx i j]
  have pair_add : ∀ x y y' : WO S T,
      ψ (symplO S T x (y + y')) = ψ (symplO S T x y) * ψ (symplO S T x y') := by
    intro x y y'; rw [symplO_add_right, AddChar.map_add_eq_mul]
  constructor
  · rintro ⟨u, huΛ, hue, rfl⟩
    have h1 : ∀ r ∈ R, ψ (symplO S T (k • u) r) = 1 := fun r hr => by
      rw [symplO_nsmul_swap]
      exact hpair u huΛ hue _ (hR r hr).2 (half_nsmul k (hR r hr).1)
    rw [Finset.sum_congr rfl h1]; simp
  · intro hnot
    have hex : ∃ r₀ ∈ R, ψ (symplO S T t r₀) ≠ 1 := by
      by_contra hall
      push_neg at hall
      apply hnot
      set a : AE D := algebraMap D.host.F (AE D) ((k : D.host.F)⁻¹) with ha
      have hka : k • a = 1 := by
        rw [ha, ← map_nsmul, nsmul_eq_mul, mul_inv_cancel₀ (by exact_mod_cast hk.ne'), map_one]
      have hkx : ∀ x : WO S T, k • (a • x) = x := fun x => by
        rw [← smul_assoc, hka, one_smul]
      refine ⟨a • t, ?_, half_smul a hte, (hkx t).symm⟩
      apply hann _ (half_smul a hte)
      intro y hyΛ hyc
      obtain ⟨r, ⟨hrR, hdiff⟩, -⟩ := hU (a • y) (half_smul a hyc) (by rw [hkx]; exact hyΛ)
      have hsw : symplO S T (a • t) y = symplO S T t (a • y) := by
        conv_lhs => rw [← hkx y]
        rw [← symplO_nsmul_swap, hkx]
      rw [hsw, show a • y = (a • y - r) + r by abel, pair_add, hall r hrR, mul_one]
      exact hpair t htΛ hte _ hdiff (half_sub (half_smul a hyc) (hR r hrR).1)
    obtain ⟨r₀, hr₀R, hr₀⟩ := hex
    obtain ⟨rep, rep_spec⟩ : ∃ rep : WO S T → WO S T,
        ∀ y, IsHalf (cA D e) y → k • y ∈ Λ → rep y ∈ R ∧ y - rep y ∈ Λ := by
      refine ⟨fun y => if h : IsHalf (cA D e) y ∧ k • y ∈ Λ then (hU y h.1 h.2).exists.choose else 0, ?_⟩
      intro y h1 h2
      dsimp only
      rw [dif_pos (And.intro h1 h2)]
      exact (hU y h1 h2).exists.choose_spec
    have rep_eq : ∀ y r, IsHalf (cA D e) y → k • y ∈ Λ → r ∈ R → y - r ∈ Λ → rep y = r :=
      fun y r h1 h2 hr hd => (hU y h1 h2).unique (rep_spec y h1 h2) ⟨hr, hd⟩
    have hadd : ∀ r ∈ R, ∀ s ∈ R, IsHalf (cA D e) (r + s) ∧ k • (r + s) ∈ Λ := fun r hr s hs =>
      ⟨half_add (hR r hr).1 (hR s hs).1, by rw [nsmul_add]; exact Λ.add_mem (hR r hr).2 (hR s hs).2⟩
    have hsub : ∀ r ∈ R, ∀ s ∈ R, IsHalf (cA D e) (r - s) ∧ k • (r - s) ∈ Λ := fun r hr s hs =>
      ⟨half_sub (hR r hr).1 (hR s hs).1, by rw [nsmul_sub]; exact Λ.sub_mem (hR r hr).2 (hR s hs).2⟩
    have key : ∑ r ∈ R, ψ (symplO S T t r₀) * ψ (symplO S T t r) = ∑ r ∈ R, ψ (symplO S T t r) := by
      apply Finset.sum_nbij' (fun r => rep (r + r₀)) (fun r => rep (r - r₀))
      · intro r hr; exact (rep_spec _ (hadd r hr r₀ hr₀R).1 (hadd r hr r₀ hr₀R).2).1
      · intro r hr; exact (rep_spec _ (hsub r hr r₀ hr₀R).1 (hsub r hr r₀ hr₀R).2).1
      · intro r hr
        obtain ⟨h1, h2⟩ := rep_spec _ (hadd r hr r₀ hr₀R).1 (hadd r hr r₀ hr₀R).2
        have hs := hsub _ h1 r₀ hr₀R
        refine rep_eq _ r hs.1 hs.2 hr ?_
        have : rep (r + r₀) - r₀ - r = -((r + r₀) - rep (r + r₀)) := by abel
        rw [this]; exact Λ.neg_mem h2
      · intro r hr
        obtain ⟨h1, h2⟩ := rep_spec _ (hsub r hr r₀ hr₀R).1 (hsub r hr r₀ hr₀R).2
        have hs := hadd _ h1 r₀ hr₀R
        refine rep_eq _ r hs.1 hs.2 hr ?_
        have : rep (r - r₀) + r₀ - r = -((r - r₀) - rep (r - r₀)) := by abel
        rw [this]; exact Λ.neg_mem h2
      · intro r hr
        obtain ⟨h1, h2⟩ := rep_spec _ (hadd r hr r₀ hr₀R).1 (hadd r hr r₀ hr₀R).2
        have hrep : rep (r + r₀) = (r + r₀) + -((r + r₀) - rep (r + r₀)) := by abel
        have hhalf : IsHalf (cA D e) (-((r + r₀) - rep (r + r₀))) := by
          have := half_sub (hadd r hr r₀ hr₀R).1 (hR _ h1).1
          intro i j; simp only [Matrix.neg_apply, mul_neg, this i j]
        show _ = ψ (symplO S T t (rep (r + r₀)))
        rw [hrep, pair_add, pair_add, hpair t htΛ hte _ (Λ.neg_mem h2) hhalf, mul_one, mul_comm]
    rw [← Finset.mul_sum] at key
    have h0 : (ψ (symplO S T t r₀) - 1) * ∑ r ∈ R, ψ (symplO S T t r) = 0 := by
      rw [sub_mul, key, one_mul, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hr₀)

end GlobalTheory.CharSumHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivRealLineEqSumRealPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDeriv_realLine_eq_sum_realPlaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ L : ℝ →+ WO S T, Continuous L →
      (∀ t, (L t).map (finPart D) = 0) →
      (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0) =
        ∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f := by
  first | exact @GlobalTheory.PlaceSum.deriv_heisO_eq_sum_dRho | exact GlobalTheory.PlaceSum.deriv_heisO_eq_sum_dRho | (intros; apply GlobalTheory.PlaceSum.deriv_heisO_eq_sum_dRho <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HomLatticeCosetIndicatorPrimePowersIntegralCosetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homLatticeCosetIndicator_primePowers_integralCoset : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ), Formalism.L2.DIV.IsFrame S.β S.Λ → Formalism.L2.DIV.IsFrame T.β T.Λ → IsIdemSum e P → ∀ c : GlobalTheory.Grid.Coset S T (∏ w ∈ P, w.asIdeal ^ d w), ∃ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ (∏ w ∈ P, w.asIdeal ^ d w), GlobalTheory.Grid.cosetInd S T e (∏ w ∈ P, w.asIdeal ^ d w) c = GlobalTheory.ChiGrid.cosInd e κ := by
  first | exact @GlobalTheory.CosetIndCompare.coset_eq_cos | exact GlobalTheory.CosetIndCompare.coset_eq_cos | (intros; apply GlobalTheory.CosetIndCompare.coset_eq_cos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFirst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThetaArrowConv

theorem thetaIntegral_integrableOn : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ h
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  obtain ⟨hν, hfd⟩ := GlobalTheory.PairLift.haar_vert hRB hG t hi (Nat.succ_le_of_lt hj)
  have hrd := GlobalTheory.Grow.rapidDec_of_cuspForm hP.cuspRapidDecay hRB.inf hφ.1 hφ.2.1
  exact GlobalTheory.Chain.LiftConv.integrableOn_of_rapidDec (GlobalTheory.KernelSeminorm.thetaGrowth D) hRB.inf hω hΦ hν hfd hrd h

end GlobalTheory.ThetaArrowConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumOverFinitePlacesUniqueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentSum_over_finite_places_unique : ∀ {D : D7} (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e e' : AE D), IsIdemSum e P → IsIdemSum e' P → e = e' := by
  first | exact @GlobalTheory.IdemSumUniq.idemSum_unique | exact GlobalTheory.IdemSumUniq.idemSum_unique | (intros; apply GlobalTheory.IdemSumUniq.idemSum_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjKOfSeparatesLinB
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx

theorem injK_of_separates_linB (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate) (hL : LinB) : InjK := by
  refine GlobalTheory.RowTest.injK_of_separates hS ?_
  obtain ⟨C0, hL⟩ := hL
  refine ⟨C0, fun ε CF hCF => ?_⟩
  obtain ⟨x0, hL⟩ := hL ε CF hCF
  refine ⟨x0, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hset ch hch hsc ρ ξ a u => ?_⟩
  exact hL D large₂ hε hx Γ Pl0 T A Ks R F hset (ch.withReal ρ ξ) hsc (hch.toIsBase.withReal ρ ξ) a u

end GlobalTheory.RowEx

end
end

