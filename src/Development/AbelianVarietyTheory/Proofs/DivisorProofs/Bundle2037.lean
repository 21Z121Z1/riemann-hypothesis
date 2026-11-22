import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceThetaFunctionVacuumConjugatePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorArchimedeanMemAdelicSchwartzStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedingerOperator_archimedean_mem_adelicSchwartz : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F h) φ ∈ GlobalTheory.WeilM.schA F κ := by
  first | exact @GlobalTheory.WeilL2Words.schr_archPair_mem_schA | exact GlobalTheory.WeilL2Words.schr_archPair_mem_schA | (intros; apply GlobalTheory.WeilL2Words.schr_archPair_mem_schA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortTranslate
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.LevelMoveShort

open GlobalTheory.TraceLattice

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem isShortRule_mv {D : D7} (T : Full D) (hT : LawsFull T) {j : ℕ} (hj : InR D j) (hxi : TwistTrivialOnRational T j)
    {w : WeightFamilies.Wt D j} {n : ℕ} (hn : w.n = n) (hnV : n = D.R.nV)
    {γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l} (hγ : DetOne γ)
    {Λ : GenLat D.host.E n} {N : ℕ} {P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F} {x x' : Fin n → (T.Q.Dw j).La} {f : T.R j}
    (h1 : Λ.Unimod) (h2 : Λ.TrivAt (badN D)) (h3 : Λ.TrivAt (T.dδ j n).l₂.M) (h4 : Λ.LevOK N (T.dδ j n).l₂.M)
    (hP : P ∈ harmL (Dw := T.Q.Dw j) T.Q.c Λ (wtA w)) (hx : IsRightMul γ x' x) (ha : AdmX (l := T.Q.l) true x)
    (ha' : AdmX (l := T.Q.l) true x') (hs : f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n)
    (hf : IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x P f) :
    IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x' P (mv T.toTop j γ f) := by
  subst hn
  have hd : decide (w.n = D.R.nV) = true := decide_eq_true hnV
  have hG : GoodDatum T.toTop j w Λ N P := ⟨h1, h2, h3, h4, hP⟩
  obtain ⟨f', hf'⟩ := exists_isSeries hT.sh hj hG (x := x') (hd ▸ ha')
  have e := mv_series T hT hj hxi (hnV ▸ Nat.le_add_right _ _) hγ hG hx ⟨hd ▸ ha, hs, hf⟩ hf'
  rw [e]
  exact hf'.2.2

end GlobalTheory.LevelMoveShort

theorem GlobalTheory.LevelMoveShort.short_translate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), R.LUnif → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ), RunPin (T := T) R i (κ i).n v p → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → ∀ u : U, ∃ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P (F₀.1 : T.R ((i : ℕ) + 1)) ∧ cuspTo hT.p fw i (f u) = (R.FW i).ρ ((u : G)⁻¹) (cuspTo hT.p fw i F₀) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw hT _ i _ ℓ hℓ hAP v p hR hPg U hU Λ N x₀ P x f h1 h2 h3 h4 ha₀ hP hx u
  obtain ⟨act, hact, hρ⟩ := hAP
  have hnV : (κ i).n = D.R.nV := (fw.kap i (D.eTau.symm 1)).2.2
  have hnV' : (Vc D i).rank = D.R.nV := (GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne.rank_Vc i).1
  have hxi := GlobalTheory.TraceLattice.twistTrivial_of_runPin hT hR
  have hdet : GlobalTheory.TraceLattice.DetOne (ℓ (u : G)) := GlobalTheory.TraceLattice.detOne_of_levelPin hT hℓ hPg (hU u)
  refine ⟨act (u : G) (f u), ?_, ?_⟩
  · rw [hact]
    exact GlobalTheory.LevelMoveShort.isShortRule_mv T hT (inR_succ i) hxi (hnV.trans hnV'.symm) hnV' hdet h1 h2 h3 h4 hP
      (hx u).1 (hx u).2.1 ha₀ (cutR_le T.C _ _ (f u).2).1 (hx u).2.2
  · rw [hρ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanTranslatesEqTop
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open Classical

noncomputable section
namespace GlobalTheory.LowSpan

theorem span_translates_eq_top : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) (v : M.Vec), IsExtVec M v → ∀ τ : D.what₂.Tau, Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ)) → Submodule.span ℂ {u : lowT M τ | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ)} = ⊤ := by
  intro D V S M v hv τ hK
  obtain ⟨_hfd, hst, hirr, -, -⟩ := hK
  obtain ⟨-, -, hU, -⟩ := M.ds τ
  obtain ⟨S₀, hS₀, hS₀sm⟩ := GlobalTheory.SmoothLowType.exists_lowK_le_sm D V S M τ
  have hle : S₀ ≤ Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) :=
    le_sSup (s := {T | Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) T}) hS₀
  have hS₀ne : S₀ ≠ ⊥ := by
    obtain ⟨w, hw, hw0, -⟩ := hS₀.2.2.2.1
    intro h; rw [h] at hw; exact hw0 ((Submodule.mem_bot ℂ).1 hw)
  have hLsm : Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ M.sm τ := by
    rcases hirr S₀ hle hS₀.2.1 with h | h
    · exact absurd h hS₀ne
    · rw [← h]; exact hS₀sm

  set L := Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) with hLdef
  set v0 : M.H τ := ((v τ : M.sm τ) : M.H τ) with hv0def
  have hv0L : v0 ∈ L := (hv τ).2.1
  have hv00 : v0 ≠ 0 := by
    intro h; have h1 := (hv τ).1; rw [← hv0def, h, norm_zero] at h1; exact zero_ne_one h1
  set T : Set (M.H τ) := {x | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), x = M.σ τ k v0} with hTdef
  have hWL : Submodule.span ℂ T ≤ L := by
    rw [Submodule.span_le]; rintro _ ⟨k, hk, rfl⟩; exact hst k hk _ hv0L
  have hWst : Formalism.MainNotions.S.IsKStableOn (M.ε τ) (M.σ τ) (Submodule.span ℂ T) := by
    intro g hg x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨g * k, Formalism.REAL.Kset_mul _ hg hk, ?_⟩
      rw [hU.1.2 g (kset_uj hg) k (kset_uj hk)]; rfl
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have h1K : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.REAL.Kset (M.ε τ) := by
    have := diag_mem (ε := M.ε τ) (fun _ => (0 : ℝ))
    simpa using this
  have hW0 : Submodule.span ℂ T ≠ ⊥ := by
    intro h
    have : v0 ∈ Submodule.span ℂ T := Submodule.subset_span ⟨1, h1K, by rw [hU.1.1]; rfl⟩
    rw [h] at this; exact hv00 ((Submodule.mem_bot ℂ).1 this)
  have hWeq : Submodule.span ℂ T = L := (hirr _ hWL hWst).resolve_left hW0
  let f : lowT M τ →ₗ[ℂ] M.H τ := (M.sm τ).subtype ∘ₗ (lowT M τ).subtype
  have hf : Function.Injective f := (M.sm τ).injective_subtype.comp (lowT M τ).injective_subtype
  apply Submodule.map_injective_of_injective hf
  rw [Submodule.map_span, Submodule.map_top]
  have himg : f '' {u : lowT M τ | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), ((u : M.sm τ) : M.H τ) = M.σ τ k v0} = T := by
    ext x; constructor
    · rintro ⟨u, ⟨k, hk, hu⟩, rfl⟩; exact ⟨k, hk, hu⟩
    · rintro ⟨k, hk, rfl⟩
      have hxL : M.σ τ k v0 ∈ L := hst k hk _ hv0L
      exact ⟨⟨⟨_, hLsm hxL⟩, hxL⟩, ⟨k, hk, rfl⟩, rfl⟩
  rw [himg, hWeq]
  ext y; constructor
  · intro hy; exact ⟨⟨⟨y, hLsm hy⟩, hy⟩, rfl⟩
  · rintro ⟨x, rfl⟩; exact x.2

end GlobalTheory.LowSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitBasisWittModelLocalStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_basis_witt_model_local : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∃ ι, M.IsLinW B.ψ t b c ι ∧ ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 := by
  first | exact @GlobalTheory.VacLinW.vac_linW | exact GlobalTheory.VacLinW.vac_linW | (intros; apply GlobalTheory.VacLinW.vac_linW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartBaseLinksOfPrimitiveRowsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPart_baseLinks_of_primitiveRows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ s : ℕ, A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → GlobalTheory.Hk3.Core R.toRealDat F.lv2 ∧ A3.A.fam.Ok s ∧ BaseLinks R.toRealDat F.lv2 := by
  first | exact @GlobalTheory.LowRow.baseLinks_of_prims | exact GlobalTheory.LowRow.baseLinks_of_prims | (intros; apply GlobalTheory.LowRow.baseLinks_of_prims <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceThetaFunctionVacuumConjugatePlaceStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

theorem _root_.GlobalTheory.T.splitPlace_thetaFunction_vacuum_conjugatePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ φ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ φ ∧ φ ≠ 0 ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            heisOF σ JS JT ξ₀ B.ψ y φ = φ ∨
            ∃ u : WOF F E nS nT, heisOF σ JS JT ξ₀ B.ψ u φ = φ ∧
              B.ψ (symplOHF σ JS JT ξ₀ u y - symplOHF σ JS JT ξ₀ y u) ≠ 1 := by
  exact @PositivityTheory.ThKW.SplitVacuumEigenvectors.exists_vac_split
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeSelfDualAndIntegralIffStabilizes
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

open scoped TensorProduct Matrix

namespace GlobalTheory.NormRatio.StdLevel

variable {D : D7}

def intSub (D : D7) : Subring (Af D.host.F ⊗[D.host.F] D.host.E) where
  carrier := intAE D
  mul_mem' := GlobalTheory.HostAdeleIso.intAE_mul_mem D
  one_mem' := AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, 1, rfl⟩
  add_mem' := (intAE D).add_mem
  zero_mem' := (intAE D).zero_mem
  neg_mem' := (intAE D).neg_mem

theorem mem_intAE_iff_swap (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ intAE D ↔ Lev.swapAE D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      have e : Lev.swapAE D (a ⊗ₜ[D.host.F] (x : D.host.E)) =
          ((x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]; rfl
      rw [e]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩))
    | zero => rw [RingHom.map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [RingHom.map_add]; exact add_mem hy hz
    | neg y _ hy => rw [RingHom.map_neg]; exact neg_mem hy
  · intro hz
    let c := (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)).toRingEquiv.toRingHom
    have key : Formalism.L2.Herm.intAf D.host.F D.host.E ≤ (intSub D).comap c := by
      refine Subring.closure_le.2 ?_
      rintro _ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
      · exact AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x, rfl⟩
      · exact AddSubgroup.subset_closure ⟨a, fun v => ha v, 1, rfl⟩
    have e : ∀ w, c (Lev.swapAE D w) = w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [RingHom.map_zero, RingHom.map_zero]
      | tmul a b => rfl
      | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]
    have h : c (Lev.swapAE D z) ∈ intSub D := key hz
    rw [e] at h
    exact h

theorem preserves_iff {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (M M' : Matrix (Fin n) (Fin n) R)
    (h1 : M * M' = 1) (h2 : M' * M = 1) :
    (∀ y : Fin n → R, (∀ i, y i ∈ S) ↔ ∀ i, (M *ᵥ y) i ∈ S) ↔ (∀ i j, M i j ∈ S) ∧ ∀ i j, M' i j ∈ S := by
  have hmv : ∀ (A : Matrix (Fin n) (Fin n) R) (y : Fin n → R), (∀ i j, A i j ∈ S) → (∀ i, y i ∈ S) →
      ∀ i, (A *ᵥ y) i ∈ S :=
    fun A y hA hy i => show (∑ j, A i j * y j) ∈ S from Subring.sum_mem _ fun j _ => mul_mem (hA i j) (hy j)
  have hs : ∀ j k : Fin n, (Pi.single j (1 : R) : Fin n → R) k ∈ S := fun j k => by
    rw [Pi.single_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · have := (h (Pi.single j 1)).1 (hs j) i
      simpa [Matrix.mulVec_single_one] using this
    · have hy := (h (M' *ᵥ Pi.single j 1)).2 (by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]; exact hs j) i
      simpa [Matrix.mulVec_single_one] using hy
  · rintro ⟨hM, hM'⟩ y
    refine ⟨hmv M y hM, fun hy => ?_⟩
    have := hmv M' _ hM' hy
    rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at this

theorem mem_latHat_stdLat (V : HSp D) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((stdLat V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
      Set (Fin V.rank → D.host.E)) ↔ ∀ i, z i ∈ intAE D := by
  classical
  constructor
  · intro hz i
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hx i trivial)
      exact AddSubgroup.subset_closure ⟨a, ha, o, congrArg (fun w => a ⊗ₜ[D.host.F] w) ho.symm⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro hz
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have := hz i
    generalize z i = w at this
    induction this using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), fun j _ => ?_, funext fun j => ?_⟩
      · by_cases hj : j = i
        · subst hj; rw [Pi.single_eq_same]; exact Submodule.mem_one.2 ⟨x, rfl⟩
        · rw [Pi.single_eq_of_ne hj]; exact zero_mem _
      · by_cases hj : j = i
        · subst hj; rw [Pi.single_eq_same, Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, TensorProduct.tmul_zero]
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
    | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy

theorem stdLat_eq (V : HSp D) : stdLat V = GlobalTheory.SW.stdL D.host.E V.rank := by
  ext x
  rw [GlobalTheory.SW.Base.mem_stdL]
  simp only [stdLat, Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  refine forall_congr' fun i => ?_
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x i, h⟩, rfl⟩⟩

end GlobalTheory.NormRatio.StdLevel

open GlobalTheory.NormRatio.StdLevel in

theorem GlobalTheory.NormRatio.selfDual_and_mem_intG_iff : ∀ {D : D7} (V : HSp D) (n : ℕ) (g : GA D V) (x : Formalism.MainNotions.StandardLatticesGL3.GA D n),
    V.gram = 1 → V.rank = n → GlobalTheory.BotFormula.IsFinPt V g x →
    IsSelfDualC V (stdLat V) ∧ (x ∈ intG D n ↔ g ∈ openOff V (stdLat V) ∅) := by
  intro D V n g x hG hn hx
  subst hn
  have hSD : IsSelfDualC V (stdLat V) := by rw [stdLat_eq]; exact GlobalTheory.Ker.Base.selfDualC_stdL hG
  refine ⟨hSD, ?_⟩
  have hfx := GlobalTheory.BotClassDict.finStd_of_isFinPt V hG hx
  subst hfx
  have e1 : ∀ (k : GA D V) (i j : Fin V.rank),
      (((GlobalTheory.BotClassDict.finStd V hG k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
        Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D ↔
        (finHom V k).1 i j ∈ intAE D := fun k i j => by
    rw [← GlobalTheory.BotClassDict.toAfE_int_iff, GlobalTheory.BotClassDict.toAfE_finStd, mem_intAE_iff_swap]
  have hL : GlobalTheory.BotClassDict.finStd V hG g ∈ intG D V.rank ↔
      (∀ i j, (finHom V g).1 i j ∈ intAE D) ∧ ∀ i j, (finHom V g⁻¹).1 i j ∈ intAE D := by
    rw [GlobalTheory.NormSum.mem_intG]
    unfold Formalism.MainNotions.StandardLatticesGL3.IntG
    have e2 : ((↑(GlobalTheory.BotClassDict.finStd V hG g) : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) =
        ↑(GlobalTheory.BotClassDict.finStd V hG g⁻¹) := by rw [map_inv, Subgroup.coe_inv]
    rw [e2]
    simp only [e1]
    exact ⟨fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩, fun h i j => ⟨h.1 i j, h.2 i j⟩⟩
  have hR : g ∈ openOff V (stdLat V) ∅ ↔
      ∀ y, (∀ i, y i ∈ intAE D) ↔ ∀ i, ((finHom V g).1 *ᵥ y) i ∈ intAE D := by
    have e : g ∈ openOff V (stdLat V) ∅ ↔ g ∈ GlobalTheory.AdelicU.levelOpen _ (HSpace.gram V) (stdLat V) := by
      rw [GlobalTheory.AdelicU.mem_levelOpen]; simp [openOff]
    haveI := hSD.1
    rw [e, GlobalTheory.AdelicU.mem_levelOpen_iff_latHat _ _ Submodule.IsLattice.fg]
    refine forall_congr' fun y => ?_
    rw [mem_latHat_stdLat, mem_latHat_stdLat]
    rfl
  have h1 : (finHom V g).1 * (finHom V g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h2 : (finHom V g⁻¹).1 * (finHom V g).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  rw [hL, hR]
  exact (preserves_iff (intSub D) _ _ h1 h2).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdMassNeZero
section
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.NormRatio
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

theorem std_mass_ne_zero : ∀ (D : D7) (N : ℕ), mass D N ≠ 0 := by
  intro D N
  haveI := (GlobalTheory.NormSum.cls_finite_card_le D N).1
  haveI := Fintype.ofFinite (GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N))
  have hne : (Finset.univ : Finset (GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N))).Nonempty :=
    ⟨DoubleCoset.mk _ _ 1, Finset.mem_univ _⟩
  have hpos : (0 : ℝ) < ∑ x : GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N),
      ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D N) x.out : ℝ))⁻¹ :=
    Finset.sum_pos (fun x _ => inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero
      (GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D N _ le_rfl x.out).1))) hne
  unfold mass
  rw [finsum_eq_sum_of_fintype]
  have h := Complex.ofReal_ne_zero.2 hpos.ne'
  push_cast at h
  exact h

end GlobalTheory.NormRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeightRpowParabolicCosetsStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_height_rpow_parabolicCosets : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), Submodule.IsLattice E L → (∀ g : GAd σ J, ∃ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 ∧ ∃ k ∈ levelAll σ J L a, g = p * k) → ∀ h : GAd σ J → ℝ≥0, (∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det β)) → ∀ (g : GAd σ J) (t : ℝ), (n : ℝ) - j < t → Summable fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) => (h ((q.out : ratPts σ J) * g) : ℝ) ^ t := by
  first | exact @GlobalTheory.SphEis.summable_height_rpow | exact GlobalTheory.SphEis.summable_height_rpow | (intros; apply GlobalTheory.SphEis.summable_height_rpow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGoodEmbeddingIndependentReadings
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnifGood

theorem span_top_of_range {H X S C : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] [AddCommGroup S]
    [Module ℂ S] (ev : H →ₗ[ℂ] X) (hev : Function.Injective ev) (ad : S →ₗ[ℂ] X) (rd : C → S) (j : C → H) (c : ℂ) (hc : c ≠ 0)
    (hj : ∀ f, ev (j f) = c • ad (rd f))
    (hr : Set.range ev = ad '' (Submodule.span ℂ (Set.range rd) : Set S)) :
    Submodule.span ℂ (Set.range j) = ⊤ := by
  refine top_le_iff.1 fun h _ => ?_
  obtain ⟨F, hF, hFh⟩ : ev h ∈ ad '' (Submodule.span ℂ (Set.range rd) : Set S) := hr ▸ ⟨h, rfl⟩
  have key : Submodule.span ℂ (Set.range rd) ≤ ((Submodule.span ℂ (Set.range j)).map ev).comap ad := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    refine ⟨c⁻¹ • j f, Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩), ?_⟩
    rw [map_smul, hj, smul_smul, inv_mul_cancel₀ hc, one_smul]
  obtain ⟨y, hy, hy'⟩ := key hF
  rwa [← hev (hy'.trans hFh)]

theorem phiC_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T hV a f = ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) •
      adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
        (rdU (T.U j σ) f) := by
  subst hV
  rfl

noncomputable def evLin {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun := evAt R i σ v
  map_add' x y := by
    unfold evAt
    rw [map_add]
    rfl
  map_smul' a x := by
    unfold evAt
    rw [map_smul]
    rfl

theorem unif_good : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ i σ, GoodEmb T.Q.c (res T σ) → (∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k)) ∧ Submodule.span ℂ (Set.range (jTop T R κ v₀ i σ)) = ⊤ := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hpb hlast hn i σ hσ
  have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := hT.laws.spaceW _ (inR i) _ hσ
  have hj := GlobalTheory.T.cuspFormAdelicFunctions_eq_modelValues_semilinear h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb i σ hσ hV
  have hev : ∀ f, evLin R i σ (v₀ i σ) (jTop T R κ v₀ i σ f) = phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) :=
    jTop_good T R κ v₀ hσ hV hj
  refine ⟨fun m b hb => ?_, ?_⟩
  · refine LinearIndependent.of_comp (evLin R i σ (v₀ i σ)) ?_
    have h := GlobalTheory.T.cuspFormAdelicFunctions_independent_goodEmbedding D T κ hT.laws i _ hσ hV m b hb
    exact (funext fun k => hev (b k) : (evLin R i σ (v₀ i σ) ∘ fun k => jTop T R κ v₀ i σ (b k)) = _) ▸ h
  · have hr := GlobalTheory.T.hilbertModel_extremalValues_eq_holomorphicCuspForms h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb i σ hσ hV
    rw [GlobalTheory.T.holomorphicCuspSections_eq_span_readings D T κ hT.laws hT.kap hlast hn i _ hσ] at hr
    exact span_top_of_range (evLin R i σ (v₀ i σ)) (GlobalTheory.EvalAtUnitVector.evInj T R v₀ hM.HW hT.hv₀ i σ hσ) _ _ _ _
      (Complex.ofReal_ne_zero.2 (lieFac_pos _ _ _).ne') (fun f => (hev f).trans (phiC_eq T hV _ _)) hr

end GlobalTheory.UnifGood
end

