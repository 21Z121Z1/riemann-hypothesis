import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0485
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  add_mem' := by
    intro f g hf hg
    obtain ⟨U₁, hU₁, h₁⟩ := hf.level
    obtain ⟨U₂, hU₂, h₂⟩ := hg.level
    refine ⟨fun γ w => ?_, ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun u hu hu0 => ?_⟩, hf.cont.add hg.cont,
      fun k L hL h0 w => (hf.smooth k L hL h0 w).add (hg.smooth k L hL h0 w)⟩
    · simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    · funext w
      have e₁ := congrFun (h₁ u hu.1 hu0) w
      have e₂ := congrFun (h₂ u hu.2 hu0) w
      simp only [heisO, Pi.add_apply] at e₁ e₂ ⊢
      rw [mul_add, e₁, e₂]
  zero_mem' := ⟨fun γ w => by simp, ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext w; simp [heisO]⟩, continuous_const,
    fun k L hL h0 w => contDiff_const⟩
  smul_mem' := by
    intro c f hf
    obtain ⟨U₁, hU₁, h₁⟩ := hf.level
    refine ⟨fun γ w => ?_, ⟨U₁, hU₁, fun u hu hu0 => ?_⟩, hf.cont.const_smul c,
      fun k L hL h0 w => (hf.smooth k L hL h0 w).const_smul c⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf.quasi]; ring
    · funext w
      have e₁ := congrFun (h₁ u hu hu0) w
      simp only [heisO, Pi.smul_apply, smul_eq_mul] at e₁ ⊢
      rw [← e₁]; ring

variable (t : T) in

def positionPair (m : ℕ) : Fin m ⊕ Fin m → Pair T
  | .inl j => .top t j
  | .inr i => .chi i m

variable (G) in

abbrev FactorFn (t : T) (a : Fin D.R.m ⊕ Fin D.R.m) : Type :=
  WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) → ℂ

def vecOf (S : GridChoice W U) {t : T} (d : PureDat G t) : ∀ a, FactorFn G t a
  | .inl j => S.Z.vec (d.1 j)
  | .inr i => S.Z.vec (d.2 i)

def kkV (S : GridChoice W U) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (a : FinPt G p.small) (b : FinPt G p.big) :
    VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big) :=
  S.Z.scal 1 p • fockComp W S.N.frC p f (a * S.N.u _) (b * S.N.u _)

def colV (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (x : ∀ j, FinPt G (.top j)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then kkV S (.top t j) (v (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowV (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (v (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

def pairFn (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (v : ∀ a, FactorFn G t a) : VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂ (colV S v x) (rowV S v y)

theorem pairPts_eq_sum (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j))
    (y : ∀ i, FinPt G (.grid i D.R.m)) : pairPts S τ x y = τ.sum fun d c => c • pairFn S x y (vecOf S d) := rfl

def moved (S : GridChoice W U) (j : ℕ) (k : FinPt G (.grid (j + 1) D.R.m)) : GA D (G.V (.grid (j + 1) D.R.m)) :=
  ((S.N.u (.grid (j + 1) D.R.m))⁻¹ * k * S.N.u (.grid (j + 1) D.R.m) : FinPt G (.grid (j + 1) D.R.m))

def moveV (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) : ∀ a, FactorFn G t a :=
  Function.update
    (Function.update v (.inr ⟨j, by omega⟩)
      (W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (v (.inr ⟨j, by omega⟩)) : FactorFn G t (.inr ⟨j, by omega⟩)))
    (.inr ⟨j + 1, hj⟩)
    (W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (v (.inr ⟨j + 1, hj⟩)) : FactorFn G t (.inr ⟨j + 1, hj⟩))

end GlobalTheory.RowVertexInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvZipFock
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem pathConv_zip_fock (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (hC : CuspStep W M ρ t) {X : Node} :
    ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p → ∀ (φ d : PureT G p), VecAll ρ e p φ d →
      ∀ (P' : PolT G p) (F : Fn G X), IsCuspListed W.θ X F →
      PathConv W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') F ∧
      IsCuspListed W.θ Y (liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') F)
  | _, .nil, _, _, _, _, _, _, hF => ⟨trivial, hF⟩
  | _, .snoc a p, hg, φ, d, hv, P', F, hF => by
    have hg' : OnGrid D.R.m t p := fun b hb => hg b (List.mem_append_left [a] hb)
    have ha : IsGridArrow D.R.m t a := hg a (List.mem_append_right p.arrows (List.mem_singleton_self a))
    obtain ⟨h1, h2⟩ := pathConv_zip_fock M ρ t he hC p hg' φ.1 d.1 hv.1 P'.1 F hF
    obtain ⟨h3, h4⟩ := hC a ha e he φ.2 d.2 hv.2 P'.2 _ h2
    exact ⟨⟨h1, h3⟩, h4⟩

theorem mem_support_tensT {X Y : Node} {p : Path T X Y} (τi : PolT G p →₀ ℂ) (τf : TotT G p) (x : PureT G p)
    (hx : x ∈ (tensT W τi τf).support) :
    ∃ d ∈ τf.support, ∃ P' : PolT G p, x = Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P' := by
  classical
  unfold tensT at hx
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hx)
  obtain ⟨d, hd, hx'⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  exact ⟨d, hd, P, Finset.mem_singleton.1 (Finsupp.support_single_subset hx')⟩

theorem totConv_tensE : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → ∀ (τ : TotT G p) (φ : PureT G p → PureT G p), (∀ d ∈ τ.support, GlobalTheory.FlipRun.VecAll ρ e p (φ d) d) → ∀ F : Fn G X, GlobalTheory.FlipRun.IsCuspListed W.θ X F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, TotConv W M p (GlobalTheory.FlipRun.tensE W p Q τ) F := by
  intro D T L sc G W M ρ t e he hC X Y p hg τ φ hv F hF Q x hx
  obtain ⟨d, hd, P', rfl⟩ := mem_support_tensT _ τ x hx
  exact (pathConv_zip_fock M ρ t he hC p hg (φ d) d (hv d hd) P' F hF).1

end GlobalTheory.FlipRun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesSmoothModerateGrowthDerivStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareSeries_smooth_moderateGrowth_deriv : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ UnifModGrowth V θ (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, (w : M.H τ) = dRep (M.rep τ) X (a τ) → (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ' => Function.update a τ w τ') = Rder θ V τ X (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  first | exact @GlobalTheory.PoinDer.poin_smooth_growth_deriv | exact GlobalTheory.PoinDer.poin_smooth_growth_deriv | (intros; apply GlobalTheory.PoinDer.poin_smooth_growth_deriv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdCardAdicCompletionIntegersQuotDvdPowFinrank
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory

theorem prod_card_quot_natCast_dvd_pow_finrank : ∀ (F : Type) [Field F] [NumberField F] (s : Finset (HeightOneSpectrum (𝓞 F))) (k : ℕ), 0 < k → ∏ v ∈ s, Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {(k : v.adicCompletionIntegers F)}) ∣ k ^ Module.finrank ℚ F := by
  intro F _ _ s k hk
  classical
  set I : Ideal (𝓞 F) := Ideal.span {(k : 𝓞 F)} with hIdef
  have hI : I ≠ 0 := by
    rw [hIdef, Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hk.ne'
  have hmap : ∀ v : HeightOneSpectrum (𝓞 F),
      I.map (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) =
        Ideal.span {(k : v.adicCompletionIntegers F)} := by
    intro v
    rw [hIdef, Ideal.map_span, Set.image_singleton, map_natCast]
  obtain ⟨hfin, hprod⟩ := GlobalTheory.LocalDifferentProduct.finprod_card_quot_map hI
  simp only [hmap] at hfin hprod
  have hnorm : Ideal.absNorm I = k ^ Module.finrank ℚ F := by
    rw [hIdef, Ideal.absNorm_span_singleton]
    have e : (k : 𝓞 F) = algebraMap ℤ (𝓞 F) (k : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Int.natAbs_pow]
    simp
  rw [← hnorm, ← hprod, finprod_eq_prod_of_mulSupport_subset (s := s ∪ hfin.toFinset) _
    (by intro x hx; simp [hx])]
  exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_left

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionOfFunctorialityAdoptedStatement
section
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_of_functoriality_adopted : GlobalTheory.FunPr.Hypotheses₂ → StepProj := by
  first | exact @GlobalTheory.Adopt.projection_of_functoriality_adopted | exact GlobalTheory.Adopt.projection_of_functoriality_adopted | (intros; apply GlobalTheory.Adopt.projection_of_functoriality_adopted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOPerm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowKer

variable {D : D7}

theorem unitMap_perm {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) (σ : Equiv.Perm (Fin n))
    (σ' : Equiv.Perm (Fin m)) (i : Fin m) (j : Fin n) :
    unitMap (B.submatrix id σ) (B'.submatrix id σ') i j = unitMap B B' (σ' i) (σ j) := by
  unfold unitMap
  have h : (B.submatrix id σ)⁻¹ = B⁻¹.submatrix σ id := by
    simpa using Matrix.inv_submatrix_equiv B (Equiv.refl _) σ
  rw [h]
  ext a b
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]

theorem pureTensorO_perm {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (σS : D.what₂.Tau → Equiv.Perm (Fin S.rank)) (σT : D.what₂.Tau → Equiv.Perm (Fin T.rank))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (Q : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT (fun τ => (BS τ).submatrix id (σS τ)) (fun τ => (BT τ).submatrix id (σT τ)) f
        (MvPolynomial.rename (fun k : FVar D T.rank S.rank => (k.1, (σT k.1).symm k.2.1, (σS k.1).symm k.2.2)) Q) =
      pureTensorO ψ θ S T sS sT BS BT f Q := by
  unfold pureTensorO
  refine GlobalTheory.ArchRec.LieAtPlace.pure_rename (fun v Q => ?_) (fun v Q => ?_) _ (fun k => ?_) Q
  · refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  · refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  · obtain ⟨τ, i, j⟩ := k
    simp only [aPlusAll, unitMap_perm, Equiv.apply_symm_apply]

open GlobalTheory.GridJoin

theorem heq_ker {V1 V0 U1 U0 : HSp D} (h1 : SameSp V1 U1) (h0 : SameSp V0 U0) (ω : GlobalTheory.Grid.WRep U1 U0)
    (om : GA D (negSp V1) × GA D V0 →* Module.End ℂ (WO (negSp V1) V0 → ℂ)) (hom : HEq (ω.toSgn true) om)
    (F : WO U1 U0 → ℂ) (F' : WO (negSp V1) V0 → ℂ) (hF : HEq F F') :
    HEq (fun (h : GA D U1) (g : GA D U0) => thetaKO ω h g F)
      (fun (h : GA D V1) (g : GA D V0) => thetaKO om (negGA V1 h) g F') := by
  obtain ⟨L, a, b, rfl⟩ := h1
  obtain ⟨L', a', b', rfl⟩ := h0
  cases hom
  cases hF
  rfl

theorem heq_fock {V1 V0 U1 U0 : HSp D} (h1 : SameSp V1 U1) (h0 : SameSp V0 U0) {ψ ψ' : AddChar (AF D.host.F) ℂ}
    {θ θ' : InfFam D} (eψ : ψ' = ψ) (eθ : θ' = θ) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {s1 b1 : D.what₂.Tau → Matrix (Fin V1.rank) (Fin V1.rank) ℂ} {s0 b0 : D.what₂.Tau → Matrix (Fin V0.rank) (Fin V0.rank) ℂ}
    {t1 c1 : D.what₂.Tau → Matrix (Fin U1.rank) (Fin U1.rank) ℂ} {t0 c0 : D.what₂.Tau → Matrix (Fin U0.rank) (Fin U0.rank) ℂ}
    (ht1 : HEq t1 s1) (ht0 : HEq t0 s0) (σ1 : D.what₂.Tau → Equiv.Perm (Fin V1.rank)) (σ0 : D.what₂.Tau → Equiv.Perm (Fin V0.rank))
    (hc1 : HEq c1 fun τ => (b1 τ).submatrix id (σ1 τ)) (hc0 : HEq c0 fun τ => (b0 τ).submatrix id (σ0 τ))
    (hs1 : ∀ τ, IsCartanInv (gramAt D V1 τ) (s1 τ)) (hs0 : ∀ τ, IsCartanInv (gramAt D V0 τ) (s0 τ))
    {f : WO U1 U0 → ℂ} {f' : WO (negSp V1) V0 → ℂ} (hf : HEq f f') (hth : IsThetaFunO ψ (GlobalTheory.Grid.sgn true U1) U0 f)
    (q : PolF D V0.rank V1.rank) : ∃ p : PolF D U0.rank U1.rank,
      HEq (pureTensorO ψ θ (GlobalTheory.Grid.sgn true U1) U0 (fun τ => GlobalTheory.Grid.sgnM true (t1 τ)) t0 c1 c0 f p)
        (pureTensorO ψ' θ' (negSp V1) V0 (fun τ => -s1 τ) s0 b1 b0 f' q) := by
  obtain ⟨L, a, b, rfl⟩ := h1
  obtain ⟨L', a', b', rfl⟩ := h0
  subst eψ eθ
  cases ht1; cases ht0; cases hc1; cases hc0; cases hf
  have hth' : IsThetaFunO _ (negSp V1) V0 _ := ⟨hth.1, hth.2, hth.3, hth.4⟩
  exact ⟨_, heq_of_eq (pureTensorO_perm (S := negSp V1) (T := V0) hψ hθ (fun τ => isCartanInv_neg (hs1 τ)) hs0 b1 b0 σ1 σ0
    hth' q)⟩

end GlobalTheory.RowKer

namespace GlobalTheory.RowKer

open GlobalTheory.GridJoin

theorem kernel_row : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R),
    IsSelfDualC (Yc D 0) (R.ΛY 0) → ch.W.Over R → ∀ (G : GlobalTheory.Grid.GridPre R), G.Is → GlobalTheory.GridJoin.Match G ch.W →
    ∀ (ρ : ch.G.RealVec) (Φ : ch.G.Datum) (i : Fin D.R.m), ∃ f,
      GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V ((i : ℕ) + 1) 0) (G.V i 0) f ∧ ∃ p,
        HEq (fun h g => thetaKO (G.X i 0).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V ((i : ℕ) + 1) 0) (G.V i 0) f p))
          (fun h g => ch.W.kerA (.right (i : ℕ) 0) (ch.W.datum ρ Φ i) g h) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hY hO G hG hM ρ Φ i
  obtain ⟨hsp, harr⟩ := hM
  have hi : (i : ℕ) < D.R.m := i.2
  obtain ⟨c, hc⟩ := (harr.cos i hi).2 (Φ i)
  have sd : ∀ k, k ≤ D.R.m → IsSelfDualC (G.V k 0).V (G.V k 0).Λ := by
    rintro (_ | k) hk
    · exact hY
    · exact GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ 1 (hG.spaces.vert k 0 hk (Nat.zero_le _)).frame
  have hfin : GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V ((i : ℕ) + 1) 0) (G.V i 0) (G.vC i c) :=
    GlobalTheory.T.isFiniteDatum_of_homLatticeCoset_selfDual c (hG.arrows.X i 0 hi (Nat.zero_le _)).vac (sd _ hi) (sd _ hi.le) hG.chars.places.idem
      (G.toPlaceDat.ideal_ne_bot _) (hG.data i hi c)
  refine ⟨G.vC i c, hfin, ?_⟩
  have n1 := hsp.vert ((i : ℕ) + 1) 0 hi (Nat.zero_le _)
  have n0 := hsp.vert i 0 hi.le (Nat.zero_le _)
  obtain ⟨σ1, hσ1⟩ := n1.onb (by simp)
  obtain ⟨σ0, hσ0⟩ := n0.onb (by simp)
  obtain ⟨p, hp⟩ := heq_fock n1.sp n0.sp hO.ψ hO.θ (hO.ψ ▸ ch.W.ψ_std) (hO.θ ▸ ch.W.θ_is) n1.cart n0.cart σ1 σ0 hσ1 hσ0
    (fun τ => ch.W.cart_is _ (by simp only [GlobalTheory.ChiGrid.Node.InRange]; omega) τ)
    (fun τ => ch.W.cart_is _ (by simp only [GlobalTheory.ChiGrid.Node.InRange]; omega) τ) hc hfin.1 (ρ i)
  exact ⟨p, heq_ker n1.sp n0.sp (G.X i 0).ω (ch.W.om (.chi i 0)) (harr.omX i 0 hi (Nat.zero_le _)) _ _ hp⟩

end GlobalTheory.RowKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeAlgebraMapMono
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx

section Mono

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil}
  {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} {S : GridChoice W Set.univ}

theorem charsIn_mono (h : CharsIn G σ) (hσ : Set.range σ ⊆ Set.range σ') : CharsIn G σ' :=
  ⟨fun j w x => hσ (h.mu0 j w x), fun t w x => hσ (h.xi t w x),
    fun i a b w x => hσ (h.chi i a b w x), fun v hv => hσ (h.eta v hv), fun v hv => hσ (h.chiPsi v hv),
    fun v hv => hσ (h.del v hv), fun v hv => hσ (h.del' v hv)⟩

theorem rootCl_mono (h : RootCl σ S) (hσ : Set.range σ ⊆ Set.range σ') : RootCl σ' S :=
  ⟨fun z hz => hσ (h.1 z hz), fun t w hw z hz => hσ (h.2.1 t w hw z hz), fun w hw => hσ (h.2.2 w hw)⟩

theorem phaseCl_mono (h : PhaseCl σ S) (hσ : Set.range σ ⊆ Set.range σ') : PhaseCl σ' S :=
  fun t Φ β hβ w x y e a b => hσ (h t Φ β hβ w x y e a b)

theorem jetCl_mono (h : JetCl σ S) (hσ : Set.range σ ⊆ Set.range σ') : JetCl σ' S :=
  fun t Φ β hβ τ hτ d hd c => ⟨fun j a b => hσ ((h t Φ β hβ τ hτ d hd c).1 j a b),
    fun i a b => hσ ((h t Φ β hβ τ hτ d hd c).2 i a b)⟩

theorem lRatios_mono {μ₀ : T} (h : ∀ i j, LRatiosIn G σ μ₀ i j) (hσ : Set.range σ ⊆ Set.range σ') :
    ∀ i j, LRatiosIn G σ' μ₀ i j :=
  fun i j t Λ Λ₀ a b s c d e => hσ (h i j t Λ Λ₀ a b s c d e)

theorem botCl_mono (h : BotCl W σ) (hσ : Set.range σ ⊆ Set.range σ') : BotCl W σ' := by
  intro i j
  obtain ⟨A, A', WW, X, h1, Ω, Ω', h2, h3, H⟩ := h i j
  exact ⟨A, A', WW, X, h1, Ω, Ω', h2, h3, fun t g hg =>
    ⟨fun k hk => hσ ((H t g hg).1 k hk), fun k hk => hσ ((H t g hg).2 k hk)⟩⟩

end Mono

theorem range_algebraMap_mono {M M' : IntermediateField ℚ ℂ} (h : M ≤ M') :
    Set.range (algebraMap M ℂ) ⊆ Set.range (algebraMap M' ℂ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x.1, h x.2⟩, rfl⟩

theorem InNF.and {Q Q' : ∀ M : IntermediateField ℚ ℂ, (M →+* ℂ) → Prop}
    (hQ : ∀ M M' : IntermediateField ℚ ℂ, M ≤ M' → Q M (algebraMap M ℂ) → Q M' (algebraMap M' ℂ))
    (hQ' : ∀ M M' : IntermediateField ℚ ℂ, M ≤ M' → Q' M (algebraMap M ℂ) → Q' M' (algebraMap M' ℂ))
    (h : InNF Q) (h' : InNF Q') : InNF fun M σ => Q M σ ∧ Q' M σ := by
  obtain ⟨M, hM, hq⟩ := h
  obtain ⟨M', hM', hq'⟩ := h'
  exact ⟨M ⊔ M', IntermediateField.finiteDimensional_sup M M', hQ _ _ le_sup_left hq, hQ' _ _ le_sup_right hq'⟩

theorem nfAll_of : NFChars → NFRoot → NFPhase → NFJet → NFRatio → NFBot → NFAll := by
  intro h1 h2 h3 h4 h5 h6
  obtain ⟨CF0, H⟩ := Big.and h1 (Big.and h2 (Big.and h3 (Big.and h4 (Big.and h5 h6))))
  refine ⟨CF0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi ha => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch hi ha
  have k := InNF.and (fun M M' h q => charsIn_mono q (range_algebraMap_mono h))
    (fun M M' h q => rootCl_mono q (range_algebraMap_mono h)) c1 c2
  have k := InNF.and (fun M M' h q => ⟨charsIn_mono q.1 (range_algebraMap_mono h), rootCl_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => phaseCl_mono q (range_algebraMap_mono h)) k c3
  have k := InNF.and (fun M M' h q => ⟨⟨charsIn_mono q.1.1 (range_algebraMap_mono h), rootCl_mono q.1.2 (range_algebraMap_mono h)⟩,
      phaseCl_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => jetCl_mono q (range_algebraMap_mono h)) k c4
  have k := InNF.and (fun M M' h q => ⟨⟨⟨charsIn_mono q.1.1.1 (range_algebraMap_mono h),
      rootCl_mono q.1.1.2 (range_algebraMap_mono h)⟩, phaseCl_mono q.1.2 (range_algebraMap_mono h)⟩,
      jetCl_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => lRatios_mono q (range_algebraMap_mono h)) k c5
  have k := InNF.and (fun M M' h q => ⟨⟨⟨⟨charsIn_mono q.1.1.1.1 (range_algebraMap_mono h),
      rootCl_mono q.1.1.1.2 (range_algebraMap_mono h)⟩, phaseCl_mono q.1.1.2 (range_algebraMap_mono h)⟩,
      jetCl_mono q.1.2 (range_algebraMap_mono h)⟩, lRatios_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => botCl_mono q (range_algebraMap_mono h)) k c6
  obtain ⟨M, hM, ⟨⟨⟨⟨⟨q1, q2⟩, q3⟩, q4⟩, q5⟩, q6⟩⟩ := k
  exact ⟨M, hM, ⟨q1, q2, q3, q4, q5, q6⟩⟩

end GlobalTheory.RowEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealActionOnVertexWeightContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RealActCont

theorem realAct_inv_continuous : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (θ : InfFam D), IsInfFam θ →
    ∀ (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (Λ : Module.Dual ℂ (VV ℂ (wt G X))) (w : VV ℂ (wt G X)),
    Continuous fun k : GinfC (G.V X) => Λ (realAct θ fr X ((k : GA D (G.V X))⁻¹) w) := by
  intro D T L sc G θ hθ fr X Λ w
  classical
  obtain ⟨hc, -⟩ := GlobalTheory.CoefModel.realGL_laws hθ (G.V X)
  have hG : ∀ _τ : D.what₂.Tau, (1 : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).PosDef := fun _ => Matrix.PosDef.one
  let A : GinfC (G.V X) → D.what₂.Tau → GL (Fin (G.V X).rank) ℂ :=
    fun k => invTrK (realIn θ fr X ((k : GA D (G.V X))⁻¹))
  have hA : ∀ τ, Continuous fun k => (A k τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) := by
    intro τ
    have e : ∀ k : GinfC (G.V X), (A k τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) =
        Matrix.transpose ((((frGL fr X τ)⁻¹ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) *
          Formalism.L2.Pj.archM (G.V X) (θ τ) (k : GA D (G.V X)) * (frGL fr X τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ)) := by
      intro k
      simp only [A, map_inv]
      show ((((realIn θ fr X (k : GA D (G.V X)) τ)⁻¹)⁻¹ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).transpose = _
      rw [inv_inv]
      simp [realIn, MulAut.conj_apply, GlobalTheory.CoefModel.realGL_coe]
    refine Continuous.congr ?_ fun k => (e k).symm
    exact ((continuous_const.mul ((hc τ).comp continuous_subtype_val)).mul continuous_const).matrix_transpose
  have key := GlobalTheory.CoefModel.continuous_rhoH (wt G X) hG A hA (GlobalTheory.CoefModel.toHilb (wt G X) hG w)
  have hΛ : Continuous (Λ ∘ₗ (GlobalTheory.CoefModel.toHilb (wt G X) hG).symm.toLinearMap) :=
    LinearMap.continuous_of_finiteDimensional _
  refine (hΛ.comp key).congr fun k => ?_
  simp only [Function.comp_apply, GlobalTheory.CoefModel.rhoH_toHilb, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

end GlobalTheory.RealActCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinersProportionalOfHarishChandra
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ArchRec

theorem itLine_of_hypotheses :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItLine D :=
  GlobalTheory.T.realThetaIntertwiners_proportional_of_discreteSeries

end GlobalTheory.ArchRec
end

