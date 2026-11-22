import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0529
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0366
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateLast
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastRowMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem negGA_mem_fin (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem fockComp_mul_right (B : VertexFrames G) (i : ℕ) (hi : (Pair.chi i D.R.m : Pair T).InRange D.R.m)
    {f : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ} (hf : IsThetaFunO W.ψ _ _ f)
    (a : FinPt G (.grid i D.R.m)) (b h : FinPt G (.grid (i + 1) D.R.m)) :
    fockComp W B (.chi i D.R.m : Pair T) f a (b * h) =
      fockComp W B (.chi i D.R.m : Pair T) (W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m : Pair T) 1 h.1) f) a b := by
  unfold fockComp
  congr 1
  funext k
  unfold jetTab kerFin GridData.Weil.ker thetaKO
  have e1 : G.toPair (.chi i D.R.m : Pair T) (a : GA D (G.V (Pair.chi i D.R.m : Pair T).small))
      ((b * h : FinPt G (.grid (i + 1) D.R.m)) : GA D _) =
      G.toPair (.chi i D.R.m : Pair T) a b * G.toPair (.chi i D.R.m : Pair T) 1 h.1 := by
    simp [GridData.toPair, Prod.ext_iff, map_mul]
  have e2 : G.toPair (.chi i D.R.m : Pair T) 1 h.1 = (negGA _ h.1, (1 : GA D _)) := rfl
  rw [e1, map_mul, Module.End.mul_apply, e2]
  unfold fockIn
  rw [GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om _) (W.om_is _ hi) W.θ W.θ_is (negGA _ h.1) (negGA_mem_fin _ h.2)
    1 (one_mem _) _ _ _ _ f _ hf]

theorem update_grid_eq {a b : ℕ} (h : a = b) (y : ∀ i, FinPt G (.grid i D.R.m)) (v : FinPt G (.grid a D.R.m)) :
    Function.update y a v b = h ▸ v := by
  subst h; simp

theorem cast_mul_grid {a b : ℕ} (h : a = b) (y : ∀ i, FinPt G (.grid i D.R.m)) (p : FinPt G (.grid a D.R.m)) :
    (h ▸ (y a * p) : FinPt G (.grid b D.R.m)) = y b * (h ▸ p : FinPt G (.grid b D.R.m)) := by
  subst h; rfl

theorem cast_conj_grid {a b : ℕ} (h : a = b) (u : ∀ X : Node, FinPt G X) (p : FinPt G (.grid a D.R.m)) :
    (h ▸ ((u (.grid a D.R.m))⁻¹ * p * u (.grid a D.R.m)) : FinPt G (.grid b D.R.m)) =
      (u (.grid b D.R.m))⁻¹ * (h ▸ p : FinPt G (.grid b D.R.m)) * u (.grid b D.R.m) := by
  subst h; rfl

end GlobalTheory.LastRowMove

namespace GlobalTheory.LastRowMove

theorem rowMapV_update_last : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m)),
    IsThetaFunO W.ψ (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) (gs (lastIx D)) →
    rowMapV S gs (Function.update y D.R.m (y D.R.m * k)) = rowMapV S (Function.update gs (lastIx D) (rowShift S k (gs (lastIx D)))) y := by
  intro D T L sc G W U S gs y k hf
  unfold rowMapV
  refine congrArg (fun q => LinearMap.comp (chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m))) q D.R.m) _) ?_
  funext j
  by_cases hjm : j < D.R.m
  · rw [dif_pos hjm, dif_pos hjm]
    by_cases hj1 : j + 1 < D.R.m
    · have h1 : j ≠ D.R.m := by omega
      have h2 : j + 1 ≠ D.R.m := by omega
      have h3 : (⟨j, hjm⟩ : Fin D.R.m) ≠ lastIx D := by
        intro h; have := congrArg Fin.val h; simp [lastIx] at this; omega
      rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
    · obtain rfl : j = (lastIx D : ℕ) := by simp [lastIx]; omega
      have h1 : ((lastIx D : ℕ)) ≠ D.R.m := by have := lastIx_succ D; omega
      rw [Function.update_of_ne h1, update_grid_eq (lastIx_succ D), cast_mul_grid (lastIx_succ D)]
      have e : ∀ a p v : FinPt G (.grid ((lastIx D : ℕ) + 1) D.R.m), a * p * v = a * v * (v⁻¹ * p * v) := by
        intro a p v; group
      rw [e, ← cast_conj_grid (lastIx_succ D) S.N.u]
      have hf' : IsThetaFunO W.ψ _ _ (gs ⟨(lastIx D : ℕ), hjm⟩) := hf
      rw [fockComp_mul_right _ _ (inRange_chi (lastIx D)) hf',
        show Function.update gs (lastIx D) (rowShift S k (gs (lastIx D))) ⟨(lastIx D : ℕ), hjm⟩ =
          rowShift S k (gs (lastIx D)) from Function.update_self _ _ _]
      rfl
  · rw [dif_neg hjm, dif_neg hjm]

end GlobalTheory.LastRowMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftEq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastVertexMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def colPt (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)) :
    GA D (G.pS (.top t (lastIx D))) × GA D (G.pT (.top t (lastIx D))) :=
  G.toPair (.top t (lastIx D)) 1 (topLast ((S.N.u (.top D.R.m))⁻¹ * g * S.N.u (.top D.R.m))).1

theorem colShift_eq (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)) :
    colShift S t g = W.om _ (colPt S t g) := rfl

def rowPt (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)) :
    GA D (G.pS (.chi (lastIx D) D.R.m : Pair T)) × GA D (G.pT (.chi (lastIx D) D.R.m : Pair T)) :=
  G.toPair (.chi (lastIx D) D.R.m) 1 (gridLast ((S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m))).1

theorem rowShift_eq (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)) :
    rowShift S k = W.om (.chi (lastIx D) D.R.m) (rowPt S k) := rfl

def stdLat (S : GridChoice W U) (p : Pair T) : AddSubgroup (WO (G.pS p) (G.pT p)) :=
  latO (G.pS p) (G.pT p) (S.N.latS p : Set _) (S.N.latT p : Set _) fun _ => True

end GlobalTheory.LastVertexMove

namespace GlobalTheory.LastVertexMove

variable {D : D7}

def moveFn {A B : HSp D} (q : GA D A × GA D B) (Φ : WO A B → ℂ) : WO A B → ℂ := fun x => Φ (actO A B q.1⁻¹ q.2⁻¹ x)

end GlobalTheory.LastVertexMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSizesNR
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

def rowSizes (D : D7) : Sizes where
  k := D.R.k
  m := D.R.m
  s := sLen D
  t := D.R.t
  k_pos := by have := D.R.m_add_three_le_k; omega
  k_even := D.R.k_even
  m_pos := by have := D.R.two_le_m; omega
  m_even := D.R.m_even
  s_odd := odd_sLen D
  t_odd := D.R.t_odd

theorem rowSizes_nR (D : D7) (j : ℕ) : (rowSizes D).nR j = rankX D j := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  simp only [Sizes.nR, rowSizes, rankX, rankP, nRk, sLen, Ranks.r]
  zify [show 1 ≤ D.R.k + D.R.m by omega, show 1 ≤ D.R.k + D.R.m - 1 + 6 by omega] at *
  push_cast
  ring_nf

theorem rowSizes_nC (D : D7) (i : ℕ) : (rowSizes D).nC i = rankV D i D.R.m := by
  simp only [Sizes.nC, rowSizes, rankV, Ranks.r]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem rank_top (G : GridData L sc) {j : ℕ} (hj : j ≤ D.R.m) : (G.V (.top j)).rank = (rowSizes D).nR j := by
  rw [rowSizes_nR]
  rcases j with _ | j
  · exact ((G.sp.P_is D.R.m le_rfl).rank).trans (by simp [rankX])
  · exact (G.sp.X_is (j + 1) (by omega) hj).rank

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem rank_gridM (G : GridData L sc) {i : ℕ} (hi : i ≤ D.R.m) : (G.V (.grid i D.R.m)).rank = (rowSizes D).nC i := by
  rw [rowSizes_nC]
  rcases i with _ | i
  · show (columnBlock L D.R.m).sp.rank = _
    rw [colY_m]
    exact D.sp.X'_rank.trans (by simp [rankV, Ranks.rankX'])
  · exact (G.sp.V_is (i + 1) D.R.m (by omega) hi le_rfl).rank

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

def rowEntries (D : D7) (C : ℝ) (τ : D.what₂.Tau) : Entries (rowSizes D) where
  a l := (num D C τ).a l
  c i := (num D C τ).cen (i + 1)
  v i := (num D C τ).v (i + 2)
  u i := (num D C τ).vHalf (i + 2)
  b j := (num D C τ).b (j + 1)
  e j := (num D C τ).e (j + 1)

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def trCol (G : GridData L sc) (j : Fin D.R.m) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₐ[ℂ]
      Pol D.what₂.Tau ((rowSizes D).nR j) ((rowSizes D).nR (j + 1)) :=
  MvPolynomial.rename fun x => (x.1, Fin.cast (rank_top G (by omega)) x.2.1, Fin.cast (rank_top G j.2.le) x.2.2)

def trRow (G : GridData L sc) (i : Fin D.R.m) :
    PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank →ₐ[ℂ]
      Pol D.what₂.Tau ((rowSizes D).nC i) ((rowSizes D).nC (i + 1)) :=
  MvPolynomial.rename fun x => (x.1, Fin.cast (rank_gridM G (by omega)) x.2.2, Fin.cast (rank_gridM G i.2.le) x.2.1)

example (G : GridData L sc) : PolCol G = ∀ j : Fin D.R.m, PolF D (G.V (.top ((j : ℕ) + 1))).rank (G.V (.top j)).rank := rfl
example (G : GridData L sc) : PolRow G = ∀ i : Fin D.R.m, PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid ((i : ℕ) + 1) D.R.m)).rank := rfl

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestChoiceDatumSurjectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTestChoice_datum_surjective : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (Φ : ch.G.Datum), ∃ a, ch.Phi a = Φ := by
  first | exact @GlobalTheory.ChoiceSurjectivity.choice_phi_surj | exact GlobalTheory.ChoiceSurjectivity.choice_phi_surj | (intros; apply GlobalTheory.ChoiceSurjectivity.choice_phi_surj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHilbertModelsOfChoiceClaims
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowClaim

namespace GlobalTheory.RowTestFromClaims

open GlobalTheory.RowTest

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem sum_gE (R : RealDat D A Ks) (hE : R.models_HE) (hg : R.models_gE) (y : R.HE.H) :
    ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gE g y = y := by
  have hmem : R.HE.e y ∈ R.EEat R.triv := hE.2.1 ▸ LinearMap.mem_range_self _ _
  have hfix := ((mem_goodPart _ _ _ _ _ _).1 hmem).2
  apply hE.1
  rw [map_sum]
  simp_rw [map_smul, hg]
  ext v
  rw [← hfix v]
  simp only [RealDat.e0, gaL, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply,
    MultilinearMap.sum_apply, MultilinearMap.smul_apply, postOn_apply]
  rfl

theorem rat_of_formula {K : Type} [Field K] (σ : K →+* ℂ) {z : K} {c c₀ κ p w : ℂ} (hz : σ z ≠ 0) (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (hκ : κ ≠ 0) (h : σ z * c * p = κ * w) (hw : w ∈ Set.range σ) (hr : c / c₀ ∈ Set.range σ) : ∃ y, σ y = c₀ * κ⁻¹ * p := by
  obtain ⟨w', rfl⟩ := hw
  obtain ⟨r', hr'⟩ := hr
  refine ⟨w' / (z * r'), ?_⟩
  rw [map_div₀, map_mul, hr']
  have hp : p = κ * σ w' / (σ z * c) := by
    rw [eq_div_iff (mul_ne_zero hz hc), ← h]
    ring
  rw [hp]
  field_simp

set_option maxHeartbeats 1000000 in

theorem exists_good (hP : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hC : GlobalTheory.Hk3.Core R F) (t : T0)
    (x : A.fam.amb.FR t) :
    ∃ x' : A.fam.amb.FR t, x' ∈ (A.fam.R t).goodF A.fam.X ∧ R.Th t (R.jX t x') = R.Th t (R.jX t x) := by
  obtain ⟨hth, -⟩ := GlobalTheory.LiftGroupEquiv.th_thG_act hP R F hC
  have hga : goodAt A.fam.X (⊥ : Subgroup G) 1 = idemOf A.X := Formalism.IndefR.CxPass.LevelOperators.goodAt_bot _ _
  have hmem : (A.fam.R t).S.gaOp (A.fam.R t).r (idemOf A.X) x ∈ (A.fam.R t).goodF A.fam.X := by
    unfold BlockDat.goodF
    rw [hga]
    exact LinearMap.mem_range_self _ x
  refine ⟨_, hmem, ?_⟩
  conv_rhs => rw [← sum_gE R hC.models.HE hC.models.gE (R.Th t (R.jX t x))]
  simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smulₛₗ, map_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hth t g x]

private theorem exists_linearMap_eq_psiK {R : RealDat D A Ks} (ch : Choice R) (hlin : ∀ a u, ConvK ch a u) :
    ∃ f : Fin ch.n → (R.HE.H →ₗ[ℂ] ℂ), ∀ a u, f a u = psiK ch a u :=
  ⟨fun a =>
    { toFun := psiK ch a
      map_add' := fun u u' => by
        simp only [psiK, map_add]
        exact GlobalTheory.FunObj.fPsiPhi_add ch.W ch.M (hlin a u) (hlin a u')
      map_smul' := fun b u => by
        have h1 := GlobalTheory.FunObj.fPsiPhi_smul ch.W ch.M ch.ρ ch.ξ 1 b (ch.col a) (ch.Phi a) (ch.form u)
        rw [one_smul, one_mul] at h1
        simp only [psiK, map_smul, RingHom.id_apply, smul_eq_mul]
        exact h1 }, fun _ _ => rfl⟩

private theorem rowTestModel_of_scaled_values_rational {R : RealDat D A Ks} (ch : Choice R) (hlin : ∀ a u, ConvK ch a u)
    (hinj : ∀ u, (∀ a, psiK ch a u = 0) → u = 0) {k : ℂ} (hk : k ≠ 0)
    (hval : ∀ t x a, ∃ z : D.what₂.LL, D.what₂.embLL z = k * psiK ch a (R.Th t (R.jX t x))) :
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R := by
  obtain ⟨f, hf⟩ := exists_linearMap_eq_psiK ch hlin
  refine ⟨ch.n, fun a => k • f a, ?_, ?_⟩
  · intro e he
    apply hinj
    intro a
    have h1 := he a
    rw [LinearMap.smul_apply, hf, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hk
  · intro t x a
    obtain ⟨z, hz⟩ := hval t x a
    refine ⟨z, hz.trans ?_⟩
    exact (((LinearMap.smul_apply k (f a) _).trans (congrArg (k • ·) (hf a _))).trans (smul_eq_mul k _)).symm

set_option maxHeartbeats 1600000 in
private theorem exists_embLL_mul_psiK_eq_vK_of_formulaAt (hP : GlobalTheory.Published.CuspRapidDecay) {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (ch : Choice R) {κ : ℂ} {ze : T0 → D.what₂.LL} (hF : FormulaAt ch κ ze) (t : T0) (x : A.fam.amb.FR t) (a : Fin ch.n) :
    ∃ x' : A.fam.amb.FR t, D.what₂.embLL (ze t) * cTot ch t * psiK ch a (R.Th t (R.jX t x)) = κ * vK ch t x' a := by
  obtain ⟨x', hx', hxx⟩ := exists_good hP R F hC t x
  refine ⟨x', ?_⟩
  rw [← hxx]
  exact hF.2 t x' hx' a

set_option maxHeartbeats 1600000 in

theorem rowTest_of_choice (hP : GlobalTheory.Published.CuspRapidDecay) {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (ch : Choice R) (hlin : ∀ a u, ConvK ch a u) (hinj : ∀ u, (∀ a, psiK ch a u = 0) → u = 0)
    (hc : ∀ i j t, ch.c i j t ≠ 0) {κ : ℂ} {ze : T0 → D.what₂.LL} (hF : FormulaAt ch κ ze)
    (hv : ∀ t x a, vK ch t x a ∈ Set.range D.what₂.embLL) (hr : ∀ i j t, sqRatio ch i j t ∈ Set.range D.what₂.embLL) :
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R := by
  have hcT : ∀ t, cTot ch t ≠ 0 := fun t =>
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => hc i j t
  have hz0 : ∀ t, D.what₂.embLL (ze t) ≠ 0 := by
    intro t
    obtain ⟨n, hn, hze⟩ := hF.1 t
    rw [map_ne_zero]
    rintro h0
    rw [h0, zero_pow hn.ne'] at hze
    exact zero_ne_one hze
  by_cases hκ : κ = 0
  · subst hκ
    refine rowTestModel_of_scaled_values_rational ch hlin hinj one_ne_zero fun t x a => ?_
    obtain ⟨x', hfo⟩ := exists_embLL_mul_psiK_eq_vK_of_formulaAt hP hC ch hF t x a
    have hp : psiK ch a (R.Th t (R.jX t x)) = 0 :=
      (mul_eq_zero.1 (hfo.trans (zero_mul _))).resolve_left (mul_ne_zero (hz0 t) (hcT t))
    exact ⟨0, (map_zero D.what₂.embLL).trans (hp.symm.trans (one_mul _).symm)⟩
  · refine rowTestModel_of_scaled_values_rational ch hlin hinj (mul_ne_zero (hcT A.μ0) (inv_ne_zero hκ)) fun t x a => ?_
    obtain ⟨x', hfo⟩ := exists_embLL_mul_psiK_eq_vK_of_formulaAt hP hC ch hF t x a
    have hrat : cTot ch t / cTot ch A.μ0 ∈ Set.range D.what₂.embLL := by
      have he : cTot ch t / cTot ch A.μ0 = ∏ i, ∏ j, sqRatio ch i j t := by
        simp only [cTot, sqRatio, Finset.prod_div_distrib]
      rw [he]
      exact RingHom.mem_fieldRange.1 (Subfield.prod_mem _ fun i _ =>
        Subfield.prod_mem _ fun j _ => RingHom.mem_fieldRange.2 (hr i j t))
    exact rat_of_formula D.what₂.embLL (hz0 t) (hcT t) (hcT _) hκ hfo (hv t x' a) hrat

set_option maxHeartbeats 1000000 in

theorem rowTestModel_of_claims : GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.RowClaim.HidaSetting large₂ R F → (∃ ch : GlobalTheory.RowTest.Choice R, ch.Is ∧ ch.AtScale CF large₂.sc.b ∧ ch.FieldOK) → GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R := by
  intro hP hL hI hC _ hF hR hRa
  obtain ⟨CF0, h⟩ := Big.and (Big.and (Big.and (Big.and (Big.and hL hI) hC) hF) hR) hRa
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := h ε CF hCF
  refine ⟨x₀, fun D large₂ hε hxl G _ _ Pl0 T0 A Ks _ _ _ R F hSet => ?_⟩
  rintro ⟨ch, hch, hsc, hfld⟩
  obtain ⟨⟨⟨⟨⟨hlin, hinj⟩, hcst⟩, hfor⟩, hrat⟩, hra⟩ := hx D large₂ hε hxl G Pl0 T0 A Ks R F hSet ch hch hsc
  obtain ⟨κ, ze, hFo⟩ := hfor hfld
  exact rowTest_of_choice hP hSet.core ch hlin hinj (fun i j t => (hcst i j t).2) hFo (hrat hfld) (hra hfld)

end GlobalTheory.RowTestFromClaims
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzTendstoOperatorCurveOfPointwise
section
open Filter Topology
open scoped Uniformity

namespace GlobalTheory

theorem schwartz_tendsto_apply_of_tendsto_pointwise :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : ℝ → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ f, Filter.Tendsto (fun t => S t f) (nhdsWithin 0 {0}ᶜ) (nhds f)) →
    ∀ (g : ℝ → SchwartzMap V ℂ) (g₀ : SchwartzMap V ℂ), Filter.Tendsto g (nhdsWithin 0 {0}ᶜ) (nhds g₀) →
      Filter.Tendsto (fun t => S t (g t)) (nhdsWithin 0 {0}ᶜ) (nhds g₀) := by
  intro V _ _ _ S hS g g₀ hg
  haveI : BarrelledSpace ℂ (SchwartzMap V ℂ) := schwartzMap_barrelledSpace V
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  have hq := schwartz_withSeminorms ℂ V ℂ
  have hUE : UniformEquicontinuous ((↑) ∘ fun n => S (u n)) := by
    refine hq.banach_steinhaus (𝓕 := fun n => S (u n)) ?_
    intro k f
    exact ((hq.continuous_seminorm k).tendsto f).comp ((hS f).comp hu) |>.bddAbove_range
  have hE := hUE.equicontinuous g₀
  have h1 : Tendsto (fun n => (S (u n) g₀, S (u n) (g (u n)))) atTop (𝓤 (SchwartzMap V ℂ)) := by
    intro U hU
    have := (hg.comp hu).eventually (hE U hU)
    rw [Filter.mem_map]
    exact this.mono fun n hn => hn n
  exact ((hS g₀).comp hu).congr_uniformity h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingExchange
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.KerStabFin

theorem stab_fin : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F), ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F v), ∀ Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p', om' (1, h) Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  intro _ D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _ _ hO hT Pi rf rl p p' hM v h hh Φ hΦ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  obtain ⟨g, hg, rfl⟩ := GlobalTheory.SquareAgree.KapOnto.kapX_onto D X e Γ.W hO.JX v h hh
  rw [mem_kerPD hstd] at hΦ ⊢
  obtain ⟨_, Φ₀, hΦ₀, hDat, hp⟩ := hΦ
  have hW := hO.weilB Φ Φ₀ hDat 1 g
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ 1 = 1 :=
    Subtype.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_one])
  rw [h1] at hW
  have hmem : ωB (1, g) Φ₀ ∈ algF ψ θ false A₁ B := hM.mapB.stabX.1 g hg Φ₀ hΦ₀
  obtain ⟨ΦD, hΦD, hD'⟩ := hO.algB _ hmem
  have heq := GlobalTheory.ThetaInj.theta_inj Γ.M' ψ hstd cB _ _ _ hW hD'
  refine ⟨heq ▸ hΦD, _, hmem, hW, ?_⟩
  rw [hM.mapB.eqf g hg Φ₀ hΦ₀, hp, map_zero]

end GlobalTheory.SquareAgree.KerStabFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTensorLatticeSelfDual
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitLatSelfDual

theorem latAtV_selfDual_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v →
    ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z →
      (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
        B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY v _ _ z hz
  exact GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X Y r s r' s' hB hX hY v z hz

end GlobalTheory.SplitLatSelfDual
end

