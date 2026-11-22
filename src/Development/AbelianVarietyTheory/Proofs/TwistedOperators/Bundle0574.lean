import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridJoinCubicSizeBound
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0557
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0561
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0543

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNonzeroRealIntertwinerGridArrow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin.ArrX

theorem vertex_par {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GlobalTheory.Grid.GridPre R) (hS : G.IsSpaces)
    (i j : ℕ) (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : (G.V i j).S = GlobalTheory.Grid.parV D i j := by
  rcases i with _ | i
  · rw [GlobalTheory.Grid.parV_zero D hj]
    show (GlobalTheory.Grid.row0 R j).S = _
    rcases j with _ | j
    · rfl
    · by_cases hlt : j + 1 < D.R.m
      · rw [← GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R hlt]
        dsimp only [GlobalTheory.Grid.nodeY]
        rw [Nat.min_eq_left hlt.le]
      · rw [← GlobalTheory.Grid.nodeX_eq_chainVertexAtRowZero_of_ge R hlt]
        have hm : j + 1 = D.R.m := by omega
        rw [hm]
  · exact (hS.vert i j hi hj).par

theorem exists_intertwiner : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∀ (ω : GlobalTheory.Grid.WRep (G.V (i + 1) j).V (G.V i j).V) (f : WO (G.V (i + 1) j).V (G.V i j).V → ℂ), GlobalTheory.Grid.IsWeil R.ψ true (G.V (i + 1) j).V (G.V i j).V (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ω → GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f → ∃ It : GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j) →ₗ[ℂ] SmT (G.V i j).M →ₗ[ℂ] SmT (G.V (i + 1) j).M, IsItW R.θ (G.V (i + 1) j).M (G.V i j).M ω (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f) It := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDS hHC hHost hSz F hCore hgap G' W hW G hS hC hSp hTh i j hi hj ω f hω hf
  have hθ : IsInfFam R.θ := hCore.models.inf
  obtain ⟨M₁, hcart, honb, hback⟩ := GlobalTheory.T.exists_discreteSeriesModel_negSpace_transfer (G.V (i + 1) j).M
  choose aS aT haS haT be de hdat hflip hlow using
    fun τ => GlobalTheory.GridJoin.ArrXPar.arrowX_par hSz hCore G hC i j hi hj τ
  have hSn := vertex_par G hS (i + 1) j hi hj
  have hSo := vertex_par G hS i j hi.le hj
  have hc : cart M₁ = GlobalTheory.Grid.cartS true (G.V (i + 1) j) := funext fun τ => (hcart τ).trans rfl
  have ho : onb M₁ = onb (G.V (i + 1) j).M := funext honb
  have hfin := hf.isFinVec
  have hne : f ≠ 0 := by
    unfold GlobalTheory.Grid.IsVac IsVacO at hf
    obtain ⟨-, ⟨-, -, -, -, ⟨⟨p, hp⟩, hq⟩⟩⟩ := hf
    intro h0
    have h1 := hq p hp
    rw [h0] at h1
    simp [nrm2] at h1
  have hvac : GlobalTheory.Chain.IsVacVec R.ψ R.θ M₁ (G.V i j).M f :=
    ⟨hfin.1, hne, fun τ => by rw [hc]; exact hfin.2 τ⟩
  obtain ⟨It₁, hIt₁⟩ := GlobalTheory.T.exists_realIntertwiner_largerSource_mirrorCase (GlobalTheory.Grid.sgn true (G.V (i + 1) j).V) (G.V i j).V
    (fun τ => ((G.V (i + 1) j).S τ).image fun x => (x.1, !x.2)) (G.V i j).S M₁ (G.V i j).M R.θ R.ψ
    (GlobalTheory.Grid.sLen D) aS aT hDS hHC hθ
    (fun τ => ⟨be τ, de τ, hdat τ, by rw [hSn]; exact hflip τ, by rw [hSo]; exact hlow τ⟩)
    _ _ (GlobalTheory.Grid.WRep.toSgn true ω) hω (fun τ => ⟨haS τ, haT τ⟩) f hvac
  obtain ⟨It, hIt⟩ := hback (G.V i j).M R.θ hθ ω _ It₁ hIt₁
  have hpt : GlobalTheory.Chain.ptOf R.ψ R.θ M₁ (G.V i j).M f =
      ⇑(GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f) := by
    unfold GlobalTheory.Chain.ptOf GlobalTheory.Grid.fock
    rw [hc, ho]
  exact ⟨It, hpt ▸ hIt⟩

end GlobalTheory.GridJoin.ArrX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalSplitStabilizerDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open Matrix

namespace GlobalTheory.RatSplitLat

theorem colLat_fg {K : Type} [Field K] [NumberField K] {n : ℕ} (B : GL (Fin n) K) : (colLat B).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem colLat_span {K : Type} [Field K] [NumberField K] {n : ℕ} (B : GL (Fin n) K) :
    Submodule.span K ((colLat B : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) = ⊤ := by
  unfold colLat
  rw [Submodule.span_span_of_tower]
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ j, (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) j •
      (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) := by
    funext a
    have := congrFun (show (B : Matrix (Fin n) (Fin n) K) *ᵥ (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) = x by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]) a
    conv_lhs => rw [← this]
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [hx]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem stab_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (H : AddSubgroup (Fin n → GlobalTheory.AdLat.RA F E)) (k : GL (Fin n) (GlobalTheory.AdLat.RA F E)) (N : ℕ)
    (h1 : ∀ z ∈ H, ∃ w ∈ H, k.1 *ᵥ z - z = N • w) (h2 : ∀ z ∈ H, (k⁻¹).1 *ᵥ z ∈ H) (y : Fin n → GlobalTheory.AdLat.RA F E) :
    y ∈ H ↔ k.1 *ᵥ y ∈ H := by
  constructor
  · intro hy
    obtain ⟨w, hw, e⟩ := h1 y hy
    rw [show k.1 *ᵥ y = (k.1 *ᵥ y - y) + y by abel, e]
    exact H.add_mem (H.nsmul_mem hw N) hy
  · intro hy
    have := h2 _ hy
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

set_option maxHeartbeats 1000000 in

theorem exists_rat_split_lat : ∀ {D : D7} (V : HSp D) (B : GL (Fin V.rank) D.host.E) (N : ℕ), 0 < N → ∀ g : GfC V,
    ∃ r s k : GfC V, GlobalTheory.MovedKappaEx.RatFin V r ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V s.1).1 ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) ↔
        Matrix.mulVec (Formalism.IndefR.Lev.finE V k.1).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B)) ∧ g = r * s * k := by
  intro D V B N hN g
  obtain ⟨-, -, -, -, c2, -, c1, gh, gd, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨γ', h', k', u1, u2, u3, hg, hs, hk, hki⟩ := GlobalTheory.T.exists_unitary_adelic_decomposition_split_support D.host.F D.host.E (GlobalTheory.Member.cF D) V.rank V.gramᵀ
    ⟨c2, c1, gh, gd⟩ (GlobalTheory.UnRep.Space.finrank_two D) (colLat B) (colLat_fg B) (colLat_span B) (finHom V g.1) N
    (GlobalTheory.UnRep.Space.isUnA_finHom V g.1) hN
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨r1, -, r3, -⟩ := GlobalTheory.Member.RatElt.rational_elements D V
  obtain ⟨h, hh, eh⟩ := lift h' u2
  obtain ⟨k, hk', ek⟩ := lift k' u3
  obtain ⟨γ, hγ⟩ := r3 γ' fun u v => by rw [GlobalTheory.UnRep.Space.herm_neg_eq, GlobalTheory.UnRep.Space.herm_neg_eq, u1]
  have eγ : (finHom V γ).1 = GlobalTheory.UnRep.fm D.host.F γ'.1 := GlobalTheory.Member.RatElt.fin_eq hγ
  have e : finHom V g.1 = finHom V γ * finHom V h * finHom V k := by
    apply Units.ext
    rw [hg, Units.val_mul, Units.val_mul, eγ, eh, ek]
  refine ⟨g * ⟨k, hk'⟩⁻¹ * ⟨h, hh⟩⁻¹, ⟨h, hh⟩, ⟨k, hk'⟩, ⟨γ, (r1 γ).2 ⟨γ', hγ⟩, ?_⟩, ?_, ?_, by rw [inv_mul_cancel_right, inv_mul_cancel_right]⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, map_mul, map_mul, map_inv, map_inv, e]
    rw [mul_inv_cancel_right, mul_inv_cancel_right]
  · change GlobalTheory.UnRep.SuppSplit _ N (finHom V h).1
    rw [eh]
    exact hs
  · intro v
    have key := GlobalTheory.StdFrames.hatL_of_hat (F := D.host.F) (colLat B) (colLat B) k'.1
      (stab_iff _ k' N hk hki) v
    have hm : (Formalism.IndefR.Lev.finE V k).1 =
        k'.1.map (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E) := by
      rw [← ek]; rfl
    refine key.trans (iff_of_eq ?_)
    exact congrArg (fun M => M *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B)) hm.symm

end GlobalTheory.RatSplitLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinCoefMultT
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColTypeLift

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

def FinCoef (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (φ : GA D V → ℂ) : Prop :=
  ∀ x, ∃ (n : ℕ) (L : Fin n → (M.H τ →L[ℂ] ℂ)) (v : Fin n → M.H τ),
    (∀ i, SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (v i)) ∧
    ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), φ (x * atTau θ V τ g) = ∑ i, L i (M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (v i))

theorem FinCoef.zero (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    FinCoef θ M τ 0 := fun _ => ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun g _ => by simp⟩

theorem FinCoef.add {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau}
    {φ ψ : GA D V → ℂ} (h₁ : FinCoef θ M τ φ) (h₂ : FinCoef θ M τ ψ) : FinCoef θ M τ (φ + ψ) := fun x => by
  obtain ⟨n₁, L₁, v₁, hv₁, e₁⟩ := h₁ x
  obtain ⟨n₂, L₂, v₂, hv₂, e₂⟩ := h₂ x
  refine ⟨n₁ + n₂, Fin.append L₁ L₂, Fin.append v₁ v₂, fun i => ?_, fun g hg => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using hv₁ i
    · simpa using hv₂ i
  · rw [Fin.sum_univ_add, Pi.add_apply, e₁ g hg, e₂ g hg]
    simp

theorem FinCoef.smul {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau}
    {φ : GA D V → ℂ} (c : ℂ) (h : FinCoef θ M τ φ) : FinCoef θ M τ (c • φ) := fun x => by
  obtain ⟨n, L, v, hv, e⟩ := h x
  refine ⟨n, fun i => c • L i, v, hv, fun g hg => ?_⟩
  rw [Pi.smul_apply, e g hg, Finset.smul_sum]
  simp

theorem FinCoef.sum {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau}
    {n : ℕ} {φ : Fin n → GA D V → ℂ} (h : ∀ i, FinCoef θ M τ (φ i)) : FinCoef θ M τ (∑ i, φ i) := by
  classical
  have : ∀ s : Finset (Fin n), FinCoef θ M τ (∑ i ∈ s, φ i) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using FinCoef.zero θ M τ
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih
  exact this Finset.univ

theorem finCoef_lift {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T)
    (z : SmT M) : FinCoef θ M τ (PiTensorProduct.lift T z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    intro x
    obtain ⟨ℓ, -, hℓ⟩ := GlobalTheory.DefiniteEnd.exists_sobCont M τ T f x
    have hsv : SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (f τ : M.H τ) := by
      have hw : ∀ w ∈ M.sm τ, SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) w := by
        intro w hw
        rw [GlobalTheory.SmVec.sm_eq M τ] at hw
        exact hw
      exact hw _ (f τ).2
    refine ⟨1, fun _ => r • LinearMap.toContinuousLinearMap ℓ, fun _ => (f τ : M.H τ), fun _ => hsv, fun g hg => ?_⟩
    have e1 := congrFun (hT.equiv τ g hg f ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩ rfl) x
    have e3 : T f (x * atTau θ V τ g) = ℓ (M.rep τ g (f τ)) := by
      rw [hℓ ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩]
      exact e1.symm
    rw [Fin.sum_univ_one, map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul, e3, LinearMap.coe_toContinuousLinearMap']
    rfl
  | add a b ha hb =>
    rw [map_add]
    exact ha.add hb

end GlobalTheory.ColTypeLift

namespace GlobalTheory.ColTypeLift

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

theorem finCoef_multT {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] (F : MultT θ M ∅ 1) (z : SmT M) : FinCoef θ M τ (F.1 z) := by
  have hm : PiTensorProduct.lift.symm F.1 ∈ Mult θ M ∅ 1 := (mem_multT θ M ∅ 1 F.1).1 F.2
  have key : ∀ T ∈ Mult θ M ∅ 1, FinCoef θ M τ (PiTensorProduct.lift T z) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem x hx => exact finCoef_lift M τ hx z
    | zero => simpa using FinCoef.zero θ M τ
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]; exact hx.add hy
    | smul c x _ hx => rw [map_smul, LinearMap.smul_apply]; exact hx.smul c
  have := key _ hm
  rwa [LinearEquiv.apply_symm_apply] at this

theorem isTypeAt_sum (θ : InfFam D) (N : Node D) (hs : N.V.SigOK) (hd : N.V.IsDefinite) (τ : D.what₂.Tau) {n : ℕ}
    (F : Fin n → N.Cusp θ) (z : Fin n → SmT N.M) : IsTypeAt θ N.V τ (N.S τ) (∑ i, (F i).1 (z i)) := by
  haveI := GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd N.M τ
  exact GlobalTheory.EndCusp.isTypeAt_of_finSum θ N.V τ (N.M.enum τ) (N.M.ds τ) (N.M.fr_unit τ) (N.M.fr_gram τ) _
    (FinCoef.sum fun i => finCoef_multT N.M τ (F i) (z i))

theorem xp_definite {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridPre R} (hG : G.Is)
    (k : ℕ) (hk : k ≤ D.R.m) : (G.Xp k).V.SigOK ∧ (G.Xp k).V.IsDefinite := by
  cases k with
  | zero =>
    have h := hG.spaces.P D.R.m le_rfl
    refine ⟨h.sigOK, fun τ => Or.inl ?_⟩
    rw [h.sig, h.rank]
    simp
  | succ k =>
    have h := hG.spaces.X k hk
    refine ⟨h.sigOK, fun τ => Or.inl ?_⟩
    rw [h.sig, h.rank]
    simp

end GlobalTheory.ColTypeLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumIsAlgebraicCombinationDefiniteBottom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BotFourierSnd

open GlobalTheory.PlaceModel GlobalTheory.AlgWave GlobalTheory.BotFourier GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

theorem unitChar_mem {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)}
    (he : IsIdemSum e S) {k : ℕ} {N : Matrix (Fin k) (Fin k) (Lev.EAf D)} (hN : IsIntM N) : unitChar ν e N ∈ Qb := by
  obtain ⟨-, -, -, m, hm, hord⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  unfold unitChar
  split_ifs with hu
  · obtain ⟨h1, h2, h3⟩ := hu.choose_spec
    have hdet : N.det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      let B : Matrix (Fin k) (Fin k) (Formalism.L2.Herm.intAf D.host.F D.host.E) := fun a b => ⟨_, hN a b⟩
      have hB : N = (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.mapMatrix B := rfl
      rw [hB, ← RingHom.map_det]
      exact (B.det).2
    have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
    have hfu : Formalism.L2.Pj.FinUnit hu.choose := ⟨h1, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (by
      rw [h2]; exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hdet)), GlobalTheory.PlaceDatum.finPart_mem_of_toEAf h3⟩
    have hpow := hord _ hfu
    refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := m) hm ?_)
    have e1 : (((ν hu.choose)⁻¹ : Circle) : ℂ) ^ m = Circle.coeHom (((ν hu.choose) ^ m)⁻¹) := by
      rw [← inv_pow, map_pow]; rfl
    rw [e1, hpow, inv_one, map_one]
    exact isAlgebraic_one
  · exact zero_mem _

theorem stdSnd_mem {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)}
    (he : IsIdemSum e S) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (A' WW : HSp D) (βA : GL (Fin A'.rank) (Lev.EAf D))
    (βW : GL (Fin WW.rank) (Lev.EAf D)) (x : WO A' WW) : stdSnd ν e I a A' WW βA βW x ∈ Qb := by
  unfold stdSnd
  split_ifs with hc
  · exact unitChar_mem hν he (GlobalTheory.CompanionTheory.StdSndTheta.isIntM_rightBlock hc.2.1)
  · exact zero_mem _

set_option maxHeartbeats 2000000 in

theorem isAlgComb_of_isThetaAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S WW : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)}
    (hSd : IsSelfDualC S ΛS) (hWd : IsSelfDualC WW ΛT) {e : AE D} (hee : e * e = e) (hinf : infPart D e = 0)
    {vac Φ f : WO S WW → ℂ} (hSB : IsSBHalf e (latO S WW ΛS ΛT fun _ => True) Φ) (hΦ : ∀ x, Φ x ∈ Qb)
    (hth : IsThetaAt ψ (symplO S WW) (heisO ψ S WW) e (latO S WW ΛS ΛT fun _ => True) 1 vac Φ f) :
    GlobalTheory.MovedAlg.IsAlgComb ψ S WW vac f := by
  classical
  have hinf' := GlobalTheory.PlaceDatum.infPart_cA hinf
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  rw [hall Tm hTm]
  set Λ : AddSubgroup (WO S WW) := latO S WW ΛS ΛT fun _ => True with hΛ

  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S WW ΛS ΛT hψ hSd hWd).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S WW _ _ hSd.1.fg hWd.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ ⊓ half S WW a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S WW _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have finX : ∀ x ∈ half S WW e, x.map (infPart D) = 0 := fun x hx =>
    GlobalTheory.PlaceDatum.infPart_of_half hinf ((isHalf_iff S WW).2 hx)
  have finY : ∀ y ∈ half S WW (cA D e), y.map (infPart D) = 0 := fun y hy =>
    GlobalTheory.PlaceDatum.infPart_of_half hinf' ((isHalf_iff S WW).2 hy)
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S WW => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S WW hk a, ← inv_smul_nsmul S WW hk b]
    exact congrArg _ hab
  have hb := isBichar_symplO S WW ψ

  obtain ⟨h1, k, hk, h2, h3⟩ := hSB
  have hmem := mem_algSpan (χ := fun x y : WO S WW => ψ (symplO S WW x y)) (X := half S WW e)
    (Y := half S WW (cA D e)) (L := Λ ⊓ half S WW e) (L' := Λ ⊓ half S WW (cA D e)) hb
    (fun x hx y hy => psi_mem hψ hSd hWd (finX x hx) (finY y hy)) inf_le_right inf_le_right
    (fun u hu y hy => (hdual u (finX u hu.2)).1 hu.1 y hy.1)
    (fun x hx h => ⟨(hdual x (finX x hx)).2 fun u hu => by
      have := h _ (hsm _ he' u hu)
      rwa [← symplO_smul, (mem_half S WW).1 hx] at this, hx⟩)
    (half_div S WW e) (half_div S WW _) tf
    (fun k hk => by
      obtain ⟨R, hR, h⟩ := hfin k hk
      refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
      obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
      refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e hee u hu, ?_⟩
      have := (mem_half S WW).1 ht.2
      rw [← this, htr, smul_add, smul_comm e k u])
    _ hΦ (fun t ht => (isHalf_iff S WW).1 (h1 t ht)) k hk
    (fun u hu => h2 u hu.1 ((isHalf_iff S WW).2 hu.2))
    (fun t ht => ⟨h3 t ht, (half S WW e).nsmul_mem ((isHalf_iff S WW).1 (h1 t ht)) _⟩)

  set V : Submodule Qb (WO S WW → ℂ) := Submodule.span Qb
    {F | ∃ w : WO S WW, w.map (infPart D) = 0 ∧ F = heisO ψ S WW w vac} with hV
  have hvac : Tm (halfInd e Λ) = vac := by simpa using hTm.vac
  have s0 := GlobalTheory.isSBHalf_halfInd e Λ
  have hT : ∀ Ψ ∈ algSpan (fun x y : WO S WW => ψ (symplO S WW x y)) (half S WW e) (half S WW (cA D e))
      (Λ ⊓ half S WW e), Tm Ψ ∈ V := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem _ hh =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hh
      have s1 : IsSBHalf e Λ fun t => ψ (symplO S WW t y) * halfInd e Λ t := by
        obtain ⟨k, hk, hk'⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' (S := S) (T := WW) hSd.1 hWd.1 y (finY y hy)
        obtain ⟨a1, k', hk1, a2, a3⟩ := s0
        refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
          fun t ht => ?_⟩
        · have e1 : halfInd e Λ (t + (k * k') • u) = halfInd e Λ t := by
            rw [mul_nsmul]
            exact a2 _ (nsmul_mem hu k) ((isHalf_iff S WW).2 (nsmul_mem ((isHalf_iff S WW).1 hh) k)) t
          have e2 : ψ (symplO S WW ((k * k') • u) y) = 1 := by
            rw [mul_nsmul']
            refine (hb.nsmul k _ y).trans ((hdual _ (finX _ (nsmul_mem ((isHalf_iff S WW).1 hh) k'))).1
              (nsmul_mem hu k') _ hk')
          simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
        · rw [mul_nsmul']
          exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
      have e1 : wave (fun x y : WO S WW => ψ (symplO S WW x y)) (Λ ⊓ half S WW e) x y =
          fun t => (fun t => ψ (symplO S WW t y) * halfInd e Λ t) (t + x) := by
        rw [halfInd_eq_ind]; rfl
      rw [e1, hTm.trans _ s1 x ((isHalf_iff S WW).2 hx), hTm.modul _ s0 y ((isHalf_iff S WW).2 hy), hvac]
      have e2 : heisO ψ S WW x (heisO ψ S WW y vac) =
          ψ (symplOH S WW x y) • heisO ψ S WW (x + y) vac := heisL_heisL S WW ψ x y vac
      rw [e2]
      refine smul_mem_of_mem (psiH_mem hψ hSd hWd (finX x hx) (finY y hy)) (Submodule.subset_span ⟨x + y, ?_, rfl⟩)
      refine Matrix.ext fun a b => ?_
      have q1 : infPart D (x a b) = 0 := congrFun (congrFun (finX x hx) a) b
      have q2 : infPart D (y a b) = 0 := congrFun (congrFun (finY y hy) a) b
      change infPart D (x a b + y a b) = 0
      rw [RingHom.map_add, q1, q2, add_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
    | smul c f _ hf =>
      change Tm ((c : ℂ) • f) ∈ V
      rw [map_smul]
      exact V.smul_mem c hf
  obtain ⟨n, f, g, hfg⟩ := (Submodule.mem_span_set').1 (hT _ hmem)
  choose w hw hgw using fun p => (g p).2
  refine ⟨n, fun p => (f p : ℂ), w, fun p => mem_algebraicClosure_iff.1 (f p).2, hw, ?_⟩
  rw [← hfg]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← hgw p]
  rfl

theorem finDatum'_isAlgComb : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X →
    ∀ t : T, GlobalTheory.MovedAlg.IsAlgComb W.ψ A' WW X.vac' (X.f' t) := by
  intro D T L sc G W i j A A' WW X hX t
  have hI := hX.is
  have hν := (hI.weil' t).hecT
  have he := hI.idem t
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum he)
  have hSd : IsSelfDualC A' X.rA'.Λ := hI.rigA'.1
  have hWd : IsSelfDualC WW X.rW.Λ := hI.rigW.1
  exact isAlgComb_of_isThetaAt hI.isVac'.1 hSd hWd (by rw [← RingHom.map_mul, hee]) hinf
    (GlobalTheory.CompanionTheory.StdSndTheta.stdSnd_isSB hν.1 he (GlobalTheory.ConstRatio.ideal_ne_bot X (locPl G) t) _ A' WW X.rA'.β X.rW.β _
      (GlobalTheory.CompanionTheory.StdSndTheta.exists_den_dualCoord hSd.1.fg hWd.1.fg X.rA'.β X.rW.β)
      (GlobalTheory.CompanionTheory.StdSndTheta.exists_mul_dualCoord hSd.1 hWd.1 hinf X.rA'.β X.rW.β))
    (fun x => stdSnd_mem hν.1 he _ _ A' WW X.rA'.β X.rW.β x) (hI.snd t)

end GlobalTheory.BotFourierSnd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionalIdealCompletionMulModulusOffExceptionaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdealCompletion_mul_modulus_offExceptional : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : GlobalTheory.ChiGrid.Consts) (v : GlobalTheory.FinPl.Pl D), v ∉ P.S0 → ∀ 𝔞 : GlobalTheory.SeeSaw.FI D, GlobalTheory.SeeSaw.idV (𝔞 * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 𝔞 v ∧ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 𝔞 v := by
  first | exact @GlobalTheory.ChiGrid.Places.idV_mul_modul | exact GlobalTheory.ChiGrid.Places.idV_mul_modul | (intros; apply GlobalTheory.ChiGrid.Places.idV_mul_modul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierInversionSchwartzBruhatStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialColumnFourier_inversion_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ⁻¹ m P (fourierInt ψ m P Ξ) = Ξ := by
  first | exact @GlobalTheory.ColFourier.fourierInt_inv_fourierInt | exact GlobalTheory.ColFourier.fourierInt_inv_fourierInt | (intros; apply GlobalTheory.ColFourier.fourierInt_inv_fourierInt <;> assumption)
end

