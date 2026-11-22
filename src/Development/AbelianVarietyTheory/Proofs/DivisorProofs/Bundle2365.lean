import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0768
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2268
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEqSmulArrowVacuaProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.VacRouteBig

open GlobalTheory.RouteSeesaw (box2 topR botR)

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
open GlobalTheory.VacUnique GlobalTheory.FockCompare in

theorem eq_smul_of_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) {f f' : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS ΛT f) (hth : IsThetaFunO ψ S T f')
    (hfock : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f')
    (hlat' : IsLatVac (heisO ψ S T)
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f') :
    ∃ a : ℂ, f' = a • f := by
  classical
  have hψ := hf.1
  have hθ : IsInfFam θ := hf.2.inf
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hΛS hΛT
  have hden := GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT hΛS.1 hΛT.1
  have hlat := hf.2.lat
  have hinf := fun u => latO_inf (u := u) S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    fun _ => True
  generalize latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at h1 h2 h3 hden hlat hlat' hinf
  choose ε hε1 hε2 using h3 f hlat
  have det : ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      IsLatVac (heisO ψ S T) Λ g → IsLatVac (heisO ψ S T) Λ g' →
      (∀ z, g' (iotaW σ T S z) = c * g (iotaW σ T S z)) → g' = c • g := by
    intro g g' c hg hg' hl hl' hz
    funext w
    obtain ⟨γ, z, u, hu, rfl⟩ := exists_decomp h h2 w
    rw [Pi.smul_apply, smul_eq_mul, hg.quasi, hg'.quasi, apply_real_add h hψ (hinf u hu) (hε2 u hu g hl),
      apply_real_add h hψ (hinf u hu) (hε2 u hu g' hl'), hz]
    ring
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 f = 1 := hn p hp
  have hne : (fun z : RW T S => f (iotaW σ T S z)) ≠ 0 := by
    intro h0
    have e := det f f 0 hf.2.theta hf.2.theta hlat hlat fun z => by rw [zero_mul]; exact congrFun h0 z
    rw [e] at n1
    simp [nrm2] at n1
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT
  have hsp : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
    have := span_piW_ratW_eq_top D θ σ h T S
    simpa only [piW_ratW hθ] using this
  have a1 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f hf.2.theta hf.2.fock
  have a2 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f' hth hfock
  let c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ := fun v =>
    if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * ε _ hv else 1
  have hc : ∀ v, ‖c v‖ = 1 := fun v => by
    simp only [c]
    split_ifs with hv
    · rw [norm_mul, hψ.1.2.1]
      rcases hε1 _ hv with e | e <;> rw [e] <;> simp
    · exact norm_one
  have law : ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) Λ g →
      ∀ v ∈ Λ.comap (finRat S T), ∀ z, g (iotaW σ T S (z + infRat S T v)) =
        c v * Complex.exp (-(Real.pi * Complex.I) * (omO S T z (infRat S T v) : ℂ)) * g (iotaW σ T S z) := by
    intro g hg hl v hv z
    have hv' : finRat S T (-v) ∈ Λ := (Λ.comap (finRat S T)).neg_mem hv
    rw [apply_add_infRat h hψ hg v (hε2 _ hv' g hl) z, ← j2]
    simp only [c, dif_pos hv']
  have hli := GlobalTheory.T.not_linearIndependent_alt (RW T S) (jO S T sS sT) (omO S T) j1 j2 j3 j4 (Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (infRat S T) (infRat_injective S T) hsp (Λ.comap (finRat S T))
    (fun x => by
      obtain ⟨N, hN, hx⟩ := hden x
      exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, AddMonoidHom.map_nsmul]⟩)
    (GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff D S T ψ Λ hψ hinf h1 h2 hden) c hc
    ![fun z => f (iotaW σ T S z), fun z => f' (iotaW σ T S z)]
    (fun k => by fin_cases k; exacts [a1.1, a2.1]) (fun k => by fin_cases k; exacts [a1.2, a2.2])
    (fun k => by fin_cases k; exacts [law f hf.2.theta hlat, law f' hth hlat'])
  rw [LinearIndependent.pair_iff' hne] at hli
  push_neg at hli
  obtain ⟨a, ha⟩ := hli
  exact ⟨a, det f f' a hf.2.theta hth hlat hlat' fun z => (congrFun ha z).symm⟩

theorem adjM_eq (S B : HSp D) (y : WO S B) : GlobalTheory.RouteSeesaw.adjM S B y = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B y := by
  unfold GlobalTheory.RouteSeesaw.adjM GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger
  rw [Matrix.mul_assoc]
  rfl

theorem heisO_adj (ψ : AddChar (AF D.host.F) ℂ) (S B : HSp D) (u : WO S B) (g : WO B S → ℂ) :
    heisO ψ (negSp S) B u (fun y => g (GlobalTheory.RouteSeesaw.adjM S B y)) =
      fun y => heisO ψ B S (GlobalTheory.RouteSeesaw.adjM S B u) g (GlobalTheory.RouteSeesaw.adjM S B y) := by
  funext y
  unfold heisO
  dsimp only
  rw [GlobalTheory.FockConj.symplOH_negSp, GlobalTheory.RouteSeesaw.adjM_add, adjM_eq, adjM_eq, GlobalTheory.AdjointPair.symplOH_dagger]

theorem heisenbergOperator_externalProduct_blocks (ψ : AddChar (AF D.host.F) ℂ) (S A B : HSp D) (φ : WO S A → ℂ) (φ' : WO S B → ℂ)
    (u : WO S (GlobalTheory.Doubling.hsum A B)) :
    heisO ψ S (GlobalTheory.Doubling.hsum A B) u (box2 φ φ') =
      box2 (heisO ψ S A (topR (A := A) (B := B) u) φ) (heisO ψ S B (botR (A := A) (B := B) u) φ') := by
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec, GlobalTheory.MixModel.OrthDec.heisO_boxT, GlobalTheory.SeesawSumTarget.boxT_sumDec,
    GlobalTheory.MixModel.OrthDec.resT_apply]
  dsimp only
  rw [GlobalTheory.SeesawSumTarget.pA_sumDec, GlobalTheory.SeesawSumTarget.pB_sumDec]

theorem isHalf_adjM (S B : HSp D) {e : AE D} {y : WO S B} (hy : IsHalf e y) :
    IsHalf (cA D e) (GlobalTheory.RouteSeesaw.adjM S B y) := fun a b => by
  have h : ∀ k l, cA D e * cA D (y k l) = cA D (y k l) := fun k l => by rw [← map_mul, hy k l]
  simp only [GlobalTheory.RouteSeesaw.adjM, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  linear_combination (incA D (S.gram⁻¹ a l) * incA D (B.gram k b)) * h k l

theorem isLatticeVacuum_externalProduct_adjoint (ψ : AddChar (AF D.host.F) ℂ) (S A B : HSp D) {ΛA : AddSubgroup (WO (negSp S) A)}
    {ΛB : AddSubgroup (WO B S)} {Λ : AddSubgroup (WO (negSp S) (GlobalTheory.Doubling.hsum A B))}
    (hΛ : ∀ u ∈ Λ, topR (A := A) (B := B) u ∈ ΛA ∧ GlobalTheory.RouteSeesaw.adjM S B (botR (A := A) (B := B) u) ∈ ΛB)
    {φ : WO (negSp S) A → ℂ} {g : WO B S → ℂ} (hφ : IsLatVac (heisO ψ (negSp S) A) ΛA φ)
    (hg : IsLatVac (heisO ψ B S) ΛB g) :
    IsLatVac (heisO ψ (negSp S) (GlobalTheory.Doubling.hsum A B)) Λ
      (box2 (S := negSp S) (A := A) (B := B) φ fun y => g (GlobalTheory.RouteSeesaw.adjM S B y)) := by
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have e1 : topR (A := A) (B := B) (2 • u) = 2 • topR (A := A) (B := B) u := rfl
    have e2 : GlobalTheory.RouteSeesaw.adjM S B (botR (A := A) (B := B) (2 • u)) =
        2 • GlobalTheory.RouteSeesaw.adjM S B (botR (A := A) (B := B) u) := by
      rw [two_nsmul, two_nsmul, ← GlobalTheory.RouteSeesaw.adjM_add]
      rfl
    rw [heisenbergOperator_externalProduct_blocks, heisO_adj, e1, e2, hφ.1 _ (hΛ u hu).1, hg.1 _ (hΛ u hu).2]
  · have h1 : IsHalf e (topR (A := A) (B := B) u) := fun a b => hh _ _
    have h2 : IsHalf e (botR (A := A) (B := B) u) := fun a b => hh _ _
    rw [heisenbergOperator_externalProduct_blocks, heisO_adj, hφ.2 e he _ (hΛ u hu).1 h1,
      hg.2 _ (GlobalTheory.PlaceModelSum.isSplitIdem_cA he) _ (hΛ u hu).2 (isHalf_adjM S B h2)]

theorem externalProduct_adjoint_ne_zero (S A B : HSp D) {φ : WO (negSp S) A → ℂ} {g : WO B S → ℂ} {x : WO (negSp S) A} {z : WO B S}
    (hx : φ x ≠ 0) (hz : g z ≠ 0) :
    (box2 (S := negSp S) (A := A) (B := B) φ fun y => g (GlobalTheory.RouteSeesaw.adjM S B y)) ≠ 0 := fun h0 => by
  let d := GlobalTheory.BiTransfer.sumDec A B
  have h := congrFun h0 ((d.resT (negSp S)).symm (x, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger B S z))
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec] at h
  unfold GlobalTheory.MixModel.OrthDec.boxT at h
  rw [AddEquiv.apply_symm_apply] at h
  dsimp only at h
  rw [adjM_eq, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger] at h
  exact mul_ne_zero hx hz h

theorem vac_eq_smul_vacA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (G.Λ (.grid (i + 1) (j + 1))) Λ (fun _ => True) : Set _) = orderingsOnSpW G i j →
      ∀ f, IsVacO W.ψ W.θ (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (fun τ => -W.cart (.grid (i + 1) (j + 1)) τ) (frSum AV AV₁).cart
        (G.Λ (.grid (i + 1) (j + 1))) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacA ρ i j := by
  intro D T L sc G μ₀ hL W ρ i j AV AV₁ hV hV₁ Λ hΛ hlat f hf
  have hX : (Node.grid (i + 1) (j + 1)).InRange D.R.m := ⟨i.2, j.2⟩
  obtain ⟨A, hA⟩ := exists_isGridFr W hX
  have u₁ := ρ.vX_is i (j + 1) i.2 j.2
  have u₂ := ρ.vT_is μ₀ (i + 1) j i.2 j.2
  have v₁ := u₁.2
  have v₂ := u₂.2
  have cA : (GlobalTheory.SquareComm.frSgn true A).cart = fun τ => -W.cart (.grid (↑i + 1) (↑j + 1)) τ := funext fun τ =>
    (GlobalTheory.PairLift.cart_frSgn true A τ).trans (congrArg Neg.neg (hA τ).2)
  have cA' : A.cart = W.cart _ := funext fun τ => (hA τ).2
  have cV : AV.cart = W.cart _ := funext fun τ => (hV τ).2
  have cV₁ : AV₁.cart = W.cart _ := funext fun τ => (hV₁ τ).2
  have w₁ : IsVacF W.ψ W.θ (GlobalTheory.SquareComm.frSgn true A) AV (ρ.vX i (j + 1)) := ⟨v₁.theta, fun τ => by
    rw [cA, cV]
    exact v₁.fock τ⟩
  have w₂ : IsVacF W.ψ W.θ AV₁ A (ρ.vT (i + 1) j) := ⟨v₂.theta, fun τ => by
    rw [cA', cV₁]
    exact v₂.fock τ⟩
  have w₃ := (GlobalTheory.SquareAlg.adj_ptF W.ψ_std W.θ_is A AV₁ w₂).1
  have hv := GlobalTheory.SquareAlg.isVacF_boxT (GlobalTheory.BiTransfer.sumDec _ _) (GlobalTheory.SquareComm.frSgn true A) (GlobalTheory.SquareComm.frSum AV AV₁) AV AV₁
    W.ψ_std W.θ_is (GlobalTheory.SquareAlg.qA_cart_frSum AV AV₁) (GlobalTheory.SquareAlg.qB_cart_frSum AV AV₁) w₁ w₃
  rw [GlobalTheory.SeesawSumTarget.boxT_sumDec] at hv
  have hfock := hv.2
  rw [cA] at hfock
  have hl : IsLatVac (heisO W.ψ (GlobalTheory.Grid.neg (spW G i j)) (spX G i j))
      (latO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (G.Λ (.grid (i + 1) (j + 1))) Λ fun _ => True) (vacA ρ i j) :=
    isLatticeVacuum_externalProduct_adjoint W.ψ (spW G i j) (spV G i j) (spV₁ G i j) (fun u hu => hlat.le hu) v₁.lat v₂.lat
  obtain ⟨a, ha⟩ := eq_smul_of_vac (S := GlobalTheory.Grid.neg (spW G i j)) (T := spX G i j) (f' := vacA ρ i j)
    (fun τ => isCartanInv_neg (W.cart_is _ hX τ)) (fun τ => GlobalTheory.CompactFockAction.cart_isCartanInv (frSum AV AV₁) τ)
    (isSelfDualC_neg (node_isV G hL hX).sd) hΛ hf hv.1 hfock hl
  obtain ⟨x, hx⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO u₁
  obtain ⟨z, hz⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO u₂
  have hne : vacA ρ i j ≠ 0 := externalProduct_adjoint_ne_zero (spW G i j) (spV G i j) (spV₁ G i j) hx hz
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hne (by rw [ha, zero_smul])
  exact ⟨a⁻¹, inv_ne_zero ha0, by rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

end GlobalTheory.TopFlip.VacRouteBig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakResolutionOfPrincipalisationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weak_resolution_of_principalisation : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (W : Scheme.{0}) [IsIntegral W] (p : W ⟶ Sp F) (n : ℕ), IsProjOver p → topologicalKrullDim W = n → ∃ (W' : Scheme.{0}) (s : W' ⟶ W) (U : W.Opens), IsIntegral W' ∧ SmoothOfRelativeDimension n (s ≫ p) ∧ IsProjOver (s ≫ p) ∧ (U : Set W).Nonempty ∧ IsIso (s ∣_ U) := by
  first | exact @GlobalTheory.WeakRes.weak_resolution | exact GlobalTheory.WeakRes.weak_resolution | (intros; apply GlobalTheory.WeakRes.weak_resolution <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.WtShape

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem laOf_real (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) (n : Fin ((dat p i).p + (dat p i).q)) :
    (laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ n : ℝ) = entR D i t n := by
  rw [← ent_cast, ← laOf_read p i τ t ht n, Rat.cast_intCast]

theorem anchor_real (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) :
    (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) = entR D i t (D.R.k - 1 - 1) := by
  have h : D.R.k - 1 - 1 < (dat p i).p + (dat p i).q := by
    have := D.R.m_add_three_le_k
    rw [dat_p]; omega
  unfold anchor
  rw [dif_pos h, laOf_real p i τ t ht]

theorem uW_real (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) (n : Fin ((dat p i).p + (dat p i).q)) :
    (uW p i τ n : ℝ) = entR D i t n - entR D i t (D.R.k - 1 - 1) := by
  rw [← laOf_real p i τ t ht n, ← anchor_real p i τ t ht, ← Int.cast_sub]
  rfl

theorem h0_eq : LevelStarExponents.h0 L = (p.h0 : ℝ) := by
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast p.hm
  unfold LevelStarExponents.h0
  rw [p.hh0]
  field_simp

theorem wtNum_at (P : ParameterChoice' D L) (T : ParamsT D L P) (hS : SizesAt L) (hx8 : 8 ≤ L.sc.x)
    (hy : 3 ≤ L.sc.x ^ (L.sc.eps / 4)) : WtNum p i T.PP := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hi := i.2
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have e1 := dat_p p i
  have e2 := dat_q p i
  have e3 := dat_rank p i
  have hD : dimFlag (dat p i) = T.Dp := (dim_eq p i).trans T.Dp_eq.symm
  have hlx : 2 ≤ Real.log L.sc.x := by
    have h1 : Real.log 8 ≤ Real.log L.sc.x := Real.log_le_log (by norm_num) hx8
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at h1
    have := Real.log_two_gt_d9
    push_cast at h1
    linarith
  have hL3 : 3 ≤ L.sc.L :=
    hy.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [L.sc.eps_pos]))
  have hwin := size_window D L hS hlx ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  have hP := forty_le_PP T
  have hPt := (parameterPrecision_le_length_and_rank D L P T (by linarith) (one_le_nWn D L P T)).2
  have hwid := mul_widths_le D L T.PP (by linarith) hS (by linarith) hy
  have hS0 := L.Sc_pos
  have hη0 := L.etaSz_pos
  have h40 : 40 * (L.Sc + L.etaSz) ≤ L.sc.w'' D.R.n := le_trans (mul_le_mul_of_nonneg_right hP (by linarith)) hwid
  have hrη : (D.R.r : ℝ) ≤ L.etaSz := by
    refine le_trans ?_ P.t_le_eta
    exact_mod_cast (by have := D.R.rank_add_five_le; omega : D.R.r ≤ D.R.t)
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have hlen : lenT p i T.PP ≤ T.TO := by
    unfold lenT; rw [hD]; exact Nat.ceil_le.2 (len_le D L P T)
  have hlen' : 4 * T.Dp + 4 ≤ lenT p i T.PP := by
    unfold lenT; rw [hD]; exact len_ge T
  obtain ⟨s1, s2, s3⟩ := spacing_ge T ((i : ℕ) + 1) _ hlen
  obtain ⟨q1, q2, q3⟩ := prod_bounds T _ hlen
  obtain ⟨g1, g2⟩ := gap_le D L P T (lenT p i T.PP) (Nat.cast_nonneg _) (by exact_mod_cast hlen)
  have hh : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη0.le (by exact_mod_cast (by omega : 1 ≤ D.R.m))
  have hstep : ∀ t a, a + 1 < D.R.r → ((lenT p i T.PP : ℝ) + T.Dp + 2) * (lenT p i T.PP + T.Dp + 2 + 2 * (D.R.r : ℝ)) + 1 ≤
      sgR D t a - sgR D t (a + 1) := fun t a ha =>
    sgR_step D L P t _ g1 g2
      (fun hm => le_trans g2 (minimalGap_le_first_lowerRowParameter D L P _ (Nat.le_add_left _ _) i.2 t (hwin t).1 hm)) a ha
  have hstep1 : ∀ t a, a + 1 < D.R.r → 1 ≤ sgR D t a - sgR D t (a + 1) := fun t a ha =>
    le_trans (le_add_of_nonneg_left (by positivity)) (hstep t a ha)
  have hent : ∀ t n, n < D.R.r → |entR D i t n| ≤ 3 * L.sc.b := by
    intro t n hn
    obtain ⟨w1, w2⟩ := hwin t
    by_cases h : n < D.R.k - 1
    · obtain ⟨a1, a2⟩ := entR_cloud L i t n h
      rw [abs_le]; constructor <;> linarith
    · have := entR_node L i t n (by omega) hn
      linarith
  have hanc : ∀ t, L.sc.w'' D.R.n - D.R.r ≤ entR D i t (D.R.k - 1 - 1) := fun t => by
    have := (entR_cloud L i t (D.R.k - 1 - 1) (by omega)).1
    linarith [(hwin t).1]
  have hc0 : (0 : ℝ) ≤ cZeroN D ((i : ℕ) + 1) := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ lenT p i T.PP := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ T.Dp := Nat.cast_nonneg _
  have eN : ((((dat p i).p + (dat p i).q : ℕ)) : ℝ) = D.R.r := by rw [e3]
  have eZ : ((((dat p i).p + (dat p i).q : ℕ)) : ℤ) = D.R.r := by rw [e3]
  refine ⟨⟨e1, e2, e3⟩, card_psi p, dim_eq p i, cols_eq p i, dom_wtA _, unit_eq p, ?_, ?_, ?_, ?_, fun him => ?_⟩
  · rw [ofRecord_logOm]; exact abs_logOm_le hS hL3
  · intro τ n
    obtain ⟨t, ht⟩ := exists_tau p τ
    rw [laOf_real p i τ t ht]
    have := hent t n (e3 ▸ n.2)
    have := abs_nonneg (entR D i t n)
    linarith
  · intro τ
    obtain ⟨t, ht⟩ := exists_tau p τ
    rw [anchor_real p i τ t ht]
    linarith [hanc t]
  · rw [hD]; exact ⟨q2, q3⟩
  rw [h0_eq p] at s1 s2 s3 q1 hh
  refine ⟨p.h0, L.Sc, L.etaSz, hS0.le, hη0.le, by linarith, by exact_mod_cast s3, by rw [hD]; exact_mod_cast q1, fun u1 => ?_⟩
  refine ⟨show 1 ≤ D.R.k - 1 by omega, show D.R.k - 1 < (dat p i).p by omega, show (dat p i).p < _ by omega,
    show _ - (dat p i).p < (dat p i).p by omega, Int.natCast_nonneg _, fun τ a ha => uWt_anchor _ _ _ _ τ a ha,
    show 4 * dimFlag (dat p i) + 4 ≤ lenT p i T.PP by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 4 * ((cZeroN D ((i : ℕ) + 1) : ℤ) + 2 * ((dat p i).p + (dat p i).q : ℕ) + lenT p i T.PP + dimFlag (dat p i) + 1) ≤ p.h0 ∧
      24 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) * lenT p i T.PP ≤ p.h0
    rw [hD, eZ]
    exact ⟨by exact_mod_cast s1, by exact_mod_cast s2⟩
  · intro τ a ha
    obtain ⟨t, ht⟩ := exists_tau p τ
    show |(uW p i τ a : ℝ) + (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)| ≤
      L.etaSz + L.Sc + ((dat p i).p + (dat p i).q : ℕ)
    rw [uW_real p i τ t ht, anchor_real p i τ t ht, sub_add_cancel, eN]
    have := entR_node L i t a ha (e3 ▸ a.2)
    linarith
  · intro τ a ha
    obtain ⟨t, ht⟩ := exists_tau p τ
    show 0 ≤ uW p i τ a ∧ (uW p i τ a : ℝ) ≤ L.Sc
    obtain ⟨a1, a2⟩ := entR_cloud_sub L i t (hstep1 t) a ha
    rw [← uW_real p i τ t ht] at a1 a2
    exact ⟨by exact_mod_cast a1, a2⟩
  · intro τ
    obtain ⟨t, ht⟩ := exists_tau p τ
    show 4 * ((L.etaSz + L.Sc + ((dat p i).p + (dat p i).q : ℕ)) + L.Sc + ((cZeroN D ((i : ℕ) + 1) : ℤ) : ℝ) +
      2 * ((dat p i).p + (dat p i).q : ℕ)) + 20 * ((dat p i).p + (dat p i).q : ℕ) * (lenT p i T.PP : ℝ) ≤
      (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)
    rw [anchor_real p i τ t ht, eN, Int.cast_natCast]
    have := hanc t
    have h5 : 0 ≤ (D.R.r : ℝ) * lenT p i T.PP := by positivity
    nlinarith
  · intro τ a b hab
    obtain ⟨t, ht⟩ := exists_tau p τ
    have hb := b.2
    have hd : ((uW p i τ a - uW p i τ b : ℤ) : ℝ) =
        sgR D t a - sgR D t (a + 1) - 1 + if (a : ℕ) + 1 = D.R.k + i then (D.R.r : ℝ) else 0 := by
      rw [Int.cast_sub, uW_real p i τ t ht, uW_real p i τ t ht, hab, ← entR_step]; ring
    have hge : sgR D t a - sgR D t (a + 1) - 1 ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by
      rw [hd]; split_ifs <;> linarith
    refine ⟨fun _ => ?_, fun ha => ?_, fun hp => ?_⟩
    · show ((lenT p i T.PP : ℤ) + dimFlag (dat p i) + 2) *
        ((lenT p i T.PP : ℤ) + dimFlag (dat p i) + 2 + 2 * ((dat p i).p + (dat p i).q : ℕ)) ≤ uW p i τ a - uW p i τ b + 2
      rw [hD, eZ]
      have := hstep t a (by omega)
      have h2 : ((lenT p i T.PP : ℝ) + T.Dp + 2) * (lenT p i T.PP + T.Dp + 2 + 2 * (D.R.r : ℝ)) ≤
        ((uW p i τ a - uW p i τ b : ℤ) : ℝ) + 2 := by linarith
      exact_mod_cast h2
    · show (p.h0 : ℤ) - 1 ≤ uW p i τ a - uW p i τ b
      have := sgR_step_low D L P t a ha (by omega)
      rw [h0_eq p] at this
      have h2 : (p.h0 : ℝ) - 1 ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by linarith
      exact_mod_cast h2
    · show (p.h0 : ℤ) ≤ uW p i τ a - uW p i τ b
      have hp' : (b : ℕ) = (dat p i).p := hp
      have := sgR_step_low D L P t a (by omega) (by omega)
      rw [h0_eq p] at this
      rw [if_pos (by omega)] at hd
      have c6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast six_le_r D.R
      have h2 : (p.h0 : ℝ) ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by linarith
      exact_mod_cast h2
  · intro τ a
    obtain ⟨t, ht⟩ := exists_tau p τ
    show |(uW p i τ a : ℝ)| + ((cZeroN D ((i : ℕ) + 1) : ℤ) : ℝ) + 4 * ((dat p i).p + (dat p i).q : ℕ) ≤ 2 * (4 * L.sc.b)
    rw [uW_real p i τ t ht, eN, Int.cast_natCast]
    have a1 := hent t a (e3 ▸ a.2)
    have a2 := hent t (D.R.k - 1 - 1) (by omega)
    have a3 := abs_sub (entR D i t a) (entR D i t (D.R.k - 1 - 1))
    obtain ⟨w1, w2⟩ := hwin t
    linarith

theorem wtN : WtN := by
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, le_rfl, max 8 ((3 : ℝ) ^ (4 / eps)), fun x hx hle ι p _ i => ?_⟩⟩⟩
  refine wtNum_at p i (Fm.params x hx ι) (Fm.parT x hx ι) (Fm.sizes x hx ι) ?_ ?_
  · rw [Fm.L_x x ι hx]; exact (le_max_left _ _).trans hle
  · rw [Fm.L_x x ι hx, Fm.L_eps x ι]
    have h3 : ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) = 3 := by
      rw [← Real.rpow_mul (by norm_num)]
      have : 4 / eps * (eps / 4) = 1 := by field_simp
      rw [this, Real.rpow_one]
    calc (3 : ℝ) = ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) := h3.symm
      _ ≤ x ^ (eps / 4) := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hle) (by positivity)

end GlobalTheory.CovTop.WtShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLatticeQuadraticSumGeDiagonalStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedLatticeQuadraticSum_ge_diagonal : ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∃ c : ℝ, 0 < c ∧ ∀ (X : Type) [AddCommGroup X] (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ y, 0 ≤ β y y) → ∀ y : Fin s → X, c * (∑ u, β (y u) (y u) : ℤ) ≤ (qW W β y : ℤ) := by
  first | exact @GlobalTheory.Poinc.QWDom.qW_ge | exact GlobalTheory.Poinc.QWDom.qW_ge | (intros; apply GlobalTheory.Poinc.QWDom.qW_ge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDegenerationTorsionClassicalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_degenerationTorsion_classical : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ k : ℕ, 0 < k → ∀ M Nn M' Nn' p p', d.Rep σ k M Nn p → d.Rep σ k M' Nn' p' → (N.wp p p' : ℂ) = Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (cv M ⬝ᵥ cv Nn' - cv Nn ⬝ᵥ cv M') / k) := by
  first | exact @GlobalTheory.MBLow.Cl.wp_classical | exact GlobalTheory.MBLow.Cl.wp_classical | (intros; apply GlobalTheory.MBLow.Cl.wp_classical <;> assumption)
end

