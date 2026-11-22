import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0550
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0010
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityPersistsRowColumnChanges
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityTransportLocalFieldIso

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacRowScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.LastRowVac

open GlobalTheory.LastVertexMove GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem eq_smul_vac (S : GridChoice W U) {p : Pair T} (hp : DefPair D.R.m p) (f : WO (G.pS p) (G.pT p) → ℂ)
    (hf : IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (S.N.latS p : Set _) (S.N.latT p : Set _) f) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ f = c • S.Z.vac p := by
  have hv := S.Z.vac_is p hp
  obtain ⟨h1, h2⟩ := hp.nodes
  rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩
  · exact GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _
      (GlobalTheory.ChiGrid.WeilOver.sigOK_negSp (h2.sigOK G)) (h1.sigOK G)
      (fun τ => isCartanInv_neg (W.cart_is _ h2.inRange τ)) (fun τ => W.cart_is _ h1.inRange τ) _ _
      (isSelfDualC_neg (S.N.selfDual h2)) (S.N.selfDual h1) _ _ hv hf
  · exact hp.elim
  · exact hp.elim
  · exact GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ (h1.sigOK G) (h2.sigOK G)
      (fun τ => W.cart_is _ h1.inRange τ) (fun τ => W.cart_is _ h2.inRange τ) _ _ (S.N.selfDual h1) (S.N.selfDual h2)
      _ _ hv hf

theorem negGA_mem (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem rowPt_mem (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)) :
    (rowPt S k).1 ∈ GfC _ ∧ (rowPt S k).2 ∈ GfC _ :=
  ⟨negGA_mem _ (gridLast ((S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m))).2, one_mem _⟩

theorem vac_row_scalar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)),
    (∀ x, actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ x ∈ stdLat S (.chi (lastIx D) D.R.m) ↔
      x ∈ stdLat S (.chi (lastIx D) D.R.m)) →
    ∃ c : ℂ, rowShift S k (S.Z.vac (.chi (lastIx D) D.R.m)) = c • S.Z.vac (.chi (lastIx D) D.R.m) := by
  intro D T L sc G W U S k hlat
  have hp : DefPair D.R.m (Pair.chi ((lastIx D : ℕ)) D.R.m : Pair T) := defPair_chi (lastIx D)
  have hom := W.om_is _ (inRange_chi (T := T) (lastIx D))
  obtain ⟨m1, m2⟩ := rowPt_mem S k
  have hΛ : ∀ u, u ∈ stdLat S (.chi (lastIx D) D.R.m) ↔
      ∃ u₀ ∈ stdLat S (.chi (lastIx D) D.R.m), u = actO _ _ (rowPt S k).1 (rowPt S k).2 u₀ := by
    intro u
    constructor
    · intro hu
      refine ⟨actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ u, (hlat u).2 hu, ?_⟩
      have e := GlobalTheory.WeilVacMove.actO_inv_actO (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ u
      rw [inv_inv, inv_inv] at e
      exact e.symm
    · rintro ⟨u₀, hu₀, rfl⟩
      refine (hlat _).1 ?_
      rw [GlobalTheory.WeilVacMove.actO_inv_actO]
      exact hu₀
  have hv' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ (W.om _) hom W.θ_is _ _ _ _ _ _ _ _ (rowPt S k).1 (rowPt S k).2
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ m1, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ m2, Matrix.mul_one, Matrix.one_mul])
    hΛ _ (S.Z.vac_is _ hp)
  obtain ⟨c, -, hc⟩ := eq_smul_vac S hp _ hv'
  exact ⟨c, by rw [rowShift_eq]; exact hc⟩

end GlobalTheory.LastRowVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionNegPairPureTensorFockStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_negPair_pureTensor_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D (GlobalTheory.ChiGrid.negSp S) × GA D T →* Module.End ℂ (WO (GlobalTheory.ChiGrid.negSp S) T → ℂ)), IsWeilDatumO ψ (GlobalTheory.ChiGrid.negSp S) T χS χT om → IsInfFam θ → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → (∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = 1) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (e₂ τ : ℚ) = -(b τ - (T.rank : ℚ) / 2)) → ∀ f, IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f → (∀ τ, IsFockVacAt (heisO ψ (GlobalTheory.ChiGrid.negSp S) T) θ τ (cplxO (-1) 1) f) → ∀ g ∈ GinfC (GlobalTheory.ChiGrid.negSp S), ∀ h ∈ GinfC T, ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, om (g, h) (pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f P) = (∏ τ, (compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g)).det ^ e₂ τ * (compAt θ τ (Formalism.L2.Theta.mt T h)).det ^ e₁ τ) • pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => ((BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ).map (starRingEnd ℂ)) (fun τ => ((((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) * BS τ)⁻¹)ᵀ).map (starRingEnd ℂ)) P) := by
  first | exact @GlobalTheory.FockRealNeg.om_pureTensorO_neg | exact GlobalTheory.FockRealNeg.om_pureTensorO_neg | (intros; apply GlobalTheory.FockRealNeg.om_pureTensorO_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionOMemLatticeOOfIntegralCombinations
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

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.LatMoveGen

variable {D : D7}

theorem gram_mul_inv (V : HSp D) (g : Formalism.L2.Theta.GA D V) :
    V.gram.map (incA D) * Formalism.L2.Theta.mt V g⁻¹ =
      ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) := by
  have h : ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D) :=
    (g : HR (AF D.host.F) D.sp.cm.sig V.gram).2
  have h2 : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    rw [← GlobalTheory.LatMoveStd.mt_mul'', mul_inv_cancel, GlobalTheory.LatMoveStd.mt_one'']
  calc V.gram.map (incA D) * Formalism.L2.Theta.mt V g⁻¹
      = (((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g) * Formalism.L2.Theta.mt V g⁻¹ := by rw [h]
    _ = _ := by rw [Matrix.mul_assoc _ (Formalism.L2.Theta.mt V g), h2, Matrix.mul_one]

theorem row_move (V : HSp D) (g : Formalism.L2.Theta.GA D V) (s : Fin V.rank → D.host.E) (j : Fin V.rank) :
    ∑ m, incA D (∑ k, star (s k) * V.gram k m) * Formalism.L2.Theta.mt V g⁻¹ m j =
      ∑ m, cA D ((Formalism.L2.Theta.mt V g *ᵥ fun k => incA D (s k)) m) * incA D (V.gram m j) := by
  have e1 : (fun m => incA D (∑ k, star (s k) * V.gram k m)) =
      (fun k => cA D (incA D (s k))) ᵥ* V.gram.map (incA D) := by
    funext m
    simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, Matrix.map_apply, GlobalTheory.FinPl.FrameLat.cA_incA]
  have e2 : (fun m => cA D ((Formalism.L2.Theta.mt V g *ᵥ fun k => incA D (s k)) m)) =
      (Formalism.L2.Theta.mt V g).map (cA D) *ᵥ fun k => cA D (incA D (s k)) := by
    funext m
    exact RingHom.map_mulVec (cA D) _ _ m
  have lhs : ∑ m, incA D (∑ k, star (s k) * V.gram k m) * Formalism.L2.Theta.mt V g⁻¹ m j =
      ((fun m => incA D (∑ k, star (s k) * V.gram k m)) ᵥ* Formalism.L2.Theta.mt V g⁻¹) j := rfl
  have rhs : ∑ m, cA D ((Formalism.L2.Theta.mt V g *ᵥ fun k => incA D (s k)) m) * incA D (V.gram m j) =
      ((fun m => cA D ((Formalism.L2.Theta.mt V g *ᵥ fun k => incA D (s k)) m)) ᵥ* V.gram.map (incA D)) j := rfl
  rw [lhs, rhs, e1, e2, Matrix.vecMul_vecMul, gram_mul_inv, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]

end GlobalTheory.LatMoveGen

namespace GlobalTheory.LatMoveGen

variable {D : D7}

theorem act_gen_apply (S T : HSp D) (g : Formalism.L2.Theta.GA D S) (h : Formalism.L2.Theta.GA D T) (α : Af D.host.F) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    actO S T g h (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) i j =
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] a) * ((Formalism.L2.Theta.mt T h *ᵥ fun k => incA D (t k)) i *
        ∑ m, cA D ((Formalism.L2.Theta.mt S g *ᵥ fun k => incA D (s k)) m) * incA D (S.gram m j)) := by
  rw [← row_move]
  simp only [actO, Matrix.mul_apply, Matrix.of_apply, GlobalTheory.LatMoveStd.gen_eq]
  simp only [ Matrix.mul_apply, Matrix.of_apply, GlobalTheory.LatMoveStd.gen_eq, Matrix.mulVec, dotProduct,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem comb_apply (S T : HSp D) (α : Af D.host.F) (a : D.host.E) {m m' : ℕ} (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin T.rank → D.host.E)
    (β' : Fin m' → Formalism.L2.Theta.AE D) (b' : Fin m' → Fin S.rank → D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    (∑ p, ∑ q, (β p * cA D (β' q)) • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
        (a * b p i * ∑ k, star (b' q k) * S.gram k j)) : WO S T) i j =
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] a) * ((∑ p, β p * incA D (b p i)) *
        ∑ k, cA D (∑ q, β' q * incA D (b' q k)) * incA D (S.gram k j)) := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, GlobalTheory.LatMoveStd.gen_eq]
  simp only [map_sum, map_mul,
    GlobalTheory.FinPl.FrameLat.cA_incA, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_)
  ring

end GlobalTheory.LatMoveGen

namespace GlobalTheory.LatMoveGen

set_option synthInstance.maxHeartbeats 400000 in

theorem actO_mem_latO : ∀ {D : D7} (S T : HSp D) (g : Formalism.L2.Theta.GA D S) (h : Formalism.L2.Theta.GA D T)
    (AS BS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (AT BT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    (∀ s ∈ AS, ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin S.rank → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ BS) ∧
      ∀ i, finPart D ((mt S g *ᵥ fun k => incA D (s k)) i) =
        finPart D (∑ p, β p * incA D (b p i))) →
    (∀ t ∈ AT, ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin T.rank → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ BT) ∧
      ∀ i, finPart D ((mt T h *ᵥ fun k => incA D (t k)) i) =
        finPart D (∑ p, β p * incA D (b p i))) →
    ∀ w ∈ latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      actO S T g h w ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  intro D S T g h AS BS AT BT hS hT w hw
  let Ψ : WO S T →+ WO S T :=
    { toFun := actO S T g h
      map_zero' := by simp only [actO, Matrix.mul_zero, Matrix.zero_mul]
      map_add' := fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul] }
  have key : latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True) ≤
      (latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True)).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    obtain ⟨m', β', b', hβ', hb', hu⟩ := hS s hs
    obtain ⟨m, β, b, hβ, hb, hv⟩ := hT t ht
    have e : actO S T g h (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
        ∑ p, ∑ q, (β p * cA D (β' q)) • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
          (a * b p i * ∑ k, star (b' q k) * S.gram k j) : WO S T) := by
      ext i j
      rw [act_gen_apply, comb_apply, mul_comm, mul_comm (pairA D.host.F 0 α ⊗ₜ[D.host.F] a),
        GlobalTheory.LatticeStable.mul_pair_tmul, GlobalTheory.LatticeStable.mul_pair_tmul]
      congr 2
      simp only [map_mul, map_sum, GlobalTheory.FinPl.FrameLat.finPart_cA, hv, hu]
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show actO S T g h _ ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True)
    rw [e]
    refine sum_mem fun p _ => sum_mem fun q _ => ?_
    refine GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ?_ _ (AddSubgroup.subset_closure
      ⟨α, hα, fun _ h => absurd trivial h, a, ha, b' q, hb' q, b p, hb p, rfl⟩)
    rw [map_mul]
    exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE (hβ p) ((GlobalTheory.FinPl.FrameLat.cA_int_iff _).2 (hβ' q))
  exact key hw

end GlobalTheory.LatMoveGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityPersistsRowColumnChangesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIdentity_persists_row_column_changes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a a₁ : ℕ) (ha : a = a₁) (A' : Type) [Fintype A'] [DecidableEq A'] (A₁ : Type) [Fintype A₁] [DecidableEq A₁] (C : Type) [Fintype C] [DecidableEq C] (C₁ : Type) [Fintype C₁] [DecidableEq C₁] (eB : A' ≃ A₁) (eC : C ≃ C₁)
    (σ : Fin a ⊕ A' ≃ C) (σ₁ : Fin a₁ ⊕ A₁ ≃ C₁) (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (μ₁ : Measure (GL A₁ k)) [μ₁.IsHaarMeasure]
    (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (gA : GL (Fin a) k) (gB : GL A' k) (c : GL C k), gA ∈ KO k (Fin a) →
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (Ξ : Matrix (Fin a₁) C₁ k → ℂ) (Ψ : Matrix A₁ C₁ k → ℂ),
      bigP (haarVol (KO k (Fin a₁))) ϖ σ₁ ν β Ξ = smallP μ₁ σ₁ ν (ν * β) Ψ →
      bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun X => Ξ (reindex (finCongr ha) eC (gA.val * X * (invT c).val))) =
        smallP μ σ ν (ν * β) fun Y => lam * Ψ (reindex eB eC (gB.val * Y * c.val)) := by
  first | exact @GlobalTheory.FlipMatch.ZMat.bigZeta_eq_smallZeta_change | exact GlobalTheory.FlipMatch.ZMat.bigZeta_eq_smallZeta_change | (intros; apply GlobalTheory.FlipMatch.ZMat.bigZeta_eq_smallZeta_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityTransportLocalFieldIsoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIdentity_transport_localFieldIso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (k' : Type) [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [MeasurableSpace k'] [BorelSpace k'] (j : k ≃+* k'), IsLocIso j → ∀ (a : ℕ) (A' : Type) [Fintype A'] [DecidableEq A'] (C : Type) [Fintype C] [DecidableEq C] (σ : Fin a ⊕ A' ≃ C)
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (μ' : Measure (GL A' k')) [μ'.IsHaarMeasure] (ϖ : kˣ) (ϖ' : k'ˣ), IsUnif ϖ → IsUnif ϖ' →
    ∀ (ν β : kˣ →* ℂˣ) (ν' β' : k'ˣ →* ℂˣ), (∀ x, ν x = ν' (Units.map (j : k →* k') x)) →
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (Ξ : Matrix (Fin a) C k' → ℂ) (Ψ : Matrix A' C k' → ℂ),
      bigP (haarVol (KO k' (Fin a))) ϖ' σ ν' β' Ξ = smallP μ' σ ν' (ν' * β') Ψ →
      bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun X => Ξ (X.map j)) = smallP μ σ ν (ν * β) fun Y => lam * Ψ (Y.map j) := by
  first | exact @GlobalTheory.FlipMatch.FieldTransport.zeta_identity_transport | exact GlobalTheory.FlipMatch.FieldTransport.zeta_identity_transport | (intros; apply GlobalTheory.FlipMatch.FieldTransport.zeta_identity_transport <;> assumption)
end

