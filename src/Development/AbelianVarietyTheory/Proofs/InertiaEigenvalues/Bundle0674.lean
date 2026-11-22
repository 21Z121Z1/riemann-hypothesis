import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0479
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0657
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0068
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodMatrixAtLogZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0208
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntertwinerUnipotentInvariant
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0011
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0110
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SaturatedAinfLatticeFreeOverBreuilKisinStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.saturatedAinfLattice_free_over_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (T0 V V' : Matrix (Fin d) (Fin d) (WCb l)) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit T0 → (∀ i j, V i j ∈ bk.OE) → (∀ i j, V' i j ∈ bk.OE) → V * V' = 1 → Y1.map (inclW l) = inclW l τ ^ N • (T0 * V) → ∃ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Wm Wm' : Matrix (Fin d) (Fin d) (WCb l)), IsUnit (Y.map (inclW l)) ∧ (∀ i j, Wm i j ∈ bk.OE) ∧ (∀ i j, Wm' i j ∈ bk.OE) ∧ Wm * Wm' = 1 ∧ Y.map (inclW l) = inclW l τ ^ N • (T0 * Wm) ∧ ∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a) := by
  first | (exact @GlobalTheory.BKLim.SatLat.main) | (exact GlobalTheory.BKLim.SatLat.main) | (intros; apply GlobalTheory.BKLim.SatLat.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDieudonneModuleSpansTensorPeriodRing
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.Pst

theorem Dst_spans_tensor_Bst : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → ∀ v : V, ∃ (k : ℕ) (a : Fin k → Bst P) (x : Fin k → V ⊗[ℚ_[l]] Bst P), (∀ i, x i ∈ Dst P ρ) ∧ v ⊗ₜ[ℚ_[l]] (1 : Bst P) = ∑ i, onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] (a i)) (x i) := by
  intro l _ P AI T K V _ _ _ ρ hS v
  set b := Module.finBasis ℚ_[l] V with hb
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.exists_semistable_period_matrix_of_isSemistable l P AI T (Fin (finrank ℚ_[l] V)) K V b ρ hS
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.tensorProduct_basis_coordinates ℚ_[l] (Bst P) V (Fin (finrank ℚ_[l] V)) b

  have hst : ∀ g : ↥(GK K), (stRep P ρ g : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P) =
      TensorProduct.map (ρ g) (actSt P (g : GQ l)).toLinearMap := by
    intro g; apply TensorProduct.ext'; intro w c; rfl
  have hon : ∀ f : End ℚ_[l] (Bst P), (onB P ℚ_[l] V f : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P) =
      TensorProduct.map LinearMap.id f := by
    intro f; apply TensorProduct.ext'; intro w c; rfl
  set w : Fin (finrank ℚ_[l] V) → Bst P := fun i => algebraMap ℚ_[l] (Bst P) (b.repr v i) with hw
  let Qm : Matrix (Fin (finrank ℚ_[l] V)) (Fin (finrank ℚ_[l] V)) (Bst P) := Q.1
  let Qi : Matrix (Fin (finrank ℚ_[l] V)) (Fin (finrank ℚ_[l] V)) (Bst P) := (Q⁻¹).1
  refine ⟨finrank ℚ_[l] V, Matrix.mulVec Qi w, fun j => e.symm (fun i => Qm i j), ?_, ?_⟩
  · intro j
    rw [mem_Dst]
    intro g
    apply e.injective
    rw [hst g, he3, LinearEquiv.apply_symm_apply]
    have h : ∀ i, (((LinearMap.toMatrix b b) (ρ g)).map ⇑(algebraMap ℚ_[l] (Bst P)) * (Q.1).map ⇑((actSt P) ↑g)) i j = Qm i j :=
      fun i => congrFun (congrFun (hQ g) i) j
    funext i
    rw [← h i]
    rfl
  · apply e.injective
    rw [map_sum]
    funext i
    rw [he1, Finset.sum_apply]
    have key : ∀ j, e (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] ((Matrix.mulVec Qi w) j)) (e.symm (fun i => Qm i j))) i =
        (Matrix.mulVec Qi w) j * Qm i j := by
      intro j
      rw [hon, he3, LinearEquiv.apply_symm_apply, LinearMap.toMatrix_id, Matrix.map_one (algebraMap ℚ_[l] (Bst P)) (map_zero _) (map_one _), Matrix.one_mulVec]
      rfl
    simp_rw [key]
    have hQQ : Qm * Qi = 1 := by
      show (Q * Q⁻¹).1 = 1
      rw [mul_inv_cancel]; rfl
    have := congrFun (congrArg (fun M => Matrix.mulVec M w) hQQ) i
    simp only [Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at this
    rw [Algebra.smul_def, mul_one]
    refine this.symm.trans ?_
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.Pst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodMatrixAtLogZeroStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_periodMatrix_at_log_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) → IsSst P (qRep ρ) → ∃ (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)) (c₁ c₃ k : ℕ) (F F' Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)), U * U' = 1 ∧ F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧ (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) ∧ Mn ^ d = 0 ∧ ∀ g : ↥(GK K), (ρ g).val.map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i := by
  first | exact @GlobalTheory.StU.period_matrix_at_zero | exact GlobalTheory.StU.period_matrix_at_zero | (intros; apply GlobalTheory.StU.period_matrix_at_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodPowDvdByBasisAinfStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriod_pow_dvd_by_basis_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → (∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y ↔ ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∃ (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  first | exact @GlobalTheory.BKLim.WHeightSprime.main | exact GlobalTheory.BKLim.WHeightSprime.main | (intros; apply GlobalTheory.BKLim.WHeightSprime.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenAdmissibleRepresentationFiniteInertia
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem senFinite : SenFinite := GlobalTheory.PMon.Ram.senFinite_of_noTower GlobalTheory.PMon.Ram.noTower

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesEqOfOpposite
section
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

noncomputable section

namespace GlobalTheory.SerSys.Opp

open GlobalTheory.GLq.Opp

open MonoidAlgebra in

def reg {G H : Type} [Group G] [Group H] (i : G →* H) : Representation ℂ G (MonoidAlgebra ℂ H) where
  toFun x := LinearMap.mulLeft ℂ (single (i x) (1 : ℂ))
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp [← MonoidAlgebra.one_def]
  map_mul' x y := by
    refine LinearMap.ext fun v => ?_
    simp [← mul_assoc, single_mul_single]

open MonoidAlgebra in
theorem map_conj {G : Type} [Group G] (p : G) (a : MonoidAlgebra ℂ G) :
    mapDomainAlgHom ℂ ℂ (MulAut.conj p).toMonoidHom a = single p 1 * a * single p⁻¹ 1 := by
  induction a using MonoidAlgebra.induction_on with
  | of m => simp [single_mul_single]
  | add x y hx hy => simp only [map_add, hx, hy, add_mul, mul_add]
  | smul r x hx => simp only [map_smul, hx, smul_mul_assoc, mul_smul_comm]

variable {g : ℕ} [Fact g.Prime] {k l n : ℕ}

theorem blk_eq (x : Gn g k) (y : Gn g l) : blk k l (k + l) x y = par finSumFinEquiv x 0 y := by
  have h : (fun i j : Fin (k + l) => if (i : ℕ) < k ∧ (j : ℕ) < k then entN (x : Mt g k) i j
      else if k ≤ (i : ℕ) ∧ k ≤ (j : ℕ) then entN (y : Mt g l) (i - k) (j - k) else 0) =
      ((par finSumFinEquiv x 0 y : Gn g (k + l)) : Mt g (k + l)) := by
    funext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [par_apply]
    rcases i with i | i <;> rcases j with j | j
    · simp [entN]
    · have := i.2
      simp [entN]
    · have := j.2
      simp [entN]
    · simp [entN]
  unfold blk
  rw [h, toG, dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]

theorem eq_par (z : Gn g (k + l)) (h0 : InPar k (z : Mt g (k + l))) (h1 : tl k (z : Mt g (k + l)) = 1)
    (h2 : br k l (z : Mt g (k + l)) = 1) : ∃ B, z = par finSumFinEquiv 1 B 1 := by
  have e1 : ∀ (M : Mt g (k + l)) (i j : Fin k), tl k M i j = M (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j)) := by
    intro M i j
    have hi := i.2
    have hj := j.2
    rw [tl, entN, dif_pos ⟨by omega, by omega⟩]
    rfl
  have e2 : ∀ (M : Mt g (k + l)) (i j : Fin l), br k l M i j = M (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j)) := by
    intro M i j
    have hi := i.2
    have hj := j.2
    rw [br, entN, dif_pos ⟨by omega, by omega⟩]
    rfl
  refine ⟨Matrix.of fun i j => (z : Mt g (k + l)) (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j)), ?_⟩
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [par_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [← e1 (z : Mt g (k + l)) i j, h1]; simp
  · simp
  · rw [h0 _ _ (by simp) (by simp)]; simp
  · rw [← e2 (z : Mt g (k + l)) i j, h2]; simp

end GlobalTheory.SerSys.Opp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanPOfGiven
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lowTNZ_holds {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) :
    Formalism.IndefR.Eqv.KerDiag.LowTNZ R := by
  intro i τ
  obtain ⟨w, hw, h0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.LowTypeRestriction.lowT_ne_bot (R.MW i (sg0 D A)) τ)
  exact ⟨⟨w, hw⟩, fun h => h0 (Subtype.ext h)⟩

theorem spanP_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.LiftRows.Given R F → Formalism.IndefR.Eqv.Act.SpanP R :=
  fun R _ _ => Formalism.IndefR.Eqv.KerDiag.spanP_of_lowTNZ R (lowTNZ_holds R)

end GlobalTheory.LiftRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehLanglandsQuotientStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.speh_langlands_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ (δ δ' : IrrGL k) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ (δ x : IrrGL k) (Δ : Segment k) (m : ℕ), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsSpeh δ m x.rep →
      ∀ s : ℝ, IsL ↑(List.ofFn fun i : Fin m => Δ.nu ((s + ((m : ℝ) - 1) / 2 - (i : ℕ) : ℝ) : ℂ)) (x.nu (s : ℂ)).rep := by
  first | exact @GlobalTheory.LocGL.isL_speh_nu | exact GlobalTheory.LocGL.isL_speh_nu | (intros; apply GlobalTheory.LocGL.isL_speh_nu <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedCrystalValueMapCommFrobeniusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stratifiedCrystalValueMap_comm_frobenius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (M' : FCrys l ↥(OL K)) (e' : Module.Basis (Fin d') bk.prism.A (M'.M bk.prism)), Framed S M e → Framed S' M' e' → ∀ Y : Matrix (Fin d') (Fin d) bk.S, IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)) (V' : Eval S' B (M'.M B)), IsCoord e V → IsCoord e' V' → ∀ w : M.M B →ₗ[B.A] M'.M B, (∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : M.M B), V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x)) → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → IsFrac (t : B.A) (M'.Φ B t (w x)) (w m) k := by
  first | exact @GlobalTheory.BSP.eval_map_Φ | exact GlobalTheory.BSP.eval_map_Φ | (intros; apply GlobalTheory.BSP.eval_map_Φ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedHomComparisonCompatibleEnvelopeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stratifiedHom_comparison_compatible_envelope : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (Y : Matrix (Fin d') (Fin d) bk.S), bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A) → (∀ g : ↥(GK K), S'.ε bk.ι ((ainfHom K g).comp bk.ι) * Y.map (BK.hf ((ainfHom K g).comp bk.ι)) = Y.map (BK.hf bk.ι) * S.ε bk.ι ((ainfHom K g).comp bk.ι)) → S'.ε En.inl En.inr * Y.map (BK.hf En.inr) = Y.map (BK.hf En.inl) * S.ε En.inl En.inr := by
  first | exact @GlobalTheory.BSP.strat_eps_compat_env | exact GlobalTheory.BSP.strat_eps_compat_env | (intros; apply GlobalTheory.BSP.strat_eps_compat_env <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedValueFrobeniusCommTransitionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stratifiedValue_frobenius_comm_transition : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B B' : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (N' : Type) [AddCommGroup N'] [Module B'.A N'] (V : Eval S B N) (V' : Eval S B' N') (k : Hom B B') (τ : N →ₛₗ[k.f] N'), (∀ (Q : Obj l ↥(OL K)) (a : Hom B' Q) (g : Hom bk.prism Q) (x : N), V'.v a g (τ x) = V.v (a.comp k) g x) → ∀ (t : B.A) (t' : B'.A) (Ψ : N →ₛₗ[B.D.φ] N) (Ψ' : N' →ₛₗ[B'.D.φ] N'), IsPsi V t Ψ → IsPsi V' t' Ψ' → ∀ x, t' ^ S.a • τ (Ψ x) = k.f t ^ S.a • Ψ' (τ x) := by
  first | exact @GlobalTheory.BSP.psi_nat | exact GlobalTheory.BSP.psi_nat | (intros; apply GlobalTheory.BSP.psi_nat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumHeckeIndicatorIntegralEqPrimitive
section
noncomputable section

open Matrix GlobalTheory.SplitHecke GlobalTheory.ExportSeries

namespace GlobalTheory.HeckeMobius

section Pure

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K]

theorem reps_mul_central {n : ℕ} {ι : Type} {x c : GL (Fin n) K} {R : Finset ι} {ρ : ι → GL (Fin n) K}
    (hc : ∀ g : GL (Fin n) K, c * g = g * c) (h : Reps O x R ρ) :
    Reps O (x * c) R fun γ => ρ γ * c := by
  have hc' : ∀ g : GL (Fin n) K, c⁻¹ * g = g * c⁻¹ := fun g => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc g, mul_inv_cancel_right]
  refine ⟨fun γ hγ => ?_, fun k₁ k₂ h₁ h₂ => ?_⟩
  · obtain ⟨k₁, k₂, h₁, h₂, e⟩ := h.1 γ hγ
    exact ⟨k₁, k₂, h₁, h₂, by show ρ γ * c = _; rw [e]; simp only [mul_assoc, hc k₂]⟩
  · have e : ∀ γ, (ρ γ * c)⁻¹ * (k₁ * (x * c) * k₂) = (ρ γ)⁻¹ * (k₁ * x * k₂) := fun γ => by
      calc (ρ γ * c)⁻¹ * (k₁ * (x * c) * k₂) = c⁻¹ * ((ρ γ)⁻¹ * (k₁ * x * k₂)) * c := by
            rw [_root_.mul_inv_rev]; simp only [mul_assoc, hc k₂]
        _ = (ρ γ)⁻¹ * (k₁ * x * k₂) := by rw [hc', inv_mul_cancel_right]
    exact (existsUnique_congr fun γ => and_congr_right fun _ => by rw [e γ]).2 (h.2 k₁ k₂ h₁ h₂)

def scal {n : ℕ} (a : K) (ha : a ≠ 0) : GL (Fin n) K :=
  Units.map (Matrix.scalar (Fin n) : K →+* Matrix (Fin n) (Fin n) K).toMonoidHom (Units.mk0 a ha)

theorem scal_val {n : ℕ} (a : K) (ha : a ≠ 0) :
    ((scal a ha : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) a := rfl

theorem scal_comm {n : ℕ} (a : K) (ha : a ≠ 0) (g : GL (Fin n) K) : scal a ha * g = g * scal a ha :=
  Units.ext (by
    rw [Units.val_mul, Units.val_mul, scal_val]
    exact (Matrix.scalar_commute a (fun _ => Commute.all _ _) _).eq)

theorem scal_inv_comm {n : ℕ} (a : K) (ha : a ≠ 0) (g : GL (Fin n) K) : (scal a ha)⁻¹ * g = g * (scal a ha)⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, scal_comm, mul_inv_cancel_right]

theorem scal_mul_val {n : ℕ} (a : K) (ha : a ≠ 0) (g : GL (Fin n) K) : (scal a ha * g).1 = a • g.1 := by
  rw [Units.val_mul, scal_val, Matrix.scalar_apply, smul_eq_diagonal_mul]

theorem hk_compl {p : O} (hp : algebraMap O K p ≠ 0) {n j : ℕ} (hj : j ≤ n) {α : GL (Fin n) K} (h : Hk O p j α) :
    Hk O p (n - j) (scal (algebraMap O K p) hp * α⁻¹) := by
  refine ⟨by rw [scal_mul_val]; exact h.2.1, ?_, ?_⟩
  · have : algebraMap O K p • ((scal (algebraMap O K p) hp * α⁻¹)⁻¹ : GL (Fin n) K).1 = α.1 := by
      rw [← scal_mul_val _ hp, _root_.mul_inv_rev, inv_inv, ← mul_assoc, scal_comm, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact h.1
  · obtain ⟨u, hu⟩ := h.2.2
    refine ⟨u⁻¹, ?_⟩
    have h1 : (α⁻¹).1.det * α.1.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have h2 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [scal_mul_val, Matrix.det_smul, Fintype.card_fin, map_mul, map_pow]
    rw [hu, map_mul, map_pow] at h1
    have hn : algebraMap O K p ^ n = algebraMap O K p ^ (n - j) * algebraMap O K p ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    rw [hn]
    linear_combination (-(algebraMap O K p ^ (n - j) * algebraMap O K p ^ j * (α⁻¹).1.det)) * h2 +
      (algebraMap O K p ^ (n - j) * algebraMap O K ((u⁻¹ : Oˣ) : O)) * h1

theorem cond_eq {p : O} (hp : algebraMap O K p ≠ 0) {r n : ℕ} (g : GL (Fin r) K) (z : Matrix (Fin r) (Fin n) O) :
    ((algebraMap O K p)⁻¹ • zᵀ.map (algebraMap O K)) * (tr ((g * (scal (algebraMap O K p) hp)⁻¹)⁻¹)).1 =
      ((g⁻¹).1 * z.map (algebraMap O K))ᵀ := by
  have : (tr ((g * (scal (algebraMap O K p) hp)⁻¹)⁻¹)).1 = (algebraMap O K p • (g⁻¹).1)ᵀ := by
    rw [_root_.mul_inv_rev, inv_inv, ← scal_mul_val _ hp]; rfl
  rw [this, Matrix.transpose_mul, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ hp, one_smul]
  rfl

open IsLocalRing in

theorem count_eq [Finite (ResidueField O)] {p : O} (hp : Irreducible p) {r n k : ℕ} (hk : k ≤ r) {ι : Type}
    {α : GL (Fin r) K} {R : Finset ι} {ρ : ι → GL (Fin r) K} (hα : Hk O p k α) (hR : Reps O α R ρ)
    (z : Matrix (Fin r) (Fin n) O) :
    Nat.card {γ : ι // γ ∈ R ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))} =
      Nat.card {W : Submodule (ResidueField O)
        (Fin (Module.finrank (ResidueField O) (LinearMap.ker (z.map (residue O))ᵀ.mulVecLin)) → ResidueField O) //
          Module.finrank (ResidueField O) W = k} := by
  have h0 : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hp.ne_zero
  have hR' : Reps O (tr (scal (algebraMap O K p) h0 * α⁻¹)) R
      fun γ => tr ((ρ γ * (scal (algebraMap O K p) h0)⁻¹)⁻¹) := by
    apply Reps.tr
    rw [_root_.mul_inv_rev, inv_inv]
    exact reps_mul_central (scal_inv_comm _ h0) hR
  have hc := Cosets.card_cosets O K p hp n r (r - k) ι _ R _ zᵀ (Nat.sub_le r k) (hk_compl h0 hk hα).tr hR'
  calc Nat.card {γ : ι // γ ∈ R ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))}
      = Nat.card {γ : ι // γ ∈ R ∧ IntM O (((algebraMap O K p)⁻¹ • zᵀ.map (algebraMap O K)) *
          (tr ((ρ γ * (scal (algebraMap O K p) h0)⁻¹)⁻¹)).1)} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun γ => and_congr_right fun _ => by
          rw [cond_eq h0]; exact ⟨fun h => h.transpose, fun h => h.transpose⟩)
    _ = _ := hc
    _ = Nat.card {W : Submodule (ResidueField O) (Fin r → ResidueField O) //
          W ≤ LinearMap.ker (z.map (residue O))ᵀ.mulVecLin ∧ Module.finrank (ResidueField O) W = k} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun W => by
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
          · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩)
    _ = _ := GlobalTheory.card_subspaces_le_eq _ _
    _ = _ := GlobalTheory.card_subspaces_finrank_congr (LinearEquiv.ofFinrankEq _ _ (Module.finrank_fin_fun _).symm) k

theorem sum_smul_row {F : Type} [Field F] {r n : ℕ} (y : Matrix (Fin r) (Fin n) F) (g : Fin r → F) :
    yᵀ *ᵥ g = ∑ i, g i • y.row i := by
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.row, mul_comm]

end Pure

open IsLocalRing in

theorem sum_hecke_indicator_eq_prim : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Finite (IsLocalRing.ResidueField O)] (p : O), Irreducible p → ∀ (r n : ℕ) (ι : Type) (α : ℕ → GL (Fin r) K) (R : ℕ → Finset ι) (ρ : ι → GL (Fin r) K), (∀ k ∈ Finset.Icc 1 r, Hk O p k (α k) ∧ Reps O (α k) (R k) ρ) → ∀ z : Matrix (Fin r) (Fin n) O, (1 : ℂ) + ∑ k ∈ Finset.Icc 1 r, (-1 : ℂ) ^ k * (Nat.card (IsLocalRing.ResidueField O) : ℂ) ^ (k * (k - 1) / 2) * (Nat.card {γ : ι // γ ∈ R k ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))} : ℂ) = ((prim (z.map (IsLocalRing.residue O)) : ℚ) : ℂ) := by
  intro O K _ _ _ _ _ _ _ p hp r n ι α R ρ h z
  set A := (z.map (residue O))ᵀ with hA
  set c := Module.finrank (ResidueField O) (LinearMap.ker A.mulVecLin) with hc
  have hcr : c ≤ r := by
    have := Submodule.finrank_le (LinearMap.ker A.mulVecLin)
    rwa [Module.finrank_fin_fun] at this
  let N : ℕ → ℂ := fun k => (Nat.card {W : Submodule (ResidueField O) (Fin c → ResidueField O) //
    Module.finrank (ResidueField O) W = k} : ℂ)
  have hN0 : N 0 = 1 := by
    simp only [N, Submodule.finrank_eq_zero]
    rw [Nat.card_unique, Nat.cast_one]
  have hNc : ∀ k, c < k → N k = 0 := fun k hk => by
    simp only [N, Nat.cast_eq_zero]
    haveI : IsEmpty {W : Submodule (ResidueField O) (Fin c → ResidueField O) //
        Module.finrank (ResidueField O) W = k} := ⟨fun W => by
      have := Submodule.finrank_le W.1
      rw [Module.finrank_fin_fun, W.2] at this
      omega⟩
    exact Nat.card_of_isEmpty
  have e1 : (1 : ℂ) + ∑ k ∈ Finset.Icc 1 r, (-1 : ℂ) ^ k * (Nat.card (ResidueField O) : ℂ) ^ (k * (k - 1) / 2) *
      (Nat.card {γ : ι // γ ∈ R k ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))} : ℂ) =
      ∑ k ∈ Finset.range (r + 1), (-1 : ℂ) ^ k * (Nat.card (ResidueField O) : ℂ) ^ (k * (k - 1) / 2) * N k * 1 ^ k := by
    rw [Finset.sum_range_succ', pow_zero, pow_zero, one_mul, hN0, mul_one, one_mul, add_comm]
    congr 1
    have hI : Finset.Icc 1 r = Finset.Ico 1 (r + 1) := by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hI, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : 1 + k ≤ r := by rw [Finset.mem_range] at hk; omega
    have hm : 1 + k ∈ Finset.Icc 1 r := Finset.mem_Icc.2 ⟨by omega, hk'⟩
    rw [count_eq hp hk' (h _ hm).1 (h _ hm).2 z, one_pow, mul_one, add_comm 1 k]
  have hli : LinearIndependent (ResidueField O) (z.map (residue O)).row ↔ c = 0 := by
    rw [hc, Submodule.finrank_eq_zero, LinearMap.ker_eq_bot', Fintype.linearIndependent_iff]
    refine forall_congr' fun g => ?_
    rw [Matrix.mulVecLin_apply, hA, sum_smul_row]
    constructor
    · intro H h0; funext i; exact H h0 i
    · intro H h0 i; rw [H h0]; rfl
  rw [e1, ← Finset.sum_subset (Finset.range_subset_range.2 (show c + 1 ≤ r + 1 by omega)) (fun k hk hk' => ?_)]
  · refine Eq.trans (GlobalTheory.GaussSubspace.sum_card_subspaces (ResidueField O) c ℂ 1) ?_
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [prim, if_pos (hli.2 h0), h0, Finset.prod_range_zero]
      simp
    · rw [prim, if_neg (fun H => by have := hli.1 H; omega)]
      obtain ⟨m, hm⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
      rw [hm, Finset.prod_range_succ', pow_zero, one_mul, sub_self, mul_zero]
      simp
  · rw [Finset.mem_range, not_lt] at hk'
    rw [hNc k (by omega)]
    ring

end GlobalTheory.HeckeMobius
end
end

