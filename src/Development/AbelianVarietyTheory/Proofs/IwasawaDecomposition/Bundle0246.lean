import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0057
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0050
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0144
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0237
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoeffExtRationalFormsValuesField
section
noncomputable section

namespace GlobalTheory.Mem.PlaceVal

section General

open Formalism.L2.DIV Formalism.BasicNotions Formalism.BasicNotions.TH

theorem exists_ext_pol {K K' I W : Type} [Field K] [Field K'] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ} (ι : K →+* K')
    (σ' : K' →+* ℂ) (hσ : σ'.comp ι = σ) (U : Submodule K (MvPolynomial I K)) (c : U →ₛₗ[σ] W) :
    ∃ c' : MvPolynomial I K' →ₛₗ[σ'] W, ∀ v : U, c' (MvPolynomial.map ι (v : MvPolynomial I K)) = c v := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective U.subtype U.ker_subtype
  let _ : Module K' W := Module.compHom W σ'
  let f : MvPolynomial I K' →ₗ[K'] W :=
    (MvPolynomial.basisMonomials I K').constr K' fun m => c (π (MvPolynomial.monomial m 1))
  have hf : ∀ m, f (MvPolynomial.monomial m 1) = c (π (MvPolynomial.monomial m 1)) := fun m => by
    have := (MvPolynomial.basisMonomials I K').constr_basis K' (fun m => c (π (MvPolynomial.monomial m 1))) m
    rwa [MvPolynomial.coe_basisMonomials] at this
  have key : ∀ p : MvPolynomial I K, f (MvPolynomial.map ι p) = c (π p) := fun p => by
    induction p using MvPolynomial.induction_on' with
    | monomial m a =>
      have e1 : MvPolynomial.map ι (MvPolynomial.monomial m a) = ι a • MvPolynomial.monomial m (1 : K') := by
        rw [MvPolynomial.map_monomial, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      have e2 : MvPolynomial.monomial m a = a • MvPolynomial.monomial m (1 : K) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [e1, f.map_smul, hf, e2, π.map_smul, map_smulₛₗ, ← RingHom.congr_fun hσ a]
      rfl
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  refine ⟨{ toFun := f, map_add' := f.map_add, map_smul' := fun a p => f.map_smul a p }, fun v => (key v).trans ?_⟩
  exact congrArg c (LinearMap.congr_fun hπ v)

theorem exists_ext_VV {K K' I W : Type} [Field K] [Field K'] [Fintype I] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ}
    (ι : K →+* K') (σ' : K' →+* ℂ) (hσ : σ'.comp ι = σ) {n : ℕ} (lam : I → DomWeight n) (c : VV K lam →ₛₗ[σ] W) :
    ∃ c' : VV K' lam →ₛₗ[σ'] W, ∀ v : VV K lam, ∃ v' : VV K' lam,
      (v' : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) ∧ c' v' = c v := by
  obtain ⟨c', hc⟩ := exists_ext_pol ι σ' hσ (VV K lam) c
  exact ⟨c'.comp (VV K' lam).subtype, fun v => ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV ι lam _ v.2⟩, rfl, hc v⟩⟩

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000 in

theorem exists_coef_placeEx : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp jL = D.what₂.embLL → ∃ c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, (∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧ CoefficientBaseChange R i jL σ' (c0L i) c0') ∧ ∀ t (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)), PlaceEx R i t h c0' := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR _ _ i K' _ jL σ' hσ
  obtain ⟨gramR, c0R, c0L, hT⟩ := hR.fam.tie
  obtain ⟨c0', hc⟩ := exists_ext_VV (W := (R.cV i).W) jL σ' hσ (lamV D i) (c0L i)
  exact ⟨c0', ⟨gramR, c0R, c0L, hT, hc⟩, fun t Cl _ h =>
    GlobalTheory.RationalValues.placeEx R i jL σ' t h c0' hR.models.jV hT hc hR.lev hR.grp.chiW hR.fam.pl_onto hR.fam.muVal⟩

end GlobalTheory.Mem.PlaceVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousUnitaryRootExchangeMapStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_unitaryRootExchangeMap : ∀ (D : D7) (B : HSp D) (η : AE D), η * cA D η = 0 → ∀ v : Fin B.rank → AE D, ∃ K : {y : Fin B.rank → AE D // η • y = y ∧ hA B v y = 0} → GA D B, Continuous K ∧ ∀ y, IsK B v y.1 (K y) := by
  first | exact @GlobalTheory.RootUnip.exists_continuous_isK | exact GlobalTheory.RootUnip.exists_continuous_isK | (intros; apply GlobalTheory.RootUnip.exists_continuous_isK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqConstMulProdInnerOfSlotwiseStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_const_mul_prod_inner_of_slotwise' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] (B : (∀ i, Hs i) → (∀ i, Hs i) → ℂ), (∀ i v v', ∃ c : ℂ, ∀ w w' : Hs i, B (Function.update v i w) (Function.update v' i w') = c * ⟪w, w'⟫_ℂ) → ∃ c : ℂ, ∀ v v', B v v' = c * ∏ i, ⟪v i, v' i⟫_ℂ := by
  first | exact @GlobalTheory.exists_eq_const_mul_prod_inner_of_positionwise | exact GlobalTheory.exists_eq_const_mul_prod_inner_of_positionwise | (intros; apply GlobalTheory.exists_eq_const_mul_prod_inner_of_positionwise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUnitIsDetRoot
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.LatticeUnitRoot

theorem exists_finUnit_isDetRoot : ∀ (D : D7) (S : HSp D) (Λ : Lt D.host.E S.rank), IsSelfDualC S Λ → ∀ k ∈ GfC S, GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt S k) Λ Λ → ∃ x : (AE D)ˣ, FinUnit x ∧ IsDetRoot S k x := by
  intro D V Λ hΛ k hk hm
  have hu : ∀ z ∈ GlobalTheory.Ker.hatV Λ, ∃ y ∈ GlobalTheory.Ker.hatV Λ, (finHom V k).1.mulVec z - z = (1 : ℕ) • y := fun z hz =>
    ⟨_, sub_mem ((hm _).2 ⟨z, hz, rfl⟩) hz, (one_nsmul _).symm⟩
  obtain ⟨w, hw, hwe⟩ := GlobalTheory.MarkDet.det_sub_one_of_cong D.host.F Λ hΛ.1.fg hΛ.1.span_eq_top 1 one_ne_zero _ hu
  rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at hw
  have hn := GlobalTheory.RecDict.det_finHom_norm V k
  obtain ⟨y, y', hy, hy', hyy, hroot, -⟩ := GlobalTheory.OddRoot.exists_root_odd D 1 odd_one _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩, ?_⟩
  have hdet : (finHom V k).1.det = finPart D (matHom V k).1.det := ((finPart D).map_det _).symm
  have hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  have hk1 : infHom V k = 1 := hk
  rw [hk1, Units.val_one, Matrix.det_one] at hdet'
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  refine Prod.ext (((he _).1.trans ?_).trans (he _).1.symm) (((he _).2.trans ?_).trans (he _).2.symm)
  · change infPart D (Y : AE D) = infPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet', GlobalTheory.UnitDetRoot.infPart_sigR_one D _ hY1, hY1, _root_.mul_one]
  · change finPart D (Y : AE D) = finPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet, GlobalTheory.DetRootCong.finPart_sigR, hY2]
    exact hroot

end GlobalTheory.LatticeUnitRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDimensionalKStableSmoothVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDimensional_kStable_smoothVectors : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → (∃ Λ S, IsKTypeOf ε σ Λ S) → ∃ W : Submodule ℂ H, FiniteDimensional ℂ W ∧ W ≠ ⊥ ∧ W ≤ smSub G (trRep σ P) ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ w ∈ W, σ k w ∈ W := by
  first | exact @GlobalTheory.SmVec.exists_finiteDimensional_kStable_smooth | exact GlobalTheory.SmVec.exists_finiteDimensional_kStable_smooth | (intros; apply GlobalTheory.SmVec.exists_finiteDimensional_kStable_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarmonicCoefficientMapAtWeights
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefMapRecord

open Formalism.L2.NTheta

lemma floor_toNat_cast {x : ℚ} (z : ℤ) (hz : x = z) (h0 : 0 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℚ) = x := by
  subst hz
  rw [Int.floor_intCast]
  have h : 0 ≤ z := by exact_mod_cast h0
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

lemma lamAt_b {R : Ranks} (h : HCParam R) (n c : ℕ) (hc : c < R.m) (hn : n = R.k - 1 + c) : lamAt h n = -h.b ⟨c, hc⟩ := by
  subst hn
  unfold lamAt
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 3
  omega

variable (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau)

lemma aPl_cast (n : ℕ) (hn : n < D.R.k + i) :
    (aPl D i (D.R.k + i) τ n : ℚ) =
      lamAt (D.hc τ) n + (D.hc τ).e i - (((D.R.k + i : ℕ) : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  obtain ⟨z, hz⟩ := lamAt_int (D.hc τ) n
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have hs' : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  rw [aPl, if_pos hn]
  refine floor_toNat_cast (z + e - ((D.R.k + i : ℕ) - (n + 1)) - (s + 1)) ?_ ?_
  · rw [hz, he, hs']; push_cast; ring
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hn
    have h1 := lamAt_add_add_le (D.hc τ) d n (by unfold Ranks.r; omega)
    rw [lamAt_b (D.hc τ) (n + d) i hi (by omega)] at h1
    have h2 := (D.hc τ).gap_be i
    rw [hd]
    push_cast
    simp only [Fin.eta] at h1
    linarith

lemma aMi_cast (q n c : ℕ) (hq : i + 1 + q = D.R.m) (hn : n + c + 1 = q) :
    (aMi D i (D.R.k + i) q τ n : ℚ) =
      -((D.hc τ).e i - (D.hc τ).b ⟨i + 1 + c, by omega⟩ + (c + 1) + ((D.R.t : ℚ) - 1) / 2) := by
  have hk := D.R.m_add_three_le_k
  obtain ⟨z, hz⟩ := (D.hc τ).b_int ⟨i + 1 + c, by omega⟩
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have hs' : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  have h0 := lamAt_b (D.hc τ) (D.R.k + i + c) (i + 1 + c) (by omega) (by omega)
  rw [aMi, if_pos (by omega), show q - n = c + 1 by omega, show D.R.k + i + (c + 1) - 1 = D.R.k + i + c by omega, h0,
    ← sub_eq_add_neg, Nat.cast_succ]
  refine floor_toNat_cast (-(e - z + (c + 1) + s)) ?_ ?_
  · rw [hz, he, hs']; push_cast; ring
  · have h1 := lamAt_add_add_le (D.hc τ) c (D.R.k + i) (by unfold Ranks.r; omega)
    rw [h0, lamAt_b (D.hc τ) (D.R.k + i) (i + 1) (by omega) (by omega)] at h1
    have h2 := (D.hc τ).gap_eb i (by omega)
    linarith

lemma lamV_eq : ∃ s : ℤ, ∀ n : Fin (Vc D i).rank, (lamV D i τ).w n =
    s + (if (n : ℕ) < D.R.k + i then (aPl D i (D.R.k + i) τ n : ℤ) else 0) -
      (if (Fin.rev n : ℕ) < D.R.m - (i + 1) then (aMi D i (D.R.k + i) (D.R.m - (i + 1)) τ (Fin.rev n) : ℤ) else 0) := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  obtain ⟨hj, W, hWk, hWm, hWt, hWj, hWe, hWv, hWb, hW⟩ :=
    GlobalTheory.ForcedWeights.lamLForced D (i + 1) (Nat.le_add_left _ _) hi τ
  have hWe' : (W.e : ℚ) = (D.hc τ).e i := hWe
  have hr : (Vc D i).rank = D.R.k + D.R.m - 1 + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) hi
  obtain ⟨q, hq⟩ : ∃ q, i + 1 + q = D.R.m := ⟨D.R.m - (i + 1), by omega⟩
  have hp : W.p = D.R.k + i := by unfold IndefiniteWeightData.WeightData.p; omega
  have hq' : W.q = q := by unfold IndefiniteWeightData.WeightData.q; omega
  have hnV : W.nV = D.R.k + i + q + D.R.t := by unfold IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r; omega
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have ha' : (D.R.k : ℚ) = a + a := by exact_mod_cast ha
  have hb' : (q : ℚ) = b + b - i - 1 := by
    have : ((i : ℕ) : ℚ) + 1 + q = b + b := by exact_mod_cast hq.trans hb
    linarith
  have hd : W.dTau = ((a + (i : ℕ) - b - W.e : ℤ) : ℚ) := by
    unfold IndefiniteWeightData.WeightData.dTau
    rw [hp, hq']
    push_cast
    rw [ha', hb']
    ring
  generalize (a + (i : ℕ) - b - W.e : ℤ) = s at hd
  rw [show D.R.m - (i + 1) = q by omega]
  refine ⟨s, fun n => ?_⟩
  have hn := n.2
  rw [← Int.cast_inj (α := ℚ), hW n, IndefiniteWeightData.WeightData.lamPrime, hd, IndefiniteWeightData.WeightData.thetaWt, hp, hq', hWt, Fin.val_rev,
    Int.cast_sub, Int.cast_add]
  by_cases h1 : (n : ℕ) < D.R.k + i
  · rw [if_pos (by omega), if_pos h1, if_neg (by omega), Int.cast_natCast, aPl_cast D i τ n h1, IndefiniteWeightData.WeightData.aPlus,
      hp, hq', hnV, hWe']
    have hl : (W.lam (n + 1) : ℚ) = lamAt (D.hc τ) n := by
      unfold IndefiniteWeightData.WeightData.lam
      rw [hWk]
      split_ifs with h2
      · rw [lamAt, dif_pos (by omega)]
        exact hWv ⟨n, by omega⟩
      · rw [lamAt_b (D.hc τ) n (n - (D.R.k - 1)) (by omega) (by omega), Int.cast_neg,
          show (n : ℕ) + 1 - (D.R.k - 1) = n - (D.R.k - 1) + 1 by omega]
        exact congrArg _ (hWb ⟨n - (D.R.k - 1), by omega⟩)
    rw [hl]
    push_cast
    ring
  · rw [if_neg (by omega), if_neg h1]
    by_cases h2 : (n : ℕ) + 1 ≤ D.R.k + i + D.R.t
    · rw [if_pos h2, if_neg (by omega)]
      push_cast
      ring
    · obtain ⟨c, hc⟩ : ∃ c, (n : ℕ) = D.R.k + i + D.R.t + c := ⟨n - (D.R.k + i + D.R.t), by omega⟩
      rw [if_neg h2, if_pos (by omega), Int.cast_natCast, aMi_cast D i τ q _ c hq (by omega), IndefiniteWeightData.WeightData.aMinus,
        hq', hWj, hWt, hWe', show q + 1 - (q + 1 - (n + 1 - (D.R.k + i) - D.R.t)) = c + 1 by omega,
        show (i : ℕ) + 1 + (c + 1) = i + 1 + c + 1 by omega, hWb ⟨i + 1 + c, by omega⟩]
      push_cast
      ring

theorem exists_io_record : ∀ (D : D7) (Q : Formalism.L2.Pj.Par D), Q.Pins → ∀ (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), KapIs κ → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff Q.l), ∃ (io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F) (hw : VsV D i c'.F), IoLFRec c' (fun τ => embF c' (tauE D τ)) (lamV D i) (wtA (κ i)) io hw := by
  intro D Q hQ κ hκ i c'
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  obtain ⟨-, hinj, hΨ, -, hval⟩ := GlobalTheory.WeightExponents.weight_exponents D Q hQ _ (inR i) (κ i)
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 _ (inR i)
  have hp1 : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := rfl
  have hq1 : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - (i + 1) := rfl
  choose s hs using lamV_eq D i
  refine GlobalTheory.FrameRead.CoefMap.exists_ioLFRec D.host.E Q.H (Q.Dw ((i : ℕ) + 1)) (Vc D i).rank D.what₂.Tau (DV.tauEmb D)
    ⟨hinj, fun τ => (hΨ τ).trans (exists_congr fun _ => eq_comm)⟩ ?_ Q.l c' (wtA (κ i)) s (lamV D i) (dom_wtA (κ i)).1 ?_
  · refine le_trans ?_ (r_le_V i)
    rw [hp, hq, hp1, hq1, Ranks.r]
    omega
  · intro τ n
    have ht := hQ.1.2.2.2 τ
    have hc : ¬ ComplexEmbedding.conjugate (DV.tauEmb D τ) (Q.H.rt : D.host.E) = Q.H.rt0 :=
      GlobalTheory.WeightExponents.not_inPsi_conj hQ.1 τ
    have hsig : (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
    obtain ⟨h1, h2, -⟩ := hκ i τ
    rw [hsig] at h1 h2
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_pos ht, if_neg hc, hp, hq, hs τ n,
      (hval τ _).1, (hval τ _).2]
    congr 1
    · congr 1
      refine if_ctx_congr Iff.rfl (fun h => ?_) fun _ => rfl
      rw [ext0, dif_pos (show (n : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1 from h), h1]
      rfl
    · refine if_ctx_congr Iff.rfl (fun h => ?_) fun _ => rfl
      rw [ext0, dif_pos (show (Fin.rev n : ℕ) < (D.R.sigW ((i : ℕ) + 1)).2 from h), h2]
      rfl

end GlobalTheory.CoefMapRecord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMeasDef
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.DefiniteMeasure

open Formalism.IndefR.Lev GlobalTheory.Mem.VolExists

theorem exists_level (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (e0 : GA D V ≃ₜ* HA (Ainf D.host.F) D.sp.cm.sig V.gram × HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
    (hf : ∀ h, HA.mat (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (e0 h).2 = finHom V h)
    (hi : ∀ h, HA.mat (Ainf D.host.F) D.sp.cm.sig V.gram (e0 h).1 = infHom V h) :
    ∃ K : Subgroup (HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram),
      (∀ h : GA D V, (e0 h).2 ∈ K ↔ finE V h ∈ lev D.sp.cm V.gram β L) ∧
      IsOpen (K : Set (HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) ∧
      IsCompact (K : Set (HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) := by
  let K : Subgroup (HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram) :=
    (lev D.sp.cm V.gram β L).comap
      ((Formalism.UG.bc (swapAE D)).comp (HR (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).subtype)
  have hK : ∀ h : GA D V, (e0 h).2 ∈ K ↔ finE V h ∈ lev D.sp.cm V.gram β L := fun h => by
    have e : HA.mat (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (e0 h).2 = finHom V h := hf h
    change Formalism.UG.bc (swapAE D) (HA.mat (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (e0 h).2) ∈
      lev D.sp.cm V.gram β L ↔ _
    rw [e]
    rfl
  have hKo : IsOpen (K : Set (HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) := by
    have hc : Continuous fun b : HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram => e0.symm (1, b) :=
      e0.symm.continuous.comp (continuous_const.prodMk continuous_id)
    have h := (GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L).preimage hc
    convert h using 1
    ext b
    have := hK (e0.symm (1, b))
    rw [e0.apply_symm_apply] at this
    exact this
  have hKc : IsCompact (K : Set (HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)) := by
    have hc : Continuous fun h : GA D V => (e0 h).2 := continuous_snd.comp e0.continuous
    have h := (GlobalTheory.ParahoricCompact.isCompact_levG V β L).image hc
    convert h using 1
    ext b
    constructor
    · intro hb
      have h1 := hK (e0.symm (1, b))
      have h2 := hi (e0.symm (1, b))
      rw [e0.apply_symm_apply] at h1 h2
      refine ⟨e0.symm (1, b), ⟨?_, h1.1 hb⟩, congrArg Prod.snd (e0.apply_symm_apply _)⟩
      exact h2.symm
    · rintro ⟨h, hh, rfl⟩
      exact (hK h).2 hh.2
  exact ⟨K, hK, hKo, hKc⟩

theorem exists_isMeasLevW (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hW : V.SigOK)
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (ν : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2))
    (hν : ∀ ρ, (ν ρ).IsHaarMeasure) (hg : ∀ ρ m, good ρ m ↔ m = ν ρ) :
    ∃ μ, IsMeasLevW V (lev D.sp.cm V.gram β L) good μ := by
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.Mem.Vol.isCMFam_host D.R D.host _ D.eTau
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hθ := GlobalTheory.Mem.VolEmb.existsUnique_infEmb D.host.F D.host.E D.sp.cm.sig hcm
  choose θ hθ1 hθ2 using fun i => hθ (tauE D i)
  have hA := fun i => GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (tauE D i))
  choose A hA1 using fun i => (hA i).2.1
  obtain ⟨e1, he1⟩ := GlobalTheory.Mem.InfGroup.real_points D.host.F D.host.E D.sp.cm.sig V.rank V.gram _ (tauE D) θ
    (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) A hcm hτ hθ1 (fun i => hW (tauE D i)) hA1
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  obtain ⟨-, hsc, ht2⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  obtain ⟨K, hK, hKo, hKc⟩ := exists_level D V β L e0 (fun h => Units.ext (he0 h).1) fun h => Units.ext (he0 h).2
  haveI : IsTopologicalGroup (HA (AF D.host.F) D.sp.cm.sig V.gram) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (HA (AF D.host.F) D.sp.cm.sig V.gram) := ⟨rfl⟩
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  have hinj := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective
  haveI := hν
  let e : HA (AF D.host.F) D.sp.cm.sig V.gram ≃ₜ*
      (∀ i, UpqT (V.sig (tauE D i)).1 (V.sig (tauE D i)).2) × HA (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram :=
    e0.trans
      { e1.toMulEquiv.prodCongr (MulEquiv.refl _) with
        continuous_toFun := e1.continuous_toFun.prodMap continuous_id
        continuous_invFun := e1.continuous_invFun.prodMap continuous_id }
  have hee : ∀ h, e h = (e1 (e0 h).1, (e0 h).2) := fun h => rfl
  obtain ⟨μ, hμ, hμB⟩ := exists_haar_prod ν e K hKo hKc
  refine ⟨μ, hμ, ⟨θ, hθ1⟩, fun θ' hθ' => ?_⟩
  obtain rfl : θ' = θ := funext fun i => hθ2 i _ (hθ' i)
  refine ⟨⟨A, hA1⟩, fun A' hA' => ⟨⟨ν, fun ρ => (hg ρ _).2 rfl⟩, fun m hm B hB => ?_⟩⟩
  obtain rfl : m = ν := funext fun ρ => (hg ρ _).1 (hm ρ)
  have hu : ∀ i, ∃ u : UpqT (V.sig (tauE D i)).1 (V.sig (tauE D i)).2, UpqT.mat u * A i = A' i := by
    intro i
    obtain ⟨C, h1, h2⟩ := (hA i).2.2 _ (hA1 i)
    obtain ⟨C', h3, h4⟩ := (hA i).2.2 _ (hA' i)
    exact exists_upq_mul _ _ C C' h1 h2 h3 h4 ((hA1 i).trans (hA' i).symm)
  choose u hu using hu
  have key := hμB (fun i => (fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i))
    (fun i => measurable_const_mul _ (measurable_mul_const _ (hB i)))
  have hcj : ∀ i, m i ((fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i)) = m i (B i) := by
    intro i
    haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant _ _ _ (hν i)
    rw [measure_preimage_mul, measure_preimage_mul_right]
  rw [Finset.prod_congr rfl (fun i _ => hcj i)] at key
  rw [← key]
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, hee, Set.mem_preimage]
  rw [hK]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  have h1 : UpqT.mat (e1 (e0 h).1 i) * A i = A i * infMat D.sp.cm.sig V.gram (θ' i) h := by
    rw [he1, (he0 h).2]; rfl
  have h2 : UpqT.mat (u i * e1 (e0 h).1 i * (u i)⁻¹) * A' i = A' i * infMat D.sp.cm.sig V.gram (θ' i) h := by
    have h3 : UpqT.mat (u i)⁻¹ * A' i = A i := by
      rw [← hu i, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mul]
    rw [mat_mul, mat_mul, Matrix.mul_assoc, h3, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, hu i]
  constructor
  · rintro ⟨b, hb, hbe⟩
    obtain ⟨C', h3, -⟩ := (hA i).2.2 _ (hA' i)
    have : b = u i * e1 (e0 h).1 i * (u i)⁻¹ := by
      apply hinj
      have h5 := congrArg (· * C') (hbe.trans h2.symm)
      simpa only [Matrix.mul_assoc, h3, Matrix.mul_one] using h5
    exact this ▸ hb
  · intro hb
    exact ⟨_, hb, h2⟩

theorem exists_probHaar (P Q : ℕ) (h : P = 0 ∨ Q = 0) : ∃ ν : Measure (UpqT P Q), ν.IsHaarMeasure ∧
    ∀ m : Measure (UpqT P Q), (m.IsHaarMeasure ∧ IsProbabilityMeasure m) ↔ m = ν := by
  haveI : CompactSpace (UpqT P Q) := by
    rcases h with rfl | rfl
    exacts [(GlobalTheory.compactSpace_UpqT_definite Q).2, (GlobalTheory.compactSpace_UpqT_definite P).1]
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  let ν : Measure (UpqT P Q) := Measure.haarMeasure ⊤
  haveI hν : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure ⊤
  haveI hp : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self (K₀ := ⊤)⟩
  refine ⟨ν, hν, fun m => ⟨fun ⟨h1, h2⟩ => ?_, fun e => e ▸ ⟨hν, hp⟩⟩⟩
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure m ν

theorem exists_isMeasDef : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), IsFrame β Λ → V.SigOK → (∀ τ, (V.sig (tauE D τ)).1 = 0 ∨ (V.sig (tauE D τ)).2 = 0) → ∃ μ 𝓕, IsMeasDef V (lev D.sp.cm V.gram β L) μ 𝓕 := by
  intro D V β _ L _ hW hd
  choose ν hν hg using fun ρ => exists_probHaar _ _ (hd ρ)
  obtain ⟨μ, hμ⟩ := exists_isMeasLevW D V β L hW (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m) ν hν hg
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ.1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

end GlobalTheory.Mem.DefiniteMeasure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalUnitaryExchangeUnimodularLatticesInerStatement
section
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_unitary_exchange_unimodular_lattices_inert : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)),
  conjPrime₂ P = P → (∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal) →
  ∀ (X Z : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E X → Submodule.IsLattice E Z →
    IsUnimodular (hStd E n) X → IsUnimodular (hStd E n) Z →
    (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Z) →
    ∃ σ : Submodule (𝓞 E) (Sp E n) → Submodule (𝓞 E) (Sp E n), σ X = Z ∧ σ Z = X ∧
      (∀ Y : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y → IsUnimodular (hStd E n) Y → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) →
        Submodule.IsLattice E (σ Y) ∧ IsUnimodular (hStd E n) (σ Y) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X (σ Y)) ∧
      (∀ Y' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y' → IsUnimodular (hStd E n) Y' → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y') →
        ∃ Y : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
          (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) ∧ σ Y = Y') ∧
      (∀ Y Y' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E Y → IsUnimodular (hStd E n) Y → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) → Submodule.IsLattice E Y' → IsUnimodular (hStd E n) Y' → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y') → σ Y = σ Y' → Y = Y') ∧
      ∀ (s : List ℕ) (Y Y' : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E Y → IsUnimodular (hStd E n) Y → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y) → Submodule.IsLattice E Y' → IsUnimodular (hStd E n) Y' → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q X Y') →
        (IsInertNbr P.asIdeal s (σ Y) (σ Y') ↔ IsInertNbr P.asIdeal s Y Y') := by
  first | exact @GlobalTheory.InertExchange.exchange | exact GlobalTheory.InertExchange.exchange | (intros; apply GlobalTheory.InertExchange.exchange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldHeckeCharacterSqrtNormValuesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberField_heckeCharacter_sqrtNorm_values : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (t : T0), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ (M' : IntermediateField ℚ ℂ), M ≤ M' → ∀ bad : ℕ, D.host.g 0 * D.host.g 1 ∣ bad → (∀ PP ∈ R.Q t, ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ B : Ideal (𝓞 D.host.E) → M', BIs R i M'.val.toRingHom t bad B := by
  first | exact @GlobalTheory.Mem.BVal.exists_field_BIs | exact GlobalTheory.Mem.BVal.exists_field_BIs | (intros; apply GlobalTheory.Mem.BVal.exists_field_BIs <;> assumption)
end

