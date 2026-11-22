import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0184
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepThetaDatumHalfEqSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0112
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCarries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.ThmBFromScal

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem eEp3_eq (R : RealDat3 D A3 Ks)
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c : Pl D.host.E → List ℤ → ℂ} (hc : R.Carries p c) :
    R.EEp3 p = R.EEc c ∧ ∀ i, R.Wp3 i p = R.Wc' i c := by
  refine ⟨le_antisymm (iSup₂_le fun c' hc' => ((hU p c c' hc hc').1).symm.le) (le_iSup₂ (f := fun c' (_ : R.Carries p c') => R.EEc c') c hc),
    fun i => le_antisymm (iSup₂_le fun c' hc' => (((hU p c c' hc hc').2 i)).symm.le)
      (le_iSup₂ (f := fun c' (_ : R.Carries p c') => R.Wc' i c') c hc)⟩

theorem exists_carries (R : RealDat3 D A3 Ks) {p : A3.fam3.base3.Ix} (h : R.EEp3 p ≠ ⊥) :
    ∃ c, R.Carries p c := by
  by_contra hn
  push_neg at hn
  apply h
  unfold RealDat3.EEp3
  exact iSup₂_eq_bot.2 fun c hc => absurd hc (hn c)

theorem wc_eq (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (c : Pl D.host.E → List ℤ → ℂ) :
    R.Wc' i c = GlobalTheory.Hk3.Wcc R.toRealDat R.SF i c := rfl

theorem ec_eq (R : RealDat3 D A3 Ks) (c : Pl D.host.E → List ℤ → ℂ) :
    R.EEc c = GlobalTheory.Hk3.EEc R.toRealDat R.SF c := rfl

end GlobalTheory.ThmBFromScal

namespace GlobalTheory.ThmBFromScal

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem act_on_part (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F)
    {lam : Fin D.R.m → T → GlobalTheory.LiftRows.Eig D → ℝ} {κ : ℝ}
    (hW : ∀ i t c, ∀ x ∈ GlobalTheory.Hk3.Wcc R.toRealDat R.SF i c,
      R.thG i t (LinearMap.adjoint (R.thG i t) x) = ((lam i t c : ℝ) : ℂ) • x)
    (hE : ∀ t c, ∀ x ∈ GlobalTheory.Hk3.EEc R.toRealDat R.SF c,
      R.Th t (LinearMap.adjoint (R.Th t) x) = ((κ * ∏ i, lam i t c : ℝ) : ℂ) • x)
    (hM : GlobalTheory.LiftRows.MatchUp R.toRealDat R.SF)
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c : Pl D.host.E → List ℤ → ℂ} (hc : R.Carries p c) (t : T) :
    (∀ i, R.lam3 i t p A3.A.v0 = lam i t c) ∧
      ∀ x ∈ R.EEp3 p, R.Th t (LinearMap.adjoint (R.Th t) x) =
        ((κ * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p : ℝ) : ℂ) • x := by
  have hEp := (eEp3_eq R hU hc).1
  have hWp := (eEp3_eq R hU hc).2
  have hl : ∀ i, R.lam3 i t p A3.A.v0 = lam i t c := by
    intro i
    refine hC.scal.lam0 i t p (lam i t c) ?_ ?_
    · rw [hWp i, wc_eq]
      exact hM c (by rw [← ec_eq]; exact hc.1) i
    · intro x hx
      rw [hWp i, wc_eq] at hx
      exact hW i t c x hx
  refine ⟨hl, fun x hx => ?_⟩
  rw [hEp] at hx
  rw [hE t c x hx, RealDat3.prod_lamN (R := R) t p]
  simp only [hl]

theorem pThmB {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} :
    A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.LiftRows.Scal R.toRealDat R.SF →
    GlobalTheory.LiftRows.MatchUp R.toRealDat R.SF →
    (∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c') → R.PThmB := by
  intro _ hC _ hS hM hU
  classical
  unfold GlobalTheory.LiftRows.Scal at hS
  obtain ⟨lam, κ, hκ, hlpos, hW, hE⟩ := hS

  have hK : Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 R.lamN κ := by
    intro t p x hx
    rw [LinearMap.comp_apply]
    by_cases h0 : R.EEp3 p = ⊥
    · rw [h0, Submodule.mem_bot] at hx
      subst hx
      simp
    · exact (act_on_part R F hC hW hE hM hU (exists_carries R h0).choose_spec t).2 x hx
  by_cases hex : ∃ (_ : T) (p : A3.fam3.base3.Ix), R.EEp3 p ≠ ⊥
  · obtain ⟨t, p, hp⟩ := hex
    have hc := (exists_carries R hp).choose_spec
    have hl := (act_on_part R F hC hW hE hM hU hc t).1
    have hk : R.kap = κ := by
      refine hC.scal.kap κ hK ⟨t, p, hp, ?_⟩
      rw [RealDat3.prod_lamN (R := R) t p, Finset.prod_congr rfl fun i _ => hl i]
      exact (Finset.prod_pos fun i _ => hlpos i t _).ne'
    intro t' p' x hx
    exact (hK t' p' x hx).trans (by rw [hk])
  · push_neg at hex
    intro t p x hx
    rw [hex t p, Submodule.mem_bot] at hx
    subst hx
    simp

end GlobalTheory.ThmBFromScal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHalfLatticeAdjointFrameReductionsEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_halfLattice_adjointFrame_reductions_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ z : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
  ∃ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) ∧ ∀ PP ∈ R.Pg ∪ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) = z PP := by
  first | exact @GlobalTheory.AdjRedOnto.exists_half_redM_eq | exact GlobalTheory.AdjRedOnto.exists_half_redM_eq | (intros; apply GlobalTheory.AdjRedOnto.exists_half_redM_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseAtSplitPlacesOfUnits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LocalInvIdem

theorem toEAf_surj {D : D7} (a : EAf D) : ∃ α : AE D, toEAf D α = a := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, by rw [RingHom.map_add, hp, hq]⟩
  | tmul x y => exact ⟨pairA D.host.F 0 y ⊗ₜ[D.host.F] x, rfl⟩

theorem inv_of_chart {D : D7} {ePP α : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (hC : GlobalTheory.SplitHecke.Chart ePP v π) {c : Fv D.host.F v} (hc : π α = c) (hv1 : Valued.v c = 1) :
    ∃ γ : AE D, finPart D γ ∈ intAE D ∧ α * γ = ePP := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hv1; exact zero_ne_one hv1
  obtain ⟨t, ht⟩ := hC.1 c⁻¹
  refine ⟨ePP * t, ?_, ?_⟩
  · refine (hC.2.2.2 t).2 (GlobalTheory.SplitHecke.isInt_Ov.2 ?_)
    rw [ht, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]
  · have h1 : π (α * t - 1) = 0 := by
      rw [map_sub, map_mul, ht, hc, mul_inv_cancel₀ hc0, map_one, sub_self]
    have h2 := (hC.2.1 _).1 h1
    linear_combination h2

theorem exists_local_inv {D : D7} {PP : Pl D.host.E} {ePP : AE D} (hPP : Formalism.L2.NTheta.IsIdemAt ePP PP)
    (α : AE D) (ha : toEAf D α ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hu : IsUnit (Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D α, ha⟩)) :
    ∃ γ : AE D, finPart D γ ∈ intAE D ∧ α * γ = ePP := by
  obtain ⟨v, τ, hIdem, hP⟩ := GlobalTheory.SplitIdemDict.exists_emb hPP
  have hProj := (GlobalTheory.SplitIdemDict.isProjAt_iff τ PP).2 hP
  obtain ⟨⟨r, -, hr0, -, hrS⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v (splitProj τ) PP hProj
  obtain ⟨hC, hE, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v (splitProj τ) ePP hIdem
  obtain ⟨hmem, hrr⟩ := hrS (toEAf D α) ha
  obtain ⟨c, hc⟩ : ∃ c, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA (splitProj τ) α = c := ⟨_, rfl⟩
  have hcE := (hE α).trans hc
  have : Nontrivial (Formalism.L2.DIV.kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  have hv1 : Valued.v c = 1 := by
    have hle : Valued.v c ≤ 1 := by
      rw [← hcE]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hmem
    refine le_antisymm hle (not_lt.1 fun hlt => hu.ne_zero ?_)
    rw [← hrr]
    refine (hr0 _).2 ?_
    exact (congrArg Valued.v hcE).trans_lt hlt
  exact inv_of_chart hC hc hv1

theorem exists_inv : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (a : EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ Z, IsUnit (Formalism.L2.DIV.resS D.host.F PP ⟨a, ha⟩)) → ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, a * w * toEAf D e = toEAf D e := by
  intro D Z e he a ha hZ
  obtain ⟨α, rfl⟩ := toEAf_surj a
  obtain ⟨es, hes, hsum⟩ := he.1
  have key : ∀ PP ∈ Z, ∃ γ : AE D, finPart D γ ∈ intAE D ∧ α * γ = es PP :=
    fun PP hPP => exists_local_inv (hes PP hPP) α ha (hZ PP hPP)
  choose! γ hγ1 hγ2 using key
  refine ⟨toEAf D (∑ PP ∈ Z, γ PP), GlobalTheory.IdemIntegral.toEAf_mem_of_finPart ?_, ?_⟩
  · rw [map_sum (finPart D)]; exact sum_mem fun PP hPP => hγ1 PP hPP
  · have hαw : α * ∑ PP ∈ Z, γ PP = e := by
      rw [Finset.mul_sum, hsum]; exact Finset.sum_congr rfl fun PP hPP => hγ2 PP hPP
    have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
    rw [← map_mul, ← map_mul, hαw, hee]

end GlobalTheory.LocalInvIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedModelSelfDualLatticeInvariantLinearFoStatement
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixedModelSelfDualLattice_invariant_linearForm : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 ∧ (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) ∧ (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) ∧ (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ℓ (ρ (embLow n' n z) s) = if z ∈ intMat L (Fin (n' / 2)) (Fin (n / 2)) then 1 else 0 := by
  first | exact @GlobalTheory.SphTheta.exists_mixLat_form | exact GlobalTheory.SphTheta.exists_mixLat_form | (intros; apply GlobalTheory.SphTheta.exists_mixLat_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplicityMapPrescribedValueDefiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplicityMap_prescribed_value_definite : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank), IsInfFam θ → V.SigOK → V.IsDefinite → c.Is → IsDualPair θ M c pr → Function.Surjective pr → (∀ x, levFn β (flag1L L) x = 1) → (∀ c₀ : Cl D.sp.cm V.gram (lev D.sp.cm V.gram β (flag1L L)), Gam c₀ = ⊥) → ∀ (h : GA D V) (ℓ : MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) ℂ), ∃ T ∈ Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L)), evAt M h T = ℓ ∧ ∀ h' : GA D V, clsA V (lev D.sp.cm V.gram β (flag1L L)) h' ≠ clsA V (lev D.sp.cm V.gram β (flag1L L)) h → evAt M h' T = 0 := by
  first | exact @GlobalTheory.DefFree.exists_mult_value | exact GlobalTheory.DefFree.exists_mult_value | (intros; apply GlobalTheory.DefFree.exists_mult_value <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNsmulActO
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinear

open GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove

variable {D : D7} {S T : HSp D}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_nsmul_actO (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT)
    (g : GA D S) (h : GA D T) : ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      N • actO S T g h u ∈ latO S T ΛS ΛT fun _ => True := by
  obtain ⟨M, hM, hMu⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.fg hT.fg
  obtain ⟨K, hK, hKt⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS hT
  obtain ⟨N, hN, hNm⟩ := GlobalTheory.PlaceDatum.exists_den_mul (Formalism.L2.Herm.intAf D.host.F D.host.E)
    (fun z => GlobalTheory.PlaceDatum.exists_den_adele z) ((Formalism.L2.Theta.mt T h).map (toEAf D))
    ((Formalism.L2.Theta.mt S g⁻¹).map (toEAf D))
  refine ⟨K * (N * M), Nat.mul_pos hK (Nat.mul_pos hN hM), fun u hu => ?_⟩
  rw [← smul_smul]
  apply hKt
  · have h0 := GlobalTheory.SplitScalar.latO_fin hu
    have hz : (actO S T g h u).map (infPart D) = 0 := by
      simp only [actO, Matrix.map_mul, h0, Matrix.mul_zero, Matrix.zero_mul]
    ext i j
    have hij := congrFun (congrFun hz i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul, Matrix.zero_apply] at hij ⊢
    rw [hij, smul_zero]
  · intro i j
    have hX := hNm M (u.map (toEAf D)) (fun i j => hMu u hu i j) i j
    have e1 : toEAf D (((N * M) • actO S T g h u) i j) = ((N * M : ℕ) : EAf D) *
        ((Formalism.L2.Theta.mt T h).map (toEAf D) * u.map (toEAf D) * (Formalism.L2.Theta.mt S g⁻¹).map (toEAf D)) i j := by
      simp only [actO]
      rw [Matrix.smul_apply, map_nsmul, nsmul_eq_mul, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
    rw [e1]
    exact hX

theorem isSBHalf_actO (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) {a : AE D}
    (g : GA D S) (h : GA D T) {Φ : WO S T → ℂ} (hΦ : IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ) :
    IsSBHalf a (latO S T ΛS ΛT fun _ => True) fun t => Φ (actO S T g h t) := by
  simp only [IsSBHalf] at hΦ ⊢
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  obtain ⟨N, hN, hNu⟩ := exists_nsmul_actO hS hT g h
  obtain ⟨M, hM, hMu⟩ := exists_nsmul_actO hS hT g⁻¹ h⁻¹
  refine ⟨fun t ht => isHalf_of_act g h (h1 _ ht), k * (N * M), Nat.mul_pos hk (Nat.mul_pos hN hM), ?_, ?_⟩
  · intro u hu hua t
    rw [act_add, act_nsmul]
    have hw := hNu u hu
    have hwa : IsHalf a (N • actO S T g h u) :=
      GlobalTheory.SplitScalar.isHalf_nsmul (GlobalTheory.SplitHecke.isHalf_actO g h hua) N
    have e : (k * (N * M)) • actO S T g h u = k • (M • (N • actO S T g h u)) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [e]
    exact h2 _ (AddSubgroup.nsmul_mem _ hw M) (GlobalTheory.SplitScalar.isHalf_nsmul hwa M) _
  · intro t ht
    have hm := hMu _ (h3 _ ht)
    rw [act_nsmul, GlobalTheory.SplitHecke.actO_inv_actO] at hm
    have e : (k * (N * M)) • t = N • (M • (k • t)) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [e]
    exact AddSubgroup.nsmul_mem _ hm N

theorem absV_mul {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : (Fv F v)ˣ) :
    absV F v (x * y) = absV F v x * absV F v y := by
  unfold absV
  have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  rw [Units.val_mul, map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
    ((Valuation.ne_zero_iff _).mpr y.ne_zero), zpow_add₀ hq]

theorem absFin_mul (x y : (AE D)ˣ) : absFin D (x * y) = absFin D x * absFin D y := by
  unfold absFin
  simp_rw [map_mul, absV_mul]
  exact finprod_mul_distrib (absFin_finite D x) (absFin_finite D y)

theorem absFin_one : absFin D 1 = 1 := by
  have h := absFin_mul (D := D) 1 1
  rw [mul_one] at h
  have hp := absFin_pos D 1
  have h2 : absFin D 1 * (absFin D 1 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hp.ne'
  · linarith

theorem modFac_mul (x x' y y' : (AE D)ˣ) : modFac S T (x * x') (y * y') = modFac S T x y * modFac S T x' y' := by
  unfold modFac
  rw [absFin_mul, absFin_mul, Real.mul_rpow (absFin_pos D x).le (absFin_pos D x').le,
    Real.mul_rpow (absFin_pos D y).le (absFin_pos D y').le]
  ring

theorem modFac_one : modFac S T 1 1 = 1 := by
  unfold modFac
  rw [absFin_one, Real.one_rpow, Real.one_rpow, one_mul]

end GlobalTheory.SplitLinear

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzHeisenbergOperatorDerivativeStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartz_heisenbergOperatorDerivative : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : SchwartzMap V ℂ),
    ∃ g : SchwartzMap V ℂ, ∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x := by
  first | exact @GlobalTheory.dHeis_schwartz | exact GlobalTheory.dHeis_schwartz | (intros; apply GlobalTheory.dHeis_schwartz <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecondStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaFunction_standardPairSecond : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A' WW : HSp D) (rA' : Rig A') (rW : Rig WW) (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Pl D.host.E)) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (vac : WO A' WW → ℂ), rA'.Is → rW.Is → IsHeckeChar D ν → IsIdemSum e S → I ≠ ⊥ → IsVacO ψ θ A' WW rA'.s rW.s rA'.Λ rW.Λ vac → ∃ f, IsThetaAt ψ (symplO A' WW) (heisO ψ A' WW) (cA D e) (latO A' WW rA'.Λ rW.Λ fun _ => True) 1 vac (stdSnd ν e I a A' WW rA'.β rW.β) f ∧ IsThetaFunO ψ A' WW f := by
  first | exact @GlobalTheory.CompanionTheory.StdSndTheta.exists_theta | exact GlobalTheory.CompanionTheory.StdSndTheta.exists_theta | (intros; apply GlobalTheory.CompanionTheory.StdSndTheta.exists_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightBruhatFundamentalDomainCentralizer
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

namespace GlobalTheory.WeightUnfold

theorem exists_weight (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H) (hcomm : IsMulCommutative (cent γ)) (μ : Measure H) [μ.IsHaarMeasure] (dt : Measure (cent γ)) [dt.IsHaarMeasure] (𝓣 : Set (cent γ)) (hfd : IsFundamentalDomain (Γ.subgroupOf (cent γ)) 𝓣 dt) :
    ∃ α : H → ℝ≥0∞, Measurable α ∧ (∀ y, ∑' h : Γ.subgroupOf (cent γ), α (((h : cent γ) : H) * y) = 1) ∧ ∀ ψ : H → ℝ≥0∞, Measurable ψ → LeftInv (cent γ) ψ → ∫⁻ y, α y * ψ y ∂μ = dt 𝓣 * ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
  have hTcl : IsClosed ((cent γ : Subgroup H) : Set H) := Set.isClosed_centralizer _
  have hc : ∀ a b : cent γ, a * b = b * a := fun a b => hcomm.is_comm.comm a b
  haveI : LocallyCompactSpace (cent γ) := hTcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : dt.IsMulRightInvariant := ⟨fun g => by
    have : (fun x : cent γ => x * g) = (fun x => g * x) := funext fun x => hc x g
    rw [this]; exact map_mul_left_eq_self dt g⟩
  obtain ⟨β, hβm, hβ⟩ := exists_bruhat (T := cent γ) hTcl dt
  have hprod : Measurable fun p : H × cent γ => β (((p.2 : cent γ) : H) * p.1) :=
    hβm.comp ((measurable_subtype_coe.comp measurable_snd).mul measurable_fst)
  have hsec : ∀ x : H, Measurable fun t : cent γ => β ((t : H) * x) := fun x =>
    hβm.comp (measurable_subtype_coe.mul_const x)
  refine ⟨fun y => ∫⁻ t in 𝓣, β ((t : H) * y) ∂dt, ?_, ?_, ?_⟩
  · exact hprod.lintegral_prod_right'
  · intro y
    haveI : Countable Γ := by
      haveI : TopologicalSpace.SeparableSpace Γ := inferInstance
      exact TopologicalSpace.separableSpace_iff_countable.mp inferInstance
    haveI : Countable (Γ.subgroupOf (cent γ)) := by
      refine Function.Injective.countable (f := fun h : Γ.subgroupOf (cent γ) => (⟨((h : cent γ) : H), h.2⟩ : Γ)) ?_
      intro a b hab
      apply Subtype.ext; apply Subtype.ext
      simpa using congrArg Subtype.val hab
    rw [← hβ y, hfd.lintegral_eq_tsum'' (fun t : cent γ => β ((t : H) * y))]
    refine tsum_congr fun h => lintegral_congr fun t => ?_
    congr 1
    have e : ((h • t : cent γ) : H) = ((h : cent γ) : H) * (t : H) := rfl
    rw [e, ← mul_assoc, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hc]
  · intro ψ hψm hψ
    haveI : dt.IsMulLeftInvariant := inferInstance
    have hq := isQuotMeasure_quotMeas (T := cent γ) dt μ hTcl

    have hinner : ∀ t : cent γ, ∫⁻ y, β ((t : H) * y) * ψ y ∂μ = ∫⁻ y, β y * ψ y ∂μ := by
      intro t
      have : (fun y => β ((t : H) * y) * ψ y) = fun y => (fun z => β z * ψ z) ((t : H) * y) := by
        funext y; show _ = β _ * ψ _; rw [hψ (t : H) t.2 y]
      rw [this]; exact lintegral_mul_left_eq_self (fun z => β z * ψ z) (t : H)
    have hC : ∫⁻ y, β y * ψ y ∂μ = ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
      rw [hq (fun y => β y * ψ y) (hβm.mul hψm)]
      refine lintegral_congr fun q => ?_
      have : (fun t : cent γ => β ((t : H) * Quotient.out q) * ψ ((t : H) * Quotient.out q)) = fun t : cent γ => β ((t : H) * Quotient.out q) * ψ (Quotient.out q) := by
        funext t; rw [hψ (t : H) t.2]
      rw [this, lintegral_mul_const _ (hsec _), hβ, one_mul]
      rfl
    calc ∫⁻ y, (∫⁻ t in 𝓣, β ((t : H) * y) ∂dt) * ψ y ∂μ
        = ∫⁻ y, ∫⁻ t in 𝓣, β ((t : H) * y) * ψ y ∂dt ∂μ := by
          refine lintegral_congr fun y => ?_
          rw [lintegral_mul_const _ (hsec y)]
      _ = ∫⁻ t in 𝓣, ∫⁻ y, β ((t : H) * y) * ψ y ∂μ ∂dt := by
          refine lintegral_lintegral_swap ?_
          exact (hprod.mul (hψm.comp measurable_fst)).aemeasurable
      _ = ∫⁻ t in 𝓣, ∫⁻ y, β y * ψ y ∂μ ∂dt := by
          refine lintegral_congr fun t => hinner t
      _ = dt 𝓣 * ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
          rw [lintegral_const, Measure.restrict_apply_univ, hC, mul_comm]

end GlobalTheory.WeightUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdelicMemFrameStabilizerOfLatticeTransportStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelic_mem_frameStabilizer_of_latticeTransport : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, IsMov (fmt V k) L L → Lev.finE V k ∈ Formalism.L2.DIV.St β := by
  first | exact @GlobalTheory.LevMov.finE_mem_St_of_isMov | exact GlobalTheory.LevMov.finE_mem_St_of_isMov | (intros; apply GlobalTheory.LevMov.finE_mem_St_of_isMov <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingIdempotentPatchInFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FineCut

theorem conj_cut {R : Type} [CommRing R] {n : ℕ} (β F : GL (Fin n) R) (c : R) :
    β.1 * (c • (β⁻¹ * F * β).1 + (1 - c) • (1 : Matrix (Fin n) (Fin n) R)) * (β⁻¹).1
      = c • F.1 + (1 - c) • (1 : Matrix (Fin n) (Fin n) R) := by
  have h1 : β.1 * (β⁻¹ * F * β).1 * (β⁻¹).1 = F.1 := by
    rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
  have h2 : β.1 * (β⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h1, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, h2]

theorem finE_cut : ∀ {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (g k : GA D T) (ε : AE D), Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → (Formalism.IndefR.Lev.finE T k : GL (Fin T.rank) (EAf D)).1 = βT.1 * (toEAf D ε • (βT⁻¹ * Formalism.IndefR.Lev.finE T g * βT : GL (Fin T.rank) (EAf D)).1 + (1 - toEAf D ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (EAf D))) * (βT⁻¹ : GL (Fin T.rank) (EAf D)).1 := by
  intro D T βT g k ε h
  have hk : (Formalism.IndefR.Lev.finE T k : GL (Fin T.rank) (EAf D)).1
      = toEAf D ε • (Formalism.IndefR.Lev.finE T g : GL (Fin T.rank) (EAf D)).1 + (1 - toEAf D ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (EAf D)) := by
    show (Formalism.L2.Theta.mt T k).map (toEAf D) = toEAf D ε • (Formalism.L2.Theta.mt T g).map (toEAf D) + (1 - toEAf D ε) • 1
    rw [h, GlobalTheory.CompStab.map_idem]
  rw [hk]
  exact (conj_cut βT (Formalism.IndefR.Lev.finE T g) (toEAf D ε)).symm

end GlobalTheory.FineCut

end
end

