import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonStepZeroScalarFormsEqPosMulInner
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0429
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0430
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChiPowOfLevG
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemGinfCOfFinM
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonStepZeroScalarFormsEqPosMulInnerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_stepZeroScalarForms_eq_pos_mul_inner : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (θ : InfFam D), IsInfFam θ → CoCpt (D.sp.X 0) → ∀ (vS : Vol (D.sp.X 0)) (y : (D.mem u).C.Y 0), ∃ c : ℝ, 0 < c ∧ ∀ φ ψ : D.what₂.Mu u, ∫ g in vS.𝓕, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y g * star ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u ψ).1 y g) ∂vS.μ = (c : ℂ) * inner ℂ ψ φ := by
  first | exact @GlobalTheory.StepZeroNorm.integral_rd_eq_inner | exact GlobalTheory.StepZeroNorm.integral_rd_eq_inner | (intros; apply GlobalTheory.StepZeroNorm.integral_rd_eq_inner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiOneEqOneIffColumnConditionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_one_eq_one_iff_column_condition : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}
    (K : Type) [Field K] (d : Formalism.L2.Col.Deco E a ST SG) (d' : Formalism.L2.Col.Deco E b ST SG') (t : 𝓞 E), d.Ok → d'.Ok →
    d.N = Formalism.L2.Col.stdLat E a → d'.N = Formalism.L2.Col.stdLat E b →
    (∀ P : ST, ∀ x ∈ Formalism.L2.Col.stdLat E a, ∀ r : Fin a, r.1 + 1 = a → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c)) →
    (∀ P : ST, ∀ x ∈ Formalism.L2.Col.stdLat E b, ∀ r : Fin b, r.1 + 1 = b → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d'.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c)) →
    ∀ x : Formalism.L2.Col.HomE E a b, (Formalism.L2.Col.phiT K d d' x = 1 ↔ ∀ P : ST, ColCond P.1 t x) := by
  first | exact @GlobalTheory.PhiOneVal.phiT_eq_one_iff_colCond | exact GlobalTheory.PhiOneVal.phiT_eq_one_iff_colCond | (intros; apply GlobalTheory.PhiOneVal.phiT_eq_one_iff_colCond <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelRestrictedTensorFixedHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_model_restricted_tensor_fixed_half : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AE D) (Λ Λ' : AddSubgroup (WO S T)) (Φ f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → (∀ t, IsHalf b t → (t ∈ Λ' ↔ t ∈ Λ)) → IsSBHalf a Λ Φ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm → IsPlaceModel ψ (symplO S T) (heisO ψ S T) b Λ' 1 (Tm (GlobalTheory.FinPl.PutIn.tens b Φ (halfInd b Λ))) (Tm ∘ₗ GlobalTheory.FinPl.PutIn.tensR b Φ) := by
  first | exact @GlobalTheory.FinPl.PutIn.Factor.isPlaceModel_tensR | exact GlobalTheory.FinPl.PutIn.Factor.isPlaceModel_tensR | (intros; apply GlobalTheory.FinPl.PutIn.Factor.isPlaceModel_tensR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrHOUpIncAdj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastPrimSplit

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_e (q : GlobalTheory.FinPl.SplitPt D k) : q.pr q.e = 1 := by
  rw [← GlobalTheory.FinPl.FrameLat.sec_one q, q.pr_sec]

theorem mem_intAt_iff_pr (q : GlobalTheory.FinPl.SplitPt D k) (a : AE D) (ha : a ∈ GlobalTheory.FinPl.idAt D (· = q.v)) :
    a ∈ GlobalTheory.FinPl.intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k] := by
  have he := (GlobalTheory.FinPl.FrameLat.e_mem_intAt q).2
  constructor
  · rintro ⟨-, h⟩
    constructor
    · rw [q.int_iff, q.sec_pr, RingHom.map_mul]
      exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE he h
    · rw [q.int_iff, q.sec_pr, RingHom.map_mul]
      exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE he ((GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 h)
  · rintro ⟨h1, h2⟩
    refine ⟨ha, ?_⟩
    rw [q.int_iff, q.sec_pr] at h1 h2
    rw [← GlobalTheory.FinPl.FrameLat.cA_int_iff, RingHom.map_mul, GlobalTheory.LocSympl.conj_conj] at h2
    rw [← (GlobalTheory.FinPl.FrameLat.idem_iff q a).1 ha, add_mul, RingHom.map_add]
    exact add_mem h1 h2

theorem incAdj_yZero_apply {ρ : ℕ} (hρ : 0 < ρ) {S T T₀ : HSp D} (d : HypDec T T₀ ρ) (z : Fin S.rank → D.host.E)
    (a : AE D) (i : Fin T.rank) (l : Fin S.rank) :
    d.incAdj S (a • yZero S ρ z) i l =
      cA D a * incA D (D.host.xi0⁻¹ * d.e' i ⟨ρ - 1, by omega⟩ * (star z ᵥ* S.gram) l) := by
  have hell : ∀ i : Fin ρ, cA D (ell D ρ i) = if i = ⟨ρ - 1, by omega⟩ then 1 else 0 := by
    intro i
    simp only [ell, Fin.ext_iff]
    split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | simp
  simp only [HypDec.incAdj_apply, HypDec.incY_apply, yZero, zEll, Matrix.vecMul, dotProduct,
    Matrix.mul_apply, Matrix.smul_apply, Matrix.neg_apply, adj, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, map_mul, map_neg, hell, map_sum]
  rw [Finset.sum_eq_single (⟨ρ - 1, by omega⟩ : Fin ρ) (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only [if_true, mul_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  change incA D (d.e' i _) * (-incA D _ * (cA D a * -incA D (star (z m)) * incA D (S.gram m l))) =
    cA D a * (incA D _ * incA D (d.e' i _) * (incA D (star (z m)) * incA D (S.gram m l)))
  ring

theorem map_row {E : Type} [Field E] (f : E →+* k) {m n : Type} [Fintype m] (w : m → E) (M : Matrix m n E) (j : n) :
    ∑ l, f (w l) * f (M l j) = f ((w ᵥ* M) j) := by
  simp only [Matrix.vecMul, dotProduct, map_sum, RingHom.map_mul]

theorem row_core (q : GlobalTheory.FinPl.SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n] (sc : k)
    (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (hF₀ : (ofSplit q).IsCoreFrame B sc FA F₀) :
    (fun l => q.pr (incA D ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l))) ᵥ* F₀.β =
      Pi.single (Sum.inr ()) (sc * (ofSplit q).hz B) := by
  set f := q.pr.comp (incA D) with hf
  funext t
  rcases t with t | ⟨⟨⟩⟩
  · rw [Pi.single_eq_of_ne Sum.inl_ne_inr]
    have h0 : (fun l => f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l)) ᵥ* B.o.iA.map f = 0 := by
      funext j
      refine (map_row f _ B.o.iA j).trans ?_
      rw [vecB, Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, B.o.orth,
        Matrix.vecMul_zero, Pi.zero_apply, Pi.zero_apply, map_zero]
    have h1 : ((fun l => f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l)) ᵥ* (B.o.iA.map f * FA.β)) t = 0 := by
      rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul, Pi.zero_apply]
    rw [← h1]
    change ∑ l, f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l) * F₀.β l (Sum.inl t) =
      ∑ l, f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l) * (B.o.iA.map f * FA.β) l t
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hF₀.1 l t]
    rfl
  · rw [Pi.single_eq_same]
    have h0 : (star (vecB B.o B.ζ) ᵥ* B.V₀.gram) ⬝ᵥ vecB B.o B.ζ = star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ := by
      rw [vecB, Matrix.star_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, B.o.isoB]
    change ∑ l, f _ * F₀.β l (Sum.inr ()) = sc * f (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)
    rw [← h0, dotProduct, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hF₀.2 l, RingHom.map_mul, mul_left_comm]
    rfl

theorem row_jac (q : GlobalTheory.FinPl.SplitPt D k) {ρ : ℕ} (hρ : 0 < ρ) (J : JacLev D ρ) {n' : Type} [Fintype n'] [DecidableEq n']
    (sc hh : k) (FW₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (2 * ρ)))
    (hFW : (ofSplit q).IsJacFrame J sc hh FW₀ FW) :
    (fun l => q.pr (incA D ((J.d.e'ᴴ * J.W.gram) ⟨ρ - 1, by omega⟩ l))) ᵥ* FW.β =
      Pi.single (Sum.inr ⟨ρ - 1, by omega⟩) (sc * (ofSplit q).xi) := by
  set f := q.pr.comp (incA D) with hf
  set i₀ : Fin ρ := ⟨ρ - 1, by omega⟩ with hi₀
  have hcol : ∀ {m : ℕ} (M : Matrix (Fin J.W.rank) (Fin m) D.host.E) (j : Fin m),
      ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * f (M l j) = f ((J.d.e'ᴴ * J.W.gram * M) i₀ j) := fun M j => by
    rw [Matrix.mul_apply (M := J.d.e'ᴴ * J.W.gram), map_sum]
    simp only [RingHom.map_mul]
  funext t
  rcases t with t | t
  · rw [Pi.single_eq_of_ne Sum.inl_ne_inr]
    have hz : J.d.e'ᴴ * J.W.gram * J.d.i₀ = 0 := by
      have := congrArg Matrix.conjTranspose J.d.i₀e'
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
        ← Matrix.mul_assoc] at this
    have h0 : (fun l => f ((J.d.e'ᴴ * J.W.gram) i₀ l)) ᵥ* J.d.i₀.map f = 0 := by
      funext j
      refine (hcol J.d.i₀ j).trans ?_
      rw [hz, Matrix.zero_apply, map_zero, Pi.zero_apply]
    have h1 : ((fun l => f ((J.d.e'ᴴ * J.W.gram) i₀ l)) ᵥ* (J.d.i₀.map f * FW₀.β)) t = 0 := by
      rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul, Pi.zero_apply]
    rw [← h1]
    change ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * FW.β l (Sum.inl t) =
      ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * (J.d.i₀.map f * FW₀.β) l t
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hFW.2.1 l t]
    rfl
  · change ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * FW.β l (Sum.inr t) = _
    have hmul : ∀ (c : k) (M : Matrix (Fin J.W.rank) (Fin ρ) D.host.E) (j : Fin ρ),
        (∀ r, FW.β r (Sum.inr t) = c * f (M r j)) →
        ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * FW.β l (Sum.inr t) = c * f ((J.d.e'ᴴ * J.W.gram * M) i₀ j) := fun c M j h => by
      rw [← hcol, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [h, mul_left_comm]
    by_cases ht : t.val < ρ
    · rw [hmul _ _ _ (hFW.2.2.1 ⟨t.val, ht⟩ t rfl), J.d.e'e]
      by_cases h2 : t.val = ρ - 1
      · have h3 : t = ⟨ρ - 1, by omega⟩ := Fin.ext h2
        have h4 : (⟨t.val, ht⟩ : Fin ρ) = i₀ := Fin.ext h2
        have h5 : ρ - (i₀ : ℕ) = 1 := by change ρ - (ρ - 1) = 1; omega
        rw [h4, Matrix.one_apply_eq, map_one, mul_one, h5, pow_one, h3, Pi.single_eq_same]
      · rw [Matrix.one_apply_ne fun h => h2 (congrArg Fin.val h).symm, map_zero, mul_zero,
          Pi.single_eq_of_ne fun h => h2 (congrArg Fin.val (Sum.inr_injective h))]
    · have h6 := t.2
      rw [hmul _ _ _ (hFW.2.2.2 ⟨2 * ρ - 1 - t.val, by omega⟩ t (by change t.val + (2 * ρ - 1 - t.val) + 1 = _; omega)),
        J.d.e'e', Matrix.zero_apply, map_zero, mul_zero, Pi.single_eq_of_ne fun h => ht (by
          have h7 : t.val = ρ - 1 := congrArg Fin.val (Sum.inr_injective h)
          omega)]

end GlobalTheory.LastPrimSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrMemOfMemLatV
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdPairTop

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_mem_of_mem_latV (p : SplitPt D k) {S : HSp D} {L : Lat S}
    (hL : ∀ z ∈ L, z ∈ GlobalTheory.AdForm.intVec D S.rank) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L (· = p.v)) (i : Fin S.rank) : p.pr (y i) ∈ 𝒪[k] := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    rw [p.int_iff, p.sec_pr, map_mul]
    refine FrameLat.mul_mem_intAE (FrameLat.e_mem_intAt p).2 ?_
    simp only [one_mul]
    exact AddSubgroup.subset_closure ⟨α, hα, ⟨x i, hL x hx i⟩, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => simpa using add_mem ha hb
  | neg a _ ha => simpa using neg_mem ha

theorem rat_mulVec_sec (p : SplitPt D k) {a b : ℕ} (Q : Matrix (Fin a) (Fin b) D.host.E) (w : Fin b → k) :
    rat Q *ᵥ (fun i => p.sec (w i)) = fun i => p.sec (((rat Q).map p.pr *ᵥ w) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (rat Q i j), FrameLat.sec_mul_right, mul_comm (w j)]

theorem hasVal_of_single {n : Type} [Fintype n] [DecidableEq n] (Q : GlobalTheory.LatPair.Pair k n) (l : n) (c : 𝓀[k])
    (hval : ∀ i, Q.HasVal (Pi.single i 1) (if i = l then c else 0)) (x : n → k) (hx : ∀ i, x i ∈ 𝒪[k]) :
    Q.HasVal x (residue 𝒪[k] ⟨x l, hx l⟩ * c) := by
  have key : ∀ T : Finset n, Q.HasVal (∑ i ∈ T, (⟨x i, hx i⟩ : 𝒪[k]) • (Pi.single i 1 : n → k))
      (∑ i ∈ T, residue 𝒪[k] ⟨x i, hx i⟩ * (if i = l then c else 0)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using GlobalTheory.LatPair.Pair.mem_ker.1 (zero_mem Q.ker)
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact ((hval a).smul _).add ih
  have h1 : (∑ i, (⟨x i, hx i⟩ : 𝒪[k]) • (Pi.single i 1 : n → k)) = x := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
  have h2 : (∑ i, residue 𝒪[k] ⟨x i, hx i⟩ * (if i = l then c else 0)) = residue 𝒪[k] ⟨x l, hx l⟩ * c := by
    simp [mul_ite]
  have := key Finset.univ
  rwa [h1, h2] at this

theorem mem_ker_iff {n : Type} (q : GlobalTheory.LatPair.Unif k) (Q : GlobalTheory.LatPair.Pair k n) (l : n) (c : 𝓀[k]) (hc : c ≠ 0)
    (hlat : ∀ x ∈ Q.lat, ∀ i, x i ∈ 𝒪[k])
    (hval : ∀ (x : n → k) (hx : ∀ i, x i ∈ 𝒪[k]), Q.HasVal x (residue 𝒪[k] ⟨x l, hx l⟩ * c)) (x : n → k) :
    x ∈ Q.ker ↔ (∀ i, x i ∈ 𝒪[k]) ∧ q.inv * x l ∈ 𝒪[k] := by
  have hq := q.ne_zero
  rw [GlobalTheory.LatPair.Pair.mem_ker]
  constructor
  · intro h
    have hx := hlat x h.mem
    refine ⟨hx, ?_⟩
    have h0 := (mul_eq_zero.1 ((hval x hx).unique h)).resolve_right hc
    obtain ⟨m, hm⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff _).1 h0)
    have hm' : x l = ((q.1 : 𝒪[k]) : k) * (m : k) := congrArg Subtype.val hm
    rw [hm', GlobalTheory.LatPair.Unif.inv, inv_mul_cancel_left₀ hq]
    exact m.2
  · rintro ⟨hx, h⟩
    have h0 : residue 𝒪[k] ⟨x l, hx l⟩ = 0 := (residue_eq_zero_iff _).2 (q.mem_max_iff.2 ⟨⟨_, h⟩, Subtype.ext (by
      change x l = ((q.1 : 𝒪[k]) : k) * (q.inv * x l)
      rw [GlobalTheory.LatPair.Unif.inv, mul_inv_cancel_left₀ hq])⟩)
    have := hval x hx
    rwa [h0, zero_mul] at this

theorem row_eq_zero {S A L : HSp D} (o : OrthDec S A L) (hg : S.gram = 1) (ζ : Fin L.rank → D.host.E) (l : Fin S.rank)
    (a : D.host.E) (ha : a ≠ 0) (hv : ∀ r, vecB o ζ r = if r = l then a else 0) (j : Fin A.rank) : o.iA l j = 0 := by
  have h1 : star (vecB o ζ) ᵥ* o.iA = 0 := by
    have h := o.orth
    rw [hg, Matrix.mul_one] at h
    rw [vecB, Matrix.star_mulVec, Matrix.vecMul_vecMul, h, Matrix.vecMul_zero]
  have h2 := congrFun h1 j
  simp only [Matrix.vecMul, dotProduct, Pi.star_apply, hv, Pi.zero_apply] at h2
  rw [Finset.sum_eq_single l (fun b _ hb => by rw [if_neg hb, star_zero, zero_mul]) (fun h => absurd (Finset.mem_univ _) h),
    if_pos rfl] at h2
  exact (mul_eq_zero.1 h2).resolve_left (star_ne_zero.2 ha)

theorem ker_stdPair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (q : GlobalTheory.LatPair.Unif k) (S A L : HSp D) (o : OrthDec S A L), S.gram = 1 → ∀ (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (π : 𝓞 D.host.E) (πc : D.host.E), (∀ r : Fin S.rank, vecB o ζ r = if r.1 + 1 = S.rank then ((π : 𝓞 D.host.E) : D.host.E) else 0) → valuation k (p.pr (incA D ((π : 𝓞 D.host.E) : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → valuation k (p.pr (incA D πc)) = 1 → ∀ (LS : GlobalTheory.FinPl.Lat S) (LA : GlobalTheory.FinPl.Lat A), (∀ z, z ∈ LS ↔ z ∈ GlobalTheory.AdForm.intVec D S.rank) → (∃ LZ : GlobalTheory.FinPl.Lat L, GlobalTheory.FinPl.OrthAt o LS LA LZ p.v) → ∀ (β : GlobalTheory.FinPl.Frame p S (Fin S.rank)) (Q : GlobalTheory.LatPair.Pair k (Fin S.rank)), β.b = 1 → β.IsLat LS Q.lat → (∀ z ∈ LS, ∀ r : Fin S.rank, r.1 + 1 = S.rank → ∃ s : 𝒪[k], (s : k) = p.pr (incA D (πc * z r)) ∧ Q.HasVal (β.b' *ᵥ fun r' => p.pr (incA D (z r'))) (residue 𝒪[k] s)) → ∃ (γ : GlobalTheory.FinPl.Frame p A (Fin A.rank)) (γ₀ : GlobalTheory.FinPl.Frame p S (Fin A.rank ⊕ Fin 1)), GlobalTheory.FinPl.IsSumFrame o ζ γ γ₀ ∧ ∃ (Λ : Submodule 𝒪[k] (Fin A.rank → k)) (s : 𝓀[k]ˣ), γ.IsLat LA Λ ∧ (∀ y, y ∈ Q.ker ↔ (γ₀.b' * β.b) *ᵥ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer Λ) ∧ Q.HasVal ((β.b' * γ₀.b) *ᵥ (q.inv • GlobalTheory.LatPair.avec k (Fin A.rank) 1 1)) s := by
  intro D k _ _ _ _ p q S A L o hg ζ hζ π πc hvec hπ hπc LS LA hLS hOrth β Q hb hlat hQ
  obtain ⟨LZ, hLZ⟩ := hOrth
  have hN : S.rank = A.rank + 1 := by rw [← o.rank_add, hζ.1]
  obtain ⟨l, hl⟩ : ∃ l : Fin S.rank, ∀ r : Fin S.rank, r.1 + 1 = S.rank ↔ r = l :=
    ⟨⟨A.rank, by omega⟩, fun r => by rw [Fin.ext_iff]; dsimp only; omega⟩
  simp only [hl] at hvec hQ
  have hb' : β.b' = 1 := by have := β.b'b; rwa [hb, Matrix.mul_one] at this
  have hsingle : ∀ i : Fin S.rank,
      (fun r' => p.pr (incA D ((Pi.single i (1 : D.host.E) : Fin S.rank → D.host.E) r'))) = Pi.single i 1 := by
    intro i
    funext r'
    by_cases h : r' = i
    · subst h; rw [Pi.single_eq_same, Pi.single_eq_same, RingHom.map_one, RingHom.map_one]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, RingHom.map_zero, RingHom.map_zero]
  have hsLS : ∀ i : Fin S.rank, (Pi.single i (1 : D.host.E) : Fin S.rank → D.host.E) ∈ LS := by
    intro i
    rw [hLS]
    intro j
    by_cases h : j = i
    · subst h; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
  obtain ⟨s0, hs0, hv0⟩ := hQ _ (hsLS l) l rfl
  rw [hb', Matrix.one_mulVec, hsingle] at hv0
  rw [Pi.single_eq_same, mul_one] at hs0
  have hval : ∀ i : Fin S.rank, Q.HasVal (Pi.single i 1) (if i = l then residue 𝒪[k] s0 else 0) := by
    intro i
    split_ifs with h
    · subst h; exact hv0
    · obtain ⟨s, hs, hv⟩ := hQ _ (hsLS i) l rfl
      rw [hb', Matrix.one_mulVec, hsingle] at hv
      rw [Pi.single_eq_of_ne (Ne.symm h), mul_zero, RingHom.map_zero, RingHom.map_zero] at hs
      have h0 : s = 0 := Subtype.ext hs
      rwa [h0, RingHom.map_zero] at hv
  have hint := hasVal_of_single Q l _ hval
  have hres : ∀ s : 𝒪[k], valuation k (s : k) = 1 → residue 𝒪[k] s ≠ 0 := fun s hs =>
    (residue_ne_zero_iff_isUnit s).2 ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 hs)
  have hc : residue 𝒪[k] s0 ≠ 0 := hres s0 (by rw [hs0, hπc])
  have hlatV : ∀ x : Fin S.rank → k, x ∈ Q.lat ↔ (fun i => p.sec (x i)) ∈ latV S LS (· = p.v) := by
    intro x; rw [hlat x, hb, Matrix.one_mulVec]
  have hlatI : ∀ x : Fin S.rank → k, x ∈ Q.lat ↔ ∀ i, x i ∈ 𝒪[k] := by
    intro x
    refine ⟨fun h i => ?_, fun h => (hint x h).mem⟩
    have := pr_mem_of_mem_latV p (fun z hz => (hLS z).1 hz) ((hlatV x).1 h) i
    rwa [p.pr_sec] at this
  have hker := mem_ker_iff q Q l _ hc (fun x hx => (hlatI x).1 hx) hint
  have hq := q.ne_zero
  obtain ⟨πw, hπw⟩ : ∃ πw, p.pr (incA D ((π : 𝓞 D.host.E) : D.host.E)) = πw := ⟨_, rfl⟩
  have hqv : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := (Valuation.ne_zero_iff _).2 hq
  have hπ0 : ((π : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun h => hqv (by
    rw [← hπ, h, RingHom.map_zero, RingHom.map_zero, Valuation.map_zero])
  rw [hπw] at hπ
  have hu : valuation k (q.inv * πw) = 1 := by
    rw [Valuation.map_mul, GlobalTheory.LatPair.Unif.inv, map_inv₀, hπ, inv_mul_cancel₀ hqv]
  have huO : q.inv * πw ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hu.le
  have hmulu : ∀ t : k, t * (q.inv * πw) ∈ 𝒪[k] ↔ t ∈ 𝒪[k] := fun t => by
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, Valuation.map_mul, hu, mul_one]
  have hπO : πw ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (by
    rw [hπ]; exact (Valuation.mem_integer_iff _ _).1 q.1.2)
  have hrow := row_eq_zero o hg ζ l _ hπ0 hvec
  obtain ⟨γ, hγ⟩ := ((GlobalTheory.T.exists_splitPoint_frame_character D).2 k p).1 A (Fin A.rank) 1 1 (Matrix.mul_one _) (Matrix.mul_one _)
  obtain ⟨γ₀, hsum⟩ := GlobalTheory.FinPl.DblInh.exists_sumFrame o hζ γ β
  have hact : ∀ (w : Fin A.rank ⊕ Fin 1 → k) (i : Fin S.rank), (γ₀.b *ᵥ w) i =
      (o.jA.map p.pr *ᵥ (w ∘ Sum.inl)) i + if i = l then πw * w (Sum.inr 0) else 0 := by
    intro w i
    have h : γ₀.b = _ := hsum
    rw [h, hγ, Matrix.mul_one]
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr,
      replicateCol_apply, Fin.sum_univ_one, Function.comp_apply, ratV, hvec]
    congr 1
    split_ifs
    · rw [hπw]
    · rw [RingHom.map_zero, RingHom.map_zero, zero_mul]
  have hlast : ∀ a : Fin A.rank → k, (o.jA.map p.pr *ᵥ a) l = 0 := fun a => by
    change ∑ j, p.pr (incA D (o.iA l j)) * a j = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hrow, RingHom.map_zero, RingHom.map_zero, zero_mul]
  refine ⟨γ, γ₀, hsum, Q.lat.comap ((Matrix.mulVecLin (o.jA.map p.pr)).restrictScalars 𝒪[k]),
    Units.mk0 _ (mul_ne_zero (hres ⟨_, huO⟩ hu) hc), fun a => ?_, fun y => ?_, ?_⟩
  · change o.jA.map p.pr *ᵥ a ∈ Q.lat ↔ _
    have h := rat_mulVec_sec p o.iA a
    change o.jA *ᵥ _ = fun i => p.sec ((o.jA.map p.pr *ᵥ a) i) at h
    rw [hlatV, ← h, hLZ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.pA_jA, o.pB_jA, Matrix.one_mulVec,
      Matrix.zero_mulVec, hγ, Matrix.one_mulVec]
    exact and_iff_left (zero_mem _)
  · rw [hb, Matrix.mul_one, GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer, hker]
    obtain ⟨w, hw⟩ : ∃ w, γ₀.b' *ᵥ y = w := ⟨_, rfl⟩
    have hy : y = γ₀.b *ᵥ w := by rw [← hw, Matrix.mulVec_mulVec, γ₀.bb', Matrix.one_mulVec]
    rw [hw]
    change _ ↔ o.jA.map p.pr *ᵥ (w ∘ Sum.inl) ∈ Q.lat ∧ _
    have hyl : y l = πw * w (Sum.inr 0) := by rw [hy, hact, hlast, if_pos rfl, zero_add]
    have hyi : ∀ i, i ≠ l → y i = (o.jA.map p.pr *ᵥ (w ∘ Sum.inl)) i := fun i hi => by
      rw [hy, hact, if_neg hi, add_zero]
    rw [hlatI, hyl, ← mul_assoc, mul_comm _ (w (Sum.inr 0)), hmulu]
    refine and_congr_left fun ht => forall_congr' fun i => ?_
    by_cases hi : i = l
    · rw [hi, hyl, hlast]
      exact iff_of_true (mul_mem hπO ht) (zero_mem _)
    · rw [hyi i hi]
  · have hx : ∀ i, ((β.b' * γ₀.b) *ᵥ (q.inv • GlobalTheory.LatPair.avec k (Fin A.rank) 1 1)) i =
        if i = l then q.inv * πw else 0 := fun i => by
      have h0 : (q.inv • GlobalTheory.LatPair.avec k (Fin A.rank) 1 1) ∘ Sum.inl = 0 := by
        funext j; simp [GlobalTheory.LatPair.avec]
      have h1 : (q.inv • GlobalTheory.LatPair.avec k (Fin A.rank) 1 1) (Sum.inr 0) = q.inv := by
        simp [GlobalTheory.LatPair.avec]
      rw [hb', Matrix.one_mul, hact, h0, h1, Matrix.mulVec_zero, Pi.zero_apply, zero_add, mul_comm]
    have hO : ∀ i, ((β.b' * γ₀.b) *ᵥ (q.inv • GlobalTheory.LatPair.avec k (Fin A.rank) 1 1)) i ∈ 𝒪[k] := fun i => by
      rw [hx]
      split_ifs
      · exact huO
      · exact zero_mem _
    have h := hint _ hO
    have e : (⟨_, hO l⟩ : 𝒪[k]) = ⟨_, huO⟩ := Subtype.ext ((hx l).trans (if_pos rfl))
    rw [e] at h
    exact h

end GlobalTheory.StdPairTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RdEmbEvz
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem rd_emb_evz : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ θ, IsInfFam θ → ∀ emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) emb → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ β, ((∃ n : ℕ, 0 < n ∧ ∀ κ, K.lev.chi κ ^ n = 1) → ∀ h (κ : K.lev.U), GlobalTheory.Core.Rk.Top.HasMat h κ.1 → ∃ hU : emb h ∈ A.U B.R.m β, A.chi B.R.m β ⟨emb h, hU⟩ = K.lev.chi κ ∧ ‖((K.lev.chi κ : ℂˣ) : ℂ)‖ = 1) ∧ ∀ φ ∈ (I.fm l u a).Fi B.R.m, ∀ c h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 → ∀ y, A.rd θ B.R.m le_rfl β φ y (emb h) = (I.per l u a).evz φ c y := by
  intro B X I hI hP l Z u a Ch₀ A hA θ hθ emb hemb bad K hK β
  refine ⟨fun hfin => GlobalTheory.AdForm.LevChiTop.emb_mem_chi I hI hP l Z u a Ch₀ A hA emb hemb bad K hK hfin β, ?_⟩
  intro φ hφ c h hh y
  have hβ := GlobalTheory.AdForm.TwDat.Is.chOf_top_eq I hI hP l Z u a Ch₀ A hA ((I.perIn u a).tilC c) β
  subst hβ
  obtain ⟨γ, hγ, k, hk, κ, he, hv⟩ := GlobalTheory.AdForm.TwDat.Is.evz_decomp I hI hP l Z u a Ch₀ A hA θ hθ emb hemb bad K hK c h hh
  obtain ⟨y', hy', hval⟩ := hv φ hφ y
  rw [he, (GlobalTheory.AdForm.rd_charts I hI hP l Z u a Ch₀ A hA θ hθ B.R.m le_rfl φ hφ).2 _ y γ hγ ⟨(I.perIn u a).tilC c, rfl⟩ k hk κ y' hy']
  exact hval

end GlobalTheory.AdForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntegralThetaLiftDefiniteFormNeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realIntegral_thetaLift_definiteForm_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t (y : (R.HV i t).H), y ≠ 0 → ∀ m : Measure (GA D (Vc D i)), m.IsHaarMeasure → ∃ (l : (R.cV i).W →ₗ[ℂ] ℂ) (P : PolF D (Wc D i).rank (Vc D i).rank), ∀ ν 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) ν 𝓕 → ∀ mR : Measure (GinfC (Vc D i)), mR.IsHaarMeasure → ∫ b : GinfC (Vc D i), GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t P) (R.ptP i t P) b * GlobalTheory.Core.Rk.IP.rcoef m (fun g => l (R.extV i t y g)) (fun g => l (R.extV i t y g)) b ∂mR ≠ 0 := by
  first | exact @GlobalTheory.Core.Rk.RealOcc.real_ne | exact GlobalTheory.Core.Rk.RealOcc.real_ne | (intros; apply GlobalTheory.Core.Rk.RealOcc.real_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTupleTwistedChainOfScalarHypotheses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

theorem GlobalTheory.ChainTw.rChain_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ h : RangeX R, RChain R h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG h
  exact GlobalTheory.ChainTw.RModel.rChain R hG.core.lev hG.core.models hG.core.chain h
end

