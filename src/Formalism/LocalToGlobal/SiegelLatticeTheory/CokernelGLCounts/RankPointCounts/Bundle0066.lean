import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModelKSN
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0029
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0005
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0063
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0039

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModelKSD
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.FourierDecayAlt Formalism.L2.SG.DataInst
open Classical ValuativeRel
open scoped nonZeroDivisors

namespace Formalism.L2.SG.Pf.LMK

variable {D : Formalism.BasicNotions.D7}

theorem modK_alg (Z : Formalism.L2.SG.TermLoc.LocDat D) (p : PlF D) [IsNonarchimedeanLocalField (D.s.atP p).Fp]
    {z : (D.s.atP p).Fp} (hz : z ≠ 0) :
    A5.modK (Z.M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z) = PI.ProdFormulaE.modF (D.s.atP p).Fp z ^ 2 := by
  have := (D.s.atP p).borel
  have := (D.s.atP p).free
  have : Module.Finite (D.s.atP p).Fp (D.s.atP p).Ep :=
    Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
  have := (D.s.atP p).top
  have hOK := (Z.agree p).1
  have := hOK.haar.haar
  have hu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep z) := (isUnit_iff_ne_zero.2 hz).map _
  have h1 := Formalism.MainNotions.LocalModelPeriodLattices.modK_of_OK (Z.M p) hOK hu.unit
  rw [IsUnit.unit_spec] at h1
  rw [← h1]
  unfold Loc.Model.modK
  rw [PI.ProdFormulaE.HaarAlgP.haarScaling (D.s.atP p).Fp (D.s.atP p).Ep (Z.M p).mu _ hu _, hOK.haar.volR, mul_one,
    Algebra.norm_algebraMap, (D.s.atP p).rank, ENNReal.toReal_ofReal (PI.ProdFormulaE.HaarBox.modF_nonneg' _), pow_two,
    PI.ProdFormulaE.modF_mul]
  ring

theorem delta_unit (Z : Formalism.L2.SG.TermLoc.LocDat D) (p : PlF D) (x0 : 𝓞 D.host.F)
    (hx0 : x0 ∈ differentIdeal ℤ (𝓞 D.host.F))
    (hv : p.intValuation x0 = WithZero.exp (-(Formalism.L2.SG.Pf.NcVal.mDiff D.host.F p : ℤ))) :
    (D.s.atP p).ιF (x0 : D.host.F) ≠ 0 ∧
      Z.δ p * ((D.s.atP p).ιF (x0 : D.host.F))⁻¹ ∈ 𝒪[(D.s.atP p).Fp] ∧
      (Z.δ p * ((D.s.atP p).ιF (x0 : D.host.F))⁻¹)⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := by
  set A := D.s.atP p with hAdef
  have hδ : Z.δ p ≠ 0 := (Z.agree p).2.1
  have hx0ne : x0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hι0 : A.ιF (x0 : D.host.F) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ A.ιF.injective]
    exact_mod_cast hx0ne
  have hvx0 : p.valuation D.host.F (x0 : D.host.F) = WithZero.exp (-(Formalism.L2.SG.Pf.NcVal.mDiff D.host.F p : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact hv

  set J : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F)
    with hJ
  have hJ0 : J ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have hdd : ((differentIdeal ℤ (𝓞 D.host.F) : Ideal (𝓞 D.host.F)) : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F) = J⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ D.host.F (𝓞 D.host.F)
  have hmemJ : ∀ y : D.host.F, y ∈ J ↔ ∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (y * a) = n := by
    intro y
    rw [hJ, FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 D.host.F)⁰ D.host.F) ≠ 0)]
    constructor
    · intro h a
      obtain ⟨n, hn⟩ := h (algebraMap _ _ a) ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
      exact ⟨n, by rw [Algebra.traceForm_apply] at hn; rw [← hn]; rfl⟩
    · intro h b hb
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
      obtain ⟨n, hn⟩ := h a
      exact ⟨n, by rw [Algebra.traceForm_apply, hn]; rfl⟩
  have hx0J : (x0 : D.host.F) ∈ J⁻¹ := by
    rw [← hdd]; exact (FractionalIdeal.mem_coeIdeal _).2 ⟨x0, hx0, rfl⟩
  have hmulO : ∀ y ∈ J, ∀ b ∈ J⁻¹, p.valuation D.host.F (y * b) ≤ 1 := by
    intro y hy b hb
    have h1 : y * b ∈ J * J⁻¹ := FractionalIdeal.mul_mem_mul hy hb
    rw [mul_inv_cancel₀ hJ0] at h1
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [← ho]
    exact p.valuation_le_one o

  obtain ⟨t, htr, hne, hu1, hu2⟩ := PI.CntNotIntW.locDiff_of PI.CntNotIntW.trace_dual_lattice
    (PI.CntNotIntW.dualApprox_of PI.CntNotIntW.small_powers_bound PI.CntNotIntW.tensorLiftSurjective)
    PI.CntNotIntW.small_powers_bound D Z.δ Z.M Z.agree p
  have htJ : t ∈ J := (hmemJ t).2 htr
  have ht0 : A.ιF t ≠ 0 := right_ne_zero_of_mul hne
  have htx0 : A.ιF (t * (x0 : D.host.F)) ∈ 𝒪[A.Fp] := by
    rw [Formalism.MainNotions.BridgeLemma.mem_OF_iff]
    exact hmulO t htJ _ hx0J

  obtain ⟨y, hy, a, ha, hya⟩ : ∃ y ∈ J, ∃ b ∈ J⁻¹, ¬ valuation A.Fp (A.ιF (y * b)) < 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : (1 : D.host.F) ∈ J * J⁻¹ := by
      rw [mul_inv_cancel₀ hJ0]; exact FractionalIdeal.one_mem_one _
    have h2 : valuation A.Fp (A.ιF 1) < 1 := by
      refine FractionalIdeal.mul_induction_on h1 (fun y hy b hb => hcon y hy b hb) ?_
      intro u v hu hv
      rw [map_add]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hu hv)
    rw [map_one, map_one] at h2
    exact lt_irrefl _ h2

  have hyδ : A.ιF y * Z.δ p ∈ 𝒪[A.Fp] := by
    have := A.lf
    have := A.ellPrime
    have hz := Formalism.L2.SG.Pf.dualLoc_holds D.host.F p A.Fp A.qlCont A.qlFin A.ιF A.dense A.val y ((hmemJ y).1 hy)
    exact Formalism.L2.SG.Pf.LocFacts.lf_dual_le p Z _ hz

  have ha0 : valuation A.Fp (A.ιF a) ≤ valuation A.Fp (A.ιF (x0 : D.host.F)) := by
    rw [Formalism.MainNotions.BridgeLemma.val_iff, hvx0]
    rw [← hdd] at ha
    obtain ⟨a', ha', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact Formalism.L2.SG.Pf.NcVal.intValuation_le_of_mem_different p ha'
  have hyx0 : 1 ≤ valuation A.Fp (A.ιF (y * (x0 : D.host.F))) := by
    have h1 : 1 ≤ valuation A.Fp (A.ιF (y * a)) := not_lt.1 hya
    rw [map_mul, map_mul] at h1 ⊢
    exact le_trans h1 (mul_le_mul' le_rfl ha0)
  have hyx0ne : A.ιF (y * (x0 : D.host.F)) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hyx0; exact absurd hyx0 (not_le.2 zero_lt_one)
  refine ⟨hι0, ?_, ?_⟩
  · have e : Z.δ p * (A.ιF (x0 : D.host.F))⁻¹ = (A.ιF y * Z.δ p) * (A.ιF (y * (x0 : D.host.F)))⁻¹ := by
      rw [map_mul]
      have hy0 : A.ιF y ≠ 0 := by intro h0; rw [map_mul, h0, zero_mul] at hyx0ne; exact hyx0ne rfl
      field_simp
    rw [e]
    refine mul_mem hyδ ?_
    rw [Valuation.mem_integer_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hyx0
  · have e : (Z.δ p * (A.ιF (x0 : D.host.F))⁻¹)⁻¹ = A.ιF (t * (x0 : D.host.F)) * (Z.δ p * A.ιF t)⁻¹ := by
      rw [map_mul]
      field_simp
    rw [e]
    exact mul_mem htx0 hu2

theorem modK_delta (Z : Formalism.L2.SG.TermLoc.LocDat D) (p : PlF D) :
    A5.modK (Z.M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)) =
      (((Ideal.absNorm (p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))) : ℕ) : ℝ)⁻¹) ^ 2 := by
  have := (D.s.atP p).lf
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (Z.M p) (Z.agree p).1
  have hd := Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK (Z.M p) (Z.agree p).1
  obtain ⟨x0, hx0, hv⟩ := Formalism.L2.SG.Pf.NcVal.exists_mem_different_intValuation_eq (F := D.host.F) p
  obtain ⟨hι0, hu1, hu2⟩ := delta_unit Z p x0 hx0 hv
  set u := Z.δ p * ((D.s.atP p).ιF (x0 : D.host.F))⁻¹ with hudef
  have hu0 : u ≠ 0 := mul_ne_zero (Z.agree p).2.1 (inv_ne_zero hι0)
  have hmu : A5.modK (Z.M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep u) = 1 :=
    Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.modK_unitR (alg_mem_R (M := Z.M) p hu1) (alg_mem_R (M := Z.M) p hu2)
      (by rw [← map_mul, mul_inv_cancel₀ hu0, map_one])
  have e : Z.δ p = u * (D.s.atP p).ιF (x0 : D.host.F) := by rw [hudef, mul_assoc, inv_mul_cancel₀ hι0, mul_one]
  have hx0ne : x0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  rw [e, map_mul, Formalism.FourierDecayAlt.P.A5x5.modK_mul' hd ((isUnit_iff_ne_zero.2 hu0).map _) ((isUnit_iff_ne_zero.2 hι0).map _),
    hmu, one_mul, modK_alg Z p hι0, PI.ProdFormulaE.modF_localization_eq_adicAbv]

  have h3 := NumberField.HeightOneSpectrum.embedding_mul_absNorm D.host.F p hx0ne
  rw [NumberField.FinitePlace.norm_embedding] at h3
  have hcount : (Associates.mk p.asIdeal).count (Associates.mk (Ideal.span {x0})).factors =
      Formalism.L2.SG.Pf.NcVal.mDiff D.host.F p := by
    rw [HeightOneSpectrum.intValuation_if_neg p hx0ne] at hv
    have := WithZero.exp_injective hv
    omega
  have hmp : p.maxPowDividing (Ideal.span {x0}) = p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F)) := by
    unfold HeightOneSpectrum.maxPowDividing
    rw [hcount]
  rw [hmp] at h3
  have hN : ((Ideal.absNorm (p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))) : ℕ) : ℝ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h3; exact zero_ne_one h3
  have h4 : (NumberField.HeightOneSpectrum.adicAbv D.host.F p) (x0 : D.host.F) =
      ((Ideal.absNorm (p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))) : ℕ) : ℝ)⁻¹ :=
    eq_inv_of_mul_eq_one_left h3
  rw [show ((x0 : D.host.F)) = algebraMap (𝓞 D.host.F) D.host.F x0 from rfl] at h4 ⊢
  rw [h4]

theorem prod_maxPow (I : Ideal (𝓞 D.host.F)) (hI : I ≠ 0) :
    (Function.mulSupport fun p : PlF D =>
      (((Ideal.absNorm (p.maxPowDividing I) : ℕ) : ℝ)⁻¹) ^ 2).Finite ∧
    ∏ᶠ p : PlF D, (((Ideal.absNorm (p.maxPowDividing I) : ℕ) : ℝ)⁻¹) ^ 2 = (((Ideal.absNorm I : ℕ) : ℝ)⁻¹) ^ 2 := by
  let φ : Ideal (𝓞 D.host.F) →* ℝ := (powMonoidHom 2).comp (invMonoidHom.comp
    ((Nat.castRingHom ℝ).toMonoidHom.comp (Ideal.absNorm : Ideal (𝓞 D.host.F) →*₀ ℕ).toMonoidHom))
  have hφ : ∀ J, φ J = (((Ideal.absNorm J : ℕ) : ℝ)⁻¹) ^ 2 := fun J => rfl
  have hfin := Ideal.finite_mulSupport hI
  have hsub : (Function.mulSupport fun p : PlF D => φ (p.maxPowDividing I)) ⊆
      Function.mulSupport fun p : PlF D => p.maxPowDividing I :=
    Function.mulSupport_comp_subset (map_one φ) _
  refine ⟨?_, ?_⟩
  · simpa only [hφ] using hfin.subset hsub
  · have h1 := (MonoidHom.map_finprod φ hfin).symm
    simp only [hφ] at h1
    rw [h1, Ideal.finprod_heightOneSpectrum_factorization hI]

theorem deltaProd_holds (D : Formalism.BasicNotions.D7) : DeltaProd D := by
  intro δ M hA
  let Z : Formalism.L2.SG.TermLoc.LocDat D := ⟨δ, M, hA⟩
  have hI : differentIdeal ℤ (𝓞 D.host.F) ≠ 0 := differentIdeal_ne_bot
  have hfun : (fun p => A5.modK (M p).R (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))) =
      fun p : PlF D => (((Ideal.absNorm (p.maxPowDividing (differentIdeal ℤ (𝓞 D.host.F))) : ℕ) : ℝ)⁻¹) ^ 2 :=
    funext fun p => modK_delta Z p
  obtain ⟨hfin, hval⟩ := prod_maxPow (D := D) _ hI
  rw [hfun]
  refine ⟨hfin, ?_⟩
  rw [hval, absNorm_differentIdeal D.host.F (𝓞 D.host.F)]
  have hf : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    have := Formalism.MainNotions.LocalModelPeriodLattices.cmE D
    rw [(Formalism.FourierDecayAlt.P.degreeFacts_statement D.host.E).1, Formalism.MainNotions.LocalModelPeriodLattices.deg_eq]
  have hrd : D.host.rdE ^ (2 * D.R.f) = |(NumberField.discr D.host.E : ℝ)| := by
    unfold Formalism.BasicNotions.Host.rdE
    rw [← hf, one_div]
    exact Real.rpow_inv_natCast_pow (abs_nonneg _) Module.finrank_pos.ne'
  rw [hrd, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq, Nat.cast_natAbs, Int.cast_abs]
  push_cast
  rw [abs_pow, inv_pow]

end Formalism.L2.SG.Pf.LMK

namespace Formalism.L2.SG.Pf

theorem localModelS_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.DataCut.LocalModelS D := localModelS_of_delta (LMK.deltaProd_holds D)

theorem localModelAt_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.DataInst.LocalModelAt D :=
  Formalism.L2.SG.DataCut.localModelAt_of_KS (localModelK_holds D) (localModelS_holds D)

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqAna
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.Pf.MainEqAna

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AnaAtG (CSt CB : ℝ) (C1 C0n A : ℕ) {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    {P : Type} [Fintype P] (B : S3.MassData P) (Ire : ℝ) : Prop :=
  ∃ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (cSt e1 : ℝ),
    Formalism.L2.SG.RealObj.NuQOK X u u νL ∧ Formalism.L2.SG.RealObj.NuQOK X u u νB ∧
    0 ≤ cSt ∧ cSt ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) ∧ 0 ≤ e1 ∧ e1 ≤ 2 ∧
    AmpVanishG Y u νL ∧
    LocalInputG (genT (Y.tO u u)) (NOfG Y u νL νB ng) C1 C0n ∧
    PN.GenMassInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) e1 ∧
    PN.MeasureInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) cSt ∧
    PN.PointSumInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) (A * (D.R.rS + 1) ^ 2)
      (Real.exp (CB * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f * Real.log large₂.sc.b) * Ire)

def StepAnalyticCG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∀ A : ℕ, ∃ CB CSt : ℝ, 0 ≤ CB ∧ 0 ≤ CSt ∧
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
        AnaAtG CSt CB C1 C0n A large₂ Y u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Ire

section Pin

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

private theorem Jw_sc_eq_smul {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (s : X.B.I.Ginf → NNReal)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (w : Point D.host.E (D.R.rS + 1)) :
    Jw Y u u (sc s ν) w = ((s (RealObj.gamW X u u w) : NNReal) : ℝ) • Jw Y u u ν w := by
  simp only [Jw, OO, sc, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal]
  rw [smul_comm]

theorem ampVanishG_sc (s : X.B.I.Ginf → NNReal) (hs : ∀ γ, 0 < s γ) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (h : AmpVanishG Y u ν) : AmpVanishG Y u (sc s ν) := by
  intro c γ ν' hJ
  refine h c γ ν' ?_
  unfold J2of at hJ ⊢
  split_ifs at hJ ⊢ with hc
  · rw [Jw_sc_eq_smul, LinearMap.map_smul_of_tower, norm_smul, mul_pow] at hJ
    rcases mul_eq_zero.mp hJ with h1 | h1
    · exfalso
      have hp : (0 : ℝ) < ((s (RealObj.gamW X u u hc.choose) : NNReal) : ℝ) := hs _
      have : (0 : ℝ) < ‖((s (RealObj.gamW X u u hc.choose) : NNReal) : ℝ)‖ ^ 2 :=
        pow_pos (norm_pos_iff.mpr hp.ne') 2
      linarith
    · exact h1
  · rfl

theorem measureInputG_sc (s : X.B.I.Ginf → NNReal) (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (c : ℝ)
    (hs : ∀ γ, (s γ : ℝ) ^ 2 ≤ c) (ng : PN.Pts D.host.E D.R.rS → ℝ) :
    PN.MeasureInput (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν ng) c := by
  intro γ _
  simp only [NOfG]
  unfold J2of
  split_ifs with hc
  · rw [Jw_sc_eq_smul, LinearMap.map_smul_of_tower, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact ⟨by positivity, mul_le_mul_of_nonneg_right (hs _) (by positivity)⟩
  · simp

theorem ampVanishG_of_term (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (h : ∀ t ∈ (Y.tO u u).genSet, J2of Y u u ν (ptPN t) = 0 → (Y.tO u u).vec t = 0) : AmpVanishG Y u ν := by
  intro c γ ν' hJ
  unfold grpGC
  refine (tsum_congr fun t => ?_).trans tsum_zero
  by_cases ht : t ∈ (Y.tO u u).genSet ∩ {t | clsG Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν'}
  · rw [Set.indicator_of_mem ht]
    exact h t ht.1 (by rw [ht.2.2.1]; exact hJ)
  · simp [Set.indicator, ht]

end Pin

def StepTermVanishG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ ν, Pinned X u u ν → ∀ t ∈ (Y.tO u u).genSet, J2of Y u u ν (ptPN t) = 0 → (Y.tO u u).vec t = 0

def StepLocGenPinnedG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ (s : X.B.I.Ginf → NNReal) (ng : PN.Pts D.host.E D.R.rS → ℝ) (e1 : ℝ),
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧ 0 ≤ e1 ∧ e1 ≤ 2 ∧
        LocalInputG (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν ng) C1 C0n ∧
        PN.GenMassInput (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν ng)
          (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA) e1

def StepThmBPinnedG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∀ A : ℕ, ∃ CB : ℝ, 0 ≤ CB ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν → ∀ (νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.PointSumInput (genT (Y.tO u u)) (NOfG Y u νL ν ng) (A * (D.R.rS + 1) ^ 2)
          (Real.exp (CB * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f * Real.log large₂.sc.b) * Ire)

end Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqAna

theorem stepAnalyticG_of (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hA : StepAnalyticCG) : StepAnalyticG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0
  obtain ⟨k₀, l₀, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨m₀, n₀, hT2⟩ := hTi Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, CSt, h1, h2, a₀, b₀, hA2⟩ := hA1 A
  refine ⟨CB, CSt, h1, h2, max a₀ (max k₀ m₀), max b₀ (max l₀ n₀), fun C' Cl e1 e2 D large₂ X Y u hc => ?_⟩
  obtain ⟨hb, X0, ψ, hT⟩ := hT2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc hb X0 ψ hT
  have hBk' := massDataValid_unscale (kapU_pos D) hBk
  obtain ⟨νL, νB, ng, cSt, e, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
    hA2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u hc hb X0 ψ hT sd C Th
      F0 what₂ vR Q i0 i0' νq (Irat * kapU D) (Ire * kapU D) hBk'
  exact ⟨_, inferInstance, _, Irat * kapU D, Ire * kapU D, νL, νB, ng, cSt, e, hBk', a1, a2, a3, a4, a5, a6, a7,
    a8, a9, a10, a11⟩

private theorem nuQOK_sc_of_eq_one_on_regX {D : D7} {X : HidaSetting D} (u : D.what₂.Word) (s : X.B.I.Ginf → NNReal)
    (hs : ∀ γ, 0 < s γ) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hreg : ∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) (h : Formalism.L2.SG.RealObj.NuQOK X u u ν) :
    Formalism.L2.SG.RealObj.NuQOK X u u (sc s ν) := by
  intro γ
  obtain ⟨h1, μR, hH, hQ⟩ := h γ
  refine ⟨fun hr => ?_, (s γ)⁻¹ • μR, ?_, ?_⟩
  · simp only [sc, hreg γ hr, ENNReal.coe_one, one_smul]
    exact h1 hr
  · obtain ⟨hσ, h0, hc, hm⟩ := hH
    refine ⟨inferInstance, smul_ne_zero (inv_ne_zero (hs γ).ne') h0, ?_, ?_⟩
    · simp [hc]
    · intro g hg
      rw [Measure.map_smul, hm g hg]
  · intro f hf
    rw [hQ f hf]
    simp only [sc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul,
      mul_inv_cancel₀ (hs γ).ne', ENNReal.coe_one, one_mul]

theorem stepAnalyticCG_of_pin_vanish_loc_thm (hE : StepPinExists) (hV : StepTermVanishG) (hL : StepLocGenPinnedG)
    (hB : StepThmBPinnedG) : StepAnalyticCG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨aE, bE, hE'⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨aV, bV, hV'⟩ := hV Cg cb Cw cT CT C0
  obtain ⟨C1, C0n, CSt, hCSt, aL, bL, hL'⟩ := hL Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, hCB, aT, bT, hT'⟩ := hB Cg cb Cw cT CT C0 A
  refine ⟨CB, CSt, hCB, hCSt, max (max aE aV) (max aL aT), max (max bE bV) (max bL bT), ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hctx hb X0 ψ htie sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok
  have hE1 : aE ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC'
  have hE2 : bE ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCl
  have hV1 : aV ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC'
  have hV2 : bV ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCl
  have hL1 : aL ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC'
  have hL2 : bL ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hT1 : aT ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC'
  have hT2 : bT ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl
  obtain ⟨ν, hν⟩ := hE' C' Cl hE1 hE2 D large₂ X Y u u hctx
  obtain ⟨s, ng, e1, hreg, hpos, hsq, he0, he2, hloc, hmass⟩ :=
    hL' C' Cl hL1 hL2 D large₂ X Y u hctx hb X0 ψ htie sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hν
  have hpt := hT' C' Cl hT1 hT2 D large₂ X Y u hctx hb X0 ψ htie sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hok ν hν
    (sc s ν) ng
  have hvan := hV' C' Cl hV1 hV2 D large₂ X Y u hctx ν hν
  refine ⟨sc s ν, ν, ng, large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f), e1,
    nuQOK_sc_of_eq_one_on_regX u s hpos ν hreg hν.1, hν.1, le_trans (sq_nonneg _) (hsq 1), le_rfl, he0, he2,
    ampVanishG_sc Y u s hpos ν (ampVanishG_of_term Y u ν hvan), hloc, hmass,
    measureInputG_sc Y u s ν _ hsq ng, hpt⟩

theorem rowMainEqC_of_pinned (hCh : PN.NGChain) (hC : StepClassG) (hN : StepNormalsG) (hP : StepPointsG)
    (hO : StepNormOneG) (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : StepTermVanishG)
    (hL : StepLocGenPinnedG) (hT : StepThmBPinnedG) : RowMainEqC :=
  rowMainEqC_of_steps2 hCh hC hN hP hO (stepAnalyticG_of hTi hB (stepAnalyticCG_of_pin_vanish_loc_thm hE hV hL hT))

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqPoints
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.NGCut.PtPf
  Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.Pf.MainEqPoints

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepPointsG_of
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepPointsG := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u _ νL νB ng γ hγ => ?_⟩
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := hγ
  have hG : t.toTerm.G ≠ 0 := by
    intro h
    apply ht.1
    show Gt t = 0
    have h' : t.G = 0 := h
    simp [Gt, h']
  have hrel : t.toTerm.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := hOV D X Y u u t hr
    show vec (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨w, hw⟩ := hAt D X Y u u t.toTerm hG hrel
  have hat := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩
  obtain ⟨F', ⟨hP, -⟩, -, hcell⟩ := hat
  have hrow := (Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam := frame_mem _ hrow.2.1.2.2.1.1 hrow.2.2
  have hF' : ∀ b, frame F' b ∈ t.toTerm.lam := frame_mem _ hP.1.1 hP.2.2.2
  have hE := blockEndMinors_of_cell _ (zhatOM_isIntegral _ _ hrow.2.1.2.1 hF hF') _ hcell
  rw [← hpt]
  exact hE

open Formalism.L2.SG.TermOp.Vanish in
theorem stepPointsG_of_leaves (hA : AvgCore) (hU : GinfUnimod) (hN : NLamNinf) (hC : ChiTrivialC) (hG : PsiInfChar)
    (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC) (h4 : NonRelCharC)
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepPointsG := by
  refine stepPointsG_of ?_ hAt
  intro D X Y u u'
  unfold Formalism.L2.SG.TermOp.KExpCut.OOVanish
  intro t ht
  exact ooVanish_of hA hU hN hC hG h1 h2 h3 h4 Y t ht

end Formalism.L2.SG.Pf.MainEqPoints
end
end

