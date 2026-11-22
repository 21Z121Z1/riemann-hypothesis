import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import GroundTheory.GlobalFields.Adele.Compact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0340
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0233
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0596
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0574
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryFactorFiniteSetOfPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.PlaceCut

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem glue_mul {e : R} (he : e * e = e) (a b c d : Matrix ι ι A) :
    (e • a + (1 - e) • b) * (e • c + (1 - e) • d) = e • (a * c) + (1 - e) • (b * d) := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, h2, mul_one, sub_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, h1, h2, h3,
    zero_smul, add_zero, zero_add]

omit [Fintype ι] [DecidableEq ι] in
theorem glue_self (e : R) (a : Matrix ι ι A) : e • a + (1 - e) • a = a := by
  rw [← add_smul, add_sub_cancel, one_smul]

theorem exists_glue (c : A →ₐ[R] A) (J : Matrix ι ι A) {e : R} (he : e * e = e) (g h : GlobalTheory.WeilM.UG c J) :
    ∃ p : GlobalTheory.WeilM.UG c J, (p.1.1 : Matrix ι ι A) = e • g.1.1 + (1 - e) • h.1.1 ∧
      ((p⁻¹).1.1 : Matrix ι ι A) = e • (g⁻¹).1.1 + (1 - e) • (h⁻¹).1.1 := by
  let q : GL ι A :=
    { val := e • g.1.1 + (1 - e) • h.1.1
      inv := e • g.1.2 + (1 - e) • h.1.2
      val_inv := by rw [glue_mul he, g.1.3, h.1.3, glue_self]
      inv_val := by rw [glue_mul he, g.1.4, h.1.4, glue_self] }
  have hq : q ∈ GlobalTheory.WeilM.UG c J := by
    have hg : (g.1.1)ᵀ * J * (g.1.1).map c = J := g.2
    have hh : (h.1.1)ᵀ * J * (h.1.1).map c = J := h.2
    show (e • g.1.1 + (1 - e) • h.1.1)ᵀ * J * (e • g.1.1 + (1 - e) • h.1.1).map c = J
    have m : (e • g.1.1 + (1 - e) • h.1.1).map c = e • (g.1.1).map c + (1 - e) • (h.1.1).map c := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add, map_smul]
    rw [m, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul]
    have k := glue_mul he (g.1.1)ᵀ (h.1.1)ᵀ J J
    rw [glue_self] at k
    rw [k, glue_mul he, hg, hh, glue_self]
  exact ⟨⟨q, hq⟩, rfl, rfl⟩

end Alg

theorem exists_idem {F : Type} [Field F] [NumberField F] (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) :
    ∃ e : AF F, e * e = e ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F e = 0 ∧ (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w e = 1) ∧
      (∀ w ∉ S, GlobalTheory.AdelicU.evFin F w e = 0) ∧
      ∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u * e = 0 := by
  classical
  let b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F := ∑ v ∈ S, GlobalTheory.AdelicU.singleFin v 1
  have hb1 : ∀ w ∈ S, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w b = 1 := by
    intro w hw
    rw [map_sum, Finset.sum_eq_single_of_mem w hw, GlobalTheory.AdelicU.evalV_singleFin_self]
    intro v _ hv
    exact GlobalTheory.AdelicU.evalV_singleFin_ne hv.symm 1
  have hb0 : ∀ w ∉ S, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w b = 0 := by
    intro w hw
    rw [map_sum]
    refine Finset.sum_eq_zero fun v hv => GlobalTheory.AdelicU.evalV_singleFin_ne ?_ 1
    rintro rfl
    exact hw hv
  refine ⟨((0 : Ainf F), b), ?_, ?_, hb1, hb0, ?_⟩
  · refine Prod.ext (by change (0 : Ainf F) * 0 = 0; exact mul_zero _) ?_
    change b * b = b
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w ∈ S
    · rw [hb1 w hw, mul_one]
    · rw [hb0 w hw, mul_zero]
  · show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  · intro u hu
    refine Prod.ext (by change u.1 * 0 = 0; exact mul_zero _) ?_
    change u.2 * b = 0
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul, map_zero]
    by_cases hw : w ∈ S
    · have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w u.2 = 0 := hu w hw
      rw [this, zero_mul]
    · rw [hb0 w hw, mul_zero]

theorem exists_cut : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)),
    ∃ gS k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J, g = gS * k ∧
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) ∧
      (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
        u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1)) ∧
      (∀ w ∉ S, ∀ z ∈ GlobalTheory.InertSph.latAt X w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z) := by
  intro F E _ _ _ _ _ σ n X g S
  obtain ⟨e, he, heI, he1, he0, heu⟩ := exists_idem S
  obtain ⟨gS, hS, -⟩ := exists_glue (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) he g 1
  obtain ⟨k, hk, hk'⟩ := exists_glue (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) he 1 g
  have hS2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS = e • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g + (1 - e) • 1 := hS
  have hk2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k = e • 1 + (1 - e) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g := hk
  have hk3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ = e • 1 + (1 - e) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ := by
    rw [inv_one] at hk'
    exact hk'
  have hoff : ∀ (u : AF F) (M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), u * e = 0 →
      u • (e • (1 : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) + (1 - e) • M) = u • M := by
    intro u M hu
    rw [smul_add, smul_smul, smul_smul, mul_sub, hu, mul_one, sub_zero, zero_smul, zero_add]
  refine ⟨gS, k, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k
    rw [hS2, hk2, glue_mul he, Matrix.mul_one, Matrix.one_mul, glue_self]
  · intro u hu
    rw [hS2, smul_sub, smul_add, smul_smul, smul_smul, mul_sub, heu u hu, mul_one, sub_zero, zero_smul, zero_add,
      sub_self]
  · intro w hw u hu
    have h1 : (1 - e) * u = 0 := hu (1 - e) (by rw [map_sub, map_one, he1 w hw, sub_self])
    have h2 : u * (1 - e) = 0 := by rw [mul_comm, h1]
    have h3 : u * e = u := by rw [mul_sub, mul_one, sub_eq_zero] at h2; exact h2.symm
    rw [hk2, smul_sub, smul_add, smul_smul, smul_smul, h2, h3, zero_smul, add_zero, sub_self]
  · intro u hu
    have h1 : e * u = 0 := hu e heI
    rw [hk2, smul_sub, smul_sub, hoff u _ (by rw [mul_comm, h1])]
  · intro w hw z hz
    have key : ∀ M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E),
        (e • (1 : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) + (1 - e) • M) *ᵥ z = M *ᵥ z := by
      intro M
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, -, y, -, rfl⟩ := hz
        have h1 : e * a = 0 := ha e (he0 w hw)
        rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec,
          hoff a M (by rw [mul_comm, h1])]
      | zero => rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, Matrix.mulVec_add, hx, hy]
      | neg x _ hx => rw [Matrix.mulVec_neg, Matrix.mulVec_neg, hx]
    rw [hk2, hk3]
    exact ⟨key _, key _⟩

end GlobalTheory.PlaceCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleFiniteFactorArchimedeanSchwartz
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.ArchUniq

variable {F : Type} [Field F] [NumberField F]

def intFinInd (F : Type) [Field F] [NumberField F] (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  Set.indicator (Set.pi Set.univ fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) 1

theorem intFinInd_mem_SB (κ : Type) [Fintype κ] : intFinInd F κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  set C := Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
  have hoI : IsOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    GroundTheory.Global.isOpen_integralFiniteAdeles
  have hcI := GroundTheory.Global.isCompact_integralFiniteAdeles F
  have ho : IsOpen C := isOpen_set_pi Set.finite_univ fun _ _ => hoI
  have hc : IsClosed C :=
    isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).toAddSubgroup hoI
  have hk : IsCompact C := isCompact_univ_pi fun _ => hcI
  refine ⟨?_, HasCompactSupport.intro' hk hc fun y hy => Set.indicator_of_notMem hy _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ C
  · filter_upwards [ho.mem_nhds hx] with y hy
    simp only [intFinInd]
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    rfl
  · filter_upwards [hc.isOpen_compl.mem_nhds hx] with y hy
    simp only [intFinInd]
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem snd_eq_zero_of_at {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
  have h2 := congrArg Prod.snd h
  change (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 at h2
  rwa [one_mul] at h2

theorem exists_admissible_finite_factor : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ r₀ : (κ → AF F) → ℂ,
    (∀ f : SInf F κ, Rest (evI F) (⇑f) r₀) ∧
    ∀ f₁ f₂ : SInf F κ, tens (evI F) (⇑f₁) r₀ = tens (evI F) (⇑f₂) r₀ → f₁ = f₂ := by
  intro F _ _ κ _
  refine ⟨fun x => intFinInd F κ (fun i => (x i).2), fun f => ⟨fun x z hz => ?_, ?_⟩, fun f₁ f₂ h => ?_⟩
  · have : (fun i => (x + z) i |>.2) = fun i => (x i).2 := by
      funext i
      change (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero_of_at hz i, add_zero]
    simp only [this]
  · exact Submodule.subset_span ⟨f, intFinInd F κ, intFinInd_mem_SB κ, rfl⟩
  · ext y
    have h1 := congrFun h (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)), 0))
    have hy : (fun i => evI F (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)) = y := by
      funext i
      simp [evI]
    have h0 : intFinInd F κ (fun _ => 0) = 1 := by
      simp only [intFinInd]
      rw [Set.indicator_of_mem (show (fun _ => (0 : FiniteAdeleRing (𝓞 F) F)) ∈ Set.pi Set.univ
        fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
        fun _ _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).zero_mem)]
      rfl
    simp only [tens, hy, h0, mul_one] at h1
    exact h1

end GlobalTheory.ArchUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntiInvariantSignAdeleSplitPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitSign

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_conj {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hc.2.2.2 τ, hc.2.2.2 τ, star_star]

theorem exists_anti_unit {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) {v : Pl F} (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) :
    ∃ (τ : E →ₐ[F] Fv F v) (δ : 𝓞 E), σ (δ : E) = -(δ : E) ∧ Valued.v (τ (δ : E)) = 1 := by
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hv
  have hPv : P.under (𝓞 F) = v := HeightOneSpectrum.ext hP
  obtain ⟨τ, hτ⟩ := SplitChart.exists_splitPrime_eq hc ⟨P, Q, hPQ, hP, hQ⟩ hPv
  obtain ⟨w', hne, -, -, -, hw'⟩ := SplitChart.exists_conj_place hc (splitPrime_under τ) ⟨P, Q, hPQ, hP, hQ⟩
  have hmax : (splitPrime τ).asIdeal.IsMaximal := (splitPrime τ).isMaximal
  have hmax' : w'.asIdeal.IsMaximal := w'.isMaximal
  have hnle : ¬ (splitPrime τ).asIdeal ≤ w'.asIdeal := fun hle =>
    hne (HeightOneSpectrum.ext (hmax.eq_of_le hmax'.ne_top hle))
  obtain ⟨θ, hθP, hθw⟩ := Set.not_subset.1 hnle
  set σθ : 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E) θ with hσθ
  have hσθP : σθ ∉ (splitPrime τ).asIdeal := by
    intro h
    apply hθw
    rw [hw']
    exact h
  refine ⟨τ, θ - σθ, ?_, ?_⟩
  · have e : ((σθ : 𝓞 E) : E) = σ (θ : E) := rfl
    push_cast
    rw [map_sub]
    change σ (θ : E) - σ (σ (θ : E)) = -((θ : E) - σ (θ : E))
    rw [conj_conj hc]
    ring
  · have hnot : θ - σθ ∉ (splitPrime τ).asIdeal := by
      intro h
      apply hσθP
      have := (splitPrime τ).asIdeal.sub_mem hθP h
      simpa using this
    rw [mem_splitPrime] at hnot
    exact le_antisymm (apply_coe_mem τ _) (not_lt.1 hnot)

theorem smul_eq_self_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {z : M}
    (hz : At (evFin F v) z) : GlobalTheory.LatVac.liftV v 1 • z = z := by
  have h := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

theorem liftV_mul_liftV (v : Pl F) (a b : Fv F v) :
    GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b = GlobalTheory.LatVac.liftV v (a * b) := by
  rw [show GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b = _ from GlobalTheory.EmbChart.atPlace_mul_right v a _]
  show GlobalTheory.LatVac.liftV v (a * evFin F v (GlobalTheory.LatVac.liftV v b)) = _
  rw [GlobalTheory.LatVac.evFin_liftV]

end GlobalTheory.SplitSign

open GlobalTheory.SplitSign in

theorem GlobalTheory.SplitSign.exists_split_sign : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → ∃ c : AE F E, cA σ c = -c ∧ At (evFin F v) c ∧
      (∀ z : AE F E, At (evFin F v) z → c * c * z = z) ∧
      ∀ (d : ℕ) (W : Spc F E d), ∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ B hB v hv
  obtain ⟨τ, δ, hσδ, hδv⟩ := exists_anti_unit hB.cm hv
  set s : Fv F v := τ (δ : E) with hs
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hδv
    exact zero_ne_one hδv
  have hsinv : s⁻¹ ∈ v.adicCompletionIntegers F := by
    show Valued.v s⁻¹ ≤ 1
    rw [map_inv₀, hδv, inv_one]
  obtain ⟨f, hf⟩ := SnMass.SkewVol.mem_range_of_cm_fixed hB.cm (x := (δ : E) * δ)
    (by rw [map_mul, hσδ, neg_mul_neg])
  refine ⟨GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E), ?_, ?_, ?_, ?_⟩
  · rw [cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hσδ, TensorProduct.tmul_neg]
  · intro u hu
    rw [TensorProduct.smul_tmul', GlobalTheory.LatVac.at_liftV v s⁻¹ u hu, TensorProduct.zero_tmul]
  · intro z hz
    have hcc : (GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E)) * (GlobalTheory.LatVac.liftV v s⁻¹ ⊗ₜ[F] (δ : E)) =
        GlobalTheory.LatVac.liftV v 1 • (1 : AE F E) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← hf, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', liftV_mul_liftV, ← map_smul]
      have h1 : f • (s⁻¹ * s⁻¹) = (1 : Fv F v) := by
        rw [Algebra.smul_def, ← AlgHom.commutes τ f, hf, map_mul, ← hs]
        field_simp
      rw [h1, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hcc, smul_mul_assoc, one_mul, smul_eq_self_of_at hz]
  · intro d W z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, y, hy, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v s⁻¹ * a, ?_, ?_, δ • y, W.L.smul_mem δ hy, ?_⟩
      · intro u hu
        rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
      · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
        exact mul_mem hsinv hav
      · funext i
        simp only [Pi.smul_apply, smul_eq_mul, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul', mul_one,
          Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRepRightTranslationMaxCompactSta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeRep

open GlobalTheory.KTypeProj GlobalTheory.Published.AutFin

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

theorem conj_UH (τ : D.what₂.Tau) (k : Formalism.REAL.KG (M.ε τ)) :
    (M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
  GlobalTheory.Published.AutFin.conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) k

theorem fr_mul_inv (τ : D.what₂.Tau) : M.fr τ * (M.fr τ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

theorem fr_inv_mul (τ : D.what₂.Tau) : (M.fr τ)⁻¹ * M.fr τ = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

theorem conj_inK (τ : D.what₂.Tau) (k : Formalism.REAL.KG (M.ε τ)) :
    GlobalTheory.CuspGK.InK M τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ) := by
  refine ⟨conj_UH M τ k, ?_⟩
  have hc : M.fr τ * ((M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ) * (M.fr τ)⁻¹ =
      (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.toMK k * (M.fr τ * (M.fr τ)⁻¹) := by
    simp only [mul_assoc]
  rw [hc, fr_mul_inv M τ, one_mul, mul_one]
  exact k.2

theorem kAt_one (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) : kAt θ V τ (M.ε τ) (M.fr τ) 1 = 1 := by
  show atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK (1 : Formalism.REAL.KG (M.ε τ)) * M.fr τ) = 1
  have h1 : Formalism.REAL.toMK (1 : Formalism.REAL.KG (M.ε τ)) = 1 := rfl
  rw [h1, mul_one, fr_inv_mul M τ]
  exact GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ

theorem kAt_mul (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) (a b : Formalism.REAL.KG (M.ε τ)) :
    kAt θ V τ (M.ε τ) (M.fr τ) (a * b) = kAt θ V τ (M.ε τ) (M.fr τ) a * kAt θ V τ (M.ε τ) (M.fr τ) b := by
  show atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK (a * b) * M.fr τ) =
    atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK a * M.fr τ) * atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK b * M.fr τ)
  rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (conj_UH M τ a) (conj_UH M τ b)]
  have hab : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
  have hsplit : (M.fr τ)⁻¹ * Formalism.REAL.toMK a * M.fr τ * ((M.fr τ)⁻¹ * Formalism.REAL.toMK b * M.fr τ) =
      (M.fr τ)⁻¹ * Formalism.REAL.toMK a * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.toMK b * M.fr τ := by
    simp only [mul_assoc]
  rw [hsplit, fr_mul_inv M τ, mul_one, hab]
  simp only [mul_assoc]

theorem continuous_kAt (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) :
    Continuous fun k => kAt θ V τ (M.ε τ) (M.fr τ) k := by
  have hK : Continuous fun k : Formalism.REAL.KG (M.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hconj : Continuous fun k : Formalism.REAL.KG (M.ε τ) => (M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ :=
    (continuous_const.matrix_mul hK).matrix_mul continuous_const
  exact (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous hconj fun k => conj_UH M τ k

def kRep (hθ : IsInfFam (D := D) θ) (Y : Submodule ℂ (GA D V → ℂ)) (hY : KStable θ M Y) (τ : D.what₂.Tau) :
    Representation ℂ (Formalism.REAL.KG (M.ε τ)) Y where
  toFun k := (rTrL (kAt θ V τ (M.ε τ) (M.fr τ) k)).restrict fun f hf => hY τ _ (conj_inK M τ k) f hf
  map_one' := by
    refine LinearMap.ext fun w => Subtype.ext (funext fun x => ?_)
    show w.1 (x * kAt θ V τ (M.ε τ) (M.fr τ) 1) = w.1 x
    rw [kAt_one M hθ, mul_one]
  map_mul' a b := by
    refine LinearMap.ext fun w => Subtype.ext (funext fun x => ?_)
    show w.1 (x * kAt θ V τ (M.ε τ) (M.fr τ) (a * b)) =
      w.1 (x * kAt θ V τ (M.ε τ) (M.fr τ) a * kAt θ V τ (M.ε τ) (M.fr τ) b)
    rw [kAt_mul M hθ, mul_assoc]

theorem isContRep_kRep (hθ : IsInfFam (D := D) θ) (Y : Submodule ℂ (GA D V → ℂ)) [FiniteDimensional ℂ Y]
    (hY : KStable θ M Y) (hc : ∀ f ∈ Y, Continuous f) (τ : D.what₂.Tau) : IsContRep (kRep M hθ Y hY τ) := by
  intro ℓ w
  have hℓ : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  refine hℓ.comp (continuous_induced_rng.2 (continuous_pi fun x => ?_))
  show Continuous fun k => (w : GA D V → ℂ) (x * kAt θ V τ (M.ε τ) (M.fr τ) k)
  exact (hc _ w.2).comp (continuous_const.mul (continuous_kAt M hθ τ))

end GlobalTheory.KTypeRep

theorem GlobalTheory.KTypeRep.exists_contRep_types : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y → GlobalTheory.KTypeProj.KStable θ M Y → (∀ f ∈ Y, Continuous f) →
    ∀ τ, ∃ ρ : Representation ℂ (Formalism.REAL.KG (M.ε τ)) Y, GlobalTheory.Published.AutFin.IsContRep ρ ∧
      ∀ T : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ),
        (∀ i, ∀ w ∈ Y, T (GlobalTheory.KTypeProj.rhoK θ M i w) = GlobalTheory.KTypeProj.rhoK θ M i (T w)) →
        ∀ w : Y, GlobalTheory.Published.AutFin.HasTypeAt θ V τ (M.ε τ) (M.fr τ) ρ (T w) := by
  intro D θ V S M hθ Y hfin hY hc τ
  haveI := hfin
  refine ⟨GlobalTheory.KTypeRep.kRep M hθ Y hY τ, GlobalTheory.KTypeRep.isContRep_kRep M hθ Y hY hc τ, ?_⟩
  intro T hT w
  refine GlobalTheory.Published.AutFin.hasTypeAt_of_map θ V τ (M.ε τ) (M.fr τ) _ (T ∘ₗ Y.subtype) (fun k u => ?_) w
  exact hT ⟨(τ, (M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ), GlobalTheory.KTypeRep.conj_inK M τ k⟩ u.1 u.2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftRealCentreAverageEigenvectorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaLift_realCentre_average_eigenvector : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → S.SigOK → S.IsDefinite → ∀ (ν : Measure (GA D S)) (fd : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) fd ν → ∀ (χ φ : GA D S → ℂ), GlobalTheory.SeeSaw.HasCen S χ φ → GlobalTheory.Unf.IsContAut S φ → ∀ Φ, IsThetaFunO ψ S T Φ → (∀ h, IntegrableOn (fun g => thetaKO om g h Φ * φ g) fd ν) → ∃ Φ', IsThetaFunO ψ S T Φ' ∧ (∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → om (z, 1) Φ' = (χ z)⁻¹ • Φ') ∧ ∀ h, ∫ g in fd, thetaKO om g h Φ * φ g ∂ν = ∫ g in fd, thetaKO om g h Φ' * φ g ∂ν := by
  first | exact @GlobalTheory.CenAvgOne.exists_central_average_one | exact GlobalTheory.CenAvgOne.exists_central_average_one | (intros; apply GlobalTheory.CenAvgOne.exists_central_average_one <;> assumption)
end

