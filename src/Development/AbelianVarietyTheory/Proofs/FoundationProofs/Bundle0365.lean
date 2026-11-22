import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0337
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphicRepWeightEmbedding
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

namespace GlobalTheory.DefU.EquivWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cEmb_eq_one_of_mem_embU {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ' ≠ InfinitePlace.mk τ) {x : UA E n}
    (hx : x ∈ embU n τ) : cEmb τ' x = 1 := by
  have h1 := (Subgroup.mem_inf.1 hx).2
  rw [Subgroup.mem_iInf] at h1
  have h2 := h1 τ'
  rw [Subgroup.mem_iInf] at h2
  exact h2 h

theorem rhoK_tenMul_update {ι : Type} [Fintype ι] [DecidableEq ι] (σ : ι → (E →+* ℂ)) (lam : ι → DomWeight n)
    (hσ : Function.Injective (fun τ => InfinitePlace.mk (σ τ))) (τ₀ : ι) {x : UA E n} (hx : x ∈ embU n (σ τ₀))
    (e : ∀ τ, nablaSq ℂ n (lam τ)) (a : nablaSq ℂ n (lam τ₀)) :
    Formalism.L2.DIV.rhoK (K := ℂ) lam ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)) x)
              (GlobalTheory.CoefIrred.tenMul lam (Function.update e τ₀ a)) =
      GlobalTheory.CoefIrred.tenMul lam (Function.update e τ₀ (GlobalTheory.Branching.sqRep ℂ n (lam τ₀) (cEmb (σ τ₀) x) a)) := by
  rw [rhoK_tenMul]
  congr 1
  funext τ
  by_cases h : τ = τ₀
  · subst h
    simp only [Function.update_self]
    rfl
  · have hne : InfinitePlace.mk (σ τ) ≠ InfinitePlace.mk (σ τ₀) := fun e' => h (hσ e')
    simp only [Function.update_of_ne h, MonoidHom.pi_apply, cEmb_eq_one_of_mem_embU hne hx, map_one,
      Module.End.one_apply]

theorem hasWeightAt_of_equivariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι]
    (σ : ι → (E →+* ℂ)) (lam : ι → DomWeight n), Function.Injective (fun τ => InfinitePlace.mk (σ τ)) →
    ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] (UA E n → ℂ)), f ≠ 0 →
    (∀ v, f v ∈ π) → (∀ (x : infU E n) v, f (((Formalism.L2.DIV.rhoK (K := ℂ) lam).comp
      ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)).comp (infU E n).subtype)) x v) = RU E n x (f v)) →
    ∀ τ, HasWeightAt π (σ τ) (lam τ) ∧ HasWeightAt π (ComplexEmbedding.conjugate (σ τ)) (lam τ).dual := by
  intro E _ _ _ n ι _ σ lam hσ π hπ f hf0 hfπ hfeq τ₀
  classical
  obtain ⟨e, he⟩ : ∃ e, f (GlobalTheory.CoefIrred.tenMul lam e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h1 := (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal ι n lam (UA E n → ℂ) 0).unique (y₁ := f) (y₂ := 0)
      (fun u => hc u) (fun u => rfl)
    exact hf0 h1
  have h1 : HasWeightAt π (σ τ₀) (lam τ₀) := by
    refine ⟨isIrreducible_sqRep n (lam τ₀), f ∘ₗ (GlobalTheory.CoefIrred.tenMul lam).toLinearMap e τ₀, fun h0 => he ?_,
      fun a => hfπ _, fun x a => ?_⟩
    · have := LinearMap.congr_fun h0 (e τ₀)
      simpa [MultilinearMap.toLinearMap] using this
    · have hx : x.1 ∈ infU E n := embU_le_infU _ x.2
      have h2 := hfeq ⟨x.1, hx⟩ (GlobalTheory.CoefIrred.tenMul lam (Function.update e τ₀ a))
      change f (Formalism.L2.DIV.rhoK (K := ℂ) lam ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)) x.1) _) = _ at h2
      rw [rhoK_tenMul_update σ lam hσ τ₀ x.2] at h2
      exact h2
  refine ⟨h1, ?_⟩
  have h3 : (AU.mk (⟨π, hπ⟩ : AutSub E n)).HasWt (σ τ₀) (lam τ₀) := (AU.hasWt_mk _ _ _).2 h1
  exact (AU.hasWt_mk _ _ _).1 h3.conjugate

end GlobalTheory.DefU.EquivWt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteUnitaryFinitePointsExistsOpenCompact
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
open Matrix

noncomputable section

namespace GlobalTheory.DefU.FinCompact

theorem exists_open_compact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    ∃ K : Subgroup (finU E n), IsOpen (K : Set (finU E n)) ∧ IsCompact (K : Set (finU E n)) := by
  intro E _ _ _ n
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E n
  let p : finU E n →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU E n).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  let K : Subgroup (finU E n) := U0.comap p
  have hKo : IsOpen (K : Set (finU E n)) := hU0o.preimage hp
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  have hfc : IsClosed ((finU E n : Subgroup (UA E n)) : Set (UA E n)) := by
    haveI : T2Space (GL (Fin n) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
    have hc := GlobalTheory.CuspRep.ContAut.continuous_map_pInf E n
    exact isClosed_eq (hc.comp continuous_subtype_val) continuous_const
  have hι : Topology.IsClosedEmbedding (fun x : finU E n => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hfc.isClosedEmbedding_subtypeVal
  refine ⟨K, hKo, IsCompact.of_isClosed_subset (hι.isCompact_preimage (hU0c.image GlobalTheory.DefU.LocAdm.continuous_finGL))
    (Subgroup.isClosed_of_isOpen K hKo) fun x hx => ⟨p x, hx, ?_⟩⟩
  have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

end GlobalTheory.DefU.FinCompact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylInvariantPairing
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.FischerInvariance

open MvPolynomial GlobalTheory.DefLift.BilFischer

theorem rowAct_eq_lin {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g =
      lin (fun v w : Fin n × Fin n => if w.2 = v.2 then g v.1 w.1 else 0) := by
  unfold Formalism.GradedWeylDivisibility.rowAct lin
  congr 1
  funext v
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single v.2]
  · simp [smul_eq_C_mul]
  · intro s _ hs
    simp [hs]
  · simp

theorem rowAct_comp {n : ℕ} (g h : Matrix (Fin n) (Fin n) ℂ) :
    (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) h) =
      Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (h * g) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, aeval_X, map_sum, map_mul, aeval_C,
    Matrix.mul_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  simp [Algebra.algebraMap_eq_smul_one, mul_assoc]

theorem rowAct_inv_cancel {n : ℕ} (g : GL (Fin n) ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ)
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) u) = u := by
  have h := congrArg (fun φ => φ u) (rowAct_comp (n := n) (g : Matrix (Fin n) (Fin n) ℂ)
    ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
  simp only [AlgHom.comp_apply] at h
  rw [h, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have : Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (1 : Matrix (Fin n) (Fin n) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply]
  rw [this, AlgHom.id_apply]

theorem pair_conj_self {σ : Type} [Fintype σ] (u : MvPolynomial σ ℂ) :
    pair (map (starRingEnd ℂ) u) u =
      ((∑ α ∈ u.support, (∏ i, ((α i).factorial : ℝ)) * Complex.normSq (coeff α u) : ℝ) : ℂ) := by
  have hv : map (starRingEnd ℂ) u = ∑ α ∈ u.support, monomial α (starRingEnd ℂ (coeff α u)) := by
    conv_lhs => rw [u.as_sum]
    rw [map_sum]
    simp only [map_monomial]
  rw [hv, map_sum, LinearMap.sum_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [pair_monomial, Complex.ofReal_mul, Complex.ofReal_prod, wt]
  push_cast
  rw [← Complex.mul_conj]
  ring

theorem pair_conj_self_ne_zero {σ : Type} [Fintype σ] (u : MvPolynomial σ ℂ) (hu : u ≠ 0) :
    pair (map (starRingEnd ℂ) u) u ≠ 0 := by
  rw [pair_conj_self, Ne, Complex.ofReal_eq_zero]
  apply ne_of_gt
  apply Finset.sum_pos
  · intro α hα
    apply mul_pos
    · exact Finset.prod_pos fun i _ => Nat.cast_pos.2 (Nat.factorial_pos _)
    · exact Complex.normSq_pos.2 (mem_support_iff.1 hα)
  · exact support_nonempty.2 hu

theorem fischer_dualWeyl_invariant (n : ℕ) (ν : Fin n → ℕ) :
    ∃ b : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ,
      (∀ u ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, u ≠ 0 → ∃ v ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, b v u ≠ 0) ∧
      ∀ (g : GL (Fin n) ℂ) v u,
        b (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose v)
          (Formalism.UG.dwAct ℂ n n g u) = b v u := by
  refine ⟨pair, fun u hu hu0 => ⟨map (starRingEnd ℂ) u, GlobalTheory.SemilinTransport.map_mem _ hu,
    pair_conj_self_ne_zero u hu0⟩, fun g v u => ?_⟩
  rw [rowAct_eq_lin, pair_lin]
  have hT : (fun v w : Fin n × Fin n =>
      if v.2 = w.2 then (g : Matrix (Fin n) (Fin n) ℂ).transpose w.1 v.1 else 0) =
      fun v w => if w.2 = v.2 then (g : Matrix (Fin n) (Fin n) ℂ) v.1 w.1 else 0 := by
    funext v w
    by_cases h : v.2 = w.2
    · simp [h, Matrix.transpose_apply]
    · simp [h, Ne.symm h]
  rw [hT, ← rowAct_eq_lin]
  unfold Formalism.UG.dwAct
  rw [rowAct_inv_cancel]

end GlobalTheory.FischerInvariance

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSurjectiveDetPowMulDualWeyl
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.Branching

def lastNat {n : ℕ} (ν : Fin n → ℕ) : ℕ := if h : 0 < n then ν ⟨n - 1, by omega⟩ else 0

theorem natW_add_lastNat {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) (a : Fin n) : lam.natW a + lastNat ν = ν a := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a.2
  have ha : a ≤ (⟨n - 1, by omega⟩ : Fin n) := Fin.le_def.2 (by have := a.2; simp only; omega)
  have hl := lam.anti ha
  rw [h, h] at hl
  simp only [DomWeight.natW, DomWeight.detShift, lastNat, dif_pos hn, h]
  omega

theorem antitone_of_weight_eq {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) : Antitone ν := fun a b hab => by
  have := lam.anti hab
  rw [h, h] at this
  omega

theorem detPow_detShift_eq {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) (g : GL (Fin n) ℂ) :
    detPow ℂ n g lam.detShift = detPow ℂ n g c * (g : Matrix (Fin n) (Fin n) ℂ).det ^ lastNat ν := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp)
    simp [detPow, h1, lastNat]
  · have hs : lam.detShift = (lastNat ν : ℤ) + c := by simp [DomWeight.detShift, lastNat, hn, h]
    rw [hs, detPow, detPow, zpow_add, Units.val_mul, zpow_natCast, mul_comm]
    simp

theorem detPowMul_mem {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) (v : nablaSq ℂ n lam) :
    Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν * (v : MvPolynomial (Fin n × Fin n) ℂ) ∈
      Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν := by
  have hm := (genericDet_pow_mul n (lastNat ν) lam.natW).1 v v.2
  have e : (fun i => lam.natW i + lastNat ν) = ν := funext (natW_add_lastNat ν c lam h)
  rwa [e] at hm

def detPowMul {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n) (h : ∀ a, lam.w a = (ν a : ℤ) + c) :
    nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν :=
  LinearMap.codRestrict _ ((LinearMap.mulLeft ℂ (Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν)).comp
    (nablaSq ℂ n lam).subtype) (detPowMul_mem ν c lam h)

theorem detPowMul_coe {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n) (h : ∀ a, lam.w a = (ν a : ℤ) + c)
    (v : nablaSq ℂ n lam) : (detPowMul ν c lam h v : MvPolynomial (Fin n × Fin n) ℂ) =
      Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν * (v : MvPolynomial (Fin n × Fin n) ℂ) := rfl

theorem detPowMul_sqRep {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n) (h : ∀ a, lam.w a = (ν a : ℤ) + c)
    (g : GL (Fin n) ℂ) (v : nablaSq ℂ n lam) :
    (detPowMul ν c lam h (GlobalTheory.Branching.sqRep ℂ n lam g v) : MvPolynomial (Fin n × Fin n) ℂ) =
      detPow ℂ n g c • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose
        (detPowMul ν c lam h v : MvPolynomial (Fin n × Fin n) ℂ) := by
  rw [detPowMul_coe, detPowMul_coe, sqRep_coe, sqAct, (genericDet_pow_mul n (lastNat ν) (fun _ => 0)).2.1,
    Matrix.det_transpose, detPow_detShift_eq ν c lam h, mul_smul_comm, smul_smul]

end GlobalTheory.Branching

namespace GlobalTheory.Branching

theorem exists_surjective_detPowMul_dualWeyl : ∀ (n : ℕ) (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n), (∀ a, lam.w a = (ν a : ℤ) + c) → ∃ e : nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, Function.Surjective e ∧ ∀ (g : GL (Fin n) ℂ) v, (e (GlobalTheory.Branching.sqRep ℂ n lam g v) : MvPolynomial (Fin n × Fin n) ℂ) = detPow ℂ n g c • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose (e v : MvPolynomial (Fin n × Fin n) ℂ) := by
  intro n ν c lam h
  refine ⟨detPowMul ν c lam h, ?_, detPowMul_sqRep ν c lam h⟩
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) :=
    (LinearMap.range (detPowMul ν c lam h)).map (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν).subtype
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, Formalism.GradedWeylDivisibility.rowAct ℂ u f ∈ M := by
    rintro u hu _ ⟨_, ⟨v, rfl⟩, rfl⟩
    let t : Matrix.unitaryGroup (Fin n) ℂ := Matrix.UnitaryGroup.transpose ⟨u, hu⟩
    have h1 : (detPowMul ν c lam h (sqRep ℂ n lam (unitaryIncl n t) v) : MvPolynomial (Fin n × Fin n) ℂ) ∈ M :=
      ⟨_, ⟨_, rfl⟩, rfl⟩
    rw [detPowMul_sqRep] at h1
    have e : ((unitaryIncl n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).transpose = u := by
      simp [t]
    rw [e] at h1
    exact (M.smul_mem_iff (Units.ne_zero _)).1 h1
  have hcl := rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)
  have hν := antitone_of_weight_eq ν c lam h
  have hle : M ≤ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν := Submodule.map_subtype_le _ _
  have hne : M ≠ ⊥ := by
    intro e0
    have ha : Antitone lam.natW := fun i j hij => by
      have := lam.anti hij
      simp only [DomWeight.natW]
      omega
    let v : nablaSq ℂ n lam := ⟨_, Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ ha⟩
    have hm : (detPowMul ν c lam h v : MvPolynomial (Fin n × Fin n) ℂ) ∈ M := ⟨_, ⟨v, rfl⟩, rfl⟩
    have e : (fun i => lam.natW i + lastNat ν) = ν := funext (natW_add_lastNat ν c lam h)
    rw [e0, Submodule.mem_bot, detPowMul_coe] at hm
    change Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν * Formalism.GradedWeylDivisibility.hw ℂ le_rfl lam.natW = 0 at hm
    rw [genericDet_pow_mul_hw, e] at hm
    exact Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl ν hm
  have hall := dualWeyl_le_of_rowDivClosed le_rfl ν hν M hle hcl hne
  intro y
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hall y.2
  exact ⟨x, Subtype.ext hx⟩

end GlobalTheory.Branching
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalVectorValuedDefiniteUnitaryForm
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

namespace GlobalTheory.DefU

theorem finiteDimensional_vecForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S) (K : Subgroup (finU E n)), IsOpen (K : Set (finU E n)) → ∀ M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)), (∀ f ∈ M, (∀ v, ∀ γ ∈ ratU E n, ∀ g, f v (γ * g) = f v g) ∧ (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) ∧ ∀ k ∈ K, ∀ v, RU E n (k : UA E n) (f v) = f v) → FiniteDimensional ℂ M := by
  intro E _ _ _ n S _ _ _ ρ K hK M hM
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n K hK
  let T : M →ₗ[ℂ] (S₀ → Module.Dual ℂ S) :=
    { toFun := fun f s => (LinearMap.proj (R := ℂ) (φ := fun _ : UA E n => ℂ) (s : UA E n)).comp f.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    obtain ⟨hl, hr, hk⟩ := hM f.1 f.2
    have h0 : ∀ s ∈ S₀, ∀ v, f.1 v s = 0 := fun s hs v => LinearMap.congr_fun (congrFun hf ⟨s, hs⟩) v
    apply Subtype.ext
    refine LinearMap.ext fun v => funext fun g => ?_
    obtain ⟨γ, hγ, s, hs, x, hx, k, hkK, rfl⟩ := hS₀ g
    have e1 : f.1 v (γ * s * x * (k : UA E n)) = f.1 v (γ * s * x) := by
      have := congrFun (hk k hkK v) (γ * s * x)
      rw [← this]; rfl
    have e3 : f.1 v (s * x) = f.1 (ρ ⟨x, hx⟩ v) s := by
      rw [hr ⟨x, hx⟩ v]; rfl
    rw [e1, mul_assoc γ s x, hl v γ hγ, e3, h0 s hs]
    rfl
  exact Module.Finite.of_injective T hT

end GlobalTheory.DefU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAutFormUCoef
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.EquivCoef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  {X : Type} [AddCommGroup X] [Module ℂ X]

def coefL (R : UA E n →* Module.End ℂ X) (F : UA E n → X) : Module.Dual ℂ X →ₗ[ℂ] (UA E n → ℂ) where
  toFun μ := fun g => μ (R g⁻¹ (F g))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isAutFormU_coef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (X : Type) [AddCommGroup X]
    [Module ℂ X] [FiniteDimensional ℂ X] (R : UA E n →* Module.End ℂ X) (F : UA E n → X),
    (∀ k ∈ finU E n, R k = 1) → (∀ (u : X) (ℓ : Module.Dual ℂ X), Continuous fun g => ℓ (R g u)) →
    (∀ y ∈ infU E n, ∀ g, F (g * y) = F g) → (∀ γ ∈ ratU E n, ∀ g, F (γ * g) = R γ (F g)) →
    (∀ᶠ y in 𝓝 (1 : UA E n), ∀ g, F (g * y) = F g) →
    ∀ ℓ : Module.Dual ℂ X, IsAutFormU fun g => ℓ (R g⁻¹ (F g)) := by
  intro E _ _ _ n X _ _ _ R F hfin hcont hinf hrat hsm ℓ
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g0 => ?_
    have hc : Continuous fun g : UA E n => ℓ (R g⁻¹ (F g0)) := (hcont (F g0) ℓ).comp continuous_inv
    refine hc.continuousAt.congr ?_
    have ht : Filter.Tendsto (fun g : UA E n => g0⁻¹ * g) (𝓝 g0) (𝓝 1) := by
      have : Continuous fun g : UA E n => g0⁻¹ * g := continuous_const.mul continuous_id
      simpa only [inv_mul_cancel] using this.tendsto g0
    filter_upwards [ht.eventually hsm] with g hg
    have e := hg g0
    rw [mul_inv_cancel_left] at e
    change ℓ (R g⁻¹ (F g0)) = ℓ (R g⁻¹ (F g))
    rw [e]
  · intro γ hγ g
    change ℓ (R (γ * g)⁻¹ (F (γ * g))) = ℓ (R g⁻¹ (F g))
    rw [hrat γ hγ g, _root_.mul_inv_rev, map_mul, Module.End.mul_apply, ← Module.End.mul_apply (R γ⁻¹), ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
  · let φ : UA E n → ℂ := fun g => ℓ (R g⁻¹ (F g))
    let H : Subgroup (finU E n) :=
      { carrier := {k | RU E n (k : UA E n) φ = φ}
        mul_mem' := fun {a b} ha hb => by
          change RU E n ((a : UA E n) * b) _ = _
          rw [← GlobalTheory.DefU.RU_RU, hb, ha]
        one_mem' := by
          change RU E n 1 _ = _
          rw [map_one]; rfl
        inv_mem' := fun {a} ha => by
          change RU E n ((a : UA E n)⁻¹) _ = _
          conv_lhs => rw [← ha]
          change RU E n ((a : UA E n)⁻¹) (RU E n (a : UA E n) _) = _
          rw [GlobalTheory.DefU.RU_RU, inv_mul_cancel, map_one]; rfl }
    have hnb : {k : finU E n | ∀ g, F (g * (k : UA E n)) = F g} ∈ 𝓝 (1 : finU E n) :=
      (continuous_subtype_val.tendsto (1 : finU E n)).eventually hsm
    refine H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hnb fun k hk => ?_)
    change RU E n (k : UA E n) φ = φ
    funext g
    change ℓ (R (g * (k : UA E n))⁻¹ (F (g * k))) = ℓ (R g⁻¹ (F g))
    rw [hk g, _root_.mul_inv_rev, map_mul, hfin _ ((finU E n).inv_mem k.2), one_mul]
  · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (coefL R F)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨ℓ ∘ₗ R (k : UA E n)⁻¹, ?_⟩
    funext g
    change ℓ (R (k : UA E n)⁻¹ (R g⁻¹ (F g))) = ℓ (R (g * (k : UA E n))⁻¹ (F (g * k)))
    rw [hinf _ k.2 g, _root_.mul_inv_rev, map_mul, Module.End.mul_apply]

end GlobalTheory.EquivCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAutRepUSpanValues
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

namespace GlobalTheory.FrameAut.VecForms

theorem isAutRepU_span_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)), M ≠ ⊥ → (∀ f ∈ M, (∀ v, IsAutFormU (f v)) ∧ ∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) → (∀ k ∈ finU E n, ∀ f ∈ M, (RU E n k) ∘ₗ f ∈ M) → (∀ N ≤ M, (∀ k ∈ finU E n, ∀ f ∈ N, (RU E n k) ∘ₗ f ∈ N) → N = ⊥ ∨ N = M) → IsAutRepU (Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ}) := by
  intro E _ _ _ n S _ _ _ ρ hsp M hM0 hf hk hirr
  let j : M →ₗ[ℂ] S →ₗ[ℂ] (UA E n → ℂ) := M.subtype
  have himg : Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ} = GlobalTheory.DefU.Pairs.img j := by
    unfold GlobalTheory.DefU.Pairs.img
    congr 1
    ext φ
    constructor
    · rintro ⟨f, hf, v, rfl⟩
      exact ⟨⟨f, hf⟩, v, rfl⟩
    · rintro ⟨p, v, rfl⟩
      exact ⟨p.1, p.2, v, rfl⟩
  rw [himg]
  have hj : ∀ (p : M) (x : infU E n) (v : S), j p (ρ x v) = RU E n x.1 (j p v) := fun p x v => (hf p.1 p.2).2 x v
  have hstab : ∀ x, ∀ φ ∈ GlobalTheory.DefU.Pairs.img j, RU E n x φ ∈ GlobalTheory.DefU.Pairs.img j := by
    intro x φ hφ
    refine GlobalTheory.DefU.Pairs.stable_of (fun a => ?_) (fun k => ?_) x φ hφ
    · have h1 : GlobalTheory.DefU.Pairs.img j ≤ (GlobalTheory.DefU.Pairs.img j).comap (RU E n a.1) := Submodule.span_le.2 (by
        rintro _ ⟨p, v, rfl⟩
        change RU E n a.1 _ ∈ GlobalTheory.DefU.Pairs.img j
        rw [← hj]
        exact GlobalTheory.DefU.Pairs.apply_mem_img _ _ _)
      exact fun φ hφ => h1 hφ
    · have h1 : GlobalTheory.DefU.Pairs.img j ≤ (GlobalTheory.DefU.Pairs.img j).comap (RU E n k.1) := Submodule.span_le.2 (by
        rintro _ ⟨p, v, rfl⟩
        exact GlobalTheory.DefU.Pairs.apply_mem_img j ⟨(RU E n k.1) ∘ₗ p.1, hk k k.2 p.1 p.2⟩ v)
      exact fun φ hφ => h1 hφ
  have hne : GlobalTheory.DefU.Pairs.img j ≠ ⊥ := by
    obtain ⟨f, hfM, h0⟩ := (Submodule.ne_bot_iff _).1 hM0
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 h0
    intro e
    have := GlobalTheory.DefU.Pairs.apply_mem_img j ⟨f, hfM⟩ v
    rw [e, Submodule.mem_bot] at this
    exact hv this
  let Q : finU E n → Module.End ℂ M := fun k =>
    ((LinearMap.llcomp ℂ S (UA E n → ℂ) (UA E n → ℂ) (RU E n k.1)) ∘ₗ M.subtype).codRestrict M
      (fun p => hk k k.2 p.1 p.2)
  have hP : ∀ N : Submodule ℂ M, (∀ k, ∀ p ∈ N, Q k p ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    have hst : ∀ k ∈ finU E n, ∀ f ∈ N.map M.subtype, (RU E n k) ∘ₗ f ∈ N.map M.subtype := by
      rintro k hkk _ ⟨p, hp, rfl⟩
      exact ⟨Q ⟨k, hkk⟩ p, hN ⟨k, hkk⟩ p hp, rfl⟩
    have hc : N = (N.map M.subtype).comap M.subtype :=
      (Submodule.comap_map_eq_of_injective M.injective_subtype N).symm
    rcases hirr _ (Submodule.map_subtype_le M N) hst with h | h
    · left
      rw [hc, h, Submodule.comap_bot, Submodule.ker_subtype]
    · right
      rw [hc, h, Submodule.comap_subtype_self]
  refine ⟨fun φ hφ => ?_, hstab, hne, fun U hle hU => ?_⟩
  · have h1 : GlobalTheory.DefU.Pairs.img j ≤ autU E n := Submodule.span_le.2 (by
      rintro _ ⟨p, v, rfl⟩
      exact (hf p.1 p.2).1 v)
    exact h1 hφ
  · exact GlobalTheory.DefU.Pairs.eq_bot_or_eq_img hsp (R := fun x => RU E n x.1) hj
      (Q := Q) (T := fun k => RU E n k.1) (fun _ _ _ => rfl) hP hle
      (fun x => hU x.1) (fun k => hU k.1)

end GlobalTheory.FrameAut.VecForms
end

