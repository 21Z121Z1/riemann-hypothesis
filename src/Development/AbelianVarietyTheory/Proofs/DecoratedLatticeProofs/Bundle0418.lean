import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0330
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0384

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAverageTranslateEqSmulBranchingMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.KJAvg

open GlobalTheory.BranchFormula

def blk {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 1)

theorem blk_castSucc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    blk A a.castSucc b.castSucc = A a b := by
  simp [blk, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem blk_castSucc_last {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) :
    blk A a.castSucc (Fin.last n) = 0 ∧ blk A (Fin.last n) a.castSucc = 0 := by
  simp [blk, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem blk_last {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : blk A (Fin.last n) (Fin.last n) = 1 := by
  simp [blk, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem blk_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : blk (A * B) = blk A * blk B := by
  simp [blk, Matrix.fromBlocks_multiply]

theorem blk_cont {n : ℕ} : Continuous (blk (n := n)) := by
  unfold blk
  fun_prop

theorem blk_mul_cont {X : Type} [TopologicalSpace X] {n : ℕ} (f : X → Matrix (Fin n) (Fin n) ℂ) (hf : Continuous f)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Continuous fun x => blk (f x) * B :=
  (blk_cont.comp hf).matrix_mul continuous_const

theorem isBlock_blk {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : IsBlock (rfl : n + 1 = n + 1) (blk A) A 1 := by
  refine ⟨fun a b => ?_, fun a => ?_, ?_⟩
  · exact blk_castSucc A a b
  · exact blk_castSucc_last A a
  · exact blk_last A

theorem eq_blk {n : ℕ} {A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {A : Matrix (Fin n) (Fin n) ℂ}
    (h : IsBlock (rfl : n + 1 = n + 1) A' A 1) : A' = blk A := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [blk_last]; exact h.2.2
    | cast b => rw [(blk_castSucc_last A b).2]; exact (h.2.1 b).2
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [(blk_castSucc_last A a).1]; exact (h.2.1 a).1
    | cast b => rw [blk_castSucc]; exact h.1 a b

theorem cptU (m : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin m) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset (t := ((Matrix.unitaryGroup (Fin m) ℂ : Submonoid _) :
      Set (Matrix (Fin m) (Fin m) ℂ))) hK isClosed_unitary ?_
  intro U hU
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j =>
    mem_closedBall_zero_iff.2 (entry_norm_bound_of_unitary hU i j)

theorem cont_val {ι : Type} [Fintype ι] {X : Type} [TopologicalSpace X] {a : ℕ} {G : ι → Matrix (Fin a) (Fin a) ℂ}
    {lam : ι → DomWeight a} {Φ : Frames G → ℂ} (hΦ : Φ ∈ ValC G lam) (M : X → ι → Matrix (Fin a) (Fin a) ℂ)
    (hM : Continuous M) (hinv : ∀ x τ, IsUnit (M x τ).det) : Continuous fun x => Φ ⟨M x, hinv x⟩ := by
  obtain ⟨P, -, rfl⟩ := hΦ
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, one_mul]
  refine Continuous.mul ?_ ?_
  · refine continuous_finset_prod _ fun τ _ => ?_
    exact Continuous.zpow₀ ((continuous_apply τ).comp hM).matrix_det _ fun x => Or.inl (hinv x τ).ne_zero
  · exact (MvPolynomial.continuous_eval P).comp
      (continuous_pi fun x => ((continuous_apply x.1).comp hM).matrix_elem x.2.1 x.2.2)

theorem cont_blkfam {ι : Type} [Fintype ι] {n : ℕ} (y : ι → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Continuous fun (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (τ : ι) => blk (u τ).1 * y τ :=
  continuous_pi fun τ => blk_mul_cont (fun u : ι → Matrix.unitaryGroup (Fin n) ℂ => (u τ).1)
    (continuous_subtype_val.comp (continuous_apply τ)) (y τ)

theorem uniH {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    u * uᴴ = 1 ∧ uᴴ * u = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact ⟨Matrix.mem_unitaryGroup_iff.1 hu, Matrix.mem_unitaryGroup_iff'.1 hu⟩

theorem r_one {ι : Type} [Fintype ι] {m : ℕ} {K : Type} [Group K] [TopologicalSpace K]
    {r : K → ι → Matrix (Fin m) (Fin m) ℂ} (hr : OntoUni r) (τ : ι) : r 1 τ = 1 := by
  have h := hr.mul 1 1 τ
  rw [mul_one] at h
  have hu := (uniH (hr.uni 1 τ)).2
  calc r 1 τ = (r 1 τ)ᴴ * r 1 τ * r 1 τ := by rw [hu, one_mul]
    _ = (r 1 τ)ᴴ * r 1 τ := by rw [mul_assoc, ← h]
    _ = 1 := hu

theorem r_inv_H {ι : Type} [Fintype ι] {m : ℕ} {K : Type} [Group K] [TopologicalSpace K]
    {r : K → ι → Matrix (Fin m) (Fin m) ℂ} (hr : OntoUni r) (k : K) (τ : ι) : (r k⁻¹ τ)ᴴ = r k τ := by
  have h := hr.mul k⁻¹ k τ
  rw [inv_mul_cancel, r_one hr] at h
  calc (r k⁻¹ τ)ᴴ = (r k⁻¹ τ)ᴴ * (r k⁻¹ τ * r k τ) := by rw [← h, mul_one]
    _ = r k τ := by rw [← mul_assoc, (uniH (hr.uni k⁻¹ τ)).2, one_mul]

theorem avg_eq_mul_branch : ∀ (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight N) (sg : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (lam τ) (sg τ)) → ∀ T₀, BrEqv hN G G' lam sg T₀ → (∃ Φ ∈ ValC G lam, T₀ Φ ≠ 0) → ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] (r : K → ι → Matrix (Fin n) (Fin n) ℂ), OntoUni r → ∀ (y : Frames G) (yk : K → Frames G), (∀ k, ∃ kt, (∀ τ, GlobalTheory.BranchFormula.IsBlock hN (kt τ) (r k τ) 1) ∧ IsTr kt y (yk k)) → ∀ J ∈ ValC G' sg, ∀ Jk : K → Frames G' → ℂ, (∀ k z z', IsTr (r k) z z' → Jk k z' = J z) → ∃ c : ℂ, ∀ Φ ∈ ValC G lam, ∀ ℓ : (Frames G' → ℂ) →ₗ[ℂ] ℂ, ∫ k, ℓ (Jk k) * Φ (yk k) ∂ν = c * ℓ (T₀ Φ) := by
  intro ι _ N n hN G G' lam sg hI T₀ hT₀ hne K _ _ _ _ _ ν _ _ r hr y yk hyk J hJ Jk hJk
  subst hN
  have hfd' : FiniteDimensional ℂ (ValC G' sg) := (GlobalTheory.T.frame_values_polynomial_det_stable_homogeneous ι n G' sg).2.1
  have stab' := (GlobalTheory.T.frame_values_polynomial_det_stable_homogeneous ι n G' sg).2.2.1
  have stab := (GlobalTheory.T.frame_values_polynomial_det_stable_homogeneous ι (n + 1) G lam).2.2.1
  haveI := cptU n
  have invH : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (z : Frames G') τ, IsUnit (((u τ).1)ᴴ * z.1 τ).det := by
    intro u z τ
    rw [Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse (uniH (u τ).2).1).mul (z.2 τ)
  let zU : (ι → Matrix.unitaryGroup (Fin n) ℂ) → Frames G' → Frames G' := fun u z => ⟨fun τ => ((u τ).1)ᴴ * z.1 τ, invH u z⟩
  have memJ : ∀ u, (fun z => J (zU u z)) ∈ ValC G' sg := by
    intro u
    refine stab' J hJ (fun τ => ((u τ).1)ᴴ) _ (fun z z' h => congrArg J (Subtype.ext (funext fun τ => (h τ).symm))) ?_
    intro τ
    exact Matrix.isUnit_det_of_left_inverse (uniH (u τ).2).1
  let jU : (ι → Matrix.unitaryGroup (Fin n) ℂ) → ValC G' sg := fun u => ⟨_, memJ u⟩
  obtain ⟨e⟩ : Nonempty (ValC G' sg ≃ₗ[ℂ] (Fin (Module.finrank ℂ (ValC G' sg)) → ℂ)) :=
    ⟨(Module.finBasis ℂ (ValC G' sg)).equivFun⟩
  have invB : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) τ, IsUnit (blk (u τ).1 * y.1 τ).det := by
    intro u τ
    rw [Matrix.det_mul, (isBlock_blk (u τ).1).det, mul_one]
    exact (Matrix.isUnit_det_of_left_inverse (uniH (u τ).2).2).mul (y.2 τ)
  let yU : (ι → Matrix.unitaryGroup (Fin n) ℂ) → Frames G := fun u => ⟨fun τ => blk (u τ).1 * y.1 τ, invB u⟩
  let r' : K → ι → Matrix.unitaryGroup (Fin n) ℂ := fun k τ => ⟨r k τ, hr.uni k τ⟩
  have hr' : Continuous r' :=
    continuous_pi fun τ => Continuous.subtype_mk ((continuous_apply τ).comp hr.cont) _
  have hyk' : ∀ k, yk k = yU (r' k) := by
    intro k
    obtain ⟨kt, hb, ht⟩ := hyk k
    exact Subtype.ext (funext fun τ => by rw [ht τ, eq_blk (hb τ)])
  have hJk' : ∀ k, Jk k = (jU (r' k)).1 := by
    intro k
    funext z'
    refine hJk k (zU (r' k) z') z' fun τ => ?_
    show z'.1 τ = r k τ * ((r k τ)ᴴ * z'.1 τ)
    rw [← mul_assoc, (uniH (hr.uni k τ)).1, one_mul]
  have hjU : Continuous jU := by
    refine Continuous.subtype_mk (continuous_pi fun z => ?_) _
    exact cont_val hJ (fun u τ => ((u τ).1)ᴴ * z.1 τ)
      (continuous_pi fun τ => ((continuous_apply τ).subtype_val.matrix_conjTranspose).matrix_mul
        continuous_const) (fun u τ => invH u z τ)
  have he : Continuous e := LinearMap.continuous_of_finiteDimensional e.toLinearMap
  have hint : ∀ Ψ ∈ ValC G lam, MeasureTheory.Integrable (fun k => Ψ (yk k) • e (jU (r' k))) ν := by
    intro Ψ hΨ
    have hH : Continuous fun u => Ψ (yU u) • e (jU u) := by
      refine Continuous.smul (f := fun u => Ψ (yU u)) (g := fun u => e (jU u)) ?_ (he.comp hjU)
      show Continuous fun u => Ψ ⟨fun τ => blk (u τ).1 * y.1 τ, invB u⟩
      have hc1 : Continuous fun (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (τ : ι) => blk (u τ).1 * y.1 τ := cont_blkfam y.1
      exact cont_val (X := ι → Matrix.unitaryGroup (Fin n) ℂ) (M := fun (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (τ : ι) => blk (u τ).1 * y.1 τ) hΨ hc1 invB
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hH.continuousOn
    have hf : (fun k => Ψ (yk k) • e (jU (r' k))) = (fun u => Ψ (yU u) • e (jU u)) ∘ r' := by
      funext k; simp only [Function.comp_apply, hyk']
    rw [hf]
    exact MeasureTheory.Integrable.of_bound (hH.comp hr').aestronglyMeasurable C
      (MeasureTheory.ae_of_all _ fun k => hC _ (Set.mem_univ _))
  let A : ValC G lam →ₗ[ℂ] (Fin (Module.finrank ℂ (ValC G' sg)) → ℂ) :=
    { toFun := fun Ψ => ∫ k, Ψ.1 (yk k) • e (jU (r' k)) ∂ν
      map_add' := fun Ψ Ψ' => by
        simp only [Submodule.coe_add, Pi.add_apply, add_smul]
        exact MeasureTheory.integral_add (hint Ψ.1 Ψ.2) (hint Ψ'.1 Ψ'.2)
      map_smul' := fun c Ψ => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact MeasureTheory.integral_smul c _ }
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (ValC G lam).subtype (Submodule.ker_subtype _)
  have hpΨ : ∀ Ψ (h : Ψ ∈ ValC G lam), p Ψ = ⟨Ψ, h⟩ := fun Ψ h => LinearMap.congr_fun hp ⟨Ψ, h⟩
  let T : (Frames G → ℂ) →ₗ[ℂ] (Frames G' → ℂ) := (ValC G' sg).subtype ∘ₗ e.symm.toLinearMap ∘ₗ A ∘ₗ p
  have key : ∀ Ψ ∈ ValC G lam, ∀ ℓ : (Frames G' → ℂ) →ₗ[ℂ] ℂ, ℓ (T Ψ) = ∫ k, Ψ (yk k) * ℓ (Jk k) ∂ν := by
    intro Ψ hΨ ℓ
    let L := (ℓ ∘ₗ (ValC G' sg).subtype ∘ₗ e.symm.toLinearMap).toContinuousLinearMap
    have h1 : ℓ (T Ψ) = L (A ⟨Ψ, hΨ⟩) := by
      simp only [T, L, LinearMap.coe_comp, Function.comp_apply, hpΨ Ψ hΨ, LinearMap.coe_toContinuousLinearMap']
    rw [h1]
    show L (∫ k, Ψ (yk k) • e (jU (r' k)) ∂ν) = _
    rw [← L.integral_comp_comm (hint Ψ hΨ)]
    congr 1
    funext k
    simp only [L, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp, Function.comp_apply, map_smul,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.subtype_apply, smul_eq_mul, hJk']
  have hT : BrEqv rfl G G' lam sg T := by
    refine ⟨fun Ψ _ => Submodule.coe_mem _, ?_⟩
    intro k0 kt0 hk0 hkt0 Ψ hΨ Ψ' hΨ' z z' hzz'
    have hΨ'm : Ψ' ∈ ValC G lam := by
      refine stab Ψ hΨ kt0 Ψ' hΨ' fun τ => ?_
      rw [(hkt0 τ).det, mul_one]
      exact Matrix.isUnit_det_of_left_inverse (uniH (hk0 τ)).2
    obtain ⟨k1, hk1⟩ := hr.onto k0 hk0
    have e1 : T Ψ' z = ∫ k, Ψ' (yk k) * Jk k z ∂ν := by
      have := key Ψ' hΨ'm (LinearMap.proj z); simpa using this
    have e2 : T Ψ z' = ∫ k, Ψ (yk k) * Jk k z' ∂ν := by
      have := key Ψ hΨ (LinearMap.proj z'); simpa using this
    rw [e1, e2]
    have p1 : ∀ k, Ψ' (yk k) * Jk k z = Ψ (yk (k1 * k)) * Jk (k1⁻¹ * (k1 * k)) z := by
      intro k
      rw [inv_mul_cancel_left]
      congr 1
      refine hΨ' _ _ fun τ => ?_
      rw [hyk', hyk']
      show blk (r (k1 * k) τ) * y.1 τ = kt0 τ * (blk (r k τ) * y.1 τ)
      rw [hr.mul, blk_mul, hk1, eq_blk (hkt0 τ), mul_assoc]
    have p2 : ∀ k, Jk (k1⁻¹ * k) z = Jk k z' := by
      intro k
      rw [hJk', hJk']
      show J (zU (r' (k1⁻¹ * k)) z) = J (zU (r' k) z')
      congr 1
      refine Subtype.ext (funext fun τ => ?_)
      show (r (k1⁻¹ * k) τ)ᴴ * z.1 τ = (r k τ)ᴴ * z'.1 τ
      rw [hr.mul, Matrix.conjTranspose_mul, r_inv_H hr, hzz' τ, ← hk1, mul_assoc]
    simp_rw [p1]
    rw [MeasureTheory.integral_mul_left_eq_self (fun k => Ψ (yk k) * Jk (k1⁻¹ * k) z) k1]
    simp_rw [p2]
  obtain ⟨c, hc⟩ := GlobalTheory.T.branching_multiplicityOne_unitary_families ι (n + 1) n rfl G G' lam sg hI T₀ hT₀ hne T hT
  refine ⟨c, fun Ψ hΨ ℓ => ?_⟩
  have := key Ψ hΨ ℓ
  rw [hc Ψ hΨ, map_smul, smul_eq_mul] at this
  refine Eq.trans ?_ this.symm
  congr 1
  funext k
  ring

end GlobalTheory.KJAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrime
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open NumberField IsDedekindDomain GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.FinPl ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le_unif (q : Unif k) {x : k} (hx : valuation k x < 1) :
    valuation k x ≤ valuation k ((q.1 : 𝒪[k]) : k) := by
  have hx' : x ∈ 𝒪[k] := hx.le
  have hm : (⟨x, hx'⟩ : 𝒪[k]) ∈ maximalIdeal 𝒪[k] := by
    rw [mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    exact hx
  rw [q.2.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
  obtain ⟨c, hc⟩ := hm
  have h : x = (c : k) * ((q.1 : 𝒪[k]) : k) := by
    have := congrArg (fun z : 𝒪[k] => (z : k)) hc
    simpa using this.symm
  rw [h, Valuation.map_mul]
  have hc1 : valuation k (c : k) ≤ 1 := c.2
  exact (mul_le_mul_of_nonneg_right hc1 zero_le').trans_eq (one_mul _)

theorem val_unif_lt_one (q : Unif k) : valuation k ((q.1 : 𝒪[k]) : k) < 1 :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 q.2.not_isUnit

theorem val_unif_pos (q : Unif k) : 0 < valuation k ((q.1 : 𝒪[k]) : k) := by
  rw [zero_lt_iff, Valuation.ne_zero_iff]
  exact fun h => q.2.ne_zero (Subtype.ext h)

variable {D : D7}

theorem val_prF_le_one (p : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (c : Formalism.L2.Herm.intAf D.host.F D.host.E) : valuation k (p.prF he c.1) ≤ 1 :=
  (p.prF_mem_iff he c.1).2 (mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D p.e PP he).1 c.2)

theorem val_lt_of_mem_idS_of_forall (p : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}
    (he : Formalism.L2.NTheta.IsIdemAt p.e PP) {I : Ideal (𝓞 D.host.E)} {γ : ValueGroupWithZero k} (hγ : 0 < γ)
    (hI : ∀ a ∈ I, valuation k (p.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E a : EAf D)) < γ)
    {s : Formalism.L2.Herm.intAf D.host.F D.host.E} (hs : s ∈ Formalism.L2.DIV.idS D.host.F I) :
    valuation k (p.prF he s.1) < γ := by
  refine Submodule.span_induction (p := fun s _ => valuation k (p.prF he s.1) < γ) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨a, ha, rfl⟩
    exact hI a ha
  · simpa using hγ
  · intro x y _ _ hx hy
    rw [Subring.coe_add, map_add]
    exact Valuation.map_add_lt _ hx hy
  · intro c x _ hx
    rw [smul_eq_mul, Subring.coe_mul, map_mul, Valuation.map_mul]
    exact (mul_le_mul_of_nonneg_right (p.val_prF_le_one he c) zero_le').trans_lt (by rwa [one_mul])

theorem val_eq_unif_and_unit : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∀ t t' : 𝓞 D.host.E, t ∈ PP.asIdeal → t ∉ PP.asIdeal ^ 2 → t' ∉ PP.asIdeal →
    (∃ q : Unif k, valuation k (p.pr (incA D (t : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k)) ∧
      valuation k (p.pr (incA D (t' : D.host.E))) = 1 := by
  intro D k _ _ _ _ p PP he t t' ht ht2 ht'
  let f : 𝓞 D.host.E →+* k :=
    (p.prF he).comp ((Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.comp (Formalism.L2.DIV.oToS D.host.F D.host.E))
  have hf : ∀ x : 𝓞 D.host.E, f x = p.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E x : EAf D) := fun _ => rfl
  have hf' : ∀ x : 𝓞 D.host.E, p.pr (incA D (x : D.host.E)) = f x := fun x =>
    (p.prF_toEAf he (incA D (x : D.host.E))).symm
  have hle : ∀ x, valuation k (f x) ≤ 1 := fun x => p.val_prF_le_one he _
  have hlt : ∀ x, x ∈ PP.asIdeal ↔ valuation k (f x) < 1 := fun x => p.mem_iff_val_lt he x
  rw [hf', hf']
  refine ⟨?_, le_antisymm (hle _) (not_lt.1 fun h => ht' ((hlt _).2 h))⟩
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  refine ⟨q, le_antisymm (val_le_unif q ((hlt _).1 ht)) (not_lt.1 fun hlt' => ?_)⟩
  set γ := valuation k ((q.1 : 𝒪[k]) : k) with hγ
  have hγ0 : 0 < γ := val_unif_pos q

  have hPP : Ideal.span {t} ⊔ PP.asIdeal ^ 2 = PP.asIdeal := by
    have h := Ideal.eq_prime_pow_of_succ_lt_of_le (P := PP.asIdeal) (I := Ideal.span {t} ⊔ PP.asIdeal ^ 2) (i := 1)
      PP.ne_bot (lt_of_le_of_ne le_sup_right fun h => ht2 (by
        rw [show (2 : ℕ) = 1 + 1 from rfl, h]
        exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self t)))
      (by
        rw [pow_one]
        exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 ht) (Ideal.pow_le_self two_ne_zero))
    rwa [pow_one] at h
  have hsq : ∀ a ∈ PP.asIdeal ^ 2, valuation k (f a) < γ := by
    intro a ha
    rw [pow_two] at ha
    refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · rw [map_mul, Valuation.map_mul]
      calc _ ≤ valuation k (f x) * γ := mul_le_mul_of_nonneg_left (val_le_unif q ((hlt _).1 hy)) zero_le'
        _ < 1 * γ := mul_lt_mul_of_pos_right ((hlt _).1 hx) hγ0
        _ = γ := one_mul _
    · rw [map_add]; exact Valuation.map_add_lt _ hx hy
  have hall : ∀ a ∈ PP.asIdeal, valuation k (f a) < γ := by
    intro a ha
    rw [← hPP] at ha
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_add]
    refine Valuation.map_add_lt _ ?_ (hsq y hy)
    rw [map_mul, Valuation.map_mul]
    exact (mul_le_mul_of_nonneg_right (hle c) zero_le').trans_lt (by rwa [one_mul])

  have hs : toEAf D (p.sec ((q.1 : 𝒪[k]) : k)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart ((p.int_iff _).1 q.1.2)
  let s : Formalism.L2.Herm.intAf D.host.F D.host.E := ⟨_, hs⟩
  have hsv : p.prF he s.1 = ((q.1 : 𝒪[k]) : k) := (p.prF_toEAf he _).trans (p.pr_sec _)
  obtain ⟨a, ha0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot s
  have ha : s - Formalism.L2.DIV.oToS D.host.F D.host.E a ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal := ha0
  have h2 := val_lt_of_mem_idS_of_forall p he hγ0 hall ha
  have e2 : ((s - Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      (s : EAf D) - ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
  rw [e2, RingHom.map_sub, hsv, ← hf] at h2
  have hγ1 : γ < 1 := val_unif_lt_one q
  have haP : a ∈ PP.asIdeal := (hlt a).2 (by simpa using Valuation.map_sub_lt _ hγ1 (h2.trans hγ1))
  have h3 := Valuation.map_add_lt _ h2 (hall a haP)
  rw [sub_add_cancel] at h3
  exact lt_irrefl _ h3

end GlobalTheory.FinPl.SplitPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VolumeSeeSawTupleLevelEqSphericalDivIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevIdx

theorem core {D : D7} (S : HSp D) (N : Lat S) (hN : IsSelfDualC S N) {r : ℕ} (k : Fin r → Type) [∀ i, Field (k i)]
    [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)]
    (q : (i : Fin r) → SplitPt D (k i)) (Y : Fin r → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (F : (i : Fin r) → GlobalTheory.LocMod.Frame (k i) S.rank (Y i))
    (hinj : Function.Injective fun i => (q i).v)
    (hlat : ∀ i, IntIn (q i) S (F i) N) (J : (i : Fin r) → Subgroup (GL (Y i) (k i)))
    (hJ : ∀ i, J i ≤ GlobalTheory.SplitWeil.KO (k i) (Y i)) (hJo : ∀ i, IsOpen (J i : Set (GL (Y i) (k i))))
    (μ : Measure (GfC S)) [μ.IsHaarMeasure] (U U' : Subgroup (GA D S)) (b : GA D S) (hb : b ∈ GfC S) (hU : U ≤ GfC S)
    (hUc : IsCompact (U : Set (GA D S))) (hUo : IsOpen ((U.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)))
    (hK : ∀ κ, InK S N (fun p => ∃ i, (q i).v = p) κ → κ ∈ U)
    (hM : ∀ g ∈ U, Moves S g N N (fun p => ∃ i, (q i).v = p))
    (hU' : ∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i (x : GL (Y i) (k i)), (mt S g).map (q i).pr = (F i).β * x.val * (F i).γ → x ∈ J i) :
    μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((J i).relIndex (GlobalTheory.SplitWeil.KO (k i) (Y i)) : ℝ) =
      μ.real {g | b * g.1 * b⁻¹ ∈ U} := by
  set φ : GA D S →* ((i : Fin r) → GL (Y i) (k i)) := MonoidHom.pi fun i => locHom (q i) S (F i) with hφ
  have hφi : ∀ g i, φ g i = locHom (q i) S (F i) g := fun _ _ => rfl
  have hU'' : ∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i, φ g i ∈ J i := by
    intro g
    rw [hU' g]
    refine and_congr_right fun _ => forall_congr' fun i => ?_
    refine ⟨fun h => h _ ((eq_locHom_iff _ _ _ _ _).2 rfl), fun h x hx => ?_⟩
    rw [(eq_locHom_iff _ _ _ _ _).1 hx]; exact h
  have hle : U' ≤ U := fun g hg => ((hU'' g).1 hg).1

  have hidx : U'.relIndex U = ∏ i, (J i).relIndex (GlobalTheory.SplitWeil.KO (k i) (Y i)) := by
    refine GlobalTheory.T.relIndex_eq_prod_relIndex_of_surjective_pi φ U U' (fun i => GlobalTheory.SplitWeil.KO (k i) (Y i)) J hJ ?_ ?_ hU''
    · intro g hg i
      exact GlobalTheory.T.mem_integralGL_split_place_of_carries_latticeCompletion (q i) S (F i) N _ ⟨i, rfl⟩ (hlat i) g (hM g hg) _ ((eq_locHom_iff _ _ _ _ _).2 rfl)
    · intro x hx
      obtain ⟨g, hg, hgx⟩ := GlobalTheory.T.exists_selfDual_stabilizer_with_prescribed_splitPlace_matrices S N hN k q Y F hinj hlat x hx
      refine ⟨g, hK g hg, funext fun i => ?_⟩
      rw [hφi]; exact ((eq_locHom_iff _ _ _ _ _).1 (hgx i)).symm

  let cj : GfC S →* GfC S :=
    { toFun := fun g => ⟨b * g.1 * b⁻¹, (GfC S).mul_mem ((GfC S).mul_mem hb g.2) ((GfC S).inv_mem hb)⟩
      map_one' := by ext1; simp
      map_mul' := fun g h => by ext1; simp [mul_assoc] }
  have hcj : Continuous cj :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have hcjb : Function.Bijective cj := by
    refine ⟨fun g h e => ?_, fun g => ⟨⟨b⁻¹ * g.1 * b, (GfC S).mul_mem ((GfC S).mul_mem ((GfC S).inv_mem hb) g.2) hb⟩, ?_⟩⟩
    · have := congrArg Subtype.val e
      ext1; simpa [cj] using this
    · ext1; simp [cj, mul_assoc]
  set H := (U.subgroupOf (GfC S)).comap cj
  set H' := (U'.subgroupOf (GfC S)).comap cj
  have eH : {g : GfC S | b * g.1 * b⁻¹ ∈ U} = (H : Set (GfC S)) := rfl
  have eH' : {g : GfC S | b * g.1 * b⁻¹ ∈ U'} = (H' : Set (GfC S)) := rfl
  have hHH' : H'.relIndex H = U'.relIndex U := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hcjb.2, Subgroup.relIndex_subgroupOf hU]

  have hHc : IsCompact (H : Set (GfC S)) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff]
    have e : Subtype.val '' (H : Set (GfC S)) = (fun g => b⁻¹ * g * b) '' (U : Set (GA D S)) := by
      ext y; constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨b * g.1 * b⁻¹, hg, by simp [mul_assoc]⟩
      · rintro ⟨u, hu, rfl⟩
        refine ⟨⟨b⁻¹ * u * b, (GfC S).mul_mem ((GfC S).mul_mem ((GfC S).inv_mem hb) (hU hu)) hb⟩, ?_, rfl⟩
        change b * (b⁻¹ * u * b) * b⁻¹ ∈ U
        simpa [mul_assoc] using hu
    convert hUc.image ((continuous_const.mul continuous_id).mul continuous_const) using 1
    exact e

  have hU'o : IsOpen ((U'.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) := by
    have e : ((U'.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) =
        ((U.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) ∩
          ⋂ i, (fun g : GfC S => locHom (q i) S (F i) g.1) ⁻¹' (J i : Set (GL (Y i) (k i))) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      rw [hU'']
      rfl
    rw [e]
    exact hUo.inter (isOpen_iInter_of_finite fun i =>
      (hJo i).preimage ((continuous_locHom (q i) S (F i)).comp continuous_subtype_val))
  have hH'o : IsOpen (H' : Set (GfC S)) := hU'o.preimage hcj
  have hH'H : H' ≤ H := fun g hg => hle hg
  rw [eH, eH', ← Nat.cast_prod, ← hidx, ← hHH']
  exact vol_mul_relIndex μ H H' hH'H hHc hH'o

end GlobalTheory.LevIdx

theorem GlobalTheory.LevIdx.vol_level_eq : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : GlobalTheory.QPl.QFam v t), F.Pins w → (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) → ∀ (μ : Measure (GfC (c.V j))), μ.IsHaarMeasure → ∀ (U U' : Subgroup (GA D (c.V j))) (b : GA D (c.V j)), b ∈ GfC _ → U ≤ GfC _ → IsCompact (U : Set (GA D (c.V j))) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (c.V j))) : Set (GfC (c.V j))) → (∀ κ, InK _ (v.N j) (· ∈ w.Q) κ → κ ∈ U) → (∀ g ∈ U, Moves _ g (v.N j) (v.N j) (· ∈ w.Q)) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i d hd x, (mt _ g).map (F.Q i).q.pr = ((F.Q i).FY j d hd).β * x.val * ((F.Q i).FY j d hd).γ → x ∈ ((F.Q i).T.lev j d hd).J) → μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((F.Q i).idx j : ℝ) = μ.real {g | b * g.1 * b⁻¹ ∈ U}) ∧ (IsSelfDualC c.T v.NT → (∀ i, IsOpen ((F.Q i).T.levTop.J : Set (GL (F.Q i).Z (F.Q i).k))) → ∀ (μ : Measure (GfC c.T)), μ.IsHaarMeasure → ∀ (U U' : Subgroup (GA D c.T)) (b : GA D c.T), b ∈ GfC _ → U ≤ GfC _ → IsCompact (U : Set (GA D c.T)) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC c.T)) : Set (GfC c.T)) → (∀ κ, InK _ v.NT (· ∈ w.Q) κ → κ ∈ U) → (∀ g ∈ U, Moves _ g v.NT v.NT (· ∈ w.Q)) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i (x : GL (F.Q i).Z (F.Q i).k), (mt _ g).map (F.Q i).q.pr = (F.Q i).FT.β * x.val * (F.Q i).FT.γ → x ∈ (F.Q i).T.levTop.J) → μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((F.Q i).idx D.R.m : ℝ) = μ.real {g | b * g.1 * b⁻¹ ∈ U}) := by
  intro D c v t w F hP
  have hQ : (· ∈ w.Q) = fun p => ∃ i, (F.Q i).q.v = p := funext fun p => propext (hP.places p)
  have hs : ∀ i, (F.Q i).s + 1 + 1 = D.R.m := fun i => (F.Q i).hs
  refine ⟨fun j hj hN μ hμ U U' b hb hU hUc hUo hK hM hU' => ?_, fun hN hTo μ hμ U U' b hb hU hUc hUo hK hM hU' => ?_⟩
  · let d : Fin F.r → ℕ := fun i => (F.Q i).s + 1 - j
    have hd : ∀ i, j + d i = (F.Q i).s + 1 := fun i => by have := hs i; simp only [d]; omega
    rw [hQ] at hK hM
    have key := GlobalTheory.LevIdx.core (c.V j) (v.N j) hN (fun i => (F.Q i).k) (fun i => (F.Q i).q) (fun i => (F.Q i).X j ⊕ Fin (d i))
      (fun i => (F.Q i).FY j (d i) (hd i)) hP.inj (fun i => (F.Q i).latY j (d i) (hd i))
      (fun i => ((F.Q i).T.lev j (d i) (hd i)).J) (fun i => (F.Q i).le j (d i) (hd i))
      (fun i => ((F.Q i).reg.2.2 j (d i) (hd i)).1) μ U U' b hb hU hUc hUo hK hM ?_
    · have e : ∀ i, (F.Q i).idx j = (((F.Q i).T.lev j (d i) (hd i)).J).relIndex (GlobalTheory.SplitWeil.KO (F.Q i).k _) :=
        fun i => (F.Q i).idx_mid j (d i) (hd i)
      simp only [e]
      exact key
    · intro g
      rw [hU' g]
      refine and_congr_right fun _ => forall_congr' fun i => ⟨fun h x hx => h (d i) (hd i) x hx, fun h d' hd' x hx => ?_⟩
      obtain rfl : d' = d i := by have := hd i; omega
      exact h x hx
  · rw [hQ] at hK hM
    have key := GlobalTheory.LevIdx.core c.T v.NT hN (fun i => (F.Q i).k) (fun i => (F.Q i).q) (fun i => (F.Q i).Z)
      (fun i => (F.Q i).FT) hP.inj (fun i => (F.Q i).latT)
      (fun i => (F.Q i).T.levTop.J) (fun i => (F.Q i).leT) hTo μ U U' b hb hU hUc hUo hK hM hU'
    have e : ∀ i, (F.Q i).idx D.R.m = ((F.Q i).T.levTop.J).relIndex (GlobalTheory.SplitWeil.KO (F.Q i).k _) :=
      fun i => by rw [← hs i]; exact (F.Q i).idx_top
    simp only [e]
    exact key

end
end

