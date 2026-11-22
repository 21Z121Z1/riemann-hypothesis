import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousActP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0414
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfLine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0555
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0551
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0530
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvTrUnitaryOne
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped InnerProductSpace ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.CoefIso

theorem bcVV_rhoVr {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
    (σ : K →+* ℂ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (g : GL (Fin n) E) (v : VV K lam) :
    GlobalTheory.CoefSpace.bcVV σ lam (rhoVr emb lam g v) =
      rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) (GlobalTheory.CoefSpace.bcVV σ lam v) := by
  apply Subtype.ext
  show MvPolynomial.map σ (actP lam (invTrK (embGL emb g)) v.1) =
    actP lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) (MvPolynomial.map σ v.1)
  rw [GlobalTheory.CoefSpace.map_actP]
  congr 2

theorem invTr_unitary_one {n : ℕ} (U : GL (Fin n) ℂ) (hU : (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * U = 1) :
    ((inside₂ ℂ n U : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * (1 : Matrix (Fin n) (Fin n) ℂ) *
      ((inside₂ ℂ n U : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  have hi : ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = (U : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
    calc ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
        = ((U : Matrix (Fin n) (Fin n) ℂ)ᴴ * U) * ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
          rw [hU, Matrix.one_mul]
      _ = (U : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  show (((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ)ᴴ * 1 * ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ = 1
  have e : (((U : Matrix (Fin n) (Fin n) ℂ)ᴴ)ᵀ)ᴴ = (U : Matrix (Fin n) (Fin n) ℂ)ᵀ := by
    ext i j
    simp
  rw [hi, Matrix.mul_one, e, ← Matrix.transpose_mul, hU, Matrix.transpose_one]

theorem ratMat_unitary {D : D7} (V : HSp D) (hg : V.gram = 1) (γ : GQ V) (γE : GL (Fin V.rank) D.host.E)
    (h : Bridge.IsRatMat V γ γE) (φ : D.host.E →+* ℂ) :
    ((Formalism.UG.bc φ γE : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ *
      ((Formalism.UG.bc φ γE : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 1 := by
  obtain ⟨γ, ⟨g, hgU, hgm⟩⟩ := γ
  have e1 : Formalism.UG.bc (incA D) g = Formalism.UG.bc (incA D) γE := hgm.trans h
  have e2 : g = γE := Units.ext (Matrix.ext fun i j =>
    (Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F))
      (congrArg (fun u => (Units.val u) i j) e1))
  subst e2
  have hu : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram := hgU
  rw [hg, Matrix.mul_one] at hu
  have hc : ((g : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map φ)ᴴ =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).map φ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
    exact (D.sp.cm.cmUnram.2.1 φ _).symm
  rw [bc_coe, hc, ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]

set_option maxHeartbeats 1000000 in

theorem coef_iso : ∀ (D : D7) (V : HSp D) (n : ℕ), V.rank = n → V.gram = 1 → ∀ (c : CoefA V), c.Is → ∀ {K ι : Type} [Field K] [NumberField K] [Fintype ι] (σ : K →+* ℂ) (emb : ι → (D.host.E →+* K)) (lam : ι → DomWeight n) (c0 : VV K lam →ₛₗ[σ] c.W), Nonempty (VVIdx lam) →
  (∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) (g : GL (Fin n) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g → ∀ v, c0 (rhoVr emb lam g v) = c.coef.ρ γ (c0 v)) →
  (LinearIndependent ℂ fun i => c0 (bVV K lam i)) →
  ∃ (e : VV ℂ lam ≃ₗ[ℂ] c.W) (s : ℝ), 0 < s ∧ (∀ v, c0 v = (s : ℂ) • e (GlobalTheory.CoefSpace.bcVV σ lam v)) ∧
    (∀ x y, inner ℂ (e x) (e y) = pairK lam (fun _ => 1) x y) ∧
    ∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) (g : GL (Fin n) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g →
      ∀ x, e (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) x) = c.coef.ρ γ (e x) := by
  intro D V n hn hg c hc K ι _ _ _ σ emb lam c0 hne hint hli
  subst hn
  classical
  have hMat : ∀ γ : GQ V, ∃ γE, Bridge.IsRatMat V γ γE ∧ MatEq γE γE := fun γ => by
    obtain ⟨γE, h⟩ := GlobalTheory.Mem.StdUnique.exists_ratMat γ
    exact ⟨γE, h, rfl, fun i j i' j' hi hj => by rw [Fin.ext hi, Fin.ext hj]⟩
  have hmem : ∀ v, c0 v ∈ Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range (bVV K lam)) := by rw [(bVV K lam).span_eq]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  obtain ⟨i₀⟩ := hne
  have htop : Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) = ⊤ := by
    refine (GlobalTheory.Mem.StdUnique.bot_or_top c hc _ fun γ hγ w hw => ?_).resolve_left fun h0 => ?_
    · obtain ⟨γE, h1, h2⟩ := hMat ⟨γ, hγ⟩
      have hle : (Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i))).map (c.ρ γ) ≤
          Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) := by
        rw [Submodule.map_span_le]
        rintro _ ⟨i, rfl⟩
        rw [show c.ρ γ (c0 (bVV K lam i)) = c.coef.ρ ⟨γ, hγ⟩ (c0 (bVV K lam i)) from rfl,
          ← hint ⟨γ, hγ⟩ γE γE h1 h2]
        exact hmem _
      exact hle ⟨w, hw, rfl⟩
    · have := hmem (bVV K lam i₀)
      rw [h0, Submodule.mem_bot] at this
      exact hli.ne_zero i₀ this
  let b1 : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) :=
    Module.Basis.mk (GlobalTheory.CoefSpace.bcVV_indep σ lam) (GlobalTheory.CoefSpace.bcVV_span σ lam).ge
  let b2 : Module.Basis (VVIdx lam) ℂ c.W := Module.Basis.mk hli htop.ge
  have hb1 : ∀ i, b1 i = GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i) := fun i => Module.Basis.mk_apply _ _ i
  have hb2 : ∀ i, b2 i = c0 (bVV K lam i) := fun i => Module.Basis.mk_apply _ _ i
  obtain ⟨e0, he0b⟩ : ∃ e0 : VV ℂ lam ≃ₗ[ℂ] c.W, ∀ i, e0 (b1 i) = b2 i :=
    ⟨b1.equiv b2 (Equiv.refl _), fun i => by simp⟩
  have he0 : ∀ v, e0 (GlobalTheory.CoefSpace.bcVV σ lam v) = c0 v := by
    intro v
    have : (e0.toLinearMap.comp (GlobalTheory.CoefSpace.bcVV σ lam) : VV K lam →ₛₗ[σ] c.W) = c0 :=
      (bVV K lam).ext fun i => by
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← hb1, he0b, hb2]
    exact LinearMap.congr_fun this v
  have hR : ∀ (γ : GQ V) (γE g : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g → ∀ x,
      e0 (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) x) = c.ρ γ (e0 x) := by
    intro γ γE g h1 h2 x
    have : e0.toLinearMap.comp (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g)) =
        (c.ρ γ).comp e0.toLinearMap := b1.ext fun i => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hb1, ← bcVV_rhoVr, LinearEquiv.coe_coe, he0, he0,
        hint γ γE g h1 h2]
      rfl
    exact LinearMap.congr_fun this x
  have hP : ∀ (γ : GQ V) (γE g : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g → ∀ x y : VV ℂ lam,
      pairK lam (fun _ => 1) (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) x)
        (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) y) = pairK lam (fun _ => 1) x y := by
    intro γ γE g h1 h2
    obtain rfl : γE = g := Units.ext (Matrix.ext fun i j => h2.2 i j i j rfl rfl)
    exact pairInv ℂ ι V.rank lam (fun _ => 1) _ fun τ =>
      invTr_unitary_one (Formalism.UG.bc (σ.comp (emb τ)) γE) (ratMat_unitary V hg γ γE h1 _)
  have hgr : GlobalTheory.CoefSpace.gramOf (fun _ : ι => (1 : GL (Fin V.rank) ℂ)) = fun _ => 1 := by
    funext τ
    simp [GlobalTheory.CoefSpace.gramOf]
  let S : c.W →ₗ[ℂ] GlobalTheory.CoefSpace.HV lam (fun _ => (1 : GL (Fin V.rank) ℂ)) := e0.symm.toLinearMap
  have hS : ∀ w, S w = e0.symm w := fun _ => rfl
  let T : Module.End ℂ c.W := (LinearMap.adjoint S).comp S
  have hT : ∀ w w', inner ℂ w (T w') = pairK lam (fun _ => 1) (e0.symm w) (e0.symm w') := by
    intro w w'
    show inner ℂ w (LinearMap.adjoint S (S w')) = _
    rw [LinearMap.adjoint_inner_right, GlobalTheory.CoefSpace.inner_HV, hgr]
    rfl
  have hBinv : ∀ (γ : GQ V) a b, pairK lam (fun _ => 1) (e0.symm (c.ρ γ a)) (e0.symm (c.ρ γ b)) =
      pairK lam (fun _ => 1) (e0.symm a) (e0.symm b) := by
    intro γ a b
    obtain ⟨γE, h1, h2⟩ := hMat γ
    have key : ∀ a, e0.symm (c.ρ γ a) = rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) γE) (e0.symm a) :=
      fun a => by rw [LinearEquiv.symm_apply_eq, hR γ γE γE h1 h2, LinearEquiv.apply_symm_apply]
    rw [key, key, hP γ γE γE h1 h2]
  have hcomm : ∀ (γ : GQ V) x, T (c.ρ γ x) = c.ρ γ (T x) := by
    intro γ x
    refine ext_inner_left ℂ fun w => ?_
    have hinv : c.ρ γ (c.ρ (γ⁻¹ : GQ V) w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, map_one,
        Module.End.one_apply]
    calc inner ℂ w (T (c.ρ γ x)) = inner ℂ (c.ρ γ (c.ρ (γ⁻¹ : GQ V) w)) (T (c.ρ γ x)) := by rw [hinv]
      _ = pairK lam (fun _ => 1) (e0.symm (c.ρ (γ⁻¹ : GQ V) w)) (e0.symm x) := by rw [hT, hBinv]
      _ = inner ℂ (c.ρ (γ⁻¹ : GQ V) w) (T x) := (hT _ _).symm
      _ = inner ℂ (c.ρ γ (c.ρ (γ⁻¹ : GQ V) w)) (c.ρ γ (T x)) := (hc.2.1 _ _ _).symm
      _ = inner ℂ w (c.ρ γ (T x)) := by rw [hinv]
  obtain ⟨μ, hμ⟩ := GlobalTheory.Mem.RowCoord.scalar_of_comm_rat c hc T hcomm
  have hx₀ : GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀) ≠ 0 := by
    rw [← hb1]
    exact b1.ne_zero i₀
  have hpos := GlobalTheory.CoefSpace.pairK_pos lam (fun _ => 1) _ hx₀
  rw [hgr] at hpos
  have h1 := hT (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))) (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀)))
  have hsq : inner ℂ (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))) (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))) =
      ((‖e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hμ, inner_smul_right, LinearEquiv.symm_apply_apply, hsq] at h1
  rw [← h1] at hpos
  have hn : 0 < ‖e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (e0.map_ne_zero_iff.2 hx₀)) 2
  obtain ⟨hre, him⟩ := Complex.lt_def.1 hpos
  simp only [Complex.re_mul_ofReal, Complex.im_mul_ofReal, Complex.zero_re, Complex.zero_im] at hre him
  have hm : 0 < μ.re := (pos_iff_pos_of_mul_pos hre).2 hn
  have hμr : ((μ.re : ℝ) : ℂ) = μ := Complex.ext rfl (by
    rw [Complex.ofReal_im]
    exact ((mul_eq_zero.1 him.symm).resolve_right hn.ne').symm)
  have hr : 0 < Real.sqrt μ.re := Real.sqrt_pos.2 hm
  have hr0 : ((Real.sqrt μ.re : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  obtain ⟨e, he⟩ : ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W, ∀ x, e x = ((Real.sqrt μ.re : ℝ) : ℂ) • e0 x :=
    ⟨e0.trans (LinearEquiv.smulOfNeZero ℂ c.W _ hr0), fun _ => rfl⟩
  refine ⟨e, (Real.sqrt μ.re)⁻¹, inv_pos.2 hr, fun v => ?_, fun x y => ?_, fun γ γE g h1 h2 x => ?_⟩
  · rw [he, he0, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
  · rw [he, he, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hm.le, hμr, ← inner_smul_right, ← hμ, hT, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
  · rw [he, he, hR γ γE g h1 h2]
    exact ((c.ρ γ).map_smul _ _).symm

end GlobalTheory.Mem.CoefIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormsLatticeDefiniteLatticeBaseChangeExtende
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftLat0

section Key

open Formalism.IndefR.Cx

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']

theorem map_mulVec_fun (φ : K →+* K') {m n : ℕ} (θ : Matrix (Fin m) (Fin n) K) (x : Fin n → K) :
    (fun k => φ ((θ *ᵥ x) k)) = θ.map φ *ᵥ fun k => φ (x k) := by
  funext k; exact RingHom.map_mulVec φ θ x k

theorem cpt_single (σ : K' →+* ℂ) {n : ℕ} (k : Fin n) : cpt σ (Pi.single k (1 : K')) = Pi.single k 1 := by
  funext i; by_cases h : i = k
  · subst h; simp [cpt]
  · simp [cpt, Pi.single_apply, h]

theorem kOf_apply (σ : K' →+* ℂ) (a : K') : kOf σ (σ a) = a := by
  classical
  have h : ∃ b : K', σ b = σ a := ⟨a, rfl⟩
  unfold kOf
  rw [dif_pos h]
  exact σ.injective h.choose_spec

theorem matLat_relMat_of_heq (φ : K →+* K') (σ : K →+* ℂ) (σ' : K' →+* ℂ)
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] {dW dW' dZ dZ' : ℕ}
    (w0 : (Fin dW → ℂ) →ₗ[ℂ] W) (t0 : (Fin dZ → ℂ) →ₗ[ℂ] W) (w0' : (Fin dW' → ℂ) →ₗ[ℂ] W')
    (t0' : (Fin dZ' → ℂ) →ₗ[ℂ] W') (θ : Matrix (Fin dW) (Fin dZ) K) (G : Matrix (Fin dW') (Fin dW) K')
    (N : Matrix (Fin dZ') (Fin dZ) K') (hN : Function.Bijective N.mulVec)
    (hG : ∀ y : Fin dW → K, HEq (w0' (cpt σ' (G *ᵥ fun k => φ (y k)))) (w0 (cpt σ y)))
    (hNc : ∀ x : Fin dZ → K, HEq (t0' (cpt σ' (N *ᵥ fun k => φ (x k)))) (t0 (cpt σ x)))
    (hR : ∀ x : Fin dZ → K, w0 (cpt σ (θ *ᵥ x)) = t0 (cpt σ x)) (hI : Function.Injective w0')
    (L : Submodule (𝓞 K) (Fin dZ → K)) :
    Formalism.DivisionValues.matLat (kMat σ' (relMat w0' t0'))
              (Submodule.span (𝓞 K') ((fun x : Fin dZ → K => N *ᵥ fun k => φ (x k)) '' (L : Set (Fin dZ → K)))) =
      Submodule.span (𝓞 K') ((fun x : Fin dW → K => G *ᵥ fun k => φ (x k)) ''
        (Formalism.DivisionValues.matLat θ L : Set (Fin dW → K))) := by
  classical
  set eN := LinearEquiv.ofBijective (Matrix.mulVecLin N) hN with heN
  have hNe : ∀ v, eN v = N *ᵥ v := fun v => rfl
  have hb : ∀ x : Fin dZ → K, t0' (cpt σ' (N *ᵥ fun k => φ (x k))) =
      w0' (cpt σ' (G *ᵥ (θ.map φ *ᵥ fun k => φ (x k)))) := by
    intro x
    rw [← map_mulVec_fun φ θ x]
    exact eq_of_heq ((hNc x).trans ((heq_of_eq (hR x)).symm.trans (hG (θ *ᵥ x)).symm))

  have hL : ((t0'.comp (cptL σ' dZ')).comp N.mulVecLin : (Fin dZ → K') →ₛₗ[σ'] W') =
      (w0'.comp (cptL σ' dW')).comp (G.mulVecLin.comp (θ.map φ).mulVecLin) := by
    refine (Pi.basisFun K' (Fin dZ)).ext fun i => ?_
    have hs : (Pi.basisFun K' (Fin dZ)) i = fun k => φ ((Pi.single i (1 : K) : Fin dZ → K) k) := by
      rw [Pi.basisFun_apply]; funext k; by_cases h : k = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [hs]
    simpa [cptL, Matrix.mulVecLin_apply] using hb (Pi.single i 1)

  have hθ : ∀ u : Fin dZ' → K', kMat σ' (relMat w0' t0') *ᵥ u = G *ᵥ (θ.map φ *ᵥ eN.symm u) := by
    have hk : ∀ k : Fin dZ', ∀ i, kMat σ' (relMat w0' t0') i k = (G *ᵥ (θ.map φ *ᵥ eN.symm (Pi.single k 1))) i := by
      intro k i
      set v := G *ᵥ (θ.map φ *ᵥ eN.symm (Pi.single k 1)) with hv
      have hw : w0' (cpt σ' v) = t0' (Pi.single k 1) := by
        have h1 := congrArg (fun f => f (eN.symm (Pi.single k 1))) hL
        simp only [LinearMap.comp_apply, cptL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply] at h1
        have h2 : N *ᵥ eN.symm (Pi.single k 1) = Pi.single k 1 := by
          rw [← hNe]; exact eN.apply_symm_apply (Pi.single k 1)
        rw [h2, cpt_single] at h1
        exact h1.symm
      have hex : ∃ y, w0' y = t0' (Pi.single k 1) := ⟨_, hw⟩
      have hsol : solve w0' (t0' (Pi.single k 1)) = cpt σ' v := by
        apply hI
        unfold solve
        rw [dif_pos hex]
        exact hex.choose_spec.trans hw.symm
      show kOf σ' (solve w0' (t0' (Pi.single k 1)) i) = v i
      rw [hsol]
      exact kOf_apply σ' (v i)
    have hlin : (kMat σ' (relMat w0' t0')).mulVecLin =
        G.mulVecLin.comp ((θ.map φ).mulVecLin.comp eN.symm.toLinearMap) := by
      refine (Pi.basisFun K' (Fin dZ')).ext fun k => ?_
      rw [Pi.basisFun_apply]
      funext i
      simp only [Matrix.mulVecLin_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← hk k i, Matrix.mulVec_single_one]
      rfl
    intro u
    exact congrArg (fun f => f u) hlin

  unfold Formalism.DivisionValues.matLat
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
  rw [hθ, map_mulVec_fun φ θ x]
  congr 2
  rw [← hNe]; exact eN.symm_apply_apply (fun k => φ (x k))

end Key

set_option maxHeartbeats 4000000 in

theorem liftFormsLattice_definiteLattice_baseChange_extended_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ G : Matrix (Fin ((s0Of z'.R z'.F).dW j')) (Fin ((s0Of z.R z.F).dW j)) (w'.st Z').toD7.what₂.LL, Function.Bijective G.mulVec ∧
          (s0Of z'.R z'.F).M j' = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' (((s0Of z.R z.F).M j : Submodule (𝓞 (w.st Z).toD7.what₂.LL) (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)) : Set (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL))) ∧
          Formalism.DivisionValues.matLat ((s0Of z'.R z'.F).θ j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) =
            Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' ((Formalism.DivisionValues.matLat ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) : Submodule (𝓞 (w.st Z).toD7.what₂.LL) (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)) : Set (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)))) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (StepW.and (GlobalTheory.T.extendedData_liftFormsLattice_baseLevel_baseChange_alt h1 h2 h3 h4 h5 h6 h7) (GlobalTheory.T.definiteLiftLattice_baseChange_extendedData h1 h2 h3 h4 h5 h6 h7))
    (StepW.and (GlobalTheory.T.baseLevelLiftMatrix_solves_relation_extendedData_alt h1 h2 h3 h4 h5 h6 h7) (GlobalTheory.T.baseLevelComplexPoints_injective_extendedData_alt h1 h2 h3 h4 h5 h6 h7))) (StepW.of_all ?_)
  intro K B' f' T' w' _ _ H B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  obtain ⟨G, hGb, hM, hGc⟩ := H.1.1 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  obtain ⟨N, hNb, hTl, hNc⟩ := H.1.2 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  have hR := H.2.1 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  have hI := H.2.2 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  refine ⟨G, hGb, hM, ?_⟩
  rw [hTl]
  exact matLat_relMat_of_heq φ _ _ _ _ _ _ _ G N hNb hGc hNc hR hI _

end GlobalTheory.Mem.R3.LiftLat0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimeLevelIffReductionLevelConjugateCharact
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

noncomputable section

namespace GlobalTheory.SeeSaw.TwLev

theorem lev_iffQ : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
    (hc : CMData F E) {n n' : ℕ} (e : n' = n) [NeZero n] {J' : Matrix (Fin n') (Fin n') E} {J : Matrix (Fin n) (Fin n) E},
    J' = 1 → J = 1 → ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad),
    S.Lb = Formalism.L2.Col.stdLat E n → ∀ {r t s : ℕ} (h : r ≤ n) (h' : r ≤ n'), 0 < t → n = r + s * t →
    ∀ {SG Q : Finset (Pl E)} (P : LevFam E K r SG) (χ : ∀ w : SG, ℕ → (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ) (emb : K →+* ℂ)
    (ξ : ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ),
    RdLevOn hc Set.univ S.U S.chi (parFam h t s P χ) emb Q (fun _ => blockTri (blk2 r))
      (fun P => (ξ P.1).comp (blkDet (blk2 r) 1)) →
    ∀ (P' : LevelP SG r ℂ) (cg : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ),
    (∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (P w).H) →
    (∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (P w).H), ((P'.chi g : ℂˣ) : ℂ) = ∏ w, emb (((P w).lam ⟨g.1 w, hg w⟩ : Kˣ) : K)) →
    (∀ c (w : SG) a, ((cg (c + 1) w.1 a : ℂˣ) : ℂ) = emb ((χ w c a : Kˣ) : K)) →
    ∀ (g : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)),
    (∀ i j, g.1 i j = y.1 (finCongr e i) (finCongr e j)) →
    (g ∈ lev hc J' 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ ↔ y ∈ S.U) ∧
      ∀ hy : y ∈ S.U, ((levFn 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ g : ℂˣ) : ℂ) = star ((S.chi ⟨y, hy⟩ : ℂˣ) : ℂ) := by
  intro F E K _ _ _ _ _ _ _ hc n n' e _ J' J hJ' hJ T f bad S hL r t s h h' ht hn SG Q P χ emb ξ hR P' cg hH hchi hcg g y hgy
  classical
  subst e hJ' hJ
  obtain rfl : g = y := Units.ext (Matrix.ext hgy)
  have hred : ∀ (hz : g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F))) (w : Pl E), redFn 1 w g = redAt 1 w ⟨g, hz⟩ :=
    fun hz w => extendOne_of_mem _ hz
  have hU : g ∈ S.U → g ∈ UAd hc n' ∧ g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) := fun hy => by
    obtain ⟨h1, h2⟩ := (S.U_eq g).1 hy
    refine ⟨h1, rll_St_of_loc n' g fun v => ⟨_, rll_put_mem_St n' v ?_, rll_put_self n' v _⟩⟩
    have := (S.Uloc_lev v (h2 v)).2
    rw [hL] at this
    exact this
  have e0 : g ∈ lev hc 1 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ ↔
      g ∈ lev hc 1 1 (parDat h t s P χ) ∧ ∀ PP ∈ Q, redFn 1 PP g ∈ blockTri (blk2 r) := by
    rw [mem_lev, mem_lev, mem_parLev, mem_parLev]
    constructor
    · rintro ⟨⟨a1, a2, a3, a4⟩, a5⟩
      exact ⟨⟨⟨a1, a2, a3, fun PP hP => absurd hP (Finset.notMem_empty PP)⟩, fun w _ => (hH _).1 a5 w⟩, a4⟩
    · rintro ⟨⟨⟨a1, a2, a3, -⟩, a5⟩, a4⟩
      exact ⟨⟨a1, a2, a3, a4⟩, (hH _).2 fun w => a5 w (Set.mem_univ w)⟩
  have e1 : g ∈ levU hc n' ∅ SG (parFam h t s P χ).grp ∧ (∀ PP ∈ Q, redFn 1 PP g ∈ blockTri (blk2 r)) ↔ g ∈ S.U := by
    rw [mem_levU_iff]
    constructor
    · rintro ⟨⟨h1, h2, -, h4⟩, hq⟩
      exact (hR g (Set.mem_univ g) h2 h1).1.2 ⟨fun w => hred h2 w.1 ▸ h4 w (Set.mem_univ w), fun PP => hred h2 PP.1 ▸ hq PP.1 PP.2⟩
    · intro hy
      obtain ⟨h1, h2⟩ := hU hy
      obtain ⟨a, b⟩ := (hR g (Set.mem_univ g) h2 h1).1.1 hy
      refine ⟨⟨h1, h2, fun P hP => absurd hP (Finset.notMem_empty P), fun w _ => ?_⟩, fun PP hP => ?_⟩
      · have := a w
        rwa [← hred h2] at this
      · have := b ⟨PP, hP⟩
        rwa [← hred h2] at this
  refine ⟨by rw [e0, ← levU_parFam_eq_lev hc h ht hn, e1], fun hy => ?_⟩
  obtain ⟨h1, h2⟩ := hU hy
  obtain ⟨h3, hq⟩ := e1.2 hy
  have h4 : g ∈ lev hc 1 1 (parDat h t s P χ) := levU_parFam_eq_lev hc h ht hn P χ ▸ h3
  have h5 := e0.2 ⟨h4, hq⟩
  obtain ⟨r1, r2⟩ := hR g (Set.mem_univ g) h2 h1
  have hq' : ∀ PP : Q, redAt 1 PP.1 ⟨g, h2⟩ ∈ blockTri (blk2 r) := fun PP => hred h2 PP.1 ▸ hq PP.1 PP.2
  have hw' : ∀ w : SG, redAt 1 w.1 ⟨g, h2⟩ ∈ (parFam h t s P χ w).H := (r1.1 hy).1
  have a1 : ((levFn 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ g : ℂˣ) : ℂ) =
      emb ((levFn 1 (parDat h t s P χ) g : Kˣ) : K) *
        ∏ PP ∈ Q, ((((ξ PP)⁻¹ (dBlk (blk2 r) 1 (redFn 1 PP g))) : ℂˣ) : ℂ) := by
    have eQ : (parDat h t s P χ).Q = ∅ := rfl
    unfold levFn
    rw [extendOne_of_mem _ h5.2, extendOne_of_mem _ h4.2, eQ, Finset.prod_empty, mul_one]
    simp only [Units.val_mul, Units.coe_prod, map_mul, map_prod]
    congr 1
    congr 1
    · rw [hchi _ fun w => h4.2 w (Set.mem_univ w)]
      have := rld_ofLocal_chi (fun w => (P w).H) (fun w => (P w).lam) ⟨_, h4.2⟩
      refine Eq.trans ?_ (congrArg (fun x : Kˣ => emb (x : K)) this).symm
      simp only [Units.coe_prod, map_prod]
      rfl
    · show ∏ PP ∈ SG, _ = ∏ PP ∈ SG, _
      refine Finset.prod_congr rfl fun w hw => ?_
      show ∏ c ∈ Finset.range s, _ = ∏ c ∈ Finset.range s, _
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [rld_parDat_cg h P χ c ⟨w, hw⟩]
      exact hcg c ⟨w, hw⟩ _
  have a2 := levChr_parFam_eq_levChar hc h ht hn P χ g h3 h4
  rw [levChar_apply] at a2
  rw [a1, ← a2, r2 hy hw' hq', star_mul']
  congr 1
  · show emb ((piChar (fun w => (parFam h t s P χ w).H) (fun w => (parFam h t s P χ w).lam) (levRed hc n' ∅ SG _ ⟨g, h3⟩) : Kˣ) : K) = _
    rw [piChar_apply, Units.coe_prod, map_prod, star_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    have : Finite (𝓞 E ⧸ w.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
    have b1 := ((emb.toMonoidHom.comp ((Units.coeHom K).comp (parFam h t s P χ w).lam)).isOfFinOrder
      (isOfFinOrder_of_finite ⟨_, hw' w⟩)).norm_eq_one
    refine Eq.trans ?_ ((congrArg star (Complex.inv_eq_conj b1)).trans (Complex.conj_conj _)).symm
    exact congrArg (fun x => emb (((parFam h t s P χ w).lam x : Kˣ) : K))
      (Subtype.ext ((levRed_apply hc n' ∅ SG _ ⟨g, h3⟩ w).trans (hred h2 w.1)))
  · rw [star_prod, ← Finset.prod_coe_sort Q]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have : Finite (𝓞 E ⧸ PP.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
    have ed : dBlk (blk2 r) 1 (redFn 1 PP.1 g) = blkDet (blk2 r) 1 ⟨_, hq' PP⟩ := by
      unfold dBlk
      rw [extendOne_of_mem _ (hq PP.1 PP.2)]
      exact congrArg _ (Subtype.ext (hred h2 PP.1))
    rw [ed, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    have b1 := (((Units.coeHom ℂ).comp (ξ PP.1)).isOfFinOrder
      (isOfFinOrder_of_finite (blkDet (blk2 r) 1 ⟨_, hq' PP⟩))).norm_eq_one
    exact Complex.inv_eq_conj b1

end GlobalTheory.SeeSaw.TwLev

end
end

