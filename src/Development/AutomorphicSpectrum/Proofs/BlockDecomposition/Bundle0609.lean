import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0209
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.StSmooth
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0584
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0386
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0587
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhat
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.SchGlue

open GlobalTheory.Published.SiegelOneVector

variable {D : D7}

theorem exists_homeomorph_of_sections {A Y Z : Type} [TopologicalSpace A] [TopologicalSpace Y] [TopologicalSpace Z]
    (p : A → Y) (s : Y → A) (c : Y → Z) (σ : Z → A) (hp : Continuous p) (hs : Continuous s)
    (hc : Continuous fun a => c (p a)) (hσ : Continuous σ) (h1 : ∀ y, p (s y) = y)
    (h2 : ∀ z, c (p (σ z)) = z) (h3 : ∀ y, p (σ (c y)) = y) :
    ∃ P : Y ≃ₜ Z, ∀ y, P y = c y := by
  have hcc : Continuous c := by
    have : c = (fun a => c (p a)) ∘ s := funext fun y => by simp only [Function.comp, h1]
    rw [this]
    exact hc.comp hs
  exact ⟨{ toFun := c, invFun := fun z => p (σ z), left_inv := h3, right_inv := h2,
           continuous_toFun := hcc, continuous_invFun := hp.comp hσ }, fun _ => rfl⟩

set_option maxHeartbeats 1600000 in

theorem exists_infHomeo {θ : InfFam D} (hθ : IsInfFam θ) :
    ∃ P : (Ainf D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (D.what₂.Tau → ℂ), ∀ y τ, P y τ = θ τ y := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, he, hec, hec'⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hinf : ∀ y, infPart D (e.symm (y, 0)) = y := fun y => by
    have := (he (e.symm (y, 0))).1
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have hfin : ∀ y, finPart D (e.symm (y, 0)) = 0 := fun y => by
    have := (he (e.symm (y, 0))).2
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have hci : Continuous (infPart D) := by
    have : (infPart D : AE D → _) = fun z => (e z).1 := funext fun z => ((he z).1).symm
    rw [this]
    exact continuous_fst.comp hec
  have hs : Continuous fun y : Ainf D.host.F ⊗[D.host.F] D.host.E => e.symm (y, 0) :=
    hec'.comp (continuous_id.prodMk continuous_const)
  have hback : ∀ a : AE D, finPart D a = 0 → a = σ fun τ => θ τ (infPart D a) := fun a ha => by
    refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
    · rw [(finPart D).map_sub, ha, hσ.fin, sub_zero]
    · rw [(infPart D).map_sub, (θ τ).map_sub, hσ.comp, sub_self]
  obtain ⟨P, hP⟩ := exists_homeomorph_of_sections (infPart D : AE D → _) (fun y => e.symm (y, 0))
    (fun (y : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : D.what₂.Tau) => θ τ y) σ hci hs
    (continuous_pi fun τ => GlobalTheory.FockCompare.continuous_comp hθ τ) hσ.cont hinf
    (fun z => funext fun τ => hσ.comp z τ)
    (fun y => by
      obtain ⟨a, ha⟩ : ∃ a : AE D, a = e.symm (y, 0) := ⟨_, rfl⟩
      have h1 : infPart D a = y := ha ▸ hinf y
      have h2 : finPart D a = 0 := ha ▸ hfin y
      subst h1
      exact congrArg (infPart D) (hback a h2).symm)
  exact ⟨P, fun y τ => congrFun (hP y) τ⟩

theorem isSchwartzArch_comp {θ : InfFam D} (hθ : IsInfFam θ) {m r : ℕ}
    (f : SchwartzMap (D.what₂.Tau → Fin m → Fin r → ℂ) ℂ) :
    IsSchwartzArch (F := D.host.F) (E := D.host.E) (M := m) (n := r)
      fun Y => f fun τ i j => θ τ (Y j i) := by
  obtain ⟨P, hP⟩ := exists_infHomeo hθ
  let Q : (Fin r → Fin m → Ainf D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (D.what₂.Tau → Fin m → Fin r → ℂ) :=
    { toFun := fun Y τ i j => P (Y j i) τ
      invFun := fun c j i => P.symm fun τ => c τ i j
      left_inv := fun Y => by simp
      right_inv := fun c => by simp
      continuous_toFun := continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply τ).comp (P.continuous.comp ((continuous_apply i).comp (continuous_apply j)))
      continuous_invFun := continuous_pi fun j => continuous_pi fun i => P.symm.continuous.comp
        (continuous_pi fun τ => (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))) }
  have hQ : ∀ Y τ i j, Q Y τ i j = θ τ (Y j i) := fun Y τ i j => hP _ _
  have hadd : ∀ X Y, Q (X + Y) = Q X + Q Y := fun X Y => by
    funext τ i j
    simp only [hQ, Pi.add_apply, map_add]
  let B : (D.what₂.Tau → Fin m → Fin r → ℂ) ≃L[ℝ]
      (Fin (Module.finrank ℝ (D.what₂.Tau → Fin m → Fin r → ℂ)) → ℝ) :=
    (Module.finBasis ℝ (D.what₂.Tau → Fin m → Fin r → ℂ)).equivFun.toContinuousLinearEquiv
  refine ⟨_, (AddEquiv.mk' Q.toEquiv hadd).trans B.toLinearEquiv.toAddEquiv,
    B.continuous.comp Q.continuous, Q.symm.continuous.comp B.symm.continuous,
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ B.symm f, fun Y => ?_⟩
  show _ = f (B.symm (B (Q Y)))
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact congrArg f (funext fun τ => funext fun i => funext fun j => (hQ Y τ i j).symm)

theorem isSB_swap {m r : ℕ} {g : (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E)) :
    IsSB fun Y : Fin r → Fin m → Af D.host.F ⊗[D.host.F] D.host.E => g fun i j => Y j i := by
  let S : (Fin r → Fin m → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ
      (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := fun Y i j => Y j i
      invFun := fun Y j i => Y i j
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply i).comp (continuous_apply j)
      continuous_invFun := continuous_pi fun j => continuous_pi fun i =>
        (continuous_apply j).comp (continuous_apply i) }
  exact ⟨hg.1.comp_continuous S.continuous, hg.2.comp_homeomorph S⟩

theorem isSchwartzArch_smul {M n : ℕ} (c : ℂ) {Φ : (Fin n → Fin M → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℂ}
    (h : IsSchwartzArch (F := D.host.F) (E := D.host.E) Φ) :
    IsSchwartzArch (F := D.host.F) (E := D.host.E) fun X => c * Φ X := by
  obtain ⟨N, e, h1, h2, f, hf⟩ := h
  exact ⟨N, e, h1, h2, c • f, fun X => by simp [hf]⟩

theorem sb_zero {M n : ℕ} :
    IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (0 : (Fin n → Fin M → AE D) → ℂ) :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun _ => by simp⟩

theorem sb_add {M n : ℕ} {Φ Ψ : (Fin n → Fin M → AE D) → ℂ}
    (hΦ : IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ)
    (hΨ : IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Ψ) :
    IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (Φ + Ψ) := by
  obtain ⟨k, a, b, ha, hb, hs⟩ := hΦ
  obtain ⟨k', a', b', ha', hb', hs'⟩ := hΨ
  refine ⟨k + k', Fin.append a a', Fin.append b b', fun i => ?_, fun i => ?_, fun X => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact ha i
    · rw [Fin.append_right]; exact ha' i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hb i
    · rw [Fin.append_right]; exact hb' i
  · rw [Fin.sum_univ_add, Pi.add_apply, hs, hs']
    simp only [Fin.append_left, Fin.append_right]

theorem sb_smul {M n : ℕ} (c : ℂ) {Φ : (Fin n → Fin M → AE D) → ℂ}
    (hΦ : IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ) :
    IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (c • Φ) := by
  obtain ⟨k, a, b, ha, hb, hs⟩ := hΦ
  refine ⟨k, fun i X => c * a i X, b, fun i => isSchwartzArch_smul c (ha i), hb, fun X => ?_⟩
  rw [Pi.smul_apply, hs, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.CompanionTheory.SiegelND.SchGlue

namespace GlobalTheory.CompanionTheory.SiegelND

open GlobalTheory.CompanionTheory.SiegelND.SchGlue

theorem isSchwartzBruhat_tupOf_of_mem_schwartzA : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m r : ℕ) (φ : Mx D m r → ℂ), φ ∈ schwartzA θ m r →
  GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (fun X : Fin r → Fin m → AE D => φ (tupOf X)) := by
  intro D θ hθ m r φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨1, fun _ Y => f fun τ i j => θ τ (Y j i), fun _ Y => g fun i j => Y j i,
      fun _ => isSchwartzArch_comp hθ f, fun _ => isSB_swap hg, fun X => ?_⟩
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rfl
  | zero => exact sb_zero
  | add a b _ _ ha hb => exact sb_add ha hb
  | smul c a _ ha => exact sb_smul c ha

end GlobalTheory.CompanionTheory.SiegelND
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzStable
section
open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.GodementSectionC

open Ad3.K.LC

noncomputable def rightMulLin (h : GL (Fin 3) ℂ) :
    (M23 × (Fin 2 → ℂ)) ≃ₗ[ℝ] (M23 × (Fin 2 → ℂ)) where
  toFun v := (Matrix.of.symm (Matrix.of v.1 * (h : Matrix (Fin 3) (Fin 3) ℂ)), v.2)
  invFun v := (Matrix.of.symm (Matrix.of v.1 * ((h⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)), v.2)
  map_add' v w := by
    refine Prod.ext ?_ rfl
    exact Matrix.add_mul (Matrix.of v.1) (Matrix.of w.1) (h : Matrix (Fin 3) (Fin 3) ℂ)
  map_smul' c v := by
    refine Prod.ext ?_ rfl
    exact Matrix.smul_mul c (Matrix.of v.1) (h : Matrix (Fin 3) (Fin 3) ℂ)
  left_inv v := by
    refine Prod.ext ?_ rfl
    change Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of v.1 * (h : Matrix (Fin 3) (Fin 3) ℂ))) *
      ((h⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)) = v.1
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one, Equiv.symm_apply_apply]
  right_inv v := by
    refine Prod.ext ?_ rfl
    change Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of v.1 *
      ((h⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ))) * (h : Matrix (Fin 3) (Fin 3) ℂ)) = v.1
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one, Equiv.symm_apply_apply]

theorem exists_rightTranslate (h : GL (Fin 3) ℂ) (Ψ : Sw) :
    ∃ Ψ' : Sw, ∀ (X : M23) (q : Fin 2 → ℂ),
      Ψ' (X, q) = Ψ (Matrix.of.symm (Matrix.of X * (h : Matrix (Fin 3) (Fin 3) ℂ)), q) :=
  ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rightMulLin h).toContinuousLinearEquiv Ψ,
    fun _ _ => rfl⟩

theorem inn_smul (c : ℂ) (Ψ : Sw) (g : GL (Fin 3) ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    inn (c • Ψ) g M t = c * inn Ψ g M t := by
  unfold inn
  rw [← integral_const_mul]
  congr 1
  funext p
  rw [SchwartzMap.smul_apply, smul_eq_mul]
  ring

theorem inn_mul_right (Ψ Ψ₀ : Sw) (g h : GL (Fin 3) ℂ)
    (hΨ : ∀ (X : M23) (q : Fin 2 → ℂ),
      Ψ₀ (X, q) = Ψ (Matrix.of.symm (Matrix.of X * (h : Matrix (Fin 3) (Fin 3) ℂ)), q))
    (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    inn Ψ (g * h) M t = inn Ψ₀ g M t := by
  unfold inn
  congr 1
  funext p
  rw [hΨ, Units.val_mul, ← Matrix.mul_assoc]
  simp

theorem stStable : StStable := by
  intro k _ Ψ h
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_rightTranslate h Ψ
  set c : ℂ := ((‖(h : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ 2 : ℝ) : ℂ) with hc
  refine ⟨c • Ψ₀, ?_⟩
  funext g
  unfold sec
  simp only [inn_smul, inn_mul_right Ψ Ψ₀ g h hΨ₀]
  have hdet : ((‖((g * h : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ 2 : ℝ) : ℂ) =
      ((‖(g : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ 2 : ℝ) : ℂ) * c := by
    rw [Units.val_mul, Matrix.det_mul, norm_mul, mul_pow, Complex.ofReal_mul]
  have hin : ∀ y : M22, (∫ t : ℂ, c * inn Ψ₀ g (Matrix.of y) t * ph (4 * (k : ℤ) - 4) t) =
      c * ∫ t : ℂ, inn Ψ₀ g (Matrix.of y) t * ph (4 * (k : ℤ) - 4) t := by
    intro y
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  have hout : (∫ y : M22, (c * ∫ t : ℂ, inn Ψ₀ g (Matrix.of y) t * ph (4 * (k : ℤ) - 4) t) *
        ph (-(2 * (k : ℤ) - 2)) (Matrix.of y).det *
        ((‖(Matrix.of y).det‖ ^ (-(2 : ℝ)) : ℝ) : ℂ)) =
      c * ∫ y : M22, (∫ t : ℂ, inn Ψ₀ g (Matrix.of y) t * ph (4 * (k : ℤ) - 4) t) *
        ph (-(2 * (k : ℤ) - 2)) (Matrix.of y).det *
        ((‖(Matrix.of y).det‖ ^ (-(2 : ℝ)) : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  simp only [hin]
  rw [hdet, hout]
  ring

end GlobalTheory.CompanionTheory.GodementSectionC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwiner
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegQuotTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem parIndMap_surjective {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {V W : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (Levi k m) V}
    {ρ' : Representation ℂ (Levi k m) W} (f : ρ.IntertwiningMap ρ') (hρ : IsSmooth ρ)
    (hf : Function.Surjective f) : Function.Surjective (parIndMap e f) := by
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k α n m e
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let σ₀ : Representation ℂ (parab k e) V := (twist ρ (deltaHalf k m)).comp (leviProj k e)
  let z : Representation.IntertwiningMap σ₀ σ₀ :=
    { toLinearMap := 0, isIntertwining' := fun _ => by ext; simp }
  refine (GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL n k) (parab k e) (KO k n) hP SplitFlip.isCompact_KO
    hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k n) _ _ _ _
    (isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ hcont)
    (compMap (twistMap f _) _) Unit (fun _ => z) hf ?_).1
  intro x _
  refine Submodule.subset_span ⟨(), -x, ?_⟩
  show x = (0 : _) - -x
  simp

theorem prod₂_map_surjective {r t : ℕ} {U U' W W' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] {σ : Representation ℂ (GL (Fin r) k) U}
    {σ' : Representation ℂ (GL (Fin r) k) U'} {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} (hσ : IsSmooth σ) (hρ : IsSmooth ρ) (f : σ.IntertwiningMap σ')
    (g : ρ.IntertwiningMap ρ') (hf : Function.Surjective f) (hg : Function.Surjective g) :
    ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ' ρ'), Function.Surjective F := by
  have hσ' : IsSmooth σ' := (IsSubquotient.of_surjective f hf).isSmooth hσ
  have hc : Continuous fun h : Levi k (Two (Fin r) (Fin t)) => (h false, h true) :=
    (continuous_apply false).prodMk (continuous_apply true)
  have h1 : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) := LinearMap.rTensor_surjective W hf
  have h2 : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapRight σ' g) := LinearMap.lTensor_surjective U' hg
  have h1' : Function.Surjective (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := h1
  have h2' : Function.Surjective (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ' g)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := h2
  have s1 := parIndMap_surjective (two (stdSum (rfl : r + t = r + t))) _
    (isSmooth_comp (isSmooth_extTensor hσ hρ) _ hc) h1'
  have s2 := parIndMap_surjective (two (stdSum (rfl : r + t = r + t))) _
    (isSmooth_comp (isSmooth_extTensor hσ' hρ) _ hc) h2'
  exact ⟨(parIndMap (two (stdSum (rfl : r + t = r + t))) (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ' g)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)).comp (parIndMap (two (stdSum (rfl : r + t = r + t)))
      (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)), s2.comp s1⟩

theorem nonempty_prodIrr_equiv_of_cast {c c' N : ℕ} (h : c = c') (x : Fin c → IrrGL k) (x' : Fin c' → IrrGL k)
    (hx : ∀ i, x i = x' (Fin.cast h i)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N) :
    Nonempty ((prodIrr x hd).Equiv (prodIrr x' hd')) := by
  subst h
  obtain rfl : x = x' := funext fun i => by simpa using hx i
  exact ⟨.refl _⟩

theorem append_term (Δ : Segment k) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len)
    (hlen : (segLow Δ a h0).len + (segHigh Δ a h1).len = Δ.len)
    (i : Fin ((segLow Δ a h0).len + (segHigh Δ a h1).len)) :
    Fin.append (segLow Δ a h0).term (segHigh Δ a h1).term i = Δ.term (Fin.cast hlen i) := by
  induction i using Fin.addCases with
  | left i =>
    rw [Fin.append_left]
    rfl
  | right j =>
    rw [Fin.append_right]
    show (Δ.first.nu ((a : ℕ) : ℂ)).nu ((j : ℕ) : ℂ) = Δ.first.nu (((segLow Δ a h0).len + (j : ℕ) : ℕ) : ℂ)
    rw [IrrGL.nu_nu]
    show _ = Δ.first.nu ((a + (j : ℕ) : ℕ) : ℂ)
    push_cast
    rfl

theorem hasFiniteLength_prodIrr (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k)
    (hd : ∑ a, (x a).1 = N) : HasFiniteLength (prodIrr x hd) :=
  GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)
    (hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA x))

theorem nontrivial_prodIrr (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k)
    (hd : ∑ a, (x a).1 = N) : Nontrivial (IndSp (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) :=
  GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp _ (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA x)
    (isSmooth_piTensor fun a => (x a).2.rep.smooth)

theorem exists_surjective_of_equiv {G A B C D : Type} [Group G] [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] {α : Representation ℂ G A}
    {β : Representation ℂ G B} {γ : Representation ℂ G C} {δ : Representation ℂ G D} (E : Nonempty (β.Equiv α))
    (F : ∃ f : β.IntertwiningMap γ, Function.Surjective f) (H : Nonempty (γ.Equiv δ)) :
    ∃ f : α.IntertwiningMap δ, Function.Surjective f := by
  obtain ⟨E⟩ := E
  obtain ⟨F, hF⟩ := F
  obtain ⟨H⟩ := H
  exact ⟨H.toIntertwiningMap.comp (F.comp E.symm.toIntertwiningMap),
    H.toLinearEquiv.surjective.comp (hF.comp E.symm.toLinearEquiv.surjective)⟩

theorem exists_surjective_of_prod₂_equiv {r t : ℕ} {U U' W W' A D : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup A]
    [Module ℂ A] [AddCommGroup D] [Module ℂ D] {σ : Representation ℂ (GL (Fin r) k) U}
    {σ' : Representation ℂ (GL (Fin r) k) U'} {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} {α : Representation ℂ (GL (Fin (r + t)) k) A}
    {δ : Representation ℂ (GL (Fin (r + t)) k) D} (hσ : IsSmooth σ) (hρ : IsSmooth ρ) (f : σ.IntertwiningMap σ')
    (g : ρ.IntertwiningMap ρ') (hf : Function.Surjective f) (hg : Function.Surjective g)
    (E : Nonempty ((prod₂ σ ρ).Equiv α)) (H : Nonempty ((prod₂ σ' ρ').Equiv δ)) :
    ∃ F : α.IntertwiningMap δ, Function.Surjective F :=
  exists_surjective_of_equiv E (prod₂_map_surjective hσ hρ f g hf hg) H

theorem exists_surjective_append {p q : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (u v : IrrGL k)
    (hx : ∑ a, (x a).1 = u.1) (hy : ∑ a, (y a).1 = v.1) (h : ∑ a, (Fin.append x y a).1 = u.1 + v.1)
    (hd : ∑ i, (![u, v] i).1 = u.1 + v.1)
    (fu : (prodIrr x hx).IntertwiningMap u.rep) (hfu : Function.Surjective fu)
    (fv : (prodIrr y hy).IntertwiningMap v.rep) (hfv : Function.Surjective fv) :
    ∃ F : (prodIrr (Fin.append x y) h).IntertwiningMap (prodIrr ![u, v] hd), Function.Surjective F :=
  exists_surjective_of_prod₂_equiv (isSmooth_prodIrr x hx) (isSmooth_prodIrr y hy) fu fv hfu hfv
    (GlobalTheory.T.product_irreducible_append_equiv k p q u.1 v.1 x y hx hy h) (nonempty_prod₂_equiv_prodIrr_pair u v hd)

theorem quotient_of_quotient {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (P : Representation ℂ G V) (Q : Representation ℂ G X)
    (hc : IsCosocle σ P) (hfl : HasFiniteLength P) (hf : ∃ f : P.IntertwiningMap Q, Function.Surjective f)
    (hQ : Nontrivial X) : ∃ g : Q.IntertwiningMap σ, Function.Surjective g := by
  obtain ⟨f, hf⟩ := hf
  exact GlobalTheory.T.cosocle_surjection_factor σ P Q hc hfl f hf hQ

theorem quottwo : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsLSeg Δ π) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len) (u v : IrrGL k)
    (hu : IsLSeg (segLow Δ a h0) u.rep) (hv : IsLSeg (segHigh Δ a h1) v.rep) (hd : ∑ i, (![u, v] i).1 = N),
    ∃ f : (prodIrr ![u, v] hd).IntertwiningMap π, Function.Surjective f := by
  intro k _ _ _ _ hA Δ N V _ _ π hπ a h0 h1 u v hu hv hd
  have hN : u.1 + v.1 = N := hd.symm ▸ (Fin.sum_univ_two (fun i => (![u, v] i).1)).symm
  subst hN
  obtain ⟨hx, -, fu, hfu, -⟩ := hu
  obtain ⟨hy, -, fv, hfv, -⟩ := hv
  obtain ⟨hΔ, hc⟩ := hπ
  have hlen : (segLow Δ a h0).len + (segHigh Δ a h1).len = Δ.len := by
    show a + (Δ.len - a) = Δ.len
    omega
  have hsum : ∑ i, (Fin.append (segLow Δ a h0).term (segHigh Δ a h1).term i).1 = u.1 + v.1 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    exact congrArg₂ (· + ·) hx hy
  exact quotient_of_quotient π _ _ hc (hasFiniteLength_prodIrr hA _ hΔ)
    (exists_surjective_of_equiv (nonempty_prodIrr_equiv_of_cast hlen _ Δ.term (append_term Δ a h0 h1 hlen) hsum hΔ)
      (exists_surjective_append _ _ u v hx hy hsum hd fu hfu fv hfv) ⟨.refl _⟩) (nontrivial_prodIrr hA _ hd)

end GlobalTheory.CompanionTheory.SegQuotTwo

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPreservesArchimedeanHaar
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem pi_map_update_add {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd₂ V] {n : ℕ}
    (ν : Measure V) [SigmaFinite ν] [ν.IsAddRightInvariant] (a : Fin n) (T : (Fin n → V) → V)
    (hT : Measurable T) (hTa : ∀ x y, T (Function.update x a y) = T x) :
    (Measure.pi fun _ : Fin n => ν).map (fun x => Function.update x a (x a + T x)) =
      Measure.pi fun _ : Fin n => ν := by
  have hf : Measurable (fun x : Fin n → V => Function.update x a (x a + T x)) := by
    refine measurable_pi_lambda _ fun j => ?_
    by_cases h : j = a
    · subst h
      simp only [Function.update_self]
      exact (measurable_pi_apply j).add hT
    · simpa [Function.update_of_ne h] using measurable_pi_apply j
  refine (Measure.pi_eq fun s hs => ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [← Measure.pi_pi, ← lintegral_indicator_one h2s, ← lintegral_indicator_one h2s,
    lintegral_map (measurable_one.indicator h2s) hf]
  refine lintegral_eq_of_lmarginal_eq {a} ((measurable_one.indicator h2s).comp hf)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  have key : ∀ y : V, Function.update (Function.update x a y) a (Function.update x a y a + T (Function.update x a y))
      = Function.update x a (y + T x) := by
    intro y
    simp [hTa]
  simp only [Function.comp_def, key]
  exact lintegral_add_right_eq_self
    (fun y => (Set.univ.pi s).indicator (1 : (Fin n → V) → ℝ≥0∞) (Function.update x a y)) (T x)

theorem coordW_map_shearK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearK a s) = GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  intro F E _ _ _ _ _ σ hσ n M d b lam hlam a s hs
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Ainf F) d b lam hlam
  haveI := hK
  haveI : SigmaFinite (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) := inferInstance
  haveI hν : (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).IsAddHaarMeasure := inferInstance
  have hmul : ∀ c : Ainf F ⊗[F] E, Measurable (fun y : Ainf F ⊗[F] E => c * y) := fun c =>
    (continuous_const.mul continuous_id).measurable
  have hT : Measurable (fun (x : Fin n → Fin M → Ainf F ⊗[F] E) (i : Fin M) => ∑ c, s c * x c i) := by
    refine measurable_pi_lambda _ fun i => ?_
    refine Finset.measurable_sum _ fun c _ => ?_
    exact (hmul (s c)).comp ((measurable_pi_apply i).comp (measurable_pi_apply c))
  have hTa : ∀ (x : Fin n → Fin M → Ainf F ⊗[F] E) (y : Fin M → Ainf F ⊗[F] E),
      (fun i => ∑ c, s c * Function.update x a y c i) = fun i => ∑ c, s c * x c i := by
    intro x y
    funext i
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : c = a
    · subst h; simp [hs]
    · simp [Function.update_of_ne h]
  exact pi_map_update_add (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) a _ hT hTa

end GlobalTheory.CompanionTheory.WhitFree.AvgInf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingCompactFreeSetStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_scaling_compact_free_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v ⊗[F] E)ˣ) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsCompact P → IsOpen P → P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} → IsCompact ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P) ∧ IsOpen ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P) ∧ (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil.dil_set | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil.dil_set | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil.dil_set <;> assumption)
end

