import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0010
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0005
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0001
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0237
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import GroundTheory.PAdicHodge.ACrisBdR
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1411
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ConstantTermZeroEq
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def E_L (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N r : ℕ) (t : ℝ) :
    (GA E N → ℂ) →ₗ[ℂ] (GA E N → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun g => aT E N r t * g

theorem E_L_apply {N r : ℕ} (t : ℝ) (f : GA E N → ℂ) (g : GA E N) : E_L E N r t f g = f (aT E N r t * g) := rfl

theorem constant_term_zero_eq {N r : ℕ} (f : GA E N → ℂ) : E_L E N r 0 f = f := by
  funext g
  rw [E_L_apply, aT_zero, one_mul]

theorem E_LL {N r : ℕ} (s t : ℝ) (f : GA E N → ℂ) : E_L E N r s (E_L E N r t f) = E_L E N r (t + s) f := by
  funext g
  rw [E_L_apply, E_L_apply, E_L_apply, aT_add, mul_assoc]

variable {r s : ℕ}

theorem E_key_left {r₁ : ℕ} (hr₁ : r₁ < r) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g))
    (ψ : GA E r → ℂ) (m₂ : GA E s) (h : GA E (r + s)) (hψF : ∀ m₁, ψ m₁ = F (lev (Ad E) r s (m₁, m₂) * h)) :
    An.ctn r₁ ψ = E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E =>
        (parGL (joinPos (r := r₁) 0 b) : GA E (r + s)))
      (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h))
      ((E_vol E r r₁)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) r₁)) τs a (An.ctn r₁ φ.1) := by
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hφl := GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E _ φ hφ
  have hcr : Continuous (An.ctn r φ.1) := E_cont_ctn r hφc hφ.left
  funext m₁
  set y := lev (Ad E) r s (m₁, m₂) * h with hy
  have hpos : ∀ x : PPos (r + s) {r₁, r}, ¬ IsTop r x → ((x.1.1 : ℕ) < r ↔ (x.1.2 : ℕ) < r) := fun x hx => by
    have := E_pos_top hr₁ x hx
    omega
  have e2 : ∀ A : UPos r r₁ → Ad E, ψ (unipGL A * m₁) = ∑ t ∈ τs, a t *
      An.ctn r φ.1 (parGL (joinPos (r := r) 0 fun q => A ((eL r s r₁ hr₁).symm q)) * (aT E (r + s) r t * y)) := by
    intro A
    rw [hψF, hF]
    refine Finset.sum_congr rfl fun t _ => ?_
    have e : lev (Ad E) r s (unipGL A * m₁, m₂) = lev (Ad E) r s (unipGL A, 1) * lev (Ad E) r s (m₁, m₂) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, lev_unipGL_left r s r₁ hr₁, mul_assoc, ← mul_assoc (aT E (r + s) r t), aT_comm_parGL _ _ _ _ hpos,
      mul_assoc]
  have e3 : ∀ z, ∫ b, An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * z)
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r₁, r} // ¬ IsTop r x} => boxMeasure E) =
      (E_vol E (r + s) r)⁻¹ * (E_vol E (r + s) r₁ * ∫ b, An.ctn r₁ φ.1 (parGL (joinPos (r := r₁) 0 b) * z)
        ∂(Measure.pi fun _ : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} => boxMeasure E)) := by
    intro z
    simp only [E_ctn_eq r]
    rw [integral_const_mul, ← constantTermPar_eq_top hr₁ hφc, constantTermPar_eq_bot hr₁ hφc hφl]
    congr 1
    rw [← integral_const_mul]
    congr 1
    funext b
    exact E_ct_eq r₁ _ _
  have hint : ∀ t ∈ τs, Integrable (fun A : UPos r r₁ → Ad E => a t * An.ctn r φ.1
      (parGL (joinPos (r := r) 0 fun q => A ((eL r s r₁ hr₁).symm q)) * (aT E (r + s) r t * y)))
      (Measure.pi fun _ => boxMeasure E) := by
    intro t _
    refine (integrable_box ?_).const_mul _
    exact hcr.comp ((((E_cont_join (E := E) (n := r + s) (S := {r₁, r}) r).comp
      (continuous_pi fun q => continuous_apply _))).mul continuous_const)
  rw [E_ctn_eq, constantTerm_eq_integral]
  simp only [e2]
  rw [integral_finsetSum _ hint]
  simp only [integral_const_mul, E_B]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← integral_box_reindex (eL r s r₁ hr₁)
    (fun b => An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * (aT E (r + s) r t * y))), e3]
  ring

theorem E_hB_left {r₁ : ℕ} (hr₁ : r₁ < r) (m₂ : GA E s) (h : GA E (r + s)) (κ : ℂ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (t : ℝ) (f : GA E (r + s) → ℂ) :
    E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E => (parGL (joinPos (r := r₁) 0 b) : GA E (r + s)))
      (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h)) κ τs a (E_L E (r + s) r₁ t f) =
    E_L E r r₁ t (E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E =>
        (parGL (joinPos (r := r₁) 0 b) : GA E (r + s)))
      (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h)) κ τs a f) := by
  have hpos : ∀ x : PPos (r + s) {r₁, r}, ¬ IsTop r₁ x → ((x.1.1 : ℕ) < r₁ ↔ (x.1.2 : ℕ) < r₁) := fun x hx => by
    have := E_pos_bot hr₁ x hx
    omega
  funext m₁
  rw [E_L_apply]
  unfold E_B
  refine congrArg (κ * ·) (Finset.sum_congr rfl fun u _ => congrArg (a u * ·)
    (integral_congr_ae (.of_forall fun b => ?_)))
  change f (aT E (r + s) r₁ t * _) = f _
  refine congrArg f ?_
  rw [← mul_assoc, aT_comm_parGL _ _ _ _ hpos, mul_assoc, ← mul_assoc (aT E (r + s) r₁ t), aT_comm, mul_assoc,
    ← mul_assoc (aT E (r + s) r₁ t), ← lev_aT_left r s r₁ hr₁.le, ← map_mul, Prod.mk_mul_mk, one_mul]

theorem E_trans_right {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (w : GA E (r + s)) :
    ∫ b, An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * w)
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) =
    (E_vol E (r + s) r)⁻¹ * (E_vol E (r + s) (r + r₂) * ∫ b, An.ctn (r + r₂) φ.1
      (parGL (joinPos (r := r + r₂) 0 b) * w)
        ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} => boxMeasure E)) := by
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hφl := GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E _ φ hφ
  have hpq : r < r + r₂ := by omega
  simp only [E_ctn_eq r]
  rw [integral_const_mul, ← constantTermPar_eq_bot hpq hφc hφl, constantTermPar_eq_top hpq hφc]
  congr 1
  rw [← integral_const_mul]
  congr 1
  funext b
  exact E_ct_eq (r + r₂) _ _

theorem E_int_right {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g)) (z : GA E (r + s)) :
    ∫ b, F (parGL (joinPos (r := r) 0 b) * z)
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) =
    ∑ t ∈ τs, a t * ((E_vol E (r + s) r)⁻¹ * (E_vol E (r + s) (r + r₂) * ∫ b, An.ctn (r + r₂) φ.1
      (parGL (joinPos (r := r + r₂) 0 b) * (aT E (r + s) r t * z))
        ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} => boxMeasure E))) := by
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hcr : Continuous (An.ctn r φ.1) := E_cont_ctn r hφc hφ.left
  have hpq : r < r + r₂ := by omega
  have hpos : ∀ x : PPos (r + s) {r, r + r₂}, ¬ IsTop r x → ((x.1.1 : ℕ) < r ↔ (x.1.2 : ℕ) < r) := fun x hx => by
    have := E_pos_bot hpq x hx
    omega
  have e1 : ∀ b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} → Ad E, F (parGL (joinPos (r := r) 0 b) * z) =
      ∑ t ∈ τs, a t * An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * (aT E (r + s) r t * z)) := by
    intro b
    rw [hF]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← mul_assoc, aT_comm_parGL _ _ _ _ hpos, mul_assoc]
  have hint : ∀ t ∈ τs, Integrable (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} → Ad E =>
      a t * An.ctn r φ.1 (parGL (joinPos (r := r) 0 b) * (aT E (r + s) r t * z))) (Measure.pi fun _ => boxMeasure E) :=
    fun t _ => (integrable_box (hcr.comp
      ((E_cont_join (E := E) (n := r + s) (S := {r, r + r₂}) r).mul continuous_const))).const_mul _
  simp only [e1]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul, E_trans_right hr₂ φ hφ]

theorem E_G_shift {r₂ : ℕ} (hr₂ : 0 < r₂) (τs : Finset ℝ) (a : ℝ → ℂ) (u : ℝ) (f : GA E (r + s) → ℂ)
    (z : GA E (r + s)) :
    E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a (E_L E (r + s) (r + r₂) u f) z =
    E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a f (aT E (r + s) (r + r₂) u * z) := by
  have hpq : r < r + r₂ := by omega
  have hpos : ∀ x : PPos (r + s) {r, r + r₂}, ¬ IsTop (r + r₂) x →
      ((x.1.1 : ℕ) < r + r₂ ↔ (x.1.2 : ℕ) < r + r₂) := fun x hx => by
    have := E_pos_top hpq x hx
    omega
  unfold E_B
  refine congrArg (1 * ·) (Finset.sum_congr rfl fun t _ => congrArg (a t * ·)
    (integral_congr_ae (.of_forall fun b => ?_)))
  change f (aT E (r + s) (r + r₂) u * _) = f _
  refine congrArg f ?_
  rw [← mul_assoc, aT_comm_parGL _ _ _ _ hpos, mul_assoc, ← mul_assoc (aT E (r + s) (r + r₂) u), aT_comm, mul_assoc]

theorem E_aT_right {r₂ : ℕ} (hr₂s : r₂ ≤ s) (t : ℝ) (m₁ : GA E r) (m₂ : GA E s) (h : GA E (r + s)) :
    aT E (r + s) (r + r₂) t * (lev (Ad E) r s (m₁, m₂) * h) =
      aT E (r + s) r t * (lev (Ad E) r s (m₁, aT E s r₂ t * m₂) * h) := by
  have e1 : aT E (r + s) (r + r₂) t = lev (Ad E) r s (1, aT E s r₂ t) * aT E (r + s) r t := by
    rw [lev_aT_right r s r₂ hr₂s, mul_assoc, ← aT_add, neg_add_cancel, aT_zero, mul_one]
  have e2 : lev (Ad E) r s (m₁, aT E s r₂ t * m₂) = lev (Ad E) r s (1, aT E s r₂ t) * lev (Ad E) r s (m₁, m₂) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e1, e2, (aT_comm_lev r s t _).symm]
  simp only [mul_assoc]

end PositivityTheory.Rg.Rs.SliceClasses

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsProj2
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.PLsProj2

theorem proj_fun {Y Γ X : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] (act : Γ → Y → Y)
    (ρ : Representation ℂ Γ X) (hρ : ρ.IsIrreducible) (T : Submodule ℂ (Y → ℂ))
    (hle : T ≤ ⨆ Φ : {Φ : X →ₗ[ℂ] (Y → ℂ) // (∀ v, Φ v ∈ T) ∧ ∀ g v, Φ (ρ g v) = fun m => Φ v (act g m)},
      LinearMap.range Φ.1) (t : Y → ℂ) (ht : t ∈ T) (h0 : t ≠ 0) :
    ∃ p : (Y → ℂ) →ₗ[ℂ] X, p t ≠ 0 ∧ ∀ g, ∀ s ∈ T, p (fun m => s (act g m)) = ρ g (p s) := by
  have key := PLsAbs2.exists_proj (fun g => LinearMap.funLeft ℂ ℂ (act g)) ρ hρ
    (fun Φ : {Φ : X →ₗ[ℂ] (Y → ℂ) // (∀ v, Φ v ∈ T) ∧ ∀ g v, Φ (ρ g v) = fun m => Φ v (act g m)} => Φ.1)
    (fun Φ => Φ.2.2) (hle ht) h0
  obtain ⟨p, hp, he⟩ := key
  exact ⟨p, hp, fun g s hs => he g s (hle hs)⟩

theorem schur {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (τ : SmIrr (GL (Fin n) k)) (φ : τ.V →ₗ[ℂ] τ.V) (hφ : ∀ g x, φ (τ.ρ g x) = τ.ρ g (φ x)) :
    ∃ c : ℂ, φ = c • LinearMap.id := by
  obtain ⟨z, hz⟩ := GlobalTheory.LocGL.schur_GL τ.smooth τ.irred ⟨φ, fun g => LinearMap.ext (hφ g)⟩
  exact ⟨z, LinearMap.ext hz⟩

theorem irr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {c : ℕ}
    {n : Fin c → ℕ} (τ : ∀ i, SmIrr (GL (Fin (n i)) k)) : (piTensor fun i => (τ i).ρ).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun i => (τ i).irred) fun i => schur (τ i)

end PositivityTheory.Rg.Rs.PLsProj2

namespace PositivityTheory.Rg.Rs

theorem existsProj2 : PositivityTheory.RSHS.LS.ExistsProj := fun E _ _ _ _ n π w τ hτ =>
  PLsProj2.proj_fun (Γ := ∀ i, GL (Fin (n i)) (w.adicCompletion E))
    (fun g (m : ∀ i, GA E (n i)) i => m i * finGL E (n i) (locGL E (n i) w (g i)))
    (piTensor fun i => (τ i).ρ) (PLsProj2.irr τ) (tensorForms π) (PositivityTheory.RSHS.LocalComponentTwist.tensorForms_le_iSup π τ hτ)

end PositivityTheory.Rg.Rs

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapE
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

namespace E

theorem cpt_mem {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (k : Kinf E (r + s)) : cptRep E (r + s) k F ∈ indSub U₁ U₂ := by
  have e : (cptRep E (r + s) k F).1 = fun x => F.1 (x * cf (r + s) k 1) := by
    funext x
    simp only [cf, map_one, mul_one]
    rfl
  change IsInd U₁ U₂ (cptRep E (r + s) k F).1
  rw [e]
  exact isInd_rt hF k 1

end E

theorem exists_expansion {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : Sm E (r + s)}
    (hF : F ∈ indSub U₁ U₂) (hK : F ∈ finVec (cptRep E (r + s))) :
    ∃ (n : ℕ) (G : Fin n → GA E r × GA E s → ℂ) (C : Fin n → Lie E (r + s) → ℂ)
      (b₁ : Lie E (r + s) → GL (Fin r) (Cinf E)) (b₂ : Lie E (r + s) → GL (Fin s) (Cinf E)),
      (∀ j, G j ∈ tens2 U₁ U₂) ∧ (∀ j, ContDiffAt ℝ ∞ (C j) (oneL E (r + s))) ∧
      ContDiffAt ℝ ∞ (fun y => toL (b₁ y).val) (oneL E (r + s)) ∧
      ContDiffAt ℝ ∞ (fun y => toL (b₂ y).val) (oneL E (r + s)) ∧
      b₁ (oneL E (r + s)) = 1 ∧ b₂ (oneL E (r + s)) = 1 ∧
      ∀ {f₁ : Sm E r →ₗ[ℂ] Sm E r} {f₂ : Sm E s →ₗ[ℂ] Sm E s}, Good U₁ U₂ f₁ f₂ → ∀ m : GA E r × GA E s,
        chart (ind f₁ f₂ F.1) (lev (Ad E) r s m) =ᶠ[nhds (oneL E (r + s))]
          fun y => ∑ j, C j y * tensOp f₁ f₂ (G j) (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y)) := by
  obtain ⟨b₁, b₂, κ, u, hb₁, hb₂, hκ, hb₁1, hb₂1, hκ1, hloc⟩ := exists_local E r s
  obtain ⟨n, ψ, C, hψ, hC, e⟩ := GlobalTheory.KFinExp.exists_expansion E (r + s) F hK
  have hψ' : ∀ j, ψ j ∈ indSub U₁ U₂ := fun j => Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact PositivityTheory.Rg.Rs.InducedTensorMap.E.cpt_mem hF k) (hψ j)
  have hκ1' : toL (κ (oneL E (r + s))).1 = oneL E (r + s) := by rw [hκ1]; rfl
  refine ⟨n, fun j => res 1 (ψ j).1, fun j y => C j (toL (κ y).1), b₁, b₂, fun j => ?_, fun j => ?_, hb₁, hb₂, hb₁1,
    hb₂1, ?_⟩
  · have := (hψ' j).2 1 1
    rwa [cf_one] at this
  · exact ContDiffAt.comp (oneL E (r + s)) (by rw [hκ1']; exact hC j) hκ
  intro f₁ f₂ H m
  filter_upwards [hloc] with y hy
  have hyw : y = toL (unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y) * Unitary.toUnits (κ y)).val := by
    show y = toL ((unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y)).val * (κ y).1)
    rw [← hy]
    rfl
  conv_lhs => rw [hyw, chart_val]
  obtain ⟨v, hv⟩ := lev_mul_infGL m (u y) (b₁ y) (b₂ y) (κ y)
  rw [hv, ind_apply H (show IsInd U₁ U₂ F.1 from hF) v _ (κ y) 1]
  have er : res (cf (r + s) (κ y) 1) F.1 = ∑ j, C j (toL (κ y).1) • res 1 (ψ j).1 := by
    have h1 : res (cf (r + s) (κ y) 1) F.1 = res 1 (cptRep E (r + s) (κ y) F).1 := by
      funext z
      simp only [res_apply, cf, map_one, mul_one]
      rfl
    rw [h1, e]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  rw [er]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem ind_mem_Sm {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (H : Good U₁ U₂ f₁ f₂) {F : Sm E (r + s)} (hF : F ∈ indSub U₁ U₂)
    (hK : F ∈ finVec (cptRep E (r + s))) : ind f₁ f₂ F.1 ∈ Sm E (r + s) := by
  have key : ∀ {F : Sm E (r + s)}, F ∈ indSub U₁ U₂ → F ∈ finVec (cptRep E (r + s)) → ∀ m,
      ContDiffAt ℝ ∞ (chart (ind f₁ f₂ F.1) (lev (Ad E) r s m)) (oneL E (r + s)) := fun hF hK m => by
    obtain ⟨n, G, C, b₁, b₂, hG, hC, hb₁, hb₂, -, -, e⟩ := exists_expansion hF hK
    exact ContDiffAt.congr_of_eventuallyEq (ContDiffAt.sum fun j _ =>
      (hC j).mul (contDiffAt_tens b₁ b₂ hb₁ hb₂ (tensOp_mem f₁ f₂ (hG j)) m)) (e H m)
  refine GlobalTheory.DiscSMO.mem_Sm_of_one fun x => ?_
  obtain ⟨u, m, k, g, rfl⟩ := exists_decomp x
  have e1 : chart (ind f₁ f₂ F.1) (unip u * lev (Ad E) r s m * cf (r + s) k g) =
      chart (ind f₁ f₂ F.1) (lev (Ad E) r s m * cf (r + s) k g) := by
    funext z
    unfold chart
    split_ifs
    · simp only [mul_assoc]
      exact ind_left H hF u _
    · rfl
  rw [e1, cf, infGL_comm, ← mul_assoc]
  refine GlobalTheory.DiscSMO.contDiffAt_chart_mul ?_
  rw [← chart_rt_fin]
  have e2 : (fun x => (fun x => ind f₁ f₂ F.1 (x * infGL E (r + s) (Unitary.toUnits k))) (x * finGL E (r + s) g)) =
      ind f₁ f₂ (rt E (r + s) (cf (r + s) k g) F).1 := by
    funext z
    rw [show (rt E (r + s) (cf (r + s) k g) F).1 = fun y => F.1 (y * cf (r + s) k g) from rfl,
      ind_rt H hF k g z, cf, infGL_comm]
    exact congrArg _ (mul_assoc _ _ _)
  rw [e2]
  exact key (isInd_rt hF k g) (finVec_rt hK k g) m

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs.StrStepB

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem absC_unrAt (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (GlobalTheory.CuspRep.Model.absC E s).UnrAt w := by
  intro x hx
  apply Units.ext
  change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E w x)) = 1
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local w x 0 (by simpa [IsUnitAt] using hx)]
  simp

theorem absC_val (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) :
    (((GlobalTheory.CuspRep.Model.absC E s).val w : ℂˣ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s) := by
  change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E w (atFin w (unif w)))) = _
  have h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local w _ 1 (unif_spec w), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
    ← Complex.natCast_log]
  congr 1; push_cast; ring

theorem absC_add (s t : ℂ) :
    GlobalTheory.CuspRep.Model.absC E (s + t) = GlobalTheory.CuspRep.Model.absC E s * GlobalTheory.CuspRep.Model.absC E t := by
  refine Subtype.ext (MonoidHom.ext fun x => Units.ext ?_)
  change Complex.exp ((s + t) * _) = Complex.exp (s * _) * Complex.exp (t * _)
  rw [← Complex.exp_add, add_mul]

theorem absC_zero : GlobalTheory.CuspRep.Model.absC E 0 = 1 := by
  refine Subtype.ext (MonoidHom.ext fun x => Units.ext ?_)
  change Complex.exp (0 * _) = 1
  simp

theorem hasSat_twist_absC {a : ℕ} (π : CuspSub E a) {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : (CG.mk π).HasSat w B) (x : ℂ) :
    ((CG.mk π).twist (GlobalTheory.CuspRep.Model.absC E x)).HasSat w (B.map (· * (GlobalTheory.CuspRep.Model.absC E x).val w)) :=
  GlobalTheory.SphGal.hasSatGL_twist E a π _ w B (absC_unrAt x w) h

abbrev dC (b : ℕ) : Lie E b := fun i j => if i = j then (1 : Cinf E) else 0

theorem lie_dC_eq_zero {b : ℕ} {ρ : CuspSub E b} (h : IsNormalised ρ) {φ : Sm E b} (hφ : φ ∈ ρ.V) :
    lie E b (dC b) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := GlobalTheory.CuspRep.SplitDeriv.hasDerivAt_splitCentre φ g 0
  have h2 : (fun t : ℝ => φ.1 (g * splitCentre E b t)) = fun _ => φ.1 g := funext fun t => by
    rw [← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm]; exact h φ hφ t g
  rw [h2, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero, mul_one] at h1
  rw [h1.unique (hasDerivAt_const 0 _)]
  rfl

theorem opAdd_dC (c : ℂ) (b : ℕ) :
    opAdd (GlobalTheory.CuspRep.Model.absC E c) (.lie (dC b) : Op E b) = c * (2 * b * Fintype.card (InfinitePlace E)) := by
  change dchi (GlobalTheory.CuspRep.Model.absC E c) (Matrix.of (dC (E := E) b)).trace = _
  rw [GlobalTheory.GKCoh.Tests.dchi_absC]
  have e : ∀ w, (Matrix.of (dC (E := E) b)).trace w = b := fun w => by
    simp [Matrix.trace, dC, Finset.sum_apply]
  simp only [e, Complex.natCast_re]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  ring

theorem eq_zero_of_iso_twist {b : ℕ} (hb : 1 ≤ b) {ρ ρ' : CuspSub E b} (h : IsNormalised ρ) (h' : IsNormalised ρ')
    {c : ℂ} (e : ρ.Iso (ρ'.twist (GlobalTheory.CuspRep.Model.absC E c))) : c = 0 := by
  obtain ⟨T, hT⟩ := e
  have := Submodule.nontrivial_iff_ne_bot.2 ρ.ne_bot
  obtain ⟨φ, hφ⟩ := exists_ne (0 : ρ.V)
  obtain ⟨ψ, hψ⟩ := (ρ'.toTwist (GlobalTheory.CuspRep.Model.absC E c)).surjective (T φ)
  have h1 := hT (.lie (dC b)) φ
  have h2 : ρ.op (.lie (dC b)) φ = 0 := Subtype.ext (lie_dC_eq_zero h φ.2)
  have h3 : ρ'.op (.lie (dC b)) ψ = 0 := Subtype.ext (lie_dC_eq_zero h' ψ.2)
  rw [h2, map_zero, ← hψ, CuspSub.op_toTwist, h3, opAdd_dC, smul_zero, zero_add] at h1
  have h4 : (c * (2 * b * Fintype.card (InfinitePlace E)) : ℂ) • ψ = 0 :=
    (ρ'.toTwist _).injective (h1.symm.trans (map_zero _).symm)
  have hψ0 : ψ ≠ 0 := fun e0 => hφ (T.injective (by rw [← hψ, e0, map_zero, map_zero]))
  have hK : (2 * b * Fintype.card (InfinitePlace E) : ℂ) ≠ 0 := by
    have : 0 < Fintype.card (InfinitePlace E) := Fintype.card_pos
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    have hc' : (Fintype.card (InfinitePlace E) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
    exact mul_ne_zero (mul_ne_zero two_ne_zero hb') hc'
  rcases smul_eq_zero.1 h4 with h5 | h5
  · exact (mul_eq_zero.1 h5).resolve_right hK
  · exact absurd h5 hψ0

theorem match_twist {b b' : ℕ} (hb : 1 ≤ b) (ρ : CuspSub E b) (ρ' : CuspSub E b') (h : IsNormalised ρ)
    (h' : IsNormalised ρ') {u u' : ℂ}
    (e : (⟨b, (CG.mk ρ).twist (GlobalTheory.CuspRep.Model.absC E u)⟩ : Σ c, CG E c) =
      ⟨b', (CG.mk ρ').twist (GlobalTheory.CuspRep.Model.absC E u')⟩) :
    u = u' ∧ (⟨b, CG.mk ρ⟩ : Σ c, CG E c) = ⟨b', CG.mk ρ'⟩ := by
  obtain ⟨rfl, e2⟩ := Sigma.mk.inj_iff.1 e
  have e3 : CG.mk ρ = CG.mk (ρ'.twist (GlobalTheory.CuspRep.Model.absC E (u' - u))) := by
    have := congrArg (fun π : CG E b => π.twist (GlobalTheory.CuspRep.Model.absC E (-u))) (eq_of_heq e2)
    simp only [← CG.twist_mul, ← absC_add] at this
    rw [add_neg_cancel, absC_zero, CG.twist_one] at this
    rw [this, CG.twist_mk, sub_eq_add_neg]
  have hI : ρ.Iso (ρ'.twist (GlobalTheory.CuspRep.Model.absC E (u' - u))) := Quotient.exact e3
  have h0 := eq_zero_of_iso_twist hb h h' hI
  obtain rfl : u = u' := by linear_combination -h0
  refine ⟨rfl, ?_⟩
  rw [e3, sub_self, absC_zero, CuspSub.twist_one]

end PositivityTheory.Rg.Rs.StrStepB

end
end

