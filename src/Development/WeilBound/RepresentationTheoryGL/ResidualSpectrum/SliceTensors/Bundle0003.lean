import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0002
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0667
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PChordA
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.ChordArithmetic

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem mulChi_absC_cancel (a : ℕ) (z : ℂ) (ψ : Sm E a) :
    mulChi a (Model.absC E z) (mulChi a (Model.absC E (-z)) ψ) = ψ := by
  refine Subtype.ext (funext fun m => ?_)
  rw [mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val, mul_assoc, ← Complex.exp_add]
  simp

theorem central_twist {a : ℕ} (w e : ℂ) (h : e + w * a * (Module.finrank ℚ E : ℂ) = 0) (ψ : Sm E a)
    (hψ : ∀ (t : ℝ) m, ψ.1 (splitCentre E a t * m) = Complex.exp (e * t) * ψ.1 m) :
    ∀ (t : ℝ) m, (mulChi a (Model.absC E w) ψ).1 (splitCentre E a t * m) = (mulChi a (Model.absC E w) ψ).1 m := by
  intro t m
  rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hψ, ExponentTwist.splitCentre_eq, ExponentTwist.chiDet_aT le_rfl]
  have e1 : Complex.exp (e * t) * Complex.exp (w * a * (Module.finrank ℚ E : ℂ) * t) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    linear_combination (t : ℂ) * h
  linear_combination (ψ.1 m * ((chiDet a (Model.absC E w) m : ℂˣ) : ℂ)) * e1

theorem left_eq (c c₁ : ℂ) (r r₁ d : ℕ) (hr : r ≠ 0) (hd : d ≠ 0) :
    (c₁ - -(c / (r * d)) * r₁ * d).re = c₁.re + (r₁ : ℝ) / r * c.re := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have e : c₁ - -(c / (r * d)) * r₁ * d = c₁ + (((r₁ : ℝ) / r : ℝ) : ℂ) * c := by
    push_cast
    field_simp
    ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul]

theorem right_eq (c c₂ : ℂ) (s r₂ d : ℕ) (hs : s ≠ 0) (hd : d ≠ 0) :
    (c + (c₂ - -(-c / (s * d)) * r₂ * d)).re = c₂.re + ((s : ℝ) - r₂) / s * c.re := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have e : c + (c₂ - -(-c / (s * d)) * r₂ * d) = c₂ + ((((s : ℝ) - r₂) / s : ℝ) : ℂ) * c := by
    push_cast
    field_simp
    ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul]

theorem left_arith (r s r₁ d lam x y : ℝ) (hr : 0 < r) (h1 : 0 < r₁) (h2 : r₁ < r) (hlam : 0 < lam)
    (hp : y / d - r * (r + s - r) / 2 = -lam * (r * s))
    (hb : (x + r₁ / r * y) / d - r₁ * (r + s - r₁) / 2 ≤ -lam * (r₁ * (r + s - r₁))) :
    x / d - r₁ * (r - r₁) / 2 < 0 := by
  have hY : y / d = r * s / 2 - lam * (r * s) := by linarith
  have e : (x + r₁ / r * y) / d = x / d + r₁ / r * (y / d) := by ring
  have e2 : r₁ / r * (r * s / 2 - lam * (r * s)) = r₁ * s / 2 - lam * (r₁ * s) := by field_simp
  rw [e, hY, e2] at hb
  nlinarith [mul_pos hlam (mul_pos h1 (sub_pos.2 h2))]

theorem right_arith (r s r₂ d lam x y : ℝ) (hs : 0 < s) (h1 : 0 < r₂) (h2 : r₂ < s) (hlam : 0 < lam)
    (hp : y / d - r * (r + s - r) / 2 = -lam * (r * s))
    (hb : (x + (s - r₂) / s * y) / d - (r + r₂) * (r + s - (r + r₂)) / 2 ≤ -lam * ((r + r₂) * (r + s - (r + r₂)))) :
    x / d - r₂ * (s - r₂) / 2 < 0 := by
  have hY : y / d = r * s / 2 - lam * (r * s) := by linarith
  have e : (x + (s - r₂) / s * y) / d = x / d + (s - r₂) / s * (y / d) := by ring
  have e2 : (s - r₂) / s * (r * s / 2 - lam * (r * s)) = r * (s - r₂) / 2 - lam * (r * (s - r₂)) := by
    field_simp
  rw [e, hY, e2] at hb
  nlinarith [mul_pos hlam (mul_pos h1 (sub_pos.2 h2))]

end PositivityTheory.Rg.Rs.ChordArithmetic
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTw
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

theorem expTw_holds : ExpTw := by
  intro E _ _ _ N φ z _ r _ hrN c hc
  let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
  obtain ⟨F₀, ⟨μ, 𝓕, hμ, h𝓕, hF₀⟩, F, hF, hF0, hFt⟩ := hc
  set χ := Model.absC E z
  set Y : GA E N → ℂ := fun g => (((chiDet N χ g)⁻¹ : ℂˣ) : ℂ) with hY
  have hu : ∀ (x : BlockIx N r → Ad E), chiDet N χ (unip x) = 1 := fun x => by
    change (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det (unip x)) = 1
    rw [det_unip, map_one]
  have hct : F₀ = fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 g * ((chiDet N χ g : ℂˣ) : ℂ) := by
    rw [hF₀]
    funext g
    simp only [PositivityTheory.Affgl.CT.ct]
    rw [← integral_mul_const]
    congr 1
    funext x
    rw [mulChi_apply, map_mul, hu, one_mul]
  have hYX : ∀ g, ((chiDet N χ g : ℂˣ) : ℂ) * Y g = 1 := fun g => Units.mul_inv _
  have hYa : ∀ t : ℝ, Y (aT E N r t) = Complex.exp (-(z * r * (Module.finrank ℚ E : ℂ) * t)) := fun t => by
    simp only [hY]
    rw [Units.val_inv_eq_inv_val, ExponentTwist.chiDet_aT hrN.le, ← Complex.exp_neg]
  refine ⟨PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1, ⟨μ, 𝓕, hμ, h𝓕, rfl⟩, LinearMap.mulRight ℂ Y F, ?_, ?_, ?_⟩
  · have h1 := Submodule.mem_map_of_mem (f := LinearMap.mulRight ℂ Y) hF
    rw [Submodule.map_span] at h1
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    have e : LinearMap.mulRight ℂ Y (fun g => F₀ (aT E N r t * g)) =
        ((chiDet N χ (aT E N r t) : ℂˣ) : ℂ) • fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (aT E N r t * g) := by
      funext g
      simp only [LinearMap.mulRight_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hct, map_mul, Units.val_mul]
      linear_combination (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (aT E N r t * g) * ((chiDet N χ (aT E N r t) : ℂˣ) : ℂ)) * hYX g
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · intro h
    apply hF0
    funext g
    have h2 := congrFun h g
    simp only [LinearMap.mulRight_apply, Pi.mul_apply, Pi.zero_apply] at h2
    have h3 : Y g ≠ 0 := Units.ne_zero _
    exact (mul_eq_zero.1 h2).resolve_right h3
  · intro t g
    simp only [LinearMap.mulRight_apply, Pi.mul_apply]
    have hYm : ∀ a b, Y (a * b) = Y a * Y b := fun a b => by simp only [hY, map_mul, mul_inv, Units.val_mul]
    have e : Complex.exp ((c - z * r * (Module.finrank ℚ E : ℂ)) * t) =
        Complex.exp (c * t) * Complex.exp (-(z * r * (Module.finrank ℚ E : ℂ) * t)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [hFt, hYm, hYa, e]
    ring

end PositivityTheory.Rg.Rs
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.ParabolicProjection

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem mulChi_absC_neg (n : ℕ) (z : ℂ) (φ : Sm E n) :
    mulChi n (Model.absC E (-z)) (mulChi n (Model.absC E z) φ) = φ := by
  refine Subtype.ext (funext fun g => ?_)
  rw [mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val, mul_assoc, ← Complex.exp_add]
  simp

theorem mulChi_absC_neg' (n : ℕ) (z : ℂ) (φ : Sm E n) :
    mulChi n (Model.absC E z) (mulChi n (Model.absC E (-z)) φ) = φ := by
  have h := mulChi_absC_neg n (-z) φ
  rwa [neg_neg] at h

theorem isStable_tw {n : ℕ} {U : Submodule ℂ (Sm E n)} (hU : IsStable U) (z : ℂ) : IsStable (tw U z) := by
  rintro o _ ⟨φ, hφ, rfl⟩
  exact ⟨_, add_mem (U.smul_mem _ (hU o φ hφ)) (U.smul_mem _ hφ), (act_mulChi _ o φ).symm⟩

def twMap (n : ℕ) (z : ℂ) (f : Sm E n →ₗ[ℂ] Sm E n) : Sm E n →ₗ[ℂ] Sm E n :=
  (mulChi n (Model.absC E z)).toLinearMap ∘ₗ f ∘ₗ (mulChi n (Model.absC E (-z))).toLinearMap

theorem twMap_apply (n : ℕ) (z : ℂ) (f : Sm E n →ₗ[ℂ] Sm E n) (φ : Sm E n) :
    twMap n z f φ = mulChi n (Model.absC E z) (f (mulChi n (Model.absC E (-z)) φ)) := rfl

theorem twMap_equiv {n : ℕ} {z : ℂ} {U : Submodule ℂ (Sm E n)} (_hU : IsStable U) {f : Sm E n →ₗ[ℂ] Sm E n}
    (hf : ∀ o, ∀ ψ ∈ U, f (act o ψ) = act o (f ψ)) : ∀ o, ∀ ψ ∈ tw U z, twMap n z f (act o ψ) = act o (twMap n z f ψ) := by
  rintro o _ ⟨φ, hφ, rfl⟩
  change twMap n z f (act o (mulChi n (Model.absC E z) φ)) = act o (twMap n z f (mulChi n (Model.absC E z) φ))
  rw [twMap_apply, twMap_apply, mulChi_absC_neg, act_mulChi, mulChi_absC_neg, map_add, map_smul, map_smul, hf o φ hφ,
    act_mulChi]

theorem twMap_mem {n : ℕ} {z : ℂ} {U W : Submodule ℂ (Sm E n)} {f : Sm E n →ₗ[ℂ] Sm E n} (hf : ∀ ψ ∈ U, f ψ ∈ W) :
    ∀ ψ ∈ tw U z, twMap n z f ψ ∈ tw W z := by
  rintro _ ⟨φ, hφ, rfl⟩
  change twMap n z f (mulChi n (Model.absC E z) φ) ∈ tw W z
  rw [twMap_apply, mulChi_absC_neg]
  exact ⟨_, hf φ hφ, rfl⟩

theorem twMap_ne {n : ℕ} {z : ℂ} {U : Submodule ℂ (Sm E n)} {f : Sm E n →ₗ[ℂ] Sm E n} (hf : ∀ ψ ∈ U, f ψ = 0 → ψ = 0) :
    ∀ ψ ∈ tw U z, twMap n z f ψ = 0 → ψ = 0 := by
  rintro _ ⟨φ, hφ, rfl⟩ h
  change twMap n z f (mulChi n (Model.absC E z) φ) = 0 at h
  rw [twMap_apply, mulChi_absC_neg, LinearEquiv.map_eq_zero_iff] at h
  change mulChi n (Model.absC E z) φ = 0
  rw [hf φ hφ h, map_zero]

variable {r s : ℕ}

theorem tensor_pair_finite_sum {V₁ : Submodule ℂ (Sm E r)} {V₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 V₁ V₂) : ∃ (n : ℕ) (ψ₁ : Fin n → Sm E r) (ψ₂ : Fin n → Sm E s), (∀ i, ψ₁ i ∈ V₁) ∧ (∀ i, ψ₂ i ∈ V₂) ∧
      ∀ m, F m = ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hF
    exact ⟨1, fun _ => φ₁, fun _ => φ₂, fun _ => h₁, fun _ => h₂, fun m => by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun m => by simp⟩
  | add F G _ _ hF hG =>
    obtain ⟨n, a₁, a₂, ha₁, ha₂, ha⟩ := hF
    obtain ⟨n', b₁, b₂, hb₁, hb₂, hb⟩ := hG
    refine ⟨n + n', Fin.append a₁ b₁, Fin.append a₂ b₂, fun i => ?_, fun i => ?_, fun m => ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using ha₁ j
      · simpa using hb₁ j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using ha₂ j
      · simpa using hb₂ j
    · simp [Fin.sum_univ_add, ha, hb]
  | smul c F _ hF =>
    obtain ⟨n, a₁, a₂, ha₁, ha₂, ha⟩ := hF
    exact ⟨n, fun i => c • a₁ i, a₂, fun i => Submodule.smul_mem _ c (ha₁ i), ha₂, fun m => by
      simp [ha, Finset.mul_sum, mul_assoc]⟩

theorem sum_mem_tens2 {V₁ : Submodule ℂ (Sm E r)} {V₂ : Submodule ℂ (Sm E s)} {n : ℕ} {ψ₁ : Fin n → Sm E r}
    {ψ₂ : Fin n → Sm E s} (h₁ : ∀ i, ψ₁ i ∈ V₁) (h₂ : ∀ i, ψ₂ i ∈ V₂) :
    (fun m : GA E r × GA E s => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) ∈ tens2 V₁ V₂ := by
  have e : (fun m : GA E r × GA E s => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) =
      ∑ i, fun m : GA E r × GA E s => (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 := by
    funext m
    simp [Finset.sum_apply]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨ψ₁ i, h₁ i, ψ₂ i, h₂ i, rfl⟩

theorem exists_decomp (g : GA E (r + s)) : ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
    (g' : GL (Fin (r + s)) (Af E)), g = unip x * lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g') := by
  obtain ⟨T, hT⟩ := GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets E r s ⊤ isOpen_univ
  obtain ⟨x, m, t, k, l, -, -, rfl⟩ := hT g
  refine ⟨x, m, k, t * l, ?_⟩
  rw [map_mul, ← mul_assoc (infGL E (r + s) _), infGL_comm]
  simp only [mul_assoc]

theorem exists_slice_ne {F : Sm E (r + s)} (hF : F ≠ 0) (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g) :
    ∃ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m : GA E r × GA E s),
      F.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hF
  apply Subtype.ext
  funext g
  obtain ⟨x, m, k, g', rfl⟩ := exists_decomp g
  rw [mul_assoc, hu, hcon k g' m]
  rfl

theorem sum_left_ne {n : ℕ} {ψ₁ : Fin n → Sm E r} {ψ₂ : Fin n → Sm E s} {m₁ : GA E r} {m₂ : GA E s}
    (h : ∑ i, (ψ₁ i).1 m₁ * (ψ₂ i).1 m₂ ≠ 0) : ∑ i, (ψ₂ i).1 m₂ • ψ₁ i ≠ 0 := by
  intro h0
  apply h
  have := congrArg (fun φ : Sm E r => φ.1 m₁) h0
  simpa [Submodule.coe_sum, Finset.sum_apply, mul_comm] using this

theorem sum_right_ne {n : ℕ} {ψ₁ : Fin n → Sm E r} {ψ₂ : Fin n → Sm E s} {m₁ : GA E r} {m₂ : GA E s}
    (h : ∑ i, (ψ₁ i).1 m₁ * (ψ₂ i).1 m₂ ≠ 0) : ∑ i, (ψ₁ i).1 m₁ • ψ₂ i ≠ 0 := by
  intro h0
  apply h
  have := congrArg (fun φ : Sm E s => φ.1 m₂) h0
  simpa [Submodule.coe_sum, Finset.sum_apply] using this

theorem step_left {n : ℕ} {ψ₁ : Fin n → Sm E r} {ψ₂ : Fin n → Sm E s} {m₂ : GA E s} (f : Sm E r →ₗ[ℂ] Sm E r)
    (h : f (∑ i, (ψ₂ i).1 m₂ • ψ₁ i) ≠ 0) : ∃ b₁, ∑ i, (f (ψ₁ i)).1 b₁ * (ψ₂ i).1 m₂ ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  apply Subtype.ext
  funext b
  have := hc b
  simpa [map_sum, Submodule.coe_sum, Finset.sum_apply, mul_comm] using this

theorem step_right {n : ℕ} {ψ₁ : Fin n → Sm E r} {ψ₂ : Fin n → Sm E s} {m₁ : GA E r} (f : Sm E s →ₗ[ℂ] Sm E s)
    (h : f (∑ i, (ψ₁ i).1 m₁ • ψ₂ i) ≠ 0) : ∃ b₂, ∑ i, (ψ₁ i).1 m₁ * (f (ψ₂ i)).1 b₂ ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  apply Subtype.ext
  funext b
  have := hc b
  simpa [map_sum, Submodule.coe_sum, Finset.sum_apply] using this

theorem inj_of_irred {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {T : Sm E N →ₗ[ℂ] Sm E N}
    (hT : ∀ o, ∀ φ ∈ V, T (act o φ) = act o (T φ)) (hne : ∃ φ ∈ V, T φ ≠ 0) : ∀ φ ∈ V, T φ = 0 → φ = 0 := by
  intro φ hφ h0
  have hW : IsStable (V ⊓ LinearMap.ker T) := fun o ψ hψ => by
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hψ ⊢
    exact ⟨hV.stable o ψ hψ.1, by rw [hT o ψ hψ.1, hψ.2, map_zero]⟩
  rcases hV.irred _ inf_le_left hW with h | h
  · have hm : φ ∈ V ⊓ LinearMap.ker T := Submodule.mem_inf.2 ⟨hφ, h0⟩
    rw [h] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  · obtain ⟨ψ, hψ, hne⟩ := hne
    exact absurd (LinearMap.mem_ker.1 (Submodule.mem_inf.1 (h.ge hψ)).2) hne

end PositivityTheory.Rg.Rs.ParabolicProjection

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatCoreA
section
noncomputable section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SatInd
open scoped TensorProduct

namespace PositivityTheory.Rg.Rs.SatakeVectors.Core

section Abstract

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem idem_map {π : Representation ℂ G V} {π' : Representation ℂ G W} (hπ : IsSmooth π) (hπ' : IsSmooth π')
    {H : Subgroup G} (hH : IsCompact (H : Set G)) (f : V →ₗ[ℂ] W) (hf : ∀ g v, f (π g v) = π' g (f v)) (v : V) :
    f (idem hπ hH v) = idem hπ' hH (f v) := by
  have hy : f (idem hπ hH v) ∈ fixed π' H := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [← hf, GlobalTheory.LGrp.mem_fixed.1 (idem_mem hπ hH v) k hk]
  have hk : v - idem hπ hH v ∈ twKer π H 1 := (idem_eq_zero_iff hπ hH).1 (by
    rw [map_sub, idem_of_mem hπ hH (idem_mem hπ hH v), sub_self])
  have hle : twKer π H 1 ≤ (twKer π' H 1).comap f := Submodule.span_le.2 (by
    rintro _ ⟨u, z, rfl⟩
    exact Submodule.subset_span ⟨u, f z, by rw [map_sub, map_smul, hf]⟩)
  have h0 : idem hπ' hH (f (v - idem hπ hH v)) = 0 := (idem_eq_zero_iff hπ' hH).2 (hle hk)
  rw [map_sub, map_sub, idem_of_mem hπ' hH hy, sub_eq_zero] at h0
  exact h0.symm

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)]
  [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  {ρ : ∀ a, Representation ℂ (Γ a) (X a)} {U : ∀ a, Subgroup (Γ a)}

theorem idem_tprod (hs : ∀ a, IsSmooth (ρ a)) (hc : ∀ a, IsCompact (U a : Set (Γ a)))
    (hC : IsCompact (Subgroup.pi Set.univ U : Set (∀ a, Γ a))) (x : ∀ a, X a) :
    idem (isSmooth_piTensor hs) hC (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ fun a => idem (hs a) (hc a) (x a) := by
  classical
  have hS := isSmooth_piTensor hs
  have h1 : ∀ (x : ∀ a, X a) (i : α) (y : X i),
      idem hS hC (PiTensorProduct.tprod ℂ (Function.update x i (idem (hs i) (hc i) y))) =
        idem hS hC (PiTensorProduct.tprod ℂ (Function.update x i y)) := fun x i y => by
    let l : X i →ₗ[ℂ] ⨂[ℂ] a, X a := idem hS hC ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap x i
    have hk : twKer (ρ i) (U i) 1 ≤ LinearMap.ker l := Submodule.span_le.2 (by
      rintro _ ⟨u, z, rfl⟩
      show l _ = 0
      rw [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, sub_eq_zero]
      have hu : Pi.mulSingle i (u : Γ i) ∈ Subgroup.pi Set.univ U := fun a _ => by
        show (Pi.mulSingle i (u : Γ i) : ∀ a, Γ a) a ∈ U a
        by_cases e : a = i
        · subst e; simp
        · rw [Pi.mulSingle_eq_of_ne e]; exact one_mem _
      refine Eq.trans ?_ (idem_apply_mem hS hC hu (PiTensorProduct.tprod ℂ (Function.update x i z)))
      rw [piTensor_tprod]
      show idem hS hC (PiTensorProduct.tprod ℂ _) = _
      congr 2
      funext a
      by_cases e : a = i
      · subst e; simp
      · simp [e])
    have h2 : l (idem (hs i) (hc i) y - y) = 0 := hk ((idem_eq_zero_iff (hs i) (hc i)).1 (by
      rw [map_sub, idem_of_mem _ _ (idem_mem _ _ _), sub_self]))
    rwa [map_sub, sub_eq_zero] at h2
  have h2 : ∀ (x : ∀ a, X a) (s : Finset α),
      idem hS hC (PiTensorProduct.tprod ℂ (s.piecewise (fun a => idem (hs a) (hc a) (x a)) x)) =
        idem hS hC (PiTensorProduct.tprod ℂ x) := fun x s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.piecewise_insert, h1, ← ih, ← Finset.piecewise_eq_of_notMem s (fun a => idem (hs a) (hc a) (x a)) x hi,
        Function.update_eq_self]
  rw [← h2 x Finset.univ, Finset.piecewise_univ, idem_of_mem]
  refine GlobalTheory.LGrp.mem_fixed.2 fun g hg => ?_
  rw [piTensor_tprod]
  congr 1
  funext a
  exact GlobalTheory.LGrp.mem_fixed.1 (idem_mem _ _ _) _ (hg a trivial)

end Abstract

section Completion

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeylGL

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isSatVecGL_twist {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {x : V} {B : Multiset ℂˣ}
    (hx : IsSatVecGL w ρ x B) (s : ℂ) {z : ℂˣ} (hz : (z : ℂ) = (qV E w : ℂ) ^ (-s)) :
    IsSatVecGL w (twist ρ (detChar (Fin n) (absPow (w.adicCompletion E) s))) x (B.map (· * z)) := by
  have hfix : x ∈ fixed (twist ρ (detChar (Fin n) (absPow (w.adicCompletion E) s))) (KGL w n) :=
    GlobalTheory.LGrp.mem_fixed.2 fun g hg => by
      rw [twist_apply, detChar_apply, absPow_det_of_mem s hg, Units.val_one, one_smul]
      exact GlobalTheory.LGrp.mem_fixed.1 hx.2.1 g hg
  refine ⟨hx.1, hfix, by rw [Multiset.card_map, hx.2.2.1], fun ϖ hϖ j hj => ?_⟩
  rw [GlobalTheory.SphGal.satEig_map_mul, mul_smul, ← hx.2.2.2 ϖ hϖ j hj, heckeVec, heckeVec, smul_finsum]
  refine finsum_congr fun c => ?_
  by_cases hc : Tj ℂ n (Ov E w) ϖ j c.out = 0
  · simp [hc]
  obtain ⟨a, ha, b, hb, e⟩ := Set.mem_of_indicator_ne_zero hc
  have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  have e2 : Matrix.GeneralLinearGroup.det c.out =
      Matrix.GeneralLinearGroup.det a * Units.mk0 ϖ hϖ0 ^ j * Matrix.GeneralLinearGroup.det b := by
    apply Units.ext
    change c.out.val.det = a.val.det * _ * b.val.det
    rw [e, Matrix.det_mul, Matrix.det_mul, GlobalTheory.SphGal.det_diagJ ϖ hj]
    simp
  have e3 : absPow (w.adicCompletion E) s (Units.mk0 ϖ hϖ0) = z := Units.ext (by
    have : ordV E w ϖ = 1 := by
      rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, show Valued.v ϖ = _ from hϖ]; rfl
    rw [val_absPow_completion, hz, Units.val_mk0, this]
    simp)
  rw [twist_apply, detChar_apply, e2, map_mul, map_mul, absPow_det_of_mem s ha, absPow_det_of_mem s hb, map_pow, e3,
    one_mul, mul_one, smul_comm, Units.val_pow_eq_pow_val]

variable {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)

theorem isSatVecGL_multiProd {X : Fin c → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    {π : ∀ a, Representation ℂ (GL (Fin (N a)) (w.adicCompletion E)) (X a)} (hs : ∀ a, IsSmooth (π a))
    {S : Fin c → Multiset ℂˣ} {x : ∀ a, X a} (hx : ∀ a, IsSatVecGL w (π a) (x a) (S a))
    {f : IndSp (stdBlocks N h) (piTensor π)} (hf : f ∈ fixed (multiProd (stdBlocks N h) π) (KGL w n)) (h0 : f ≠ 0)
    {r : ℂ} (hr : f.1.1 1 = r • PiTensorProduct.tprod ℂ x) :
    IsSatVecGL w (multiProd (stdBlocks N h) π) f (∑ a, S a) := by
  have hKO : ∀ m, KGL w m = KO (w.adicCompletion E) (Fin m) := fun m => (SphCompletion.KO_completion w m).symm
  have hf' := hf
  rw [hKO] at hf'
  choose Z iZ mZ R β l y hR hβ hyS h1 hl using fun a => exists_model (w := w) (hx a).2.2.1
  have hy : ∀ a, y a ∈ fixed (R a) (KO _ _) := fun a => hKO _ ▸ (hyS a).2.1
  obtain ⟨F, hF, hF1⟩ := exists_fixed_apply_one (stdBlocks N h) (ρ := piTensor R) (x := PiTensorProduct.tprod ℂ y)
    fun g hg => by
      rw [piTensor_tprod]
      congr 1
      exact funext fun a => GlobalTheory.LGrp.mem_fixed.1 (hy a) _ (hg a)
  obtain ⟨Y, hYe, hY⟩ := exists_map_isSatVecGL h h1 hl hF hF1
  rw [funext hβ] at hY
  refine ⟨h0, hf, hY.2.2.1, fun ϖ hϖ j hj => ?_⟩
  have hϖ0 : ϖ ≠ 0 := fun e => by simp [IsUnifV, e] at hϖ
  have hT := Tj_mem_hecke (n := n) hϖ j
  have hK : IsCommensurated (KGL w n) := Final.GLintComm E w n
  have e1 := (map_heckeVec (ρ := multiProd (stdBlocks N h) R) hK hT Y hYe F).trans (hY.2.2.2 ϖ hϖ j hj)
  rw [hKO] at hT hK e1 ⊢
  have hp : ∀ q : GL (Fin n) (w.adicCompletion E) ⧸ KO (w.adicCompletion E) (Fin n),
      ∃ p : parab (w.adicCompletion E) (stdBlocks N h), ((p : GL (Fin n) (w.adicCompletion E)) : _ ⧸ KO _ _) = q :=
    fun q => by
      obtain ⟨p, hp, u, hu, e⟩ := (LeviInt.levi_integral_facts _ _ _ _ (stdBlocks N h)).2.2.2.2.2.2.2.2 q.out
      exact ⟨⟨p, hp⟩, (QuotientGroup.eq.2 (by simpa [e] using hu)).trans q.out_eq'⟩
  choose p hp using hp
  have hω : ∀ q a, ∃ t : ℂ, Tj ℂ n (Ov E w) ϖ j (p q) ≠ 0 →
      idem (hs a) GlobalTheory.SplitFlip.isCompact_KO (π a (leviProj _ _ (p q) a) (x a)) = t • x a ∧
      idem (hR a) GlobalTheory.SplitFlip.isCompact_KO (R a (leviProj _ _ (p q) a) (y a)) = t • y a := fun q a => by
    by_cases hq : Tj ℂ n (Ov E w) ϖ j (p q) = 0
    · exact ⟨0, fun e => absurd hq e⟩
    obtain ⟨i1, i2⟩ := intM_of_Tj hϖ0 hϖ hq
    obtain ⟨l, hl, e⟩ := dosetInd_eq_Tj hϖ0 hϖ (g := leviProj _ _ (p q) a) (fun s t => i1 _ _) fun s t => by
      have := i2 (stdBlocks N h ⟨a, s⟩) (stdBlocks N h ⟨a, t⟩)
      rw [← Pi.inv_apply, ← map_inv]
      rw [Units.val_mul, tor_val, Matrix.diagonal_mul] at this ⊢
      exact this
    exact ⟨_, fun _ => ⟨idem_of_isSatVecGL (hs a) (hx a) hϖ hl e, idem_of_isSatVecGL (hR a) (hyS a) hϖ hl e⟩⟩
  choose ω hω using hω
  rw [heckeVec_multiProd _ hK hT hR hF (hF1.trans (one_smul ℂ _).symm) p hp ω (fun q hq a => (hω q a hq).2),
    map_smul] at e1
  rw [heckeVec_multiProd _ hK hT hs hf' hr p hp ω (fun q hq a => (hω q a hq).1), smul_left_injective ℂ hY.1 e1]

end Completion

end PositivityTheory.Rg.Rs.SatakeVectors.Core

end
end

