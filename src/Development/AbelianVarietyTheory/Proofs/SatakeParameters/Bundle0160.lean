import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0151
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0154

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralOfTraceCharPairingSkewHermitian
section
open Matrix

namespace GlobalTheory.Hk3.GramSep

theorem int_of_psi_trace_gam : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ),
  Formalism.UG.IsUnramInv ϖ σ q → (Valued.v δ = 1 ∧ σ δ = -δ) →
  (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) →
  ∀ (r : ℕ) (e : Fin r → ℕ) (Δ : Matrix (Fin r) (Fin r) L), (∀ j k, σ (Δ j k) = Δ k j) →
  (∀ Γ ∈ GlobalTheory.Hk3.GramSep.gam σ ϖ e, ψ (δ * Matrix.trace (Γ * Δ)) = 1) →
  ∀ j k, Δ j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ q δ ψ hU hδ hne r e Δ hΔ hψ j k
  have hσ := hU.1
  have hv := hU.2.1
  have hw : δ * (Δ j k * ϖ ^ max (e j) (e k)) ∈ Formalism.UG.intL L := by
    refine GlobalTheory.Hk3.int_of_psi hU ψ hne _ (fun b hb => ?_)
    set c : L := b * ϖ ^ max (e j) (e k) with hc
    have hcv : Valued.v c ≤ Valued.v ϖ ^ max (e j) (e k) := by
      rw [hc, map_mul, map_pow]
      exact mul_le_of_le_one_left' hb
    have hmem : Matrix.single k j c + Matrix.single j k (-σ c) ∈ gam σ ϖ e := by
      refine ⟨fun a a' => ?_, fun a a' => ?_⟩
      · simp only [Matrix.add_apply, Matrix.single_apply, map_add, apply_ite σ, map_neg, hσ, map_zero,
          and_comm (a := k = a'), and_comm (a := j = a')]
        split_ifs <;> ring
      · rw [Matrix.add_apply]
        refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
        · rw [Matrix.single_apply]
          split_ifs with h
          · obtain ⟨rfl, rfl⟩ := h
            rw [max_comm]; exact hcv
          · simp
        · rw [Matrix.single_apply]
          split_ifs with h
          · obtain ⟨rfl, rfl⟩ := h
            rw [Valuation.map_neg, hv]; exact hcv
          · simp
    have h := hψ _ hmem
    have e1 : b * (δ * (Δ j k * ϖ ^ max (e j) (e k))) = δ * (c * Δ j k) := by rw [hc]; ring
    rw [e1, map_mul, map_mul σ c, hδ.2, hΔ, ← h]
    congr 1
    rw [Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul]
    simp only [smul_eq_mul]
    ring
  rw [GlobalTheory.Hk3.mem_intL_iff, map_mul, hδ.1, one_mul] at hw
  exact hw

end GlobalTheory.Hk3.GramSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleWdEigenEqualNorm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IrrWeilAbs

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_pow_central {n : ℕ} (a : WDRep h (Fin n → ℂ)) {φ : Weil h} (hφ : deg φ = 1) :
    ∃ m : ℕ, 0 < m ∧ ∀ σ : Weil h, a.ρ (φ ^ m) * a.ρ σ = a.ρ σ * a.ρ (φ ^ m) := by
  classical
  let S : Set (Module.End ℂ (Fin n → ℂ)) := Set.range fun τ : Ine (F := E) A => a.ρ (ineIncl h τ)
  haveI : Finite S := a.smooth.finite_range.to_subtype
  have conj_mem : ∀ (k : ℕ), ∀ s ∈ S, a.ρ (φ ^ k) * s * a.ρ ((φ ^ k)⁻¹) ∈ S := by
    rintro k _ ⟨τ, rfl⟩
    have h0 : deg (φ ^ k * ineIncl h τ * (φ ^ k)⁻¹) = 0 := by simp
    refine ⟨⟨_, deg_eq_zero_iff.mp h0⟩, ?_⟩
    simp only [← map_mul]
    exact congrArg a.ρ (Subtype.ext rfl)
  let g : ℕ → (S → S) := fun k s => ⟨_, conj_mem k s.1 s.2⟩
  obtain ⟨k1, k2, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite g
  obtain ⟨k, m, hm, hkm⟩ : ∃ k m : ℕ, 0 < m ∧ g k = g (k + m) := by
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact ⟨k1, k2 - k1, by omega, by rw [show k1 + (k2 - k1) = k2 by omega]; exact heq⟩
    · exact ⟨k2, k1 - k2, by omega, by rw [show k2 + (k1 - k2) = k1 by omega]; exact heq.symm⟩
  have comm_ine : ∀ τ : Ine (F := E) A,
      a.ρ (φ ^ m) * a.ρ (ineIncl h τ) = a.ρ (ineIncl h τ) * a.ρ (φ ^ m) := by
    intro τ
    have e1 : a.ρ (φ ^ k * ineIncl h τ * (φ ^ k)⁻¹) =
        a.ρ (φ ^ (k + m) * ineIncl h τ * (φ ^ (k + m))⁻¹) := by
      have := congrArg Subtype.val (congrFun hkm ⟨_, τ, rfl⟩)
      rw [map_mul, map_mul, map_mul, map_mul]
      exact this
    have e2 := congrArg (fun X => a.ρ ((φ ^ k)⁻¹) * X * a.ρ (φ ^ k * φ ^ m)) e1
    simp only [← map_mul] at e2
    rw [← map_mul, ← map_mul]
    convert e2.symm using 2 <;> group
  refine ⟨m, hm, fun σ => ?_⟩
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul hφ σ
  have hc : φ ^ m * φ ^ deg σ = φ ^ deg σ * φ ^ m :=
    ((Commute.refl φ).pow_left m).zpow_right (deg σ)
  rw [hτ, map_mul, ← mul_assoc, ← map_mul, hc, map_mul, mul_assoc, comm_ine, ← mul_assoc]

theorem exists_smul_of_commute {n : ℕ} (a : WDRep h (Fin n → ℂ)) (hirr : a.ρ.IsIrreducible)
    (P : Module.End ℂ (Fin n → ℂ)) (hP : ∀ σ : Weil h, P * a.ρ σ = a.ρ σ * P) :
    ∃ c : ℂ, ∀ v, P v = c • v := by
  haveI := hirr
  let f : Representation.IntertwiningMap a.ρ a.ρ :=
    ⟨P, fun σ => LinearMap.ext fun v => LinearMap.congr_fun (hP σ) v⟩
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := a.ρ)).2 f
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun F : Representation.IntertwiningMap a.ρ a.ρ => F v) hc
  rw [Algebra.algebraMap_eq_smul_one] at this
  simpa [f] using this.symm

theorem irrWD_eig_norm_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ = ‖β‖ := by
  intro E Ω _ _ _ _ _ A w h x hx φ hφ α hα β hβ
  obtain ⟨n, a, rfl, hirr⟩ := hx
  rw [WD.eig_mk] at hα hβ
  obtain ⟨m, hm, hcomm⟩ := exists_pow_central a hφ
  obtain ⟨c, hc⟩ := exists_smul_of_commute a hirr _ hcomm
  have hev : ∀ γ ∈ (a.ρ φ).charpoly.roots, γ ^ m = c := by
    intro γ hγ
    obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
      (Polynomial.isRoot_of_mem_roots hγ)).exists_hasEigenvector
    have hpow : ∀ k : ℕ, ((a.ρ φ) ^ k) v = γ ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv.apply_eq_smul, smul_smul, pow_succ]
    have h1 : γ ^ m • v = c • v := by rw [← hpow, ← map_pow, hc]
    exact smul_left_injective ℂ hv.2 h1
  have h2 : ‖α‖ ^ m = ‖β‖ ^ m := by rw [← norm_pow, ← norm_pow, hev α hα, hev β hβ]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hm.ne').mp h2

end GlobalTheory.IrrWeilAbs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConj
section
noncomputable section

open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CsdFromConj

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

theorem invTOp_invTOp (o : Op L a) : invTOp (invTOp o) = o := by
  cases o with
  | fin k => exact congrArg Op.fin (Units.ext (Matrix.transpose_transpose k.val))
  | cpt k =>
    refine congrArg Op.cpt (Subtype.ext ?_)
    ext i j : 1
    simp [barK, Matrix.star_apply]
  | lie X =>
    refine congrArg Op.lie ?_
    funext i j
    simp [toL]

theorem invT_map {R : Type} [CommRing R] (c : R →+* R) (g : GL (Fin a) R) :
    invT a R (GeneralLinearGroup.map c g) = GeneralLinearGroup.map c (invT a R g) :=
  Units.ext (by rw [show (invT a R (GeneralLinearGroup.map c g)).val = ((GeneralLinearGroup.map c g)⁻¹).valᵀ from rfl,
    ← map_inv]; rfl)

omit [NumberField L] [IsCMField L] in

theorem barK_barK (k : Kinf L a) : barK (barK k) = k := by
  refine Subtype.ext ?_
  ext i j : 1
  simp [barK, Matrix.star_apply]

def phiG (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) : GA L a :=
  finGL L a (PhiU a (Af L)) * infGL L a (Unitary.toUnits (PhiK L a))

theorem toUnits_PhiK : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl

theorem act_thetaOp (o : Op L a) :
    act (thetaOp o) * rt L a (phiG L a) = rt L a (phiG L a) * act (conjOp (invTOp o)) := by
  cases o with
  | fin k =>
    change rt L a (finGL L a _) * rt L a (phiG L a) = rt L a (phiG L a) * rt L a (finGL L a _)
    rw [← map_mul, ← map_mul]
    congr 1
    refine ga_ext ?_ ?_
    · simp [phiG, map_mul]
    · simp only [phiG, map_mul, pFin_finGL, pFin_infGL, mul_one]
      rw [thetaGL, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, invT_map]
      simp [mul_assoc]
  | cpt k =>
    change rt L a (infGL L a (Unitary.toUnits _)) * rt L a (phiG L a) =
      rt L a (phiG L a) * rt L a (infGL L a (Unitary.toUnits _))
    rw [← map_mul, ← map_mul]
    congr 1
    rw [barK_barK]
    refine ga_ext ?_ ?_
    · simp [phiG, map_mul, map_inv]
    · simp [phiG, map_mul]
  | lie X =>
    have hY : (fun i j => star (toL (-(Matrix.of X)ᵀ) i j) : Lie L a) = toL (-(Matrix.of X)ᴴ) := by
      funext i j
      simp [toL, Matrix.conjTranspose_apply]
    have hR := GlobalTheory.CapAdInv.rt_lie (PhiU a (Cinf L)) (-(Matrix.of X)ᴴ)
    have e : (PhiU a (Cinf L)).val * -(Matrix.of X)ᴴ * ((PhiU a (Cinf L))⁻¹).val =
        -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) := by
      rw [Matrix.mul_neg, Matrix.neg_mul]; rfl
    rw [e] at hR
    change lie L a _ * rt L a (phiG L a) = rt L a (phiG L a) * lie L a (fun i j => star (toL (-(Matrix.of X)ᵀ) i j))
    rw [hY, phiG, map_mul, toUnits_PhiK, mul_assoc (rt L a (finGL L a _)), hR, ← mul_assoc (rt L a (finGL L a _)),
      ← lie_rt_fin, mul_assoc (lie L a _)]

theorem rt_phiG : rt L a (phiG L a) = act (.fin (PhiU a (Af L))) * act (.cpt (PhiK L a)) := map_mul _ _ _

theorem act_fin_inv (k : GL (Fin a) (Af L)) : act (.fin k) * act (.fin k⁻¹) = 1 := by
  change finRep L a k * finRep L a k⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

theorem act_fin_inv' (k : GL (Fin a) (Af L)) : act (.fin k⁻¹) * act (.fin k) = 1 := by
  change finRep L a k⁻¹ * finRep L a k = 1
  rw [← map_mul, inv_mul_cancel, map_one]

theorem act_cpt_inv (k : Kinf L a) : act (.cpt k) * act (.cpt k⁻¹) = 1 := by
  change cptRep L a k * cptRep L a k⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

theorem act_cpt_inv' (k : Kinf L a) : act (.cpt k⁻¹) * act (.cpt k) = 1 := by
  change cptRep L a k⁻¹ * cptRep L a k = 1
  rw [← map_mul, inv_mul_cancel, map_one]

def phiEquiv (π : CuspSub L a) : π.V ≃ₗ[ℂ] π.V :=
  LinearEquiv.ofLinear (π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a)))
    (π.op (.cpt (PhiK L a)⁻¹) * π.op (.fin (PhiU a (Af L))⁻¹))
    (LinearMap.ext fun φ => Subtype.ext <| by
      change act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) (act (.cpt (PhiK L a)⁻¹)
        (act (.fin (PhiU a (Af L))⁻¹) φ.1))) = φ.1
      rw [← Module.End.mul_apply (act (.cpt (PhiK L a))), act_cpt_inv, Module.End.one_apply,
        ← Module.End.mul_apply, act_fin_inv, Module.End.one_apply])
    (LinearMap.ext fun φ => Subtype.ext <| by
      change act (.cpt (PhiK L a)⁻¹) (act (.fin (PhiU a (Af L))⁻¹) (act (.fin (PhiU a (Af L)))
        (act (.cpt (PhiK L a)) φ.1))) = φ.1
      rw [← Module.End.mul_apply (act (.fin (PhiU a (Af L))⁻¹)), act_fin_inv', Module.End.one_apply,
        ← Module.End.mul_apply, act_cpt_inv', Module.End.one_apply])

theorem op_thetaOp_phiEquiv (π : CuspSub L a) (o : Op L a) (φ : π.V) :
    π.op (thetaOp o) (phiEquiv π φ) = phiEquiv π (π.op (conjOp (invTOp o)) φ) := Subtype.ext <| by
  change act (thetaOp o) (act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) φ.1)) =
    act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) (act (conjOp (invTOp o)) φ.1))
  have h := LinearMap.congr_fun (act_thetaOp (L := L) (a := a) o) φ.1
  rw [rt_phiG] at h
  exact h

theorem isCsd_of_invT_conj (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a)
    (S : π.V ≃ₗ[ℂ] π.V) (hS : ∀ o φ, S (π.op (invTOp o) φ) = π.op (conjOp o) (S φ)) : π.IsCsd := by
  refine ⟨(phiEquiv π).symm.trans S.symm, fun o φ => ?_⟩
  obtain ⟨χ, rfl⟩ := (phiEquiv π).surjective φ
  obtain ⟨ψ, rfl⟩ := S.surjective χ
  have h := hS (invTOp o) ψ
  rw [invTOp_invTOp] at h
  simp only [LinearEquiv.trans_apply, op_thetaOp_phiEquiv, LinearEquiv.symm_apply_apply, ← h]

end GlobalTheory.CsdFromConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleCoinvariantsSubsingletonOfCharConj
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory

theorem jacquet_subsingleton_of_char_nontrivial_on_conj :
    ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), π.IsIrreducible →
      ∀ (N H : Subgroup G) (χ : H →* ℂˣ) (v : V), v ≠ 0 → (∀ h : H, π h v = (χ h : ℂ) • v) →
      (∀ g : G, ∃ h : H, g * h * g⁻¹ ∈ N ∧ χ h ≠ 1) → Subsingleton (Jacquet π N) := by
  intro G V _ _ _ π hπ N H χ v hv0 hv hconj
  set K : Submodule ℂ V := twKer π N 1 with hK

  have hgv : ∀ g : G, π g v ∈ K := by
    intro g
    obtain ⟨h, hn, hχ⟩ := hconj g
    have hmem : π (g * h * g⁻¹) (π g v) - (1 : ℂ) • π g v ∈ K := by
      refine Submodule.subset_span ⟨⟨_, hn⟩, π g v, ?_⟩
      simp
    have hcalc : π (g * h * g⁻¹) (π g v) = (χ h : ℂ) • π g v := by
      rw [← Module.End.mul_apply, ← map_mul]
      have : g * (h : G) * g⁻¹ * g = g * h := by group
      rw [this, map_mul, Module.End.mul_apply, hv h, map_smul]
    rw [hcalc, ← sub_smul] at hmem
    have hne : (χ h : ℂ) - 1 ≠ 0 := by
      intro e
      apply hχ
      ext
      simpa [sub_eq_zero] using e
    have := K.smul_mem ((χ h : ℂ) - 1)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  let S : Submodule ℂ V := ⨅ g : G, K.comap (π g)
  have hS : ∀ w, w ∈ S ↔ ∀ g : G, π g w ∈ K := by
    intro w; simp [S, Submodule.mem_iInf]
  let Wr : Subrepresentation π :=
    { toSubmodule := S
      apply_mem_toSubmodule := by
        intro g w hw
        rw [hS] at hw ⊢
        intro g'
        rw [← Module.End.mul_apply, ← map_mul]
        exact hw _ }
  have hvW : v ∈ S := (hS v).2 hgv
  have htop : K = ⊤ := by
    rcases hπ.eq_bot_or_eq_top Wr with e | e
    · exfalso
      have : v ∈ Wr.toSubmodule := hvW
      rw [e] at this
      exact hv0 this
    · rw [eq_top_iff]
      intro w _
      have : w ∈ Wr.toSubmodule := by rw [e]; trivial
      have := (hS w).1 this 1
      simpa using this
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K b
  exact (Submodule.Quotient.eq K).2 (by rw [htop]; trivial)
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDataIntegralAwayFromLevels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.CplTwoInt

open GlobalTheory.GO.ChRoot (mem_stdAt' intAt_natCast intAt_one' intAt_zero' psi_root)

theorem intOff_prod {S : Finset ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, IntOff S (f i)) :
    IntOff S (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IntOff S) (fun _ _ ha hb => ha.mul hb) IntOff.one h

theorem sNum_pow {S : Finset ℕ} {a : ℕ} (h : SNum S a) (k : ℕ) : SNum S (a ^ k) :=
  ⟨pow_pos h.1 k, fun q hq hd => h.2 q hq (hq.dvd_of_dvd_pow hd)⟩

section Lin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_eval {n : ℕ} (η : Sp E n →ₗ[E] E) (c a : E) (y : Sp E n)
    (hη : ∀ i, IntAt P (c * η (Pi.single i 1))) (hy : a • y ∈ stdAt E n P) : IntAt P (a * c * η y) := by
  have hy' := mem_stdAt'.1 hy
  have e : η y = ∑ i, y i * η (Pi.single i 1) := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (Pi.single i (y i) : Sp E n) = y i • Pi.single i (1 : E) by
      ext j; by_cases h : j = i <;> simp [h, Pi.single_apply], map_smul, smul_eq_mul]
  rw [e, Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun _ _ ha hb => ha.add hb) intAt_zero' fun i _ => ?_
  have := (hy' i).mul (hη i)
  simp only [Pi.smul_apply, smul_eq_mul] at this
  convert this using 1
  ring

theorem smul_symm_mem {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} {f : Sp E n ≃ₗ[E] Sp E n}
    (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P) (a : E) {z : Sp E n} (hz : a • z ∈ localization₂ P.asIdeal N) :
    a • f.symm z ∈ stdAt E n P := by
  rw [← hf, map_smul, LinearEquiv.apply_symm_apply]
  exact hz

end Lin

section Yb

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem repY_mem {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Yb : Set (Sp X.E n)} (hY : Yb ∈ ybSet sel mu cst N)
    (P : rowSG Pr sel mu) :
    ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • repY Yb ∈ localization₂ P.1.asIdeal N := by
  obtain ⟨y, hy, rfl⟩ := hY
  have hq : (qOf P.1 : X.E) ≠ 0 := by exact_mod_cast (GlobalTheory.GO.ChRoot.qOf_pos P.1).ne'
  have hs : ∀ (k : ℕ) v, v ∈ localization₂ P.1.asIdeal N → ((qOf P.1 : X.E) ^ k) • v ∈ localization₂ P.1.asIdeal N := by
    intro k v hv
    have := Submodule.smul_mem _ ((qOf P.1 : 𝓞 X.E) ^ k) hv
    rwa [← algebraMap_smul X.E, map_pow, map_natCast] at this
  have key : ∀ z, z - y ∈ locLat (rowSG Pr sel mu) N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) →
      ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • z ∈ localization₂ P.1.asIdeal N := by
    intro z hz
    rw [mem_locLat] at hy hz
    have h1 := hy P
    have h2 := hz P
    rw [show z = y + (z - y) by abel, smul_add]
    split_ifs at h1 h2 ⊢ with hP
    · refine add_mem ?_ ?_
      · simpa using h1
      · exact hs 1 _ (by simpa using h2)
    · refine add_mem ?_ ?_
      · simpa [zpow_neg] using h1
      · have e : ((qOf P.1 : X.E) ^ cst.M) • (z - y) =
            ((qOf P.1 : X.E) ^ (cst.M + cst.M)) • (((qOf P.1 : X.E) ^ (cst.M : ℤ))⁻¹ • (z - y)) := by
          rw [smul_smul, zpow_natCast, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), mul_one]
        rw [e]
        exact hs _ _ h2
  exact key _ (Classical.epsilon_spec (p := fun z => z - y ∈ locLat (rowSG Pr sel mu) N
    (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))) ⟨y, by simp⟩)

end Yb

end GlobalTheory.CplTwoInt

namespace GlobalTheory.CplTwoInt

open GlobalTheory.GO.ChRoot (mem_stdAt' intAt_natCast intAt_one' intAt_zero' psi_root)

section Ft

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem ftY_intOff (hc : cst.Ok) (P : rowSG Pr sel mu) (hG : P.1 ∈ Pr.vGs → cst.D P = 1)
    (hQ : P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) (σ : X.K →+* ℂ) {B : Finset ℕ} (hB : SNum B (qOf P.1)) {n : ℕ}
    (η : Sp X.E n →ₗ[X.E] X.E) {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • y ∈ stdAt X.E n P.1) :
    IntOff B (σ (ftY sel mu cst P η y)) := by
  have he : IntAt P.1 ((epsSg : ℤ) : X.E) := by simpa [epsSg] using IntAt.coe P.1 (-1 : 𝓞 X.E)
  have hpos : 0 < qOf P.1 ^ cst.D P := pow_pos (GlobalTheory.GO.ChRoot.qOf_pos P.1) _
  unfold ftY
  by_cases hP : P.1 ∈ Pr.vGs
  · rw [if_pos hP] at hy ⊢
    split_ifs with hη
    · refine IntOff.of_pow hpos ?_
      rw [← map_pow, psi_root hc P _ ?_, map_one]
      rw [hG hP, pow_one]
      have h1 := intAt_eval η 1 _ y (fun i => by simpa using hη i) hy
      convert he.mul h1 using 1
      ring
    · simpa using (IntOff.zero : IntOff B 0)
  · rw [if_neg hP] at hy ⊢
    split_ifs with hη
    · rw [map_mul, map_inv₀, map_pow, map_natCast]
      refine IntOff.mul ?_ (IntOff.of_pow hpos ?_)
      · simpa [Nat.cast_pow] using IntOff.inv_nat (sNum_pow hB (cst.M * n))
      · rw [← map_pow, psi_root hc P _ ?_, map_one]
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hQ hP)
        have h1 := intAt_eval η _ _ y hη hy
        have hk' : IntAt P.1 ((qOf P.1 : X.E) ^ k) := by simpa using intAt_natCast (P := P.1) (qOf P.1 ^ k)
        rw [hk]
        convert (he.mul hk').mul h1 using 1
        ring
    · simpa using (IntOff.zero : IntOff B 0)

end Ft

theorem xiCpl2_intOff (hPhi : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
      (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ
      (P : HeightOneSpectrum (𝓞 t.X.E)) x,
      IntOff (t.O u μ).S (t.seam.σ₀ (PhiTop (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp t.m2 P x))) :
    ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ p Yb d x, Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N → IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl2 (R := D.R) (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 p Yb d x)) := by
  intro D L hT Gi Gl K Y cX ex t u μ p Yb d x hY
  have hok := t.idx_ok μ
  unfold XiCpl2
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using (IntOff.one : IntOff (t.O u μ).S 1)
    · simpa using (IntOff.zero : IntOff (t.O u μ).S 0)
  · rw [map_mul]
    refine IntOff.mul (hPhi D L hT Gi Gl K Y cX ex t u μ P.1 _) ?_
    exact ftY_intOff t.sel (t.tup μ) (t.cst μ) hok.cst_ok P (hok.depthG P) (hok.depthQ P) _
      (GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P) _
      (smul_symm_mem (GlobalTheory.ColPeriod.isFrames_frsF p P) _ (repY_mem t.sel (t.tup μ) (t.cst μ) hY P))

theorem xiCpl2_intOff_tied : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ p Yb d x, Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N → IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl2 (R := D.R) (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 p Yb d x)) :=
  xiCpl2_intOff fun D L hT Gi Gl K Y cX ex t u μ P x => (GlobalTheory.T.chain_local_data_integral_off_levels D L hT Gi Gl K Y cX ex t u μ P).2 x

end GlobalTheory.CplTwoInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalLatticeVacuumMemSpanFixedStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLatticeVacuum_mem_span_fixed : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ w : M, GlobalTheory.Hk3.LocVac ρ w → w ∈ Submodule.span ℂ {s} := by
  first | exact @GlobalTheory.Hk3.locVac_mem_span_vac | exact GlobalTheory.Hk3.locVac_mem_span_vac | (intros; apply GlobalTheory.Hk3.locVac_mem_span_vac <;> assumption)
end

