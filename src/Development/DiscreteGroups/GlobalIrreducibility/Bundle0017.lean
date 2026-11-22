import Development.DiscreteGroups.GlobalIrreducibility.LConvIrrPre
import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0015
import Development.DiscreteGroups.GlobalIrreducibility.LConvSepM

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvIrrComm
section
noncomputable section

open scoped InnerProductSpace
open UniformSpace

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

theorem comm_apply {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {S T : E →L[ℂ] E}
    (h : S * T = T * S) (v : E) : S (T v) = T (S v) := by
  have := congrArg (fun A : E →L[ℂ] E => A v) h
  exact this

variable {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)

def formOf (S : Hs B hB →L[ℂ] Hs B hB) : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ⟪iota B hB x, S (iota B hB y)⟫_ℂ)
    (fun x₁ x₂ y => by simp [map_add, inner_add_left])
    (fun c x y => by simp [map_smul, inner_smul_left])
    (fun x y₁ y₂ => by simp [map_add, inner_add_right])
    (fun c x y => by simp [map_smul, inner_smul_right])

theorem formOf_apply (S : Hs B hB →L[ℂ] Hs B hB) (x y : M) :
    formOf B hB S x y = ⟪iota B hB x, S (iota B hB y)⟫_ℂ := rfl

variable {G : Type} [Group G] (ρ : Representation ℂ G M) (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

theorem scalar_sa (hext : IsExtremeForm ρ B) (S : Hs B hB →L[ℂ] Hs B hB) (hS : IsSelfAdjoint S)
    (hc : ∀ g, S * pi B hB ρ hinv g = pi B hB ρ hinv g * S) : ∃ c : ℂ, S = c • 1 := by
  set a : ℝ := (2 * (‖S‖ + 1))⁻¹ with ha_def
  have ha : 0 < a := by positivity
  have hsym : ∀ u v, ⟪S u, v⟫_ℂ = ⟪u, S v⟫_ℂ := fun u v => by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, hS.star_eq]
  have hherm : ∀ x y, starRingEnd ℂ (formOf B hB S x y) = formOf B hB S y x := fun x y => by
    rw [formOf_apply, formOf_apply, inner_conj_symm, hsym]
  have hinvQ : ∀ g x y, formOf B hB S (ρ g x) (ρ g y) = formOf B hB S x y := fun g x y => by
    rw [formOf_apply, formOf_apply, ← pi_iota B hB ρ hinv, ← pi_iota B hB ρ hinv, comm_apply (hc g), pi_inner]
  have hbd : ∀ x, |(formOf B hB S x x).re| ≤ ‖S‖ * ‖iota B hB x‖ ^ 2 := fun x => by
    rw [formOf_apply]
    calc _ ≤ ‖⟪iota B hB x, S (iota B hB x)⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖iota B hB x‖ * ‖S (iota B hB x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖iota B hB x‖ * (‖S‖ * ‖iota B hB x‖) := by gcongr; exact S.le_opNorm _
      _ = _ := by ring
  have key : ∀ x, |a * (formOf B hB S x x).re| ≤ (B x x).re / 2 := fun x => by
    rw [re_B B hB, abs_mul, abs_of_pos ha]
    calc a * |(formOf B hB S x x).re| ≤ a * ((‖S‖ + 1) * ‖iota B hB x‖ ^ 2) := by
          gcongr; exact (hbd x).trans (by gcongr; linarith)
      _ = _ := by rw [ha_def]; field_simp
  have h1 : IsInvForm ρ (((1 / 2 : ℝ) : ℂ) • B + (a : ℂ) • formOf B hB S) := by
    refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩ <;>
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    · rw [map_add, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, hB.1, hherm]
    · rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      have := abs_le.1 (key x); linarith
    · rw [hext.1.2.2, hinvQ]
  have h2 : IsInvForm ρ (B - (((1 / 2 : ℝ) : ℂ) • B + (a : ℂ) • formOf B hB S)) := by
    refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩ <;>
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    · rw [map_sub, map_add, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, hB.1, hherm]
    · rw [Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      have := abs_le.1 (key x); linarith
    · rw [hext.1.2.2, hinvQ]
  obtain ⟨c, hc'⟩ := hext.2 _ h1 h2
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hQ : ∀ x y, formOf B hB S x y = ((a : ℂ)⁻¹ * (c - ((1 / 2 : ℝ) : ℂ))) * B x y := fun x y => by
    have h := hc' x y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h
    rw [mul_assoc, eq_inv_mul_iff_mul_eq₀ ha']
    linear_combination h
  set d := (a : ℂ)⁻¹ * (c - ((1 / 2 : ℝ) : ℂ))
  have hQ' : ∀ x y : M, ⟪iota B hB x, S (iota B hB y)⟫_ℂ = d * ⟪iota B hB x, iota B hB y⟫_ℂ := fun x y => by
    rw [inner_iota, ← formOf_apply]; exact hQ x y
  have hall : ∀ u v : Hs B hB, ⟪u, S v⟫_ℂ = d * ⟪u, v⟫_ℂ := by
    intro u v
    refine Completion.induction_on₂ u v ?_ fun p q => ?_
    · exact isClosed_eq (continuous_fst.inner (S.continuous.comp continuous_snd))
        (continuous_const.mul (continuous_fst.inner continuous_snd))
    · exact hQ' p q
  refine ⟨d, ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_⟩
  rw [hall, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]

theorem commutant (hext : IsExtremeForm ρ B) (T : Hs B hB →L[ℂ] Hs B hB)
    (hT : ∀ g, T * pi B hB ρ hinv g = pi B hB ρ hinv g * T) : ∃ c : ℂ, T = c • 1 := by
  have hT' : ∀ g, star T * pi B hB ρ hinv g = pi B hB ρ hinv g * star T := fun g => by
    have h := congrArg star (hT g⁻¹)
    simp only [star_mul, star_pi, inv_inv] at h
    exact h.symm
  have hre : ∀ g, (realPart T : Hs B hB →L[ℂ] Hs B hB) * pi B hB ρ hinv g =
      pi B hB ρ hinv g * realPart T := fun g => by
    simp only [realPart_apply_coe, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hT, hT']
  have him : ∀ g, (imaginaryPart T : Hs B hB →L[ℂ] Hs B hB) * pi B hB ρ hinv g =
      pi B hB ρ hinv g * imaginaryPart T := fun g => by
    simp only [imaginaryPart_apply_coe, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, hT, hT']
  obtain ⟨c₁, h₁⟩ := scalar_sa B hB ρ hinv hext _ (realPart T).prop hre
  obtain ⟨c₂, h₂⟩ := scalar_sa B hB ρ hinv hext _ (imaginaryPart T).prop him
  refine ⟨c₁ + Complex.I * c₂, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T]
  rw [h₁, h₂, smul_smul, add_smul]

end DiscreteGroups.sglob.LConv.IrreduciblePresentation
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvSepF
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

theorem form_eq_zero_of_self {M : Type} [AddCommGroup M] [Module ℂ M] {B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ}
    (hh : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (hp : ∀ x, 0 ≤ (B x x).re) {z : M} (hz : B z z = 0)
    (x : M) : B z x = 0 := by
  by_contra ha
  have hn : 0 < Complex.normSq (B z x) := Complex.normSq_pos.2 ha
  have hxz : B x z = (starRingEnd ℂ) (B z x) := (hh z x).symm
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 2 * t * Complex.normSq (B z x) = (B x x).re + 1 :=
    ⟨((B x x).re + 1) / (2 * Complex.normSq (B z x)), by field_simp⟩
  have key := hp (x + ((-(t : ℂ)) * B z x) • z)
  have e1 : B (x + ((-(t : ℂ)) * B z x) • z) (x + ((-(t : ℂ)) * B z x) • z) =
      B x x + (-(t : ℂ)) * B z x * (starRingEnd ℂ) (B z x) +
        (starRingEnd ℂ) (-(t : ℂ) * B z x) * B z x := by
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, hz, hxz]
    ring
  have e2 : (B (x + ((-(t : ℂ)) * B z x) • z) (x + ((-(t : ℂ)) * B z x) • z)).re =
      (B x x).re - 2 * t * Complex.normSq (B z x) := by
    rw [e1]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, map_mul, map_neg,
      Complex.conj_ofReal, Complex.normSq_apply]
    ring
  linarith

theorem circle_conj_mul (z : Circle) : (starRingEnd ℂ) (z : ℂ) * z = 1 := by
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]

theorem conj_mul_self_re (z : ℂ) : ((starRingEnd ℂ) z * z).re = Complex.normSq z := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle}

theorem conj_psi (c : k) : (starRingEnd ℂ) ((ψ c : Circle) : ℂ) = ((ψ⁻¹ c : Circle) : ℂ) := by
  rw [AddChar.inv_apply', Circle.coe_inv_eq_conj]

theorem superDiag_inv {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) : superDiag u⁻¹ = -superDiag u := by
  have h := superDiag_mul ((unipB k (Fin m)).inv_mem hu) hu
  rw [inv_mul_cancel, superDiag_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem superDiag_conj {u n : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) (hn : n ∈ unipB k (Fin m)) :
    superDiag (u⁻¹ * n * u) = superDiag n := by
  have hu' := (unipB k (Fin m)).inv_mem hu
  rw [superDiag_mul ((unipB k (Fin m)).mul_mem hu' hn) hu, superDiag_mul hu' hn, superDiag_inv hu]
  ring

theorem delta_one {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) : (delta ψ K : GL (Fin m) k → ℂ) 1 = 1 := by
  have := delta_mul hK (unipB k (Fin m)).one_mem K.one_mem
  rw [mul_one, superDiag_one, AddChar.map_zero_eq_one, Circle.coe_one] at this
  exact this

theorem delta_ne_zero {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) : delta ψ K ≠ 0 := fun h => by
  have := delta_one hK
  rw [h] at this
  exact zero_ne_one this

theorem delta_eq_of_le {K K' : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (hK' : Good ψ K') (hle : K' ≤ K)
    (g : GL (Fin m) k) (hg : (delta ψ K' : GL (Fin m) k → ℂ) g ≠ 0) :
    (delta ψ K : GL (Fin m) k → ℂ) g = (delta ψ K' : GL (Fin m) k → ℂ) g := by
  obtain ⟨u, hu, κ, hκ, rfl⟩ : ∃ u ∈ unipB k (Fin m), ∃ κ ∈ K', g = u * κ := by
    by_contra h
    exact hg (delta_eq_zero h)
  rw [delta_mul hK hu (hle hκ), delta_mul hK' hu hκ]

theorem good_conj {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) {u : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) : Good ψ (K.map (MulAut.conj u).toMonoidHom) := by
  have e : ((K.map (MulAut.conj u).toMonoidHom : Subgroup (GL (Fin m) k)) : Set (GL (Fin m) k)) =
      (fun y => u⁻¹ * y * u) ⁻¹' K := Set.ext fun _ => mem_conj
  have hc : Continuous fun κ : GL (Fin m) k => u * κ * u⁻¹ := by fun_prop
  refine ⟨?_, ?_, fun n hn hnK => ?_⟩
  · rw [e]
    exact hK.1.preimage (by fun_prop)
  · rw [Subgroup.coe_map]
    exact hK.2.1.image hc
  · rw [← superDiag_conj hu hn]
    exact hK.2.2 _ ((unipB k (Fin m)).mul_mem ((unipB k (Fin m)).mul_mem
      ((unipB k (Fin m)).inv_mem hu) hn) hu) (mem_conj.1 hnK)

end DiscreteGroups.sglob.LConv

end
end

