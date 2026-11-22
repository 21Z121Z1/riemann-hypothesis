import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0035
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportConvolutionTriple
section
namespace GlobalTheory.CompanionTheory.HeckeProduct

section Single

variable {G M V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem out_invariant (K : Subgroup G) (F : G → M) (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) (g : G) :
    F ((g : G ⧸ K).out) = F g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
  rw [hh]; exact hF g h h.2

noncomputable def heckeSum (π : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) (u : V) : V :=
  ∑ᶠ q : G ⧸ K, f q.out • π q.out u

variable (π : Representation ℂ G V) (K : Subgroup G) {f : G → ℂ}

theorem term_support_subset (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) (u : V) :
    (Function.support fun q : G ⧸ K => f q.out • π q.out u) ⊆ hf.toFinset := by
  intro q hq
  simp only [Set.Finite.coe_toFinset, Function.mem_support]
  intro h0
  exact hq (by simp [h0])

theorem heckeSum_eq_sum (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) (u : V) :
    heckeSum π K f u = ∑ q ∈ hf.toFinset, f q.out • π q.out u :=
  finsum_eq_sum_of_support_subset _ (term_support_subset π K hf u)

theorem map_heckeSum (hf : (Function.support fun q : G ⧸ K => f q.out).Finite)
    (T : V →ₗ[ℂ] V) (hT : ∀ g u, T (π g u) = π g (T u)) (u : V) :
    T (heckeSum π K f u) = heckeSum π K f (T u) := by
  rw [heckeSum_eq_sum π K hf, heckeSum_eq_sum π K hf, map_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [map_smul, hT]

noncomputable def heckeLin (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) : V →ₗ[ℂ] V :=
  ∑ q ∈ hf.toFinset, f q.out • π q.out

theorem heckeLin_apply (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) (u : V) :
    heckeLin π K hf u = heckeSum π K f u := by
  rw [heckeSum_eq_sum π K hf, heckeLin, LinearMap.sum_apply]
  rfl

theorem heckeSum_fixed (hf : (Function.support fun q : G ⧸ K => f q.out).Finite)
    (hl : ∀ k ∈ K, ∀ g, f (k * g) = f g) (hr : ∀ k ∈ K, ∀ g, f (g * k) = f g)
    (u : V) (hu : ∀ k ∈ K, π k u = u) (k : G) (hk : k ∈ K) :
    π k (heckeSum π K f u) = heckeSum π K f u := by
  have hF : ∀ g, ∀ c ∈ K, (fun g => f g • π g u) (g * c) = (fun g => f g • π g u) g := by
    intro g c hc
    simp only [map_mul, Module.End.mul_apply, hu c hc, hr c hc]
  have key : ∀ q : G ⧸ K, π k (f q.out • π q.out u)
      = (fun q : G ⧸ K => f q.out • π q.out u) ((MulAction.toPerm k : Equiv.Perm (G ⧸ K)) q) := by
    intro q
    have hq : (MulAction.toPerm k : Equiv.Perm (G ⧸ K)) q = ((k * q.out : G) : G ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have h1 := out_invariant K (fun g => f g • π g u) hF (k * q.out)
    simp only [hq]
    rw [h1, map_smul, hl k hk, map_mul, Module.End.mul_apply]
  have h2 : π k (heckeSum π K f u) = ∑ᶠ q : G ⧸ K, π k (f q.out • π q.out u) := by
    rw [heckeSum_eq_sum π K hf, map_sum]
    refine (finsum_eq_sum_of_support_subset _ ?_).symm
    intro q hq
    refine term_support_subset π K hf u ?_
    intro h0
    exact hq (by simp only [h0, map_zero])
  rw [h2, finsum_congr key]
  exact finsum_comp_equiv (f := fun q : G ⧸ K => f q.out • π q.out u)
    (MulAction.toPerm k : Equiv.Perm (G ⧸ K))

end Single

section Product

variable {G₁ G₂ V : Type} [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V]

noncomputable def cosetPairEquiv (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) :
    (G₁ ⧸ K₁) × (G₂ ⧸ K₂) ≃ (G₁ × G₂) ⧸ K₁.prod K₂ :=
  Equiv.ofBijective (fun p => (((p.1.out, p.2.out) : G₁ × G₂) : (G₁ × G₂) ⧸ K₁.prod K₂)) (by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h' := QuotientGroup.eq.1 h
      rw [Subgroup.mem_prod] at h'
      have ha : (a.out : G₁ ⧸ K₁) = a'.out := QuotientGroup.eq.2 h'.1
      have hb : (b.out : G₂ ⧸ K₂) = b'.out := QuotientGroup.eq.2 h'.2
      simp only [QuotientGroup.out_eq'] at ha hb
      rw [ha, hb]
    · intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        refine ⟨((g.1 : G₁ ⧸ K₁), (g.2 : G₂ ⧸ K₂)), ?_⟩
        obtain ⟨c₁, h₁⟩ := QuotientGroup.mk_out_eq_mul K₁ g.1
        obtain ⟨c₂, h₂⟩ := QuotientGroup.mk_out_eq_mul K₂ g.2
        refine QuotientGroup.eq.2 ?_
        rw [Subgroup.mem_prod]
        simp only [h₁, h₂, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
        constructor
        · simpa using K₁.inv_mem c₁.2
        · simpa using K₂.inv_mem c₂.2)

variable (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)

noncomputable abbrev left : Representation ℂ G₁ V := ρ.comp (MonoidHom.inl G₁ G₂)

noncomputable abbrev right : Representation ℂ G₂ V := ρ.comp (MonoidHom.inr G₁ G₂)

theorem left_right_comm (g : G₁) (h : G₂) (u : V) :
    left ρ g (right ρ h u) = right ρ h (left ρ g u) := by
  have e1 : left ρ g (right ρ h u) = ρ ((g, 1) * (1, h)) u := by
    rw [map_mul]; rfl
  have e2 : right ρ h (left ρ g u) = ρ ((1, h) * (g, 1)) u := by
    rw [map_mul]; rfl
  rw [e1, e2]; simp

theorem left_right_mul (g : G₁) (h : G₂) (u : V) :
    ρ (g, h) u = left ρ g (right ρ h u) := by
  have : ((g, h) : G₁ × G₂) = (g, 1) * (1, h) := by simp
  rw [this, map_mul]; rfl

variable {f : G₁ → ℂ} {f' : G₂ → ℂ}

theorem sum_left_right_comm (hf : (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite)
    (hf' : (Function.support fun q : G₂ ⧸ K₂ => f' q.out).Finite) (u : V) :
    heckeSum (left ρ) K₁ f (heckeSum (right ρ) K₂ f' u)
      = heckeSum (right ρ) K₂ f' (heckeSum (left ρ) K₁ f u) := by
  rw [← heckeLin_apply (left ρ) K₁ hf, ← heckeLin_apply (left ρ) K₁ hf]
  refine map_heckeSum (right ρ) K₂ hf' _ (fun h w => ?_) u
  rw [heckeLin_apply (left ρ) K₁ hf, heckeLin_apply (left ρ) K₁ hf]
  exact map_heckeSum (left ρ) K₁ hf (right ρ h) (fun g w => (left_right_comm ρ g h w).symm) w |>.symm

theorem product_sum (hf : (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite)
    (hf' : (Function.support fun q : G₂ ⧸ K₂ => f' q.out).Finite)
    (hr : ∀ k ∈ K₁, ∀ g, f (g * k) = f g) (hr' : ∀ k ∈ K₂, ∀ g, f' (g * k) = f' g)
    (u : V) (hu : ∀ k ∈ K₁.prod K₂, ρ k u = u) :
    ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f q.out.1 * f' q.out.2) • ρ q.out u
      = heckeSum (left ρ) K₁ f (heckeSum (right ρ) K₂ f' u) := by
  have hF : ∀ g, ∀ c ∈ K₁.prod K₂, (fun g : G₁ × G₂ => (f g.1 * f' g.2) • ρ g u) (g * c)
      = (fun g : G₁ × G₂ => (f g.1 * f' g.2) • ρ g u) g := by
    intro g c hc
    have hc' := Subgroup.mem_prod.1 hc
    simp only [map_mul, Module.End.mul_apply, hu c hc, Prod.fst_mul, Prod.snd_mul,
      hr c.1 hc'.1, hr' c.2 hc'.2]
  rw [← finsum_comp_equiv (cosetPairEquiv K₁ K₂)]
  have h1 : ∀ p : (G₁ ⧸ K₁) × (G₂ ⧸ K₂),
      (f ((cosetPairEquiv K₁ K₂ p).out.1) * f' ((cosetPairEquiv K₁ K₂ p).out.2)) •
        ρ (cosetPairEquiv K₁ K₂ p).out u = (f p.1.out * f' p.2.out) • ρ (p.1.out, p.2.out) u :=
    fun p => out_invariant (K₁.prod K₂) (fun g : G₁ × G₂ => (f g.1 * f' g.2) • ρ g u) hF
      (p.1.out, p.2.out)
  rw [finsum_congr h1, finsum_eq_sum_of_support_subset (s := hf.toFinset ×ˢ hf'.toFinset) _ ?_,
    Finset.sum_product, heckeSum_eq_sum _ K₁ hf]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [heckeSum_eq_sum _ K₂ hf', map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [left_right_mul, map_smul, smul_smul]
  · rintro ⟨a, b⟩ hp
    simp only [Finset.coe_product, Set.Finite.coe_toFinset, Set.mem_prod, Function.mem_support]
    constructor
    · intro h0; exact hp (by simp [h0])
    · intro h0; exact hp (by simp [h0])

theorem fixed_left (hf : (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite)
    (hl : ∀ k ∈ K₁, ∀ g, f (k * g) = f g) (hr : ∀ k ∈ K₁, ∀ g, f (g * k) = f g)
    (u : V) (hu : ∀ k ∈ K₁.prod K₂, ρ k u = u) :
    ∀ c ∈ K₁.prod K₂, ρ c (heckeSum (left ρ) K₁ f u) = heckeSum (left ρ) K₁ f u := by
  rintro ⟨c₁, c₂⟩ hc
  have hc' := Subgroup.mem_prod.1 hc
  have hu₁ : ∀ k ∈ K₁, left ρ k u = u := fun k hk =>
    hu (k, 1) (Subgroup.mem_prod.2 ⟨hk, K₂.one_mem⟩)
  have hu₂ : right ρ c₂ u = u := hu (1, c₂) (Subgroup.mem_prod.2 ⟨K₁.one_mem, hc'.2⟩)
  rw [left_right_mul, map_heckeSum (left ρ) K₁ hf (right ρ c₂)
    (fun g w => (left_right_comm ρ g c₂ w).symm), hu₂]
  exact heckeSum_fixed (left ρ) K₁ hf hl hr u hu₁ c₁ hc'.1

theorem fixed_right (hf' : (Function.support fun q : G₂ ⧸ K₂ => f' q.out).Finite)
    (hl : ∀ k ∈ K₂, ∀ g, f' (k * g) = f' g) (hr : ∀ k ∈ K₂, ∀ g, f' (g * k) = f' g)
    (u : V) (hu : ∀ k ∈ K₁.prod K₂, ρ k u = u) :
    ∀ c ∈ K₁.prod K₂, ρ c (heckeSum (right ρ) K₂ f' u) = heckeSum (right ρ) K₂ f' u := by
  rintro ⟨c₁, c₂⟩ hc
  have hc' := Subgroup.mem_prod.1 hc
  have hu₁ : left ρ c₁ u = u := hu (c₁, 1) (Subgroup.mem_prod.2 ⟨hc'.1, K₂.one_mem⟩)
  have hu₂ : ∀ k ∈ K₂, right ρ k u = u := fun k hk =>
    hu (1, k) (Subgroup.mem_prod.2 ⟨K₁.one_mem, hk⟩)
  rw [left_right_mul, heckeSum_fixed (right ρ) K₂ hf' hl hr u hu₂ c₂ hc'.2,
    map_heckeSum (right ρ) K₂ hf' (left ρ c₁) (fun h w => left_right_comm ρ c₁ h w), hu₁]

end Product

theorem product_operators_mul : ∀ (G₁ G₂ V : Type) [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (f₁ f₁' f₁'' : G₁ → ℂ) (f₂ f₂' f₂'' : G₂ → ℂ), (∀ f ∈ ({f₁, f₁', f₁''} : Set (G₁ → ℂ)), (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite ∧ ∀ k ∈ K₁, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → (∀ f ∈ ({f₂, f₂', f₂''} : Set (G₂ → ℂ)), (Function.support fun q : G₂ ⧸ K₂ => f q.out).Finite ∧ ∀ k ∈ K₂, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → (∀ v : V, (∀ k ∈ K₁, ρ (k, 1) v = v) → ∑ᶠ q : G₁ ⧸ K₁, f₁'' q.out • ρ (q.out, 1) v = ∑ᶠ q : G₁ ⧸ K₁, f₁ q.out • ρ (q.out, 1) (∑ᶠ q' : G₁ ⧸ K₁, f₁' q'.out • ρ (q'.out, 1) v)) → (∀ v : V, (∀ k ∈ K₂, ρ (1, k) v = v) → ∑ᶠ q : G₂ ⧸ K₂, f₂'' q.out • ρ (1, q.out) v = ∑ᶠ q : G₂ ⧸ K₂, f₂ q.out • ρ (1, q.out) (∑ᶠ q' : G₂ ⧸ K₂, f₂' q'.out • ρ (1, q'.out) v)) → ∀ v : V, (∀ k ∈ K₁.prod K₂, ρ k v = v) → ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁'' q.out.1 * f₂'' q.out.2) • ρ q.out v = ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁ q.out.1 * f₂ q.out.2) • ρ q.out (∑ᶠ q' : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁' q'.out.1 * f₂' q'.out.2) • ρ q'.out v) := by
  intro G₁ G₂ V _ _ _ _ ρ K₁ K₂ f₁ f₁' f₁'' f₂ f₂' f₂'' h1 h2 hA hB v hv
  obtain ⟨a, ai⟩ := h1 f₁ (by simp)
  obtain ⟨a', ai'⟩ := h1 f₁' (by simp)
  obtain ⟨a'', ai''⟩ := h1 f₁'' (by simp)
  obtain ⟨b, bi⟩ := h2 f₂ (by simp)
  obtain ⟨b', bi'⟩ := h2 f₂' (by simp)
  obtain ⟨b'', bi''⟩ := h2 f₂'' (by simp)
  have hA' : ∀ w : V, (∀ k ∈ K₁, left ρ k w = w) → heckeSum (left ρ) K₁ f₁'' w
      = heckeSum (left ρ) K₁ f₁ (heckeSum (left ρ) K₁ f₁' w) := hA
  have hB' : ∀ w : V, (∀ k ∈ K₂, right ρ k w = w) → heckeSum (right ρ) K₂ f₂'' w
      = heckeSum (right ρ) K₂ f₂ (heckeSum (right ρ) K₂ f₂' w) := hB
  have hv₂ : ∀ k ∈ K₂, right ρ k v = v := fun k hk =>
    hv (1, k) (Subgroup.mem_prod.2 ⟨K₁.one_mem, hk⟩)
  have hy := fixed_right ρ K₁ K₂ b' (fun k hk g => (bi' k hk g).1) (fun k hk g => (bi' k hk g).2) v hv
  have hx := fixed_right ρ K₁ K₂ b (fun k hk g => (bi k hk g).1) (fun k hk g => (bi k hk g).2) _ hy
  have hw := fixed_left ρ K₁ K₂ a' (fun k hk g => (ai' k hk g).1) (fun k hk g => (ai' k hk g).2) _ hy
  have hx₁ : ∀ k ∈ K₁, left ρ k (heckeSum (right ρ) K₂ f₂ (heckeSum (right ρ) K₂ f₂' v))
      = heckeSum (right ρ) K₂ f₂ (heckeSum (right ρ) K₂ f₂' v) := fun k hk =>
    hx (k, 1) (Subgroup.mem_prod.2 ⟨hk, K₂.one_mem⟩)
  rw [product_sum ρ K₁ K₂ a'' b'' (fun k hk g => (ai'' k hk g).2) (fun k hk g => (bi'' k hk g).2) v hv,
    product_sum ρ K₁ K₂ a' b' (fun k hk g => (ai' k hk g).2) (fun k hk g => (bi' k hk g).2) v hv,
    product_sum ρ K₁ K₂ a b (fun k hk g => (ai k hk g).2) (fun k hk g => (bi k hk g).2) _ hw,
    hB' v hv₂, hA' _ hx₁, sum_left_right_comm ρ K₁ K₂ a' b]

end GlobalTheory.CompanionTheory.HeckeProduct
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInversionProd
section
noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open scoped FourierTransform

namespace GlobalTheory.CompanionTheory.TubeFourier

def planeCoord : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem planeCoord_apply (v : EuclideanSpace ℝ (Fin 2)) : planeCoord v = (v 0, v 1) := rfl

theorem continuous_planeCoord : Continuous planeCoord := by
  rw [show (planeCoord : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ) = fun v => (v 0, v 1) from funext planeCoord_apply]
  fun_prop

theorem measurePreserving_planeCoord : MeasurePreserving planeCoord volume volume := by
  exact (volume_preserving_finTwoArrow ℝ).comp (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

theorem inner_eq_rdot (v w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ v w = rdot (planeCoord v) (planeCoord w) := by
  rw [planeCoord_apply, planeCoord_apply]
  simp [rdot, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem fourier_comp_planeCoord {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (h : ℝ × ℝ → X) (w : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (fun v => h (planeCoord v)) w =
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y ((2 * Real.pi) • planeCoord w) : ℝ) : ℂ))) • h y := by
  rw [Real.fourier_eq', ← measurePreserving_planeCoord.integral_comp'
    (fun y : ℝ × ℝ => Complex.exp (-(Complex.I * ((rdot y ((2 * Real.pi) • planeCoord w) : ℝ) : ℂ))) • h y)]
  congr 1
  ext v
  rw [inner_eq_rdot]
  congr 2
  simp only [rdot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  push_cast
  ring

theorem fourier_inversion_prod : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (h : ℝ × ℝ → X), Continuous h → Integrable h → Integrable (fun t : ℝ × ℝ => ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • h y) → ∀ y : ℝ × ℝ, h y = (((2 * Real.pi) ^ 2 : ℂ)⁻¹) • ∫ t : ℝ × ℝ, Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • ∫ y' : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y' t : ℝ) : ℂ))) • h y' := by
  intro X _ _ _ h hc hi hT y
  set T : ℝ × ℝ → X := fun t => ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • h y with hTdef
  set f : EuclideanSpace ℝ (Fin 2) → X := fun v => h (planeCoord v) with hf
  have hfc : Continuous f := hc.comp continuous_planeCoord
  have hfi : Integrable f :=
    (measurePreserving_planeCoord.integrable_comp_emb planeCoord.measurableEmbedding).mpr hi
  have hFf : ∀ w, 𝓕 f w = T ((2 * Real.pi) • planeCoord w) := fun w => fourier_comp_planeCoord h w
  have hFi : Integrable (𝓕 f) := by
    rw [show 𝓕 f = fun w => T ((2 * Real.pi) • planeCoord w) from funext hFf]
    have h1 : Integrable (fun t : ℝ × ℝ => T ((2 * Real.pi) • t)) := hT.comp_smul (by positivity)
    exact (measurePreserving_planeCoord.integrable_comp_emb planeCoord.measurableEmbedding).mpr h1
  have hinv := congrFun (hfc.fourierInv_fourier_eq hfi hFi) (planeCoord.symm y)
  have hsub := Measure.integral_comp_smul (μ := (volume : Measure (ℝ × ℝ)))
    (f := fun t => Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • T t) (R := 2 * Real.pi)
  have hrank : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hrank] at hsub
  have hlhs : 𝓕⁻ (𝓕 f) (planeCoord.symm y) = ∫ s : ℝ × ℝ,
      (fun t => Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • T t) ((2 * Real.pi) • s) := by
    rw [Real.fourierInv_eq', ← measurePreserving_planeCoord.integral_comp'
      (fun s : ℝ × ℝ => (fun t => Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • T t) ((2 * Real.pi) • s))]
    congr 1
    ext w
    simp only [hFf, inner_eq_rdot, MeasurableEquiv.apply_symm_apply]
    congr 2
    simp only [rdot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    push_cast
    ring
  rw [hinv] at hlhs
  have hy : h y = f (planeCoord.symm y) := by simp [hf]
  rw [hy, hlhs, hsub, abs_of_pos (by positivity), ← Complex.coe_smul]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.TubeFourier
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianTubeTransformBound
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem integrable_gauss_one : Integrable (fun s : ℝ => Real.exp (-s ^ 2)) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

theorem integral_gauss_one : ∫ s : ℝ, Real.exp (-s ^ 2) = Real.sqrt Real.pi := by
  simpa using integral_gaussian 1

theorem integrable_gauss_prod :
    Integrable (fun y : ℝ × ℝ => Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) :=
  Integrable.mul_prod integrable_gauss_one integrable_gauss_one

theorem integral_gauss_prod :
    ∫ y : ℝ × ℝ, Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2) = Real.pi := by
  rw [Measure.volume_eq_prod, integral_prod_mul (fun s : ℝ => Real.exp (-s ^ 2)) (fun s : ℝ => Real.exp (-s ^ 2)),
    integral_gauss_one, Real.mul_self_sqrt Real.pi_pos.le]

theorem re_dot_pt (x y t : ℝ × ℝ) : (dot (pt x y) t).re = rdot x t := by
  simp [dot, pt, rdot, Complex.mul_re]

theorem norm_phi_le : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (G : ℂ × ℂ → X) (x : ℝ × ℝ) (M : ℝ),
    (∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) →
    ∀ t : ℝ × ℝ, ‖phi G x t‖ ≤ M * Real.pi * Real.exp (-rdot x t) := by
  intro X _ _ G x M hG t
  have hb : ∀ y : ℝ × ℝ, ‖Complex.exp (-dot (pt x y) t) • G (pt x y)‖ ≤
      M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
    intro y
    rw [norm_smul, Complex.norm_exp, Complex.neg_re, re_dot_pt]
    calc Real.exp (-rdot x t) * ‖G (pt x y)‖
        ≤ Real.exp (-rdot x t) * (M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) :=
          mul_le_mul_of_nonneg_left (hG y) (Real.exp_pos _).le
      _ = M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
          rw [neg_add, Real.exp_add]; ring
  unfold phi
  calc ‖∫ y : ℝ × ℝ, Complex.exp (-dot (pt x y) t) • G (pt x y)‖
      ≤ ∫ y : ℝ × ℝ, M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) :=
        norm_integral_le_of_norm_le (Integrable.const_mul integrable_gauss_prod _) (Eventually.of_forall hb)
    _ = M * Real.pi * Real.exp (-rdot x t) := by
        rw [integral_const_mul, integral_gauss_prod]; ring

end GlobalTheory.CompanionTheory.TubeFourier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianTubeTransformContinuous
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem re_dot_pt_eq_rdot (x y t : ℝ × ℝ) : (dot (pt x y) t).re = rdot x t := by
  simp [dot, pt, rdot]

theorem integrable_gaussian_plane :
    Integrable (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) (volume : Measure (ℝ × ℝ)) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-1 * x ^ 2)) := integrable_exp_neg_mul_sq one_pos
  have h := h1.mul_prod h1
  have e : (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) =
      fun z : ℝ × ℝ => Real.exp (-1 * z.1 ^ 2) * Real.exp (-1 * z.2 ^ 2) := by
    funext z
    rw [← Real.exp_add]
    ring_nf
  rw [e]
  exact h

theorem phi_joint_continuous (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T]
    [FirstCountableTopology T] (G : T → ℂ × ℂ → X) (x : ℝ × ℝ)
    (hG : Continuous (fun p : (ℝ × ℝ) × T => G p.2 (pt x p.1)))
    (hb : ∀ g : T, ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ g' ∈ U, ∀ y : ℝ × ℝ,
      ‖G g' (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) :
    Continuous (fun p : (ℝ × ℝ) × T => phi (G p.2) x p.1) := by
  have hform : ∀ y t : ℝ × ℝ, dot (pt x y) t =
      ((x.1 * t.1 + x.2 * t.2 : ℝ) : ℂ) + ((y.1 * t.1 + y.2 * t.2 : ℝ) : ℂ) * Complex.I := by
    intro y t
    apply Complex.ext <;> simp [dot, pt]
  have hdt : ∀ y : ℝ × ℝ, Continuous (fun t : ℝ × ℝ => Complex.exp (-dot (pt x y) t)) := by
    intro y
    simp_rw [hform]
    fun_prop
  have hdy : ∀ t : ℝ × ℝ, Continuous (fun y : ℝ × ℝ => Complex.exp (-dot (pt x y) t)) := by
    intro t
    simp_rw [hform]
    fun_prop
  have hnorm : ∀ y t : ℝ × ℝ, ‖Complex.exp (-dot (pt x y) t)‖ = Real.exp (-rdot x t) := by
    intro y t
    rw [Complex.norm_exp, Complex.neg_re, re_dot_pt_eq_rdot]
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨U, hU, M, hM⟩ := hb p₀.2
  have hr : Continuous (fun p : (ℝ × ℝ) × T => Real.exp (-rdot x p.1)) := by
    unfold rdot
    fun_prop
  have hV : ∀ᶠ p in 𝓝 p₀, Real.exp (-rdot x p.1) < Real.exp (-rdot x p₀.1) + 1 :=
    (hr.tendsto p₀).eventually (eventually_lt_nhds (lt_add_one _))
  have hU' : ∀ᶠ p in 𝓝 p₀, p.2 ∈ U := continuous_snd.continuousAt.preimage_mem_nhds hU
  unfold phi
  refine continuousAt_of_dominated
    (bound := fun y => (Real.exp (-rdot x p₀.1) + 1) * (|M| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)))) ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun p => ?_
    apply Continuous.aestronglyMeasurable
    exact (hdy p.1).smul (hG.comp (continuous_id.prodMk continuous_const))
  · filter_upwards [hV, hU'] with p hp1 hp2
    refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_smul, hnorm]
    have hg := hM p.2 hp2 y
    have hg' : ‖G p.2 (pt x y)‖ ≤ |M| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) :=
      hg.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le)
    calc Real.exp (-rdot x p.1) * ‖G p.2 (pt x y)‖
        ≤ Real.exp (-rdot x p.1) * (|M| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) :=
          mul_le_mul_of_nonneg_left hg' (Real.exp_pos _).le
      _ ≤ (Real.exp (-rdot x p₀.1) + 1) * (|M| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) :=
          mul_le_mul_of_nonneg_right hp1.le (mul_nonneg (abs_nonneg M) (Real.exp_pos _).le)
  · exact (integrable_gaussian_plane.const_mul _).const_mul _
  · refine Filter.Eventually.of_forall fun y => ?_
    exact (((hdt y).comp continuous_fst).smul (hG.comp (continuous_const.prodMk continuous_snd))).continuousAt

end GlobalTheory.CompanionTheory.TubeFourier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSumInvariant
section
namespace GlobalTheory.CompanionTheory.Hecke

theorem heckeSum_fixed :
    ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (K : Subgroup G) (f : G → ℂ), (Function.support fun q : G ⧸ K => f q.out).Finite →
      (∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → ∀ v : V, (∀ k ∈ K, ρ k v = v) →
      ∀ k ∈ K, ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v) = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v := by
  intro G V _ _ _ ρ K f hfin hbi v hv k hk
  have hsupp : (Function.support fun q : G ⧸ K => f q.out • ρ q.out v).Finite := by
    refine hfin.subset ?_
    intro q hq h0
    apply hq
    have h0' : f q.out = 0 := h0
    simp [h0']
  have hstep : ∀ q : G ⧸ K, ρ k (f q.out • ρ q.out v)
      = f (MulAction.toPerm k q).out • ρ (MulAction.toPerm k q).out v := by
    intro q
    have hmk : ((MulAction.toPerm k q : G ⧸ K).out : G ⧸ K) = ((k * q.out : G) : G ⧸ K) := by
      rw [QuotientGroup.out_eq', MulAction.toPerm_apply]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hκ : (k * q.out)⁻¹ * (MulAction.toPerm k q : G ⧸ K).out ∈ K :=
      QuotientGroup.eq.mp hmk.symm
    obtain ⟨κ, hκK, hκ⟩ : ∃ κ ∈ K, (MulAction.toPerm k q : G ⧸ K).out = k * q.out * κ :=
      ⟨_, hκ, by group⟩
    rw [hκ, (hbi κ hκK _).2, (hbi k hk _).1, map_mul, map_mul, map_smul]
    simp [hv κ hκK]
  have h1 := (ρ k).toAddMonoidHom.map_finsum hsupp
  have h2 : ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v)
      = ∑ᶠ q : G ⧸ K, ρ k (f q.out • ρ q.out v) := h1
  rw [h2, finsum_congr hstep]
  exact finsum_comp_equiv (MulAction.toPerm k) (f := fun q : G ⧸ K => f q.out • ρ q.out v)

end GlobalTheory.CompanionTheory.Hecke
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeThirdProperty
section
namespace GlobalTheory.CompanionTheory.TwistedCent

open PositivityTheory.Rg.Tf.Loc

theorem mem_twCent_twConj_iff {G : Type} [Group G] (θ : Monoid.End G) (g δ x : G) :
    x ∈ twCent θ (twConj θ g δ) ↔ g * x * g⁻¹ ∈ twCent θ δ := by
  rw [mem_twCent, mem_twCent]
  simp only [twConj, map_mul, map_inv]
  constructor
  · intro h
    calc (g * x * g⁻¹)⁻¹ * δ * (θ g * θ x * (θ g)⁻¹)
        = g * (x⁻¹ * (g⁻¹ * δ * θ g) * θ x) * (θ g)⁻¹ := by group
      _ = g * (g⁻¹ * δ * θ g) * (θ g)⁻¹ := by rw [h]
      _ = δ := by group
  · intro h
    calc x⁻¹ * (g⁻¹ * δ * θ g) * θ x
        = g⁻¹ * ((g * x * g⁻¹)⁻¹ * δ * (θ g * θ x * (θ g)⁻¹)) * θ g := by group
      _ = g⁻¹ * δ * θ g := by rw [h]

theorem h3 : PositivityTheory.Rg.Tf.Loc.H3 := fun _ _ θ g δ x => mem_twCent_twConj_iff θ g δ x

end GlobalTheory.CompanionTheory.TwistedCent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicSeriesUniformTubeStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_series_uniform_tube : ∀ (ι X T : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] [TopologicalSpace T]
    (t : ι → ℂ × ℂ → T → X) (Ω : Set (ℝ × ℝ)),
    (∀ r g (p v : ℂ × ℂ), Differentiable ℂ fun τ : ℂ => t r (p + τ • v) g) →
    (∀ r, Continuous fun y : (ℂ × ℂ) × T => t r y.1 y.2) →
    (∀ x ∈ Ω, ∀ g, ∃ V ∈ 𝓝 x, ∃ U ∈ 𝓝 g, ∃ u : ι → ℝ, Summable u ∧
      ∀ l ∈ PositivityTheory.RgEis.tube V, ∀ g' ∈ U, ∀ r, ‖t r l g'‖ ≤ u r) →
    PositivityTheory.RgEis.TubeGood (fun l g => ∑' r, t r l g) Ω ∧
      ∀ l ∈ PositivityTheory.RgEis.tube Ω, ∀ g, Summable fun r => ‖t r l g‖ := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCross.tubeGood_tsum | exact GlobalTheory.CompanionTheory.RgEisCross.tubeGood_tsum | (intros; apply GlobalTheory.CompanionTheory.RgEisCross.tubeGood_tsum <;> assumption)
end

