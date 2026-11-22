import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import GroundTheory.GlobalFields.TateThesis.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothOnGroupOfSpecial
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SmoothCentral

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiff_det_real : ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x.det) := by
  have h : (fun x : Matrix (Fin n) (Fin n) ℂ => x.det) =
      fun x => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, x (σ i) i := by
    funext x
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [h]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  exact contDiff_apply_apply (𝕜 := ℝ) (E := ℂ) (σ i) i

theorem norm_det_of_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : ‖g.det‖ = 1 := by
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ : (Jm ε).det * (Jm ε).det = 1 := by rw [← Matrix.det_mul, Jm_mul_self, Matrix.det_one]
  have hJ0 : (Jm ε).det ≠ 0 := left_ne_zero_of_mul_eq_one hJ
  have h2 : star g.det * g.det = 1 := by
    have : (star g.det * g.det) * (Jm ε).det = 1 * (Jm ε).det := by linear_combination h
    exact mul_right_cancel₀ hJ0 this
  have h3 : ((Complex.normSq g.det : ℝ) : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact h2
  have h4 : Complex.normSq g.det = 1 := by exact_mod_cast h3
  have h5 : ‖g.det‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h4
  have := norm_nonneg g.det
  nlinarith

theorem inUJ_smul {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) {c : ℂ} (hc : ‖c‖ = 1) :
    inUJ ε (c • g) := by
  unfold inUJ at *
  have hc2 : star c * c = 1 := by
    have : ((Complex.normSq c : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hc]; norm_num
    rw [Complex.normSq_eq_conj_mul_self] at this; exact this
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hg, mul_comm, hc2, one_smul]

theorem norm_eq_one_of_pow {w : ℂ} {k : ℕ} (hk : k ≠ 0) (h : ‖w‖ ^ k = 1) : ‖w‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg w) hk).1 h

theorem smooth_of_central : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ),
    (∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, f (z • g) = z ^ m * f' g) → SmoothS ε f' → SmoothOnG ε f := by
  intro n hn ε m f f' hf hS g₀ hg₀
  have hn0 : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  set d₀ := g₀.det with hd₀def
  have hd₀ : ‖d₀‖ = 1 := norm_det_of_inUJ hg₀
  have hd₀ne : d₀ ≠ 0 := by intro h; rw [h, norm_zero] at hd₀; exact zero_ne_one hd₀
  set z₀ := Complex.exp (Complex.log d₀ / n) with hz₀def
  have hz₀n : z₀ ^ n = d₀ := by
    rw [hz₀def, ← Complex.exp_nat_mul]
    have : (n : ℂ) * (Complex.log d₀ / n) = Complex.log d₀ := by field_simp
    rw [this, Complex.exp_log hd₀ne]
  have hz₀ne : z₀ ≠ 0 := Complex.exp_ne_zero _
  have hz₀norm : ‖z₀‖ = 1 := norm_eq_one_of_pow hn0 (by rw [← norm_pow, hz₀n, hd₀])
  set L : Matrix (Fin n) (Fin n) ℂ → ℂ := fun x => Complex.log (x.det / d₀) with hLdef
  set ζ : Matrix (Fin n) (Fin n) ℂ → ℂ := fun x => z₀ * Complex.exp (L x / n) with hζdef
  set ζi : Matrix (Fin n) (Fin n) ℂ → ℂ := fun x => z₀⁻¹ * Complex.exp (-(L x / n)) with hζidef
  set U : Set (Matrix (Fin n) (Fin n) ℂ) := {x | x.det / d₀ ∈ Complex.slitPlane} with hUdef
  have hUo : IsOpen U := Complex.isOpen_slitPlane.preimage ((contDiff_det_real.continuous).div_const _)
  have hg₀U : g₀ ∈ U := by
    show g₀.det / d₀ ∈ Complex.slitPlane
    rw [← hd₀def, div_self hd₀ne]; exact Complex.one_mem_slitPlane
  have hL : ContDiffOn ℝ ∞ L U := by
    intro x hx
    have h1 : ContDiffAt ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x.det / d₀) x :=
      (contDiff_det_real.div_const d₀).contDiffAt
    have h2 : ContDiffAt ℝ ∞ Complex.log (x.det / d₀) := (Complex.contDiffAt_log hx).restrict_scalars ℝ
    exact (h2.comp x h1).contDiffWithinAt
  have hζi : ContDiffOn ℝ ∞ ζi U := contDiffOn_const.mul ((hL.div_const _).neg.cexp)
  have hζ : ContDiffOn ℝ ∞ ζ U := contDiffOn_const.mul ((hL.div_const _).cexp)
  have hh : ContDiffOn ℝ ∞ (fun x => ζi x • x) U := hζi.smul contDiffOn_id
  have hζζi : ∀ x, ζ x * ζi x = 1 := by
    intro x
    simp only [hζdef, hζidef]
    rw [mul_mul_mul_comm, mul_inv_cancel₀ hz₀ne, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  have hζne : ∀ x, ζ x ≠ 0 := fun x => left_ne_zero_of_mul_eq_one (hζζi x)
  have hζn : ∀ x ∈ U, ζ x ^ n = x.det := by
    intro x hx
    have hx0 : x.det / d₀ ≠ 0 := Complex.slitPlane_ne_zero hx
    simp only [hζdef]
    rw [mul_pow, hz₀n, ← Complex.exp_nat_mul]
    have : (n : ℂ) * (L x / n) = L x := by field_simp
    rw [this]
    simp only [hLdef]
    rw [Complex.exp_log hx0]
    field_simp
  have hζig₀ : ζi g₀ = z₀⁻¹ := by
    simp only [hζidef, hLdef]
    rw [← hd₀def, div_self hd₀ne, Complex.log_one, zero_div, neg_zero, Complex.exp_zero, mul_one]
  have hinvnorm : ‖z₀⁻¹‖ = 1 := by rw [norm_inv, hz₀norm, inv_one]
  have hg₁ : z₀⁻¹ • g₀ ∈ SUset ε := by
    refine ⟨inUJ_smul hg₀ hinvnorm, ?_⟩
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hz₀n, ← hd₀def, inv_mul_cancel₀ hd₀ne]
  obtain ⟨U', F', hU'o, hg₁U', hF', hF'eq⟩ := hS _ hg₁
  have hzpow : ContDiffOn ℝ ∞ (fun x => ζ x ^ m) U := by
    intro x hx
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · simpa only [zpow_natCast] using (hζ x hx).pow k
    · refine (((hζ x hx).pow k).inv (pow_ne_zero k (hζne x))).congr (fun y _ => ?_) ?_ <;>
        simp [_root_.zpow_neg]
  refine ⟨U ∩ (fun x => ζi x • x) ⁻¹' U', fun x => ζ x ^ m * F' (ζi x • x),
    hh.continuousOn.isOpen_inter_preimage hUo hU'o, ⟨hg₀U, ?_⟩, ?_, ?_⟩
  · show ζi g₀ • g₀ ∈ U'
    rw [hζig₀]; exact hg₁U'
  · exact (hzpow.mono Set.inter_subset_left).mul
      (hF'.comp (hh.mono Set.inter_subset_left) fun x hx => hx.2)
  · intro x hx hxU
    have hxdet : ‖x.det‖ = 1 := norm_det_of_inUJ hxU
    have hnorm : ‖ζ x‖ = 1 := norm_eq_one_of_pow hn0 (by rw [← norm_pow, hζn x hx.1, hxdet])
    have hζi_eq : ζi x = (ζ x)⁻¹ := eq_inv_of_mul_eq_one_right (hζζi x)
    have hinorm : ‖ζi x‖ = 1 := by rw [hζi_eq, norm_inv, hnorm, inv_one]
    have hdet0 : x.det ≠ 0 := by intro h; rw [h, norm_zero] at hxdet; exact zero_ne_one hxdet
    have hmem : ζi x • x ∈ SUset ε := by
      refine ⟨inUJ_smul hxU hinorm, ?_⟩
      rw [Matrix.det_smul, Fintype.card_fin, hζi_eq, inv_pow, hζn x hx.1, inv_mul_cancel₀ hdet0]
    calc f x = f (ζ x • (ζi x • x)) := by rw [smul_smul, hζζi, one_smul]
      _ = ζ x ^ m * f' (ζi x • x) := hf _ hnorm _ hmem
      _ = ζ x ^ m * F' (ζi x • x) := by rw [hF'eq _ hx.2 hmem]

end GlobalTheory.SmoothCentral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmulOneMem
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CentralChar

variable {n : ℕ}

theorem smul_one_mem (ε : Fin n → Bool) {z : ℂ} (hz : ‖z‖ = 1) :
    (z • (1 : Matrix (Fin n) (Fin n) ℂ)) ∈ UJset ε := by
  show Formalism.REAL.inUJ ε _
  unfold Formalism.REAL.inUJ
  rw [conjTranspose_smul, conjTranspose_one, smul_mul_assoc, Matrix.one_mul, mul_smul_comm,
    Matrix.mul_one, smul_smul]
  have : z * star z = 1 := by
    rw [RCLike.star_def, RCLike.mul_conj, hz]; simp
  rw [this, one_smul]

theorem inv_facts (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    (Jm ε * gᴴ * Jm ε) * g = 1 ∧ g * (Jm ε * gᴴ * Jm ε) = 1 ∧ (Jm ε * gᴴ * Jm ε) ∈ UJset ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hl : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', Jm_mul_self]
  have hr : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.mp hl
  refine ⟨hl, hr, ?_⟩
  show (Jm ε * gᴴ * Jm ε)ᴴ * Jm ε * (Jm ε * gᴴ * Jm ε) = Jm ε
  rw [conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose, conjTranspose_conjTranspose]
  calc Jm ε * (g * Jm ε) * Jm ε * (Jm ε * gᴴ * Jm ε)
      = Jm ε * (g * (Jm ε * Jm ε) * (Jm ε * gᴴ * Jm ε)) := by simp only [Matrix.mul_assoc]
    _ = Jm ε * (g * (Jm ε * gᴴ * Jm ε)) := by rw [Jm_mul_self, Matrix.mul_one]
    _ = Jm ε := by rw [hr, Matrix.mul_one]

theorem central_char : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), CompleteSpace H →
    Nontrivial H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∃ m : ℤ, Ext ε m σ σ := by
  intro n _ ε H _ _ σ hc hnt hrep hirr
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hrep
  have hstar : ∀ g ∈ UJset ε, star (σ g) = σ (Jm ε * gᴴ * Jm ε) := by
    intro g hg
    obtain ⟨-, hr, hm⟩ := inv_facts ε hg
    rw [ContinuousLinearMap.star_eq_adjoint]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    let L : H →ₗᵢ[ℂ] H := ⟨(σ g).toLinearMap, hiso g hg⟩
    have hx : σ g (σ (Jm ε * gᴴ * Jm ε) x) = x := by
      rw [← ContinuousLinearMap.comp_apply, ← hmul g hg _ hm, hr, h1]; rfl
    calc ⟪σ (Jm ε * gᴴ * Jm ε) x, y⟫_ℂ = ⟪L (σ (Jm ε * gᴴ * Jm ε) x), L y⟫_ℂ :=
          (L.inner_map_map _ _).symm
      _ = ⟪x, σ g y⟫_ℂ := by
          show ⟪σ g (σ (Jm ε * gᴴ * Jm ε) x), σ g y⟫_ℂ = _
          rw [hx]
  have hscal : ∀ z : ℂ, ‖z‖ = 1 → ∃ c : ℂ, σ (z • 1) = c • (1 : H →L[ℂ] H) := by
    intro z hz
    apply Formalism.MainNotions.BridgeCSchur.schur_bounded (σ '' UJset ε)
    · rintro _ ⟨g, hg, rfl⟩; exact ⟨_, (inv_facts ε hg).2.2, (hstar g hg).symm⟩
    · intro S hS hst; exact hirr S hS (fun g hg v hv => hst _ ⟨g, hg, rfl⟩ v hv)
    · rintro _ ⟨g, hg, rfl⟩
      have hz1 := smul_one_mem ε hz
      show σ (z • 1) * σ g = σ g * σ (z • 1)
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, ← hmul _ hz1 _ hg,
        ← hmul _ hg _ hz1, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one]
  obtain ⟨v0, hv0⟩ := exists_ne (0 : H)
  let χ : ℂ → ℂ := fun z => ⟪v0, σ (z • 1) v0⟫_ℂ / ⟪v0, v0⟫_ℂ
  have hvv : ⟪v0, v0⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv0
  have hχ : ∀ z : ℂ, ‖z‖ = 1 → σ (z • 1) = χ z • (1 : H →L[ℂ] H) := by
    intro z hz
    obtain ⟨c, hc'⟩ := hscal z hz
    have : χ z = c := by
      simp only [χ, hc', ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        inner_smul_right]
      field_simp
    rw [this, hc']
  have hχv : ∀ z : ℂ, ‖z‖ = 1 → σ (z • 1) v0 = χ z • v0 := by
    intro z hz; rw [hχ z hz]; rfl
  have hnorm : ∀ z : ℂ, ‖z‖ = 1 → ‖χ z‖ = 1 := by
    intro z hz
    have h := hiso _ (smul_one_mem ε hz) v0
    rw [hχv z hz, norm_smul] at h
    have hp : 0 < ‖v0‖ := norm_pos_iff.mpr hv0
    nlinarith [h]
  have hne : ∀ w : Circle, χ w ≠ 0 := by
    intro w h0
    have := hnorm w (Circle.norm_coe _)
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hcontχ : Continuous fun w : Circle => χ w := by
    have hc1 : Continuous fun w : Circle => σ ((w : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) v0 :=
      (hcont v0).comp_continuous (by fun_prop) (fun w => smul_one_mem ε (Circle.norm_coe _))
    exact (continuous_const.inner hc1).div_const _
  let χU : Circle →ₜ* ℂˣ :=
    { toFun := fun w => Units.mk0 (χ w) (hne w)
      map_one' := by
        apply Units.ext
        simp only [Units.val_mk0, Units.val_one, Circle.coe_one, χ, one_smul, h1,
          ContinuousLinearMap.one_apply]
        exact div_self hvv
      map_mul' := by
        intro a b
        apply Units.ext
        simp only [Units.val_mk0, Units.val_mul]
        have ha := smul_one_mem ε (z := (a : ℂ)) (Circle.norm_coe _)
        have hb := smul_one_mem ε (z := (b : ℂ)) (Circle.norm_coe _)
        have hab : σ (((a * b : Circle) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) v0
            = (χ a * χ b) • v0 := by
          rw [Circle.coe_mul, show ((a : ℂ) * b) • (1 : Matrix (Fin n) (Fin n) ℂ) =
            ((a : ℂ) • 1) * ((b : ℂ) • 1) by rw [smul_mul_smul_comm, Matrix.one_mul], hmul _ ha _ hb,
            ContinuousLinearMap.comp_apply, hχv _ (Circle.norm_coe b), map_smul, hχv _ (Circle.norm_coe a),
            smul_smul, mul_comm]
        rw [hχv _ (Circle.norm_coe (a * b))] at hab
        exact smul_left_injective ℂ hv0 hab
      continuous_toFun := by
        rw [Units.continuous_iff]
        refine ⟨hcontχ, ?_⟩
        simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
        exact hcontχ.inv₀ hne }
  obtain ⟨m, hm, -⟩ := GroundTheory.Global.existsUnique_circle_zpow χU
  refine ⟨m, fun z hz g hg => ?_⟩
  have hz1 := smul_one_mem ε hz
  have hw : ((Circle.exp (Complex.arg z) : Circle) : ℂ) = z := by
    rw [Circle.coe_exp]
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz] at this; simpa using this
  have hχz : χ z = z ^ m := by
    have : χ ((Circle.exp (Complex.arg z) : Circle) : ℂ) = ((Circle.exp (Complex.arg z) : Circle) : ℂ) ^ m :=
      hm (Circle.exp (Complex.arg z))
    rwa [hw] at this
  rw [show z • g = (z • (1 : Matrix (Fin n) (Fin n) ℂ)) * g by rw [smul_mul_assoc, Matrix.one_mul],
    hmul _ hz1 _ hg.1, hχ z hz, hχz]
  ext v
  rfl

end GlobalTheory.CentralChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryToSpecialUnitaryLocal
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SUSplit

variable {n : ℕ}

lemma det_Jm_ne_zero (ε : Fin n → Bool) : (Jm ε).det ≠ 0 := by
  have h := congrArg Matrix.det (Jm_mul_self ε)
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

lemma norm_eq_one_of_pow {c : ℂ} (hn : n ≠ 0) (h : ‖c ^ n‖ = 1) : ‖c‖ = 1 := by
  rw [norm_pow] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) hn).1 h

lemma star_mul_self_of_norm {c : ℂ} (hc : ‖c‖ = 1) : star c * c = 1 := by
  have h := Complex.normSq_eq_conj_mul_self (z := c)
  rw [Complex.normSq_eq_norm_sq, hc] at h
  simpa using h.symm

lemma norm_det_of_mem {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ‖g.det‖ = 1 := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h2
  have h3 : star g.det * g.det = 1 := by
    have : (star g.det * g.det) * (Jm ε).det = 1 * (Jm ε).det := by rw [one_mul]; linear_combination h2
    exact mul_right_cancel₀ (det_Jm_ne_zero ε) this
  have h4 := Complex.normSq_eq_conj_mul_self (z := g.det)
  rw [Complex.normSq_eq_norm_sq] at h4
  have h5 : ‖g.det‖ ^ 2 = 1 := by
    have : ((‖g.det‖ ^ 2 : ℝ) : ℂ) = 1 := by rw [h4]; simpa using h3
    exact_mod_cast this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h5

lemma smul_mem_UJset_iff {ε : Fin n → Bool} {x : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (hc : ‖c‖ = 1) :
    c • x ∈ UJset ε ↔ x ∈ UJset ε := by
  have hcc := star_mul_self_of_norm hc
  show inUJ ε (c • x) ↔ inUJ ε x
  unfold inUJ
  have : (c • x)ᴴ * Jm ε * (c • x) = (star c * c) • (xᴴ * Jm ε * x) := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [this, hcc, one_smul]

lemma smul_mem_Kset_iff {ε : Fin n → Bool} {x : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (hc : ‖c‖ = 1) :
    c • x ∈ Kset ε ↔ x ∈ Kset ε := by
  have hcc := star_mul_self_of_norm hc
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  show (c • x ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ c • x * Jm ε = Jm ε * (c • x)) ↔
    (x ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ x * Jm ε = Jm ε * x)
  rw [Matrix.mem_unitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  have e1 : c • x * star (c • x) = (c * star c) • (x * star x) := by
    rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have e2 : c • x * Jm ε = c • (x * Jm ε) := Matrix.smul_mul _ _ _
  have e3 : Jm ε * (c • x) = c • (Jm ε * x) := Matrix.mul_smul _ _ _
  rw [e1, e2, e3, mul_comm, hcc, one_smul, smul_right_inj hc0]

lemma inv_smul_mem_SUset {ε : Fin n → Bool} {x : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (hx : x ∈ UJset ε)
    (hc : ‖c‖ = 1) (hpow : c ^ n = x.det) : c⁻¹ • x ∈ SUset ε := by
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  refine ⟨(smul_mem_UJset_iff (by rw [norm_inv, hc, inv_one])).2 hx, ?_⟩
  rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hpow]
  exact inv_mul_cancel₀ (by rw [← hpow]; exact pow_ne_zero _ hc0)

theorem unit_scalar_split : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool), (∀ g ∈ UJset ε, ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ g₀ ∈ SUset ε, g = z • g₀ ∧ (g ∈ Kset ε ↔ g₀ ∈ KS ε)) ∧ (∀ z : ℂ, ‖z‖ = 1 → ∀ g₀ ∈ SUset ε, z • g₀ ∈ UJset ε ∧ (g₀ ∈ KS ε → z • g₀ ∈ Kset ε)) ∧ ∀ g ∈ UJset ε, ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (ζ : Matrix (Fin n) (Fin n) ℂ → ℂ), IsOpen U ∧ g ∈ U ∧ ContinuousOn ζ U ∧ ∀ x ∈ U, x ∈ UJset ε → ‖ζ x‖ = 1 ∧ (ζ x)⁻¹ • x ∈ SUset ε := by
  intro n hn ε
  have hn0 : n ≠ 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq g.det (by omega : 0 < n)
    have hzn : ‖z‖ = 1 := norm_eq_one_of_pow hn0 (by rw [hz]; exact norm_det_of_mem hg)
    have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hzn; exact zero_ne_one hzn
    have hmem := inv_smul_mem_SUset hg hzn hz
    refine ⟨z, hzn, z⁻¹ • g, hmem, ?_, ?_⟩
    · rw [smul_smul, mul_inv_cancel₀ hz0, one_smul]
    · have hzi : ‖z⁻¹‖ = 1 := by rw [norm_inv, hzn, inv_one]
      show g ∈ Kset ε ↔ (z⁻¹ • g ∈ Kset ε ∧ (z⁻¹ • g).det = 1)
      rw [smul_mem_Kset_iff hzi]
      exact ⟨fun h => ⟨h, hmem.2⟩, fun h => h.1⟩
  · intro z hz g₀ hg₀
    exact ⟨(smul_mem_UJset_iff hz).2 hg₀.1, fun h => (smul_mem_Kset_iff hz).2 h.1⟩
  · intro g hg
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq g.det (by omega : 0 < n)
    have hdg : g.det ≠ 0 := by
      intro h; have := norm_det_of_mem hg; rw [h, norm_zero] at this; exact zero_ne_one this
    have hcont : Continuous fun x : Matrix (Fin n) (Fin n) ℂ => x.det / g.det :=
      (continuous_id.matrix_det).div_const _
    refine ⟨{x | 0 < (x.det / g.det).re},
      fun x => z * Complex.exp (Complex.log (x.det / g.det) / n), ?_, ?_, ?_, ?_⟩
    · exact isOpen_lt continuous_const (Complex.continuous_re.comp hcont)
    · show 0 < (g.det / g.det).re
      rw [div_self hdg]; simp
    · refine continuousOn_const.mul (Complex.continuous_exp.comp_continuousOn ?_)
      exact (ContinuousOn.clog hcont.continuousOn
        (fun x hx => Complex.mem_slitPlane_iff.2 (Or.inl hx))).div_const _
    · intro x hxU hx
      have hw0 : x.det / g.det ≠ 0 := by
        intro h; have hxU' : 0 < (x.det / g.det).re := hxU; rw [h] at hxU'; simp at hxU'
      have hpow : (z * Complex.exp (Complex.log (x.det / g.det) / n)) ^ n = x.det := by
        rw [mul_pow, ← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn0 : (n : ℂ) ≠ 0),
          Complex.exp_log hw0, hz, mul_div_cancel₀ _ hdg]
      have hnorm : ‖z * Complex.exp (Complex.log (x.det / g.det) / n)‖ = 1 :=
        norm_eq_one_of_pow hn0 (by rw [hpow]; exact norm_det_of_mem hx)
      exact ⟨hnorm, inv_smul_mem_SUset hx hnorm hpow⟩

end GlobalTheory.SUSplit

end
end

