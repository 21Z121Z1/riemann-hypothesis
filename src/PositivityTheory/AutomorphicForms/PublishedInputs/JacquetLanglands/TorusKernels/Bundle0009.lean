import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.EllipticTermsContributionProof
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.EllipticTermsContribution

open UpperTheory.Esk

theorem mk_out {F : Type} [Field F] (q : PG F) : ((q.out : GL (Fin 2) F) : PG F) = q := Quotient.out_eq' q

theorem elliptic_lower_left_ne_zero (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : h 1 0 ≠ 0 := by
  intro e
  rw [Matrix.trace_fin_two, det_eq, e] at hh
  nlinarith [sq_nonneg (h 0 0 - h 1 1)]

def disc (h : GL (Fin 2) ℝ) : ℝ := 4 * h.val.det - h.val.trace ^ 2

def fpC (h : GL (Fin 2) ℝ) : ℂ :=
  (((h 0 0 - h 1 1) / (2 * h 1 0) : ℝ) : ℂ) + Complex.I * ((Real.sqrt (disc h) / (2 * h 1 0) : ℝ) : ℂ)

theorem fpC_im (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : (fpC h).im ≠ 0 := by
  have hr := elliptic_lower_left_ne_zero h hh
  have hd : 0 < disc h := by unfold disc; linarith
  simp only [fpC, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, one_mul, zero_add]
  exact div_ne_zero (Real.sqrt_pos.2 hd).ne' (mul_ne_zero two_ne_zero hr)

def fp (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : P := ⟨fpC h, fpC_im h hh⟩

theorem fp_eq (h : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) :
    ((h 1 0 : ℝ) : ℂ) * fpC h ^ 2 + (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * fpC h - ((h 0 1 : ℝ) : ℂ) = 0 := by
  have hr := elliptic_lower_left_ne_zero h hh
  have hd : 0 < disc h := by unfold disc; linarith
  have hr' : ((h 1 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have hs : ((Real.sqrt (disc h) : ℝ) : ℂ) ^ 2 = ((disc h : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hd.le]
  have hD : ((disc h : ℝ) : ℂ) = 4 * (((h 0 0 : ℝ) : ℂ) * ((h 1 1 : ℝ) : ℂ) - ((h 0 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ))
      - (((h 0 0 : ℝ) : ℂ) + ((h 1 1 : ℝ) : ℂ)) ^ 2 := by
    simp only [disc, Matrix.trace_fin_two, det_eq]; push_cast; ring
  have hz : 2 * ((h 1 0 : ℝ) : ℂ) * fpC h = (((h 0 0 : ℝ) : ℂ) - ((h 1 1 : ℝ) : ℂ)) + Complex.I * ((Real.sqrt (disc h) : ℝ) : ℂ) := by
    simp only [fpC]; push_cast; field_simp
  have h4 : (4 * ((h 1 0 : ℝ) : ℂ)) * (((h 1 0 : ℝ) : ℂ) * fpC h ^ 2 + (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * fpC h - ((h 0 1 : ℝ) : ℂ)) = 0 := by
    rw [show (4 * ((h 1 0 : ℝ) : ℂ)) * (((h 1 0 : ℝ) : ℂ) * fpC h ^ 2 + (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * fpC h - ((h 0 1 : ℝ) : ℂ))
      = (2 * ((h 1 0 : ℝ) : ℂ) * fpC h) ^ 2 + 2 * (((h 1 1 : ℝ) : ℂ) - ((h 0 0 : ℝ) : ℂ)) * (2 * ((h 1 0 : ℝ) : ℂ) * fpC h)
        - 4 * ((h 1 0 : ℝ) : ℂ) * ((h 0 1 : ℝ) : ℂ) by ring, hz]
    linear_combination ((Real.sqrt (disc h) : ℝ) : ℂ) ^ 2 * Complex.I_sq - hs - hD
  rcases mul_eq_zero.1 h4 with h5 | h5
  · exact absurd h5 (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hr')
  · exact h5

theorem fix_comm (h g : GL (Fin 2) ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) (hc : g * h = h * g) :
    g • fp h hh = fp h hh := by
  have hr := elliptic_lower_left_ne_zero h hh
  have hr' : ((h 1 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have e00 := congrArg (fun M : GL (Fin 2) ℝ => M 0 0) hc
  have e10 := congrArg (fun M : GL (Fin 2) ℝ => M 1 0) hc
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
  have e00' : ((g 0 0 : ℝ) : ℂ) * ((h 0 0 : ℝ) : ℂ) + ((g 0 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ)
      = ((h 0 0 : ℝ) : ℂ) * ((g 0 0 : ℝ) : ℂ) + ((h 0 1 : ℝ) : ℂ) * ((g 1 0 : ℝ) : ℂ) := by exact_mod_cast e00
  have e10' : ((g 1 0 : ℝ) : ℂ) * ((h 0 0 : ℝ) : ℂ) + ((g 1 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ)
      = ((h 1 0 : ℝ) : ℂ) * ((g 0 0 : ℝ) : ℂ) + ((h 1 1 : ℝ) : ℂ) * ((g 1 0 : ℝ) : ℂ) := by exact_mod_cast e10
  have hQ := fp_eq h hh
  apply Subtype.ext
  rw [coe_smul, div_eq_iff (den_ne g (fp h hh).2)]
  apply mul_left_cancel₀ hr'
  change ((h 1 0 : ℝ) : ℂ) * (((g 0 0 : ℝ) : ℂ) * fpC h + ((g 0 1 : ℝ) : ℂ))
    = ((h 1 0 : ℝ) : ℂ) * (fpC h * (((g 1 0 : ℝ) : ℂ) * fpC h + ((g 1 1 : ℝ) : ℂ)))
  linear_combination e00' - fpC h * e10' - ((g 1 0 : ℝ) : ℂ) * hQ

theorem tr_r {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (v : I) (g : GL (Fin 2) F) :
    (D.r v g).val.trace = D.σ v g.val.trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add]; rfl

theorem det_r {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (v : I) (g : GL (Fin 2) F) :
    (D.r v g).val.det = D.σ v g.val.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_mul]; rfl

end UpperTheory.Esk.EllipticTermsContribution

open UpperTheory.Esk.EllipticTermsContribution in
theorem UpperTheory.Esk.elliptic_terms_contribution_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.B4 → UpperTheory.Esk.C1 → UpperTheory.Esk.E0a → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.Mult → UpperTheory.Esk.Fcen → UpperTheory.Esk.F3 := by
  intro hB1a _ hB1c hB4 hC1 hE0a hE0c _ hMult hFcen F I Gf ι _ _ _ _ D k a hyp γ ω hT hTe
  have : SigmaFinite (volume : Measure P) := hB1a.1
  obtain ⟨_, c2, c3, _, c5, c6⟩ := hE0c F I Gf ι D k a hyp
  have htr : γ.out.val.trace ≠ 0 := by
    obtain ⟨i, hi⟩ := c5 γ ω hTe
    exact (c6 γ ω i hi).1
  have hTv : ∀ v, (D.r v γ.out).val.trace ^ 2 < 4 * (D.r v γ.out).val.det := fun v => by
    rw [tr_r, det_r]; exact hT v
  let z0 : D.Xs := fun v => fp (D.r v γ.out) (hTv v)
  set S := MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om) with hS
  have memS : ∀ g : PG F, g ∈ S → g * γ * g⁻¹ = γ ∧ g • ω = ω := by
    intro g hg
    rw [hS, MulAction.mem_stabilizer_iff] at hg
    exact ⟨congrArg Prod.fst hg, congrArg Prod.snd hg⟩
  have fixS : ∀ g : PG F, g ∈ S → g • z0 = z0 := by
    intro g hg
    obtain ⟨h1, -⟩ := memS g hg
    have hc : g.out * γ.out = γ.out * g.out := by
      apply hFcen F γ.out g.out htr
      rw [mk_out, mk_out]; exact h1
    rw [← mk_out g, Dat.mk_smulX]
    funext v
    exact fix_comm _ _ (hTv v) (by rw [← map_mul, ← map_mul, hc])
  obtain ⟨c₀, hc₀, hmink⟩ := hyp.ax.mink
  obtain ⟨s, hs, hsc⟩ := hmink z0 (D.rep ω)
  obtain ⟨C, hC⟩ := hMult F I Gf D hyp.ax 1 c₀ one_pos hc₀
  have hfin := (hC (ω, z0) s hs hsc).1
  have hSfin : (S : Set (PG F)).Finite := hfin.subset fun g hg => ⟨(memS g hg).2, fun v => by
      show 1 ≤ kap (z0 v) ((g • z0 : D.Xs) v)
      rw [fixS g hg, hB1c.2.1]⟩
  have hSF : Finite S := hSfin.to_subtype
  refine ⟨hSF, fun β hβ => ?_⟩
  let f : I → P → ℂ := fun v w => q1 (k v) w (D.r v γ.out • w) * j1 (k v) (D.r v γ.out) w
  have hu : ∀ z : D.Xs, D.kk k a γ (ω, z) = D.Te a γ.out (D.rep ω) * ∏ v, f v (z v) := by
    intro z
    show D.Te a γ.out (D.rep ω) * (qq k z (D.act γ.out z) * D.J k γ.out z) =
      D.Te a γ.out (D.rep ω) * ∏ v, (q1 (k v) (z v) (D.r v γ.out • z v) * j1 (k v) (D.r v γ.out) (z v))
    rw [Finset.prod_mul_distrib]; rfl
  have hint : Integrable (fun z : D.Xs => ∏ v, f v (z v)) :=
    Integrable.fintype_prod (f := f) (μ := fun _ => volume) fun v => (hB4 (k v) (hyp.four v) _ (hTv v)).1
  have hval : ∫ z : D.Xs, ∏ v, f v (z v) = D.orb k γ.out := by
    rw [show (∫ z : D.Xs, ∏ v, f v (z v)) = ∫ z : I → P, ∏ v, f v (z v) ∂(Measure.pi fun _ => volume) from rfl,
      integral_fintype_prod_eq_prod]
    unfold Dat.orb
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [(hB4 (k v) (hyp.four v) _ (hTv v)).2, tr_r, det_r]
  haveI : Fintype S := Fintype.ofFinite S
  have hcard : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos_iff.2 ⟨1⟩
  let c : ℝ := (Fintype.card S : ℝ)⁻¹
  have hcut : IsCut S (fun _ : D.Xs => c) := ⟨measurable_const, fun _ => inv_nonneg.2 hcard.le, fun _ => by
      have e : ∑ _ : S, c = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne']
      rw [← e]; exact hasSum_fintype _⟩
  have hP : Pres S (volume : Measure D.Xs) := fun g => (hE0a F I Gf D hyp.ax).2.2.1 (g : PG F)
  have hinv : ∀ (g : S) (z : D.Xs), D.kk k a γ (ω, g • z) = D.kk k a γ (ω, z) := by
    intro g z
    obtain ⟨h1, h2⟩ := memS g g.2
    have := c2 g γ (ω, z)
    have e : (g : PG F) • ((ω, z) : D.Y) = (ω, g • z) := Prod.ext h2 rfl
    rw [h1, e] at this
    exact this
  have hmeas : Measurable (fun z : D.Xs => D.kk k a γ (ω, z)) := (c3 γ).comp measurable_prodMk_left
  have hintc : Integrable (fun z : D.Xs => c • D.kk k a γ (ω, z)) := by
    rw [show (fun z : D.Xs => c • D.kk k a γ (ω, z)) = fun z => c • (D.Te a γ.out (D.rep ω) * ∏ v, f v (z v)) from
      funext fun z => by rw [hu]]
    exact (hint.const_mul _).smul c
  obtain ⟨-, heq⟩ := (hC1 (↥S) D.Xs volume hP (fun _ => c) β hcut hβ).2 _ hmeas hinv hintc
  rw [← heq]
  simp_rw [hu]
  rw [integral_smul, integral_const_mul, hval, Nat.card_eq_fintype_card, Complex.real_smul]
  simp only [c, Complex.ofReal_inv, Complex.ofReal_natCast]
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HolomorphicOnHalfPlaneFinsetSum
section
open MeasureTheory Matrix

namespace UpperTheory.Esk.FormsStableLemmas

open UpperTheory.Esk

theorem extendHalfPlane_finset_sum {ι : Type} (s : Finset ι) (g : ι → P → ℂ) :
    ext1 (fun t => ∑ i ∈ s, g i t) = fun t => ∑ i ∈ s, ext1 (g i) t := by
  funext t
  unfold ext1
  split_ifs <;> simp

theorem holomorphic_on_half_plane_finset_sum {ι : Type} (s : Finset ι) (g : ι → P → ℂ) (h : ∀ i ∈ s, Hol1 (g i)) :
    Hol1 (fun t => ∑ i ∈ s, g i t) := by
  unfold Hol1
  rw [extendHalfPlane_finset_sum]
  exact (DifferentiableOn.sum h).congr fun t _ => by simp [Finset.sum_apply]

theorem holomorphic_on_half_plane_add (f g : P → ℂ) (hf : Hol1 f) (hg : Hol1 g) : Hol1 (fun t => f t + g t) := by
  have : ext1 (fun t => f t + g t) = fun t => ext1 f t + ext1 g t := by
    funext t; unfold ext1; split_ifs <;> simp
  unfold Hol1 at *
  rw [this]
  exact hf.add hg

theorem holomorphic_on_half_plane_const_mul (c : ℂ) (f : P → ℂ) (hf : Hol1 f) : Hol1 (fun t => c * f t) := by
  have : ext1 (fun t => c * f t) = fun t => c * ext1 f t := by
    funext t; unfold ext1; split_ifs <;> simp
  unfold Hol1 at *
  rw [this]
  exact hf.const_mul c

theorem holomorphic_on_half_plane_zero : Hol1 (fun _ : P => (0 : ℂ)) := by
  have : ext1 (fun _ : P => (0 : ℂ)) = fun _ => 0 := by
    funext t; unfold ext1; split_ifs <;> simp
  unfold Hol1
  rw [this]
  exact differentiableOn_const 0

theorem nrm_nonneg {I : Type} [Fintype I] (k : I → ℕ) (z : X I) : 0 ≤ nrm k z := by
  unfold nrm
  exact Finset.prod_nonneg fun v _ => Real.rpow_nonneg (abs_nonneg _) _

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

omit [Fintype I] in
theorem op_apply {ι : Type} [Fintype ι] (a : ι → Gf) (f : X I × Gf → ℂ) (p : X I × Gf) :
    Dat.Op a f p = ∑ i, f (p.1, p.2 * a i) := rfl

theorem isForm_zero (k : I → ℕ) : D.IsForm k 0 where
  hol x := ⟨continuous_const, fun _ _ => holomorphic_on_half_plane_zero⟩
  aut γ z x := by simp
  lev z x h := by simp
  bdd := ⟨0, fun z x => by simp⟩

theorem isForm_add (k : I → ℕ) (f g : X I × Gf → ℂ) (hf : D.IsForm k f) (hg : D.IsForm k g) :
    D.IsForm k (f + g) where
  hol x := ⟨(hf.hol x).1.add (hg.hol x).1, fun z v => holomorphic_on_half_plane_add _ _ ((hf.hol x).2 z v) ((hg.hol x).2 z v)⟩
  aut γ z x := by simp [Pi.add_apply, hf.aut, hg.aut, mul_add]
  lev z x h := by simp [Pi.add_apply, hf.lev, hg.lev, mul_add]
  bdd := by
    obtain ⟨C₁, h₁⟩ := hf.bdd
    obtain ⟨C₂, h₂⟩ := hg.bdd
    refine ⟨C₁ + C₂, fun z x => ?_⟩
    have hn := nrm_nonneg k z
    calc ‖(f + g) (z, x)‖ * nrm k z ≤ (‖f (z, x)‖ + ‖g (z, x)‖) * nrm k z :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) hn
      _ = ‖f (z, x)‖ * nrm k z + ‖g (z, x)‖ * nrm k z := add_mul _ _ _
      _ ≤ C₁ + C₂ := add_le_add (h₁ z x) (h₂ z x)

theorem isForm_smul (k : I → ℕ) (c : ℂ) (f : X I × Gf → ℂ) (hf : D.IsForm k f) :
    D.IsForm k (c • f) where
  hol x := ⟨continuous_const.mul (hf.hol x).1, fun z v => holomorphic_on_half_plane_const_mul c _ ((hf.hol x).2 z v)⟩
  aut γ z x := by simp [Pi.smul_apply, hf.aut]; ring
  lev z x h := by simp [Pi.smul_apply, hf.lev]; ring
  bdd := by
    obtain ⟨C, h⟩ := hf.bdd
    refine ⟨‖c‖ * C, fun z x => ?_⟩
    have := h z x
    have hc := norm_nonneg c
    calc ‖(c • f) (z, x)‖ * nrm k z = ‖c‖ * (‖f (z, x)‖ * nrm k z) := by
          rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      _ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left this hc

def S (k : I → ℕ) : Submodule ℂ (X I × Gf → ℂ) where
  carrier := {f | D.IsForm k f}
  add_mem' {f g} hf hg := isForm_add D k f g hf hg
  zero_mem' := isForm_zero D k
  smul_mem' c f hf := isForm_smul D k c f hf

theorem M_eq (k : I → ℕ) : D.M k = S D k := Submodule.span_eq (S D k)

theorem mem_M (k : I → ℕ) (f : X I × Gf → ℂ) : f ∈ D.M k ↔ D.IsForm k f := by
  rw [M_eq]; rfl

open Classical in
theorem isForm_op (k : I → ℕ) {ι : Type} [Fintype ι] (a : ι → Gf) (ha : D.Good a)
    (f : X I × Gf → ℂ) (hf : D.IsForm k f) : D.IsForm k (Dat.Op a f) where
  hol x := by
    refine ⟨?_, fun z v => ?_⟩
    · simp only [op_apply]
      exact continuous_finsetSum _ fun i _ => (hf.hol (x * a i)).1
    · simp only [op_apply]
      exact holomorphic_on_half_plane_finset_sum Finset.univ (fun i t => f (Function.update z v t, x * a i))
        (fun i _ => (hf.hol (x * a i)).2 z v)
  aut γ z x := by
    simp only [op_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, hf.aut]
  lev z x h := by
    simp only [op_apply]
    exact ha (fun y => f (z, y)) (fun y h' => hf.lev z y h') x h
  bdd := by
    obtain ⟨C, hC⟩ := hf.bdd
    refine ⟨Fintype.card ι * C, fun z x => ?_⟩
    have hn := nrm_nonneg k z
    simp only [op_apply]
    calc ‖∑ i, f (z, x * a i)‖ * nrm k z ≤ (∑ i, ‖f (z, x * a i)‖) * nrm k z :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) hn
      _ = ∑ i, ‖f (z, x * a i)‖ * nrm k z := Finset.sum_mul _ _ _
      _ ≤ ∑ _i : ι, C := Finset.sum_le_sum fun i _ => hC z (x * a i)
      _ = Fintype.card ι * C := by simp

theorem main (k : I → ℕ) : (∀ f, f ∈ D.M k ↔ D.IsForm k f) ∧
    ∀ (ι : Type) [Fintype ι] (a : ι → Gf), D.Good a → ∀ f ∈ D.M k, Dat.Op a f ∈ D.M k := by
  refine ⟨mem_M D k, fun ι _ a ha f hf => ?_⟩
  rw [mem_M] at hf ⊢
  exact isForm_op D k a ha f hf

end UpperTheory.Esk.FormsStableLemmas

theorem UpperTheory.Esk.forms_stable_under_operators_proof : UpperTheory.Esk.FormsStableUnderOperators :=
  fun _ _ _ _ _ _ D _ k => UpperTheory.Esk.FormsStableLemmas.main D k
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.KernelInverseSymmetry
section
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.KernelInverseSymmetry

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

def cK (k : I → ℕ) : ℝ := ∏ v, ((k v : ℝ) - 1) / (4 * Real.pi)

def T (k : I → ℕ) (p : X I × Gf) (γ : PG F) (y : D.Y) : ℂ :=
  D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2) * (qq k p.1 (D.act γ.out y.2) * D.J k γ.out y.2)

theorem cK_nonneg (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) : 0 ≤ cK k :=
  Finset.prod_nonneg fun v _ => div_nonneg (by
    have h : (4 : ℝ) ≤ k v := by exact_mod_cast hk v
    linarith) (by positivity)

theorem nrm_pos (k : I → ℕ) (z : X I) : 0 < nrm k z :=
  Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (abs_pos.2 (z v).2) _

theorem act_out (γ : PG F) (z : D.Xs) : D.act γ.out z = γ • z := by
  rw [← D.mk_smulX]
  congr 1
  exact Quotient.out_eq γ

theorem norm_qj (hB : B1b) (k : ℕ) (hk : 1 ≤ k) (g : GL (Fin 2) ℝ) (z w : P) :
    ‖q1 k z (g • w)‖ * ‖j1 k g w‖ * |z.1.im| ^ ((k : ℝ) / 2) =
      ((k : ℝ) - 1) / (4 * Real.pi) * kap z (g • w) ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2) := by
  obtain ⟨-, -, -, -, hj, hq, -⟩ := hB
  have e1 := hq k z (g • w) hk
  have e2 := hj k g w
  calc _ = (‖q1 k z (g • w)‖ * |z.1.im| ^ ((k : ℝ) / 2)) * ‖j1 k g w‖ := by ring
    _ = _ := by rw [e1, ← e2]; ring

theorem norm_term (hB : B1b) (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (g : GL (Fin 2) F) (z w : X I) :
    ‖qq k z (D.act g w) * D.J k g w‖ * nrm k z = cK k * Kap k z (D.act g w) * nrm k w := by
  simp only [qq, Dat.J, Kap, nrm, cK, norm_mul, norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  exact norm_qj hB (k v) (hk v) (D.r v g) (z v) (w v)

theorem Kap_smul (hB : B1b) (k : I → ℕ) (δ : PG F) (z w : D.Xs) :
    Kap k (δ • z : D.Xs) (δ • w : D.Xs) = Kap k z w := by
  obtain ⟨-, -, -, hkap, -⟩ := hB
  rw [← act_out, ← act_out]
  unfold Kap
  refine Finset.prod_congr rfl fun v _ => ?_
  show kap (D.r v δ.out • z v) (D.r v δ.out • w v) ^ _ = _
  rw [hkap]

theorem Kap_symm (hBc : B1c) (k : I → ℕ) (z w : X I) : Kap k z w = Kap k w z := by
  obtain ⟨hsym, -⟩ := hBc
  unfold Kap
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [(hsym _ _).2.2]

theorem Kap_swap (hB : B1b) (hBc : B1c) (k : I → ℕ) (γ : PG F) (z w : D.Xs) :
    Kap k z (γ • w : D.Xs) = Kap k w (γ⁻¹ • z : D.Xs) := by
  rw [← Kap_smul D hB k γ⁻¹ z (γ • w), inv_smul_smul]
  exact Kap_symm hBc k _ _

theorem ee_mem (x : Gf) (h : D.ee x ≠ 0) : x ∈ D.H := by
  unfold Dat.ee at h
  split_ifs at h with hx
  · exact hx
  · exact absurd rfl h

theorem norm_ee (hAx : D.Ax) (x : Gf) : ‖D.ee x‖ ≤ 1 := by
  unfold Dat.ee
  split_ifs with hx
  · rw [hAx.χn]
  · simp

theorem supp (γ : PG F) (ω : D.Om) (x : Gf) (h : D.ee ((D.rep ω)⁻¹ * (D.j γ.out)⁻¹ * x) ≠ 0) :
    γ • ω = (show D.Om from (x : Gf ⧸ D.H)) := by
  have hm := ee_mem D _ h
  rw [mul_assoc] at hm
  have e : ((D.rep ω : Gf) : Gf ⧸ D.H) = (((D.j γ.out)⁻¹ * x : Gf) : Gf ⧸ D.H) := QuotientGroup.eq.2 hm
  have hω : ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := Quotient.out_eq ω
  have hγ : ((γ.out : GL (Fin 2) F) : PG F) = γ := Quotient.out_eq γ
  have key : ((γ.out : GL (Fin 2) F) : PG F) • (show D.Om from (((D.j γ.out)⁻¹ * x : Gf) : Gf ⧸ D.H)) =
      (show D.Om from (x : Gf ⧸ D.H)) := by
    rw [D.mk_smulO, mul_inv_cancel_left]
  rw [← hω, e]
  rw [hγ] at key
  exact key

def xH (_D : Dat F I Gf) (p : X I × Gf) : _D.Om := (p.2 : Gf ⧸ _D.H)

def zX (_D : Dat F I Gf) (p : X I × Gf) : _D.Xs := p.1

def invEquiv (ω x : D.Om) : {γ : PG F // γ • ω = x} ≃ {δ : PG F // δ • x = ω} where
  toFun γ := ⟨γ.1⁻¹, by rw [inv_smul_eq_iff, γ.2]⟩
  invFun δ := ⟨δ.1⁻¹, by rw [inv_smul_eq_iff, δ.2]⟩
  left_inv γ := Subtype.ext (inv_inv _)
  right_inv δ := Subtype.ext (inv_inv _)

theorem T_le (hB : B1b) (hBc : B1c) (hAx : D.Ax) (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (p : X I × Gf) (γ : PG F) (y : D.Y) :
    ‖T D k p γ y‖ₑ ≤ {γ : PG F | γ • y.1 = (xH D p)}.indicator
      (fun γ => ENNReal.ofReal (cK k / nrm k p.1 * nrm k y.2) *
        ENNReal.ofReal (Kap k y.2 (γ⁻¹ • (zX D p) : D.Xs))) γ := by
  by_cases hγ : γ • y.1 = (xH D p)
  · rw [Set.indicator_of_mem (show γ ∈ {γ : PG F | γ • y.1 = (xH D p)} from hγ)]
    rw [← ENNReal.ofReal_mul (mul_nonneg (div_nonneg (cK_nonneg k hk) (nrm_pos k p.1).le) (nrm_pos k y.2).le),
      ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    have hn := norm_term D hB k (fun v => le_trans (by norm_num) (hk v)) γ.out p.1 y.2
    have hK : Kap k p.1 (D.act γ.out y.2) = Kap k y.2 (γ⁻¹ • (zX D p) : D.Xs) := by
      rw [act_out]
      exact Kap_swap D hB hBc k γ p.1 y.2
    rw [hK] at hn
    have hN := eq_div_of_mul_eq (nrm_pos k p.1).ne' hn
    have he := norm_ee D hAx ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2)
    unfold T
    rw [norm_mul]
    calc _ ≤ 1 * ‖qq k p.1 (D.act γ.out y.2) * D.J k γ.out y.2‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ = _ := by rw [hN]; ring
  · rw [Set.indicator_of_notMem (show γ ∉ {γ : PG F | γ • y.1 = (xH D p)} from hγ)]
    have h0 : D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2) = 0 := by
      by_contra hne
      exact hγ (supp D γ y.1 p.2 hne)
    simp [T, h0]

theorem tsum_le (hB : B1b) (hBc : B1c) (hAx : D.Ax) (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (p : X I × Gf) (Bnd : ℝ)
    (hS : ∀ (ω : D.Om) (w : X I), ∑' δ : {δ : PG F // δ • (xH D p) = ω},
      ENNReal.ofReal (Kap k w (δ.1 • (zX D p) : D.Xs)) ≤ ENNReal.ofReal Bnd) (y : D.Y) :
    ∑' γ, ‖T D k p γ y‖ₑ ≤ ENNReal.ofReal (cK k / nrm k p.1 * nrm k y.2) * ENNReal.ofReal Bnd := by
  have h1 := ENNReal.tsum_le_tsum fun γ => T_le D hB hBc hAx k hk p γ y
  rw [← tsum_subtype] at h1
  beta_reduce at h1
  rw [ENNReal.tsum_mul_left] at h1
  refine h1.trans (mul_le_mul' le_rfl (Eq.trans_le ?_ (hS y.1 y.2)))
  exact Equiv.tsum_eq (invEquiv D y.1 (xH D p))
    (fun δ => ENNReal.ofReal (Kap k y.2 (δ.1 • (zX D p) : D.Xs)))

theorem main (hB1a : B1a) (hB : B1b) (hBc : B1c) (hE0a : E0a) (hKS : KapSum) (hAx : D.Ax)
    (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (p : X I × Gf) :
    (∀ y : D.Y, Summable fun γ : PG F => ‖D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2) *
      (qq k p.1 (D.act γ.out y.2) * D.J k γ.out y.2)‖) ∧
    Measurable (fun y => D.Kern k y p) ∧ ∃ C, ∀ y, ‖D.Kern k y p‖ ≤ C * nrm k y.2 := by
  obtain ⟨hcount, -, -, -, -, -, hborel, -⟩ := hE0a F I Gf D hAx
  obtain ⟨c₀, hc₀, hmink⟩ := hAx.mink
  obtain ⟨C, hCb⟩ := hKS F I Gf D hAx k hk c₀ hc₀
  obtain ⟨s, hs, hsle⟩ := hmink p.1 (D.rep (xH D p))
  obtain ⟨Bnd, hBnd, hS⟩ : ∃ Bnd : ℝ, 0 ≤ Bnd ∧ ∀ (ω : D.Om) (w : X I),
      ∑' δ : {δ : PG F // δ • (xH D p) = ω},
        ENNReal.ofReal (Kap k w (δ.1 • (zX D p) : D.Xs)) ≤ ENNReal.ofReal Bnd :=
    ⟨max (C * (1 + D.HtY s ((xH D p), p.1))) 0, le_max_right _ _, fun ω w =>
      (hCb ((xH D p), p.1) s hs hsle ω w).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hT := fun y => tsum_le D hB hBc hAx k hk p Bnd hS y
  have hfin : ∀ y : D.Y, ∑' γ, ‖T D k p γ y‖ₑ ≠ ⊤ := fun y =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hT y)
  have hsumm : ∀ y : D.Y, Summable fun γ => ‖T D k p γ y‖ := fun y => by
    simpa only [toReal_enorm] using ENNReal.summable_toReal (hfin y)
  have hc0 : 0 ≤ cK k / nrm k p.1 := div_nonneg (cK_nonneg k hk) (nrm_pos k p.1).le
  have hbound : ∀ y : D.Y, ∑' γ, ‖T D k p γ y‖ ≤ cK k / nrm k p.1 * Bnd * nrm k y.2 := fun y => by
    have h1 : ∑' γ, ‖T D k p γ y‖ = (∑' γ, ‖T D k p γ y‖ₑ).toReal := by
      rw [ENNReal.tsum_toReal_eq (fun γ => enorm_ne_top)]
      simp only [toReal_enorm]
    rw [h1]
    refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg hc0 hBnd) (nrm_pos k y.2).le) ?_
    calc _ ≤ _ := hT y
      _ = ENNReal.ofReal (cK k / nrm k p.1 * Bnd * nrm k y.2) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hc0 (nrm_pos k y.2).le)]
        congr 1
        ring
  refine ⟨hsumm, ?_, ⟨cK k / nrm k p.1 * Bnd, fun y => (norm_tsum_le_tsum_norm (hsumm y)).trans (hbound y)⟩⟩
  haveI := hcount
  haveI := hborel
  obtain ⟨-, -, -, -, -, -, hjc, hqc, -⟩ := hB
  have hgc : ∀ g : GL (Fin 2) ℝ, Continuous fun z : P => g • z := fun g => (hB1a.2.2 g).1
  have hTm : ∀ γ : PG F, Measurable (T D k p γ) := fun γ => by
    have hG : Continuous fun w : D.Xs => qq k p.1 (D.act γ.out w) * D.J k γ.out w := by
      refine Continuous.mul ?_ ?_
      · refine continuous_finsetProd _ fun v _ => ?_
        exact (hqc (k v)).comp (continuous_const.prodMk ((hgc (D.r v γ.out)).comp (continuous_apply v)))
      · exact continuous_finsetProd _ fun v _ => (hjc (k v) (D.r v γ.out)).comp (continuous_apply v)
    exact ((Measurable.of_discrete (f := fun ω : D.Om => D.ee ((D.rep ω)⁻¹ * (D.j γ.out)⁻¹ * p.2))).comp
      measurable_fst).mul (hG.measurable.comp measurable_snd)
  have hlim : Tendsto (fun (s : Finset (PG F)) (y : D.Y) => ∑ γ ∈ s, T D k p γ y) atTop
      (𝓝 fun y => ∑' γ, T D k p γ y) :=
    tendsto_pi_nhds.2 fun y => ((hsumm y).of_norm).hasSum
  exact measurable_of_tendsto_metrizable' atTop (fun s => Finset.measurable_sum s fun γ _ => hTm γ) hlim

end UpperTheory.Esk.KernelInverseSymmetry

theorem UpperTheory.Esk.kernel_inverse_symmetry : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0a → UpperTheory.Esk.E0d → UpperTheory.Esk.KapSum → UpperTheory.Esk.faceMap_zero_comp_eq_one := by
  intro hB1a hB1b hB1c hE0a _ hKS F I Gf _ _ _ D hAx k hk _ p
  exact UpperTheory.Esk.KernelInverseSymmetry.main D hB1a hB1b hB1c hE0a hKS hAx k hk p
end
end

