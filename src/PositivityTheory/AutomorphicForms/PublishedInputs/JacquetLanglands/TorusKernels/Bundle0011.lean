import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfEcut
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.TruncationKernelLemmas

open UpperTheory.Esk

def iN : P := ⟨-Complex.I, by simp⟩

def bs {I : Type} (e : I → Bool) : X I := fun v => if e v then iP else iN

theorem kap_pos (a z : P) (ha : a.1.im = 1 ∨ a.1.im = -1) (h : 0 < a.1.im * z.1.im) : 0 < kap a z := by
  unfold kap
  rw [if_pos h]
  apply div_pos (by linarith)
  apply pow_pos
  apply norm_pos_iff.2
  intro h0
  have h1 := congrArg Complex.im h0
  simp at h1
  rcases ha with ha | ha <;> rw [ha] at h h1 <;> nlinarith

theorem kap_bs_pos {I : Type} (z : X I) (v : I) :
    0 < kap (bs (fun i => decide (0 < (z v).1.im)) v) (z v) := by
  have hz := (z v).2
  unfold bs
  by_cases h : 0 < (z v).1.im
  · simp only [h, decide_true, if_true]
    exact kap_pos _ _ (Or.inl (by simp [iP])) (by simpa [iP] using h)
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    have h' : (z v).1.im < 0 := lt_of_le_of_ne (not_lt.1 h) hz
    exact kap_pos _ _ (Or.inr (by simp [iN])) (by simp [iN]; linarith)

theorem Kap_nonneg {I : Type} [Fintype I] (hk0 : ∀ z w : P, 0 ≤ kap z w) (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun v _ => Real.rpow_nonneg (hk0 _ _) _

open Classical in

def uX {I : Type} [Fintype I] (z : X I) : ℝ := ∑ e : I → Bool, Kap (fun _ => 4) (bs e) z

theorem uX_nonneg {I : Type} [Fintype I] (hk0 : ∀ z w : P, 0 ≤ kap z w) (z : X I) : 0 ≤ uX z :=
  Finset.sum_nonneg fun e _ => Kap_nonneg hk0 _ _ _

theorem uX_pos {I : Type} [Fintype I] (hk0 : ∀ z w : P, 0 ≤ kap z w) (z : X I) : 0 < uX z := by
  classical
  unfold uX
  refine Finset.sum_pos' (fun e _ => Kap_nonneg hk0 _ _ _) ⟨fun v => decide (0 < (z v).1.im), Finset.mem_univ _, ?_⟩
  exact Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (kap_bs_pos z v) _

theorem uX_cont {I : Type} [Fintype I] (hkc : Continuous fun p : P × P => kap p.1 p.2) :
    Continuous (uX : X I → ℝ) := by
  unfold uX Kap
  refine continuous_finsetSum _ fun _ _ => continuous_finsetProd _ fun v _ => ?_
  exact (hkc.comp (continuous_const.prodMk (continuous_apply v))).rpow_const fun _ => Or.inr (by positivity)

theorem tsum_le_fiber {G Ω : Type} (φ : G → Ω) (w : Ω → ℝ≥0∞) (K : G → ℝ≥0∞) (M : ℝ≥0∞)
    (hK : ∀ ω', ∑' g : {g // φ g = ω'}, K g.1 ≤ M) : ∑' g, w (φ g) * K g ≤ (∑' ω', w ω') * M := by
  rw [← ENNReal.tsum_fiberwise _ φ, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun ω' => ?_
  calc ∑' b : φ ⁻¹' {ω'}, w (φ b) * K b = ∑' b : φ ⁻¹' {ω'}, w ω' * K b :=
        tsum_congr fun b => by rw [show φ b = ω' from b.2]
    _ = w ω' * ∑' b : φ ⁻¹' {ω'}, K b := ENNReal.tsum_mul_left
    _ ≤ w ω' * M := by gcongr; exact hK ω'

end UpperTheory.Esk.TruncationKernelLemmas

open UpperTheory.Esk in
open Classical in
theorem UpperTheory.Esk.pf_Ecut : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.C2 → UpperTheory.Esk.E0a → UpperTheory.Esk.E0d → UpperTheory.Esk.KapSum → UpperTheory.Esk.Ecut := by
  intro _ hB hC hE _ hK F I Gf _ _ _ D hax
  obtain ⟨hcount, -, hpres, -⟩ := hE F I Gf D hax
  have : Countable (PG F) := hcount
  have : Countable D.Om := hax.cO
  obtain ⟨hk0', -, -, -, hkc, -⟩ := hB
  have hk0 : ∀ z w : P, 0 ≤ kap z w := fun z w => (hk0' z w).1
  obtain ⟨c₀, hc₀, hmk⟩ := hax.mink
  obtain ⟨C, hCK⟩ := hK F I Gf D hax (fun _ => 4) (fun _ => le_rfl) c₀ hc₀
  have hmX : ∀ g : PG F, Measurable fun z : D.Xs => g • z := fun g => (hpres g).measurable
  have hfib : ∀ y : D.Y, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ (e : I → Bool) (ω' : D.Om),
      ∑' γ : {γ : PG F // γ • y.1 = ω'}, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (γ.1 • y.2 : D.Xs)) ≤ M := by
    intro y
    obtain ⟨s, hs, hsy⟩ := hmk y.2 (D.rep y.1)
    exact ⟨_, ENNReal.ofReal_ne_top, fun e ω' => hCK y s hs hsy ω' (TruncationKernelLemmas.bs e)⟩
  have hucont : Continuous (TruncationKernelLemmas.uX : X I → ℝ) := TruncationKernelLemmas.uX_cont hkc
  have hsplit : ∀ z : X I, ENNReal.ofReal (TruncationKernelLemmas.uX z) =
      ∑ e : I → Bool, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) z) := by
    intro z
    rw [TruncationKernelLemmas.uX, ENNReal.ofReal_sum_of_nonneg (fun e _ => TruncationKernelLemmas.Kap_nonneg hk0 _ _ _)]
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat D.Om
  set w : D.Om → ℝ := fun ω => (1 / 2 : ℝ) ^ f ω with hw
  have hW : ∑' ω, ENNReal.ofReal (w ω) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' n : ℕ, (1 / 2 : ℝ) ^ n))
      ((ENNReal.tsum_comp_le_tsum_of_injective hf (fun n => ENNReal.ofReal ((1 / 2 : ℝ) ^ n))).trans (le_of_eq ?_))
    exact (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two).symm
  refine ⟨?_, ?_⟩
  · refine (hC (PG F) D.Y).1 ?_ (fun y => w y.1 * TruncationKernelLemmas.uX y.2) ?_ ?_ ?_ ?_
    · intro g
      exact (Measurable.of_discrete.comp measurable_fst).prodMk ((hmX g).comp measurable_snd)
    · have h1 : Measurable fun y : D.Y => w y.1 := (Measurable.of_discrete (f := w)).comp measurable_fst
      have h2 : Measurable fun y : D.Y => TruncationKernelLemmas.uX (y.2 : X I) := hucont.measurable.comp measurable_snd
      exact h1.mul h2
    · exact fun y => mul_nonneg (by positivity) (TruncationKernelLemmas.uX_nonneg hk0 _)
    · exact fun y => ⟨1, by simpa using mul_pos (by positivity : (0 : ℝ) < w y.1) (TruncationKernelLemmas.uX_pos hk0 y.2)⟩
    · intro y
      obtain ⟨M, hM, hMb⟩ := hfib y
      have hle : ∑' g : PG F, ENNReal.ofReal (w (g • y).1 * TruncationKernelLemmas.uX (g • y).2) ≤
          ∑ e : I → Bool, (∑' ω, ENNReal.ofReal (w ω)) * M := by
        calc ∑' g : PG F, ENNReal.ofReal (w (g • y).1 * TruncationKernelLemmas.uX (g • y).2)
            = ∑' g : PG F, ∑ e : I → Bool, ENNReal.ofReal (w (g • y.1)) *
                ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • y.2 : D.Xs)) := by
              refine tsum_congr fun g => ?_
              exact (ENNReal.ofReal_mul (by positivity)).trans
                ((congrArg (fun t => ENNReal.ofReal (w (g • y.1)) * t) (hsplit _)).trans (by rw [Finset.mul_sum]; rfl))
          _ = ∑ e : I → Bool, ∑' g : PG F, ENNReal.ofReal (w (g • y.1)) *
                ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • y.2 : D.Xs)) :=
              Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
          _ ≤ _ := Finset.sum_le_sum fun e _ => TruncationKernelLemmas.tsum_le_fiber (fun g : PG F => g • y.1)
                (fun ω => ENNReal.ofReal (w ω))
                (fun g : PG F => ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • y.2 : D.Xs))) M (hMb e)
      have hfin : ∑' g : PG F, ENNReal.ofReal (w (g • y).1 * TruncationKernelLemmas.uX (g • y).2) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.sum_lt_top.2 fun e _ => ENNReal.mul_lt_top hW.lt_top hM.lt_top).ne hle
      refine (ENNReal.summable_toReal hfin).congr fun g => ?_
      exact ENNReal.toReal_ofReal (mul_nonneg (by positivity) (TruncationKernelLemmas.uX_nonneg hk0 _))
  · intro ω S hS
    refine (hC S D.Xs).1 ?_ TruncationKernelLemmas.uX ?_ ?_ ?_ ?_
    · intro g
      exact hmX (g : PG F)
    · exact hucont.measurable
    · exact TruncationKernelLemmas.uX_nonneg hk0
    · exact fun z => ⟨1, by simpa using TruncationKernelLemmas.uX_pos hk0 z⟩
    · intro z
      obtain ⟨M, hM, hMb⟩ := hfib ((ω, z) : D.Y)
      have hinj : Function.Injective (fun g : S => (⟨(g : PG F), hS g.2⟩ : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω})) :=
by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun x : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω} => x.1) h
      have hle : ∑' g : S, ENNReal.ofReal (TruncationKernelLemmas.uX (g • z : D.Xs)) ≤ ∑ e : I → Bool, M := by
        calc ∑' g : S, ENNReal.ofReal (TruncationKernelLemmas.uX (g • z : D.Xs))
            = ∑' g : S, ∑ e : I → Bool, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • z : D.Xs)) :=
              tsum_congr fun g => hsplit _
          _ = ∑ e : I → Bool, ∑' g : S, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • z : D.Xs)) :=
              Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
          _ ≤ _ := Finset.sum_le_sum fun e _ =>
              (ENNReal.tsum_comp_le_tsum_of_injective hinj
                (fun γ : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω} =>
                  ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (γ.1 • ((ω, z) : D.Y).2 : D.Xs)))).trans (hMb e ω)
      have hfin : ∑' g : S, ENNReal.ofReal (TruncationKernelLemmas.uX (g • z : D.Xs)) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.sum_lt_top.2 fun e _ => hM.lt_top).ne hle
      refine (ENNReal.summable_toReal hfin).congr fun g => ?_
      exact ENNReal.toReal_ofReal (TruncationKernelLemmas.uX_nonneg hk0 _)
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfFcen
section
open Matrix

namespace UpperTheory.Esk.CentralTermsContribution

theorem trace_conj {F : Type} [Field F] (γ δ : GL (Fin 2) F) :
    ((δ * γ * δ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = (γ : Matrix (Fin 2) (Fin 2) F).trace := by
  simp only [Units.val_mul]
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

end UpperTheory.Esk.CentralTermsContribution

theorem UpperTheory.Esk.pf_Fcen : UpperTheory.Esk.Fcen := by
  intro F _ γ δ htr h
  have h' : ((δ * γ * δ⁻¹ : GL (Fin 2) F) : UpperTheory.Esk.PG F) = (γ : UpperTheory.Esk.PG F) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]; exact h
  rw [QuotientGroup.eq] at h'
  set c := (δ * γ * δ⁻¹)⁻¹ * γ with hc
  obtain ⟨h1, h2, h3⟩ := UpperTheory.Esk.center_entries h'
  have hcv : (c : Matrix (Fin 2) (Fin 2) F) = c 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]
  have hγ : γ = (δ * γ * δ⁻¹) * c := by rw [hc]; group
  have hv : (γ : Matrix (Fin 2) (Fin 2) F) = ((δ * γ * δ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) := by
    conv_lhs => rw [hγ]
    rw [Units.val_mul]
  have htr2 : c 0 0 * (γ : Matrix (Fin 2) (Fin 2) F).trace = 1 * (γ : Matrix (Fin 2) (Fin 2) F).trace := by
    conv_rhs => rw [hv, hcv, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, UpperTheory.Esk.CentralTermsContribution.trace_conj]
    ring
  have ht : c 0 0 = 1 := mul_right_cancel₀ htr htr2
  have hc1 : c = 1 := by
    ext : 1
    rw [hcv, ht, one_smul, Units.val_one]
  rw [hc1, mul_one] at hγ
  calc δ * γ = δ * γ * δ⁻¹ * δ := by group
    _ = γ * δ := by rw [← hγ]
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfFhyp
section
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal

namespace UpperTheory.Esk.HyperbolicTermsContribution

open UpperTheory.Esk

theorem vecMul_ne {F : Type} [Field F] (s : Fin 2 → F) (hs : s ≠ 0) (δ : GL (Fin 2) F) : s ᵥ* δ.val ≠ 0 := by
  intro h
  apply hs
  have h2 := congrArg (fun v => v ᵥ* (δ⁻¹ : GL (Fin 2) F).val) h
  simpa [Matrix.vecMul_vecMul] using h2

theorem isEll_conj {F : Type} [Field F]
    (hfix : ∀ (s : Fin 2 → F) (γ δ : GL (Fin 2) F), Fix s ((δ : PG F) * γ * (δ : PG F)⁻¹) ↔
      ∃ c : F, (s ᵥ* δ.val) ᵥ* γ.val = c • (s ᵥ* δ.val)) (g γ : PG F) :
    IsEll (g * γ * g⁻¹) ↔ IsEll γ := by
  obtain ⟨δ, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective γ
  have h1 : ∀ s : Fin 2 → F, Fix s (γ : PG F) ↔ ∃ c : F, s ᵥ* γ.val = c • s := by
    intro s
    have := hfix s γ 1
    simpa using this
  constructor
  · intro h s hs hf
    obtain ⟨c, hc⟩ := (h1 s).1 hf
    have hs' : s ᵥ* (δ⁻¹ : GL (Fin 2) F).val ≠ 0 := vecMul_ne s hs _
    apply h _ hs'
    rw [hfix]
    refine ⟨c, ?_⟩
    have e : (s ᵥ* (δ⁻¹ : GL (Fin 2) F).val) ᵥ* δ.val = s := by
      rw [Matrix.vecMul_vecMul]; simp
    rw [e, hc]
  · intro h s hs hf
    obtain ⟨c, hc⟩ := (hfix s γ δ).1 hf
    exact h _ (vecMul_ne s hs δ) ((h1 _).2 ⟨c, hc⟩)

variable {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι]

open Classical in

def uT (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (T : ℝ) (γ : PG F) (y : D.Y) : ℂ :=
  if IsEll γ then 0 else (D.LamF T γ).indicator (D.kk k a γ) y

theorem enorm_uT_le (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (T : ℝ) (γ : PG F) (y : D.Y) :
    ‖uT D k a T γ y‖ₑ ≤ ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ := by
  unfold uT
  split_ifs <;> simp

theorem enorm_ind_le (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (T : ℝ) (γ : PG F) (y : D.Y) :
    ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ ≤ ‖D.kk k a γ y‖ₑ := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> simp

open Classical in
theorem fhyp (hC4 : C4) (hE0a : E0a) (hE0c : KernelTermsInvariantBounded) (hE0d : E0d) (hE2 : E2) (hE3 : E3) (hEcut : Ecut)
    (hFsum : Fsum) (hF5 : F5) (hF6 : F6) (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (hyp : D.Hyp k a)
    (b : D.Y → ℝ) (hb : IsCut (PG F) b)
    (hint : Integrable (fun y => b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) D.μY) :
    ∫ y, b y • (∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) ∂D.μY = 0 := by
  have hax := hyp.ax
  obtain ⟨hcnt, hsf, hpres, -, -, -, -, -⟩ := hE0a F I Gf D hax
  obtain ⟨-, hkkc, hkkm, -, -, -⟩ := hE0c F I Gf ι D k a hyp
  obtain ⟨-, -, -, -, -, -, -, hLamF, hev, -, hfix⟩ := hE0d F I Gf D hax
  obtain ⟨-, hE2'⟩ := hE2 F I Gf ι D k a hyp
  have hb3 := hE3 F I Gf D hax b hb
  obtain ⟨-, hcut⟩ := hEcut F I Gf D hax
  obtain ⟨C, hC⟩ := hF5 F I Gf ι D k a hyp
  have hF6' := hF6 F I Gf ι D k a hyp
  have : Countable (PG F) := hcnt
  have : Countable D.Cj := hcnt
  have : Countable D.Om := hax.cO

  have hbI : Integrable b D.μY := by
    refine ⟨hb.meas.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq ?_) hb3
    refine lintegral_congr fun y => ?_
    exact Real.enorm_eq_ofReal (hb.nonneg y)

  have hum : ∀ T γ, Measurable (uT D k a T γ) := by
    intro T γ
    by_cases h : IsEll γ
    · unfold uT; simp only [h, if_true]; exact measurable_const
    · unfold uT; simp only [h, if_false]; exact (hkkm γ).indicator (hLamF T γ).1

  have hsumle : ∀ T : ℝ, 1 < T → ∀ y, y ∉ D.abelian₂ T → ∑' γ, ‖uT D k a T γ y‖ₑ ≤ C := by
    intro T hT y hy
    exact le_trans (ENNReal.tsum_le_tsum fun γ => enorm_uT_le D k a T γ y) ((hC T hT y).2 hy)
  have hon : ∀ T : ℝ, 1 < T → ∀ y, y ∈ D.abelian₂ T → ∀ γ, uT D k a T γ y = if IsEll γ then 0 else D.kk k a γ y := by
    intro T hT y hy γ
    unfold uT
    split_ifs
    · rfl
    · exact Set.indicator_of_mem ((hC T hT y).1 hy γ) _

  have hinv : ∀ T (g γ : PG F) (y : D.Y), uT D k a T (g * γ * g⁻¹) (g • y) = uT D k a T γ y := by
    intro T g γ y
    unfold uT
    rw [isEll_conj hfix g γ]
    split_ifs
    · rfl
    · rw [Set.indicator_apply, Set.indicator_apply, hkkc]
      simp only [(hLamF T γ).2 g y]

  have step1 : ∀ T : ℝ, 1 < T → Integrable (fun y => b y • ∑' γ, uT D k a T γ y) D.μY ∧
      ∫ y, b y • ∑' γ, uT D k a T γ y ∂D.μY = 0 := by
    intro T hT
    obtain ⟨CT, hCT⟩ := hE2' T
    have hfin : ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖uT D k a T γ y‖ₑ ∂D.μY < ⊤ := by
      have hle : ∀ y, ∑' γ, ‖uT D k a T γ y‖ₑ ≤ (CT : ℝ≥0∞) + C := by
        intro y
        by_cases hy : y ∈ D.abelian₂ T
        · refine le_trans ?_ le_self_add
          refine le_trans (ENNReal.tsum_le_tsum fun γ => ?_) (hCT y hy)
          exact (enorm_uT_le D k a T γ y).trans (enorm_ind_le D k a T γ y)
        · exact (hsumle T hT y hy).trans le_add_self
      calc ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖uT D k a T γ y‖ₑ ∂D.μY
          ≤ ∫⁻ y, ENNReal.ofReal (b y) * ((CT : ℝ≥0∞) + C) ∂D.μY :=
            lintegral_mono fun y => by gcongr; exact hle y
        _ = (∫⁻ y, ENNReal.ofReal (b y) ∂D.μY) * ((CT : ℝ≥0∞) + C) :=
            lintegral_mul_const' _ _ (by simp)
        _ < ⊤ := ENNReal.mul_lt_top hb3 (by simp)
    obtain ⟨hb', hFs⟩ := hFsum F I Gf D hax b hb
    obtain ⟨hm', hi', hiY, heq⟩ := hFs (uT D k a T) (hum T) hfin
    refine ⟨hiY, ?_⟩
    rw [heq]

    let R : Set (D.Cj × D.Om) := Set.range (fun q : MulAction.orbitRel.Quotient (PG F) (D.Cj × D.Om) => q.out)
    have hR : ∀ ω : D.Cj × D.Om, ∃! r, r ∈ R ∧ r ∈ MulAction.orbit (PG F) ω := by
      intro ω
      refine ⟨(Quotient.mk (MulAction.orbitRel (PG F) (D.Cj × D.Om)) ω).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
      · exact (MulAction.orbitRel_apply).1 (Quotient.mk_out ω)
      · rintro r ⟨⟨q, rfl⟩, hq⟩
        have e1 : q = Quotient.mk (MulAction.orbitRel (PG F) (D.Cj × D.Om)) ω := by
          rw [← Quotient.out_eq q]
          exact Quotient.sound ((MulAction.orbitRel_apply).2 hq)
        rw [e1]
    have hβ : ∀ r : D.Cj × D.Om, ∃ β : D.Xs → ℝ, IsCut (MulAction.stabilizer (PG F) r) β := by
      intro r
      refine hcut r.2 _ ?_
      intro g hg
      rw [MulAction.mem_stabilizer_iff] at hg ⊢
      have := congrArg Prod.snd hg
      simpa using this
    choose β hβ using hβ
    have hinv' : ∀ (g : PG F) (p : (D.Cj × D.Om) × D.Xs),
        uT D k a T (D.el (g • p).1.1) ((g • p).1.2, (g • p).2) = uT D k a T (D.el p.1.1) (p.1.2, p.2) := by
      intro g p
      have e : ((g • p).1.2, (g • p).2) = g • ((p.1.2, p.2) : D.Y) := rfl
      rw [e, show D.el (g • p).1.1 = g * D.el p.1.1 * g⁻¹ from D.smulC g p.1.1, hinv]
    obtain ⟨hI, hS⟩ := hC4 (PG F) (D.Cj × D.Om) D.Xs volume hpres _ hb' _ hm' hinv' hi' R hR β (fun r _ => hβ r)
    have hz : ∀ r : R, ∫ x, β r x • uT D k a T (D.el r.1.1) (r.1.2, x) = 0 := by
      intro r
      by_cases he : IsEll (D.el r.1.1)
      · simp [uT, he]
      · have hI' := hI r.1 r.2
        simp only [uT, he, if_false] at hI' ⊢
        exact hF6' T hT (D.el r.1.1) r.1.2 he (β r.1) (hβ r.1) hI'
    have hS' := hS
    simp only [hz] at hS'
    exact (hS'.unique hasSum_zero)

  have hT2 : ∀ n : ℕ, (1 : ℝ) < (n : ℝ) + 2 := fun n => by
    have := n.cast_nonneg (α := ℝ)
    linarith
  have hlim : Tendsto (fun n : ℕ => ∫ y, b y • ∑' γ, uT D k a ((n : ℝ) + 2) γ y ∂D.μY) atTop
      (𝓝 (∫ y, b y • (∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) ∂D.μY)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => ‖b y • ∑' γ : PG F, (if IsEll γ then 0 else D.kk k a γ y)‖ + b y * C)
      (fun n => (step1 _ (hT2 n)).1.aestronglyMeasurable) (hint.norm.add (hbI.mul_const _)) ?_ ?_
    · intro n
      refine Filter.Eventually.of_forall fun y => ?_
      have hT : (1 : ℝ) < (n : ℝ) + 2 := hT2 n
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (hb.nonneg y), ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (hb.nonneg y)
      by_cases hy : y ∈ D.abelian₂ ((n : ℝ) + 2)
      · rw [tsum_congr (hon _ hT y hy)]
        exact le_add_of_nonneg_right C.2
      · have h1 : ‖∑' γ, uT D k a ((n : ℝ) + 2) γ y‖ₑ ≤ C :=
          enorm_tsum_le_tsum_enorm.trans (hsumle _ hT y hy)
        have h2 : ‖∑' γ, uT D k a ((n : ℝ) + 2) γ y‖ ≤ C := by
          have := ENNReal.toReal_mono ENNReal.coe_ne_top h1
          simpa using this
        exact h2.trans (le_add_of_nonneg_left (norm_nonneg _))
    · refine Filter.Eventually.of_forall fun y => ?_
      obtain ⟨T₀, hT₀⟩ := hev y
      obtain ⟨N, hN⟩ := exists_nat_ge T₀
      refine tendsto_const_nhds.congr' ?_
      refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have hT : (1 : ℝ) < (n : ℝ) + 2 := hT2 n
      have hy : y ∈ D.abelian₂ ((n : ℝ) + 2) := hT₀ _ (by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
      dsimp only
      rw [tsum_congr (hon _ hT y hy)]
  have h0 : Tendsto (fun n : ℕ => ∫ y, b y • ∑' γ, uT D k a ((n : ℝ) + 2) γ y ∂D.μY) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => ?_)
    exact ((step1 _ (hT2 n)).2).symm
  exact tendsto_nhds_unique hlim h0

end UpperTheory.Esk.HyperbolicTermsContribution

theorem UpperTheory.Esk.pf_Fhyp : UpperTheory.Esk.C4 → UpperTheory.Esk.E0a → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.E2 → UpperTheory.Esk.E3 → UpperTheory.Esk.Ecut → UpperTheory.Esk.Fsum → UpperTheory.Esk.F5 → UpperTheory.Esk.F6 → UpperTheory.Esk.Fhyp := by
  intro hC4 hE0a hE0c hE0d hE2 hE3 hEcut hFsum hF5 hF6 F I Gf ι _ _ _ _ D k a hyp b hb hint
  exact UpperTheory.Esk.HyperbolicTermsContribution.fhyp hC4 hE0a hE0c hE0d hE2 hE3 hEcut hFsum hF5 hF6 D k a hyp b hb hint
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfFsum
section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UpperTheory.Esk.SummedOrbitIntegrals

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]

theorem meas_pair [Countable α] {E : Type*} [MeasurableSpace E] {f : α → β → E} (hf : ∀ a, Measurable (f a)) :
    Measurable (fun q : α × β => f q.1 q.2) := by
  intro s hs
  have e : (fun q : α × β => f q.1 q.2) ⁻¹' s = ⋃ a : α, ({a} : Set α) ×ˢ (f a ⁻¹' s) := by
    ext ⟨a, b⟩
    simp
  rw [e]
  exact MeasurableSet.iUnion fun a => (measurableSet_singleton a).prod (hf a hs)

theorem lint_pair (μ : Measure β) [SFinite μ] (f : α × β → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, f q ∂(Measure.count.prod μ) = ∑' a, ∫⁻ y, f (a, y) ∂μ := by
  rw [lintegral_prod f hf.aemeasurable, lintegral_count]

theorem count_prod {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [Countable A] [Countable B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    (Measure.count : Measure A).prod (Measure.count : Measure B) = Measure.count := by
  refine Measure.ext_iff_singleton.2 fun p => ?_
  obtain ⟨a, b⟩ := p
  rw [Measure.count_singleton, ← Set.singleton_prod_singleton, Measure.prod_prod,
    Measure.count_singleton, Measure.count_singleton, one_mul]

end UpperTheory.Esk.SummedOrbitIntegrals

open UpperTheory.Esk.SummedOrbitIntegrals in
theorem UpperTheory.Esk.pf_Fsum : UpperTheory.Esk.E0a → UpperTheory.Esk.Fsum := by
  intro h0 F I Gf _ _ _ D hax
  obtain ⟨hcG, hsig, -⟩ := h0 F I Gf D hax
  haveI : Countable D.Cj := hcG
  haveI : Countable D.Om := hax.cO
  haveI : SigmaFinite (volume : Measure D.Xs) := hsig
  haveI : SFinite D.μY := by unfold UpperTheory.Esk.Dat.μY; infer_instance
  intro b hb
  refine ⟨⟨hb.meas.comp (measurable_fst.snd.prodMk measurable_snd), fun p => hb.nonneg _,
    fun p => hb.sum (p.1.2, p.2)⟩, ?_⟩
  intro u hu hfin
  have hgm : Measurable (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2) :=
    meas_pair (f := fun (c : D.Cj) (y : D.Y) => b y • u (D.el c) y) fun c => hb.meas.smul (hu (D.el c))
  have hlin : ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY) =
      ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY := by
    calc ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY)
        = ∑' c : D.Cj, ∫⁻ y, ‖b y • u (D.el c) y‖ₑ ∂D.μY :=
          lint_pair D.μY (fun q : D.Cj × D.Y => ‖b q.2 • u (D.el q.1) q.2‖ₑ) hgm.enorm
      _ = ∫⁻ y, ∑' c : D.Cj, ‖b y • u (D.el c) y‖ₑ ∂D.μY :=
          (lintegral_tsum fun c => ((hb.meas.smul (hu (D.el c))).enorm).aemeasurable).symm
      _ = ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY := by
          refine lintegral_congr fun y => ?_
          simp only [enorm_smul, Real.enorm_of_nonneg (hb.nonneg y)]
          exact ENNReal.tsum_mul_left
  have hgi : Integrable (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2) (Measure.count.prod D.μY) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    show ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY) < ⊤
    rw [hlin]
    exact hfin
  have hae : ∀ᵐ y ∂D.μY, ∫ c, b y • u (D.el c) y ∂(Measure.count : Measure D.Cj) = b y • ∑' γ, u γ y := by
    filter_upwards [hgi.prod_left_ae] with y hy
    have hy' : Integrable (fun c : D.Cj => b y • u (D.el c) y) Measure.count := hy
    rw [integral_countable' hy']
    simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    exact tsum_const_smul'' (b y)
  have hP : Integrable (fun y => b y • ∑' γ, u γ y) D.μY := hgi.integral_prod_right.congr hae
  have hm1 : Measurable (fun p : (D.Cj × D.Om) × D.Xs => u (D.el p.1.1) (p.1.2, p.2)) :=
    meas_pair (α := D.Cj × D.Om) (β := D.Xs) (f := fun a z => u (D.el a.1) (a.2, z))
      fun a => (hu (D.el a.1)).comp measurable_prodMk_left
  have hmp : MeasurePreserving (MeasurableEquiv.prodAssoc : (D.Cj × D.Om) × D.Xs ≃ᵐ D.Cj × D.Om × D.Xs)
      D.μC (Measure.count.prod D.μY) := by
    have e : D.μC = (Measure.count.prod Measure.count).prod volume := by
      unfold UpperTheory.Esk.Dat.μC
      rw [count_prod]
    rw [e]
    exact measurePreserving_prodAssoc _ _ _
  have hC : Integrable (fun p : (D.Cj × D.Om) × D.Xs => b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2)) D.μC :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hgi
  have hint : ∫ y, b y • ∑' γ, u γ y ∂D.μY =
      ∫ p, b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2) ∂D.μC := by
    calc ∫ y, b y • ∑' γ, u γ y ∂D.μY
        = ∫ y, ∫ c, b y • u (D.el c) y ∂(Measure.count : Measure D.Cj) ∂D.μY := (integral_congr_ae hae).symm
      _ = ∫ q, b q.2 • u (D.el q.1) q.2 ∂(Measure.count.prod D.μY) := (integral_prod_symm _ hgi).symm
      _ = ∫ p, b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2) ∂D.μC :=
          (hmp.integral_comp' (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2)).symm
  exact ⟨hm1, hC, hP, hint⟩
end
end

