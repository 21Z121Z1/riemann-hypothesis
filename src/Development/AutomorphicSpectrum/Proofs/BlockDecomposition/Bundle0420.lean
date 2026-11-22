import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.TemperednessTransfer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0406
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0389
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0407
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.InUQT

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMemOfStable
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.InjHw

variable {n : ℕ}

theorem exp_mem_unitary (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]
  have h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
    rw [conjTranspose_smul, hX]
    simp
  have hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X)) := (Commute.refl _).neg_right
  rw [h, ← Matrix.exp_add_of_commute _ _ hc]
  simp

theorem single_conjT (a b : Fin n) (c : ℂ) :
    (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ)ᴴ = Matrix.single b a (star c) := by
  ext i j
  simp only [conjTranspose_apply, Matrix.single_apply]
  by_cases h : a = j ∧ b = i
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.2, hh.1⟩)]
    simp

theorem single_negI (a b : Fin n) (c : ℂ) :
    (Matrix.single a b (-c) : Matrix (Fin n) (Fin n) ℂ) = -Matrix.single a b c := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.single_apply]
  split_ifs <;> simp

def expU (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨NormedSpace.exp ((s : ℂ) • X), exp_mem_unitary X hX s⟩

section V

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {Kf : Fin n → Fin n → Module.End ℂ V}

theorem deriv_expU (h : IsDerivK σ Kf) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (w : V) :
    HasDerivAt (fun s : ℝ => σ (expU X hX s) w) (∑ a, ∑ b, X a b • Kf a b w) 0 := by
  obtain ⟨S, _, hw, _, _, hd⟩ := h.2 w
  exact hd X (expU X hX) (fun _ => rfl) w hw

theorem sum_mem_of_stable (h : IsDerivK σ Kf) (R : Submodule ℂ V) [FiniteDimensional ℂ R]
    (hR : ∀ k, ∀ w ∈ R, σ k w ∈ R) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) {w : V} (hw : w ∈ R) :
    ∑ a, ∑ b, X a b • Kf a b w ∈ R := by
  have hd := deriv_expU h X hX w
  have hcl : IsClosed (R : Set V) := Submodule.closed_of_finiteDimensional R
  have ht := hasDerivAt_iff_tendsto_slope_zero.1 hd
  refine hcl.mem_of_tendsto ht (Filter.Eventually.of_forall fun s => ?_)
  have : s⁻¹ • (σ (expU X hX (0 + s)) w - σ (expU X hX 0) w) ∈ R.restrictScalars ℝ :=
    Submodule.smul_mem _ _ (sub_mem (hR _ _ hw) (hR _ _ hw))
  exact this

theorem sum_single (w : V) (a b : Fin n) (c : ℂ) :
    ∑ x, ∑ y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • Kf x y w = c • Kf a b w := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro y _ hy
    rw [Matrix.single_apply, if_neg (fun hh => hy hh.2.symm), zero_smul]
  · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Matrix.single_apply, if_neg (fun hh => hx hh.1.symm), zero_smul]
  · simp

theorem entry_mem (h : IsDerivK σ Kf) (R : Submodule ℂ V) [FiniteDimensional ℂ R]
    (hR : ∀ k, ∀ w ∈ R, σ k w ∈ R) (a b : Fin n) {w : V} (hw : w ∈ R) : Kf a b w ∈ R := by
  have h1 : (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)ᴴ = -(Matrix.single a b (1 : ℂ) - Matrix.single b a 1) := by
    rw [conjTranspose_sub, single_conjT, single_conjT, star_one, neg_sub]
  have h2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
      -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
    rw [conjTranspose_add, single_conjT, single_conjT, Complex.star_def, Complex.conj_I, single_negI, single_negI, neg_add,
      add_comm]
  have m1 := sum_mem_of_stable h R hR _ h1 hw
  have m2 := sum_mem_of_stable h R hR _ h2 hw
  have e1 : ∑ x, ∑ y, (Matrix.single a b (1 : ℂ) - Matrix.single b a 1 : Matrix (Fin n) (Fin n) ℂ) x y • Kf x y w =
      Kf a b w - Kf b a w := by
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, sum_single, one_smul]
  have e2 : ∑ x, ∑ y, (Matrix.single a b Complex.I + Matrix.single b a Complex.I : Matrix (Fin n) (Fin n) ℂ) x y • Kf x y w =
      Complex.I • Kf a b w + Complex.I • Kf b a w := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, sum_single]
  rw [e1] at m1
  rw [e2] at m2
  have m3 := R.smul_mem (-Complex.I) m2
  have m4 := R.smul_mem (1 / 2 : ℂ) (R.add_mem m1 m3)
  have e3 : (1 / 2 : ℂ) • (Kf a b w - Kf b a w + -Complex.I • (Complex.I • Kf a b w + Complex.I • Kf b a w)) = Kf a b w := by
    rw [smul_add (-Complex.I), smul_smul, smul_smul]
    have : -Complex.I * Complex.I = 1 := by simp
    rw [this, one_smul, one_smul, sub_add_add_cancel, ← two_smul ℂ, smul_smul]
    norm_num
  rwa [e3] at m4

theorem weight_of_torus (h : IsDerivK σ Kf) (μ : Fin n → ℤ) {v : V}
    (hv : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → σ k v = (∏ a, z a ^ μ a) • v)
    (a : Fin n) : Kf a a v = ((μ a : ℝ) : ℂ) • v := by
  have hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I) := by
    rw [single_conjT, Complex.star_def, Complex.conj_I, single_negI]
  have hd := deriv_expU (Kf := Kf) h _ hX v
  rw [sum_single] at hd
  have hk : ∀ s : ℝ, (expU _ hX s).1 = diagonal (fun c => if c = a then Complex.exp (s * Complex.I) else 1) := by
    intro s
    have e : (s : ℂ) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ) =
        diagonal (fun c => if c = a then (s : ℂ) * Complex.I else 0) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases hc : i = a
        · subst hc
          simp
        · simp [Matrix.single_apply, hc, Ne.symm hc]
      · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.single_apply,
          if_neg (fun hh => hij (hh.1.symm.trans hh.2)), smul_zero]
    show NormedSpace.exp _ = _
    rw [e, Matrix.exp_diagonal]
    congr 1
    funext c
    split_ifs with hc <;> simp [hc, Complex.exp_eq_exp_ℂ]
  have hf : (fun s : ℝ => σ (expU _ hX s) v) =
      fun s : ℝ => Complex.exp ((s : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) • v := by
    funext s
    rw [hv _ _ (hk s), Finset.prod_eq_single a]
    · simp only [if_true]
      rw [← Complex.exp_int_mul]
      congr 2
      push_cast
      ring
    · intro c _ hc
      simp [hc]
    · simp
  rw [hf] at hd
  have h2 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) • v)
      ((Complex.I * ((μ a : ℝ) : ℂ)) • v) 0 := by
    have h3 : HasDerivAt (fun y : ℂ => Complex.exp (y * (Complex.I * ((μ a : ℝ) : ℂ))))
        (Complex.exp ((0 : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) * (1 * (Complex.I * ((μ a : ℝ) : ℂ)))) 0 :=
      ((hasDerivAt_id (0 : ℂ)).mul_const _).cexp
    have h4 := (h3.comp_ofReal).smul_const v
    simpa using h4
  have e := hd.unique h2
  calc Kf a a v = (-Complex.I) • (Complex.I • Kf a a v) := by rw [smul_smul]; simp
    _ = ((μ a : ℝ) : ℂ) • v := by rw [e, smul_smul, ← mul_assoc]; simp

end V

section Main

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem gl_kF {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : IsPair E1 E2) : Formalism.REAL.GlRel (kF E1 E2) := by
  intro a b c d
  have h1 := h.gl1 a b c d
  have h2 := h.gl2 a b c d
  have c1 := h.comm a b c d
  have c2 := h.comm c d a b
  have e : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [kF, add_mul, mul_add]
    rw [c1, c2]
    abel
  rw [e, h1, h2]
  simp only [kF]
  split_ifs <;> abel

theorem weight_shift {K : Fin n → Fin n → Module.End ℂ V} (hg : Formalism.REAL.GlRel K) (μ : Fin n → ℤ) {v : V}
    (hv : ∀ c, K c c v = ((μ c : ℝ) : ℂ) • v) {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    K c c (K a b v) =
      (((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℤ) : ℝ) : ℂ) • K a b v := by
  have e : K c c (K a b v) = K a b (K c c v) +
      ((if c = a then K c b else 0) - (if b = c then K a c else 0)) v := by
    rw [← hg c c a b]
    simp [Module.End.mul_apply]
  rw [e, hv c, map_smul]
  by_cases h1 : c = a
  · subst h1
    have h2 : ¬ b = c := fun h => hab h.symm
    have h3 : ¬ c = b := hab
    simp only [↓reduceIte, h2, h3, LinearMap.sub_apply, LinearMap.zero_apply]
    push_cast
    module
  · by_cases h2 : c = b
    · subst h2
      simp only [↓reduceIte, h1, LinearMap.sub_apply, LinearMap.zero_apply]
      push_cast
      module
    · have h3 : ¬ b = c := fun h => h2 h.symm
      simp only [↓reduceIte, h1, h2, h3, sub_zero, LinearMap.zero_apply, add_zero]

def jt (K : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ) : Submodule ℂ V :=
  ⨅ c, (K c c).maxGenEigenspace (χ c)

theorem mem_jt {K : Fin n → Fin n → Module.End ℂ V} {χ : Fin n → ℂ} {v : V} (hv : ∀ c, K c c v = χ c • v) :
    v ∈ jt K χ := by
  refine (Submodule.mem_iInf _).2 fun c => ?_
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨1, by simp [hv c]⟩

theorem jt_indep {K : Fin n → Fin n → Module.End ℂ V} (hg : Formalism.REAL.GlRel K) : iSupIndep (jt K) := by
  have hc : ∀ i j, Commute (K i i) (K j j) := by
    intro i j
    have h := hg i i j j
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · have h' : ¬ j = i := fun h => hij h.symm
      rw [if_neg hij, if_neg h', sub_zero] at h
      exact sub_eq_zero.1 h
  exact Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun c => K c c)
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)

def wtC (μ : Fin n → ℤ) : Fin n → ℂ := fun a => ((μ a : ℝ) : ℂ)

theorem wtC_injective : Function.Injective (wtC (n := n)) := by
  intro x y h
  funext c
  have := congrFun h c
  simpa [wtC] using this

end Main

end GlobalTheory.CompanionTheory.RealCount.InjHw
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedRestriction
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Module
open PositivityTheory.Pf1.CLGD.DescRes LocalGlobalAboveLAlt

namespace GlobalTheory.CompanionTheory.TempRes

section Lin

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem iSup_eigenspace_eq_top {f : End ℂ V} (hf : f.IsSemisimple) : ⨆ α, f.eigenspace α = ⊤ := by
  have h := Module.End.iSup_maxGenEigenspace_eq_top f
  simp_rw [hf.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at h
  exact h

theorem mem_eigenspace_pow {f : End ℂ V} {α : ℂ} {v : V} (hv : v ∈ f.eigenspace α) (M : ℕ) :
    v ∈ (f ^ M).eigenspace (α ^ M) := by
  rw [End.mem_eigenspace_iff] at hv ⊢
  induction M with
  | zero => simp
  | succ n ih => rw [pow_succ, End.mul_apply, hv, map_smul, ih, smul_smul, pow_succ, mul_comm]

theorem absSpace_le_pow (f : End ℂ V) (t : ℝ) (M : ℕ) : absSpace f t ≤ absSpace (f ^ M) (t ^ M) := by
  refine iSup₂_le fun α hα v hv => ?_
  exact Submodule.mem_iSup_of_mem (α ^ M) (Submodule.mem_iSup_of_mem (by rw [norm_pow, hα])
    (mem_eigenspace_pow hv M))

theorem absSpace_pow_eq {f : End ℂ V} (hf : f.IsSemisimple) {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : M ≠ 0) :
    absSpace (f ^ M) (t ^ M) = absSpace f t := by
  set S : Set ℂ := {β | ‖β‖ = t ^ M} with hS
  set b : Submodule ℂ V := ⨆ (α : ℂ) (_ : ‖α‖ ≠ t), f.eigenspace α with hb
  have hbW : b ≤ ⨆ β ∈ Sᶜ, (f ^ M).eigenspace β := by
    refine iSup₂_le fun α hα v hv => ?_
    refine Submodule.mem_iSup_of_mem (α ^ M) (Submodule.mem_iSup_of_mem ?_ (mem_eigenspace_pow hv M))
    intro h
    have h' : ‖α‖ ^ M = t ^ M := by simpa [hS, norm_pow] using h
    exact hα ((pow_left_inj₀ (norm_nonneg _) ht hM).mp h')
  have hab : absSpace f t ⊔ b = ⊤ := by
    rw [eq_top_iff, ← iSup_eigenspace_eq_top hf]
    refine iSup_le fun α => ?_
    by_cases hα : ‖α‖ = t
    · exact le_sup_of_le_left (le_iSup₂_of_le α hα le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le α hα le_rfl)
  have hd : Disjoint (absSpace (f ^ M) (t ^ M)) (⨆ β ∈ Sᶜ, (f ^ M).eigenspace β) :=
    (End.eigenspaces_iSupIndep (f ^ M)).disjoint_biSup_biSup (s := S) (t := Sᶜ) disjoint_compl_right
  refine le_antisymm ?_ (absSpace_le_pow f t M)
  have e : absSpace (f ^ M) (t ^ M) = absSpace f t ⊔ (b ⊓ absSpace (f ^ M) (t ^ M)) := by
    rw [← sup_inf_assoc_of_le _ (absSpace_le_pow f t M), hab, top_inf_eq]
  have e0 : b ⊓ absSpace (f ^ M) (t ^ M) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ hbW).trans (by rw [inf_comm]; exact hd.le_bot))
  rw [e0, sup_bot_eq] at e
  exact e.le

end Lin

section Weil

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem exists_pow_eq (a : WDRep h V) {φ ψ : Weil h} {d : ℕ} (hφ : deg φ = 1) (hψ : deg ψ = d) :
    ∃ M : ℕ, 0 < M ∧ a.ρ ψ ^ M = a.ρ φ ^ (d * M) := by
  have key : ∀ n k : ℕ, 0 < k → a.ρ (ψ ^ (n + k) * (φ ^ (d * (n + k)))⁻¹) = a.ρ (ψ ^ n * (φ ^ (d * n))⁻¹) →
      ∃ M : ℕ, 0 < M ∧ a.ρ ψ ^ M = a.ρ φ ^ (d * M) := by
    intro n k hk e
    refine ⟨k, hk, ?_⟩
    have e1 : ψ ^ k = (ψ ^ n)⁻¹ * (ψ ^ (n + k) * (φ ^ (d * (n + k)))⁻¹) * φ ^ (d * (n + k)) := by
      rw [pow_add]; group
    have e2 : φ ^ (d * k) = (ψ ^ n)⁻¹ * (ψ ^ n * (φ ^ (d * n))⁻¹) * φ ^ (d * (n + k)) := by
      rw [mul_add, pow_add]; group
    rw [← map_pow, ← map_pow, e1, e2, map_mul, map_mul, e, ← map_mul, ← map_mul]
  have hdeg : ∀ n : ℕ, deg (ψ ^ n * (φ ^ (d * n))⁻¹) = 0 := fun n => by
    simp [hφ, hψ, mul_comm]
  let u : ℕ → Ine (F := E) A := fun n => ⟨((ψ ^ n * (φ ^ (d * n))⁻¹ : Weil h) : G E Ω), deg_eq_zero_iff.mp (hdeg n)⟩
  have hu : ∀ n, ineIncl h (u n) = ψ ^ n * (φ ^ (d * n))⁻¹ := fun n => Subtype.ext rfl
  have hfin : Finite (Set.range fun σ : Ine (F := E) A => a.ρ (ineIncl h σ)) := a.smooth.finite_range
  obtain ⟨m, n, hne, hmn⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨a.ρ (ineIncl h (u k)), u k, rfl⟩ :
      Set.range fun σ : Ine (F := E) A => a.ρ (ineIncl h σ)))
  have hmn' : a.ρ (ψ ^ m * (φ ^ (d * m))⁻¹) = a.ρ (ψ ^ n * (φ ^ (d * n))⁻¹) := by
    have := congrArg Subtype.val hmn
    simpa only [hu] using this
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact key m (k + 1) (by omega) (by rw [← add_assoc]; exact hmn'.symm)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact key n (k + 1) (by omega) (by rw [← add_assoc]; exact hmn')

theorem isPurePair_iff (a : WDRep h V) {φ ψ : Weil h} {f : ℕ} (hf : f ≠ 0) (hφ : deg φ = 1) (hψ : deg ψ = f) :
    IsPurePair (((normV w : ℕ) : ℝ) ^ f) (a.ρ ψ) a.N ↔ IsPurePair ((normV w : ℕ) : ℝ) (a.ρ φ) a.N := by
  have hq : (0 : ℝ) ≤ ((normV w : ℕ) : ℝ) := Nat.cast_nonneg _
  have hs : ∀ r : ℝ, 0 ≤ r → absSpace (a.ρ ψ) (r ^ f) = absSpace (a.ρ φ) r := by
    intro r hr
    obtain ⟨M, hM, e⟩ := exists_pow_eq a hφ hψ
    rw [← absSpace_pow_eq (a.semisimple ψ) (pow_nonneg hr f) hM.ne', e, ← pow_mul,
      absSpace_pow_eq (a.semisimple φ) hr (mul_ne_zero hf hM.ne')]
  have hs' : ∀ x : ℝ, absSpace (a.ρ ψ) ((((normV w : ℕ) : ℝ) ^ f) ^ x) = absSpace (a.ρ φ) (((normV w : ℕ) : ℝ) ^ x) := by
    intro x
    rw [← hs _ (Real.rpow_nonneg hq x), ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq,
      ← Real.rpow_mul hq, mul_comm]
  unfold IsPurePair
  simp only [hs']

end Weil

section Res

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
  (h : IsPlaceOver A w) (h' : IsPlaceOver A w')
  {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem resF_ne_zero : resF h h' ≠ 0 := by
  intro h0
  have e := normV_eq_pow_resF h h'
  rw [h0, pow_zero] at e
  exact (one_lt_normV w').ne' e

theorem tempered_resRep (a : WDRep h V) : (resRep h h' a).Tempered ↔ a.Tempered := by
  have hq : ((normV w' : ℕ) : ℝ) = ((normV w : ℕ) : ℝ) ^ resF h h' := by
    rw [normV_eq_pow_resF h h']; push_cast; rfl
  have hd : deg (resW h h' (frob h')) = (resF h h' : ℕ) := by
    rw [deg_resW, deg_frob, mul_one]
  constructor
  · intro ht φ hφ
    have h1 := ht (frob h') deg_frob
    rw [hq] at h1
    exact (isPurePair_iff a (resF_ne_zero h h') hφ hd).mp h1
  · intro ht φ' hφ'
    rw [hq]
    have hd' : deg (resW h h' φ') = (resF h h' : ℕ) := by rw [deg_resW, hφ', mul_one]
    exact (isPurePair_iff a (resF_ne_zero h h') deg_frob hd').mpr (ht _ deg_frob)

theorem normV_cpow (s : ℝ) :
    ((normV w' : ℕ) : ℂ) ^ ((s : ℝ) : ℂ) = (((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) ^ resF h h' := by
  have hq : (0 : ℝ) ≤ ((normV w : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [normV_eq_pow_resF h h', Nat.cast_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_pow,
    ← Complex.ofReal_cpow (pow_nonneg hq _), ← Complex.ofReal_cpow hq, ← Complex.ofReal_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq, ← Real.rpow_mul hq, mul_comm]

theorem iso_res_tw (a : WDRep h V) (s : ℝ) : ((resRep h h' a).tw s).Iso (resRep h h' (a.tw s)) := by
  refine ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  simp only [LinearEquiv.refl_apply, WDRep.tw_ρ, resRep_ρ, deg_resW, LinearMap.smul_apply]
  rw [zpow_mul, zpow_natCast, normV_cpow h h']

end Res

theorem tempRes : TempRes := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ _ _ A w w' h h' x s
  induction x using WD.ind with
  | hP n a =>
    rw [WD.res_mk, WD.lpTw_mk, WD.lpTw_mk, WD.tempered_mk, WD.tempered_mk]
    exact ⟨fun ht => (tempered_resRep h h' (a.tw s)).mp ((iso_res_tw h h' a s).tempered ht),
      fun ht => (iso_res_tw h h' a s).symm.tempered ((tempered_resRep h h' (a.tw s)).mpr ht)⟩

end GlobalTheory.CompanionTheory.TempRes
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantSmallBoxesStatement
section
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_invariant_small_boxes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (χ : Multiplicative (Fin n → k) →* ℂˣ) (v : V), v ∈ twKer ρ ⊤ (χ.comp (⊤ : Subgroup (Multiplicative (Fin n → k))).subtype) → ∃ j : ℤ, ∀ j' ≤ j, v ∈ twKer ρ (box k n j') (χ.comp (box k n j').subtype) := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_mem_twKer_box | exact GlobalTheory.CompanionTheory.MirFourier.exists_mem_twKer_box | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_mem_twKer_box <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquivStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_jacquet_phi_minus_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m n : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (m + 1)) V), Nonempty (TwJacquet (phiMinus k ψ τ) (derUnipM k m n) (derCharM k ψ m n) ≃ₗ[ℂ] TwJacquet τ (derUnipM k (m + 1) n) (derCharM k ψ (m + 1) n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZMirStep.phiMinus_twJacquet_equiv | exact GlobalTheory.CompanionTheory.BZMirStep.phiMinus_twJacquet_equiv | (intros; apply GlobalTheory.CompanionTheory.BZMirStep.phiMinus_twJacquet_equiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelConjugation
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirabolic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem twKer_le_comap_levi (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k n) V) (a : Fin n → k) (m : GL (Fin n) k) :
    twKer τ (MirUin k n) (thetaA k ψ (vecMul a (m : Matrix (Fin n) (Fin n) k))) ≤
      (twKer τ (MirUin k n) (thetaA k ψ a)).comap (τ (levi k n m)) := by
  unfold GlobalTheory.PRep.twKer
  rw [Submodule.span_le]
  intro x hx
  have key : ∀ (u : GlobalTheory.BZMir.MirUin k n) (w : V),
      τ (GlobalTheory.BZMir.levi k n m) (τ u w) =
        τ (GlobalTheory.BZMir.levi k n m * u * (GlobalTheory.BZMir.levi k n m)⁻¹) (τ (GlobalTheory.BZMir.levi k n m) w) := by
    intro u w
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  first
    | (obtain ⟨u, w, rfl⟩ := hx
       obtain ⟨hm, hc⟩ := GlobalTheory.CompanionTheory.BZMirabolic.thetaConj k ψ n a m u
       simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, Units.smul_def, map_smul]
       rw [key, hc]
       exact Submodule.subset_span ⟨⟨_, hm⟩, _, rfl⟩)
    | (obtain ⟨⟨u, w⟩, rfl⟩ := hx
       obtain ⟨hm, hc⟩ := GlobalTheory.CompanionTheory.BZMirabolic.thetaConj k ψ n a m u
       simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, Units.smul_def, map_smul]
       rw [key, hc]
       exact Submodule.subset_span ⟨(⟨_, hm⟩, _), rfl⟩)

theorem twKerConj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : TwKerConj k := by
  unfold GlobalTheory.BZMir.Fun.TwKerConj
  intro ψ n V _ _ τ a m v
  constructor
  · intro hv
    exact GlobalTheory.CompanionTheory.BZMirabolic.twKer_le_comap_levi ψ τ a m hv
  · intro hv
    have ha : vecMul (vecMul a (m : Matrix (Fin n) (Fin n) k))
        ((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = a := by
      rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
    rw [← ha] at hv
    have h := GlobalTheory.CompanionTheory.BZMirabolic.twKer_le_comap_levi ψ τ _ m⁻¹ hv
    rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel,
      map_one, map_one, Module.End.one_apply] at h
    exact h

end GlobalTheory.CompanionTheory.BZMirabolic

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelOfSmallBoxCharacterStatement
section
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_kernel_of_small_box_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V), IsSmooth ρ → ∀ (v : V) (N J : ℤ), J ≤ N → (∀ x ∈ box k n N, ρ x v = v) → (∀ a : Fin n → k, (∀ i, a i ∈ valBall k (addCharConductor ψ - N)) → v ∈ twKer ρ (box k n J) (chiOn k ψ a (box k n J))) → v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.FiniteInversion.fourier_finite | exact GlobalTheory.CompanionTheory.MirFourier.FiniteInversion.fourier_finite | (intros; apply GlobalTheory.CompanionTheory.MirFourier.FiniteInversion.fourier_finite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundOfArchimedeanLipschitzStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_bound_of_archimedean_lipschitz : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) (f₀ f₁ : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (r : ℕ), 0 < r → r < n → UFam f₁ →
  (∀ R : ℝ, ∃ (Q₀ : Set (AdelicGLn.AdelicGL K n)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧ ∀ i g (Y : ArchMatrix K n) (M : ℝ), Y * Y = 0 → ‖Y‖ ≤ R →
    (∀ q ∈ Q₀, ‖f₀ i (g * q)‖ ≤ M) → ‖f₁ i (g * CuspidalSpectrum.archExp Y) - f₁ i g‖ ≤ C * ‖Y‖ * M) →
  UBnd f₀ m → UBnd (fun i g => f₁ i g - An.ctn r (f₁ i) g) (Function.update m r (m r - 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Conc.diffStepU | exact GlobalTheory.CompanionTheory.Conc.diffStepU | (intros; apply GlobalTheory.CompanionTheory.Conc.diffStepU <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittCoordQuotientPullBijectiveStatement
section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution CrystallineSemistableComparison.Pb.LsQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_coord_quotient_pull_bijective : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ} (hn : n ≠ 0) {W : X.Opens} {d : ℕ} (cW : Coord q W d) (j : ℕ), Function.Bijective (((mqS q ρ hn {W}).o (IdF.span _ ((l : WittVector l k) ^ n)) (fun _ => le_rfl)).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal.local_bij | exact GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal.local_bij | (intros; apply GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal.local_bij <;> assumption)
end

