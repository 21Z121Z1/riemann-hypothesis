import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.ExLLeOfCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHFinC
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.GlobalFixedVectors UpperTheory.V.Sd
open Neutral.B1 Formalism.L2.Host UpperTheory.V.Base

namespace UpperTheory.Esk.HFinCAux

theorem exists_rep {K ι A : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [Finite ι] (e : ι → K) (r : A → K)
    (χ : A → ℂ) (h : ∀ x, ∃ i a, x = e i * r a) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W) (ρ : Representation ℂ K W),
      GlobalTheory.Published.AutFin.IsContRep ρ ∧
        ∀ f : K → ℂ, Continuous f → (∀ x a, f (x * r a) = χ a * f x) → f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  let V : Submodule ℂ (K → ℂ) :=
    { carrier := {f | Continuous f ∧ ∀ x a, f (x * r a) = χ a * f x}
      add_mem' := fun hf hg => ⟨hf.1.add hg.1, fun x a => by simp [hf.2, hg.2, mul_add]⟩
      zero_mem' := ⟨continuous_const, fun x a => by simp⟩
      smul_mem' := fun c f hf => ⟨hf.1.const_smul c, fun x a => by simp [hf.2, mul_left_comm]⟩ }
  haveI : FiniteDimensional ℂ V := by
    refine Module.Finite.of_injective ((LinearMap.funLeft ℂ ℂ e).comp V.subtype) ?_
    rw [injective_iff_map_eq_zero]
    intro f hf
    ext x
    obtain ⟨i, a, rfl⟩ := h x
    have : f.1 (e i) = 0 := congrFun hf i
    rw [f.2.2, this]; simp
  let L : Representation ℂ K V :=
    { toFun := fun k =>
        { toFun := fun f => ⟨fun x => f.1 (k⁻¹ * x), f.2.1.comp (continuous_const.mul continuous_id), fun x a => by
            simp only [← mul_assoc, f.2.2]⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_one' := by ext f x; simp
      map_mul' := fun k k' => by ext f x; simp [mul_assoc] }
  refine ⟨Module.Dual ℂ V, inferInstance, inferInstance, inferInstance, L.dual, fun l w => ?_, fun f hf hf' => ?_⟩
  · obtain ⟨f, rfl⟩ := (Module.evalEquiv ℂ V).surjective l
    change Continuous fun k => w (L k⁻¹ f)
    refine w.continuous_of_finiteDimensional.comp (Continuous.subtype_mk (continuous_pi fun x => ?_) _)
    exact f.2.1.comp (continuous_inv.inv.mul continuous_const)
  · refine Submodule.subset_span ⟨Module.Dual.eval ℂ V ⟨f, hf, hf'⟩, (LinearMap.proj 1).comp V.subtype, funext fun k => ?_⟩
    change f k = f (k⁻¹⁻¹ * 1)
    simp

variable {F : Type} [Field F] [NumberField F]

theorem local_mem_principal_congruence {M : ℕ} (w : HeightOneSpectrum (𝓞 F)) (c : ℕ)
    (hM : (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)
    {k : GL (Fin 2) (Af F)} (hk : k ∈ KLev F 2 M) : GeneralLinearGroup.map (pLoc F w) k ∈ K1 w c := by
  obtain ⟨g, hg, rfl⟩ := hk
  let p : Ohat F →+* w.adicCompletionIntegers F :=
    ((pLoc F w).comp (Ohat F).subtype).codRestrict (w.adicCompletionIntegers F) fun x => GlobalFixedVectors.mem_Ohat.1 x.2 w
  refine ⟨GeneralLinearGroup.map p g, ?_, Units.ext rfl⟩
  have key : GeneralLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)) (GeneralLinearGroup.map p g) = 1 := by
    let q := Ideal.quotientMap (I := Ideal.span {(M : ↥(Ohat F))}) (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c) p
      ((Ideal.span_singleton_le_iff_mem _).2 (by simpa using hM))
    have := congrArg (GeneralLinearGroup.map q) (MonoidHom.mem_ker.1 hg)
    rw [map_one] at this
    rw [← this]
    rfl
  exact Subgroup.mem_comap.2 (key ▸ one_mem _)

theorem exists_level (c : HeightOneSpectrum (𝓞 F) → ℕ) (hc : {w | c w ≠ 0}.Finite) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c w := by
  refine ⟨∏ w ∈ hc.toFinset, Ideal.absNorm w.asIdeal ^ c w, ?_, fun w => ?_⟩
  · refine Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_)
    exact fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · by_cases h : c w = 0
    · simp [h]
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun w : HeightOneSpectrum (𝓞 F) => Ideal.absNorm w.asIdeal ^ c w)
      (hc.mem_toFinset.2 h)
    rw [hm, Nat.cast_mul, Nat.cast_pow]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ _)
    have h1 := Ideal.absNorm_mem w.asIdeal
    rw [← map_natCast (algebraMap (𝓞 F) (w.adicCompletionIntegers F))]
    generalize (Ideal.absNorm w.asIdeal : 𝓞 F) = x at h1
    refine (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (w.adicCompletion F) _)).2 ?_
    have h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) x) < 1 := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (w.adicCompletion F)]
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_lt ((w.valuation_lt_one_iff_mem x).2 h1)
    exact h2

theorem fixed_KLev {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (Af F)) V) {M : ℕ} (v : V)
    (ho : IsOpen {k | ρ k v = v}) (h : ∀ w, ∀ k ∈ KLev F 2 M, ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) v = v) :
    ∀ k ∈ KLev F 2 M, ρ k v = v := by
  classical
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ k ∈ KAway 2 M S, ρ k v = v) → ∀ k ∈ KAway 2 M ∅, ρ k v = v := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      refine fun hv => ih fun k hk => ?_
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway 2 M (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 := h w k (mem_KAway.1 hk).1
      have h4 := hv _ h2
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := M) (ho.mem_nhds (by simp))
  exact fun k hk => key S (fun k hk => hS hk) k (mem_KAway.2 ⟨hk, by simp⟩)

noncomputable def rot (θ : TR.Rinf F) : TR.Kinf F 2 :=
  ⟨!![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq (θ v)]⟩

noncomputable def eps (s : InfinitePlace F → ℤˣ) : TR.Kinf F 2 :=
  ⟨!![1, 0; 0, fun v => ((s v : ℤ) : ℝ)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
    rcases Int.units_eq_one_or (s v) with h | h <;> simp [h]⟩

omit [NumberField F] in
theorem rot_add (θ η : TR.Rinf F) : rot (θ + η) = rot θ * rot η := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

omit [NumberField F] in
theorem rot_zero : rot (0 : TR.Rinf F) = 1 := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot]

theorem real_dec {a b c d : ℝ} (h1 : a * a + b * b = 1) (h2 : a * c + b * d = 0) (h3 : c * c + d * d = 1) :
    ∃ (s : ℤˣ) (t : ℝ), a = Real.cos t ∧ b = Real.sin t ∧ c = -((s : ℤ) * Real.sin t) ∧ d = (s : ℤ) * Real.cos t := by
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, h1, Real.sqrt_one]
  have h0 : (⟨a, b⟩ : ℂ) ≠ 0 := fun h => by simp [h] at hn
  have ha : a = Real.cos (Complex.arg ⟨a, b⟩) := by rw [Complex.cos_arg h0, hn, div_one]
  have hb : b = Real.sin (Complex.arg ⟨a, b⟩) := by rw [Complex.sin_arg, hn, div_one]
  have hc : c = -((a * d - b * c) * b) := by linear_combination (-c) * h1 + a * h2
  have hd : d = (a * d - b * c) * a := by linear_combination (-d) * h1 + b * h2
  have hs : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (c * c + d * d) * h1 + h3 - (a * c + b * d) * h2
  rcases mul_self_eq_one_iff.1 hs with h | h
  · exact ⟨1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩
  · exact ⟨-1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩

omit [NumberField F] in
theorem dec (x : TR.Kinf F 2) : ∃ s θ, x = eps s * rot θ := by
  have h := Matrix.mem_unitaryGroup_iff.1 x.2
  have e : ∀ i j v, x.1 i 0 v * x.1 j 0 v + x.1 i 1 v * x.1 j 1 v = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v := fun i j v => by
    rw [← h]; simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
  choose s θ h1 h2 h3 h4 using fun v => real_dec (a := x.1 0 0 v) (b := x.1 0 1 v) (c := x.1 1 0 v) (d := x.1 1 1 v)
    (by simpa using e 0 0 v) (by simpa using e 0 1 v) (by simpa using e 1 1 v)
  refine ⟨s, θ, ?_⟩
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, eps, Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, h3, h4]

variable [IsTotallyReal F]

theorem cont (φ : TR.Sm F 2) (g : GA F 2) : Continuous fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g := by
  have e : (fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g) = fun k : TR.Kinf F 2 => TR.chart φ.1 g (TR.toL k.1) :=
    funext fun k => (TR.chart_val φ.1 g (Unitary.toUnits k)).symm
  rw [e]
  exact (φ.2 g).continuousOn.comp_continuous continuous_subtype_val fun k => TR.val_mem_invSet (Unitary.toUnits k)

theorem rot_eig (φ : TR.Sm F 2) (z : InfinitePlace F → ℂ) (h : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = z v • φ) (g : GA F 2) (θ : TR.Rinf F) :
    φ.1 (g * TR.infGL F 2 (Unitary.toUnits (rot θ))) = Complex.exp (∑ v, z v * (θ v : ℂ)) * φ.1 g := by
  classical
  set μ : ℂ := ∑ v, z v * (θ v : ℂ) with hμ
  let X : TR.Lie F 2 := TR.toL !![0, θ; -θ, 0]
  have hX : X = ∑ v, θ v • (TR.toL (Matrix.single 0 1 (Pi.single v 1)) - TR.toL (Matrix.single 1 0 (Pi.single v 1))) := by
    ext i j u
    fin_cases i <;> fin_cases j <;> simp [X, Finset.sum_apply, Pi.single_apply]
  have hL : TR.lie F 2 X φ = μ • φ := by
    rw [hX, map_sum, LinearMap.sum_apply, hμ, Finset.sum_smul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, mul_comm, mul_smul, Complex.coe_smul, ← h v]
    simp only [TR.Eop]
  have hc : HasDerivAt (fun t : ℝ => TR.toL (Unitary.toUnits (rot (t • θ))).val) X 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
    have h1 : HasDerivAt (fun t : ℝ => t * θ v) (θ v) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (θ v)
    fin_cases i <;> fin_cases j
    · simpa [X, rot] using h1.cos
    · simpa [X, rot] using h1.sin
    · simpa [X, rot] using h1.sin.fun_neg
    · simpa [X, rot] using h1.cos
  let f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (Unitary.toUnits (rot (t • θ))))
  have hf : ∀ t, HasDerivAt f (μ * f t) t := fun t => by
    have h1 := TR.hasDerivAt_curve φ (g * TR.infGL F 2 (Unitary.toUnits (rot (t • θ)))) (fun s => Unitary.toUnits (rot (s • θ))) X
      (by rw [zero_smul, rot_zero, map_one]) hc
    rw [← TR.lie_apply, hL] at h1
    have h2 : HasDerivAt (fun s => f (t + s)) (μ * f t) 0 := by
      simpa only [f, add_smul, rot_add, map_mul, mul_assoc] using! h1
    have h3 := HasDerivAt.comp_sub_const t t (f := fun s => f (t + s)) (by rw [sub_self]; exact h2)
    simpa using h3
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-μ * s) * f s) 0 t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => -μ * (s : ℂ)) (-μ) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-μ)
    exact (h1.cexp.fun_mul (hf t)).congr_deriv (by ring)
  have h4 := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [f, one_smul, zero_smul, rot_zero, map_one, mul_one, Complex.ofReal_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul] at h4
  rw [← h4, ← mul_assoc, ← Complex.exp_add]
  simp

end UpperTheory.Esk.HFinCAux

open UpperTheory.Esk.HFinCAux in
theorem UpperTheory.Esk.pf_HFinC : UpperTheory.Esk.HCap → UpperTheory.Esk.HFinC := by
  intro hcap F _ _ _ k c hc ω hω
  obtain ⟨M, hM1, hM⟩ := exists_level c hc
  have hfix : ∀ φ : TR.Sm F 2, UpperTheory.Esk.IsHolV k c ω φ → ∀ u ∈ KLev F 2 M, TR.finRep F 2 u φ = φ := fun φ hφ =>
    fixed_KLev _ φ hφ.aut.level fun w u hu => hφ.level w _ (local_mem_principal_congruence w _ (hM w) hu)
  obtain ⟨W, _, _, _, ρ, hρ, hf⟩ := exists_rep (eps (F := F)) (rot (F := F))
    (fun θ => Complex.exp (∑ v, Complex.I * (k v : ℂ) * (θ v : ℂ))) dec
  have := UpperTheory.V.Af.cuspFormsFiniteReal F 2 (KLev F 2 M) (isOpen_KLev hM1) W ρ hρ
    fun v u => (u + ((k v : ℂ) - 1) / 2) * (u - ((k v : ℂ) - 1) / 2)
  refine Submodule.finiteDimensional_of_le (S₂ := _) (Submodule.span_mono (fun φ hφ => ?_) : _ ≤ Submodule.span ℂ
    {φ : TR.Sm F 2 | TR.IsCuspForm φ ∧ (∀ u ∈ KLev F 2 M, TR.finRep F 2 u φ = φ) ∧
      (∀ g : GA F 2, (fun u : TR.Kinf F 2 => (TR.cptRep F 2 u φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
      ∀ v u, TR.cap v u φ = ((u + ((k v : ℂ) - 1) / 2) * (u - ((k v : ℂ) - 1) / 2)) • φ})
  obtain ⟨hφ', hcusp⟩ := hφ
  refine ⟨hcusp, hfix φ hφ', fun g => hf _ (cont φ g) fun x θ => ?_, (hcap F k c ω hω φ hφ').2⟩
  have := rot_eig φ (fun v => Complex.I * (k v : ℂ)) hφ'.wt (g * TR.infGL F 2 (Unitary.toUnits x)) θ
  rw [mul_assoc, ← map_mul, ← map_mul] at this
  exact this
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfPropMV
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

namespace UpperTheory.Esk.PropMVAux

variable {l : ℕ} [Fact l.Prime]

theorem add_lt {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

theorem norm_one_of {x : Qbar l} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have h1 : ‖x - 1‖ ≠ ‖(1 : Qbar l)‖ := by rw [norm_one]; exact h.ne
  have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1
  rwa [sub_add_cancel, norm_one, max_eq_right h.le] at h2

def oneU (l : ℕ) [Fact l.Prime] : Subgroup (Qbar l)ˣ where
  carrier := {x | ‖(x : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have e : ((a * b : (Qbar l)ˣ) : Qbar l) - 1 = a * (b - 1) + (a - 1) := by rw [Units.val_mul]; ring
    show ‖_‖ < 1
    rw [e]
    refine add_lt ?_ ha
    rw [norm_mul, norm_one_of ha, one_mul]
    exact hb
  inv_mem' {a} ha := by
    have e : (a : Qbar l) * (((a⁻¹ : (Qbar l)ˣ) : Qbar l) - 1) = -(a - 1) := by
      rw [mul_sub, Units.mul_inv]; ring
    have h := congrArg norm e
    rw [norm_mul, norm_one_of ha, one_mul, norm_neg] at h
    show ‖_‖ < 1
    rw [h]
    exact ha

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] in
theorem cyc_mem (s : G F Ω) : cycBar F Ω l s ^ (l - 1) ∈ oneU l := by
  have e : ((cycBar F Ω l s ^ (l - 1) : (Qbar l)ˣ) : Qbar l) - 1 =
      algebraMap ℚ_[l] (Qbar l) ((((cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1 : ℤ_[l])) : ℚ_[l]) := by
    rw [Units.val_pow_eq_pow_val]
    change (algebraMap ℚ_[l] (Qbar l) ((cycZ F Ω l s : ℤ_[l]) : ℚ_[l])) ^ _ - 1 = _
    simp
  show ‖_‖ < 1
  rw [e, norm_algebraMap']
  change ‖(cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1‖ < 1
  rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
    map_one, ZMod.pow_card_sub_one_eq_one, sub_self]
  exact ((cycZ F Ω l s).isUnit.map _).ne_zero

theorem cont_cyc : Continuous (cycBar F Ω l) :=
  have h : Continuous fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l]) :=
    (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom h).comp (continuous_cycZ F Ω l)

theorem cyc_frob [IsAlgClosure F Ω] {A : ValuationSubring Ω} {v : Pl F} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (h : IsPlaceOver A v) {σ : G F Ω} (hσ : IsFrob A (normV v) σ) :
    ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) := by
  change algebraMap ℚ_[l] (Qbar l) ((cycZ F Ω l σ : ℤ_[l]) : ℚ_[l]) = _
  rw [cycZ_of_isFrob hl h hσ]
  simp

theorem fin_l : {w : Pl F | ((l : ℕ) : 𝓞 F) ∈ w.asIdeal}.Finite := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr hv

theorem cond_ex (ω : HChar F) {m : ℕ} (hm : 0 < m) (h : ω.OrderDvd m) :
    ∃ c : Pl F → ℕ, (∀ w, IsCondAt w ω (c w)) ∧ (∀ w, c w = 0 ↔ ω.UnrAt w) ∧ {w | c w ≠ 0}.Finite := by
  classical
  have ho := isOpen_ker_of_pow ω.1 ω.2.1 hm fun x => congrArg (fun ξ : HChar F => ξ.1 x) h
  obtain ⟨S, M, hS, key⟩ := GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen ω.1.ker ho
  have hex : ∀ w, ∃ n, ω.LevelLe w n := fun w => ⟨M, fun x hu hx => key w x hu fun _ => hx⟩
  have h0 : ∀ w, Nat.find (hex w) = 0 ↔ ω.UnrAt w := fun w => by rw [Nat.find_eq_zero, HChar.unrAt_iff]
  refine ⟨fun w => Nat.find (hex w), fun w => ⟨Nat.find_spec (hex w), fun n hn => Nat.find_min' (hex w) hn⟩, h0,
    hS.subset fun w hw => ?_⟩
  by_contra hS
  exact hw ((h0 w).2 fun x hx => key w x hx fun h => absurd h hS)

theorem loc_zpow {ω : HChar F} {w : Pl F} (hu : ω.UnrAt w) (x : (w.adicCompletion F)ˣ) :
    ∃ n : ℤ, ω.loc w x = ω.val w ^ n := by
  have hx0 : Valued.v (x : w.adicCompletion F) ≠ 0 := by simp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (x : w.adicCompletion F) = WithZero.exp n := ⟨_, (WithZero.exp_log hx0).symm⟩
  have hun : IsUnitAt w (x * atFin w (unif w) ^ n) := by
    have h2 := unif_spec w
    unfold IsUnitAt IsUnifAt at *
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h2, ← WithZero.exp_zsmul, hn, ← WithZero.exp_add]
    simp
  have h3 := hu _ hun
  rw [map_mul, map_zpow, mul_eq_one_iff_eq_inv, ← zpow_neg] at h3
  exact ⟨_, h3⟩

theorem closed_oneU : IsClosed (oneU l : Set (Qbar l)ˣ) := by
  have : IsClosed {x : Qbar l | ‖x - 1‖ < 1} := by
    simpa only [Metric.ball, dist_eq_norm] using IsUltrametricDist.isClosed_ball (1 : Qbar l) 1
  exact this.preimage Units.continuous_val

theorem dec_cong {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) {ι : Qbar l ≃+* ℂ} {ω : HChar F}
    {ξ : G F Ω →* (Qbar l)ˣ} (hc : Continuous ξ) (hL : IsLAdicOf art ι ω 0 ξ) {w : Pl F} (hu : ω.UnrAt w)
    (hv : ‖ι.symm (ω.val w : ℂˣ) - 1‖ < 1) {A : ValuationSubring Ω} (hA : IsPlaceOver A w) {σ : G F Ω}
    (hσ : σ ∈ Dec (F := F) A) : Cong (ξ σ) 1 := by
  have hm : toAb F Ω σ ∈ (art.comp (localIdele F w)).range.topologicalClosure := by
    rw [ha.dec w A hA]
    exact ⟨σ, hσ, rfl⟩
  have hle : (art.comp (localIdele F w)).range ≤ (oneU l).comap (liftAb ξ hc) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨τ, hτ⟩ := toAb_surjective (art (localIdele F w x))
    obtain ⟨n, hn⟩ := loc_zpow hu x
    have hv' : Units.map ι.symm.toRingHom.toMonoidHom (ω.val w) ∈ oneU l := hv
    have e : ξ τ = Units.map ι.symm.toRingHom.toMonoidHom (ω.val w) ^ n := by
      rw [← map_zpow, ← hn]
      exact Units.ext (hL.loc_away (Or.inr rfl) x τ hτ.symm)
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, ← hτ, liftAb_toAb, e]
    exact zpow_mem hv' _
  have h := Subgroup.topologicalClosure_minimal _ hle (closed_oneU.preimage (continuous_liftAb ξ hc)) hm
  rw [Subgroup.mem_comap, liftAb_toAb] at h
  exact h

theorem tr_det (ι : Qbar l ≃+* ℂ) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (a b : ℂ)
    (h : M.charpoly.map ι.toRingHom = Polynomial.X ^ 2 - C a * Polynomial.X + C b) : M.trace = ι.symm a ∧ M.det = ι.symm b := by
  rw [Matrix.charpoly_fin_two] at h
  have h2 := congrArg (coeff · 1) h
  have h3 := congrArg (coeff · 0) h
  simp [coeff_X_pow, coeff_C] at h2 h3
  rw [← h2, ← h3]
  simp

theorem det_res [IsAlgClosure F Ω] (ξ : G F Ω →* (Qbar l)ˣ) (hξ : Continuous ξ) (r : G F Ω →* GL (Fin 2) (Qbar l))
    (hr : Continuous r) (k : ℕ) (hk : l - 1 ∣ k) (hn : ∀ s, ‖(ξ s : Qbar l)‖ = 1) {S : Set (Pl F)} (hS : S.Finite)
    (h : ∀ w, w ∉ S → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ σ : G F Ω, IsFrob A (normV w) σ →
      ‖(r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + ξ σ⁻¹)‖ < 1 ∧
      (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = ξ σ⁻¹ * (cycBar F Ω l σ : Qbar l) ^ k) :
    Matrix.GeneralLinearGroup.det.comp r = cycBar F Ω l ^ (-(k : ℤ)) * ξ ∧ ResSum r ![1, ξ] := by
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
  have c1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp (hr.comp continuous_inv)
  have c2 : Continuous fun g : G F Ω => (ξ g⁻¹ : Qbar l) := Units.continuous_val.comp (hξ.comp continuous_inv)
  have c3 : Continuous fun g : G F Ω => (cycBar F Ω l g : Qbar l) := Units.continuous_val.comp cont_cyc
  have hdet : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = ξ g⁻¹ * (cycBar F Ω l g : Qbar l) ^ k := fun g => by
    refine congrFun (Continuous.ext_on hD c1.matrix_det (c2.mul (c3.pow k)) ?_) g
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    exact (h v hv A hA σ hσ).2
  have htr : ∀ g : G F Ω, ‖(r g⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + ξ g⁻¹)‖ < 1 := fun g => by
    have h0 : IsClosed {x : Qbar l | ‖x‖ < 1} := by
      simpa only [Metric.ball, dist_zero_right] using IsUltrametricDist.isClosed_ball (0 : Qbar l) 1
    have h1 := h0.preimage (c1.matrix_trace.sub (continuous_const.add c2 : Continuous fun g : G F Ω => 1 + (ξ g⁻¹ : Qbar l)))
    refine h1.closure_subset_iff.2 ?_ (hD g)
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    exact (h v hv A hA σ hσ).1
  refine ⟨MonoidHom.ext fun g => Units.ext ?_, fun g i => ?_⟩
  · have h1 := hdet g⁻¹
    rw [inv_inv] at h1
    change (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det = ((cycBar F Ω l g ^ (-(k : ℤ)) * ξ g : (Qbar l)ˣ) : Qbar l)
    rw [h1]
    simp [mul_comm]
  · have h1 := hdet g⁻¹
    have h2 := htr g⁻¹
    rw [inv_inv] at h1 h2
    have h3 : ‖(r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det - ξ g‖ < 1 := by
      obtain ⟨t, rfl⟩ := hk
      have h4 : ‖((cycBar F Ω l g⁻¹ ^ ((l - 1) * t) : (Qbar l)ˣ) : Qbar l) - 1‖ < 1 := by
        rw [pow_mul]; exact pow_mem (cyc_mem g⁻¹) t
      rw [h1, ← mul_sub_one, norm_mul, hn, one_mul, ← Units.val_pow_eq_pow_val]
      exact h4
    have e : (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly - ∏ j, (Polynomial.X - C ((![1, ξ] j g : (Qbar l)ˣ) : Qbar l)) =
        C (-((r g : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + ξ g))) * Polynomial.X + C ((r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det - ξ g) := by
      rw [Matrix.charpoly_fin_two, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.one_apply, Units.val_one, map_neg, map_sub, map_add, map_one]
      ring
    rw [← coeff_sub, e]
    rcases i with _ | _ | i
    · rwa [coeff_add, mul_coeff_zero, coeff_X_zero, mul_zero, zero_add, coeff_C_zero]
    · rwa [coeff_add, coeff_mul_X, coeff_C_zero, coeff_C_succ, add_zero, norm_neg]
    · rw [coeff_add, coeff_mul_X, coeff_C_succ, coeff_C_succ, add_zero, norm_zero]
      exact zero_lt_one

theorem norm_eq_one {x y : Qbar l} (hy : ‖y‖ = 1) (h : ‖x - y‖ < 1) : ‖x‖ = 1 := by
  have h1 : ‖x - y‖ ≠ ‖y‖ := by rw [hy]; exact h.ne
  have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1
  rwa [sub_add_cancel, hy, max_eq_right h.le] at h2

theorem nu_lt {ι : Qbar l ≃+* ℂ} {x : ℂ} : Wc.nu ι x < 1 ↔ ‖ι.symm x‖ < 1 := by
  rw [Wc.nu_apply, ← NNReal.coe_lt_one, coe_nnnorm]

theorem nu_eq {ι : Qbar l ≃+* ℂ} {x : ℂ} : Wc.nu ι x = 1 ↔ ‖ι.symm x‖ = 1 := by
  rw [Wc.nu_apply, ← NNReal.coe_eq_one, coe_nnnorm]

open Classical in
theorem prod_away {ι : Qbar l ≃+* ℂ} (D : Wc.LDat F ι) (S : Set (InfinitePlace F)) (t : ℕ) (w : Pl F)
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) : (∏ v, if D.pl v = w ∧ v ∈ S then (l : ℂ) ^ t else 1) = 1 :=
  Finset.prod_eq_one fun v _ => by
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hw (h ▸ D.mem v)

open Classical in
theorem prod_at {ι : Qbar l ≃+* ℂ} (D : Wc.LDat F ι) (S : Set (InfinitePlace F)) (t : ℕ) (w : Pl F) (v₀ : InfinitePlace F)
    (hv : D.pl v₀ = w) : (∏ v, if D.pl v = w ∧ v ∈ S then (l : ℂ) ^ t else 1) = if v₀ ∈ S then (l : ℂ) ^ t else 1 := by
  rw [Finset.prod_eq_single v₀ (fun v _ hne => if_neg fun h => hne (D.inj (h.1.trans hv.symm)))
    (fun h => absurd (Finset.mem_univ _) h)]
  by_cases h : v₀ ∈ S <;> simp [hv, h]

end UpperTheory.Esk.PropMVAux
end

